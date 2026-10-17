import Char2Theta.Section1.FiniteBasics
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.RepresentationTheory.Character
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Pauli、Heisenberg 与 Clifford 正合列（§§1.1–1.2）

本文件按证明依赖组织有限群理论：Pauli 群的忠实酉模型与完整 Clifford 正规化子；
二元 Heisenberg 群、二次型及中心固定自同构；Pauli 自同构的辛作用与核；
辛变换提升；最后用酉实现构造实际射影 Clifford 商及正合列 (1.1)。

主要入口：`Pauli.matrix_unitary`、`Heisenberg₂.inducedQuadraticIsometry`、
`PauliAut.toSymplectic_surjective`、`projectiveCliffordEquiv`、`equation_1_1`。
一般中心扩张与复相位工具来自 `FiniteBasics`；全体复单位标量参与射影商，
没有将其缩小为有限单位根。
-/

set_option autoImplicit false

/-! ## The Pauli group and its faithful unitary model (§1.1) -/

namespace Char2Theta
namespace Pauli

open BilinearExtension
variable {N : ℕ}

/-- Translation label. -/
abbrev a (g : Pauli N) := g.label.1
/-- Modulation label. -/
abbrev b (g : Pauli N) := g.label.2

/-- Normal-form parameters are unique by construction. -/
def normalFormEquiv (N : ℕ) : Pauli N ≃ Labels N × ZMod 4 where
  toFun g := (g.label, g.central)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (N : ℕ) : Fintype (Pauli N) := Fintype.ofEquiv _ (normalFormEquiv N).symm

theorem card (N : ℕ) : Fintype.card (Pauli N) = 2 ^ (2 * N + 2) := by
  rw [Fintype.card_congr (normalFormEquiv N)]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  ring

/-- Complex functions on the finite label set realize `ℂ[𝔽₂ᴺ]`. -/
abbrev Hilbert (N : ℕ) := Bits N → ℂ

/-- The computational delta basis. -/
noncomputable def delta (x : Bits N) : Hilbert N := Pi.single x 1

/-- Shift operator, written on coefficient functions. In characteristic two, `z-a=z+a`. -/
noncomputable def X (a : Bits N) : Module.End ℂ (Hilbert N) where
  toFun f z := f (z + a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Phase operator. -/
noncomputable def Z (b : Bits N) : Module.End ℂ (Hilbert N) where
  toFun f z := sign (dot b z) * f z
  map_add' f g := by ext; simp [mul_add]
  map_smul' c f := by ext; simp [mul_comm, mul_assoc]

@[simp] theorem X_apply (a : Bits N) (f : Hilbert N) (z : Bits N) :
    X a f z = f (z + a) := rfl
@[simp] theorem Z_apply (b : Bits N) (f : Hilbert N) (z : Bits N) :
    Z b f z = sign (dot b z) * f z := rfl

/-- The basis-vector convention in the notes, not its inverse. -/
theorem X_delta (a x : Bits N) : X a (delta x) = delta (x + a) := by
  ext z
  have haa : a + a = 0 := by ext i; exact CharTwo.add_self_eq_zero (a i)
  have hz : z + a = x ↔ z = x + a := by
    constructor <;> intro h <;> simpa [add_assoc, haa] using congrArg (· + a) h
  simp [delta, Pi.single_apply, hz]

theorem Z_delta (b x : Bits N) : Z b (delta x) = sign (dot b x) • delta x := by
  ext z
  by_cases hz : z = x
  · subst z; simp [delta]
  · simp [delta, hz]

/-- The exact commutation relation of §1.1. -/
theorem Z_mul_X (a b : Bits N) :
    Z b * X a = sign (dot a b) • (X a * Z b) := by
  apply LinearMap.ext
  intro f
  funext z
  change sign (dot b z) * f (z + a) =
    sign (dot a b) * (sign (dot b (z + a)) * f (z + a))
  simp only [dot, dotProduct_add, sign_add]
  rw [dotProduct_comm a b]
  calc
    sign (dot b z) * f (z + a) =
        sign (dot b z) * (sign (dot b a) * sign (dot b a)) * f (z + a) := by simp
    _ = _ := by ring

/-- The matrix of `i^s X_a Z_b` in the delta basis. -/
noncomputable def matrix (g : Pauli N) : Matrix (Bits N) (Bits N) ℂ :=
  fun x y => if x = y + g.a then phase g.central * sign (dot g.b y) else 0

@[simp] theorem matrix_at (g : Pauli N) (y : Bits N) :
    matrix g (y + g.a) y = phase g.central * sign (dot g.b y) := by simp [matrix]

@[simp] theorem matrix_one : matrix (1 : Pauli N) = 1 := by
  ext x y
  simp [matrix, a, b, Matrix.one_apply]

/-- Multiplication includes the central correction `2 b·a'`. -/
theorem matrix_mul (g h : Pauli N) : matrix (g * h) = matrix g * matrix h := by
  classical
  ext x y
  rw [Matrix.mul_apply, Finset.sum_eq_single (y + h.a)]
  · simp only [matrix, mul_central]
    change (if x = y + (g.a + h.a) then
      phase (g.central + h.central + twoLift (dot g.b h.a)) * sign (dot (g.b + h.b) y)
      else 0) =
      (if x = y + h.a + g.a then phase g.central * sign (dot g.b (y + h.a)) else 0) *
        (phase h.central * sign (dot h.b y))
    simp only [phase_add, add_dotProduct, dotProduct_add, sign_add]
    by_cases hx : x = y + (g.a + h.a)
    · simp [hx, add_comm, add_left_comm]
      simp only [sign]
      ring
    · simp [hx, add_comm, add_left_comm]
  · intro z _ hz
    simp [matrix, hz]
  · simp

/-- Each normal-form matrix is unitary for the standard Hermitian form. -/
theorem matrix_unitary (g : Pauli N) : matrix g ∈ Matrix.unitaryGroup (Bits N) ℂ := by
  classical
  rw [Matrix.mem_unitaryGroup_iff']
  ext x y
  rw [Matrix.mul_apply, Finset.sum_eq_single (x + g.a)]
  · simp only [Matrix.star_apply, matrix_at]
    by_cases hxy : x = y
    · subst y
      simp only [matrix_at, Matrix.one_apply]
      change star (phase g.central * sign (dot g.b x)) *
        (phase g.central * sign (dot g.b x)) = 1
      rw [star_mul]
      calc
        _ = (star (phase g.central) * phase g.central) *
            (star (sign (dot g.b x)) * sign (dot g.b x)) := by ring
        _ = 1 := by simp only [sign, phase_star_mul, mul_one]
    · have hshift : x + g.a ≠ y + g.a := fun h => hxy (add_right_cancel h)
      simp [matrix, hshift, hxy]
  · intro z _ hz
    simp [Matrix.star_apply, matrix, hz]
  · simp

/-- The representation is faithful, for arbitrary rank (including zero). -/
theorem matrix_injective : Function.Injective (matrix (N := N)) := by
  classical
  intro g h he
  have ha : g.a = h.a := by
    by_contra hn
    have hh := congrFun (congrFun he g.a) 0
    simp [matrix, hn, phase_ne_zero] at hh
  have hs : g.central = h.central := by
    apply phase_injective
    have hh := congrFun (congrFun he g.a) 0
    simpa [matrix, ha] using hh
  have hb : g.b = h.b := by
    funext i
    have hh := congrFun (congrFun he (Pi.single i 1 + g.a)) (Pi.single i 1)
    simp only [matrix, ha, hs] at hh
    have hh' := sign_injective (mul_left_cancel₀ (phase_ne_zero h.central) hh)
    simpa using hh'
  exact BilinearExtension.ext (Prod.ext ha hb) hs

/-- The concrete matrices realize the displayed action `i^s X_a Z_b` on every
computational basis vector. -/
theorem matrix_delta (g : Pauli N) (x : Bits N) :
    (matrix g).mulVec (delta x) = phase g.central • (X g.a (Z g.b (delta x))) := by
  rw [Z_delta, map_smul, X_delta]
  change (matrix g).mulVec (Pi.single x 1) = _
  rw [Matrix.mulVec_single_one]
  funext z
  simp [Matrix.col, matrix, delta, Pi.single_apply, smul_eq_mul, mul_ite]

/-- Faithful homomorphism into mathlib's unitary matrix group. -/
noncomputable def unitaryHom (N : ℕ) : Pauli N →* Matrix.unitaryGroup (Bits N) ℂ where
  toFun g := ⟨matrix g, matrix_unitary g⟩
  map_one' := Subtype.ext matrix_one
  map_mul' g h := Subtype.ext (matrix_mul g h)

/-- The actual finite subgroup of operators denoted `P_N` in the notes. -/
noncomputable def operatorGroup (N : ℕ) : Subgroup (Matrix.unitaryGroup (Bits N) ℂ) :=
  (unitaryHom N).range

/-- The center consists exactly of the zero labels, hence of the fourth-root scalars. -/
theorem mem_center_iff (g : Pauli N) :
    g ∈ Subgroup.center (Pauli N) ↔ g.label = 0 := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro hg
    have ha : g.a = 0 := by
      funext i
      have hc : Commute g (⟨(0, Pi.single i 1), 0⟩ : Pauli N) := (hg _).symm
      have he := (BilinearExtension.commute_iff _ _).mp hc
      change twoLift (dot g.b 0) = twoLift (dot (Pi.single i 1) g.a) at he
      have := twoLift_injective he
      simpa using this.symm
    have hb : g.b = 0 := by
      funext i
      have hc : Commute g (⟨(Pi.single i 1, 0), 0⟩ : Pauli N) := (hg _).symm
      have he := (BilinearExtension.commute_iff _ _).mp hc
      change twoLift (dot g.b (Pi.single i 1)) = twoLift (dot 0 g.a) at he
      have := twoLift_injective he
      simpa using this
    exact Prod.ext ha hb
  · intro hg h
    have : g = ofCenter g.central := by ext <;> simp [hg]
    rw [this]
    exact (ofCenter_commute _ _).symm

/-- On the central copy of `Z/4`, the representation is exactly `s ↦ i^s I`. -/
theorem matrix_ofCenter (s : ZMod 4) :
    matrix (ofCenter s : Pauli N) = phase s • (1 : Matrix (Bits N) (Bits N) ℂ) := by
  ext x y
  simp [matrix, a, b, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul, mul_ite]

end Pauli

/-- The full unitary Clifford group, using the normalizer from mathlib. -/
noncomputable def Clifford (N : ℕ) : Subgroup (Matrix.unitaryGroup (Bits N) ℂ) :=
  Subgroup.normalizer (Pauli.operatorGroup N : Set (Matrix.unitaryGroup (Bits N) ℂ))

end Char2Theta

/-! ## Scalar operators and the full Pauli normalizer (§1.1) -/

namespace Char2Theta

noncomputable section

/-- The standard finite function space has the stated dimension `2^N`. -/
theorem hilbert_finrank (N : ℕ) : Module.finrank ℂ (Pauli.Hilbert N) = 2 ^ N := by
  rw [Module.finrank_fintype_fun_eq_card]
  simp [Bits]

/-- The scalar unitary matrix `c I`. -/
def scalarUnitary (N : ℕ) (c : unitary ℂ) : Matrix.unitaryGroup (Bits N) ℂ :=
  ⟨(c : ℂ) • (1 : Matrix (Bits N) (Bits N) ℂ),
    Unitary.smul_mem c (one_mem (unitary (Matrix (Bits N) (Bits N) ℂ)))⟩

theorem scalarUnitary_central (N : ℕ) (c : unitary ℂ) :
    scalarUnitary N c ∈ Subgroup.center (Matrix.unitaryGroup (Bits N) ℂ) := by
  rw [Subgroup.mem_center_iff]
  intro U
  apply Subtype.ext
  change U.val * ((c : ℂ) • 1) = ((c : ℂ) • 1) * U.val
  simp

/-- All of `U(1)I`, not only fourth roots of unity, is contained in the Clifford group. -/
theorem scalarUnitary_mem_clifford (N : ℕ) (c : unitary ℂ) :
    scalarUnitary N c ∈ Clifford N :=
  Subgroup.center_le_normalizer _ (scalarUnitary_central N c)

theorem scalarUnitary_injective (N : ℕ) : Function.Injective (scalarUnitary N) := by
  intro c d h
  apply Subtype.ext
  have hm := congrArg (fun U : Matrix.unitaryGroup (Bits N) ℂ => U.val 0 0) h
  simpa [scalarUnitary] using hm

/-- The usual unit circle as unitary scalars. -/
def circleUnitary (z : Circle) : unitary ℂ := by
  refine ⟨(z : ℂ), ?_⟩
  have h : (z : ℂ) * star (z : ℂ) = 1 := by
    simpa using Complex.mul_conj (z : ℂ)
  exact ⟨by simpa [mul_comm] using h, h⟩

/-- The full Clifford group is infinite, even though its Pauli subgroup is finite. -/
theorem clifford_infinite (N : ℕ) : Infinite (Clifford N) := by
  letI : Infinite (Set.Ioc (-Real.pi) Real.pi) := Set.Ioc.infinite (by
    linarith [Real.pi_pos])
  letI : Infinite Circle := Infinite.of_injective Circle.argEquiv.symm
    Circle.argEquiv.symm.injective
  let f : Circle → Clifford N := fun z =>
    ⟨scalarUnitary N (circleUnitary z), scalarUnitary_mem_clifford N _⟩
  apply Infinite.of_injective f
  intro z w h
  apply Circle.ext
  exact congrArg (fun c : unitary ℂ => (c : ℂ))
    (scalarUnitary_injective N (congrArg Subtype.val h))

/-- The abstract normal form and the concrete operator subgroup agree as groups. -/
def pauliEquivOperatorGroup (N : ℕ) : Pauli N ≃* Pauli.operatorGroup N :=
  MonoidHom.ofInjective (f := Pauli.unitaryHom N) (fun _ _ h =>
    Pauli.matrix_injective (congrArg Subtype.val h))

/-- The order formula also holds for the actual subgroup of unitary operators. -/
theorem operatorGroup_card (N : ℕ) : Nat.card (Pauli.operatorGroup N) = 2 ^ (2 * N + 2) := by
  rw [← Nat.card_congr (pauliEquivOperatorGroup N).toEquiv, Nat.card_eq_fintype_card, Pauli.card]

/-- The center in normal-form coordinates is `Z/4` with its additive group law. -/
def pauliCenterEquiv (N : ℕ) : Subgroup.center (Pauli N) ≃* Multiplicative (ZMod 4) where
  toFun g := Multiplicative.ofAdd g.val.central
  invFun s := ⟨BilinearExtension.ofCenter s.toAdd, (Pauli.mem_center_iff _).mpr rfl⟩
  left_inv g := by
    apply Subtype.ext
    apply BilinearExtension.ext
    · exact ((Pauli.mem_center_iff _).mp g.property).symm
    · rfl
  right_inv _ := rfl
  map_mul' g h := by
    change Multiplicative.ofAdd (g.val.central + h.val.central +
      pauliCocycle N g.val.label h.val.label) =
      Multiplicative.ofAdd (g.val.central + h.val.central)
    rw [(Pauli.mem_center_iff _).mp g.property]
    simp

end
end Char2Theta

/-! ## Heisenberg groups with centers C₂ and C₄ (§1.2) -/

namespace Char2Theta
namespace Heisenberg₂

variable {W : Type*} [AddCommGroup W] [Module F₂ W]

/-- The cocycle of `H(B)` is the additive map underlying the bilinear form. -/
def cocycle (B : LinearMap.BilinForm F₂ W) : W →+ W →+ F₂ where
  toFun v := (B v).toAddMonoidHom
  map_zero' := by ext; simp
  map_add' := by intros; ext; simp

abbrev H (B : LinearMap.BilinForm F₂ W) := BilinearExtension (cocycle B)

/-- Reuse mathlib's quadratic form associated to a bilinear form. No division by two. -/
abbrev Q (B : LinearMap.BilinForm F₂ W) : QuadraticForm F₂ W := B.toQuadraticMap

@[simp] theorem Q_apply (B : LinearMap.BilinForm F₂ W) (v : W) : Q B v = B v v := rfl

/-- Polarization is valid in characteristic two. -/
theorem polar_Q (B : LinearMap.BilinForm F₂ W) (v w : W) :
    QuadraticMap.polar (Q B) v w = B v w + B w v :=
  LinearMap.BilinMap.polar_toQuadraticMap (B := B) v w

lemma add_self (v : W) : v + v = 0 := by
  calc
    v + v = (1 + 1 : F₂) • v := by simp [add_smul]
    _ = 0 := by rw [show (1 + 1 : F₂) = 0 by decide, zero_smul]

/-- Squaring remembers the quadratic refinement, not just its alternating polarization. -/
theorem square (B : LinearMap.BilinForm F₂ W) (g : H B) :
    g ^ 2 = BilinearExtension.ofCenter (Q B g.label) := by
  rw [pow_two]
  ext <;> simp [add_self, cocycle]

/-- The commutator depends only on the alternating polarization. -/
theorem commutator (B : LinearMap.BilinForm F₂ W) (g h : H B) :
    g * h * g⁻¹ * h⁻¹ = BilinearExtension.ofCenter
      (B g.label h.label + B h.label g.label) := by
  rw [BilinearExtension.commutator]
  congr 1
  exact CharTwo.sub_eq_add _ _

/-- Nondegeneracy of the alternating polarization makes the center exactly the zero labels. -/
theorem mem_center_iff (B : LinearMap.BilinForm F₂ W)
    (hnd : ∀ v, (∀ w, B v w + B w v = 0) → v = 0) (g : H B) :
    g ∈ Subgroup.center (H B) ↔ g.label = 0 := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro hg
    apply hnd
    intro w
    have hc : Commute g (⟨w, 0⟩ : H B) := (hg ⟨w, 0⟩).symm
    have he := (BilinearExtension.commute_iff _ _).mp hc
    change B g.label w = B w g.label at he
    rw [he, CharTwo.add_self_eq_zero]
  · intro hg h
    have : g = BilinearExtension.ofCenter g.central := by ext <;> simp [hg]
    rw [this]
    exact (BilinearExtension.ofCenter_commute _ _).symm

/-- Any center-fixing automorphism with induced label map `g` preserves `Q`.
The compatibility hypothesis states explicitly what “induced on labels” means. -/
theorem automorphism_preserves_Q (B : LinearMap.BilinForm F₂ W)
    (α : H B ≃* H B) (g : W ≃ₗ[F₂] W)
    (hcenter : ∀ t, α (BilinearExtension.ofCenter t) = BilinearExtension.ofCenter t)
    (hlabel : ∀ h, (α h).label = g h.label) (v : W) :
    Q B (g v) = Q B v := by
  have h := map_pow α (⟨v, 0⟩ : H B) 2
  rw [square, hcenter, square] at h
  have hc := congrArg BilinearExtension.central h
  simpa [hlabel] using hc.symm

/-- Pack the previous result as mathlib's isometry equivalence of quadratic forms. -/
def quadraticIsometry (B : LinearMap.BilinForm F₂ W)
    (α : H B ≃* H B) (g : W ≃ₗ[F₂] W)
    (hcenter : ∀ t, α (BilinearExtension.ofCenter t) = BilinearExtension.ofCenter t)
    (hlabel : ∀ h, (α h).label = g h.label) : (Q B).IsometryEquiv (Q B) :=
  { g with map_app' := automorphism_preserves_Q B α g hcenter hlabel }

/-- A quadratic isometry preserves the polar alternating form. This is the
inclusion `O(Q) ⊆ Sp(W)` used in §1.2, expressed without changing coordinates. -/
theorem preserves_polar (B : LinearMap.BilinForm F₂ W)
    (g : (Q B).IsometryEquiv (Q B)) (v w : W) :
    B (g v) (g w) + B (g w) (g v) = B v w + B w v := by
  rw [← polar_Q, ← polar_Q]
  unfold QuadraticMap.polar
  rw [← map_add, g.map_app, g.map_app, g.map_app]

/-- The anisotropic binary plane, expressed using mathlib's matrix quadratic form. -/
def anisotropicPlaneQ : QuadraticForm F₂ (Fin 2 → F₂) :=
  ( !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F₂).toQuadraticForm'

/-- Its value is one on each of the three nonzero vectors. -/
theorem anisotropicPlaneQ_value (x : Fin 2 → F₂) :
    anisotropicPlaneQ x = if x = 0 then 0 else 1 := by
  revert x
  decide

/-- In particular every symplectic transformation in dimension two preserves
this anisotropic form: in fact every invertible linear transformation does. -/
theorem anisotropicPlaneQ_invariant (g : (Fin 2 → F₂) ≃ₗ[F₂] (Fin 2 → F₂))
    (x : Fin 2 → F₂) : anisotropicPlaneQ (g x) = anisotropicPlaneQ x := by
  simp only [anisotropicPlaneQ_value, g.map_eq_zero_iff]

end Heisenberg₂
end Char2Theta

/-! ## The induced orthogonal action in §1.2

Construct the label map from a center-fixing automorphism itself, removing the
need to supply a separate compatible linear map to `quadraticIsometry`.
-/
namespace Char2Theta.Heisenberg₂
open BilinearExtension
variable {W : Type*} [AddCommGroup W] [Module F₂ W]
variable (B : LinearMap.BilinForm F₂ W)

private def rep (v : W) : H B := ⟨v, 0⟩

private theorem label_from_rep (α : H B ≃* H B)
    (hcenter : ∀ t, α (ofCenter t) = ofCenter t) (x : H B) :
    (α (rep B x.label)).label = (α x).label := by
  have hx : x = ofCenter x.central * rep B x.label := by
    apply BilinearExtension.ext <;> simp [rep]
  conv_rhs => rw [hx, map_mul, hcenter]
  simp

/-- Additive action on labels, obtained directly from the group automorphism. -/
def inducedLabelMap (α : H B ≃* H B)
    (hcenter : ∀ t, α (ofCenter t) = ofCenter t) : W →ₗ[F₂] W :=
  ({ toFun := fun v => (α (rep B v)).label
     map_zero' := by change (α 1).label = 0; simp
     map_add' := by
       intro v w
       have h := label_from_rep B α hcenter (rep B v * rep B w)
       rw [map_mul] at h
       exact h } : W →+ W).toZModLinearMap 2

@[simp] theorem inducedLabelMap_label (α : H B ≃* H B)
    (hcenter : ∀ t, α (ofCenter t) = ofCenter t) (x : H B) :
    inducedLabelMap B α hcenter x.label = (α x).label := label_from_rep B α hcenter x

private theorem inverse_fixes_center (α : H B ≃* H B)
    (hcenter : ∀ t, α (ofCenter t) = ofCenter t) (t : F₂) :
    α.symm (ofCenter t) = ofCenter t := by
  apply α.injective
  rw [α.apply_symm_apply, hcenter]

/-- The induced action is a linear equivalence, with inverse induced by `α⁻¹`. -/
def inducedLabelEquiv (α : H B ≃* H B)
    (hcenter : ∀ t, α (ofCenter t) = ofCenter t) : W ≃ₗ[F₂] W where
  __ := inducedLabelMap B α hcenter
  invFun := inducedLabelMap B α.symm (inverse_fixes_center B α hcenter)
  left_inv v := by
    change inducedLabelMap B α.symm _ (α (rep B v)).label = v
    rw [inducedLabelMap_label, α.symm_apply_apply]
    rfl
  right_inv v := by
    change inducedLabelMap B α hcenter (α.symm (rep B v)).label = v
    rw [inducedLabelMap_label, α.apply_symm_apply]
    rfl

/-- Every center-fixing automorphism canonically induces an element of `O(Q)`.
No compatible label action is an extra input. -/
def inducedQuadraticIsometry (α : H B ≃* H B)
    (hcenter : ∀ t, α (ofCenter t) = ofCenter t) : (Q B).IsometryEquiv (Q B) :=
  quadraticIsometry B α (inducedLabelEquiv B α hcenter) hcenter
    (fun x => (inducedLabelMap_label B α hcenter x).symm)

/-- In particular, the canonically induced label action preserves the polarization. -/
theorem inducedLabelEquiv_preserves_polar (α : H B ≃* H B)
    (hcenter : ∀ t, α (ofCenter t) = ofCenter t) (v w : W) :
    B (inducedLabelEquiv B α hcenter v) (inducedLabelEquiv B α hcenter w) +
      B (inducedLabelEquiv B α hcenter w) (inducedLabelEquiv B α hcenter v) = B v w + B w v :=
  preserves_polar B (inducedQuadraticIsometry B α hcenter) v w

end Char2Theta.Heisenberg₂

/-! ## Center-fixing Pauli automorphisms and their action on labels

The label action is constructed from the automorphism, rather than supplied as
an additional hypothesis. The symplectic form is the commutator pairing.
-/

namespace Char2Theta
noncomputable section
open BilinearExtension

/-- Automorphisms fixing the central fourth roots pointwise. -/
def PauliAut (N : ℕ) : Subgroup (MulAut (Pauli N)) where
  carrier := {α | ∀ s, α (ofCenter s) = ofCenter s}
  one_mem' := fun _ => rfl
  mul_mem' := by intro α β hα hβ s; change α (β _) = _; rw [hβ, hα]
  inv_mem' := by
    intro α hα s
    change α.symm (ofCenter s) = ofCenter s
    apply α.injective
    rw [α.apply_symm_apply, hα]

/-- The symplectic group on the label space, as a subgroup of mathlib's linear
automorphism group. This uses the coordinates `(a,b)` of the original Pauli model. -/
def LabelSymplectic (N : ℕ) : Subgroup (Labels N ≃ₗ[F₂] Labels N) where
  carrier := {g | ∀ v w, binarySymplectic (g v) (g w) = binarySymplectic v w}
  one_mem' := fun _ _ => rfl
  mul_mem' := by intro g h hg hh v w; exact (hg _ _).trans (hh _ _)
  inv_mem' := by
    intro g hg v w
    have := hg (g.symm v) (g.symm w)
    simpa using this.symm

namespace PauliAut
variable {N : ℕ}

/-- A standard representative of a label. -/
def rep (v : Labels N) : Pauli N := ⟨v, 0⟩

@[simp] theorem rep_label (v : Labels N) : (rep v).label = v := rfl

theorem map_label (α : PauliAut N) (g : Pauli N) :
    (α.val g).label = (α.val (rep g.label)).label := by
  have hg : g = ofCenter g.central * rep g.label := by ext <;> simp [rep]
  rw [hg, map_mul, α.property]
  simp [rep]

/-- The induced additive action on `P_N/Z(P_N)`. -/
def labelAddHom (α : PauliAut N) : Labels N →+ Labels N where
  toFun v := (α.val (rep v)).label
  map_zero' := by change (α.val 1).label = 0; simp
  map_add' v w := by
    have h := map_label α (rep v * rep w)
    rw [map_mul] at h
    exact h.symm

@[simp] theorem labelAddHom_apply (α : PauliAut N) (v : Labels N) :
    labelAddHom α v = (α.val (rep v)).label := rfl

@[simp] theorem labelAddHom_label (α : PauliAut N) (g : Pauli N) :
    labelAddHom α g.label = (α.val g).label := (map_label α g).symm

/-- Additivity over the prime field is automatically linearity. -/
def labelLinear (α : PauliAut N) : Labels N →ₗ[F₂] Labels N :=
  (labelAddHom α).toZModLinearMap 2

@[simp] theorem labelLinear_label (α : PauliAut N) (g : Pauli N) :
    labelLinear α g.label = (α.val g).label := labelAddHom_label α g

@[simp] theorem labelLinear_mul (α β : PauliAut N) (v : Labels N) :
    labelLinear (α * β) v = labelLinear α (labelLinear β v) := by
  exact (labelAddHom_label α (β.val (rep v))).symm

@[simp] theorem labelLinear_one (v : Labels N) : labelLinear (1 : PauliAut N) v = v := rfl

/-- An actual linear automorphism, including its induced inverse. -/
def labelEquiv (α : PauliAut N) : Labels N ≃ₗ[F₂] Labels N where
  __ := labelLinear α
  invFun := labelLinear α⁻¹
  left_inv v := by
    change labelLinear α⁻¹ (labelLinear α v) = v
    rw [← labelLinear_mul, inv_mul_cancel, labelLinear_one]
  right_inv v := by
    change labelLinear α (labelLinear α⁻¹ v) = v
    rw [← labelLinear_mul, mul_inv_cancel, labelLinear_one]

/-- The Pauli commutator records the full alternating pairing. -/
theorem commutator_formula (g h : Pauli N) :
    g * h * g⁻¹ * h⁻¹ = ofCenter (twoLift (binarySymplectic g.label h.label)) := by
  rw [BilinearExtension.commutator]
  congr 1
  change twoLift (dot g.label.2 h.label.1) - twoLift (dot h.label.2 g.label.1) = _
  rw [← map_sub]
  congr 1
  simp [binarySymplectic, CharTwo.sub_eq_add, dotProduct_comm, add_comm]

theorem labelEquiv_preserves (α : PauliAut N) (v w : Labels N) :
    binarySymplectic (labelEquiv α v) (labelEquiv α w) = binarySymplectic v w := by
  apply twoLift_injective
  have h := congrArg α.val (commutator_formula (rep v) (rep w))
  simp only [map_mul, map_inv] at h
  rw [α.property] at h
  rw [commutator_formula] at h
  exact congrArg BilinearExtension.central h

/-- The natural action on the symplectic label space. -/
def toSymplectic (N : ℕ) : PauliAut N →* LabelSymplectic N where
  toFun α := ⟨labelEquiv α, labelEquiv_preserves α⟩
  map_one' := by apply Subtype.ext; apply LinearEquiv.ext; intro v; rfl
  map_mul' α β := by apply Subtype.ext; apply LinearEquiv.ext; intro v; exact labelLinear_mul α β v

end PauliAut
end
end Char2Theta

/-! ## The kernel of the symplectic action -/

namespace Char2Theta
noncomputable section
open BilinearExtension

namespace PauliAut
variable {N : ℕ}

/-- Inner conjugation fixes the center pointwise. -/
def conjugation (N : ℕ) : Pauli N →* PauliAut N :=
  (MulAut.conj : Pauli N →* MulAut (Pauli N)).codRestrict (PauliAut N) (by
    intro x s
    change x * ofCenter s * x⁻¹ = ofCenter s
    rw [(ofCenter_commute s x).eq.symm, mul_inv_cancel_right])

/-- The central-coordinate formula for inner conjugation. -/
theorem conjugation_formula (x y : Pauli N) :
    (conjugation N x).val y =
      ⟨y.label, y.central + twoLift (binarySymplectic x.label y.label)⟩ := by
  have h := commutator_formula x y
  have hh := congrArg (· * y) h
  simp only [inv_mul_cancel_right] at hh
  change x * y * x⁻¹ = _
  rw [hh]
  apply BilinearExtension.ext
  · simp
  · simp [add_comm]

/-- The inner action depends only on the label, not on its central lift. -/
def inner (N : ℕ) : Multiplicative (Labels N) →* PauliAut N where
  toFun v := conjugation N (rep v.toAdd)
  map_one' := by change conjugation N 1 = 1; exact map_one _
  map_mul' v w := by
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    change (conjugation N (rep (v.toAdd + w.toAdd))).val x =
      ((conjugation N (rep v.toAdd) * conjugation N (rep w.toAdd))).val x
    rw [← map_mul]
    simp only [conjugation_formula, rep_label, mul_label]

@[simp] theorem inner_apply (v : Multiplicative (Labels N)) (x : Pauli N) :
    (inner N v).val x =
      ⟨x.label, x.central + twoLift (binarySymplectic v.toAdd x.label)⟩ :=
  conjugation_formula _ _

/-- Nondegeneracy of the binary alternating form, checked against coordinate vectors. -/
theorem pairing_nondegenerate (v : Labels N)
    (hv : ∀ w, binarySymplectic v w = 0) : v = 0 := by
  apply Prod.ext
  · funext i
    simpa [binarySymplectic] using hv (0, Pi.single i 1)
  · funext i
    simpa [binarySymplectic] using hv (Pi.single i 1, 0)

theorem inner_injective (N : ℕ) : Function.Injective (inner N) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm
  · intro v hv
    have h : inner N v = 1 := hv
    have hz : v.toAdd = 0 := pairing_nondegenerate _ (by
      intro w
      have hc := congrArg (fun α : PauliAut N => (α.val (rep w)).central) h
      simp only [inner_apply] at hc
      change 0 + twoLift (binarySymplectic v.toAdd w) = 0 at hc
      exact twoLift_injective (by simpa using hc))
    exact hz
  · exact bot_le

/-- Every linear functional is pairing against a unique label. -/
theorem exists_pairing (f : Labels N →ₗ[F₂] F₂) :
    ∃ v, ∀ w, binarySymplectic v w = f w := by
  classical
  let v : Labels N := (fun i => f (0, Pi.single i 1), fun i => f (Pi.single i 1, 0))
  refine ⟨v, fun w => ?_⟩
  have hw : w = (∑ i : Fin N, w.1 i • (Pi.single i 1, (0 : Bits N))) +
      ∑ i : Fin N, w.2 i • ((0 : Bits N), Pi.single i 1) := by
    apply Prod.ext <;> funext j <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  rw [hw, map_add, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]
  change binarySymplectic v _ = _
  rw [← hw]
  simp only [binarySymplectic, dot, dotProduct, v]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

private theorem two_torsion (s : ZMod 4) : s + s = 0 ↔ ∃ t, twoLift t = s := by
  fin_cases s <;> decide

/-- A label-trivial automorphism is inner. -/
theorem mem_ker_iff_inner (α : PauliAut N) :
    toSymplectic N α = 1 ↔ ∃ v, inner N v = α := by
  constructor
  · intro hα
    have hl (x : Pauli N) : (α.val x).label = x.label := by
      have h := congrArg (fun g : LabelSymplectic N => g.val x.label) hα
      change labelLinear α x.label = x.label at h
      rwa [labelLinear_label] at h
    let δ : Labels N →+ ZMod 4 :=
      { toFun := fun v => (α.val (rep v)).central
        map_zero' := by change (α.val 1).central = 0; simp
        map_add' := by
          intro v w
          have h : rep v * rep w = ofCenter (pauliCocycle N v w) * rep (v + w) := by
            apply BilinearExtension.ext <;> simp [rep]
          have hh := congrArg (fun x => (α.val x).central) h
          simp only [map_mul] at hh
          rw [α.property] at hh
          simp only [mul_central, hl, ofCenter_label,
            ofCenter_central, rep_label, map_zero, AddMonoidHom.zero_apply, add_zero] at hh
          linear_combination -hh }
    have hδ (v : Labels N) : ∃ t, twoLift t = δ v := by
      apply (two_torsion _).mp
      rw [← map_add]
      have hv : v + v = 0 := by ext <;> apply CharTwo.add_self_eq_zero
      rw [hv, map_zero]
    let f : Labels N →+ F₂ :=
      { toFun := fun v => (hδ v).choose
        map_zero' := by
          apply twoLift_injective
          rw [(hδ 0).choose_spec, map_zero, map_zero]
        map_add' := by
          intro v w
          apply twoLift_injective
          rw [(hδ (v + w)).choose_spec, twoLift.map_add, (hδ v).choose_spec,
            (hδ w).choose_spec, δ.map_add] }
    obtain ⟨v, hv⟩ := exists_pairing (f.toZModLinearMap 2)
    refine ⟨Multiplicative.ofAdd v, ?_⟩
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    rw [inner_apply]
    apply BilinearExtension.ext
    · exact (hl x).symm
    · change x.central + twoLift (binarySymplectic v x.label) = (α.val x).central
      rw [hv]
      have hx : x = ofCenter x.central * rep x.label := by
        apply BilinearExtension.ext <;> simp [rep]
      have he : twoLift ((f.toZModLinearMap 2) x.label) = δ x.label :=
        (hδ x.label).choose_spec
      rw [he]
      conv_rhs => rw [hx, map_mul, α.property]
      simp [δ]
  · rintro ⟨v, rfl⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    change ((inner N v).val (rep w)).label = w
    rw [inner_apply]
    rfl

/-- Exactness at the center-fixing automorphism group. -/
theorem inner_range_eq_ker (N : ℕ) : (inner N).range = (toSymplectic N).ker := by
  ext α
  exact (mem_ker_iff_inner α).symm

end PauliAut
end
end Char2Theta

/-! ## Identification with mathlib's standard matrix symplectic group -/
namespace Char2Theta
noncomputable section
open Module

/-- The ordered coordinate basis, translation coordinates followed by modulation coordinates. -/
def labelBasis (N : ℕ) : Basis (Fin N ⊕ Fin N) F₂ (Labels N) :=
  (Pi.basisFun F₂ (Fin N)).prod (Pi.basisFun F₂ (Fin N))

/-- The commutator pairing bundled as a mathlib bilinear form. -/
def binaryForm (N : ℕ) : LinearMap.BilinForm F₂ (Labels N) where
  toFun v :=
    { toFun := binarySymplectic v
      map_add' := by intros; simp [binarySymplectic, dotProduct_add, add_dotProduct]; ring
      map_smul' := by intros; simp [binarySymplectic, dotProduct_smul, smul_dotProduct, mul_add] }
  map_add' v w := by
    apply LinearMap.ext; intro u
    change binarySymplectic (v + w) u = binarySymplectic v u + binarySymplectic w u
    simp [binarySymplectic, dotProduct_add, add_dotProduct]; ring
  map_smul' c v := by
    apply LinearMap.ext; intro u
    change binarySymplectic (c • v) u = c * binarySymplectic v u
    simp [binarySymplectic, dotProduct_smul, smul_dotProduct, mul_add]

/-- In characteristic two the commutator form has exactly mathlib's standard `J` matrix. -/
theorem binaryForm_matrix (N : ℕ) :
    LinearMap.BilinForm.toMatrix (labelBasis N) (binaryForm N) = Matrix.J (Fin N) F₂ := by
  ext i j
  cases i <;> cases j <;>
    simp [LinearMap.BilinForm.toMatrix_apply, labelBasis, binaryForm, binarySymplectic,
      Matrix.J, Matrix.fromBlocks, Pi.basisFun_apply, CharTwo.neg_eq, eq_comm,
      Matrix.one_apply, Pi.single_apply]

/-- Preservation of the original pairing is precisely the standard matrix condition. -/
theorem preserves_iff_matrix {N : ℕ} (l : Module.End F₂ (Labels N)) :
    (∀ v w, binarySymplectic (l v) (l w) = binarySymplectic v w) ↔
    LinearMap.toMatrix (labelBasis N) (labelBasis N) l ∈ Matrix.symplecticGroup (Fin N) F₂ := by
  rw [SymplecticGroup.mem_iff']
  have hcomp := LinearMap.BilinForm.toMatrix_comp (labelBasis N) (labelBasis N)
    (binaryForm N) l l
  rw [binaryForm_matrix] at hcomp
  rw [← hcomp, ← binaryForm_matrix]
  constructor
  · intro h
    congr 1
    apply LinearMap.ext; intro v
    apply LinearMap.ext; intro w
    exact h v w
  · intro h v w
    have he := (LinearMap.BilinForm.toMatrix (labelBasis N)).injective h
    exact LinearMap.congr_fun (LinearMap.congr_fun he v) w

/-- The symplectic matrix of a label automorphism in the standard basis. -/
def labelSymplecticToMatrix (N : ℕ) :
    LabelSymplectic N →* Matrix.symplecticGroup (Fin N) F₂ where
  toFun g := ⟨LinearMap.toMatrix (labelBasis N) (labelBasis N) g.val.toLinearMap,
    (preserves_iff_matrix _).mp g.property⟩
  map_one' := by apply Subtype.ext; exact LinearMap.toMatrix_one _
  map_mul' g h := by
    apply Subtype.ext
    exact LinearMap.toMatrix_mul (labelBasis N) g.val.toLinearMap h.val.toLinearMap

private def matrixLabelEquiv {N : ℕ} (A : Matrix.symplecticGroup (Fin N) F₂) :
    Labels N ≃ₗ[F₂] Labels N where
  __ := Matrix.toLinAlgEquiv (labelBasis N) A.val
  invFun := Matrix.toLinAlgEquiv (labelBasis N) (A⁻¹).val
  left_inv v := by
    have h : (Matrix.toLinAlgEquiv (labelBasis N) (A⁻¹).val) *
        (Matrix.toLinAlgEquiv (labelBasis N) A.val) = 1 := by
      rw [← map_mul, ← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one, map_one]
    exact LinearMap.congr_fun h v
  right_inv v := by
    have h : (Matrix.toLinAlgEquiv (labelBasis N) A.val) *
        (Matrix.toLinAlgEquiv (labelBasis N) (A⁻¹).val) = 1 := by
      rw [← map_mul, ← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one, map_one]
    exact LinearMap.congr_fun h v

/-- A group isomorphism to the existing mathlib symplectic matrix group. -/
def labelSymplecticMatrixEquiv (N : ℕ) :
    LabelSymplectic N ≃* Matrix.symplecticGroup (Fin N) F₂ := by
  apply MulEquiv.ofBijective (labelSymplecticToMatrix N)
  constructor
  · intro g h he
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    exact (LinearMap.toMatrix (labelBasis N) (labelBasis N)).injective (congrArg Subtype.val he)
  · intro A
    have hm : LinearMap.toMatrix (labelBasis N) (labelBasis N) (matrixLabelEquiv A).toLinearMap =
        A.val := (LinearMap.toMatrixAlgEquiv (labelBasis N)).apply_symm_apply A.val
    refine ⟨⟨matrixLabelEquiv A, (preserves_iff_matrix _).mpr (hm ▸ A.property)⟩, ?_⟩
    exact Subtype.ext hm

end
end Char2Theta

/-! ## Lifting symplectic transformations to Pauli automorphisms

The difference of the two cocycles is symmetric. Its commutative central
extension admits an extension of the central character, by mathlib's Baer
criterion for divisible abelian groups. Since the extension has exponent four,
this character takes fourth-root values. This supplies the required correction
without choosing a symplectic generating set.
-/

namespace Char2Theta
noncomputable section
open BilinearExtension

/-- The faithful fourth-root character as a homomorphism into complex units. -/
def phaseUnits : Multiplicative (ZMod 4) →* ℂˣ where
  toFun s := Units.mk0 (phase s.toAdd) (phase_ne_zero _)
  map_one' := Units.ext phase_zero
  map_mul' s t := Units.ext (phase_add s.toAdd t.toAdd)

@[simp] theorem phaseUnits_val (s : ZMod 4) :
    (phaseUnits (Multiplicative.ofAdd s) : ℂ) = phase s := rfl

/-- Every fourth root is one of the four central phases. -/
def phaseRootsEquiv : Multiplicative (ZMod 4) ≃* rootsOfUnity 4 ℂ := by
  letI : Fintype (rootsOfUnity 4 ℂ) := Fintype.ofFinite _
  let f : Multiplicative (ZMod 4) →* rootsOfUnity 4 ℂ :=
    { toFun := fun s => ⟨phaseUnits s, by
        rw [mem_rootsOfUnity]
        have h : s ^ 4 = 1 := by
          have hz : (4 : ℕ) • s.toAdd = 0 := by
            rw [nsmul_eq_mul]
            exact zero_mul _
          exact congrArg Multiplicative.ofAdd hz
        rw [← map_pow, h, map_one]⟩
      map_one' := Subtype.ext (map_one phaseUnits)
      map_mul' := fun s t => Subtype.ext (map_mul phaseUnits s t) }
  apply MulEquiv.ofBijective f
  apply (Fintype.bijective_iff_injective_and_card f).mpr
  constructor
  · intro s t h
    apply Multiplicative.ofAdd.injective
    exact phase_injective (congrArg (fun z : rootsOfUnity 4 ℂ => (z.val : ℂ)) h)
  · simp only [Fintype.card_multiplicative, ZMod.card]
    rw [← Nat.card_eq_fintype_card, Complex.card_rootsOfUnity]

namespace PauliAut
variable {N : ℕ}

/-- Difference between the pulled-back cocycle and the original cocycle. -/
def cocycleDifference (g : LabelSymplectic N) : Labels N →+ Labels N →+ ZMod 4 where
  toFun v :=
    { toFun := fun w => pauliCocycle N (g.val v) (g.val w) - pauliCocycle N v w
      map_zero' := by simp
      map_add' := by intros; simp [map_add, sub_add_sub_comm] }
  map_zero' := by ext; simp
  map_add' := by intros; ext; simp [map_add, sub_add_sub_comm]

theorem cocycleDifference_symmetric (g : LabelSymplectic N) (v w : Labels N) :
    cocycleDifference g v w = cocycleDifference g w v := by
  have h := congrArg twoLift (g.property v w)
  simp only [binarySymplectic, map_add] at h
  change twoLift (dot (g.val v).2 (g.val w).1) - twoLift (dot v.2 w.1) =
    twoLift (dot (g.val w).2 (g.val v).1) - twoLift (dot w.2 v.1)
  dsimp only [dot] at h ⊢
  rw [dotProduct_comm (g.val v).1, dotProduct_comm v.1,
    dotProduct_comm (g.val w).1, dotProduct_comm w.1] at h
  have hc (x : F₂) : -twoLift x = twoLift x := by
    rw [← map_neg]; congr 1; exact CharTwo.neg_eq x
  simp only [sub_eq_add_neg, hc]
  have ht (x : F₂) : twoLift x + twoLift x = 0 := by
    rw [← map_add]; simp [CharTwo.add_self_eq_zero]
  linear_combination h - ht (dot (g.val w).2 (g.val v).1) + ht (dot v.2 w.1)

/-- The symmetric difference defines an abelian extension. -/
@[implicit_reducible] def differenceCommGroup (g : LabelSymplectic N) :
    CommGroup (BilinearExtension (cocycleDifference g)) where
  mul_comm x y := by
    apply BilinearExtension.ext
    · exact add_comm _ _
    · simp only [mul_central, cocycleDifference_symmetric g x.label y.label]
      abel

/-- Every element of this auxiliary extension has fourth power one. -/
theorem difference_pow_four (g : LabelSymplectic N)
    (x : BilinearExtension (cocycleDifference g)) : x ^ 4 = 1 := by
  have hv : x.label + x.label = 0 := by ext <;> apply CharTwo.add_self_eq_zero
  have hC : cocycleDifference g x.label x.label +
      cocycleDifference g x.label x.label = 0 := by
    simp only [← map_add, hv, map_zero]
  have hz (s : ZMod 4) : s + s + s + s = 0 := by fin_cases s <;> decide
  change x ^ (2 * 2) = 1
  rw [pow_mul, pow_two, pow_two]
  apply BilinearExtension.ext
  · simp [hv]
  · simp only [mul_central, mul_label, hv, map_zero,
      one_central, add_zero]
    linear_combination hz x.central + hC

/-- The central correction required to lift any symplectic transformation exists. -/
theorem exists_correction (g : LabelSymplectic N) :
    ∃ q : Labels N → ZMod 4, q 0 = 0 ∧ ∀ v w,
      q (v + w) = q v + q w + cocycleDifference g v w := by
  let E := BilinearExtension (cocycleDifference g)
  letI : CommGroup E := differenceCommGroup g
  let i : Multiplicative (ZMod 4) →* E := centerHom
  have hi : Function.Injective i := by
    intro s t h
    exact congrArg (fun x : E => Multiplicative.ofAdd x.central) h
  obtain ⟨ψ, hψ⟩ := extend_unit_character i hi phaseUnits
  have hcenter (s : ZMod 4) : ψ (ofCenter s) = phaseUnits (Multiplicative.ofAdd s) :=
    DFunLike.congr_fun hψ (Multiplicative.ofAdd s)
  let ψ₄ : E →* rootsOfUnity 4 ℂ :=
    { toFun := fun x => ⟨ψ x, by rw [mem_rootsOfUnity, ← map_pow, difference_pow_four, map_one]⟩
      map_one' := Subtype.ext (map_one ψ)
      map_mul' := fun x y => Subtype.ext (map_mul ψ x y) }
  let f : E →* Multiplicative (ZMod 4) := phaseRootsEquiv.symm.toMonoidHom.comp ψ₄
  have hf (s : ZMod 4) : f (ofCenter s) = Multiplicative.ofAdd s := by
    apply phaseRootsEquiv.injective
    change phaseRootsEquiv (phaseRootsEquiv.symm (ψ₄ (ofCenter s))) = _
    rw [phaseRootsEquiv.apply_symm_apply]
    exact Subtype.ext (hcenter s)
  let q : Labels N → ZMod 4 := fun v => -(f ⟨v, 0⟩).toAdd
  refine ⟨q, ?_, ?_⟩
  · change -(f 1).toAdd = 0
    simp
  · intro v w
    have he : (⟨v, 0⟩ : E) * ⟨w, 0⟩ =
        ofCenter (cocycleDifference g v w) * ⟨v + w, 0⟩ := by ext <;> simp
    have hh := congrArg Multiplicative.toAdd (congrArg f he)
    simp only [map_mul, hf] at hh
    change (f ⟨v, 0⟩).toAdd + (f ⟨w, 0⟩).toAdd =
      cocycleDifference g v w + (f ⟨v + w, 0⟩).toAdd at hh
    dsimp [q]
    linear_combination hh

/-- A correction gives a genuine automorphism of the original Pauli group. -/
def ofCorrection (g : LabelSymplectic N) (q : Labels N → ZMod 4) (hq0 : q 0 = 0)
    (hq : ∀ v w, q (v + w) = q v + q w + cocycleDifference g v w) : PauliAut N :=
  ⟨{ toFun := fun x => ⟨g.val x.label, x.central + q x.label⟩
     invFun := fun x => ⟨g.val.symm x.label, x.central - q (g.val.symm x.label)⟩
     left_inv := by intro x; ext <;> simp
     right_inv := by intro x; ext <;> simp
     map_mul' := by
       intro x y
       apply BilinearExtension.ext
       · exact map_add g.val _ _
       · simp only [mul_central, mul_label, hq]
         change _ = _ + _ + pauliCocycle N (g.val x.label) (g.val y.label)
         dsimp [cocycleDifference]
         abel }, by intro s; ext <;> simp [hq0]⟩

/-- Surjectivity onto the entire symplectic group, with no lifting assumption. -/
theorem toSymplectic_surjective (N : ℕ) : Function.Surjective (toSymplectic N) := by
  intro g
  obtain ⟨q, hq0, hq⟩ := exists_correction g
  refine ⟨ofCorrection g q hq0 hq, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  rfl

/-- Conversely, every center-fixing automorphism has exactly the label-plus-central-
correction form used in §1.2. The correction identity follows from its group law. -/
theorem exists_correction_description (α : PauliAut N) :
    ∃ (q : Labels N → ZMod 4) (hq0 : q 0 = 0)
      (hq : ∀ v w, q (v + w) = q v + q w + cocycleDifference (toSymplectic N α) v w),
      ofCorrection (toSymplectic N α) q hq0 hq = α := by
  let q : Labels N → ZMod 4 := fun v => (α.val (rep v)).central
  have hq0 : q 0 = 0 := by change (α.val 1).central = 0; simp
  have hq : ∀ v w, q (v + w) = q v + q w + cocycleDifference (toSymplectic N α) v w := by
    intro v w
    have h : rep v * rep w = ofCenter (pauliCocycle N v w) * rep (v + w) := by
      apply BilinearExtension.ext <;> simp [rep]
    have hh := congrArg (fun x => (α.val x).central) h
    simp only [map_mul] at hh
    rw [α.property] at hh
    simp only [mul_central, ofCenter_central, ofCenter_label, map_zero,
      AddMonoidHom.zero_apply, add_zero] at hh
    change q v + q w + pauliCocycle N ((labelEquiv α) v) ((labelEquiv α) w) =
      pauliCocycle N v w + q (v + w) at hh
    change q (v + w) = q v + q w +
      (pauliCocycle N ((labelEquiv α) v) ((labelEquiv α) w) - pauliCocycle N v w)
    linear_combination -hh
  refine ⟨q, hq0, hq, ?_⟩
  apply Subtype.ext; apply MulEquiv.ext
  intro x
  apply BilinearExtension.ext
  · exact labelLinear_label α x
  · change x.central + q x.label = (α.val x).central
    have hx : x = ofCenter x.central * rep x.label := by
      apply BilinearExtension.ext <;> simp [rep]
    conv_rhs => rw [hx, map_mul, α.property]
    simp [q]

end PauliAut
end
end Char2Theta

/-! ## The commutant and uniqueness of the finite Pauli representation -/

namespace Char2Theta
noncomputable section
open BilinearExtension PauliAut

namespace Pauli
variable {N : ℕ}

/-- The concrete Pauli matrices as a complex representation. -/
def representation (N : ℕ) : Representation ℂ (Pauli N) (Hilbert N) where
  toFun g := Matrix.toLinAlgEquiv' (matrix g)
  map_one' := by rw [matrix_one, map_one]
  map_mul' g h := by rw [matrix_mul, map_mul]

/-- Only scalar matrices commute with all Pauli operators. -/
theorem commutant_scalar (M : Matrix (Bits N) (Bits N) ℂ)
    (hM : ∀ g : Pauli N, M * matrix g = matrix g * M) :
    M = M 0 0 • 1 := by
  classical
  have hz (b : Bits N) (x y : Bits N) : M x y * sign (dot b y) = sign (dot b x) * M x y := by
    have h := congrArg (fun A : Matrix (Bits N) (Bits N) ℂ => A x y) (hM (rep (0, b)))
    simpa [Matrix.mul_apply, matrix, a, Pauli.b, rep] using h
  have off (x y : Bits N) (hxy : x ≠ y) : M x y = 0 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
    have hs : sign (dot (Pi.single j 1) y) ≠ sign (dot (Pi.single j 1) x) := by
      intro he
      have := sign_injective he
      exact hj (by simpa using this.symm)
    exact (mul_eq_mul_right_iff.mp (by simpa [mul_comm] using hz (Pi.single j 1) x y)).resolve_left hs
  have diagonal : M = Matrix.diagonal (fun x => M x x) := by
    ext x y
    by_cases h : x = y
    · subst y; simp
    · simp [h, off x y h]
  have hd (x : Bits N) : M x x = M 0 0 := by
    have h := congrArg (fun A : Matrix (Bits N) (Bits N) ℂ => A x 0) (hM (rep (x, 0)))
    rw [diagonal] at h
    simpa [Matrix.diagonal_mul, Matrix.mul_diagonal, matrix, a, Pauli.b, rep] using h
  ext x y
  by_cases h : x = y
  · subst y; simpa using hd x
  · simp [h, off x y h]

/-- Central-coordinate translation acts by the expected complex scalar. -/
theorem matrix_shift (v : Labels N) (s t : ZMod 4) :
    matrix (⟨v, s + t⟩ : Pauli N) = phase t • matrix ⟨v, s⟩ := by
  ext x y
  simp only [matrix, a, b, phase_add, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- The character vanishes away from the center. -/
theorem character_eq_zero (x : Pauli N) (hx : x.label ≠ 0) :
    (representation N).character x = 0 := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, binarySymplectic v x.label = 1 := by
    by_contra hn
    push Not at hn
    apply hx
    apply pairing_nondegenerate
    intro v
    have he : binarySymplectic v x.label = 0 := by
      have hh : ∀ t : F₂, t ≠ 1 → t = 0 := by decide
      exact hh _ (hn v)
    simpa [binarySymplectic, add_comm] using he
  have h := (representation N).char_conj x (rep v)
  change LinearMap.trace ℂ _ (Matrix.toLinAlgEquiv' (matrix _)) =
    LinearMap.trace ℂ _ (Matrix.toLinAlgEquiv' (matrix x)) at h
  change LinearMap.trace ℂ _ (matrix _).toLin' = LinearMap.trace ℂ _ (matrix x).toLin' at h
  simp only [Matrix.trace_toLin'_eq] at h
  change (matrix ((conjugation N (rep v)).val x)).trace = (matrix x).trace at h
  rw [conjugation_formula, rep_label, hv, matrix_shift] at h
  simp only [twoLift_one, phase_two, neg_smul, one_smul, Matrix.trace_neg] at h
  change LinearMap.trace ℂ _ (matrix x).toLin' = 0
  rw [Matrix.trace_toLin'_eq]
  linear_combination -h / 2

/-- A center-fixing automorphism leaves the character unchanged. -/
theorem character_aut (α : PauliAut N) (x : Pauli N) :
    (representation N).character (α.val x) = (representation N).character x := by
  by_cases hx : x.label = 0
  · have he : x = ofCenter x.central := BilinearExtension.ext hx rfl
    rw [he, α.property]
  · have hy : (α.val x).label ≠ 0 := by
      intro hy
      apply hx
      have he := labelLinear_label (α⁻¹) (α.val x)
      rw [hy, map_zero] at he
      simpa using he.symm
    rw [character_eq_zero _ hx, character_eq_zero _ hy]

/-- Character theory supplies a nonzero intertwiner for every center-fixing
Pauli automorphism. No irreducibility or equivalence is assumed. -/
theorem exists_intertwiner (α : PauliAut N) :
    ∃ T : Matrix (Bits N) (Bits N) ℂ, T ≠ 0 ∧
      ∀ g : Pauli N, T * matrix g = matrix (α.val g) * T := by
  let ρ := representation N
  let σ : Representation ℂ (Pauli N) (Hilbert N) := ρ.comp α.val.toMonoidHom
  letI : Invertible (Nat.card (Pauli N) : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := Pauli N)).ne')
  have hχ : σ.character = ρ.character := funext (character_aut α)
  have hd : Module.finrank ℂ (Representation.IntertwiningMap ρ σ) =
      Module.finrank ℂ (Representation.IntertwiningMap ρ ρ) := by
    apply Nat.cast_injective (R := ℂ)
    rw [← ρ.card_inv_mul_sum_char_mul_char_eq_finrank σ,
      ← ρ.card_inv_mul_sum_char_mul_char_eq_finrank ρ, hχ]
  have hp : 0 < Module.finrank ℂ (Representation.IntertwiningMap ρ ρ) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨Representation.IntertwiningMap.id ρ, ?_⟩
    intro h
    have := congrArg (fun f : Representation.IntertwiningMap ρ ρ => f (fun _ => 1) 0) h
    simp at this
  obtain ⟨f, hf⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (hd ▸ hp)
  refine ⟨LinearMap.toMatrixAlgEquiv' f.toLinearMap, ?_, ?_⟩
  · intro h
    apply hf
    apply Representation.IntertwiningMap.ext
    apply LinearMap.toMatrixAlgEquiv'.injective
    simpa using h
  · intro g
    apply Matrix.toLinAlgEquiv'.injective
    simp only [map_mul, Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']
    exact f.isIntertwining' g

end Pauli
end
end Char2Theta

/-! ## Conjugation by the concrete Pauli normalizer -/
namespace Char2Theta
noncomputable section
open BilinearExtension

/-- The normalizer action transported along the faithful Pauli realization. -/
def cliffordAut (N : ℕ) : Clifford N →* MulAut (Pauli N) :=
  (MulAut.congr (pauliEquivOperatorGroup N).symm).toMonoidHom.comp
    (Pauli.operatorGroup N).normalizerMonoidHom

theorem cliffordAut_formula {N : ℕ} (U : Clifford N) (g : Pauli N) :
    Pauli.unitaryHom N (cliffordAut N U g) =
      U.val * Pauli.unitaryHom N g * U.val⁻¹ := by
  let e := pauliEquivOperatorGroup N
  change (e (e.symm (_))).val = _
  rw [e.apply_symm_apply]
  rfl

/-- Clifford conjugation fixes the entire central `μ₄` pointwise. -/
theorem cliffordAut_center {N : ℕ} (U : Clifford N) (s : ZMod 4) :
    cliffordAut N U (ofCenter s) = ofCenter s := by
  apply Pauli.matrix_injective
  have h := congrArg Subtype.val (cliffordAut_formula U (ofCenter s))
  change Pauli.matrix _ = U.val.val * Pauli.matrix (ofCenter s) * (U.val⁻¹).val at h
  rw [h, Pauli.matrix_ofCenter]
  simp only [Matrix.mul_smul, mul_one, Matrix.smul_mul, ← Submonoid.coe_mul,
    mul_inv_cancel, OneMemClass.coe_one]

/-- The concrete Clifford action lands in the center-fixing automorphisms. -/
def cliffordAction (N : ℕ) : Clifford N →* PauliAut N :=
  (cliffordAut N).codRestrict (PauliAut N) (fun U => cliffordAut_center U)

/-- All scalar unitary operators, embedded in the concrete Clifford group. -/
def cliffordScalar (N : ℕ) : unitary ℂ →* Clifford N where
  toFun c := ⟨scalarUnitary N c, scalarUnitary_mem_clifford N c⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; simp [scalarUnitary]
  map_mul' c d := by
    apply Subtype.ext; apply Subtype.ext
    change ((c : ℂ) * (d : ℂ)) • 1 = ((c : ℂ) • 1) * ((d : ℂ) • 1)
    simp [smul_smul, mul_comm]

theorem cliffordScalar_injective (N : ℕ) : Function.Injective (cliffordScalar N) :=
  fun _ _ h => scalarUnitary_injective N (congrArg Subtype.val h)

/-- The scalar subgroup used in the projective quotient is exactly `U(1)I`. -/
def cliffordScalars (N : ℕ) : Subgroup (Clifford N) := (cliffordScalar N).range

theorem cliffordScalars_central (N : ℕ) : cliffordScalars N ≤ Subgroup.center (Clifford N) := by
  rintro _ ⟨c, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro U
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp (scalarUnitary_central N c)) U.val

instance (N : ℕ) : (cliffordScalars N).Normal where
  conj_mem x hx U := by
    rw [Subgroup.mem_center_iff.mp (cliffordScalars_central N hx) U, mul_inv_cancel_right]
    exact hx

/-- The projective Clifford group in (1.1), literally the quotient by scalar unitaries. -/
abbrev ProjectiveClifford (N : ℕ) := Clifford N ⧸ cliffordScalars N

/-- Trivial conjugation is equivalent to being a scalar operator. -/
theorem cliffordAction_ker (N : ℕ) : (cliffordAction N).ker = cliffordScalars N := by
  apply le_antisymm
  · intro U hU
    have hact : cliffordAction N U = 1 := hU
    have hc (g : Pauli N) : U.val * Pauli.unitaryHom N g = Pauli.unitaryHom N g * U.val := by
      have h := cliffordAut_formula U g
      have he : cliffordAut N U g = g := congrArg (fun α : PauliAut N => α.val g) hact
      rw [he] at h
      exact (eq_mul_inv_iff_mul_eq.mp h).symm
    have hs := Pauli.commutant_scalar U.val.val (fun g => congrArg Subtype.val (hc g))
    let c := U.val.val 0 0
    have hunit : c ∈ unitary ℂ := by
      have h := Matrix.UnitaryGroup.star_mul_self U.val
      rw [hs] at h
      have he := congrArg (fun M : Matrix (Bits N) (Bits N) ℂ => M 0 0) h
      have he' : star c * c = 1 := by simpa [c, mul_comm] using he
      exact ⟨he', by simpa [mul_comm] using he'⟩
    refine ⟨⟨c, hunit⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext
    exact hs.symm
  · rintro _ ⟨c, rfl⟩
    change cliffordAction N (cliffordScalar N c) = 1
    apply Subtype.ext; apply MulEquiv.ext
    intro g
    apply (pauliEquivOperatorGroup N).injective
    apply Subtype.ext
    change Pauli.unitaryHom N (cliffordAut N (cliffordScalar N c) g) = Pauli.unitaryHom N g
    rw [cliffordAut_formula]
    change scalarUnitary N c * Pauli.unitaryHom N g * (scalarUnitary N c)⁻¹ = _
    rw [← (Subgroup.mem_center_iff.mp (scalarUnitary_central N c)) (Pauli.unitaryHom N g),
      mul_inv_cancel_right]

end
end Char2Theta

/-! ## Unitary implementation of center-fixing Pauli automorphisms -/
namespace Char2Theta
noncomputable section
open scoped ComplexOrder

namespace Pauli
variable {N : ℕ}

@[simp] theorem matrix_inv (g : Pauli N) : matrix g⁻¹ = star (matrix g) :=
  congrArg Subtype.val ((unitaryHom N).map_inv g)

/-- Every center-fixing automorphism is implemented by an actual unitary matrix. -/
theorem exists_unitary_implementation (α : PauliAut N) :
    ∃ U : Matrix.unitaryGroup (Bits N) ℂ,
      ∀ g : Pauli N, U.val * matrix g = matrix (α.val g) * U.val := by
  classical
  obtain ⟨T, hT0, hT⟩ := exists_intertwiner α
  have hstar (g : Pauli N) : star T * matrix (α.val g) = matrix g * star T := by
    have h := congrArg star (hT g⁻¹)
    simpa only [map_inv, matrix_inv, star_mul, star_star] using h.symm
  have hc := commutant_scalar (star T * T) (fun g => by
    rw [mul_assoc, hT, ← mul_assoc, hstar, mul_assoc])
  let c : ℂ := (star T * T) 0 0
  have hc0 : 0 ≤ c := (Matrix.posSemidef_conjTranspose_mul_self T).diag_nonneg
  have hcne : c ≠ 0 := by
    intro he
    apply hT0
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    rw [← Matrix.star_eq_conjTranspose, hc]
    change c • (1 : Matrix (Bits N) (Bits N) ℂ) = 0
    rw [he, zero_smul]
  have hcreal : c = (c.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using (Complex.nonneg_iff.mp hc0).2.symm
  let r : ℝ := Real.sqrt c.re
  have hr : (r : ℂ) ≠ 0 := by
    have hre : c.re ≠ 0 := by intro he; apply hcne; rw [hcreal, he]; rfl
    exact_mod_cast (Real.sqrt_ne_zero (Complex.nonneg_iff.mp hc0).1).mpr hre
  have hr2 : (r : ℂ) * (r : ℂ) = c := by
    rw [hcreal, ← Complex.ofReal_mul]
    exact congrArg Complex.ofReal (Real.mul_self_sqrt (Complex.nonneg_iff.mp hc0).1)
  let z : ℂ := (r : ℂ)⁻¹
  have hz : star z * z * c = 1 := by
    dsimp [z]
    simp only [map_inv₀, Complex.conj_ofReal]
    rw [← hr2]
    field_simp
  have hU : z • T ∈ Matrix.unitaryGroup (Bits N) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    have hc' : star T * T = c • 1 := hc
    rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, hc']
    simpa only [smul_smul, mul_assoc, mul_comm, mul_left_comm, one_smul] using
      congrArg (fun a : ℂ => a • (1 : Matrix (Bits N) (Bits N) ℂ)) hz
  refine ⟨⟨z • T, hU⟩, fun g => ?_⟩
  change (z • T) * matrix g = matrix (α.val g) * (z • T)
  rw [Matrix.smul_mul, Matrix.mul_smul, hT]

end Pauli

/-- The faithful realization identifies all center-fixing automorphisms with
conjugations by elements of the concrete Clifford normalizer. -/
theorem cliffordAction_surjective (N : ℕ) : Function.Surjective (cliffordAction N) := by
  intro α
  obtain ⟨U, hU⟩ := Pauli.exists_unitary_implementation α
  have hu (g : Pauli N) : U * Pauli.unitaryHom N g * U⁻¹ = Pauli.unitaryHom N (α.val g) := by
    apply mul_inv_eq_iff_eq_mul.mpr
    exact Subtype.ext (hU g)
  have hnorm : U ∈ Clifford N := by
    intro x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨α.val g, (hu g).symm⟩
    · rintro ⟨g, hg⟩
      refine ⟨α.val.symm g, ?_⟩
      have h := hu (α.val.symm g)
      rw [α.val.apply_symm_apply] at h
      rw [hg] at h
      exact mul_left_cancel (mul_right_cancel h)
  refine ⟨⟨U, hnorm⟩, ?_⟩
  apply Subtype.ext; apply MulEquiv.ext
  intro g
  apply (pauliEquivOperatorGroup N).injective
  apply Subtype.ext
  change Pauli.unitaryHom N (cliffordAut N ⟨U, hnorm⟩ g) = Pauli.unitaryHom N (α.val g)
  rw [cliffordAut_formula, hu]

/-- The projective quotient is canonically the center-fixing automorphism group. -/
def projectiveCliffordEquiv (N : ℕ) : ProjectiveClifford N ≃* PauliAut N :=
  QuotientGroup.liftEquiv (cliffordScalars N) (cliffordAction_surjective N)
    (cliffordAction_ker N).symm

end
end Char2Theta

/-! ## The projective Pauli exact sequence (1.1)

For every `N`, including `N = 0`, the two displayed maps give
`1 → (𝔽₂^(2N),+) → Cl_N / U(1) → Sp_(2N)(𝔽₂) → 1`.
The middle term is the quotient of the concrete unitary normalizer; the target
is mathlib's matrix symplectic group. All endpoint and kernel assertions are
proved without additional assumptions.
-/
namespace Char2Theta
noncomputable section

/-- The left map of (1.1), transporting inner Pauli conjugation to the concrete quotient. -/
def projectivePauli (N : ℕ) : Multiplicative (Labels N) →* ProjectiveClifford N :=
  (projectiveCliffordEquiv N).symm.toMonoidHom.comp (PauliAut.inner N)

/-- The right map of (1.1), the symplectic action of conjugation on Pauli labels. -/
def projectiveSymplectic (N : ℕ) :
    ProjectiveClifford N →* Matrix.symplecticGroup (Fin N) F₂ :=
  (labelSymplecticMatrixEquiv N).toMonoidHom.comp
    ((PauliAut.toSymplectic N).comp (projectiveCliffordEquiv N).toMonoidHom)

theorem projectivePauli_injective (N : ℕ) : Function.Injective (projectivePauli N) :=
  (projectiveCliffordEquiv N).symm.injective.comp (PauliAut.inner_injective N)

theorem projectiveSymplectic_surjective (N : ℕ) : Function.Surjective (projectiveSymplectic N) :=
  (labelSymplecticMatrixEquiv N).surjective.comp
    ((PauliAut.toSymplectic_surjective N).comp (projectiveCliffordEquiv N).surjective)

/-- Exactness at the projective Clifford group. -/
theorem projectiveClifford_exact (N : ℕ) :
    Function.MulExact (projectivePauli N) (projectiveSymplectic N) := by
  intro x
  change labelSymplecticMatrixEquiv N (PauliAut.toSymplectic N (projectiveCliffordEquiv N x)) = 1 ↔ _
  rw [← (labelSymplecticMatrixEquiv N).map_one,
    (labelSymplecticMatrixEquiv N).injective.eq_iff, PauliAut.mem_ker_iff_inner]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    change (projectiveCliffordEquiv N).symm (PauliAut.inner N v) = x
    rw [hv, MulEquiv.symm_apply_apply]
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    rw [← hv]
    exact ((projectiveCliffordEquiv N).apply_symm_apply _).symm

/-- Equivalent bundled subgroup formulation of the middle exactness assertion. -/
theorem projectivePauli_range (N : ℕ) :
    (projectivePauli N).range = (projectiveSymplectic N).ker := by
  ext x
  exact (projectiveClifford_exact N x).symm

/-- Equation (1.1): injective left arrow, exact middle, and surjective right arrow. -/
theorem equation_1_1 (N : ℕ) :
    Function.Injective (projectivePauli N) ∧
    Function.MulExact (projectivePauli N) (projectiveSymplectic N) ∧
    Function.Surjective (projectiveSymplectic N) :=
  ⟨projectivePauli_injective N, projectiveClifford_exact N, projectiveSymplectic_surjective N⟩

/-- The quotient is finite, despite the infinite scalar subgroup of the full Clifford group. -/
instance projectiveClifford_finite (N : ℕ) : Finite (ProjectiveClifford N) :=
  Finite.of_injective (projectiveCliffordEquiv N) (projectiveCliffordEquiv N).injective

/-- The actual Pauli subgroup lies in its unitary normalizer. -/
def pauliClifford (N : ℕ) : Pauli N →* Clifford N :=
  (Pauli.unitaryHom N).codRestrict (Clifford N) (fun g =>
    (Pauli.operatorGroup N).le_normalizer ⟨g, rfl⟩)

theorem cliffordAction_pauli {N : ℕ} (g : Pauli N) :
    cliffordAction N (pauliClifford N g) = PauliAut.conjugation N g := by
  apply Subtype.ext; apply MulEquiv.ext
  intro h
  apply (pauliEquivOperatorGroup N).injective
  apply Subtype.ext
  change Pauli.unitaryHom N (cliffordAut N (pauliClifford N g) h) =
    Pauli.unitaryHom N (g * h * g⁻¹)
  rw [cliffordAut_formula, map_mul, map_mul, map_inv]
  rfl

/-- The left arrow really sends `(a,b)` to the projective class of `X_a Z_b`. -/
theorem projectivePauli_eq_mk (N : ℕ) (v : Labels N) :
    projectivePauli N (Multiplicative.ofAdd v) =
      QuotientGroup.mk (pauliClifford N (PauliAut.rep v)) := by
  apply (projectiveCliffordEquiv N).injective
  change (projectiveCliffordEquiv N) ((projectiveCliffordEquiv N).symm _) = _
  rw [MulEquiv.apply_symm_apply]
  change PauliAut.inner N (Multiplicative.ofAdd v) = cliffordAction N (pauliClifford N (PauliAut.rep v))
  exact (cliffordAction_pauli _).symm

/-- The right arrow is the matrix of the action induced by actual conjugation. -/
theorem projectiveSymplectic_mk (N : ℕ) (U : Clifford N) :
    projectiveSymplectic N (QuotientGroup.mk U) =
      labelSymplecticMatrixEquiv N (PauliAut.toSymplectic N (cliffordAction N U)) := rfl

end
end Char2Theta
