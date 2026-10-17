import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# 有限坐标、中心扩张与公共特征工具（§§1.1–1.3）

本文件提供有限群与局部特征共用的基础：双加性 cocycle 的中心扩张、
二元坐标、辛配对、模四中心、复相位及 Heisenberg–Pauli 换坐标同构。
最后证明阿贝尔群的子群特征可延拓到复单位群，供辛提升和局部导子构造复用。

阅读顺序：`BilinearExtension` → `F₂`、`Bits`、`Labels` → `twoLift`、`phase` →
`heisenbergEquivPauli` → `extend_unit_character`。
-/

set_option autoImplicit false

/-!
## Bilinear central extensions

The common group construction used for both groups in §1.2 of `Char2Theta.pdf`.
The cocycle is additive in each argument; it need not be alternating.
-/

namespace Char2Theta

/-- `C(v,w)` is the central cocycle, in additive notation. -/
@[ext]
structure BilinearExtension {V A : Type*} [AddCommGroup V] [AddCommGroup A]
    (C : V →+ V →+ A) where
  label : V
  central : A

namespace BilinearExtension

variable {V A : Type*} [AddCommGroup V] [AddCommGroup A]
variable {C : V →+ V →+ A}

instance : Mul (BilinearExtension C) :=
  ⟨fun g h => ⟨g.label + h.label, g.central + h.central + C g.label h.label⟩⟩

instance : One (BilinearExtension C) := ⟨⟨0, 0⟩⟩

instance : Inv (BilinearExtension C) :=
  ⟨fun g => ⟨-g.label, -g.central + C g.label g.label⟩⟩

@[simp] theorem mul_label (g h : BilinearExtension C) :
    (g * h).label = g.label + h.label := rfl
@[simp] theorem mul_central (g h : BilinearExtension C) :
    (g * h).central = g.central + h.central + C g.label h.label := rfl
@[simp] theorem one_label : (1 : BilinearExtension C).label = 0 := rfl
@[simp] theorem one_central : (1 : BilinearExtension C).central = 0 := rfl
@[simp] theorem inv_label (g : BilinearExtension C) : (g⁻¹).label = -g.label := rfl
@[simp] theorem inv_central (g : BilinearExtension C) :
    (g⁻¹).central = -g.central + C g.label g.label := rfl

instance : Group (BilinearExtension C) where
  mul_assoc g h k := by
    ext <;> simp only [mul_label, mul_central, map_add, AddMonoidHom.add_apply] <;> abel
  one_mul g := by ext <;> simp
  mul_one g := by ext <;> simp
  inv_mul_cancel g := by ext <;> simp

/-- A central element with zero label. -/
def ofCenter (a : A) : BilinearExtension C := ⟨0, a⟩

@[simp] theorem ofCenter_label (a : A) : (ofCenter (C := C) a).label = 0 := rfl
@[simp] theorem ofCenter_central (a : A) : (ofCenter (C := C) a).central = a := rfl

/-- The central copy of `A`. -/
def centerHom : Multiplicative A →* BilinearExtension C where
  toFun a := ofCenter a.toAdd
  map_one' := rfl
  map_mul' a b := by ext <;> simp [ofCenter]

theorem ofCenter_commute (a : A) (g : BilinearExtension C) :
    Commute (ofCenter a) g := by
  show ofCenter a * g = g * ofCenter a
  ext <;> simp [ofCenter, add_comm]

/-- The commutator convention is `g h g⁻¹ h⁻¹`. -/
theorem commutator (g h : BilinearExtension C) :
    g * h * g⁻¹ * h⁻¹ = ofCenter (C g.label h.label - C h.label g.label) := by
  ext <;> simp [ofCenter, map_add, map_neg]
  all_goals abel

theorem commute_iff (g h : BilinearExtension C) :
    Commute g h ↔ C g.label h.label = C h.label g.label := by
  change g * h = h * g ↔ _
  constructor
  · intro hgh
    have := congrArg central hgh
    simpa only [mul_central, add_comm h.central g.central, add_right_inj] using this
  · intro hC
    ext <;> simp [hC, add_comm]

end BilinearExtension
end Char2Theta

/-! ## Finite coordinates and central phases (§§1.1–1.2) -/

namespace Char2Theta

abbrev F₂ := ZMod 2
abbrev Bits (N : ℕ) := Fin N → F₂
abbrev Labels (N : ℕ) := Bits N × Bits N

/-- The dot product in the notes is the mathlib dot product over `ZMod 2`. -/
abbrev dot {N : ℕ} (a b : Bits N) : F₂ := dotProduct a b

/-- The injective additive map `t ↦ 2t` from `Z/2` to `Z/4`.
It is deliberately not declared a ring homomorphism. -/
def twoLift : F₂ →+ ZMod 4 where
  toFun t := 2 * (t.val : ZMod 4)
  map_zero' := rfl
  map_add' a b := by fin_cases a <;> fin_cases b <;> decide

@[simp] theorem twoLift_zero : twoLift 0 = 0 := rfl
@[simp] theorem twoLift_one : twoLift 1 = 2 := rfl

theorem twoLift_injective : Function.Injective twoLift := by decide

/-- The central character `s ↦ i^s`, independent of the representative modulo four. -/
def phase (s : ZMod 4) : ℂ := Complex.I ^ s.val

@[simp] theorem phase_zero : phase 0 = 1 := rfl
@[simp] theorem phase_one : phase 1 = Complex.I := by change Complex.I ^ 1 = Complex.I; simp
@[simp] theorem phase_two : phase 2 = -1 := by change Complex.I ^ 2 = -1; norm_num
@[simp] theorem phase_add (s t : ZMod 4) : phase (s + t) = phase s * phase t := by
  simp only [phase, ZMod.val_add]
  fin_cases s <;> fin_cases t <;> norm_num [ZMod.val, pow_succ]

theorem phase_ne_zero (s : ZMod 4) : phase s ≠ 0 :=
  pow_ne_zero _ Complex.I_ne_zero

theorem phase_injective : Function.Injective phase := by
  intro s t h
  fin_cases s <;> fin_cases t <;> norm_num [phase, ZMod.val, pow_succ, Complex.ext_iff] at *

@[simp] theorem phase_star_mul (s : ZMod 4) : star (phase s) * phase s = 1 := by
  fin_cases s <;> norm_num [phase, ZMod.val, pow_succ]

/-- `(-1)^t` for a binary exponent. -/
def sign (t : F₂) : ℂ := phase (twoLift t)

@[simp] theorem sign_zero : sign 0 = 1 := rfl
@[simp] theorem sign_one : sign 1 = -1 := by simp [sign]
@[simp] theorem sign_add (a b : F₂) : sign (a + b) = sign a * sign b := by
  simp [sign]
@[simp] theorem sign_mul_self (a : F₂) : sign a * sign a = 1 := by
  rw [← sign_add]; simp [CharTwo.add_self_eq_zero]

theorem sign_ne_zero (a : F₂) : sign a ≠ 0 := phase_ne_zero _

theorem sign_injective : Function.Injective sign :=
  phase_injective.comp twoLift_injective

/-- The alternating pairing on labels in characteristic two. -/
def binarySymplectic {N : ℕ} (v w : Labels N) : F₂ :=
  dot v.1 w.2 + dot w.1 v.2

@[simp] theorem binarySymplectic_self {N : ℕ} (v : Labels N) :
    binarySymplectic v v = 0 := by
  simp [binarySymplectic, CharTwo.add_self_eq_zero]

/-- The cocycle for ordered operators `i^s X_a Z_b` is `2 b·a'`. -/
def pauliCocycle (N : ℕ) : Labels N →+ Labels N →+ ZMod 4 where
  toFun v :=
    { toFun := fun w => twoLift (dot v.2 w.1)
      map_zero' := by simp
      map_add' := by intros; simp [dotProduct_add] }
  map_zero' := by ext; simp
  map_add' := by intros; ext; simp [add_dotProduct]

/-- The cocycle displayed for `H₄` in §1.2 is `2 x·y'`. -/
def heisenbergCocycle (N : ℕ) : Labels N →+ Labels N →+ ZMod 4 where
  toFun v :=
    { toFun := fun w => twoLift (dot v.1 w.2)
      map_zero' := by simp
      map_add' := by intros; simp [dotProduct_add] }
  map_zero' := by ext; simp
  map_add' := by intros; ext; simp [add_dotProduct]

abbrev Pauli (N : ℕ) := BilinearExtension (pauliCocycle N)
abbrev Heisenberg₄ (N : ℕ) := BilinearExtension (heisenbergCocycle N)

/-- Swapping the two label coordinates matches the displayed `H₄` law with
ordered Pauli operators. In particular `((x,y),s)` acts as `i^s X_y Z_x`. -/
def heisenbergEquivPauli (N : ℕ) : Heisenberg₄ N ≃* Pauli N where
  toFun g := ⟨(g.label.2, g.label.1), g.central⟩
  invFun g := ⟨(g.label.2, g.label.1), g.central⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end Char2Theta

/-! ## Extension of abelian-group characters to complex units -/

namespace Char2Theta
noncomputable section

@[implicit_reducible] private def complexUnitsDivisibleNat : DivisibleBy (Additive ℂˣ) ℕ :=
  divisibleByOfSMulRightSurj _ _ fun {n} hn a => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a.toMul : ℂ) (Nat.pos_of_ne_zero hn)
    have hzne : z ≠ 0 := by
      intro h; subst z
      exact Units.ne_zero a.toMul (by simpa [zero_pow hn] using hz.symm)
    refine ⟨Additive.ofMul (Units.mk0 z hzne), ?_⟩
    change Additive.ofMul ((Units.mk0 z hzne) ^ n) = a
    apply Additive.ofMul.injective
    exact Units.ext hz

/-- A character on a subgroup of an abelian group extends to complex units. -/
theorem extend_unit_character {G H : Type*} [CommGroup G] [CommGroup H]
    (i : G →* H) (hi : Function.Injective i) (χ : G →* ℂˣ) :
    ∃ ψ : H →* ℂˣ, ψ.comp i = χ := by
  letI := complexUnitsDivisibleNat
  letI := AddGroup.divisibleByIntOfDivisibleByNat (Additive ℂˣ)
  obtain ⟨ψ, hψ⟩ := (Module.Baer.of_divisible (Additive ℂˣ)).extension_property_addMonoidHom
    i.toAdditive hi χ.toAdditive
  exact ⟨ψ.toMultiplicative, congrArg AddMonoidHom.toMultiplicative hψ⟩

end
end Char2Theta
