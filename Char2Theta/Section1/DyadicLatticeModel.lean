import Char2Theta.Section1.DyadicCharacter
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.RepresentationTheory.Subrepresentation

/-!
# 紧开格、局部函数模型与根算子（§1.3、式 (2.2)–(2.3)）

本文件集中格与表示的约定、坐标格紧开性、Schwartz–Bruhat 空间及局部子空间 `S_L`。
构造 `S_L` 与有限商 `(𝒪/2𝒪)^n` 上函数空间的同构，证明 delta 基和维数 `q^(en)`，
再构造有限 Fourier、局部相位与坐标剪切，证明根算子的稳定性和有限坐标公式。
最后给出从实际环境表示及生成元公式构造限制表示的条件性接口。

主要入口：`latticeEquivFinite`、`latticeDeltaBasis`、`localLatticeSpace_finrank`、
`finiteFourier`、`latticeLongRoot`、`latticeShortRoot`、`latticeShear`、
`latticeRepresentationOfGenerators`。该接口要求已有环境表示，尚未据此构造
具体 metaplectic 群、完整 Weil 表示或原文的 `τ_L`。
-/

set_option autoImplicit false

namespace Char2Theta.Dyadic
noncomputable section

/-- The integer called `D` in §1.3. -/
def symplecticDimension (n : ℕ) : ℕ := n * (2 * n + 1)

/-- Standard polarization, valid over any commutative ring. -/
abbrev W (O : Type*) (n : ℕ) := (Fin n → O) × (Fin n → O)

/-- The sign convention is `x·y' - x'·y`, exactly as in the notes. -/
def pairing {O : Type*} [CommRing O] {n : ℕ} (v w : W O n) : O :=
  dotProduct v.1 w.2 - dotProduct w.1 v.2

@[simp] theorem pairing_self {O : Type*} [CommRing O] {n : ℕ} (v : W O n) :
    pairing v v = 0 := sub_self _

theorem pairing_skew {O : Type*} [CommRing O] {n : ℕ} (v w : W O n) :
    pairing v w = -pairing w v := by simp [pairing, neg_sub]

/-- The integral symplectic group, directly from mathlib. -/
abbrev K (O : Type*) [CommRing O] (n : ℕ) := Matrix.symplecticGroup (Fin n) O

/-- Entrywise reduction of a symplectic matrix through a ring homomorphism. -/
def symplecticMap {O S : Type*} [CommRing O] [CommRing S] (n : ℕ) (f : O →+* S) :
    K O n →* K S n where
  toFun g := ⟨(g.val).map f, SymplecticGroup.map_mem g.property f⟩
  map_one' := by apply Subtype.ext; exact Matrix.map_one (n := Fin n ⊕ Fin n) f f.map_zero f.map_one
  map_mul' g h := by apply Subtype.ext; exact Matrix.map_mul

/-- Congruence subgroup for an arbitrary ideal. -/
def congruence {O : Type*} [CommRing O] (n : ℕ) (I : Ideal O) : Subgroup (K O n) :=
  (symplecticMap n (Ideal.Quotient.mk I)).ker

/-- `K(r)`, in particular `K(2)` and `K(4)`. -/
def Klevel {O : Type*} [CommRing O] (n r : ℕ) : Subgroup (K O n) :=
  congruence n (rationalIdeal O r)

/-- Reduction modulo the chosen uniformizer is kept separate. -/
def Kuniformizer {O : Type*} [CommRing O] (n : ℕ) (π : O) : Subgroup (K O n) :=
  congruence n (Ideal.span {π})

/-- Schwartz–Bruhat functions: locally constant and compactly supported.
This is distinct from mathlib's real/complex rapidly decreasing Schwartz space. -/
def schwartzBruhatSubmodule (X : Type*) [TopologicalSpace X] [T2Space X] :
    Submodule ℂ (LocallyConstant X ℂ) where
  carrier := {f | HasCompactSupport (f : X → ℂ)}
  zero_mem' := by simpa using (HasCompactSupport.zero : HasCompactSupport (0 : X → ℂ))
  add_mem' hf hg := hf.add hg
  smul_mem' c f hf := by
    change HasCompactSupport ((fun _ : X => c) • (f : X → ℂ))
    exact hf.smul_left

abbrev SchwartzBruhat (X : Type*) [TopologicalSpace X] [T2Space X] :=
  schwartzBruhatSubmodule X

/-- The finite function model `𝒮(𝒪ⁿ/2𝒪ⁿ)`; `DyadicLatticeModel` identifies it
with the local lattice subspace. -/
abbrev FiniteLatticeSpace (O : Type*) [CommRing O] (n : ℕ) := (Fin n → R O) → ℂ

/-- The defining support and translation conditions for the local lattice subspace. -/
def latticeSubmodule {E : Type*} [Field E] [TopologicalSpace E] [T2Space E]
    (O : Subring E) (n : ℕ) : Submodule ℂ (SchwartzBruhat (Fin n → E)) where
  carrier := {f | (∀ z, (∃ i, z i ∉ O) → f.val z = 0) ∧
    ∀ z (u : Fin n → O), f.val (z + fun i => 2 * (u i).val) = f.val z}
  zero_mem' := by constructor <;> intros <;> rfl
  add_mem' := by
    intro f g hf hg
    constructor
    · intro z hz
      change f.val z + g.val z = 0
      rw [hf.1 z hz, hg.1 z hz, add_zero]
    · intro z u
      change f.val _ + g.val _ = f.val z + g.val z
      rw [hf.2 z u, hg.2 z u]
  smul_mem' c f hf := by
    constructor
    · intro z hz; change c * _ = 0; rw [hf.1 z hz, mul_zero]
    · intro z u; change c * _ = c * _; rw [hf.2 z u]

/-- For locally profinite groups, smooth means every vector has an open stabilizer. -/
def SmoothRepresentation {G V : Type*} [Group G] [TopologicalSpace G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) : Prop :=
  ∀ v, IsOpen {g | ρ g v = v}

/-- Genuineness relative to the specified nontrivial covering-kernel element. -/
def Genuine {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (ε : G) : Prop := ∀ v, ρ ε v = -v

end
end Char2Theta.Dyadic

/-!
## Compact open integral lattices (§1.3)

The integral lattice and its rational multiples use the original integer ring.
Reduction is coordinatewise modulo `(2)`, including in ramified extensions.
-/

namespace Char2Theta.Dyadic
noncomputable section

variable (F : Type*) [NormedField F] [NormedAlgebra ℚ_[2] F]
  [FiniteDimensional ℚ_[2] F] (n : ℕ)

/-- The inclusion of the coordinate lattice in the local vector space. -/
def integralVector (x : Fin n → Integers F) : Fin n → F := fun i => (x i : F)

/-- The subset `𝒪ⁿ` of `Fⁿ`. -/
def integralLattice : Set (Fin n → F) := {z | ∀ i, z i ∈ Integers F}

/-- The subset `r𝒪ⁿ` of `Fⁿ`, for a rational integer `r`. -/
def multipleLattice (r : ℕ) : Set (Fin n → F) :=
  {z | ∀ i, z i ∈ multiples (Integers F).toSubring r}

/-- The coordinatewise quotient map to `(𝒪/2𝒪)ⁿ`. -/
def reduceVector (x : Fin n → Integers F) : Fin n → R (Integers F) :=
  fun i => Ideal.Quotient.mk (rationalIdeal (Integers F) 2) (x i)

theorem integralLattice_isCompact : IsCompact (integralLattice F n) :=
  isCompact_pi_infinite (fun _ => integers_isCompact F)

theorem integralLattice_isOpen : IsOpen (integralLattice F n) := by
  convert isOpen_iInter_of_finite (fun i : Fin n =>
    (integers_isOpen F).preimage
      (show Continuous (fun z : Fin n → F => z i) from continuous_apply i)) using 1
  ext z
  simp [integralLattice]

theorem multipleLattice_isCompact (r : ℕ) : IsCompact (multipleLattice F n r) :=
  isCompact_pi_infinite (fun _ => multiples_isCompact F r)

theorem multipleLattice_isOpen (r : ℕ) (hr : r ≠ 0) : IsOpen (multipleLattice F n r) := by
  convert isOpen_iInter_of_finite (fun i : Fin n =>
    (multiples_isOpen F r hr).preimage
      (show Continuous (fun z : Fin n → F => z i) from continuous_apply i)) using 1
  ext z
  simp [multipleLattice]

/-- The coset `x + 2𝒪ⁿ` in the ambient vector space. -/
def latticeCoset (x : Fin n → Integers F) : Set (Fin n → F) :=
  (fun z => z + integralVector F n x) '' multipleLattice F n 2

theorem latticeCoset_isCompact (x : Fin n → Integers F) : IsCompact (latticeCoset F n x) :=
  (multipleLattice_isCompact F n 2).image (continuous_id.add continuous_const)

theorem latticeCoset_isOpen (x : Fin n → Integers F) : IsOpen (latticeCoset F n x) :=
  (Homeomorph.addRight (integralVector F n x)).isOpenMap _
    (multipleLattice_isOpen F n 2 (by decide))

theorem latticeCoset_isClopen (x : Fin n → Integers F) : IsClopen (latticeCoset F n x) :=
  ⟨(latticeCoset_isCompact F n x).isClosed, latticeCoset_isOpen F n x⟩

omit [FiniteDimensional ℚ_[2] F] in
/-- Membership in a lattice coset is translation by an actual vector in `2𝒪ⁿ`. -/
theorem mem_latticeCoset_iff (x : Fin n → Integers F) (z : Fin n → F) :
    z ∈ latticeCoset F n x ↔
      ∃ u : Fin n → Integers F,
        z = integralVector F n x + fun i => 2 * (u i : F) := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    choose u hu using hv
    refine ⟨u, ?_⟩
    funext i
    simp only [Pi.add_apply, integralVector]
    have hi : (2 : F) * (u i : F) = v i := hu i
    rw [← hi, add_comm]
  · rintro ⟨u, rfl⟩
    refine ⟨(fun i => 2 * (u i : F)), (fun i => ⟨u i, rfl⟩), ?_⟩
    exact add_comm _ _

omit [FiniteDimensional ℚ_[2] F] in
theorem integralVector_mem_latticeCoset (x : Fin n → Integers F) :
    integralVector F n x ∈ latticeCoset F n x :=
  (mem_latticeCoset_iff F n x _).mpr ⟨0, by ext i; simp⟩

omit [FiniteDimensional ℚ_[2] F] in
theorem latticeCoset_subset_integralLattice (x : Fin n → Integers F) :
    latticeCoset F n x ⊆ integralLattice F n := by
  intro z hz
  obtain ⟨u, rfl⟩ := (mem_latticeCoset_iff F n x z).mp hz
  intro i
  exact (Integers F).add_mem (x i).property
    ((Integers F).mul_mem (by exact_mod_cast (Integers F).natCast_mem 2) (u i).property)

omit [FiniteDimensional ℚ_[2] F] in
/-- Equal residue labels mean precisely that the two integer vectors differ by `2𝒪ⁿ`. -/
theorem reduceVector_eq_iff (x y : Fin n → Integers F) :
    reduceVector F n x = reduceVector F n y ↔
      ∃ u : Fin n → Integers F,
        integralVector F n x = integralVector F n y + fun i => 2 * (u i : F) := by
  constructor
  · intro h
    have hxy : ∀ i, ∃ u : Integers F, x i - y i = 2 * u := by
      intro i
      have hi := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (congrFun h i)
      exact Ideal.mem_span_singleton.mp hi
    choose u hu using hxy
    refine ⟨u, ?_⟩
    funext i
    have hi := congrArg (fun t : Integers F => (t : F)) (hu i)
    change (x i : F) - (y i : F) = 2 * (u i : F) at hi
    exact sub_eq_iff_eq_add'.mp hi
  · rintro ⟨u, h⟩
    funext i
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    apply Ideal.mem_span_singleton.mpr
    refine ⟨u i, ?_⟩
    apply Subtype.val_injective
    have hi := congrFun h i
    change (x i : F) = (y i : F) + 2 * (u i : F) at hi
    change (x i : F) - (y i : F) = 2 * (u i : F)
    exact sub_eq_iff_eq_add'.mpr hi

omit [FiniteDimensional ℚ_[2] F] in
theorem integralVector_mem_latticeCoset_iff (x y : Fin n → Integers F) :
    integralVector F n y ∈ latticeCoset F n x ↔ reduceVector F n y = reduceVector F n x := by
  rw [mem_latticeCoset_iff, reduceVector_eq_iff]

omit [FiniteDimensional ℚ_[2] F] in
/-- The coset depends only on the residue label, not on its integer representative. -/
theorem latticeCoset_eq_of_reduceVector_eq (x y : Fin n → Integers F)
    (h : reduceVector F n x = reduceVector F n y) : latticeCoset F n x = latticeCoset F n y := by
  have hs : ∀ (v w : Fin n → Integers F), reduceVector F n v = reduceVector F n w →
      latticeCoset F n v ⊆ latticeCoset F n w := by
    intro v w hvw z hz
    have hzi := latticeCoset_subset_integralLattice F n v hz
    let z' : Fin n → Integers F := fun i => ⟨z i, hzi i⟩
    exact (integralVector_mem_latticeCoset_iff F n w z').mpr
      (((integralVector_mem_latticeCoset_iff F n v z').mp hz).trans hvw)
  exact Set.Subset.antisymm (hs x y h) (hs y x h.symm)

omit [FiniteDimensional ℚ_[2] F] in
/-- Reduction is surjective, coordinate by coordinate. -/
theorem reduceVector_surjective : Function.Surjective (reduceVector F n) := by
  intro a
  choose x hx using (fun i => Ideal.Quotient.mk_surjective (a i))
  exact ⟨x, funext hx⟩

omit [FiniteDimensional ℚ_[2] F] in
/-- Translation by `2𝒪ⁿ` preserves membership in `𝒪ⁿ`. -/
theorem add_two_mem_integralLattice_iff (z : Fin n → F) (u : Fin n → Integers F) :
    (z + fun i => 2 * (u i : F)) ∈ integralLattice F n ↔ z ∈ integralLattice F n := by
  have hu : ∀ i, (2 : F) * (u i : F) ∈ Integers F := fun i =>
    (Integers F).mul_mem ((Integers F).natCast_mem 2) (u i).property
  constructor
  · intro h i
    have hi := (Integers F).sub_mem (h i) (hu i)
    simpa using hi
  · intro h i
    exact (Integers F).add_mem (h i) (hu i)

end
end Char2Theta.Dyadic

namespace Char2Theta
noncomputable section

/-- A finite lattice function space has one basis vector for each residue label. -/
theorem finiteLatticeSpace_finrank (O : Type*) [CommRing O] (n : ℕ)
    [Fintype (Dyadic.R O)] :
    Module.finrank ℂ (Dyadic.FiniteLatticeSpace O n) = Fintype.card (Dyadic.R O) ^ n := by
  rw [Module.finrank_fintype_fun_eq_card]
  simp

/-- For a finite dyadic extension, the finite lattice space has dimension `q^(en)`. -/
theorem dyadic_finiteLatticeSpace_finrank (F : Type*) [Field F] [Algebra ℚ_[2] F]
    [FiniteDimensional ℚ_[2] F] (n : ℕ) :
    Module.finrank ℂ (Dyadic.FiniteLatticeSpace (Dyadic.Integers F) n) =
      Dyadic.residueCard F ^ (Dyadic.ramificationIndex (Dyadic.Integers F) * n) := by
  rw [finiteLatticeSpace_finrank, ← Nat.card_eq_fintype_card, Dyadic.card_R, pow_mul]

end
end Char2Theta

/-!
## The local lattice function model (§1.3)

Functions on `(𝒪/2𝒪)ⁿ` extend by zero outside `𝒪ⁿ`. This gives the
linear equivalence with the original subspace `S_L` of Schwartz–Bruhat functions.
-/

namespace Char2Theta.Dyadic
noncomputable section
open scoped Classical

variable (F : Type*) [NormedField F] [NormedAlgebra ℚ_[2] F]
  [FiniteDimensional ℚ_[2] F] (n : ℕ)

/-- The local subspace `S_L`, with the support and translation conditions of §1.3. -/
abbrev LocalLatticeSpace := latticeSubmodule (Integers F).toSubring n

/-- Pull back a finite function on the integer lattice, then extend it by zero. -/
def latticeExtensionFun (g : FiniteLatticeSpace (Integers F) n) (z : Fin n → F) : ℂ :=
  if hz : z ∈ integralLattice F n then
    g (reduceVector F n (fun i => ⟨z i, hz i⟩)) else 0

omit [FiniteDimensional ℚ_[2] F] in
@[simp]
theorem latticeExtensionFun_integralVector (g : FiniteLatticeSpace (Integers F) n)
    (x : Fin n → Integers F) :
    latticeExtensionFun F n g (integralVector F n x) = g (reduceVector F n x) := by
  simp [latticeExtensionFun, integralLattice, integralVector, fun i => (x i).property]

omit [FiniteDimensional ℚ_[2] F] in
theorem latticeExtensionFun_eq_zero (g : FiniteLatticeSpace (Integers F) n)
    (z : Fin n → F) (hz : z ∉ integralLattice F n) : latticeExtensionFun F n g z = 0 :=
  dif_neg hz

/-- Compact open residue cosets make every extended finite function locally constant. -/
theorem latticeExtensionFun_isLocallyConstant (g : FiniteLatticeSpace (Integers F) n) :
    IsLocallyConstant (latticeExtensionFun F n g) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro z
  by_cases hz : z ∈ integralLattice F n
  · let x : Fin n → Integers F := fun i => ⟨z i, hz i⟩
    refine ⟨latticeCoset F n x, latticeCoset_isOpen F n x,
      integralVector_mem_latticeCoset F n x, ?_⟩
    intro y hy
    have hyi := latticeCoset_subset_integralLattice F n x hy
    let y' : Fin n → Integers F := fun i => ⟨y i, hyi i⟩
    have hred : reduceVector F n y' = reduceVector F n x :=
      (integralVector_mem_latticeCoset_iff F n x y').mp hy
    change latticeExtensionFun F n g (integralVector F n y') =
      latticeExtensionFun F n g (integralVector F n x)
    rw [latticeExtensionFun_integralVector, latticeExtensionFun_integralVector, hred]
  · refine ⟨(integralLattice F n)ᶜ, (integralLattice_isCompact F n).isClosed.isOpen_compl,
      hz, ?_⟩
    intro y hy
    rw [latticeExtensionFun_eq_zero F n g y hy, latticeExtensionFun_eq_zero F n g z hz]

theorem latticeExtensionFun_hasCompactSupport (g : FiniteLatticeSpace (Integers F) n) :
    HasCompactSupport (latticeExtensionFun F n g) := by
  apply HasCompactSupport.of_support_subset_isCompact (integralLattice_isCompact F n)
  intro z hz
  by_contra hn
  exact hz (latticeExtensionFun_eq_zero F n g z hn)

omit [FiniteDimensional ℚ_[2] F] in
theorem latticeExtensionFun_add_two (g : FiniteLatticeSpace (Integers F) n)
    (z : Fin n → F) (u : Fin n → Integers F) :
    latticeExtensionFun F n g (z + fun i => 2 * (u i : F)) = latticeExtensionFun F n g z := by
  by_cases hz : z ∈ integralLattice F n
  · let x : Fin n → Integers F := fun i => ⟨z i, hz i⟩
    let y : Fin n → Integers F := fun i => x i + 2 * u i
    have hred : reduceVector F n y = reduceVector F n x :=
      (reduceVector_eq_iff F n y x).mpr ⟨u, rfl⟩
    change latticeExtensionFun F n g (integralVector F n y) =
      latticeExtensionFun F n g (integralVector F n x)
    rw [latticeExtensionFun_integralVector, latticeExtensionFun_integralVector, hred]
  · have ht := mt (add_two_mem_integralLattice_iff F n z u).mp hz
    rw [latticeExtensionFun_eq_zero F n g _ ht, latticeExtensionFun_eq_zero F n g z hz]

/-- Extension by zero takes values in the original local lattice subspace. -/
def latticeExtension (g : FiniteLatticeSpace (Integers F) n) : LocalLatticeSpace F n :=
  ⟨⟨⟨latticeExtensionFun F n g, latticeExtensionFun_isLocallyConstant F n g⟩,
      latticeExtensionFun_hasCompactSupport F n g⟩, by
    constructor
    · intro z hz
      apply latticeExtensionFun_eq_zero
      rintro hi
      obtain ⟨i, hni⟩ := hz
      exact hni (hi i)
    · exact latticeExtensionFun_add_two F n g⟩

omit [FiniteDimensional ℚ_[2] F] in
/-- Evaluation at representatives will be independent of the representative. -/
theorem localLattice_eq_of_reduceVector_eq (f : LocalLatticeSpace F n)
    (x y : Fin n → Integers F) (h : reduceVector F n x = reduceVector F n y) :
    f.val.val (integralVector F n x) = f.val.val (integralVector F n y) := by
  obtain ⟨u, hu⟩ := (reduceVector_eq_iff F n x y).mp h
  rw [hu]
  exact f.property.2 _ u

/-- A section of coordinatewise reduction, used only to define restriction. -/
def residueVectorRepresentative (a : Fin n → R (Integers F)) : Fin n → Integers F :=
  (reduceVector_surjective F n a).choose

omit [FiniteDimensional ℚ_[2] F] in
@[simp]
theorem reduceVector_representative (a : Fin n → R (Integers F)) :
    reduceVector F n (residueVectorRepresentative F n a) = a :=
  (reduceVector_surjective F n a).choose_spec

/-- Restrict to the integer lattice and descend modulo `2𝒪ⁿ`. -/
def latticeRestriction (f : LocalLatticeSpace F n) : FiniteLatticeSpace (Integers F) n :=
  fun a => f.val.val (integralVector F n (residueVectorRepresentative F n a))

omit [FiniteDimensional ℚ_[2] F] in
theorem latticeRestriction_reduceVector (f : LocalLatticeSpace F n)
    (x : Fin n → Integers F) :
    latticeRestriction F n f (reduceVector F n x) = f.val.val (integralVector F n x) :=
  localLattice_eq_of_reduceVector_eq F n f _ x (reduceVector_representative F n _)

/-- The local lattice functions are exactly the functions on the finite quotient. -/
def latticeEquivFinite : LocalLatticeSpace F n ≃ₗ[ℂ] FiniteLatticeSpace (Integers F) n where
  toFun := latticeRestriction F n
  invFun := latticeExtension F n
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    apply LocallyConstant.ext
    intro z
    by_cases hz : z ∈ integralLattice F n
    · let x : Fin n → Integers F := fun i => ⟨z i, hz i⟩
      change latticeExtensionFun F n (latticeRestriction F n f) (integralVector F n x) = _
      rw [latticeExtensionFun_integralVector, latticeRestriction_reduceVector]
      rfl
    · change latticeExtensionFun F n (latticeRestriction F n f) z = f.val.val z
      rw [latticeExtensionFun_eq_zero F n _ z hz]
      exact (f.property.1 z (by simpa [integralLattice, not_forall] using hz)).symm
  right_inv g := by
    funext a
    change latticeExtensionFun F n g (integralVector F n (residueVectorRepresentative F n a)) = g a
    rw [latticeExtensionFun_integralVector, reduceVector_representative]
  map_add' f g := rfl
  map_smul' c f := rfl

@[simp]
theorem latticeEquivFinite_apply (f : LocalLatticeSpace F n) (x : Fin n → Integers F) :
    latticeEquivFinite F n f (reduceVector F n x) = f.val.val (integralVector F n x) :=
  latticeRestriction_reduceVector F n f x

@[simp]
theorem latticeEquivFinite_symm_apply (g : FiniteLatticeSpace (Integers F) n) (z : Fin n → F) :
    ((latticeEquivFinite F n).symm g).val.val z = latticeExtensionFun F n g z := rfl

/-- The delta function labelled by a vector of residue classes. -/
def latticeDelta (a : Fin n → R (Integers F)) : LocalLatticeSpace F n :=
  (latticeEquivFinite F n).symm (Pi.single a 1)

/-- The finite standard function basis transported to the actual local function space. -/
def latticeDeltaBasis : Module.Basis (Fin n → R (Integers F)) ℂ (LocalLatticeSpace F n) :=
  (Pi.basisFun ℂ (Fin n → R (Integers F))).map (latticeEquivFinite F n).symm

@[simp]
theorem latticeDeltaBasis_apply (a : Fin n → R (Integers F)) :
    latticeDeltaBasis F n a = latticeDelta F n a := by
  simp [latticeDeltaBasis, latticeDelta]

/-- On the integer lattice, a delta function tests equality of residue labels. -/
theorem latticeDelta_integralVector (a : Fin n → R (Integers F)) (x : Fin n → Integers F) :
    (latticeDelta F n a).val.val (integralVector F n x) =
      if reduceVector F n x = a then 1 else 0 := by
  simp [latticeDelta, latticeEquivFinite_symm_apply, latticeExtensionFun_integralVector,
    Pi.single_apply, eq_comm]

theorem latticeDelta_eq_zero (a : Fin n → R (Integers F)) (z : Fin n → F)
    (hz : z ∉ integralLattice F n) : (latticeDelta F n a).val.val z = 0 :=
  latticeExtensionFun_eq_zero F n _ z hz

/-- The local delta functions are exactly the characteristic functions of residue cosets. -/
theorem latticeDelta_eq_indicator (a : Fin n → R (Integers F)) :
    ((latticeDelta F n a).val.val : (Fin n → F) → ℂ) =
      (latticeCoset F n (residueVectorRepresentative F n a)).indicator (fun _ => 1) := by
  funext z
  by_cases hz : z ∈ integralLattice F n
  · let x : Fin n → Integers F := fun i => ⟨z i, hz i⟩
    change (latticeDelta F n a).val.val (integralVector F n x) = _
    rw [latticeDelta_integralVector]
    have hm : z ∈ latticeCoset F n (residueVectorRepresentative F n a) ↔
        reduceVector F n x = a := by
      change integralVector F n x ∈ _ ↔ _
      rw [integralVector_mem_latticeCoset_iff, reduceVector_representative]
    simp only [Set.indicator_apply, hm]
  · rw [latticeDelta_eq_zero F n a z hz, Set.indicator_of_notMem]
    exact fun h => hz (latticeCoset_subset_integralLattice F n _ h)

/-- For every integer representative `x`, the note's formula is `δ_[x] = 1_(x+2𝒪ⁿ)`. -/
theorem latticeDelta_reduceVector_eq_indicator (x : Fin n → Integers F) :
    ((latticeDelta F n (reduceVector F n x)).val.val : (Fin n → F) → ℂ) =
      (latticeCoset F n x).indicator (fun _ => 1) := by
  rw [latticeDelta_eq_indicator,
    latticeCoset_eq_of_reduceVector_eq F n _ x (reduceVector_representative F n _)]

/-- Ordinary and topological supports are the compact open residue coset. -/
theorem latticeDelta_support (a : Fin n → R (Integers F)) :
    Function.support ((latticeDelta F n a).val.val : (Fin n → F) → ℂ) =
      latticeCoset F n (residueVectorRepresentative F n a) := by
  rw [latticeDelta_eq_indicator]
  ext z
  simp

theorem latticeDelta_tsupport (a : Fin n → R (Integers F)) :
    tsupport ((latticeDelta F n a).val.val : (Fin n → F) → ℂ) =
      latticeCoset F n (residueVectorRepresentative F n a) := by
  rw [tsupport, latticeDelta_support,
    (latticeCoset_isClopen F n (residueVectorRepresentative F n a)).isClosed.closure_eq]

/-- The coefficient of a delta basis vector is the function's value on that residue class. -/
theorem latticeDeltaBasis_repr (f : LocalLatticeSpace F n) (a : Fin n → R (Integers F)) :
    (latticeDeltaBasis F n).repr f a = latticeEquivFinite F n f a := by
  rfl

/-- Every local lattice function has its finite delta expansion. -/
theorem latticeDelta_expansion (f : LocalLatticeSpace F n) :
    ∑ a, latticeEquivFinite F n f a • latticeDelta F n a = f := by
  simpa only [Module.Basis.equivFun_apply, latticeDeltaBasis_repr, latticeDeltaBasis_apply] using
    (latticeDeltaBasis F n).sum_equivFun f

instance localLatticeSpace_finiteDimensional : FiniteDimensional ℂ (LocalLatticeSpace F n) :=
  Module.Finite.equiv (latticeEquivFinite F n).symm

/-- The local lattice model has the dimension stated in §1.3. -/
theorem localLatticeSpace_finrank :
    Module.finrank ℂ (LocalLatticeSpace F n) =
      residueCard F ^ (ramificationIndex (Integers F) * n) := by
  rw [(latticeEquivFinite F n).finrank_eq]
  exact Char2Theta.dyadic_finiteLatticeSpace_finrank F n

end
end Char2Theta.Dyadic

/-!
## The finite Fourier pairing on the local lattice model

The kernel is exactly `ψ(2x·y)` from (2.3), for any character satisfying (1.2).
This file constructs the invertible finite transform; identifying it, with its
Weil scalar, as a restriction of a local metaplectic operator is a separate step.
-/

namespace Char2Theta.Dyadic
noncomputable section
open scoped BigOperators

variable (F : Type*) [Field F] [Algebra ℚ_[2] F] [FiniteDimensional ℚ_[2] F]
  (ψ : AddChar F ℂˣ) (hψ : HasConductorFour (Integers F).toSubring ψ)

/-- The character `x mod 2 ↦ ψ(2x)`, with values in complex units. -/
def characterModTwo : AddChar (R (Integers F)) ℂˣ := by
  let χ : AddChar (Integers F) ℂˣ := ψ.compAddMonoidHom
    { toFun := fun x => 2 * (x : F)
      map_zero' := by simp
      map_add' := fun x y => by simp [mul_add] }
  exact AddChar.toAddMonoidHomEquiv.symm
    (QuotientAddGroup.lift (rationalIdeal (Integers F) 2).toAddSubgroup χ.toAddMonoidHom (by
      intro x hx
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
      change ψ ((2 : F) * (2 * (y : F))) = 1
      rw [← mul_assoc]
      norm_num
      exact trivial_on_four (Integers F).toSubring ψ hψ y))

omit [FiniteDimensional ℚ_[2] F] in
@[simp]
theorem characterModTwo_mk (x : Integers F) :
    characterModTwo F ψ hψ (Ideal.Quotient.mk (rationalIdeal (Integers F) 2) x) = ψ (2 * (x : F)) := rfl

omit [FiniteDimensional ℚ_[2] F] in
/-- The annihilator of the finite pairing is zero, also in ramified extensions. -/
theorem characterModTwo_annihilator (a : R (Integers F)) :
    (∀ b, characterModTwo F ψ hψ (a * b) = 1) ↔ a = 0 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  constructor
  · intro hx
    have hc : ∀ y : Integers F, ψ ((2 * (x : F)) * (y : F)) = 1 := by
      intro y
      simpa only [← map_mul, characterModTwo_mk, Subalgebra.coe_mul, mul_assoc] using
        hx (Ideal.Quotient.mk (rationalIdeal (Integers F) 2) y)
    obtain ⟨y, hy⟩ := (conductor_mem_iff (Integers F).toSubring ψ hψ (2 * (x : F))).mp hc
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_span_singleton.mpr
    refine ⟨y, ?_⟩
    apply Subtype.val_injective
    change (x : F) = 2 * (y : F)
    have h2 : (2 : F) ≠ 0 := by norm_num
    apply mul_left_cancel₀ h2
    calc
      2 * (x : F) = 4 * (y : F) := hy
      _ = 2 * (2 * (y : F)) := by ring
  · intro ha b
    rw [ha, zero_mul, AddChar.map_zero_eq_one]

omit [FiniteDimensional ℚ_[2] F] in
theorem characterModTwo_isPrimitive : (characterModTwo F ψ hψ).IsPrimitive := by
  intro a ha h
  apply ha
  apply (characterModTwo_annihilator F ψ hψ a).mp
  intro b
  exact congrArg (fun χ : AddChar (R (Integers F)) ℂˣ => χ b) h

/-- The character in the second variable of the finite Fourier pairing. -/
def fourierPairingChar (n : ℕ) (a : Fin n → R (Integers F)) :
    AddChar (Fin n → R (Integers F)) ℂ where
  toFun b := ∏ i, (characterModTwo F ψ hψ (a i * b i) : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' b c := by simp [mul_add, AddChar.map_add_eq_mul, Finset.prod_mul_distrib]

omit [FiniteDimensional ℚ_[2] F] in
@[simp]
theorem fourierPairingChar_single (n : ℕ) (a : Fin n → R (Integers F))
    (i : Fin n) (b : R (Integers F)) :
    fourierPairingChar F ψ hψ n a (Pi.single i b) = characterModTwo F ψ hψ (a i * b) := by
  classical
  simp [fourierPairingChar, Pi.single_apply, apply_ite]

omit [FiniteDimensional ℚ_[2] F] in
theorem fourierPairingChar_injective (n : ℕ) : Function.Injective (fourierPairingChar F ψ hψ n) := by
  intro a b h
  funext i
  apply AddChar.to_mulShift_inj_of_isPrimitive (characterModTwo_isPrimitive F ψ hψ)
  apply AddChar.ext
  intro t
  apply Units.val_injective
  simpa only [fourierPairingChar_single, AddChar.mulShift_apply] using
    congrArg (fun χ : AddChar (Fin n → R (Integers F)) ℂ => χ (Pi.single i t)) h

/-- The pairing characters form a basis, by mathlib's character independence theorem. -/
def finiteFourierBasis (n : ℕ) :
    Module.Basis (Fin n → R (Integers F)) ℂ (FiniteLatticeSpace (Integers F) n) :=
  basisOfLinearIndependentOfCardEqFinrank
    ((AddChar.linearIndependent (Fin n → R (Integers F)) ℂ).comp _
      (fourierPairingChar_injective F ψ hψ n)) (by
      rw [Module.finrank_fintype_fun_eq_card])

@[simp]
theorem finiteFourierBasis_apply (n : ℕ) (a b : Fin n → R (Integers F)) :
    finiteFourierBasis F ψ hψ n a b = fourierPairingChar F ψ hψ n a b := by
  rw [finiteFourierBasis, coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

/-- The unnormalized finite Fourier transform as a complex linear equivalence. -/
def finiteFourier (n : ℕ) : FiniteLatticeSpace (Integers F) n ≃ₗ[ℂ] FiniteLatticeSpace (Integers F) n :=
  (finiteFourierBasis F ψ hψ n).equivFun.symm

theorem finiteFourier_apply (n : ℕ) (f : FiniteLatticeSpace (Integers F) n)
    (b : Fin n → R (Integers F)) :
    finiteFourier F ψ hψ n f b = ∑ a, f a * fourierPairingChar F ψ hψ n a b := by
  simp [finiteFourier, Module.Basis.equivFun_symm_apply, Finset.sum_apply]

end

noncomputable section
variable (F : Type*) [NormedField F] [NormedAlgebra ℚ_[2] F]
  [FiniteDimensional ℚ_[2] F] (n : ℕ)
  (ψ : AddChar F ℂˣ) (hψ : HasConductorFour (Integers F).toSubring ψ)

omit [FiniteDimensional ℚ_[2] F] in
/-- On integer representatives the finite pairing has exactly the kernel in (2.3). -/
theorem fourierPairingChar_integral (x y : Fin n → Integers F) :
    fourierPairingChar F ψ hψ n (reduceVector F n x) (reduceVector F n y) =
      (ψ (2 * ∑ i, (x i : F) * (y i : F)) : ℂ) := by
  change (∏ i, (characterModTwo F ψ hψ
    (Ideal.Quotient.mk _ (x i) * Ideal.Quotient.mk _ (y i)) : ℂ)) = _
  simp only [← map_mul, characterModTwo_mk, Subalgebra.coe_mul]
  rw [Finset.mul_sum]
  have hs : ∀ s : Finset (Fin n),
      (∏ i ∈ s, (ψ (2 * ((x i : F) * (y i : F))) : ℂ)) =
        (ψ (∑ i ∈ s, 2 * ((x i : F) * (y i : F))) : ℂ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [hi, ψ.map_add_eq_mul, ih]
  exact hs Finset.univ

/-- The finite Fourier equivalence transported to the actual lattice space,
with an explicit nonzero scalar factor. No Weil scalar is silently discarded. -/
def latticeFiniteFourier (c : ℂˣ) : LocalLatticeSpace F n ≃ₗ[ℂ] LocalLatticeSpace F n :=
  (latticeEquivFinite F n).trans
    (((finiteFourier F ψ hψ n).trans (LinearEquiv.smulOfUnit c)).trans
      (latticeEquivFinite F n).symm)

/-- The coordinate formula for the transported finite transform. -/
theorem latticeFiniteFourier_apply (c : ℂˣ) (f : LocalLatticeSpace F n)
    (y : Fin n → Integers F) :
    (latticeFiniteFourier F n ψ hψ c f).val.val (integralVector F n y) =
      (c : ℂ) * ∑ a, latticeEquivFinite F n f a *
        fourierPairingChar F ψ hψ n a (reduceVector F n y) := by
  change latticeExtensionFun F n
    ((LinearEquiv.smulOfUnit c) (finiteFourier F ψ hψ n (latticeEquivFinite F n f)))
      (integralVector F n y) = _
  rw [latticeExtensionFun_integralVector]
  change (c : ℂ) * finiteFourier F ψ hψ n (latticeEquivFinite F n f) (reduceVector F n y) = _
  rw [finiteFourier_apply]

end
end Char2Theta.Dyadic

/-! ## Multiplication and changes of variables on Schwartz–Bruhat functions -/

namespace Char2Theta.Dyadic
noncomputable section

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- Multiplication by a locally constant complex function preserves compact support. -/
def schwartzMul (m : LocallyConstant X ℂ) (f : SchwartzBruhat X) : SchwartzBruhat X :=
  ⟨⟨fun x => m x * f.val x, m.isLocallyConstant.mul f.val.isLocallyConstant⟩,
    HasCompactSupport.mul_left (f := (m : X → ℂ)) f.property⟩

/-- Multiplication by a locally constant, nowhere-zero function. -/
def schwartzMultiplier (m : LocallyConstant X ℂˣ) : SchwartzBruhat X ≃ₗ[ℂ] SchwartzBruhat X where
  toFun := schwartzMul (m.map (fun u : ℂˣ => (u : ℂ)))
  invFun := schwartzMul (m.map (fun u : ℂˣ => ((u⁻¹ : ℂˣ) : ℂ)))
  left_inv f := by
    apply Subtype.ext
    ext x
    change (((m x)⁻¹ : ℂˣ) : ℂ) * ((m x : ℂ) * f.val x) = f.val x
    simp
  right_inv f := by
    apply Subtype.ext
    ext x
    change (m x : ℂ) * ((((m x)⁻¹ : ℂˣ) : ℂ) * f.val x) = f.val x
    simp
  map_add' f g := by
    apply Subtype.ext
    ext x
    exact mul_add _ _ _
  map_smul' c f := by
    apply Subtype.ext
    ext x
    change (m x : ℂ) * (c * f.val x) = c * ((m x : ℂ) * f.val x)
    ring

@[simp]
theorem schwartzMultiplier_apply (m : LocallyConstant X ℂˣ) (f : SchwartzBruhat X) (x : X) :
    (schwartzMultiplier m f).val x = (m x : ℂ) * f.val x := rfl

/-- Pullback along a homeomorphism preserves local constancy and compact support. -/
def schwartzPullback (e : X ≃ₜ X) : SchwartzBruhat X ≃ₗ[ℂ] SchwartzBruhat X where
  toFun f := ⟨f.val.comap ⟨e, e.continuous⟩, f.property.comp_isClosedEmbedding e.isClosedEmbedding⟩
  invFun f := ⟨f.val.comap ⟨e.symm, e.symm.continuous⟩,
    f.property.comp_isClosedEmbedding e.symm.isClosedEmbedding⟩
  left_inv f := by apply Subtype.ext; ext x; exact congrArg f.val (e.apply_symm_apply x)
  right_inv f := by apply Subtype.ext; ext x; exact congrArg f.val (e.symm_apply_apply x)
  map_add' f g := rfl
  map_smul' c f := rfl

@[simp]
theorem schwartzPullback_apply (e : X ≃ₜ X) (f : SchwartzBruhat X) (x : X) :
    (schwartzPullback e f).val x = f.val (e x) := rfl

end
end Char2Theta.Dyadic

/-!
## Integral upper-root phase operators

These are the actual multiplication operators in equation (2.2), on the ambient
Schwartz–Bruhat space and its original lattice subspace. This file does not
construct the metaplectic covering group or identify these operators with lifts
in a previously constructed Weil representation.
-/

namespace Char2Theta.Dyadic
noncomputable section

variable (F : Type*) [NormedField F] [NormedAlgebra ℚ_[2] F]
  [FiniteDimensional ℚ_[2] F] (n : ℕ)

omit [FiniteDimensional ℚ_[2] F] in
/-- An integral-periodic multiplier preserves the original lattice subspace. -/
theorem schwartzMultiplier_mem_lattice
    (m : LocallyConstant (Fin n → F) ℂˣ)
    (hm : ∀ (x u : Fin n → Integers F),
      m (integralVector F n x + fun i => 2 * (u i : F)) = m (integralVector F n x))
    (f : SchwartzBruhat (Fin n → F)) (hf : f ∈ LocalLatticeSpace F n) :
    schwartzMultiplier m f ∈ LocalLatticeSpace F n := by
  constructor
  · intro z hz
    change (m z : ℂ) * f.val z = 0
    rw [hf.1 z hz, mul_zero]
  · intro z u
    change (m (z + fun i => 2 * (u i : F)) : ℂ) * f.val (z + fun i => 2 * (u i : F)) =
      (m z : ℂ) * f.val z
    rw [hf.2 z u]
    by_cases hz : z ∈ integralLattice F n
    · let x : Fin n → Integers F := fun i => ⟨z i, hz i⟩
      exact congrArg (fun c : ℂˣ => (c : ℂ) * f.val z) (hm x u)
    · have hfz := hf.1 z (by simpa [integralLattice, not_forall] using hz)
      rw [hfz, mul_zero, mul_zero]

/-- Restriction of a proved integral-periodic ambient multiplier to `S_L`. -/
def latticeMultiplier (m : LocallyConstant (Fin n → F) ℂˣ)
    (hm : ∀ (x u : Fin n → Integers F),
      m (integralVector F n x + fun i => 2 * (u i : F)) = m (integralVector F n x)) :
    LocalLatticeSpace F n ≃ₗ[ℂ] LocalLatticeSpace F n :=
  (schwartzMultiplier m).ofSubmodules _ _ (by
    apply le_antisymm
    · rintro _ ⟨f, hf, rfl⟩
      exact schwartzMultiplier_mem_lattice F n m hm f hf
    · intro f hf
      refine ⟨(schwartzMultiplier m).symm f, ?_, (schwartzMultiplier m).apply_symm_apply f⟩
      exact schwartzMultiplier_mem_lattice F n m⁻¹
        (fun x u => congrArg Inv.inv (hm x u)) f hf)

omit [FiniteDimensional ℚ_[2] F] in
@[simp]
theorem latticeMultiplier_apply (m : LocallyConstant (Fin n → F) ℂˣ) (hm)
    (f : LocalLatticeSpace F n) (z : Fin n → F) :
    (latticeMultiplier F n m hm f).val.val z = (m z : ℂ) * f.val.val z := rfl

variable (ψ : AddChar F ℂˣ) (hψ : HasConductorFour (Integers F).toSubring ψ)

/-- Compose the chosen smooth character with a continuous polynomial phase. -/
def polynomialPhase (P : (Fin n → F) → F) (hP : Continuous P) :
    LocallyConstant (Fin n → F) ℂˣ :=
  ⟨fun z => ψ (P z), (smoothCharacter_of_hasConductorFour F ψ hψ).comp_continuous hP⟩

/-- The long-root multiplier `ψ(t yᵢ²)`. -/
def longRootPhase (i : Fin n) (t : Integers F) : LocallyConstant (Fin n → F) ℂˣ :=
  polynomialPhase F n ψ hψ (fun z => (t : F) * z i ^ 2)
    (continuous_const.mul ((continuous_apply i).pow 2))

/-- The upper short-root multiplier `ψ(2t yᵢ yⱼ)`. For roots one takes `i≠j`. -/
def shortRootPhase (i j : Fin n) (t : Integers F) : LocallyConstant (Fin n → F) ℂˣ :=
  polynomialPhase F n ψ hψ (fun z => 2 * (t : F) * z i * z j)
    (((continuous_const.mul continuous_const).mul (continuous_apply i)).mul (continuous_apply j))

omit [FiniteDimensional ℚ_[2] F] in
include hψ in
/-- The conductor turns an integral phase difference divisible by four into equal values. -/
theorem character_eq_of_sub_eq_four (a b : F) (v : Integers F) (h : a - b = 4 * (v : F)) :
    ψ a = ψ b := by
  have hh : ψ (a - b) = 1 := by rw [h]; exact trivial_on_four (Integers F).toSubring ψ hψ v
  rw [ψ.map_sub_eq_div] at hh
  exact div_eq_one.mp hh

theorem longRootPhase_periodic (i : Fin n) (t : Integers F) (x u : Fin n → Integers F) :
    longRootPhase F n ψ hψ i t (integralVector F n x + fun k => 2 * (u k : F)) =
      longRootPhase F n ψ hψ i t (integralVector F n x) := by
  apply character_eq_of_sub_eq_four F ψ hψ _ _ (t * (x i * u i + u i ^ 2))
  change (t : F) * ((x i : F) + 2 * (u i : F)) ^ 2 - (t : F) * (x i : F) ^ 2 =
    4 * ((t : F) * ((x i : F) * (u i : F) + (u i : F) ^ 2))
  ring

theorem shortRootPhase_periodic (i j : Fin n) (t : Integers F) (x u : Fin n → Integers F) :
    shortRootPhase F n ψ hψ i j t (integralVector F n x + fun k => 2 * (u k : F)) =
      shortRootPhase F n ψ hψ i j t (integralVector F n x) := by
  apply character_eq_of_sub_eq_four F ψ hψ _ _
    (t * (x i * u j + u i * x j + 2 * u i * u j))
  change 2 * (t : F) * ((x i : F) + 2 * (u i : F)) * ((x j : F) + 2 * (u j : F)) -
    2 * (t : F) * (x i : F) * (x j : F) =
    4 * ((t : F) * ((x i : F) * (u j : F) + (u i : F) * (x j : F) +
      2 * (u i : F) * (u j : F)))
  ring

/-- The long-root operator, constructed on the full local function space. -/
def longRootOperator (i : Fin n) (t : Integers F) :=
  schwartzMultiplier (longRootPhase F n ψ hψ i t)

/-- The upper short-root operator, constructed on the full local function space. -/
def shortRootOperator (i j : Fin n) (t : Integers F) :=
  schwartzMultiplier (shortRootPhase F n ψ hψ i j t)

theorem longRootOperator_stable (i : Fin n) (t : Integers F)
    (f : SchwartzBruhat (Fin n → F)) (hf : f ∈ LocalLatticeSpace F n) :
    longRootOperator F n ψ hψ i t f ∈ LocalLatticeSpace F n :=
  schwartzMultiplier_mem_lattice F n _ (longRootPhase_periodic F n ψ hψ i t) f hf

theorem shortRootOperator_stable (i j : Fin n) (t : Integers F)
    (f : SchwartzBruhat (Fin n → F)) (hf : f ∈ LocalLatticeSpace F n) :
    shortRootOperator F n ψ hψ i j t f ∈ LocalLatticeSpace F n :=
  schwartzMultiplier_mem_lattice F n _ (shortRootPhase_periodic F n ψ hψ i j t) f hf

/-- The restriction of the long-root operator to the lattice space. -/
def latticeLongRoot (i : Fin n) (t : Integers F) : LocalLatticeSpace F n ≃ₗ[ℂ] LocalLatticeSpace F n :=
  latticeMultiplier F n _ (longRootPhase_periodic F n ψ hψ i t)

/-- The restriction of the upper short-root operator to the lattice space. -/
def latticeShortRoot (i j : Fin n) (t : Integers F) : LocalLatticeSpace F n ≃ₗ[ℂ] LocalLatticeSpace F n :=
  latticeMultiplier F n _ (shortRootPhase_periodic F n ψ hψ i j t)

@[simp]
theorem latticeLongRoot_apply (i : Fin n) (t : Integers F) (f : LocalLatticeSpace F n) (z : Fin n → F) :
    (latticeLongRoot F n ψ hψ i t f).val.val z = (ψ ((t : F) * z i ^ 2) : ℂ) * f.val.val z := rfl

@[simp]
theorem latticeShortRoot_apply (i j : Fin n) (t : Integers F) (f : LocalLatticeSpace F n) (z : Fin n → F) :
    (latticeShortRoot F n ψ hψ i j t f).val.val z = (ψ (2 * (t : F) * z i * z j) : ℂ) * f.val.val z := rfl

/-- The long-root family satisfies the additive parameter law on actual local functions. -/
def latticeLongRootRepresentation (i : Fin n) :
    Representation ℂ (Multiplicative (Integers F)) (LocalLatticeSpace F n) where
  toFun t := (latticeLongRoot F n ψ hψ i t.toAdd).toLinearMap
  map_one' := by
    ext f z
    change (ψ ((0 : F) * z i ^ 2) : ℂ) * f.val.val z = f.val.val z
    simp
  map_mul' t s := by
    ext f z
    change (ψ (((t.toAdd : F) + (s.toAdd : F)) * z i ^ 2) : ℂ) * f.val.val z =
      (ψ ((t.toAdd : F) * z i ^ 2) : ℂ) *
        ((ψ ((s.toAdd : F) * z i ^ 2) : ℂ) * f.val.val z)
    simp [add_mul, ψ.map_add_eq_mul, mul_assoc]

/-- The upper short-root family also gives a representation of the additive parameter group. -/
def latticeShortRootRepresentation (i j : Fin n) :
    Representation ℂ (Multiplicative (Integers F)) (LocalLatticeSpace F n) where
  toFun t := (latticeShortRoot F n ψ hψ i j t.toAdd).toLinearMap
  map_one' := by
    ext f z
    change (ψ (2 * (0 : F) * z i * z j) : ℂ) * f.val.val z = f.val.val z
    simp
  map_mul' t s := by
    ext f z
    change (ψ (2 * ((t.toAdd : F) + (s.toAdd : F)) * z i * z j) : ℂ) * f.val.val z =
      (ψ (2 * (t.toAdd : F) * z i * z j) : ℂ) *
        ((ψ (2 * (s.toAdd : F) * z i * z j) : ℂ) * f.val.val z)
    simp [mul_add, add_mul, ψ.map_add_eq_mul, mul_assoc]

/-- The restricted long-root operator has the stated finite coordinate formula. -/
theorem latticeLongRoot_finite (i : Fin n) (t : Integers F) (f : LocalLatticeSpace F n)
    (x : Fin n → Integers F) :
    latticeEquivFinite F n (latticeLongRoot F n ψ hψ i t f) (reduceVector F n x) =
      (ψ ((t : F) * (x i : F) ^ 2) : ℂ) * latticeEquivFinite F n f (reduceVector F n x) := by
  simp [integralVector]

theorem latticeShortRoot_finite (i j : Fin n) (t : Integers F) (f : LocalLatticeSpace F n)
    (x : Fin n → Integers F) :
    latticeEquivFinite F n (latticeShortRoot F n ψ hψ i j t f) (reduceVector F n x) =
      (ψ (2 * (t : F) * (x i : F) * (x j : F)) : ℂ) *
        latticeEquivFinite F n f (reduceVector F n x) := by
  simp [integralVector]

end
end Char2Theta.Dyadic

/-!
## Integral changes of coordinates in the upper root operators

The shear here is the first formula of (2.2), with its action proved on actual
local functions. No metaplectic covering group is postulated.
-/

namespace Char2Theta.Dyadic
noncomputable section
open scoped Classical

variable (F : Type*) [NormedField F] [NormedAlgebra ℚ_[2] F]
  [FiniteDimensional ℚ_[2] F] (n : ℕ)

/-- The elementary coordinate change `y ↦ y + t yᵢ eⱼ`, for `i≠j`. -/
def rootShear (i j : Fin n) (hij : i ≠ j) (t : F) : (Fin n → F) ≃ₜ (Fin n → F) where
  toFun z k := if k = j then z j + t * z i else z k
  invFun z k := if k = j then z j + (-t) * z i else z k
  left_inv z := by
    funext k
    by_cases hk : k = j <;> simp [hk, hij]
  right_inv z := by
    funext k
    by_cases hk : k = j <;> simp [hk, hij]
  continuous_toFun := continuous_pi fun k => by
    by_cases hk : k = j <;> simp only [hk, ↓reduceIte] <;> fun_prop
  continuous_invFun := continuous_pi fun k => by
    by_cases hk : k = j <;> simp only [hk, ↓reduceIte] <;> fun_prop

/-- The corresponding change of integer coordinates. -/
def integralRootShear (i j : Fin n) (t : Integers F) (x : Fin n → Integers F) : Fin n → Integers F :=
  fun k => if k = j then x j + t * x i else x k

omit [FiniteDimensional ℚ_[2] F] in
@[simp]
theorem rootShear_integralVector (i j : Fin n) (hij : i ≠ j) (t : Integers F)
    (x : Fin n → Integers F) :
    rootShear F n i j hij t (integralVector F n x) =
      integralVector F n (integralRootShear F n i j t x) := by
  funext k
  by_cases hk : k = j <;> simp [rootShear, integralRootShear, integralVector, hk]

omit [FiniteDimensional ℚ_[2] F] in
theorem rootShear_mem_integralLattice_iff (i j : Fin n) (hij : i ≠ j) (t : Integers F)
    (z : Fin n → F) :
    rootShear F n i j hij t z ∈ integralLattice F n ↔ z ∈ integralLattice F n := by
  constructor
  · intro h k
    by_cases hk : k = j
    · subst k
      have hi : z i ∈ Integers F := by simpa [rootShear, hij] using h i
      have hj : z j + (t : F) * z i ∈ Integers F := by simpa [rootShear] using h j
      simpa using (Integers F).sub_mem hj ((Integers F).mul_mem t.property hi)
    · simpa [rootShear, hk] using h k
  · intro h k
    by_cases hk : k = j
    · simpa [rootShear, hk] using
        (Integers F).add_mem (h j) ((Integers F).mul_mem t.property (h i))
    · simpa [rootShear, hk] using h k

omit [FiniteDimensional ℚ_[2] F] in
theorem rootShear_add_two (i j : Fin n) (hij : i ≠ j) (t : Integers F)
    (z : Fin n → F) (u : Fin n → Integers F) :
    rootShear F n i j hij t (z + fun k => 2 * (u k : F)) =
      rootShear F n i j hij t z + fun k => 2 * (integralRootShear F n i j t u k : F) := by
  funext k
  by_cases hk : k = j
  · simp [rootShear, integralRootShear, hk]
    ring
  · simp [rootShear, integralRootShear, hk]

/-- The shear operator on the entire Schwartz–Bruhat space. -/
def shearOperator (i j : Fin n) (hij : i ≠ j) (t : Integers F) :=
  schwartzPullback (rootShear F n i j hij t)

omit [FiniteDimensional ℚ_[2] F] in
theorem shearOperator_stable (i j : Fin n) (hij : i ≠ j) (t : Integers F)
    (f : SchwartzBruhat (Fin n → F)) (hf : f ∈ LocalLatticeSpace F n) :
    shearOperator F n i j hij t f ∈ LocalLatticeSpace F n := by
  constructor
  · intro z hz
    apply hf.1
    have hn : z ∉ integralLattice F n := by simpa [integralLattice, not_forall] using hz
    have hn' := mt (rootShear_mem_integralLattice_iff F n i j hij t z).mp hn
    simpa [integralLattice, not_forall] using hn'
  · intro z u
    change f.val (rootShear F n i j hij t (z + fun k => 2 * (u k : F))) = _
    rw [rootShear_add_two]
    exact hf.2 _ _

/-- Restriction of the ambient shear operator, with stability proved in both directions. -/
def latticeShear (i j : Fin n) (hij : i ≠ j) (t : Integers F) :
    LocalLatticeSpace F n ≃ₗ[ℂ] LocalLatticeSpace F n :=
  (shearOperator F n i j hij t).ofSubmodules _ _ (by
    apply le_antisymm
    · rintro _ ⟨f, hf, rfl⟩
      exact shearOperator_stable F n i j hij t f hf
    · intro f hf
      refine ⟨(shearOperator F n i j hij t).symm f, ?_,
        (shearOperator F n i j hij t).apply_symm_apply f⟩
      exact shearOperator_stable F n i j hij (-t) f hf)

omit [FiniteDimensional ℚ_[2] F] in
@[simp]
theorem latticeShear_apply (i j : Fin n) (hij : i ≠ j) (t : Integers F)
    (f : LocalLatticeSpace F n) (z : Fin n → F) :
    (latticeShear F n i j hij t f).val.val z = f.val.val (rootShear F n i j hij t z) := rfl

/-- The coordinate-shear family gives a representation of its additive parameter group. -/
def latticeShearRepresentation (i j : Fin n) (hij : i ≠ j) :
    Representation ℂ (Multiplicative (Integers F)) (LocalLatticeSpace F n) where
  toFun t := (latticeShear F n i j hij t.toAdd).toLinearMap
  map_one' := by
    ext f z
    change f.val.val (rootShear F n i j hij 0 z) = f.val.val z
    congr 1
    ext k
    by_cases hk : k = j <;> simp [rootShear, hk]
  map_mul' t s := by
    ext f z
    change f.val.val (rootShear F n i j hij ((t.toAdd : F) + (s.toAdd : F)) z) =
      f.val.val (rootShear F n i j hij s.toAdd (rootShear F n i j hij t.toAdd z))
    congr 1
    ext k
    by_cases hk : k = j <;> simp [rootShear, hk, hij]
    ring

/-- Coordinate formula after passing to the finite quotient model. -/
theorem latticeShear_finite (i j : Fin n) (hij : i ≠ j) (t : Integers F)
    (f : LocalLatticeSpace F n) (x : Fin n → Integers F) :
    latticeEquivFinite F n (latticeShear F n i j hij t f) (reduceVector F n x) =
      latticeEquivFinite F n f (reduceVector F n (integralRootShear F n i j t x)) := by
  simp

end
end Char2Theta.Dyadic

/-!
## Restricting an ambient representation using the lattice generator formulas

This is a conditional construction: the input is an actual representation of a
specified group, a proof that the specified elements generate that group, and
proofs of their operator formulas. In particular it does not supply the local
metaplectic cover, the Weil representation, or its Fourier restriction formula.
Once those inputs are available for the inverse image of `Sp(L)`, the output is
the restriction called `τ_L` in §1.3, on the original local function subspace.
-/

namespace Char2Theta.Dyadic
noncomputable section

section Restriction
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (U : Submodule ℂ V) [FiniteDimensional ℂ U]

/-- On a finite-dimensional invariant subspace, invariance under an invertible
ambient operator also implies invariance under its inverse. -/
theorem invariant_inverse_of_finiteDimensional (g : G)
    (h : ∀ v ∈ U, ρ g v ∈ U) : ∀ v ∈ U, ρ g⁻¹ v ∈ U := by
  let T : U →ₗ[ℂ] U := (ρ g).restrict (fun v hv => h v hv)
  have hi : Function.Injective T := by
    intro u v huv
    apply Subtype.ext
    exact (ρ.apply_bijective g).injective (congrArg Subtype.val huv)
  intro v hv
  obtain ⟨u, hu⟩ := LinearMap.surjective_of_injective hi ⟨v, hv⟩
  have he : ρ g u.val = v := congrArg Subtype.val hu
  rw [← he, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  exact u.property

/-- Forward invariance on group generators suffices for a finite-dimensional
subspace; no additional inverse-invariance hypothesis is needed. -/
theorem invariant_of_group_generators (S : Set G) (hS : Subgroup.closure S = ⊤)
    (h : ∀ g ∈ S, ∀ v ∈ U, ρ g v ∈ U) : ∀ g : G, ∀ v ∈ U, ρ g v ∈ U := by
  intro g
  have hg : g ∈ Subgroup.closure S := by rw [hS]; trivial
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact h g hg
  | one => intro v hv; simpa using hv
  | mul g k _ _ hg hk =>
    intro v hv
    simpa only [map_mul, Module.End.mul_apply] using hg _ (hk v hv)
  | inv g _ hg => exact invariant_inverse_of_finiteDimensional ρ U g hg

end Restriction

variable (F : Type*) [NormedField F] [NormedAlgebra ℚ_[2] F]
  [FiniteDimensional ℚ_[2] F] (n : ℕ)
  (ψ : AddChar F ℂˣ) (hψ : HasConductorFour (Integers F).toSubring ψ)

/-- Operator formulas sufficient for lattice stability. The Fourier case is an
explicit equality on `S_L` to be proved for an ambient Fourier operator; the
invertibility of the finite transform alone does not establish that equality. -/
inductive LatticeGeneratorFormula (T : Module.End ℂ (SchwartzBruhat (Fin n → F))) : Prop
  | longRoot (i : Fin n) (t : Integers F)
      (h : T = (longRootOperator F n ψ hψ i t).toLinearMap)
  | shortRoot (i j : Fin n) (t : Integers F)
      (h : T = (shortRootOperator F n ψ hψ i j t).toLinearMap)
  | shear (i j : Fin n) (hij : i ≠ j) (t : Integers F)
      (h : T = (shearOperator F n i j hij t).toLinearMap)
  | fourier (c : ℂˣ)
      (h : ∀ f : LocalLatticeSpace F n, T f.val = (latticeFiniteFourier F n ψ hψ c f).val)
  | scalar (c : ℂ) (h : T = c • LinearMap.id)

/-- Each listed formula preserves the support and periodicity defining `S_L`. -/
theorem LatticeGeneratorFormula.stable
    {T : Module.End ℂ (SchwartzBruhat (Fin n → F))}
    (h : LatticeGeneratorFormula F n ψ hψ T)
    (f : SchwartzBruhat (Fin n → F)) (hf : f ∈ LocalLatticeSpace F n) :
    T f ∈ LocalLatticeSpace F n := by
  cases h with
  | longRoot i t h => rw [h]; exact longRootOperator_stable F n ψ hψ i t f hf
  | shortRoot i j t h => rw [h]; exact shortRootOperator_stable F n ψ hψ i j t f hf
  | shear i j hij t h => rw [h]; exact shearOperator_stable F n i j hij t f hf
  | fourier c h => rw [h ⟨f, hf⟩]; exact (latticeFiniteFourier F n ψ hψ c ⟨f, hf⟩).property
  | scalar c h => rw [h]; exact (LocalLatticeSpace F n).smul_mem c hf

variable {G : Type*} [Group G] (ω : Representation ℂ G (SchwartzBruhat (Fin n → F)))
  (S : Set G) (hS : Subgroup.closure S = ⊤)
  (hform : ∀ g ∈ S, LatticeGeneratorFormula F n ψ hψ (ω g))

include hS hform in
/-- Conditional stability for an ambient representation with verified generator
formulas. No existence of such a representation is asserted here. -/
theorem lattice_stable_of_generatorFormulas (g : G)
    (f : SchwartzBruhat (Fin n → F)) (hf : f ∈ LocalLatticeSpace F n) :
    ω g f ∈ LocalLatticeSpace F n :=
  invariant_of_group_generators ω (LocalLatticeSpace F n) S hS
    (fun g hg f hf => (hform g hg).stable F n ψ hψ f hf) g f hf

/-- The original lattice submodule as a mathlib subrepresentation, conditional
on the ambient representation, generation, and formula inputs. -/
def latticeSubrepresentationOfGenerators : Subrepresentation ω where
  toSubmodule := LocalLatticeSpace F n
  apply_mem_toSubmodule g _ hf :=
    lattice_stable_of_generatorFormulas F n ψ hψ ω S hS hform g _ hf

/-- The restriction construction that will give `τ_L` after an actual local Weil
representation and its generator formulas have been supplied. -/
def latticeRepresentationOfGenerators : Representation ℂ G (LocalLatticeSpace F n) :=
  (latticeSubrepresentationOfGenerators F n ψ hψ ω S hS hform).toRepresentation

/-- The inclusion into local Schwartz–Bruhat functions intertwines the restricted
representation with the given ambient representation. -/
@[simp]
theorem latticeRepresentationOfGenerators_apply (g : G) (f : LocalLatticeSpace F n) :
    (latticeRepresentationOfGenerators F n ψ hψ ω S hS hform g f).val = ω g f.val := rfl

end
end Char2Theta.Dyadic
