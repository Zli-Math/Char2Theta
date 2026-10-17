import Char2Theta.Section1.DyadicArithmetic
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Dyadic 局部拓扑、加法特征与导子（式 (1.2)）

本文件先建立局部域的完备、局部紧与超度量结构，并证明整数环及非零整数倍
紧开；再定义导子条件，刻画其与模四商上本原性的等价，构造满足 (1.2) 的
光滑加法特征。`d>1` 时，普通核严格大于 `4𝒪`，不可与导子混同。

主要入口：`integers_isCompact`、`integers_isOpen`、
`hasConductorFour_iff_isPrimitive`、`character_kernel_ne_four`、
`conductorFourCharacter`、`exists_smooth_character_conductor_four`。
可开启 `SpectralTopology` 作用域，从有限扩张假设选取相容谱范数。
坐标格及有限函数空间维数统一放在 `DyadicLatticeModel`。
-/

set_option autoImplicit false

/-!
## The topology of a finite dyadic extension (§1.3)

The scope `Char2Theta.Dyadic.SpectralTopology` supplies the spectral norm
and its compatible `ℚ₂`-algebra structure when no such structures are already
available. The results below apply to every compatible normed algebra structure.
They establish completeness, local compactness, the ultrametric property,
and compact openness of `𝒪` and `4𝒪` in the ambient field.
-/

namespace Char2Theta.Dyadic
noncomputable section

namespace SpectralTopology

variable (F : Type*) [Field F] [Algebra ℚ_[2] F] [FiniteDimensional ℚ_[2] F]

/-- The spectral norm gives a nontrivially normed field structure. -/
scoped instance (priority := 50) normedField : NontriviallyNormedField F :=
  spectralNorm.nontriviallyNormedField ℚ_[2] F

/-- The spectral norm extends the given dyadic norm. -/
scoped instance (priority := 50) normedAlgebra :
    @NormedAlgebra ℚ_[2] F _ (spectralNorm.seminormedRing ℚ_[2] F) :=
  spectralNorm.normedAlgebra ℚ_[2] F

end SpectralTopology

section CompatibleNorm
variable (F : Type*) [NormedField F] [NormedAlgebra ℚ_[2] F] [FiniteDimensional ℚ_[2] F]

instance extensionCompleteSpace : CompleteSpace F := FiniteDimensional.complete ℚ_[2] F

instance extensionProperSpace : ProperSpace F := FiniteDimensional.proper ℚ_[2] F

instance extensionIsUltrametricDist : IsUltrametricDist F :=
  IsUltrametricDist.of_normedAlgebra ℚ_[2]

/-- The original integral closure is precisely the closed unit ball. -/
theorem integers_eq_closedBall : (Integers F : Set F) = Metric.closedBall (0 : F) 1 := by
  ext x
  change IsIntegral ℤ_[2] x ↔ dist x 0 ≤ 1
  rw [dist_zero_right, NormedAlgebra.norm_eq_spectralNorm ℚ_[2]]
  exact isIntegral_iff_spectralNorm_le_one F x

theorem integers_isCompact : IsCompact (Integers F : Set F) := by
  rw [integers_eq_closedBall]
  exact isCompact_closedBall _ _

theorem integers_isOpen : IsOpen (Integers F : Set F) := by
  rw [integers_eq_closedBall]
  exact IsUltrametricDist.isOpen_closedBall _ one_ne_zero

instance integersCompactSpace : CompactSpace (Integers F) :=
  isCompact_iff_compactSpace.mp (integers_isCompact F)

omit [FiniteDimensional ℚ_[2] F] in
/-- Multiples of the integers are images of the integer set under scalar multiplication. -/
theorem multiples_eq_image (r : ℕ) :
    multiples (Integers F).toSubring r = (fun x : F => (r : F) * x) '' (Integers F : Set F) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, y.property, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

theorem multiples_isCompact (r : ℕ) : IsCompact (multiples (Integers F).toSubring r) := by
  rw [multiples_eq_image]
  exact (integers_isCompact F).image (continuous_const.mul continuous_id)

theorem multiples_isOpen (r : ℕ) (hr : r ≠ 0) : IsOpen (multiples (Integers F).toSubring r) := by
  rw [multiples_eq_image]
  exact (Homeomorph.mulLeft₀ (r : F) (by exact_mod_cast hr)).isOpenMap _ (integers_isOpen F)

/-- The subgroup `4𝒪` is compact and open in the local field topology. -/
theorem fourIntegers_isCompact_isOpen :
    IsCompact (multiples (Integers F).toSubring 4) ∧ IsOpen (multiples (Integers F).toSubring 4) :=
  ⟨multiples_isCompact F 4, multiples_isOpen F 4 (by decide)⟩

end CompatibleNorm
end
end Char2Theta.Dyadic

namespace Char2Theta.Dyadic
noncomputable section

/-- The annihilator of `𝒪` under `ψ(a·)`. This uses all of `a𝒪`, not just `a`. -/
def conductorSet {E : Type*} [Field E] (O : Subring E) (ψ : AddChar E ℂˣ) : Set E :=
  {a | ∀ x : O, ψ (a * x.val) = 1}

/-- Equation (1.2), as a condition on a chosen additive character. -/
def HasConductorFour {E : Type*} [Field E] (O : Subring E) (ψ : AddChar E ℂˣ) : Prop :=
  conductorSet O ψ = multiples O 4

theorem conductor_mem_iff {E : Type*} [Field E] (O : Subring E) (ψ : AddChar E ℂˣ)
    (hψ : HasConductorFour O ψ) (a : E) :
    (∀ x : O, ψ (a * x.val) = 1) ↔ ∃ x : O, a = 4 * x.val := by
  change a ∈ conductorSet O ψ ↔ _
  rw [hψ]
  simp [multiples, eq_comm]

theorem trivial_on_four {E : Type*} [Field E] (O : Subring E) (ψ : AddChar E ℂˣ)
    (hψ : HasConductorFour O ψ) (x : O) : ψ (4 * x.val) = 1 := by
  have h := ((conductor_mem_iff O ψ hψ (4 * x.val)).mpr ⟨x, rfl⟩) 1
  simpa using h

/-- The integral values have order dividing four. -/
theorem integral_value_pow_four {E : Type*} [Field E] (O : Subring E) (ψ : AddChar E ℂˣ)
    (hψ : HasConductorFour O ψ) (x : O) : ψ x.val ^ 4 = 1 := by
  rw [← ψ.map_nsmul_eq_pow]
  simpa [nsmul_eq_mul] using trivial_on_four O ψ hψ x

/-- Smoothness of an additive character means local constancy. -/
def SmoothCharacter {E : Type*} [AddCommGroup E] [TopologicalSpace E]
    (ψ : AddChar E ℂˣ) : Prop := IsLocallyConstant ψ

end
end Char2Theta.Dyadic

/-! ## The conductor condition and finite character obstruction (§1.3) -/

namespace Char2Theta

/-- An additive character on `(Z/4)^d` takes its values in `μ₄`. -/
theorem modFour_character_pow_four {d : ℕ} (χ : AddChar (Fin d → ZMod 4) ℂˣ)
    (x : Fin d → ZMod 4) : χ x ^ 4 = 1 := by
  rw [← χ.map_nsmul_eq_pow]
  have hx : (4 : ℕ) • x = 0 := by
    funext i
    change (4 : ℕ) • x i = 0
    exact (show ∀ y : ZMod 4, (4 : ℕ) • y = 0 by decide) (x i)
  rw [hx, χ.map_zero_eq_one]

/-- The obstruction stated below (1.2): for `d > 1`, no additive character
of `(Z/4)^d` is injective into `ℂˣ`. No choice of conductor is assumed. -/
theorem modFour_character_not_injective {d : ℕ} (hd : 1 < d)
    (χ : AddChar (Fin d → ZMod 4) ℂˣ) : ¬ Function.Injective χ := by
  intro hinj
  let f : (Fin d → ZMod 4) → rootsOfUnity 4 ℂ := fun x =>
    ⟨χ x, (mem_rootsOfUnity 4 (χ x)).mpr (modFour_character_pow_four χ x)⟩
  have hf : Function.Injective f := fun x y h => hinj (congrArg Subtype.val h)
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Complex.card_rootsOfUnity] at hcard
  have hpow : 4 ^ d ≤ 4 := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_fun] using hcard
  have hbound : 4 ^ 2 ≤ 4 ^ d := Nat.pow_le_pow_right (by decide) (by omega)
  omega

end Char2Theta

/-!
## The conductor condition and the ordinary character kernel (§1.3)

Characters trivial on `4𝒪` descend to `A`. The integral basis comparison
transfers the obstruction for `(ℤ/4ℤ)^d` to the actual dyadic quotient.
Consequently, when `d > 1`, the kernel of a field character cannot equal `4𝒪`.
For a character satisfying (1.2), its kernel strictly contains `4𝒪`, while
the multiplicative annihilator of its induced character on `A` is zero.
-/

namespace Char2Theta.Dyadic
noncomputable section

variable (F : Type*) [Field F] [Algebra ℚ_[2] F] [FiniteDimensional ℚ_[2] F]

omit [FiniteDimensional ℚ_[2] F] in
/-- Membership in the ideal `(4)` agrees with membership in `4𝒪` inside `F`. -/
theorem coe_mem_multiples_four_iff (x : Integers F) :
    (x : F) ∈ multiples (Integers F).toSubring 4 ↔
      x ∈ rationalIdeal (Integers F) 4 := by
  rw [multiples, Set.mem_range, rationalIdeal, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, Subtype.ext hy.symm⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg Subtype.val hy.symm⟩

/-- No character of the actual quotient `A` is injective if `d > 1`. -/
theorem A_character_not_injective (hd : 1 < degree F)
    (χ : AddChar (A (Integers F)) ℂˣ) : ¬ Function.Injective χ := by
  intro hχ
  exact modFour_character_not_injective hd
    (χ.compAddMonoidHom (AAddEquivModFour F).symm.toAddMonoidHom)
    (hχ.comp (AAddEquivModFour F).symm.injective)

/-- A nonzero element of the kernel exists in `A` when `d > 1`. -/
theorem A_character_exists_nonzero (hd : 1 < degree F)
    (χ : AddChar (A (Integers F)) ℂˣ) : ∃ a, a ≠ 0 ∧ χ a = 1 := by
  have h := A_character_not_injective F hd χ
  rw [AddChar.injective_iff] at h
  push Not at h
  obtain ⟨a, ha, hne⟩ := h
  exact ⟨a, hne, ha⟩

/-- Restriction of a field character to its ring of integers. -/
def integralCharacter (ψ : AddChar F ℂˣ) : AddChar (Integers F) ℂˣ :=
  ψ.compAddMonoidHom (Integers F).toSubring.subtype.toAddMonoidHom

/-- A character trivial on `4𝒪` descends to the actual ideal quotient `A`. -/
def characterModFour (ψ : AddChar F ℂˣ)
    (h4 : ∀ x : Integers F, ψ (4 * (x : F)) = 1) : AddChar (A (Integers F)) ℂˣ :=
  AddChar.toAddMonoidHomEquiv.symm
    (QuotientAddGroup.lift (rationalIdeal (Integers F) 4).toAddSubgroup
      (integralCharacter F ψ).toAddMonoidHom (by
        intro x hx
        obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
        change ψ ((4 : Integers F) * y : Integers F) = 1
        exact h4 y))

omit [FiniteDimensional ℚ_[2] F] in
@[simp]
theorem characterModFour_mk (ψ : AddChar F ℂˣ)
    (h4 : ∀ x : Integers F, ψ (4 * (x : F)) = 1) (x : Integers F) :
    characterModFour F ψ h4 (Ideal.Quotient.mk (rationalIdeal (Integers F) 4) x) =
      ψ (x : F) := rfl

/-- Triviality on `4𝒪` forces an additional integral kernel element when `d > 1`. -/
theorem exists_integral_kernel_outside_four (hd : 1 < degree F) (ψ : AddChar F ℂˣ)
    (h4 : ∀ x : Integers F, ψ (4 * (x : F)) = 1) :
    ∃ x : Integers F, ψ (x : F) = 1 ∧ (x : F) ∉ multiples (Integers F).toSubring 4 := by
  obtain ⟨a, hne, ha⟩ := A_character_exists_nonzero F hd (characterModFour F ψ h4)
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨x, ha, ?_⟩
  rw [coe_mem_multiples_four_iff]
  exact fun hx => hne (Ideal.Quotient.eq_zero_iff_mem.mpr hx)

/-- For `d > 1`, the ordinary kernel of any field character cannot be `4𝒪`.
The kernel is written as the set of arguments whose character value is `1`. -/
theorem character_kernel_ne_four (hd : 1 < degree F) (ψ : AddChar F ℂˣ) :
    {a : F | ψ a = 1} ≠ multiples (Integers F).toSubring 4 := by
  intro hker
  have h4 : ∀ x : Integers F, ψ (4 * (x : F)) = 1 := by
    intro x
    have hx : 4 * (x : F) ∈ multiples (Integers F).toSubring 4 := ⟨x, rfl⟩
    rwa [← hker] at hx
  obtain ⟨x, hx, hnot⟩ := exists_integral_kernel_outside_four F hd ψ h4
  exact hnot (by rw [← hker]; exact hx)

/-- The character of `A` induced by a field character with conductor (1.2). -/
def conductorCharacter (ψ : AddChar F ℂˣ)
    (hψ : HasConductorFour (Integers F).toSubring ψ) : AddChar (A (Integers F)) ℂˣ :=
  characterModFour F ψ (trivial_on_four (Integers F).toSubring ψ hψ)

omit [FiniteDimensional ℚ_[2] F] in
@[simp]
theorem conductorCharacter_mk (ψ : AddChar F ℂˣ)
    (hψ : HasConductorFour (Integers F).toSubring ψ) (x : Integers F) :
    conductorCharacter F ψ hψ (Ideal.Quotient.mk (rationalIdeal (Integers F) 4) x) =
      ψ (x : F) := rfl

omit [FiniteDimensional ℚ_[2] F] in
/-- Equation (1.2) makes the multiplicative annihilator in `A` zero. -/
theorem conductorCharacter_annihilator (ψ : AddChar F ℂˣ)
    (hψ : HasConductorFour (Integers F).toSubring ψ) (a : A (Integers F)) :
    (∀ b : A (Integers F), conductorCharacter F ψ hψ (a * b) = 1) ↔ a = 0 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  constructor
  · intro hx
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← coe_mem_multiples_four_iff, ← hψ]
    intro y
    change ψ ((x * y : Integers F) : F) = 1
    simpa only [← map_mul, conductorCharacter_mk] using
      hx (Ideal.Quotient.mk (rationalIdeal (Integers F) 4) y)
  · intro hx b
    rw [hx, zero_mul, AddChar.map_zero_eq_one]

omit [FiniteDimensional ℚ_[2] F] in
/-- The character induced by (1.2) is primitive in mathlib's sense. -/
theorem conductorCharacter_isPrimitive (ψ : AddChar F ℂˣ)
    (hψ : HasConductorFour (Integers F).toSubring ψ) :
    (conductorCharacter F ψ hψ).IsPrimitive := by
  intro a ha hshift
  apply ha
  apply (conductorCharacter_annihilator F ψ hψ a).mp
  intro b
  exact congrArg (fun χ : AddChar (A (Integers F)) ℂˣ => χ b) hshift

/-- For a character trivial on `4𝒪`, condition (1.2) is equivalent to
primitivity of its induced character on `A`. -/
theorem hasConductorFour_iff_isPrimitive (ψ : AddChar F ℂˣ)
    (h4 : ∀ x : Integers F, ψ (4 * (x : F)) = 1) :
    HasConductorFour (Integers F).toSubring ψ ↔
      (characterModFour F ψ h4).IsPrimitive := by
  constructor
  · intro hψ
    exact conductorCharacter_isPrimitive F ψ hψ
  · intro hprim
    apply Set.Subset.antisymm
    · intro a ha
      rcases ValuationRing.isInteger_or_isInteger (Integers F) a with ⟨x, hx⟩ | ⟨x, hx⟩
      · change (x : F) = a at hx
        subst a
        apply (coe_mem_multiples_four_iff F x).mpr
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        by_contra hne
        apply hprim hne
        apply AddChar.ext
        intro b
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
        rw [AddChar.mulShift_apply, AddChar.one_apply, ← map_mul, characterModFour_mk]
        exact ha y
      · change (x : F) = a⁻¹ at hx
        by_cases ha0 : a = 0
        · subst a
          exact ⟨0, by simp⟩
        have htriv : ∀ y : Integers F, ψ (y : F) = 1 := by
          intro y
          have h := ha (x * y)
          change ψ (a * ((x : F) * (y : F))) = 1 at h
          simpa only [hx, ← mul_assoc, mul_inv_cancel₀ ha0, one_mul] using h
        exfalso
        apply hprim (a := 1) one_ne_zero
        apply AddChar.ext
        intro b
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
        simpa only [AddChar.mulShift_apply, AddChar.one_apply, one_mul,
          characterModFour_mk] using htriv y
    · rintro a ⟨x, rfl⟩ y
      change ψ ((4 : F) * (x : F) * (y : F)) = 1
      rw [mul_assoc]
      exact h4 (x * y)

/-- Under (1.2), `4𝒪` is strictly smaller than the ordinary kernel if `d > 1`. -/
theorem conductor_four_strictSubset_kernel (hd : 1 < degree F) (ψ : AddChar F ℂˣ)
    (hψ : HasConductorFour (Integers F).toSubring ψ) :
    multiples (Integers F).toSubring 4 ⊂ {a : F | ψ a = 1} := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨?_, (character_kernel_ne_four F hd ψ).symm⟩
  rintro a ⟨x, rfl⟩
  exact trivial_on_four (Integers F).toSubring ψ hψ x

end
end Char2Theta.Dyadic

/-!
## Existence of a character with conductor four (§1.3)

A character of `A` which detects `ϖ^(2e-1)` is primitive: every nonzero
principal ideal of `A` contains this element. Finite abelian duality supplies
such a character. Its pullback to `𝒪` extends to `F` by divisibility of `ℂˣ`.
The conductor comparison from `DyadicCharacter` then gives equation (1.2).
-/

namespace Char2Theta.Dyadic
noncomputable section

variable (F : Type*) [Field F] [Algebra ℚ_[2] F] [FiniteDimensional ℚ_[2] F]

/-- The valuation criterion for membership in `(4)`. -/
theorem mem_four_iff_addVal (x : Integers F) :
    x ∈ rationalIdeal (Integers F) 4 ↔
      (2 * ramificationIndex (Integers F) : ℕ) ≤ IsDiscreteValuationRing.addVal (Integers F) x := by
  obtain ⟨π⟩ := uniformizerNonempty F
  rw [rationalIdeal_four, π.property.maximalIdeal_eq, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, ← IsDiscreteValuationRing.addVal_le_iff_dvd,
    π.property.addVal_pow]

/-- A generator of the smallest nonzero ideal in `A`. -/
def socleGenerator (π : Uniformizer (Integers F)) : A (Integers F) :=
  Ideal.Quotient.mk (rationalIdeal (Integers F) 4)
    (π.val ^ (2 * ramificationIndex (Integers F) - 1))

theorem socleGenerator_ne_zero (π : Uniformizer (Integers F)) : socleGenerator F π ≠ 0 := by
  intro h
  have hv := (mem_four_iff_addVal F _).mp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  rw [π.property.addVal_pow] at hv
  have hn : 2 * ramificationIndex (Integers F) ≤ 2 * ramificationIndex (Integers F) - 1 :=
    by exact_mod_cast hv
  have he := ramificationIndex_pos F
  omega

/-- Every nonzero element of `A` has a multiple equal to the socle generator. -/
theorem exists_mul_eq_socleGenerator (π : Uniformizer (Integers F))
    (a : A (Integers F)) (ha : a ≠ 0) : ∃ b, a * b = socleGenerator F π := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hx : x ≠ 0 := by intro hx; apply ha; simp [hx]
  obtain ⟨n, u, hxu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx π.property
  have hn : n < 2 * ramificationIndex (Integers F) := by
    by_contra h
    apply ha
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [mem_four_iff_addVal, hxu, IsDiscreteValuationRing.addVal_def' u π.property]
    exact_mod_cast Nat.le_of_not_gt h
  have hd : x ∣ π.val ^ (2 * ramificationIndex (Integers F) - 1) := by
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, hxu,
      IsDiscreteValuationRing.addVal_def' u π.property, π.property.addVal_pow]
    exact_mod_cast (show n ≤ 2 * ramificationIndex (Integers F) - 1 by omega)
  obtain ⟨y, hy⟩ := hd
  refine ⟨Ideal.Quotient.mk _ y, ?_⟩
  rw [← map_mul, ← hy]
  rfl

/-- Finite abelian duality supplies a primitive complex-unit-valued character of `A`. -/
theorem exists_primitive_A_character : ∃ χ : AddChar (A (Integers F)) ℂˣ, χ.IsPrimitive := by
  obtain ⟨π⟩ := uniformizerNonempty F
  obtain ⟨χ, hχ⟩ := AddChar.exists_apply_ne_zero.mpr (socleGenerator_ne_zero F π)
  let χu : AddChar (A (Integers F)) ℂˣ :=
    { toFun := fun a => (χ.val_isUnit a).unit
      map_zero_eq_one' := Units.ext (by simp)
      map_add_eq_mul' := fun a b => Units.ext (by simp [χ.map_add_eq_mul]) }
  refine ⟨χu, ?_⟩
  intro a ha hshift
  obtain ⟨b, hb⟩ := exists_mul_eq_socleGenerator F π a ha
  have h := congrArg (fun φ : AddChar (A (Integers F)) ℂˣ => (φ b : ℂ)) hshift
  change χ (a * b) = 1 at h
  exact hχ (hb ▸ h)

/-- A chosen primitive character on the finite quotient `A`. -/
def primitiveACharacter : AddChar (A (Integers F)) ℂˣ :=
  (exists_primitive_A_character F).choose

theorem primitiveACharacter_isPrimitive : (primitiveACharacter F).IsPrimitive :=
  (exists_primitive_A_character F).choose_spec

/-- A chosen primitive quotient character extends to the whole field. -/
theorem exists_extension_primitiveACharacter :
    ∃ ψ : AddChar F ℂˣ, ∀ x : Integers F,
      ψ (x : F) = primitiveACharacter F (Ideal.Quotient.mk (rationalIdeal (Integers F) 4) x) := by
  let χ := (primitiveACharacter F).compAddMonoidHom
    (Ideal.Quotient.mk (rationalIdeal (Integers F) 4)).toAddMonoidHom
  let i : Integers F →+ F := (Integers F).toSubring.subtype.toAddMonoidHom
  obtain ⟨ψ, hψ⟩ := extend_unit_character i.toMultiplicative
    (show Function.Injective i.toMultiplicative from Subtype.val_injective) χ.toMonoidHom
  refine ⟨AddChar.toMonoidHomEquiv.symm ψ, fun x => ?_⟩
  exact DFunLike.congr_fun hψ (Multiplicative.ofAdd x)

/-- A field character whose conductor is proved below to be `4𝒪`. -/
def conductorFourCharacter : AddChar F ℂˣ := (exists_extension_primitiveACharacter F).choose

@[simp]
theorem conductorFourCharacter_coe (x : Integers F) :
    conductorFourCharacter F (x : F) =
      primitiveACharacter F (Ideal.Quotient.mk (rationalIdeal (Integers F) 4) x) :=
  (exists_extension_primitiveACharacter F).choose_spec x

theorem conductorFourCharacter_trivial_on_four (x : Integers F) :
    conductorFourCharacter F (4 * (x : F)) = 1 := by
  change conductorFourCharacter F ((4 * x : Integers F) : F) = 1
  rw [conductorFourCharacter_coe]
  have hz : Ideal.Quotient.mk (rationalIdeal (Integers F) 4) (4 * x) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton.mpr ⟨x, rfl⟩
  rw [hz, AddChar.map_zero_eq_one]

/-- The constructed field character satisfies exactly equation (1.2). -/
theorem conductorFourCharacter_hasConductorFour :
    HasConductorFour (Integers F).toSubring (conductorFourCharacter F) := by
  apply (hasConductorFour_iff_isPrimitive F _ (conductorFourCharacter_trivial_on_four F)).mpr
  have he : characterModFour F (conductorFourCharacter F)
      (conductorFourCharacter_trivial_on_four F) = primitiveACharacter F := by
    apply AddChar.ext
    intro a
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [characterModFour_mk, conductorFourCharacter_coe]
  rw [he]
  exact primitiveACharacter_isPrimitive F

end
end Char2Theta.Dyadic

/-!
## A smooth additive character satisfying (1.2)

The algebraically constructed character is trivial on the compact open
subgroup `4𝒪`. It is therefore locally constant on every additive coset.
This proves existence for the actual local field topology, using the original
`SmoothCharacter` and `HasConductorFour` definitions.
-/

namespace Char2Theta.Dyadic
noncomputable section

section CompatibleNorm
variable (F : Type*) [NormedField F] [NormedAlgebra ℚ_[2] F] [FiniteDimensional ℚ_[2] F]

/-- Triviality on the open subgroup `4𝒪` implies local constancy. -/
theorem smoothCharacter_of_trivial_on_four (ψ : AddChar F ℂˣ)
    (h4 : ∀ x : Integers F, ψ (4 * (x : F)) = 1) : SmoothCharacter ψ := by
  apply (IsLocallyConstant.iff_exists_open ψ).mpr
  intro a
  refine ⟨(fun b : F => b - a) ⁻¹' multiples (Integers F).toSubring 4,
    (multiples_isOpen F 4 (by decide)).preimage (continuous_id.sub continuous_const), ?_, ?_⟩
  · exact ⟨0, by simp⟩
  · rintro b ⟨x, hx⟩
    change (4 : F) * (x : F) = b - a at hx
    have h : ψ (b - a) = 1 := by rw [← hx]; exact h4 x
    rw [ψ.map_sub_eq_div] at h
    exact div_eq_one.mp h

/-- Every character satisfying (1.2) is smooth in the dyadic local field topology. -/
theorem smoothCharacter_of_hasConductorFour (ψ : AddChar F ℂˣ)
    (hψ : HasConductorFour (Integers F).toSubring ψ) : SmoothCharacter ψ :=
  smoothCharacter_of_trivial_on_four F ψ (trivial_on_four (Integers F).toSubring ψ hψ)

theorem conductorFourCharacter_smooth : SmoothCharacter (conductorFourCharacter F) :=
  smoothCharacter_of_trivial_on_four F _ (conductorFourCharacter_trivial_on_four F)

theorem conductorFourCharacter_continuous : Continuous (conductorFourCharacter F) :=
  (conductorFourCharacter_smooth F).continuous

/-- Existence of the smooth additive character required in §1.3, equation (1.2). -/
theorem exists_smooth_character_conductor_four :
    ∃ ψ : AddChar F ℂˣ, SmoothCharacter ψ ∧ HasConductorFour (Integers F).toSubring ψ :=
  ⟨conductorFourCharacter F, conductorFourCharacter_smooth F,
    conductorFourCharacter_hasConductorFour F⟩

end CompatibleNorm

section SpectralNorm
open scoped SpectralTopology
variable (F : Type*) [Field F] [Algebra ℚ_[2] F] [FiniteDimensional ℚ_[2] F]

/-- No topology need be supplied: the spectral topology gives a smooth character
with conductor `4𝒪` from the finite extension hypotheses alone. -/
theorem exists_smooth_character_conductor_four_spectral :
    ∃ ψ : AddChar F ℂˣ, SmoothCharacter ψ ∧ HasConductorFour (Integers F).toSubring ψ :=
  exists_smooth_character_conductor_four F

end SpectralNorm
end
end Char2Theta.Dyadic
