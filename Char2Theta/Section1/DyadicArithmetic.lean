import Char2Theta.Section1.FiniteBasics
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Perfectoid.FontaineTheta

/-!
# Dyadic 整数环、剩余域与商环（§1.3）

本文件从有限扩张 `F/ℚ₂` 出发，定义整数环、`R=𝒪/(2)`、`A=𝒪/(4)`、
均匀化元与分歧指数，建立 DVR、有限剩余域及相关实例，证明 `d=ef`、
`|R|=q^e`、`|A|=q^(2e)`。随后比较非分歧／分歧商环，构造长度二 Witt 环
同构与模四加法群同构。

主要入口：`dyadic_numerical_identities`、`unramifiedREquivResidue`、
`unramifiedAEquivWittTwo`、`ramified_R_exists_nonzero_nilpotent`、`AAddEquivModFour`。
商环始终使用有理整数理想 `(2)`、`(4)`；模四加法同构不声称乘法相容。
拓扑与导子在 `DyadicCharacter`，格与表示约定在 `DyadicLatticeModel`。
-/

set_option autoImplicit false

namespace Char2Theta.Dyadic
noncomputable section

variable (F : Type*) [Field F] [Algebra ℚ_[2] F]

/-- The canonical `ℤ₂`-algebra structure inherited through `ℚ₂`. -/
instance (priority := 50) integersAlgebra : Algebra ℤ_[2] F :=
  ((algebraMap ℚ_[2] F).comp (algebraMap ℤ_[2] ℚ_[2])).toAlgebra

/-- The ring of integers of the algebraic extension, via mathlib's integral closure. -/
abbrev Integers := integralClosure ℤ_[2] F

/-- The degree `d`; finiteness is an explicit hypothesis of dyadic-field results. -/
abbrev degree [FiniteDimensional ℚ_[2] F] : ℕ := Module.finrank ℚ_[2] F

/-- Rational integers generate the ideals denoted `r𝒪` in the notes. -/
def rationalIdeal (O : Type*) [CommRing O] (r : ℕ) : Ideal O := Ideal.span {(r : O)}

abbrev R (O : Type*) [CommRing O] := O ⧸ rationalIdeal O 2
abbrev A (O : Type*) [CommRing O] := O ⧸ rationalIdeal O 4

/-- The residue field is the quotient by the maximal ideal, not by `2𝒪`. -/
abbrev residueField (O : Type*) [CommRing O] [IsLocalRing O] := IsLocalRing.ResidueField O

/-- A chosen uniformizer in a DVR. -/
abbrev Uniformizer (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :=
  {π : O // Irreducible π}

/-- The absolute ramification index, as a natural number. The DVR valuation has
value `⊤` at zero; its finiteness at `2` needs characteristic zero. -/
def ramificationIndex (O : Type*) [CommRing O] [IsDomain O] [CharZero O]
    [IsDiscreteValuationRing O] : ℕ := (IsDiscreteValuationRing.addVal O 2).toNat

theorem valuation_uniformizer (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (π : Uniformizer O) :
    IsDiscreteValuationRing.addVal O π.val = 1 :=
  IsDiscreteValuationRing.addVal_uniformizer π.property

/-- The set `r𝒪` as a subset of the ambient field. -/
def multiples {E : Type*} [Field E] (O : Subring E) (r : ℕ) : Set E :=
  Set.range (fun x : O => (r : E) * x.val)

end
end Char2Theta.Dyadic

/-!
## Integers of a finite dyadic extension (§1.3)

The existing `Integers F = integralClosure ℤ_[2] F` is finite free of rank `d`
over `ℤ_[2]` and is a DVR with fraction field `F`. The only field hypotheses
are `[Field F] [Algebra ℚ_[2] F] [FiniteDimensional ℚ_[2] F]`.

Mathlib supplies finiteness, freeness and the Dedekind property. To obtain
locality, we identify the integral elements using minimal polynomials and the
spectral norm, then compare norms to prove the valuation-ring divisibility
condition. The normed-field structure is used locally in that proof.
-/

namespace Char2Theta.Dyadic
noncomputable section

variable (F : Type*) [Field F] [Algebra ℚ_[2] F]

instance integersScalarTower : IsScalarTower ℤ_[2] ℚ_[2] F :=
  IsScalarTower.of_algebraMap_eq' rfl

instance integersTorsionFree : Module.IsTorsionFree ℤ_[2] F :=
  .trans_faithfulSMul ℤ_[2] ℚ_[2] F

instance (priority := 50) extensionCharZero : CharZero F :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[2] F).injective

variable [FiniteDimensional ℚ_[2] F]

instance integersFinite : Module.Finite ℤ_[2] (Integers F) :=
  IsIntegralClosure.finite ℤ_[2] ℚ_[2] F (Integers F)

instance integersFree : Module.Free ℤ_[2] (Integers F) :=
  IsIntegralClosure.module_free ℤ_[2] ℚ_[2] F (Integers F)

instance integersDedekind : IsDedekindDomain (Integers F) :=
  integralClosure.isDedekindDomain ℤ_[2] ℚ_[2] F

instance integersFractionRing : IsFractionRing (Integers F) F :=
  IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[2] ℚ_[2] F (Integers F)

/-- The integral closure has rank `d` over `ℤ₂`. -/
theorem integers_rank : Module.finrank ℤ_[2] (Integers F) = degree F :=
  IsIntegralClosure.rank ℤ_[2] ℚ_[2] F (Integers F)

/-- Integrality is equivalent to lying in the closed unit ball of the spectral norm. -/
theorem isIntegral_iff_spectralNorm_le_one (x : F) :
    IsIntegral ℤ_[2] x ↔ spectralNorm ℚ_[2] F x ≤ 1 := by
  rw [spectralNorm, spectralValue_le_one_iff
    (minpoly.monic (Algebra.IsIntegral.isIntegral (R := ℚ_[2]) x))]
  constructor
  · intro hx n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[2] hx,
      Polynomial.coeff_map]
    exact ((minpoly ℤ_[2] x).coeff n).property
  · intro hx
    have hl : minpoly ℚ_[2] x ∈ Polynomial.lifts (algebraMap ℤ_[2] ℚ_[2]) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, hx n⟩, rfl⟩
    obtain ⟨P, hP⟩ := (Polynomial.lifts_iff_set_range _).mp hl
    refine ⟨P, ?_, ?_⟩
    · exact ((IsFractionRing.injective ℤ_[2] ℚ_[2]).monic_map_iff).mpr
        (hP ▸ minpoly.monic (Algebra.IsIntegral.isIntegral (R := ℚ_[2]) x))
    · change Polynomial.aeval x P = 0
      rw [← Polynomial.aeval_map_algebraMap ℚ_[2], hP, minpoly.aeval]

instance integersValuationRing : ValuationRing (Integers F) where
  cond' a b := by
    letI := spectralNorm.normedField ℚ_[2] F
    have hint (x : F) : IsIntegral ℤ_[2] x ↔ ‖x‖ ≤ 1 :=
      isIntegral_iff_spectralNorm_le_one F x
    by_cases ha : a = 0
    · exact ⟨0, Or.inr (by simp [ha])⟩
    by_cases hb : b = 0
    · exact ⟨0, Or.inl (by simp [hb])⟩
    have ha' : (a : F) ≠ 0 := Subtype.coe_ne_coe.mpr ha
    have hb' : (b : F) ≠ 0 := Subtype.coe_ne_coe.mpr hb
    rcases le_total ‖(a : F)‖ ‖(b : F)‖ with h | h
    · refine ⟨⟨(a : F) / b, (hint _).mpr ?_⟩, Or.inr ?_⟩
      · rw [norm_div, div_le_one (norm_pos_iff.mpr hb')]; exact h
      · apply Subtype.ext; exact mul_div_cancel₀ _ hb'
    · refine ⟨⟨(b : F) / a, (hint _).mpr ?_⟩, Or.inl ?_⟩
      · rw [norm_div, div_le_one (norm_pos_iff.mpr ha')]; exact h
      · apply Subtype.ext; exact mul_div_cancel₀ _ ha'

instance integersDVR : IsDiscreteValuationRing (Integers F) := by
  have hn : ¬IsField (Integers F) := fun h =>
    IsDiscreteValuationRing.not_isField ℤ_[2]
      (isField_of_isIntegral_of_isField
        (FaithfulSMul.algebraMap_injective ℤ_[2] (Integers F)) h)
  exact ((IsDiscreteValuationRing.TFAE (Integers F) hn).out 2 0).mp
    (show IsDedekindDomain (Integers F) from inferInstance)

end
end Char2Theta.Dyadic

/-!
## Residue fields and dyadic cardinalities (§1.3)

For the actual integers of a finite extension `F/ℚ₂`, construct `k`, `f` and
`q`, and prove `q = 2^f`, `d = ef`, `|R| = q^e` and `|A| = q^(2e)`.
The exponent `e` remains the normalized valuation of `2` defined above.

The cardinalities follow from mathlib's formula for quotients by prime ideal
powers. The degree formula follows by comparing `|R| = q^e` with `|R| = 2^d`,
using the rank of the integral closure and the rank of its reduction modulo `2`.
-/

namespace Char2Theta.Dyadic
noncomputable section

variable (F : Type*) [Field F] [Algebra ℚ_[2] F] [FiniteDimensional ℚ_[2] F]

/-- The residue field `k = 𝒪/𝔪` of the dyadic field. -/
abbrev Residue := residueField (Integers F)

instance residueFinite : Finite (Residue F) := by
  haveI : Finite (IsLocalRing.ResidueField ℤ_[2]) :=
    Finite.of_equiv (ZMod 2) (PadicInt.residueField (p := 2)).symm.toEquiv
  exact IsLocalRing.ResidueField.finite_of_finite (R := ℤ_[2]) inferInstance

instance residueCharTwo : CharP (Residue F) 2 := by
  let g : ZMod 2 →+* Residue F :=
    (algebraMap (IsLocalRing.ResidueField ℤ_[2]) (Residue F)).comp
      (PadicInt.residueField (p := 2)).symm.toRingHom
  exact charP_of_injective_ringHom g.injective 2

instance residueAlgebra : Algebra F₂ (Residue F) :=
  (ZMod.castHom (by simp) (Residue F)).toAlgebra

instance residueFintype : Fintype (Residue F) := Fintype.ofFinite _

/-- The residue degree `f = [k : 𝔽₂]`. -/
abbrev residueDegree : ℕ := Module.finrank F₂ (Residue F)

/-- The residue cardinality `q = |k|`. -/
abbrev residueCard : ℕ := Nat.card (Residue F)

theorem residueCard_eq_two_pow : residueCard F = 2 ^ residueDegree F := by
  simpa using (Module.natCard_eq_pow_finrank (K := F₂) (V := Residue F))

theorem residueCard_pos : 0 < residueCard F := Nat.card_pos

theorem residueCard_gt_one : 1 < residueCard F := by
  simpa only [residueCard, Nat.card_eq_fintype_card] using
    (Fintype.one_lt_card : 1 < Fintype.card (Residue F))

instance uniformizerNonempty : Nonempty (Uniformizer (Integers F)) :=
  let ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Integers F)
  ⟨⟨π, hπ⟩⟩

/-- A principal ideal in a DVR is the power specified by the normalized valuation. -/
theorem span_singleton_eq_maximalIdeal_pow {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {x : O} (hx : x ≠ 0) :
    Ideal.span {x} = IsLocalRing.maximalIdeal O ^
      (IsDiscreteValuationRing.addVal O x).toNat := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  rw [IsDiscreteValuationRing.addVal_def' u hπ, ENat.toNat_coe,
    hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
    Ideal.span_singleton_mul_left_unit u.isUnit]

/-- The ideal `(2)` is `𝔪^e`, with the original definition `e = v_F(2)`. -/
theorem rationalIdeal_two : rationalIdeal (Integers F) 2 =
    IsLocalRing.maximalIdeal (Integers F) ^ ramificationIndex (Integers F) :=
  span_singleton_eq_maximalIdeal_pow (by norm_num)

/-- The ideal `(4)` is `𝔪^(2e)`, rather than `𝔪²` in general. -/
theorem rationalIdeal_four : rationalIdeal (Integers F) 4 =
    IsLocalRing.maximalIdeal (Integers F) ^ (2 * ramificationIndex (Integers F)) := by
  have h : rationalIdeal (Integers F) 4 = rationalIdeal (Integers F) 2 ^ 2 := by
    simp only [rationalIdeal, Ideal.span_singleton_pow]
    norm_num
  rw [h, rationalIdeal_two, ← pow_mul, Nat.mul_comm]

theorem card_R : Nat.card (R (Integers F)) =
    residueCard F ^ ramificationIndex (Integers F) := by
  change Submodule.cardQuot (rationalIdeal (Integers F) 2) = _
  rw [rationalIdeal_two, cardQuot_pow_of_prime
    (IsDiscreteValuationRing.not_a_field (Integers F))]
  rfl

theorem card_A : Nat.card (A (Integers F)) =
    residueCard F ^ (2 * ramificationIndex (Integers F)) := by
  change Submodule.cardQuot (rationalIdeal (Integers F) 4) = _
  rw [rationalIdeal_four, cardQuot_pow_of_prime
    (IsDiscreteValuationRing.not_a_field (Integers F))]
  rfl

instance RFinite : Finite (R (Integers F)) :=
  Nat.finite_of_card_ne_zero (by rw [card_R]; exact pow_ne_zero _ (residueCard_pos F).ne')

instance AFinite : Finite (A (Integers F)) :=
  Nat.finite_of_card_ne_zero (by rw [card_A]; exact pow_ne_zero _ (residueCard_pos F).ne')

instance RFintype : Fintype (R (Integers F)) := Fintype.ofFinite _
instance AFintype : Fintype (A (Integers F)) := Fintype.ofFinite _

omit [FiniteDimensional ℚ_[2] F] in
/-- Base change of the maximal ideal `(2)` of `ℤ₂` gives `(2)` in `𝒪`. -/
theorem map_base_maximalIdeal :
    (IsLocalRing.maximalIdeal ℤ_[2]).map (algebraMap ℤ_[2] (Integers F)) =
      rationalIdeal (Integers F) 2 := by
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton]
  rw [map_natCast]
  rfl

/-- Reduction modulo `2` also computes the extension degree: `|𝒪/2𝒪| = 2^d`. -/
theorem card_R_eq_two_pow_degree : Nat.card (R (Integers F)) = 2 ^ degree F := by
  let p := IsLocalRing.maximalIdeal ℤ_[2]
  let Q := Integers F ⧸ p.map (algebraMap ℤ_[2] (Integers F))
  letI : p.IsMaximal := inferInstanceAs (IsLocalRing.maximalIdeal ℤ_[2]).IsMaximal
  letI : Field (ℤ_[2] ⧸ p) := Ideal.Quotient.field p
  letI : Module.Finite (ℤ_[2] ⧸ p) Q :=
    Module.Finite.of_restrictScalars_finite ℤ_[2] _ _
  have hcard : Nat.card (ℤ_[2] ⧸ p) = 2 := by
    change Nat.card (IsLocalRing.ResidueField ℤ_[2]) = 2
    rw [Nat.card_congr (PadicInt.residueField (p := 2)).toEquiv]
    simp
  calc
    Nat.card (R (Integers F)) = Nat.card Q :=
      (Nat.card_congr (Ideal.quotEquivOfEq (map_base_maximalIdeal F)).toEquiv).symm
    _ = Nat.card (ℤ_[2] ⧸ p) ^ Module.finrank (ℤ_[2] ⧸ p) Q :=
      Module.natCard_eq_pow_finrank (K := ℤ_[2] ⧸ p) (V := Q)
    _ = 2 ^ degree F := by
      rw [hcard, IsLocalRing.finrank_quotient_map, integers_rank]

/-- The degree formula `d = ef` of §1.3. -/
theorem degree_eq_ramificationIndex_mul_residueDegree :
    degree F = ramificationIndex (Integers F) * residueDegree F := by
  apply Nat.pow_right_injective (a := 2) (by decide)
  dsimp only
  rw [← card_R_eq_two_pow_degree, card_R, residueCard_eq_two_pow, ← pow_mul,
    Nat.mul_comm]

theorem degree_pos : 0 < degree F := Module.finrank_pos

theorem residueDegree_pos : 0 < residueDegree F := Module.finrank_pos

theorem ramificationIndex_pos : 0 < ramificationIndex (Integers F) := by
  have h := degree_pos F
  rw [degree_eq_ramificationIndex_mul_residueDegree] at h
  exact Nat.pos_of_mul_pos_right h

/-- The normalized valuation of `2` is finite and equals `e`. -/
theorem valuation_two : IsDiscreteValuationRing.addVal (Integers F) 2 =
    (ramificationIndex (Integers F) : ENat) := by
  exact (ENat.coe_toNat (by simp [IsDiscreteValuationRing.addVal_eq_top_iff])).symm

/-- The residue-field presentation `k = 𝒪/ϖ𝒪` for any uniformizer. -/
def residueEquivQuotientUniformizer (π : Uniformizer (Integers F)) :
    Residue F ≃+* Integers F ⧸ Ideal.span {π.val} :=
  Ideal.quotEquivOfEq π.property.maximalIdeal_eq

theorem two_not_isUnit : ¬IsUnit (2 : Integers F) := by
  intro h
  exact (PadicInt.irreducible_p (p := 2)).not_isUnit
    (isUnit_of_map_unit (algebraMap ℤ_[2] (Integers F)) (2 : ℤ_[2]) (by rw [map_ofNat]; exact h))

instance RCharTwo : CharP (R (Integers F)) 2 :=
  CharP.quotient (Integers F) 2 (two_not_isUnit F)

instance RNontrivial : Nontrivial (R (Integers F)) :=
  CharP.nontrivial_of_char_ne_one (by decide : 2 ≠ 1)

instance ANontrivial : Nontrivial (A (Integers F)) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  change Ideal.span {(4 : Integers F)} ≠ ⊤
  intro ht
  have h := Ideal.span_singleton_eq_top.mp ht
  exact two_not_isUnit F (isUnit_of_mul_isUnit_left
    (show IsUnit ((2 : Integers F) * 2) by norm_num at h ⊢; exact h))

/-- In particular, reduction modulo `4` does not turn `2` into zero. -/
theorem two_ne_zero_in_A : (2 : A (Integers F)) ≠ 0 := by
  intro h
  have hm : (2 : Integers F) ∈ rationalIdeal (Integers F) 4 :=
    Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_ofNat]; exact h)
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hm
  apply two_not_isUnit F
  apply isUnit_iff_dvd_one.mpr
  refine ⟨z, mul_left_cancel₀ (by norm_num : (2 : Integers F) ≠ 0) ?_⟩
  calc
    (2 : Integers F) * 1 = 2 := mul_one _
    _ = 4 * z := hz
    _ = 2 * (2 * z) := by ring

instance ACharFour : CharP (A (Integers F)) 4 := by
  have h4 : (4 : A (Integers F)) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton_self _
  have hd := ringChar.dvd h4
  have hne := CharP.ringChar_ne_one (R := A (Integers F))
  have hne2 : ringChar (A (Integers F)) ≠ 2 := by
    intro h
    exact two_ne_zero_in_A F (by simpa [h] using (ringChar.Nat.cast_ringChar (R := A (Integers F))))
  apply ringChar.of_eq
  have hcases : ringChar (A (Integers F)) = 1 ∨
      ringChar (A (Integers F)) = 2 ∨ ringChar (A (Integers F)) = 4 := by
    have hbound := Nat.le_of_dvd (by decide : 0 < 4) hd
    interval_cases hc : ringChar (A (Integers F)) <;> simp_all
  exact (hcases.resolve_left hne).resolve_left hne2

instance RLocalRing : IsLocalRing (R (Integers F)) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (rationalIdeal (Integers F) 2))
    Ideal.Quotient.mk_surjective

instance ALocalRing : IsLocalRing (A (Integers F)) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (rationalIdeal (Integers F) 4))
    Ideal.Quotient.mk_surjective

instance RAlgebra : Algebra F₂ (R (Integers F)) :=
  (ZMod.castHom (by simp) (R (Integers F))).toAlgebra

instance AAlgebra : Algebra (ZMod 4) (A (Integers F)) :=
  (ZMod.castHom (by simp) (A (Integers F))).toAlgebra

/-- The three numerical identities from the dyadic conventions, with no extra hypotheses. -/
theorem dyadic_numerical_identities :
    degree F = ramificationIndex (Integers F) * residueDegree F ∧
    Nat.card (R (Integers F)) = residueCard F ^ ramificationIndex (Integers F) ∧
    Nat.card (A (Integers F)) = residueCard F ^ (2 * ramificationIndex (Integers F)) :=
  ⟨degree_eq_ramificationIndex_mul_residueDegree F, card_R F, card_A F⟩

end
end Char2Theta.Dyadic

/-!
## Unramified and ramified quotients (§1.3)

The unramified case is expressed by `e = 1`, and the ramified case by `1 < e`.
The quotients retain the original rational ideals `(2)` and `(4)`.
-/

namespace Char2Theta.Dyadic
noncomputable section

variable (F : Type*) [Field F] [Algebra ℚ_[2] F] [FiniteDimensional ℚ_[2] F]

/-- In the unramified case, `(2)` is the maximal ideal. -/
theorem rationalIdeal_two_eq_maximalIdeal (he : ramificationIndex (Integers F) = 1) :
    rationalIdeal (Integers F) 2 = IsLocalRing.maximalIdeal (Integers F) := by
  rw [rationalIdeal_two, he, pow_one]

/-- The numerical condition `e = 1` agrees with mathlib's unramified algebra condition. -/
theorem formallyUnramified_iff_ramificationIndex_eq_one :
    Algebra.FormallyUnramified ℤ_[2] (Integers F) ↔ ramificationIndex (Integers F) = 1 := by
  haveI : Finite (IsLocalRing.ResidueField ℤ_[2]) :=
    Finite.of_equiv (ZMod 2) (PadicInt.residueField (p := 2)).symm.toEquiv
  rw [Algebra.FormallyUnramified.iff_map_maximalIdeal_eq]
  have hs : Algebra.IsSeparable (IsLocalRing.ResidueField ℤ_[2]) (Residue F) := inferInstance
  simp only [hs, true_and, map_base_maximalIdeal, rationalIdeal_two]
  constructor
  · intro h
    have hc := congrArg Submodule.cardQuot h
    rw [cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field (Integers F))] at hc
    apply Nat.pow_right_injective (Nat.succ_le_of_lt (residueCard_gt_one F))
    change residueCard F ^ ramificationIndex (Integers F) = residueCard F at hc
    simpa only [pow_one] using hc
  · intro h
    rw [h, pow_one]

/-- The canonical reduction isomorphism `R ≃ k` when `e = 1`. -/
def unramifiedREquivResidue (he : ramificationIndex (Integers F) = 1) :
    R (Integers F) ≃+* Residue F :=
  Ideal.quotEquivOfEq (rationalIdeal_two_eq_maximalIdeal F he)

@[simp]
theorem unramifiedREquivResidue_mk (he : ramificationIndex (Integers F) = 1)
    (x : Integers F) :
    unramifiedREquivResidue F he (Ideal.Quotient.mk _ x) = IsLocalRing.residue _ x := rfl

/-- A uniformizer gives a nonzero residue in `R` in the ramified case. -/
theorem uniformizer_ne_zero_in_R (he : 1 < ramificationIndex (Integers F))
    (π : Uniformizer (Integers F)) :
    Ideal.Quotient.mk (rationalIdeal (Integers F) 2) π.val ≠ 0 := by
  intro h
  have hd : (2 : Integers F) ∣ π.val :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hv := IsDiscreteValuationRing.addVal_le_iff_dvd.mpr hd
  rw [valuation_two, valuation_uniformizer] at hv
  exact (not_le_of_gt he) (by exact_mod_cast hv)

/-- The uniformizer class in `R` has zero `e`-th power. -/
theorem uniformizer_pow_eq_zero_in_R (π : Uniformizer (Integers F)) :
    (Ideal.Quotient.mk (rationalIdeal (Integers F) 2) π.val) ^
      ramificationIndex (Integers F) = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, rationalIdeal_two,
    π.property.maximalIdeal_eq, Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton_self _

/-- In the ramified case, `R` contains a nonzero nilpotent. -/
theorem ramified_R_exists_nonzero_nilpotent (he : 1 < ramificationIndex (Integers F)) :
    ∃ x : R (Integers F), x ≠ 0 ∧ IsNilpotent x := by
  obtain ⟨π⟩ := uniformizerNonempty F
  exact ⟨Ideal.Quotient.mk _ π.val, uniformizer_ne_zero_in_R F he π,
    ⟨ramificationIndex (Integers F), uniformizer_pow_eq_zero_in_R F π⟩⟩

/-- The quotient by the square of any uniformizer has `q²` elements. -/
theorem card_quotient_uniformizer_sq (π : Uniformizer (Integers F)) :
    Nat.card (Integers F ⧸ Ideal.span {π.val ^ 2}) = residueCard F ^ 2 := by
  change Submodule.cardQuot (Ideal.span {π.val ^ 2}) = _
  rw [← Ideal.span_singleton_pow, ← π.property.maximalIdeal_eq,
    cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field (Integers F))]
  rfl

/-- In the ramified case, `𝒪/ϖ²𝒪` is strictly smaller than `A`. -/
theorem card_quotient_uniformizer_sq_lt_card_A
    (he : 1 < ramificationIndex (Integers F)) (π : Uniformizer (Integers F)) :
    Nat.card (Integers F ⧸ Ideal.span {π.val ^ 2}) < Nat.card (A (Integers F)) := by
  rw [card_quotient_uniformizer_sq, card_A]
  exact Nat.pow_lt_pow_right (residueCard_gt_one F) (by omega)

/-- The ramified quotients are not isomorphic, even as sets. -/
theorem ramified_A_not_equiv_quotient_uniformizer_sq
    (he : 1 < ramificationIndex (Integers F)) (π : Uniformizer (Integers F)) :
    IsEmpty (A (Integers F) ≃ (Integers F ⧸ Ideal.span {π.val ^ 2})) := by
  refine ⟨fun e => ?_⟩
  exact (ne_of_lt (card_quotient_uniformizer_sq_lt_card_A F he π))
    (Nat.card_congr e).symm

/-- In particular, there is no ring isomorphism in the ramified case. -/
theorem ramified_A_not_ringEquiv_quotient_uniformizer_sq
    (he : 1 < ramificationIndex (Integers F)) (π : Uniformizer (Integers F)) :
    IsEmpty (A (Integers F) ≃+* (Integers F ⧸ Ideal.span {π.val ^ 2})) :=
  ⟨fun e => (ramified_A_not_equiv_quotient_uniformizer_sq F he π).false e.toEquiv⟩

end
end Char2Theta.Dyadic

/-!
## The unramified quotient as length-two Witt vectors (§1.3)

The Witt ring is mathlib's `TruncatedWittVector 2 2 k`. The comparison uses
mathlib's ghost-component map modulo powers of `(2)`, precomposed with inverse
Frobenius on the perfect residue field. This normalization preserves reduction
to `k`.
-/

namespace Char2Theta.Dyadic
noncomputable section

section Ghost
variable (O : Type*) [CommRing O]

/-- Squaring the rational ideal `(2)` gives `(4)`. -/
theorem rationalIdeal_two_sq : rationalIdeal O 2 ^ 2 = rationalIdeal O 4 := by
  simp only [rationalIdeal, Ideal.span_singleton_pow]
  norm_num

/-- The second ghost component, descended modulo `(4)` using mathlib. -/
def ghostToModFour : WittVector 2 (R O) →+* A O :=
  (Ideal.quotEquivOfEq (rationalIdeal_two_sq O)).toRingHom.comp
    (WittVector.ghostComponentModPPow (R := O) (p := 2) 1)

@[simp]
theorem ghostToModFour_map_mk (x : WittVector 2 O) :
    ghostToModFour O (WittVector.map (Ideal.Quotient.mk (rationalIdeal O 2)) x) =
      Ideal.Quotient.mk (rationalIdeal O 4) (WittVector.ghostComponent 1 x) := by
  exact congrArg (Ideal.quotEquivOfEq (rationalIdeal_two_sq O))
    (WittVector.ghostComponentModPPow_map_mk (p := 2) 1 x)

/-- The explicit polynomial underlying the second dyadic ghost component. -/
theorem ghostComponent_one (x : WittVector 2 O) :
    WittVector.ghostComponent 1 x = x.coeff 0 ^ 2 + 2 * x.coeff 1 := by
  rw [WittVector.ghostComponent_apply, wittPolynomial_one]
  simp [add_comm]

/-- The second ghost component modulo `(4)` depends only on two coefficients. -/
theorem ker_truncate_le_ker_ghostToModFour :
    RingHom.ker (WittVector.truncate (p := 2) (R := R O) 2) ≤
      RingHom.ker (ghostToModFour O) := by
  intro x hx
  obtain ⟨y, rfl⟩ := WittVector.map_surjective
    (Ideal.Quotient.mk (rationalIdeal O 2)) Ideal.Quotient.mk_surjective x
  have hz := (WittVector.mem_ker_truncate 2 _).mp hx
  change ghostToModFour O (WittVector.map _ y) = 0
  rw [ghostToModFour_map_mk, Ideal.Quotient.eq_zero_iff_mem]
  apply Ideal.mem_span_singleton.mpr
  have hg := WittVector.pow_dvd_ghostComponent_of_dvd_coeff (p := 2) (n := 1)
    (x := y) (fun i hi => ?_)
  · convert hg using 1; norm_num
  · exact Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp (hz i (by omega)))

end Ghost

section Unramified
variable (F : Type*) [Field F] [Algebra ℚ_[2] F] [FiniteDimensional ℚ_[2] F]

/-- Inverse Frobenius, transported from `k` to `R`, normalizes the ghost map. -/
def inverseFrobeniusToR (he : ramificationIndex (Integers F) = 1) :
    Residue F ≃+* R (Integers F) :=
  (frobeniusEquiv (Residue F) 2).symm.trans (unramifiedREquivResidue F he).symm

/-- The normalized second ghost component on full Witt vectors over `k`. -/
def unramifiedWittToA (he : ramificationIndex (Integers F) = 1) :
    WittVector 2 (Residue F) →+* A (Integers F) :=
  (ghostToModFour (Integers F)).comp
    (WittVector.map (inverseFrobeniusToR F he).toRingHom)

/-- Only the first two Witt coordinates enter the comparison. -/
theorem ker_truncate_le_ker_unramifiedWittToA
    (he : ramificationIndex (Integers F) = 1) :
    RingHom.ker (WittVector.truncate (p := 2) (R := Residue F) 2) ≤
      RingHom.ker (unramifiedWittToA F he) := by
  intro x hx
  apply ker_truncate_le_ker_ghostToModFour (Integers F)
  rw [WittVector.mem_ker_truncate] at hx ⊢
  intro i hi
  simp [hx i hi]

/-- The comparison homomorphism from mathlib's length-two Witt ring to `A`. -/
def unramifiedWittTwoToA (he : ramificationIndex (Integers F) = 1) :
    TruncatedWittVector 2 2 (Residue F) →+* A (Integers F) :=
  RingHom.liftOfSurjective (WittVector.truncate 2)
    (WittVector.truncate_surjective 2 2 (Residue F))
    ⟨unramifiedWittToA F he, ker_truncate_le_ker_unramifiedWittToA F he⟩

@[simp]
theorem unramifiedWittTwoToA_truncate (he : ramificationIndex (Integers F) = 1)
    (x : WittVector 2 (Residue F)) :
    unramifiedWittTwoToA F he (WittVector.truncate 2 x) = unramifiedWittToA F he x :=
  RingHom.liftOfSurjective_comp_apply ..

/-- Perfectness of `k` and `(2) = 𝔪` make the second ghost map surjective. -/
theorem ghostToModFour_surjective (he : ramificationIndex (Integers F) = 1) :
    Function.Surjective (ghostToModFour (Integers F)) := by
  intro a
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨a₀, ha₀⟩ := surjective_frobenius (Residue F) 2 (IsLocalRing.residue _ z)
  obtain ⟨x₀, rfl⟩ := IsLocalRing.residue_surjective a₀
  have hz : z - x₀ ^ 2 ∈ rationalIdeal (Integers F) 2 := by
    rw [rationalIdeal_two_eq_maximalIdeal F he, ← IsLocalRing.residue_eq_zero_iff]
    simpa only [map_sub, map_pow, sub_eq_zero, frobenius_def] using ha₀.symm
  obtain ⟨x₁, hx₁⟩ := Ideal.mem_span_singleton.mp hz
  refine ⟨WittVector.map (Ideal.Quotient.mk (rationalIdeal (Integers F) 2))
    (WittVector.mk 2 (fun i => if i = 0 then x₀ else x₁)), ?_⟩
  rw [ghostToModFour_map_mk, ghostComponent_one]
  congr 1
  simp only [WittVector.coeff_mk, ↓reduceIte, Nat.one_ne_zero]
  linear_combination -hx₁

theorem unramifiedWittToA_surjective (he : ramificationIndex (Integers F) = 1) :
    Function.Surjective (unramifiedWittToA F he) :=
  (ghostToModFour_surjective F he).comp
    (WittVector.map_surjective _ (inverseFrobeniusToR F he).surjective)

theorem unramifiedWittTwoToA_surjective (he : ramificationIndex (Integers F) = 1) :
    Function.Surjective (unramifiedWittTwoToA F he) := by
  intro a
  obtain ⟨x, rfl⟩ := unramifiedWittToA_surjective F he a
  exact ⟨WittVector.truncate 2 x, unramifiedWittTwoToA_truncate F he x⟩

/-- Surjectivity and the previously established cardinality imply bijectivity. -/
theorem unramifiedWittTwoToA_bijective (he : ramificationIndex (Integers F) = 1) :
    Function.Bijective (unramifiedWittTwoToA F he) := by
  rw [Nat.bijective_iff_surjective_and_card]
  refine ⟨unramifiedWittTwoToA_surjective F he, ?_⟩
  rw [card_A, he, mul_one, Nat.card_eq_fintype_card, TruncatedWittVector.card]
  simp only [residueCard, Nat.card_eq_fintype_card]

/-- The unramified isomorphism `A = 𝒪/(4) ≃ W₂(k)`, with mathlib's Witt ring. -/
def unramifiedAEquivWittTwo (he : ramificationIndex (Integers F) = 1) :
    A (Integers F) ≃+* TruncatedWittVector 2 2 (Residue F) :=
  (RingEquiv.ofBijective (unramifiedWittTwoToA F he)
    (unramifiedWittTwoToA_bijective F he)).symm

/-- Reduction from `A = 𝒪/(4)` to the residue field. -/
def AtoResidue : A (Integers F) →+* Residue F :=
  Ideal.Quotient.lift _ (IsLocalRing.residue _) (by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
    simp only [map_mul, map_natCast]
    have h4 : (4 : Residue F) = 0 := (CharP.cast_eq_zero_iff (Residue F) 2 4).mpr (by decide)
    change (4 : Residue F) * IsLocalRing.residue _ y = 0
    rw [h4, zero_mul])

@[simp]
theorem AtoResidue_mk (x : Integers F) :
    AtoResidue F (Ideal.Quotient.mk (rationalIdeal (Integers F) 4) x) =
      IsLocalRing.residue _ x := rfl

theorem AtoResidue_ghostToModFour (he : ramificationIndex (Integers F) = 1)
    (x : WittVector 2 (R (Integers F))) :
    AtoResidue F (ghostToModFour (Integers F) x) =
      (unramifiedREquivResidue F he (x.coeff 0)) ^ 2 := by
  obtain ⟨y, rfl⟩ := WittVector.map_surjective
    (Ideal.Quotient.mk (rationalIdeal (Integers F) 2)) Ideal.Quotient.mk_surjective x
  rw [ghostToModFour_map_mk, AtoResidue_mk, ghostComponent_one]
  simp only [map_add, map_pow, map_mul, map_ofNat, WittVector.map_coeff,
    unramifiedREquivResidue_mk]
  have h2 : (2 : Residue F) = 0 := CharP.cast_eq_zero (Residue F) 2
  rw [h2, zero_mul, add_zero]

/-- Inverse Frobenius removes the Frobenius twist in the residue of the ghost map. -/
theorem AtoResidue_unramifiedWittToA (he : ramificationIndex (Integers F) = 1)
    (x : WittVector 2 (Residue F)) :
    AtoResidue F (unramifiedWittToA F he x) = x.coeff 0 := by
  rw [unramifiedWittToA, RingHom.comp_apply, AtoResidue_ghostToModFour F he]
  simp only [WittVector.map_coeff, inverseFrobeniusToR, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  exact frobeniusEquiv_symm_pow_p (Residue F) 2 _

/-- The Witt comparison commutes with canonical reduction to `k`. -/
theorem AtoResidue_unramifiedWittTwoToA (he : ramificationIndex (Integers F) = 1)
    (x : TruncatedWittVector 2 2 (Residue F)) :
    AtoResidue F (unramifiedWittTwoToA F he x) = x.coeff 0 := by
  obtain ⟨y, rfl⟩ := WittVector.truncate_surjective 2 2 (Residue F) x
  rw [unramifiedWittTwoToA_truncate, AtoResidue_unramifiedWittToA]
  rfl

/-- The zeroth Witt coordinate of the isomorphism is the usual residue class. -/
@[simp]
theorem unramifiedAEquivWittTwo_coeff_zero (he : ramificationIndex (Integers F) = 1)
    (a : A (Integers F)) :
    (unramifiedAEquivWittTwo F he a).coeff 0 = AtoResidue F a := by
  rw [← AtoResidue_unramifiedWittTwoToA F he]
  congr 1
  exact (unramifiedAEquivWittTwo F he).symm_apply_apply a

end Unramified

end
end Char2Theta.Dyadic

/-!
## The additive group of the mod-four quotient (§1.3)

A choice of integral basis identifies `𝒪/(4)` additively with `(ℤ/4ℤ)^d`.
The coordinates use mathlib's reduction map on the dyadic integers and the
additive quotient isomorphism theorem. No multiplicative compatibility is asserted.
-/

namespace Char2Theta.Dyadic
noncomputable section

/-- Reduction of a dyadic integer modulo four. -/
def padicToModFour : ℤ_[2] →+* ZMod 4 := PadicInt.toZModPow 2

theorem padicToModFour_eq_zero_iff (x : ℤ_[2]) :
    padicToModFour x = 0 ↔ (4 : ℤ_[2]) ∣ x := by
  change PadicInt.toZModPow 2 x = 0 ↔ _
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
  norm_num

variable (F : Type*) [Field F] [Algebra ℚ_[2] F] [FiniteDimensional ℚ_[2] F]

/-- An integral basis indexed by the field degree `d`. -/
def integralBasis : Module.Basis (Fin (degree F)) ℤ_[2] (Integers F) :=
  Module.finBasisOfFinrankEq ℤ_[2] (Integers F) (integers_rank F)

/-- Integral basis coordinates followed by reduction modulo four. -/
def integralCoordinatesModFour : Integers F →+ (Fin (degree F) → ZMod 4) where
  toFun x i := padicToModFour ((integralBasis F).equivFun x i)
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

@[simp]
theorem integralCoordinatesModFour_apply (x : Integers F) (i : Fin (degree F)) :
    integralCoordinatesModFour F x i = padicToModFour ((integralBasis F).equivFun x i) := rfl

theorem integralCoordinatesModFour_surjective :
    Function.Surjective (integralCoordinatesModFour F) := by
  intro x
  have hs := ZMod.ringHom_surjective padicToModFour
  choose y hy using fun i => hs (x i)
  refine ⟨(integralBasis F).equivFun.symm y, ?_⟩
  ext i
  change padicToModFour ((integralBasis F).equivFun
    ((integralBasis F).equivFun.symm y) i) = x i
  rw [LinearEquiv.apply_symm_apply]
  exact hy i

/-- The kernel of coordinate reduction is precisely the additive subgroup `4𝒪`. -/
theorem ker_integralCoordinatesModFour :
    (integralCoordinatesModFour F).ker = (rationalIdeal (Integers F) 4).toAddSubgroup := by
  ext x
  change integralCoordinatesModFour F x = 0 ↔ x ∈ rationalIdeal (Integers F) 4
  rw [rationalIdeal, Ideal.mem_span_singleton]
  constructor
  · intro hx
    have hc : ∀ i, (4 : ℤ_[2]) ∣ (integralBasis F).equivFun x i := fun i =>
      (padicToModFour_eq_zero_iff _).mp (congrFun hx i)
    choose y hy using hc
    refine ⟨(integralBasis F).equivFun.symm y, ?_⟩
    apply (integralBasis F).equivFun.injective
    rw [← nsmul_eq_mul, map_nsmul, LinearEquiv.apply_symm_apply]
    funext i
    exact hy i
  · rintro ⟨y, rfl⟩
    rw [← nsmul_eq_mul, map_nsmul]
    ext i
    change (4 : ℕ) • integralCoordinatesModFour F y i = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- A choice of integral basis gives `(𝒪/4𝒪,+) ≃ (ℤ/4ℤ)^d` for every dyadic field. -/
def AAddEquivModFour : A (Integers F) ≃+ (Fin (degree F) → ZMod 4) :=
  QuotientAddGroup.liftEquiv (rationalIdeal (Integers F) 4).toAddSubgroup
    (integralCoordinatesModFour_surjective F) (ker_integralCoordinatesModFour F).symm

@[simp]
theorem AAddEquivModFour_mk (x : Integers F) :
    AAddEquivModFour F (Ideal.Quotient.mk (rationalIdeal (Integers F) 4) x) =
      integralCoordinatesModFour F x := rfl

end
end Char2Theta.Dyadic
