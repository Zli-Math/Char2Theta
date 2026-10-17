import Char2Theta.Section1.DyadicLatticeModel
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

/-!
# 局部 Fourier 积分、自对偶归一化与 Plancherel（§1.3）

本文件统一局部 Fourier 的测试函数理论：正号核 `ψ(2x·y)`、Haar 积分、
变换保持 Schwartz–Bruhat 空间，以及限制到 `S_L` 的准确有限 Fourier 公式。
令 `N=q^(en)`，自对偶测度满足 `vol(2𝒪ⁿ)=1/√N`、`vol(𝒪ⁿ)=√N`。
随后证明平移、调制、缩放和积分对偶，推出全测试函数空间上的反演、
Parseval、Plancherel，以及该 Haar 归一化的唯一性。

阅读顺序：核与初始测度 → 积分闭合性 → 有限限制及体积缩放 → 格上反演 →
全空间反演与 Plancherel → 自对偶测度唯一性。
主要入口：`localFourierOperator_lattice_eq`、`localFourierOperator_sq`、
`localFourierOperator_plancherel`、`isSelfDualFourierMeasure_iff`。
完整 L² 酉延拓及 Gaussian／Weil 标量统一见 `DyadicWeil`。
-/

set_option autoImplicit false

/-! ## The local Fourier kernel and its integral-lattice annihilator -/

namespace Char2Theta.Dyadic
noncomputable section
open scoped BigOperators
variable (F : Type*) [NormedField F] [NormedAlgebra ℚ_[2] F]
  [FiniteDimensional ℚ_[2] F] (n : ℕ)
  (ψ : AddChar F ℂˣ) (hψ : HasConductorFour (Integers F).toSubring ψ)

/-- Positive-sign kernel, matching (2.3): `ψ(2x·y)`. -/
def localFourierKernel (y : Fin n → F) : LocallyConstant (Fin n → F) ℂ :=
  (polynomialPhase F n ψ hψ (fun x => 2 * ∑ i, x i * y i) (by fun_prop)).map
    (fun u : ℂˣ => (u : ℂ))

@[simp]
theorem localFourierKernel_apply (x y : Fin n → F) :
    localFourierKernel F n ψ hψ y x = (ψ (2 * ∑ i, x i * y i) : ℂ) := rfl

theorem localFourierKernel_add (x z y : Fin n → F) :
    localFourierKernel F n ψ hψ y (x + z) =
      localFourierKernel F n ψ hψ y x * localFourierKernel F n ψ hψ y z := by
  simp [localFourierKernel_apply, add_mul, Finset.sum_add_distrib, mul_add, ψ.map_add_eq_mul]

theorem localFourierKernel_symm (x y : Fin n → F) :
    localFourierKernel F n ψ hψ y x = localFourierKernel F n ψ hψ x y := by
  simp only [localFourierKernel_apply, mul_comm]

theorem localFourierKernel_integral_two (x u : Fin n → Integers F) :
    localFourierKernel F n ψ hψ (integralVector F n x) (fun i => 2 * (u i : F)) = 1 := by
  change (ψ (2 * ∑ i, (2 * (u i : F)) * (x i : F)) : ℂ) = 1
  have he : 2 * (∑ i, (2 * (u i : F)) * (x i : F)) =
      4 * ((∑ i, u i * x i : Integers F) : F) := by
    have hs := map_sum (Integers F).val (fun i => u i * x i) Finset.univ
    change ((∑ i, u i * x i : Integers F) : F) = ∑ i, (u i : F) * (x i : F) at hs
    rw [hs]
    simp only [mul_assoc, ← Finset.mul_sum]
    ring
  rw [he]
  exact congrArg (fun c : ℂˣ => (c : ℂ))
    (trivial_on_four (Integers F).toSubring ψ hψ (∑ i, u i * x i))

/-- The annihilator of `2𝒪ⁿ` for the kernel `ψ(2x·y)` is exactly `𝒪ⁿ`. -/
theorem localFourierKernel_annihilator (y : Fin n → F) :
    (∀ u : Fin n → Integers F,
      localFourierKernel F n ψ hψ y (fun i => 2 * (u i : F)) = 1) ↔
      y ∈ integralLattice F n := by
  classical
  constructor
  · intro h i
    have hc : ∀ a : Integers F, ψ ((4 * y i) * (a : F)) = 1 := by
      intro a
      apply Units.val_injective
      have hh := h (Pi.single i a)
      simpa [localFourierKernel_apply, Pi.single_apply, apply_ite, mul_assoc,
        mul_comm, mul_left_comm, show (2 : F) * 2 = 4 by norm_num] using hh
    obtain ⟨a, ha⟩ := (conductor_mem_iff (Integers F).toSubring ψ hψ (4 * y i)).mp hc
    have he : y i = (a : F) := mul_left_cancel₀ (by norm_num : (4 : F) ≠ 0) ha
    rw [he]
    exact a.property
  · intro hy u
    exact localFourierKernel_integral_two F n ψ hψ (fun i => ⟨y i, hy i⟩) u

theorem localFourierKernel_integral (x y : Fin n → Integers F) :
    localFourierKernel F n ψ hψ (integralVector F n y) (integralVector F n x) =
      fourierPairingChar F ψ hψ n (reduceVector F n x) (reduceVector F n y) :=
  (fourierPairingChar_integral F n ψ hψ x y).symm

end
end Char2Theta.Dyadic

/-!
## Haar measure conventions for the lattice Fourier transform

The initial Haar measure gives `2𝒪ⁿ` mass one. A subsequent explicit positive
rescaling gives the Fourier normalization used for the lattice model.
-/

namespace Char2Theta.Dyadic
noncomputable section
open MeasureTheory TopologicalSpace

namespace BorelTopology
/-- Opt-in Borel sigma algebra; existing measurable structures need not be replaced. -/
scoped instance (priority := 50) measurableSpace (F : Type*) [TopologicalSpace F] :
    MeasurableSpace F := borel F

scoped instance (priority := 50) borelSpace (F : Type*) [TopologicalSpace F] :
    @BorelSpace F _ (measurableSpace F) := ⟨rfl⟩
end BorelTopology

variable (F : Type*) [NormedField F] [NormedAlgebra ℚ_[2] F]
  [FiniteDimensional ℚ_[2] F] (n : ℕ)
  [MeasurableSpace (Fin n → F)] [BorelSpace (Fin n → F)]

/-- The compact open set used to normalize the initial Haar measure. -/
def twoLatticePositiveCompact : PositiveCompacts (Fin n → F) :=
  ⟨⟨multipleLattice F n 2, multipleLattice_isCompact F n 2⟩, by
    rw [(multipleLattice_isOpen F n 2 (by decide)).interior_eq]
    exact ⟨0, fun _ => ⟨0, by simp⟩⟩⟩

/-- Haar measure with `vol(2𝒪ⁿ)=1`, before Fourier normalization. -/
def latticeCountingHaar : Measure (Fin n → F) :=
  Measure.addHaarMeasure (twoLatticePositiveCompact F n)

instance latticeCountingHaar_isAddHaarMeasure : (latticeCountingHaar F n).IsAddHaarMeasure :=
  Measure.isAddHaarMeasure_addHaarMeasure _

@[simp]
theorem latticeCountingHaar_two : latticeCountingHaar F n (multipleLattice F n 2) = 1 :=
  Measure.addHaarMeasure_self

/-- Every residue coset has mass one for the initial normalization. -/
theorem latticeCountingHaar_coset (x : Fin n → Integers F) :
    latticeCountingHaar F n (latticeCoset F n x) = 1 := by
  have he : latticeCoset F n x =
      (fun z => z + (-integralVector F n x)) ⁻¹' multipleLattice F n 2 := by
    ext z
    simp only [latticeCoset, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hz
      exact ⟨z + -integralVector F n x, hz, by simp⟩
  rw [he, measure_preimage_add_right, latticeCountingHaar_two]

@[simp]
theorem latticeCountingHaar_real_coset (x : Fin n → Integers F) :
    (latticeCountingHaar F n).real (latticeCoset F n x) = 1 := by
  simp [Measure.real, latticeCountingHaar_coset]

end
end Char2Theta.Dyadic

/-!
## The local Fourier integral and its lattice restriction

The kernel has positive sign: `ψ(2x·y)`. All integrals are genuine Bochner
integrals on `Fⁿ` with its Borel sigma algebra and a specified Haar measure.
-/

namespace Char2Theta.Dyadic
noncomputable section
open MeasureTheory
open scoped BigOperators

variable (F : Type*) [NormedField F] [NormedAlgebra ℚ_[2] F]
  [FiniteDimensional ℚ_[2] F] (n : ℕ)
  [MeasurableSpace (Fin n → F)] [BorelSpace (Fin n → F)]
  (ψ : AddChar F ℂˣ) (hψ : HasConductorFour (Integers F).toSubring ψ)
  (μ : Measure (Fin n → F)) [μ.IsAddHaarMeasure]

/-- The integrand is continuous and compactly supported, hence integrable. -/
theorem localFourier_integrable (f : SchwartzBruhat (Fin n → F)) (y : Fin n → F) :
    Integrable (fun x => localFourierKernel F n ψ hψ y x * f.val x) μ :=
  ((localFourierKernel F n ψ hψ y).continuous.mul f.val.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.mul_left f.property)

/-- Fourier integral on all local test functions; lattice closure is proved below. -/
def localFourierIntegral (f : SchwartzBruhat (Fin n → F)) (y : Fin n → F) : ℂ :=
  ∫ x, localFourierKernel F n ψ hψ y x * f.val x ∂μ

/-- Linearity on the entire ambient Schwartz–Bruhat space. -/
def localFourierLinear : SchwartzBruhat (Fin n → F) →ₗ[ℂ] ((Fin n → F) → ℂ) where
  toFun := localFourierIntegral F n ψ hψ μ
  map_add' f g := by
    funext y
    change (∫ x, localFourierKernel F n ψ hψ y x * (f.val x + g.val x) ∂μ) = _
    simp_rw [mul_add]
    exact integral_add (localFourier_integrable F n ψ hψ μ f y)
      (localFourier_integrable F n ψ hψ μ g y)
  map_smul' c f := by
    funext y
    change (∫ x, localFourierKernel F n ψ hψ y x * (c * f.val x) ∂μ) =
      c * ∫ x, localFourierKernel F n ψ hψ y x * f.val x ∂μ
    simp_rw [mul_left_comm (localFourierKernel F n ψ hψ y _) c]
    exact integral_const_mul _ _

/-- Translation invariance of Haar measure and the character law give the
annihilator argument on actual integrals. -/
theorem localFourierIntegral_period_relation (f : LocalLatticeSpace F n)
    (u : Fin n → Integers F) (y : Fin n → F) :
    localFourierIntegral F n ψ hψ μ f.val y =
      localFourierKernel F n ψ hψ y (fun i => 2 * (u i : F)) *
        localFourierIntegral F n ψ hψ μ f.val y := by
  let w : Fin n → F := fun i => 2 * (u i : F)
  calc
    localFourierIntegral F n ψ hψ μ f.val y =
        ∫ x, localFourierKernel F n ψ hψ y (x + w) * f.val.val (x + w) ∂μ :=
      (integral_add_right_eq_self _ w).symm
    _ = ∫ x, localFourierKernel F n ψ hψ y w *
        (localFourierKernel F n ψ hψ y x * f.val.val x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [localFourierKernel_add, f.property.2]
      ring
    _ = _ := integral_const_mul _ _

/-- The integral vanishes outside `𝒪ⁿ`, using the actual conductor, not a
hypothesis identifying the finite and local transforms. -/
theorem localFourierIntegral_eq_zero (f : LocalLatticeSpace F n) (y : Fin n → F)
    (hy : y ∉ integralLattice F n) : localFourierIntegral F n ψ hψ μ f.val y = 0 := by
  have hn := mt (localFourierKernel_annihilator F n ψ hψ y).mp hy
  push Not at hn
  obtain ⟨u, hu⟩ := hn
  have he := localFourierIntegral_period_relation F n ψ hψ μ f u y
  have hh : (1 - localFourierKernel F n ψ hψ y (fun i => 2 * (u i : F))) *
      localFourierIntegral F n ψ hψ μ f.val y = 0 := by
    rw [sub_mul, one_mul, ← he, sub_self]
  exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr (Ne.symm hu))

omit [MeasurableSpace (Fin n → F)] [BorelSpace (Fin n → F)] in
/-- On an integral frequency the kernel is constant on each residue coset. -/
theorem localFourierKernel_on_coset (x y : Fin n → Integers F) (z : Fin n → F)
    (hz : z ∈ latticeCoset F n x) :
    localFourierKernel F n ψ hψ (integralVector F n y) z =
      localFourierKernel F n ψ hψ (integralVector F n y) (integralVector F n x) := by
  obtain ⟨u, rfl⟩ := (mem_latticeCoset_iff F n x z).mp hz
  rw [localFourierKernel_add, localFourierKernel_integral_two, mul_one]

omit [μ.IsAddHaarMeasure] in
/-- The transform of a lattice delta at an integral frequency, for any Haar measure. -/
theorem localFourierIntegral_delta (x y : Fin n → Integers F) :
    localFourierIntegral F n ψ hψ μ (latticeDelta F n (reduceVector F n x)).val
      (integralVector F n y) =
      (μ.real (latticeCoset F n x) : ℂ) *
        fourierPairingChar F ψ hψ n (reduceVector F n x) (reduceVector F n y) := by
  unfold localFourierIntegral
  rw [latticeDelta_reduceVector_eq_indicator]
  have he : (fun z => localFourierKernel F n ψ hψ (integralVector F n y) z *
      (latticeCoset F n x).indicator (fun _ => (1 : ℂ)) z) =
      (latticeCoset F n x).indicator (fun _ =>
        localFourierKernel F n ψ hψ (integralVector F n y) (integralVector F n x)) := by
    funext z
    by_cases hz : z ∈ latticeCoset F n x
    · simp only [Set.indicator_of_mem hz, mul_one]
      exact localFourierKernel_on_coset F n ψ hψ x y z hz
    · simp [hz]
  rw [he, integral_indicator_const _ (latticeCoset_isCompact F n x).isClosed.measurableSet]
  rw [localFourierKernel_integral, Complex.real_smul]

/-- With residue cosets of mass one, the local integral is exactly the finite sum. -/
theorem localFourierIntegral_counting_lattice (f : LocalLatticeSpace F n)
    (y : Fin n → Integers F) :
    localFourierIntegral F n ψ hψ (latticeCountingHaar F n) f.val (integralVector F n y) =
      finiteFourier F ψ hψ n (latticeEquivFinite F n f) (reduceVector F n y) := by
  have hd : ∀ a : Fin n → R (Integers F),
      localFourierIntegral F n ψ hψ (latticeCountingHaar F n) (latticeDelta F n a).val
        (integralVector F n y) = fourierPairingChar F ψ hψ n a (reduceVector F n y) := by
    intro a
    obtain ⟨x, rfl⟩ := reduceVector_surjective F n a
    rw [localFourierIntegral_delta, latticeCountingHaar_real_coset]
    simp
  let T := (localFourierLinear F n ψ hψ (latticeCountingHaar F n)).comp
    (LocalLatticeSpace F n).subtype
  have he := congrArg (fun h : LocalLatticeSpace F n => T h (integralVector F n y))
    (latticeDelta_expansion F n f)
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at he
  change (∑ a, latticeEquivFinite F n f a *
    localFourierIntegral F n ψ hψ (latticeCountingHaar F n) (latticeDelta F n a).val
      (integralVector F n y)) = _ at he
  simp_rw [hd] at he
  rw [finiteFourier_apply]
  exact he.symm

/-- Equality on the whole local space of arguments, including points outside the integer lattice. -/
theorem localFourierIntegral_counting_eq_extension (f : LocalLatticeSpace F n) :
    localFourierIntegral F n ψ hψ (latticeCountingHaar F n) f.val =
      latticeExtensionFun F n (finiteFourier F ψ hψ n (latticeEquivFinite F n f)) := by
  funext y
  by_cases hy : y ∈ integralLattice F n
  · let y' : Fin n → Integers F := fun i => ⟨y i, hy i⟩
    change localFourierIntegral F n ψ hψ (latticeCountingHaar F n) f.val
      (integralVector F n y') =
      latticeExtensionFun F n _ (integralVector F n y')
    rw [localFourierIntegral_counting_lattice, latticeExtensionFun_integralVector]
  · rw [localFourierIntegral_eq_zero F n ψ hψ _ f y hy,
      latticeExtensionFun_eq_zero F n _ y hy]

end
end Char2Theta.Dyadic

/-! ## The Fourier integral takes local Schwartz–Bruhat functions to themselves -/

namespace Char2Theta.Dyadic
noncomputable section
open MeasureTheory
open scoped BigOperators

/-- Compact support upgrades local constancy to a common open set of translation periods. -/
theorem schwartz_exists_open_periods {V : Type*} [NormedAddCommGroup V]
    (f : SchwartzBruhat V) :
    ∃ U : Set V, IsOpen U ∧ 0 ∈ U ∧ ∀ u ∈ U, ∀ x, f.val (x + u) = f.val x := by
  have ho : IsOpen {p : V × V | f.val (p.1 + p.2) = f.val p.1} := by
    simpa only [Pi.sub_apply, Function.comp_apply, Pi.add_apply, sub_eq_zero,
      LocallyConstant.toFun_eq_coe] using
      ((f.val.isLocallyConstant.comp_continuous (continuous_fst.add continuous_snd)).sub
        (f.val.isLocallyConstant.comp_continuous continuous_fst)).isOpen_fiber 0
  obtain ⟨A, B, _, hB, hA, h0, hAB⟩ := generalized_tube_lemma f.property
    (isCompact_singleton (x := (0 : V))) ho (by rintro ⟨x, u⟩ ⟨_, rfl⟩; simp)
  refine ⟨B ∩ (fun u => -u) ⁻¹' B, hB.inter (hB.preimage continuous_neg), ?_, ?_⟩
  · have hz := h0 (Set.mem_singleton 0)
    simpa using And.intro hz hz
  · rintro u ⟨hu, hnu⟩ x
    by_cases hx : x ∈ tsupport f.val
    · exact hAB (show (x, u) ∈ A ×ˢ B from ⟨hA hx, hu⟩)
    · by_cases hxu : x + u ∈ tsupport f.val
      · have hh := hAB (show (x + u, -u) ∈ A ×ˢ B from ⟨hA hxu, hnu⟩)
        simpa using hh.symm
      · rw [image_eq_zero_of_notMem_tsupport hxu, image_eq_zero_of_notMem_tsupport hx]

variable (F : Type*) [NormedField F] [NormedAlgebra ℚ_[2] F]
  [FiniteDimensional ℚ_[2] F] (n : ℕ)

/-- A common scalar multiple of the integer lattice fits inside any neighborhood of zero. -/
theorem exists_scaled_integralLattice_subset {U : Set (Fin n → F)}
    (hU : IsOpen U) (h0 : (0 : Fin n → F) ∈ U) :
    ∃ a : F, a ≠ 0 ∧ ∀ u : Fin n → Integers F, (fun i => a * (u i : F)) ∈ U := by
  obtain ⟨ε, hε, he⟩ := Metric.isOpen_iff.mp hU 0 h0
  obtain ⟨r, hr, hrε⟩ := NormedField.exists_norm_lt ℚ_[2] hε
  refine ⟨algebraMap ℚ_[2] F r, (map_ne_zero (algebraMap ℚ_[2] F)).mpr (norm_pos_iff.mp hr), ?_⟩
  intro u
  apply he
  rw [Metric.mem_ball, dist_zero_right]
  have hu : ‖integralVector F n u‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    have hi : (u i : F) ∈ (Integers F : Set F) := (u i).property
    rw [integers_eq_closedBall F] at hi
    simpa [integralVector, Metric.mem_closedBall, dist_zero_right] using hi
  calc
    ‖fun i => algebraMap ℚ_[2] F r * (u i : F)‖ =
        ‖(algebraMap ℚ_[2] F r) • integralVector F n u‖ := rfl
    _ = ‖algebraMap ℚ_[2] F r‖ * ‖integralVector F n u‖ := norm_smul _ _
    _ ≤ ‖algebraMap ℚ_[2] F r‖ := by nlinarith [norm_nonneg (algebraMap ℚ_[2] F r)]
    _ = ‖r‖ := norm_algebraMap' F r
    _ < ε := hrε

variable [MeasurableSpace (Fin n → F)] [BorelSpace (Fin n → F)]
  (ψ : AddChar F ℂˣ) (hψ : HasConductorFour (Integers F).toSubring ψ)
  (μ : Measure (Fin n → F)) [μ.IsAddHaarMeasure]

set_option maxHeartbeats 800000 in
omit [BorelSpace (Fin n → F)] [μ.IsAddHaarMeasure] in
/-- A tube around the compact support makes the Fourier kernel uniformly constant
in the frequency variable, proving local constancy of the integral. -/
theorem localFourierIntegral_isLocallyConstant (f : SchwartzBruhat (Fin n → F)) :
    IsLocallyConstant (localFourierIntegral F n ψ hψ μ f) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro y
  have hK : IsLocallyConstant (fun p : (Fin n → F) × (Fin n → F) =>
      (ψ (2 * ∑ i, p.1 i * p.2 i) : ℂ)) :=
    ((smoothCharacter_of_hasConductorFour F ψ hψ).comp_continuous (by fun_prop)).comp
      (fun c : ℂˣ => (c : ℂ))
  have ho : IsOpen {p : (Fin n → F) × (Fin n → F) |
      localFourierKernel F n ψ hψ p.2 p.1 = localFourierKernel F n ψ hψ y p.1} := by
    simpa only [Pi.sub_apply, Function.comp_apply, Pi.add_apply, sub_eq_zero,
      LocallyConstant.toFun_eq_coe, localFourierKernel_apply] using
      (hK.sub ((localFourierKernel F n ψ hψ y).isLocallyConstant.comp_continuous
        continuous_fst)).isOpen_fiber 0
  obtain ⟨A, B, _, hB, hA, hy, hAB⟩ := generalized_tube_lemma f.property
    (isCompact_singleton (x := y)) ho (by rintro ⟨x, z⟩ ⟨_, rfl⟩; rfl)
  refine ⟨B, hB, hy (Set.mem_singleton y), ?_⟩
  intro z hz
  change (∫ x, localFourierKernel F n ψ hψ z x * f.val x ∂μ) =
    ∫ x, localFourierKernel F n ψ hψ y x * f.val x ∂μ
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ tsupport f.val
  · have hh : localFourierKernel F n ψ hψ z x = localFourierKernel F n ψ hψ y x :=
      hAB (show (x, z) ∈ A ×ˢ B from ⟨hA hx, hz⟩)
    exact congrArg (fun c : ℂ => c * f.val x) hh
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]

/-- An open lattice of translation periods forces the Fourier support into a
compact scaled integer lattice, by the conductor condition. -/
theorem localFourierIntegral_hasCompactSupport (f : SchwartzBruhat (Fin n → F)) :
    HasCompactSupport (localFourierIntegral F n ψ hψ μ f) := by
  classical
  obtain ⟨U, hU, h0, hperiod⟩ := schwartz_exists_open_periods f
  obtain ⟨a, ha, hsmall⟩ := exists_scaled_integralLattice_subset F n hU h0
  let C : Set (Fin n → F) := (fun x : Fin n → F => (2 / a) • x) '' integralLattice F n
  have hC : IsCompact C := (integralLattice_isCompact F n).image (by fun_prop)
  apply HasCompactSupport.of_support_subset_isCompact hC
  intro y hy
  have hk : ∀ u : Fin n → Integers F,
      localFourierKernel F n ψ hψ y (fun i => a * (u i : F)) = 1 := by
    intro u
    let w : Fin n → F := fun i => a * (u i : F)
    have he : localFourierIntegral F n ψ hψ μ f y =
        localFourierKernel F n ψ hψ y w * localFourierIntegral F n ψ hψ μ f y := by
      calc
        _ = ∫ x, localFourierKernel F n ψ hψ y (x + w) * f.val (x + w) ∂μ :=
          (integral_add_right_eq_self _ w).symm
        _ = ∫ x, localFourierKernel F n ψ hψ y w *
            (localFourierKernel F n ψ hψ y x * f.val x) ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [localFourierKernel_add, hperiod w (hsmall u) x]
          ring
        _ = _ := integral_const_mul _ _
    exact mul_right_cancel₀ hy (by simpa only [one_mul] using he.symm)
  have hi : ∀ i : Fin n, ∃ b : Integers F, y i = (2 / a) * (b : F) := by
    intro i
    have hc : ∀ b : Integers F, ψ ((2 * a * y i) * (b : F)) = 1 := by
      intro b
      apply Units.val_injective
      simpa [localFourierKernel_apply, Pi.single_apply, apply_ite, mul_assoc,
        mul_comm, mul_left_comm] using hk (Pi.single i b)
    obtain ⟨b, hb⟩ := (conductor_mem_iff (Integers F).toSubring ψ hψ (2 * a * y i)).mp hc
    refine ⟨b, ?_⟩
    field_simp
    have h2 : (2 : F) ≠ 0 := by norm_num
    apply mul_left_cancel₀ h2
    calc
      2 * (y i * a) = 2 * a * y i := by ring
      _ = 4 * (b : F) := hb
      _ = 2 * (2 * (b : F)) := by ring
  choose b hb using hi
  exact ⟨integralVector F n b, fun i => (b i).property, funext (fun i => (hb i).symm)⟩

/-- The local Fourier operator on the entire original Schwartz–Bruhat space. -/
def localFourierOperator : SchwartzBruhat (Fin n → F) →ₗ[ℂ] SchwartzBruhat (Fin n → F) where
  toFun f := ⟨⟨localFourierIntegral F n ψ hψ μ f,
    localFourierIntegral_isLocallyConstant F n ψ hψ μ f⟩,
    localFourierIntegral_hasCompactSupport F n ψ hψ μ f⟩
  map_add' f g := by
    apply Subtype.ext
    apply LocallyConstant.ext
    exact congrFun ((localFourierLinear F n ψ hψ μ).map_add f g)
  map_smul' c f := by
    apply Subtype.ext
    apply LocallyConstant.ext
    exact congrFun ((localFourierLinear F n ψ hψ μ).map_smul c f)

@[simp]
theorem localFourierOperator_apply (f : SchwartzBruhat (Fin n → F)) (y : Fin n → F) :
    (localFourierOperator F n ψ hψ μ f).val y = localFourierIntegral F n ψ hψ μ f y := rfl

end
end Char2Theta.Dyadic

/-!
## Haar normalization and the exact finite Fourier coefficient

Write `N = |(𝒪/2𝒪)ⁿ| = q^(en)`. Our positive Haar normalization is
`vol(2𝒪ⁿ)=1/√N` and `vol(𝒪ⁿ)=√N`. The positive-sign Fourier integral therefore
restricts to `N^(-1/2)` times the finite character sum. An additional Weil scalar
belongs to the choice of a metaplectic lift, not to the Haar measure.
-/

namespace Char2Theta.Dyadic
noncomputable section
open MeasureTheory
open scoped BigOperators

variable (F : Type*) [NormedField F] [NormedAlgebra ℚ_[2] F]
  [FiniteDimensional ℚ_[2] F] (n : ℕ)

/-- Number of residue labels in the lattice model. -/
abbrev latticeLabelCard : ℕ := Fintype.card (Fin n → R (Integers F))

theorem latticeLabelCard_eq :
    latticeLabelCard F n = residueCard F ^ (ramificationIndex (Integers F) * n) := by
  rw [latticeLabelCard, Fintype.card_fun, ← Nat.card_eq_fintype_card, card_R, pow_mul, Fintype.card_fin]

theorem latticeLabelCard_pos : 0 < latticeLabelCard F n := Fintype.card_pos

/-- The positive real coefficient of the normalized finite Fourier sum. -/
def latticeFourierScale : ℝ := (Real.sqrt (latticeLabelCard F n : ℝ))⁻¹

theorem latticeFourierScale_eq :
    latticeFourierScale F n =
      (Real.sqrt ((residueCard F : ℝ) ^ (ramificationIndex (Integers F) * n)))⁻¹ := by
  simp only [latticeFourierScale, latticeLabelCard_eq, Nat.cast_pow]

theorem latticeFourierScale_pos : 0 < latticeFourierScale F n :=
  inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast latticeLabelCard_pos F n))

/-- The Fourier coefficient as a nonzero complex scalar. -/
def latticeFourierUnit : ℂˣ :=
  Units.mk0 (latticeFourierScale F n : ℂ)
    (Complex.ofReal_ne_zero.mpr (latticeFourierScale_pos F n).ne')

@[simp]
theorem latticeFourierUnit_coe : (latticeFourierUnit F n : ℂ) = latticeFourierScale F n := rfl

variable [MeasurableSpace (Fin n → F)] [BorelSpace (Fin n → F)]

/-- Explicit Haar normalization for the kernel `ψ(2x·y)`. -/
def latticeFourierHaar : Measure (Fin n → F) :=
  ENNReal.ofReal (latticeFourierScale F n) • latticeCountingHaar F n

instance latticeFourierHaar_isAddHaarMeasure : (latticeFourierHaar F n).IsAddHaarMeasure :=
  Measure.IsAddHaarMeasure.smul _
    (ENNReal.ofReal_ne_zero_iff.mpr (latticeFourierScale_pos F n)) ENNReal.ofReal_ne_top

@[simp]
theorem latticeFourierHaar_two :
    latticeFourierHaar F n (multipleLattice F n 2) = ENNReal.ofReal (latticeFourierScale F n) := by
  simp [latticeFourierHaar, Measure.smul_apply]

@[simp]
theorem latticeFourierHaar_coset (x : Fin n → Integers F) :
    (latticeFourierHaar F n).real (latticeCoset F n x) = latticeFourierScale F n := by
  simp [latticeFourierHaar, ENNReal.toReal_ofReal (latticeFourierScale_pos F n).le]

/-- The stated mass of `2𝒪ⁿ` determines the Haar measure uniquely. -/
theorem latticeFourierHaar_unique (μ : Measure (Fin n → F)) [μ.IsAddHaarMeasure]
    (hμ : μ (multipleLattice F n 2) = ENNReal.ofReal (latticeFourierScale F n)) :
    μ = latticeFourierHaar F n := by
  rw [Measure.addHaarMeasure_unique μ (twoLatticePositiveCompact F n)]
  change μ (multipleLattice F n 2) • latticeCountingHaar F n = latticeFourierHaar F n
  rw [hμ]
  rfl

variable (ψ : AddChar F ℂˣ) (hψ : HasConductorFour (Integers F).toSubring ψ)

/-- Scaling the measure scales the actual local integral, on every test function. -/
theorem localFourierIntegral_normalized (f : SchwartzBruhat (Fin n → F)) (y : Fin n → F) :
    localFourierIntegral F n ψ hψ (latticeFourierHaar F n) f y =
      (latticeFourierScale F n : ℂ) *
        localFourierIntegral F n ψ hψ (latticeCountingHaar F n) f y := by
  simp only [localFourierIntegral, latticeFourierHaar, integral_smul_measure,
    ENNReal.toReal_ofReal (latticeFourierScale_pos F n).le, Complex.real_smul]

/-- The actual normalized local Fourier operator restricted to the lattice space
agrees with the previously constructed finite transform, with a proved scalar. -/
theorem localFourierOperator_lattice_eq (f : LocalLatticeSpace F n) :
    localFourierOperator F n ψ hψ (latticeFourierHaar F n) f.val =
      (latticeFiniteFourier F n ψ hψ (latticeFourierUnit F n) f).val := by
  apply Subtype.ext
  apply LocallyConstant.ext
  intro y
  change localFourierIntegral F n ψ hψ (latticeFourierHaar F n) f.val y = _
  rw [localFourierIntegral_normalized, localFourierIntegral_counting_eq_extension]
  change (latticeFourierScale F n : ℂ) * latticeExtensionFun F n
      (finiteFourier F ψ hψ n (latticeEquivFinite F n f)) y =
    latticeExtensionFun F n ((latticeFourierUnit F n : ℂ) •
      finiteFourier F ψ hψ n (latticeEquivFinite F n f)) y
  simp [latticeExtensionFun, Pi.smul_apply, smul_eq_mul]

/-- Stability of `S_L` under the actual local Fourier operator. -/
theorem localFourierOperator_stable (f : SchwartzBruhat (Fin n → F))
    (hf : f ∈ LocalLatticeSpace F n) :
    localFourierOperator F n ψ hψ (latticeFourierHaar F n) f ∈ LocalLatticeSpace F n := by
  rw [localFourierOperator_lattice_eq F n ψ hψ ⟨f, hf⟩]
  exact (latticeFiniteFourier F n ψ hψ (latticeFourierUnit F n) ⟨f, hf⟩).property

/-- The lattice Fourier equivalence, now identified with a genuine Haar integral. -/
def normalizedLatticeFourier : LocalLatticeSpace F n ≃ₗ[ℂ] LocalLatticeSpace F n :=
  latticeFiniteFourier F n ψ hψ (latticeFourierUnit F n)

omit [MeasurableSpace (Fin n → F)] [BorelSpace (Fin n → F)] in
/-- The restriction in finite coordinates is the normalized character sum. -/
@[simp]
theorem normalizedLatticeFourier_finite (f : LocalLatticeSpace F n) :
    latticeEquivFinite F n (normalizedLatticeFourier F n ψ hψ f) =
      (latticeFourierScale F n : ℂ) •
        finiteFourier F ψ hψ n (latticeEquivFinite F n f) := by
  simp only [normalizedLatticeFourier, latticeFiniteFourier, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rfl

omit [MeasurableSpace (Fin n → F)] [BorelSpace (Fin n → F)] in
/-- Exact finite-coordinate formula, including the positive measure factor. -/
theorem normalizedLatticeFourier_apply (f : LocalLatticeSpace F n) (y : Fin n → Integers F) :
    (normalizedLatticeFourier F n ψ hψ f).val.val (integralVector F n y) =
      (latticeFourierScale F n : ℂ) * ∑ a, latticeEquivFinite F n f a *
        fourierPairingChar F ψ hψ n a (reduceVector F n y) :=
  latticeFiniteFourier_apply F n ψ hψ (latticeFourierUnit F n) f y

/-- An additional nonzero scalar multiplying the local operator also multiplies
the finite coefficient. This does not identify any particular metaplectic lift. -/
theorem scaled_localFourierOperator_lattice_eq (γ : ℂˣ) (f : LocalLatticeSpace F n) :
    (γ : ℂ) • localFourierOperator F n ψ hψ (latticeFourierHaar F n) f.val =
      (latticeFiniteFourier F n ψ hψ (γ * latticeFourierUnit F n) f).val := by
  rw [localFourierOperator_lattice_eq]
  apply Subtype.ext
  apply LocallyConstant.ext
  intro y
  change (γ : ℂ) * latticeExtensionFun F n
      ((latticeFourierUnit F n : ℂ) • finiteFourier F ψ hψ n (latticeEquivFinite F n f)) y =
    latticeExtensionFun F n (((γ * latticeFourierUnit F n : ℂˣ) : ℂ) •
      finiteFourier F ψ hψ n (latticeEquivFinite F n f)) y
  simp [latticeExtensionFun, Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- The Fourier case of the earlier generator interface is now discharged by an
actual integral operator, with no assumed restriction formula. -/
theorem localFourierOperator_generatorFormula :
    LatticeGeneratorFormula F n ψ hψ
      (localFourierOperator F n ψ hψ (latticeFourierHaar F n)) :=
  .fourier (latticeFourierUnit F n) (localFourierOperator_lattice_eq F n ψ hψ)

/-- The initial Haar normalization gives the integer lattice mass `N`. -/
theorem latticeCountingHaar_real_integralLattice :
    (latticeCountingHaar F n).real (integralLattice F n) = latticeLabelCard F n := by
  let f : LocalLatticeSpace F n := latticeExtension F n (fun _ => 1)
  let χ := conductorFourCharacter F
  have hχ := conductorFourCharacter_hasConductorFour F
  have he := localFourierIntegral_counting_lattice F n χ hχ f 0
  have hf : (f.val.val : (Fin n → F) → ℂ) = (integralLattice F n).indicator (fun _ => 1) := by
    funext x
    by_cases hx : x ∈ integralLattice F n <;>
      simp [f, latticeExtension, latticeExtensionFun, hx]
  have hred : latticeEquivFinite F n f = fun _ => 1 :=
    (latticeEquivFinite F n).apply_symm_apply _
  simp only [localFourierIntegral, localFourierKernel_apply, integralVector, Pi.zero_apply,
    ZeroMemClass.coe_zero, mul_zero, Finset.sum_const_zero, AddChar.map_zero_eq_one,
    Units.val_one, one_mul, hf] at he
  rw [integral_indicator_const _ (integralLattice_isCompact F n).isClosed.measurableSet] at he
  rw [finiteFourier_apply, hred] at he
  simp [fourierPairingChar, reduceVector, Complex.real_smul] at he
  apply Complex.ofReal_injective
  simpa [latticeLabelCard] using he

/-- The chosen normalization has `vol(𝒪ⁿ)=√N` and `vol(2𝒪ⁿ)=1/√N`. -/
theorem latticeFourierHaar_real_integralLattice :
    (latticeFourierHaar F n).real (integralLattice F n) = Real.sqrt (latticeLabelCard F n : ℝ) := by
  rw [latticeFourierHaar, measureReal_ennreal_smul_apply,
    ENNReal.toReal_ofReal (latticeFourierScale_pos F n).le,
    latticeCountingHaar_real_integralLattice F n]
  have hN : (0 : ℝ) < latticeLabelCard F n := by exact_mod_cast latticeLabelCard_pos F n
  dsimp [latticeFourierScale]
  calc
    (Real.sqrt (latticeLabelCard F n : ℝ))⁻¹ * (latticeLabelCard F n : ℝ) =
        (Real.sqrt (latticeLabelCard F n : ℝ))⁻¹ *
          (Real.sqrt (latticeLabelCard F n : ℝ) * Real.sqrt (latticeLabelCard F n : ℝ)) := by
      rw [Real.mul_self_sqrt hN.le]
    _ = _ := inv_mul_cancel_left₀ (Real.sqrt_pos.mpr hN).ne' _

end
end Char2Theta.Dyadic

/-! ## Inversion on the local lattice model with the specified Haar normalization -/

namespace Char2Theta.Dyadic
noncomputable section
open scoped BigOperators Classical
variable (F : Type*) [NormedField F] [NormedAlgebra ℚ_[2] F]
  [FiniteDimensional ℚ_[2] F] (n : ℕ)
  (ψ : AddChar F ℂˣ) (hψ : HasConductorFour (Integers F).toSubring ψ)

omit [FiniteDimensional ℚ_[2] F] in
/-- Symmetry of the finite pairing. -/
theorem fourierPairingChar_symm (a b : Fin n → R (Integers F)) :
    fourierPairingChar F ψ hψ n a b = fourierPairingChar F ψ hψ n b a := by
  simp [fourierPairingChar, mul_comm]

omit [FiniteDimensional ℚ_[2] F] in
theorem fourierPairingChar_add_left (a b c : Fin n → R (Integers F)) :
    fourierPairingChar F ψ hψ n (a + b) c =
      fourierPairingChar F ψ hψ n a c * fourierPairingChar F ψ hψ n b c := by
  simp [fourierPairingChar, add_mul, AddChar.map_add_eq_mul, Finset.prod_mul_distrib]

/-- Orthogonality, by mathlib's sum of a nontrivial character theorem. -/
theorem fourierPairingChar_sum (a : Fin n → R (Integers F)) :
    ∑ b, fourierPairingChar F ψ hψ n a b =
      if a = 0 then (latticeLabelCard F n : ℂ) else 0 := by
  classical
  by_cases ha : a = 0
  · subst a
    simp [fourierPairingChar, latticeLabelCard]
  · rw [if_neg ha]
    apply AddChar.sum_eq_zero_of_ne_one
    intro he
    apply ha
    apply fourierPairingChar_injective F ψ hψ n
    rw [he]
    ext b
    simp [fourierPairingChar]

/-- The unnormalized transform squares to cardinality times reflection. -/
theorem finiteFourier_sq (f : FiniteLatticeSpace (Integers F) n)
    (b : Fin n → R (Integers F)) :
    finiteFourier F ψ hψ n (finiteFourier F ψ hψ n f) b =
      (latticeLabelCard F n : ℂ) * f (-b) := by
  classical
  simp_rw [finiteFourier_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ a, ∑ c, (f a * fourierPairingChar F ψ hψ n a c) *
        fourierPairingChar F ψ hψ n c b) =
        ∑ a, f a * ∑ c, fourierPairingChar F ψ hψ n (a + b) c := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [fourierPairingChar_add_left, fourierPairingChar_symm F n ψ hψ c b]
      ring
    _ = _ := by
      simp_rw [fourierPairingChar_sum, add_eq_zero_iff_eq_neg]
      simp [mul_ite, mul_comm]

/-- The square of the normalization coefficient cancels the cardinality factor. -/
theorem latticeFourierScale_sq :
    (latticeFourierScale F n : ℂ) ^ 2 * (latticeLabelCard F n : ℂ) = 1 := by
  have hN : (0 : ℝ) < latticeLabelCard F n := by exact_mod_cast latticeLabelCard_pos F n
  have hs : Real.sqrt (latticeLabelCard F n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
  have he : latticeFourierScale F n ^ 2 * (latticeLabelCard F n : ℝ) = 1 := by
    dsimp [latticeFourierScale]
    rw [inv_pow]
    calc
      _ = (Real.sqrt (latticeLabelCard F n : ℝ) ^ 2)⁻¹ *
          Real.sqrt (latticeLabelCard F n : ℝ) ^ 2 := by
        congr 1
        exact (Real.sq_sqrt hN.le).symm
      _ = _ := inv_mul_cancel₀ (pow_ne_zero _ hs)
  exact_mod_cast he

/-- On the mod-two lattice model reflection is the identity, so the normalized
Fourier operator is an involution. This statement concerns `S_L`, not global inversion. -/
theorem normalizedLatticeFourier_involutive :
    Function.Involutive (normalizedLatticeFourier F n ψ hψ) := by
  intro f
  apply (latticeEquivFinite F n).injective
  simp only [normalizedLatticeFourier_finite]
  ext b
  change (latticeFourierScale F n : ℂ) *
    finiteFourier F ψ hψ n ((latticeFourierScale F n : ℂ) •
      finiteFourier F ψ hψ n (latticeEquivFinite F n f)) b = _
  rw [map_smul]
  change (latticeFourierScale F n : ℂ) * ((latticeFourierScale F n : ℂ) *
    finiteFourier F ψ hψ n (finiteFourier F ψ hψ n (latticeEquivFinite F n f)) b) = _
  rw [finiteFourier_sq]
  have hn : -b = b := by
    funext i
    exact CharTwo.neg_eq (b i)
  rw [hn]
  have hs := latticeFourierScale_sq F n
  calc
    _ = ((latticeFourierScale F n : ℂ) ^ 2 * (latticeLabelCard F n : ℂ)) *
        latticeEquivFinite F n f b := by ring
    _ = _ := by rw [hs, one_mul]

variable [MeasurableSpace (Fin n → F)] [BorelSpace (Fin n → F)]

/-- Inversion on `S_L`, expressed with the actual ambient Haar-integral operator. -/
theorem localFourierOperator_sq_on_lattice (f : LocalLatticeSpace F n) :
    localFourierOperator F n ψ hψ (latticeFourierHaar F n)
      (localFourierOperator F n ψ hψ (latticeFourierHaar F n) f.val) = f.val := by
  have hres (g : LocalLatticeSpace F n) :
      localFourierOperator F n ψ hψ (latticeFourierHaar F n) g.val =
        (normalizedLatticeFourier F n ψ hψ g).val :=
    localFourierOperator_lattice_eq F n ψ hψ g
  rw [hres f, hres (normalizedLatticeFourier F n ψ hψ f)]
  exact congrArg Subtype.val (normalizedLatticeFourier_involutive F n ψ hψ f)

end
end Char2Theta.Dyadic

/-! ## Change of variables and bilinear duality for the local Fourier integral -/

namespace Char2Theta.Dyadic
noncomputable section
open MeasureTheory
open scoped BigOperators

variable (F : Type*) [NormedField F] [NormedAlgebra ℚ_[2] F]
  [FiniteDimensional ℚ_[2] F] (n : ℕ)

/-- Translation with the convention `Tₐ f(x)=f(x+a)`. -/
def schwartzTranslate (a : Fin n → F) := schwartzPullback (Homeomorph.addRight a)

/-- Pullback by a nonzero scalar. -/
def schwartzDilate (a : Fˣ) :
    SchwartzBruhat (Fin n → F) ≃ₗ[ℂ] SchwartzBruhat (Fin n → F) :=
  schwartzPullback (Homeomorph.smul a)

/-- The complex-valued modulus of scalar dilation, supplied by mathlib's Haar character. -/
def haarDilation (a : Fˣ) : ℂ := (distribHaarChar (Fin n → F) a : ℝ)

theorem haarDilation_inv_mul (a : Fˣ) : haarDilation F n a⁻¹ * haarDilation F n a = 1 := by
  unfold haarDilation
  rw [← Complex.ofReal_mul, ← NNReal.coe_mul, ← map_mul, inv_mul_cancel, map_one]
  rfl

variable [MeasurableSpace (Fin n → F)] [BorelSpace (Fin n → F)]
  (ψ : AddChar F ℂˣ) (hψ : HasConductorFour (Integers F).toSubring ψ)
  (μ : Measure (Fin n → F)) [μ.IsAddHaarMeasure]

/-- Haar change of variables, without choosing coordinates or a determinant formula. -/
theorem integral_unit_smul (a : Fˣ) (g : (Fin n → F) → ℂ) :
    (∫ x, g (a • x) ∂μ) = haarDilation F n a⁻¹ * ∫ x, g x ∂μ := by
  have he := integral_domSMul (μ := μ) (DomMulAct.mk a⁻¹) g
  simp only [Equiv.symm_apply_apply, inv_inv] at he
  rw [← he, Measure.isAddLeftInvariant_eq_smul (DomMulAct.mk a⁻¹ • μ) μ,
    addHaarScalarFactor_smul_eq_distribHaarChar, integral_smul_nnreal_measure]
  change (distribHaarChar (Fin n → F) a⁻¹ : ℝ) • (∫ x, g x ∂μ) = _
  rw [Complex.real_smul]
  rfl

omit [MeasurableSpace (Fin n → F)] [BorelSpace (Fin n → F)] in
theorem localFourierKernel_smul (a : Fˣ) (x y : Fin n → F) :
    localFourierKernel F n ψ hψ y (a • x) =
      localFourierKernel F n ψ hψ (a • y) x := by
  simp only [localFourierKernel_apply, Pi.smul_apply, Units.smul_def, smul_eq_mul]
  congr 3
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Fourier transform of a dilation. -/
theorem localFourierOperator_dilate (a : Fˣ) (f : SchwartzBruhat (Fin n → F)) :
    localFourierOperator F n ψ hψ μ (schwartzDilate F n a f) =
      haarDilation F n a⁻¹ • schwartzDilate F n a⁻¹ (localFourierOperator F n ψ hψ μ f) := by
  apply Subtype.ext
  apply LocallyConstant.ext
  intro y
  change (∫ x, localFourierKernel F n ψ hψ y x * f.val (a • x) ∂μ) =
    haarDilation F n a⁻¹ * ∫ x, localFourierKernel F n ψ hψ (a⁻¹ • y) x * f.val x ∂μ
  rw [← integral_unit_smul]
  congr 1
  funext x
  rw [localFourierKernel_smul, smul_inv_smul]

/-- The two reciprocal Haar factors cancel in the square of Fourier. -/
theorem localFourierOperator_sq_dilate (a : Fˣ) (f : SchwartzBruhat (Fin n → F)) :
    localFourierOperator F n ψ hψ μ
      (localFourierOperator F n ψ hψ μ (schwartzDilate F n a f)) =
    schwartzDilate F n a (localFourierOperator F n ψ hψ μ
      (localFourierOperator F n ψ hψ μ f)) := by
  rw [localFourierOperator_dilate, map_smul, localFourierOperator_dilate, inv_inv,
    smul_smul, haarDilation_inv_mul, one_smul]

/-- Multiplication by a Fourier character. -/
def schwartzModulate (a : Fin n → F) (f : SchwartzBruhat (Fin n → F)) :=
  schwartzMul (localFourierKernel F n ψ hψ a) f

omit [MeasurableSpace (Fin n → F)] [BorelSpace (Fin n → F)] in
theorem localFourierKernel_add_frequency (a b x : Fin n → F) :
    localFourierKernel F n ψ hψ (a + b) x =
      localFourierKernel F n ψ hψ a x * localFourierKernel F n ψ hψ b x := by
  simp [localFourierKernel_apply, mul_add, Finset.sum_add_distrib, ψ.map_add_eq_mul]

/-- Modulation becomes translation in frequency. -/
theorem localFourierOperator_modulate (a : Fin n → F) (f : SchwartzBruhat (Fin n → F)) :
    localFourierOperator F n ψ hψ μ (schwartzModulate F n ψ hψ a f) =
      schwartzTranslate F n a (localFourierOperator F n ψ hψ μ f) := by
  apply Subtype.ext
  apply LocallyConstant.ext
  intro y
  change (∫ x, localFourierKernel F n ψ hψ y x *
    (localFourierKernel F n ψ hψ a x * f.val x) ∂μ) =
    ∫ x, localFourierKernel F n ψ hψ (y + a) x * f.val x ∂μ
  simp_rw [localFourierKernel_add_frequency, mul_assoc]

/-- Translation becomes multiplication by the negative-frequency character. -/
theorem localFourierOperator_translate (a : Fin n → F) (f : SchwartzBruhat (Fin n → F)) :
    localFourierOperator F n ψ hψ μ (schwartzTranslate F n a f) =
      schwartzModulate F n ψ hψ (-a) (localFourierOperator F n ψ hψ μ f) := by
  apply Subtype.ext
  apply LocallyConstant.ext
  intro y
  change (∫ x, localFourierKernel F n ψ hψ y x * f.val (x + a) ∂μ) =
    localFourierKernel F n ψ hψ (-a) y * ∫ x, localFourierKernel F n ψ hψ y x * f.val x ∂μ
  rw [← integral_const_mul]
  have he := integral_add_right_eq_self
    (fun x => localFourierKernel F n ψ hψ (-a) y *
      (localFourierKernel F n ψ hψ y x * f.val x)) a (μ := μ)
  rw [← he]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [localFourierKernel_symm F n ψ hψ y (-a), ← mul_assoc,
    ← localFourierKernel_add]
  simp

/-- Fourier squared reverses the translation parameter. -/
theorem localFourierOperator_sq_translate (a : Fin n → F) (f : SchwartzBruhat (Fin n → F)) :
    localFourierOperator F n ψ hψ μ
      (localFourierOperator F n ψ hψ μ (schwartzTranslate F n a f)) =
    schwartzTranslate F n (-a) (localFourierOperator F n ψ hψ μ
      (localFourierOperator F n ψ hψ μ f)) := by
  rw [localFourierOperator_translate, localFourierOperator_modulate]

set_option maxHeartbeats 800000 in
/-- Bilinear Fourier duality on test functions, by compact-support Fubini. -/
theorem localFourierOperator_bilinear (f g : SchwartzBruhat (Fin n → F)) :
    (∫ y, (localFourierOperator F n ψ hψ μ f).val y * g.val y ∂μ) =
      ∫ x, f.val x * (localFourierOperator F n ψ hψ μ g).val x ∂μ := by
  have hc : Continuous (fun p : (Fin n → F) × (Fin n → F) =>
      localFourierKernel F n ψ hψ p.2 p.1 * f.val p.1 * g.val p.2) := by
    have hk : Continuous (fun p : (Fin n → F) × (Fin n → F) =>
        localFourierKernel F n ψ hψ p.2 p.1) :=
      Units.continuous_val.comp ((smoothCharacter_of_hasConductorFour F ψ hψ).continuous.comp
        (show Continuous (fun p : (Fin n → F) × (Fin n → F) =>
          2 * ∑ i, p.1 i * p.2 i) from by fun_prop))
    exact (hk.mul (f.val.continuous.comp continuous_fst)).mul
      (g.val.continuous.comp continuous_snd)
  have hs : HasCompactSupport (fun p : (Fin n → F) × (Fin n → F) =>
      localFourierKernel F n ψ hψ p.2 p.1 * f.val p.1 * g.val p.2) := by
    apply HasCompactSupport.of_support_subset_isCompact (f.property.prod g.property)
    intro p hp
    exact ⟨subset_tsupport _ (fun h => hp (by simp [h])),
      subset_tsupport _ (fun h => hp (by simp [h]))⟩
  simp only [localFourierOperator_apply, localFourierIntegral]
  simp_rw [← integral_mul_const, ← integral_const_mul]
  rw [← integral_integral_swap_of_hasCompactSupport hc hs]
  congr 1
  funext x
  congr 1
  funext y
  rw [localFourierKernel_symm F n ψ hψ x y]
  ring

end
end Char2Theta.Dyadic

/-!
## Fourier inversion on the whole Schwartz–Bruhat space

Small dilations of the lattice delta test equality at zero. Bilinear Fourier
duality and covariance then promote lattice inversion to global inversion.
-/

namespace Char2Theta.Dyadic
noncomputable section
open MeasureTheory

variable (F : Type*) [NormedField F] [NormedAlgebra ℚ_[2] F]
  [FiniteDimensional ℚ_[2] F] (n : ℕ)

/-- A dilated characteristic function of `2𝒪ⁿ`, used as a local test function. -/
def fourierTest (a : Fˣ) : SchwartzBruhat (Fin n → F) :=
  schwartzDilate F n a (latticeDelta F n 0).val

/-- These test functions have arbitrarily small support. -/
theorem exists_fourierTest_support_subset {U : Set (Fin n → F)}
    (hU : IsOpen U) (h0 : (0 : Fin n → F) ∈ U) :
    ∃ a : Fˣ, Function.support (fourierTest F n a).val ⊆ U := by
  obtain ⟨b, hb, hsmall⟩ := exists_scaled_integralLattice_subset F n hU h0
  let b' : Fˣ := Units.mk0 b hb
  refine ⟨b'⁻¹, ?_⟩
  intro x hx
  have hi : b'⁻¹ • x ∈ integralLattice F n := by
    by_contra hn
    exact hx (latticeDelta_eq_zero F n 0 _ hn)
  let u : Fin n → Integers F := fun i => ⟨(b'⁻¹ • x) i, hi i⟩
  have he : (fun i => b * (u i : F)) = x := by
    change b' • (b'⁻¹ • x) = x
    exact smul_inv_smul b' x
  simpa only [he] using hsmall u

/-- The zero delta is exactly the characteristic function of `2𝒪ⁿ`. -/
theorem latticeDelta_zero_indicator :
    ((latticeDelta F n 0).val.val : (Fin n → F) → ℂ) =
      (multipleLattice F n 2).indicator (fun _ => 1) := by
  have hz : reduceVector F n 0 = 0 := by ext i; simp [reduceVector]
  have hv : integralVector F n 0 = 0 := rfl
  rw [← hz, latticeDelta_reduceVector_eq_indicator, latticeCoset, hv]
  simp

variable [MeasurableSpace (Fin n → F)] [BorelSpace (Fin n → F)]
  (ψ : AddChar F ℂˣ) (hψ : HasConductorFour (Integers F).toSubring ψ)

local notation "μ" => latticeFourierHaar F n
local notation "𝓕" => localFourierOperator F n ψ hψ μ

/-- Every dilated lattice test function has nonzero integral. -/
theorem integral_fourierTest_ne_zero (a : Fˣ) :
    (∫ x, (fourierTest F n a).val x ∂μ) ≠ 0 := by
  have he : (∫ x, (latticeDelta F n 0).val.val x ∂μ) = (latticeFourierScale F n : ℂ) := by
    rw [latticeDelta_zero_indicator, integral_indicator_const _
      (multipleLattice_isCompact F n 2).isClosed.measurableSet]
    simp [Measure.real, ENNReal.toReal_ofReal (latticeFourierScale_pos F n).le,
      Complex.real_smul]
  change (∫ x, (latticeDelta F n 0).val.val (a • x) ∂μ) ≠ 0
  rw [integral_unit_smul, he]
  apply mul_ne_zero
  · intro hz
    have hh := haarDilation_inv_mul F n a
    rw [hz, zero_mul] at hh
    exact zero_ne_one hh
  · exact Complex.ofReal_ne_zero.mpr (latticeFourierScale_pos F n).ne'

/-- Inversion already holds on every arbitrarily small lattice test function. -/
theorem localFourierOperator_sq_fourierTest (a : Fˣ) :
    𝓕 (𝓕 (fourierTest F n a)) = fourierTest F n a := by
  unfold fourierTest
  rw [localFourierOperator_sq_dilate, localFourierOperator_sq_on_lattice]

/-- Global inversion at zero, obtained by testing against a small lattice delta. -/
theorem localFourierOperator_sq_zero (f : SchwartzBruhat (Fin n → F)) :
    (𝓕 (𝓕 f)).val 0 = f.val 0 := by
  let g := 𝓕 (𝓕 f)
  let U := {x | g.val x = g.val 0} ∩ {x | f.val x = f.val 0}
  have hU : IsOpen U := (g.val.isLocallyConstant.isOpen_fiber _).inter
    (f.val.isLocallyConstant.isOpen_fiber _)
  obtain ⟨a, ha⟩ := exists_fourierTest_support_subset F n hU ⟨rfl, rfl⟩
  let h := fourierTest F n a
  have havg (k : SchwartzBruhat (Fin n → F))
      (hk : ∀ x, h.val x ≠ 0 → k.val x = k.val 0) :
      (∫ x, k.val x * h.val x ∂μ) = k.val 0 * ∫ x, h.val x ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : h.val x = 0
    · simp [hx]
    · rw [hk x hx]
  have hg := havg g (fun x hx => (ha hx).1)
  have hf := havg f (fun x hx => (ha hx).2)
  have he : (∫ x, g.val x * h.val x ∂μ) = ∫ x, f.val x * h.val x ∂μ := by
    calc
      _ = ∫ x, (𝓕 f).val x * (𝓕 h).val x ∂μ :=
        localFourierOperator_bilinear F n ψ hψ μ (𝓕 f) h
      _ = ∫ x, f.val x * (𝓕 (𝓕 h)).val x ∂μ :=
        localFourierOperator_bilinear F n ψ hψ μ f (𝓕 h)
      _ = _ := by rw [localFourierOperator_sq_fourierTest]
  rw [hg, hf] at he
  exact mul_right_cancel₀ (integral_fourierTest_ne_zero F n a) he

/-- Fourier inversion for every local Schwartz–Bruhat function, at every point.
The same explicitly normalized Haar measure is used in both integrals. -/
theorem localFourierOperator_sq (f : SchwartzBruhat (Fin n → F)) (x : Fin n → F) :
    (𝓕 (𝓕 f)).val x = f.val (-x) := by
  have he := localFourierOperator_sq_zero F n ψ hψ (schwartzTranslate F n (-x) f)
  rw [localFourierOperator_sq_translate] at he
  simpa [schwartzTranslate] using he

/-- Reflection on the original local test-function space. -/
def schwartzReflect : SchwartzBruhat (Fin n → F) ≃ₗ[ℂ] SchwartzBruhat (Fin n → F) :=
  schwartzPullback (Homeomorph.neg _)

/-- The square identity as an equality in the original function space. -/
theorem localFourierOperator_sq_eq_reflect (f : SchwartzBruhat (Fin n → F)) :
    𝓕 (𝓕 f) = schwartzReflect F n f := by
  apply Subtype.ext
  apply LocallyConstant.ext
  exact localFourierOperator_sq F n ψ hψ f

/-- The inverse Fourier transform is reflection after the positive-sign transform. -/
def localFourierEquiv : SchwartzBruhat (Fin n → F) ≃ₗ[ℂ] SchwartzBruhat (Fin n → F) :=
  LinearEquiv.ofBijective 𝓕 (by
    constructor
    · intro f g h
      apply (schwartzReflect F n).injective
      rw [← localFourierOperator_sq_eq_reflect F n ψ hψ f,
        ← localFourierOperator_sq_eq_reflect F n ψ hψ g, h]
    · intro f
      refine ⟨𝓕 ((schwartzReflect F n).symm f), ?_⟩
      rw [localFourierOperator_sq_eq_reflect, LinearEquiv.apply_symm_apply])

@[simp]
theorem localFourierEquiv_apply (f : SchwartzBruhat (Fin n → F)) :
    localFourierEquiv F n ψ hψ f = 𝓕 f := rfl

/-- Pointwise formula for the inverse of the Fourier equivalence. -/
theorem localFourierEquiv_symm_apply (f : SchwartzBruhat (Fin n → F)) (x : Fin n → F) :
    ((localFourierEquiv F n ψ hψ).symm f).val x = (𝓕 f).val (-x) := by
  have he := localFourierOperator_sq F n ψ hψ ((localFourierEquiv F n ψ hψ).symm f) (-x)
  have hf : 𝓕 ((localFourierEquiv F n ψ hψ).symm f) = f :=
    (localFourierEquiv F n ψ hψ).apply_symm_apply f
  rw [hf, neg_neg] at he
  exact he.symm

end
end Char2Theta.Dyadic

/-! ## Unitary characters and Plancherel on the local Schwartz–Bruhat space -/

namespace Char2Theta.Dyadic
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators

variable (F : Type*) [NormedField F] [NormedAlgebra ℚ_[2] F]
  [FiniteDimensional ℚ_[2] F]
  (ψ : AddChar F ℂˣ) (hψ : HasConductorFour (Integers F).toSubring ψ)

include hψ in
/-- A smooth dyadic additive character takes values on the unit circle.
Multiplication by a sufficiently large power of two puts any argument in its open kernel. -/
theorem norm_character_of_hasConductorFour (x : F) : ‖(ψ x : ℂ)‖ = 1 := by
  have htwo : ‖(2 : F)‖ < 1 := by
    have he := norm_algebraMap' F (2 : ℚ_[2])
    rw [map_ofNat] at he
    rw [he]
    exact Padic.norm_natCast_lt_one_iff.mpr (dvd_refl 2)
  have ht : Tendsto (fun m : ℕ => (2 : F) ^ m * x) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one htwo).mul_const x
  obtain ⟨m, hm⟩ := (ht.eventually
    ((smoothCharacter_of_hasConductorFour F ψ hψ).eventually_eq 0)).exists
  have hp' : ψ x ^ (2 ^ m) = 1 := by
    rw [← ψ.map_nsmul_eq_pow]
    simpa [nsmul_eq_mul, Nat.cast_pow] using hm
  have hp : (ψ x : ℂ) ^ (2 ^ m) = 1 :=
    congrArg (fun c : ℂˣ => (c : ℂ)) hp'
  exact Complex.norm_eq_one_of_pow_eq_one hp (pow_ne_zero _ (by decide))

variable (n : ℕ)

/-- Conjugating the kernel reverses its frequency. -/
theorem localFourierKernel_conj (x y : Fin n → F) :
    (starRingEnd ℂ) (localFourierKernel F n ψ hψ y x) =
      localFourierKernel F n ψ hψ (-y) x := by
  simp only [localFourierKernel_apply, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  rw [ψ.map_neg_eq_inv, Units.val_inv_eq_inv_val]
  exact (Complex.inv_eq_conj (norm_character_of_hasConductorFour F ψ hψ _)).symm

/-- Complex conjugation preserves local constancy and compact support. -/
def schwartzConjugate (f : SchwartzBruhat (Fin n → F)) : SchwartzBruhat (Fin n → F) :=
  ⟨f.val.map (starRingEnd ℂ), f.property.comp_left (map_zero (starRingEnd ℂ))⟩

variable [MeasurableSpace (Fin n → F)] [BorelSpace (Fin n → F)]

/-- Conjugation of the Fourier integral, including the sign change. -/
theorem localFourierOperator_conjugate (μ : Measure (Fin n → F)) [μ.IsAddHaarMeasure]
    (f : SchwartzBruhat (Fin n → F)) (x : Fin n → F) :
    (localFourierOperator F n ψ hψ μ (schwartzConjugate F n f)).val x =
      (starRingEnd ℂ) ((localFourierOperator F n ψ hψ μ f).val (-x)) := by
  change (∫ y, localFourierKernel F n ψ hψ x y * (starRingEnd ℂ) (f.val y) ∂μ) =
    (starRingEnd ℂ) (∫ y, localFourierKernel F n ψ hψ (-x) y * f.val y ∂μ)
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [map_mul, localFourierKernel_conj, neg_neg]

local notation "μ" => latticeFourierHaar F n
local notation "𝓕" => localFourierOperator F n ψ hψ μ

/-- Parseval's identity for any two local Schwartz–Bruhat functions. -/
theorem localFourierOperator_parseval (f g : SchwartzBruhat (Fin n → F)) :
    (∫ x, (starRingEnd ℂ) ((𝓕 f).val x) * (𝓕 g).val x ∂μ) =
      ∫ x, (starRingEnd ℂ) (f.val x) * g.val x ∂μ := by
  have he := localFourierOperator_bilinear F n ψ hψ μ g
    (schwartzConjugate F n (𝓕 f))
  have hc (x : Fin n → F) :
      (𝓕 (schwartzConjugate F n (𝓕 f))).val x = (starRingEnd ℂ) (f.val x) := by
    rw [localFourierOperator_conjugate, localFourierOperator_sq, neg_neg]
  simp_rw [hc] at he
  simpa only [schwartzConjugate, LocallyConstant.map_apply, Function.comp_apply, mul_comm] using he

omit [NormedAlgebra ℚ_[2] F] [FiniteDimensional ℚ_[2] F] in
/-- The squared norm of a test function is integrable, so the norm identity
below concerns genuine finite integrals. -/
theorem schwartz_norm_sq_integrable (ν : Measure (Fin n → F)) [IsFiniteMeasureOnCompacts ν]
    (f : SchwartzBruhat (Fin n → F)) : Integrable (fun x => ‖f.val x‖ ^ 2) ν := by
  have hc : Continuous (fun x : Fin n → F => ‖f.val x‖ ^ 2) := f.val.continuous.norm.pow 2
  have hs : HasCompactSupport (fun x : Fin n → F => ‖f.val x‖ ^ 2) := by
    apply HasCompactSupport.of_support_subset_isCompact f.property
    intro x hx
    apply subset_tsupport f.val
    intro h
    exact hx (by simp [h])
  exact hc.integrable_of_hasCompactSupport hs

/-- Plancherel's identity on the entire local Schwartz–Bruhat space, using
exactly the same normalized Haar measure on both sides. -/
theorem localFourierOperator_plancherel (f : SchwartzBruhat (Fin n → F)) :
    (∫ x, ‖(𝓕 f).val x‖ ^ 2 ∂μ) = ∫ x, ‖f.val x‖ ^ 2 ∂μ := by
  apply Complex.ofReal_injective
  simpa only [Complex.conj_mul', ← Complex.ofReal_pow, integral_complex_ofReal] using
    localFourierOperator_parseval F ψ hψ n f f

end
end Char2Theta.Dyadic

/-! ## The self-dual Haar normalization is uniquely determined by Fourier inversion -/

namespace Char2Theta.Dyadic
noncomputable section
open MeasureTheory

variable (F : Type*) [NormedField F] [NormedAlgebra ℚ_[2] F]
  [FiniteDimensional ℚ_[2] F] (n : ℕ)
  [MeasurableSpace (Fin n → F)] [BorelSpace (Fin n → F)]
  (ψ : AddChar F ℂˣ) (hψ : HasConductorFour (Integers F).toSubring ψ)

/-- Self-duality for the fixed positive kernel means inversion with the same
Haar measure in the two Fourier integrals, on all local test functions. -/
def IsSelfDualFourierMeasure (μ : Measure (Fin n → F)) [μ.IsAddHaarMeasure] : Prop :=
  ∀ (f : SchwartzBruhat (Fin n → F)) (x : Fin n → F),
    (localFourierOperator F n ψ hψ μ (localFourierOperator F n ψ hψ μ f)).val x = f.val (-x)

/-- The previously selected volume normalization is self-dual. -/
theorem latticeFourierHaar_isSelfDual :
    IsSelfDualFourierMeasure F n ψ hψ (latticeFourierHaar F n) :=
  localFourierOperator_sq F n ψ hψ

/-- Changing Haar measure multiplies Fourier by mathlib's positive Haar factor. -/
theorem localFourierOperator_eq_haarScalarFactor_smul
    (μ : Measure (Fin n → F)) [μ.IsAddHaarMeasure] (f : SchwartzBruhat (Fin n → F)) :
    localFourierOperator F n ψ hψ μ f =
      ((Measure.addHaarScalarFactor μ (latticeFourierHaar F n) : ℝ) : ℂ) •
        localFourierOperator F n ψ hψ (latticeFourierHaar F n) f := by
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  change (∫ y, localFourierKernel F n ψ hψ x y * f.val y ∂μ) = _
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul μ (latticeFourierHaar F n),
    integral_smul_nnreal_measure]
  rfl

/-- Self-duality uniquely determines the Haar measure, not just its scale up to sign. -/
theorem selfDualFourierMeasure_unique (μ : Measure (Fin n → F)) [μ.IsAddHaarMeasure]
    (hμ : IsSelfDualFourierMeasure F n ψ hψ μ) : μ = latticeFourierHaar F n := by
  let c := Measure.addHaarScalarFactor μ (latticeFourierHaar F n)
  let δ := (latticeDelta F n 0).val
  have hδ : δ.val 0 = 1 := by
    change (latticeDelta F n 0).val.val 0 = 1
    rw [latticeDelta_zero_indicator]
    apply Set.indicator_of_mem
    exact fun _ => ⟨0, by simp⟩
  have he := hμ δ 0
  rw [localFourierOperator_eq_haarScalarFactor_smul,
    localFourierOperator_eq_haarScalarFactor_smul F n ψ hψ μ δ,
    map_smul, smul_smul] at he
  change (c : ℂ) * (c : ℂ) *
    (localFourierOperator F n ψ hψ (latticeFourierHaar F n)
      (localFourierOperator F n ψ hψ (latticeFourierHaar F n) δ)).val 0 = δ.val (-0) at he
  rw [localFourierOperator_sq, neg_zero, hδ, mul_one] at he
  have hc : (c : ℝ) * (c : ℝ) = 1 := by exact_mod_cast he
  have hc1 : c = 1 := by
    apply NNReal.coe_injective
    change (c : ℝ) = 1
    nlinarith [c.coe_nonneg]
  rw [Measure.isAddLeftInvariant_eq_smul μ (latticeFourierHaar F n)]
  change c • latticeFourierHaar F n = latticeFourierHaar F n
  rw [hc1, one_smul]

/-- An intrinsic characterization of the chosen normalization. -/
theorem isSelfDualFourierMeasure_iff (μ : Measure (Fin n → F)) [μ.IsAddHaarMeasure] :
    IsSelfDualFourierMeasure F n ψ hψ μ ↔ μ = latticeFourierHaar F n := by
  constructor
  · exact selfDualFourierMeasure_unique F n ψ hψ μ
  · intro h
    subst μ
    exact latticeFourierHaar_isSelfDual F n ψ hψ

end
end Char2Theta.Dyadic
