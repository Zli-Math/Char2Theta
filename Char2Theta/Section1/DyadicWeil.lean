import Char2Theta.Section1.DyadicFourier
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Separation.Profinite
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
import Mathlib.Topology.MetricSpace.Ultra.Pi
import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# 完整 L² 酉算子、Gaussian 积分与 Weil 关系（§1.3）

本文件承接 `DyadicFourier` 的自对偶测度与测试函数 Fourier。先证明测试函数
在实际 `L²(Fⁿ,μ)` 中稠密，构造 Fourier 的唯一酉延拓，再构造二次相位、
归一化线性换元及下相位，证明代表元公式、复合律和 Fourier 协变。

随后对非退化二次型 `Q`，以 `Q(x+y)=Q(x)+Q(y)+2x·By` 记录极化映射，
定义 `Q∨=Q∘B⁻¹`。紧开球上的 Gaussian 积分最终恒定，其值 `C(Q)` 经
`γ(Q)=√δ(B)C(Q)` 归一化后模长为 1。主要关系为
`F M_Q F = γ(Q) M_(-Q∨) D_(B⁻¹) F⁻¹ M_(-Q∨)`；标准型 `q=∑xᵢ²`
满足 `(F M_q)³=γ(q)·Id`，并有 `F⁴=Id`，均给出实际酉群中的等式。

主要入口：`localFourierL2`、`quadraticPhaseL2`、`linearChangeL2`、
`gaussianTruncation_stabilizes`、`localWeilIndex`、`localFourierL2Unitary_quadratic_bruhat`。
秩一归一化指数另取 `γ(ax²)/γ(x²)`。一般 L² 元素由连续延拓定义，Gaussian
通过紧域积分定义；未声称相应全空间积分逐点绝对收敛。单位根阶数、Hilbert
符号公式、规范提升的识别及完整 metaplectic 表示仍待完成。
-/

set_option autoImplicit false

/-!
## Dense embedding of local test functions in L²

Regularity approximates finite-measure sets by compact sets inside open sets.
Compact open intermediates then give Schwartz–Bruhat indicator approximations.
This uses the existing function space, without replacing L² by its test-function closure.
-/

namespace Char2Theta.Dyadic
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- A locally compact totally disconnected space has a basis of compact open sets. -/
theorem schwartz_prespectral [LocallyCompactSpace X] [TotallyDisconnectedSpace X] :
    PrespectralSpace X := by
  constructor
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (fun U hU => hU.1)
  intro x U hx hU
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset hU hx
  obtain ⟨V, hV, hxV, hVK⟩ :=
    loc_compact_Haus_tot_disc_of_zero_dim.exists_subset_of_mem_open hxK isOpen_interior
  exact ⟨V, ⟨hV.2, hK.of_isClosed_subset hV.1 (hVK.trans interior_subset)⟩,
    hxV, hVK.trans (interior_subset.trans hKU)⟩

variable [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasureOnCompacts ν]

/-- Every local test function defines an actual L² equivalence class. -/
theorem schwartz_memLp_two (f : SchwartzBruhat X) : MemLp f.val 2 ν :=
  f.val.continuous.memLp_of_hasCompactSupport f.property

/-- The canonical complex-linear map from the original test functions to L². -/
def schwartzToL2 : SchwartzBruhat X →ₗ[ℂ] Lp ℂ 2 ν where
  toFun f := (schwartz_memLp_two ν f).toLp f.val
  map_add' f g := by
    exact MemLp.toLp_add (schwartz_memLp_two ν f) (schwartz_memLp_two ν g)
  map_smul' c f := rfl

/-- The L² class has the original test function as an almost-everywhere representative. -/
theorem schwartzToL2_coeFn (f : SchwartzBruhat X) :
    (schwartzToL2 ν f : X → ℂ) =ᵐ[ν] f.val :=
  (schwartz_memLp_two ν f).coeFn_toLp

/-- For measures positive on nonempty opens, passing to L² loses no test functions. -/
theorem schwartzToL2_injective [ν.IsOpenPosMeasure] :
    Function.Injective (schwartzToL2 (X := X) ν) := by
  intro f g h
  apply Subtype.ext
  apply LocallyConstant.ext
  have hae : (f.val : X → ℂ) =ᵐ[ν] g.val :=
    (schwartzToL2_coeFn ν f).symm.trans (h ▸ schwartzToL2_coeFn ν g)
  exact congrFun (Measure.eq_of_ae_eq hae f.val.continuous g.val.continuous)

/-- The L² inner product agrees with the original Hermitian integral. -/
theorem schwartzToL2_inner (f g : SchwartzBruhat X) :
    inner ℂ (schwartzToL2 ν f) (schwartzToL2 ν g) =
      ∫ x, (starRingEnd ℂ) (f.val x) * g.val x ∂ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [schwartzToL2_coeFn ν f, schwartzToL2_coeFn ν g] with x hf hg
  rw [hf, hg]
  change g.val x * (starRingEnd ℂ) (f.val x) = _
  exact mul_comm _ _

variable [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
  [ν.OuterRegular] [ν.InnerRegularCompactLTTop]

/-- Compactly supported locally constant functions approximate every L² function. -/
theorem exists_schwartz_eLpNorm_sub_le {f : X → ℂ} (hf : MemLp f 2 ν)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : SchwartzBruhat X, eLpNorm (f - (g.val : X → ℂ)) 2 ν ≤ ε := by
  letI : PrespectralSpace X := schwartz_prespectral
  have ha : ∃ g : X → ℂ, eLpNorm (f - g) 2 ν ≤ ε ∧
      IsLocallyConstant g ∧ HasCompactSupport g := by
    apply hf.induction_dense (by norm_num) _ _ _ _ hε
    · intro c t ht htν ε hε
      obtain ⟨δ, hδ, hadd⟩ := exists_Lp_half ℂ ν 2 hε
      obtain ⟨η, hη, hsmall⟩ := exists_eLpNorm_indicator_le (μ := ν) (p := 2)
        (by norm_num) c hδ.ne'
      have hη' : (η : ℝ≥0∞) ≠ 0 := (ENNReal.coe_pos.mpr hη).ne'
      obtain ⟨K, hKt, hK, hdiff⟩ := ht.exists_isCompact_sdiff_lt htν.ne hη'
      have hKν : ν K ≠ ∞ := ne_top_of_le_ne_top htν.ne (measure_mono hKt)
      obtain ⟨U, hKU, hU, _, hUK⟩ := hK.isClosed.measurableSet.exists_isOpen_sdiff_lt hKν hη'
      obtain ⟨V, hV, hVo, hKV, hVU⟩ :=
        PrespectralSpace.exists_isCompact_and_isOpen_between hK hU hKU
      let g : LocallyConstant X ℂ := (LocallyConstant.const X c).indicator ⟨hV.isClosed, hVo⟩
      have hg : HasCompactSupport (g : X → ℂ) :=
        HasCompactSupport.of_support_subset_isCompact hV Set.support_indicator_subset
      have hmem : MemLp g 2 ν := g.continuous.memLp_of_hasCompactSupport hg
      have h1 : eLpNorm ((K.indicator fun _ => c) - t.indicator (fun _ => c)) 2 ν ≤ δ := by
        rw [← eLpNorm_neg, neg_sub, ← indicator_sdiff hKt]
        exact hsmall _ hdiff.le
      have h2 : eLpNorm ((g : X → ℂ) - K.indicator (fun _ => c)) 2 ν ≤ δ := by
        change eLpNorm ((V.indicator fun _ => c) - K.indicator (fun _ => c)) 2 ν ≤ δ
        rw [← indicator_sdiff hKV]
        exact hsmall _ ((measure_mono (sdiff_subset_sdiff_left hVU)).trans hUK.le)
      refine ⟨g, ?_, g.isLocallyConstant, hg⟩
      simpa only [sub_add_sub_cancel] using (hadd _ _
        (hmem.aestronglyMeasurable.sub (aestronglyMeasurable_const.indicator hK.isClosed.measurableSet))
        ((aestronglyMeasurable_const.indicator hK.isClosed.measurableSet).sub
          (aestronglyMeasurable_const.indicator ht)) h2 h1).le
    · intro f g hf hg
      exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩
    · intro f hf
      exact hf.1.continuous.aestronglyMeasurable
  obtain ⟨g, hg, hloc, hcomp⟩ := ha
  exact ⟨⟨⟨g, hloc⟩, hcomp⟩, hg⟩

/-- Density is in the full mathlib L² space, for the given regular measure. -/
theorem schwartzToL2_denseRange : DenseRange (schwartzToL2 (X := X) ν) := by
  rw [Metric.denseRange_iff]
  intro f ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨g, hg⟩ := exists_schwartz_eLpNorm_sub_le ν (Lp.memLp f)
    (ENNReal.ofReal_ne_zero_iff.mpr hhalf)
  refine ⟨g, ?_⟩
  rw [dist_edist]
  have he : edist f (schwartzToL2 ν g) = eLpNorm ((f : X → ℂ) - (g.val : X → ℂ)) 2 ν := by
    simpa only [schwartzToL2, LinearMap.coe_mk, AddHom.coe_mk, Lp.toLp_coeFn] using
      Lp.edist_toLp_toLp (f : X → ℂ) (g.val : X → ℂ) (Lp.memLp f) (schwartz_memLp_two ν g)
  rw [he]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hg).trans_lt
    (by rw [ENNReal.toReal_ofReal hhalf.le]; linarith)

end
end Char2Theta.Dyadic

/-!
## Unitary Fourier transform on the full L² space

The same self-dual Haar measure is used in the source and target. Density and
Parseval allow mathlib's `LinearEquiv.extendOfIsometry` to extend the already
bijective test-function transform. Compatibility is equality of L² classes,
and hence an almost-everywhere equality of representatives.
-/

namespace Char2Theta.Dyadic
noncomputable section
open MeasureTheory

variable (F : Type*) [NormedField F] [NormedAlgebra ℚ_[2] F]
  [FiniteDimensional ℚ_[2] F] (n : ℕ)
  [MeasurableSpace (Fin n → F)] [BorelSpace (Fin n → F)]
  (ψ : AddChar F ℂˣ) (hψ : HasConductorFour (Integers F).toSubring ψ)

local notation "μ" => latticeFourierHaar F n

/-- The Hilbert space is mathlib's full L² space for the fixed self-dual Haar measure. -/
abbrev LocalL2 := Lp ℂ 2 μ

/-- Parseval supplies exactly the norm condition required for dense extension. -/
theorem schwartz_fourier_L2_norm (f : SchwartzBruhat (Fin n → F)) :
    ‖schwartzToL2 μ (localFourierEquiv F n ψ hψ f)‖ = ‖schwartzToL2 μ f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
    InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
    schwartzToL2_inner, schwartzToL2_inner, localFourierEquiv_apply,
    localFourierOperator_parseval]

/-- The unique extension of the local Fourier transform to a surjective complex-linear
isometry of the full L² space. No density or surjectivity hypothesis is added. -/
def localFourierL2 : LocalL2 F n ≃ₗᵢ[ℂ] LocalL2 F n :=
  (localFourierEquiv F n ψ hψ).extendOfIsometry
    (schwartzToL2 μ) (schwartzToL2 μ)
    (schwartzToL2_denseRange μ) (schwartzToL2_denseRange μ)
    (schwartz_fourier_L2_norm F n ψ hψ)

/-- Compatibility with the original Fourier operator on every test function. -/
@[simp]
theorem localFourierL2_apply_test (f : SchwartzBruhat (Fin n → F)) :
    localFourierL2 F n ψ hψ (schwartzToL2 μ f) =
      schwartzToL2 μ (localFourierOperator F n ψ hψ μ f) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ f

/-- The L² extension has the original Fourier integral as its a.e. representative
when the input is a Schwartz–Bruhat function. -/
theorem localFourierL2_coeFn_test (f : SchwartzBruhat (Fin n → F)) :
    (localFourierL2 F n ψ hψ (schwartzToL2 μ f) : (Fin n → F) → ℂ) =ᵐ[μ]
      fun y => ∫ x, localFourierKernel F n ψ hψ y x * f.val x ∂μ := by
  rw [localFourierL2_apply_test]
  exact schwartzToL2_coeFn μ _

/-- The inverse L² operator also extends the already proved inverse on test functions. -/
@[simp]
theorem localFourierL2_symm_apply_test (f : SchwartzBruhat (Fin n → F)) :
    (localFourierL2 F n ψ hψ).symm (schwartzToL2 μ f) =
      schwartzToL2 μ ((localFourierEquiv F n ψ hψ).symm f) :=
  LinearEquiv.extendOfIsometry_symm_eq _ _ _ _ _ _ f

/-- Plancherel as norm preservation for all L² classes. -/
theorem localFourierL2_norm (f : LocalL2 F n) :
    ‖localFourierL2 F n ψ hψ f‖ = ‖f‖ :=
  (localFourierL2 F n ψ hψ).norm_map f

/-- Parseval for arbitrary elements of the full Hilbert space. -/
theorem localFourierL2_inner (f g : LocalL2 F n) :
    inner ℂ (localFourierL2 F n ψ hψ f) (localFourierL2 F n ψ hψ g) = inner ℂ f g :=
  (localFourierL2 F n ψ hψ).inner_map_map f g

/-- Surjectivity is part of the constructed equivalence, not merely dense range. -/
theorem localFourierL2_surjective : Function.Surjective (localFourierL2 F n ψ hψ) :=
  (localFourierL2 F n ψ hψ).surjective

/-- The same operator packaged in mathlib's unitary group of bounded operators. -/
def localFourierL2Unitary : unitary (LocalL2 F n →L[ℂ] LocalL2 F n) :=
  Unitary.linearIsometryEquiv.symm (localFourierL2 F n ψ hψ)

@[simp]
theorem localFourierL2Unitary_apply (f : LocalL2 F n) :
    (localFourierL2Unitary F n ψ hψ : LocalL2 F n →L[ℂ] LocalL2 F n) f =
      localFourierL2 F n ψ hψ f := rfl

/-- A continuous linear extension compatible with the original transform is unique. -/
theorem localFourierL2_unique (T : LocalL2 F n →L[ℂ] LocalL2 F n)
    (hT : ∀ f : SchwartzBruhat (Fin n → F),
      T (schwartzToL2 μ f) = schwartzToL2 μ (localFourierOperator F n ψ hψ μ f)) :
    T = (localFourierL2 F n ψ hψ : LocalL2 F n →L[ℂ] LocalL2 F n) := by
  apply ContinuousLinearMap.ext
  exact (schwartzToL2_denseRange μ).induction
    (by rintro _ ⟨f, rfl⟩
        exact (hT f).trans (localFourierL2_apply_test F n ψ hψ f).symm)
    (isClosed_eq T.continuous (localFourierL2 F n ψ hψ).continuous)

/-- The Hilbert adjoint is the inverse transform on the entire L² space. -/
theorem localFourierL2_adjoint :
    ContinuousLinearMap.adjoint
      (localFourierL2 F n ψ hψ : LocalL2 F n →L[ℂ] LocalL2 F n) =
      ((localFourierL2 F n ψ hψ).symm : LocalL2 F n →L[ℂ] LocalL2 F n) :=
  (localFourierL2 F n ψ hψ).adjoint_eq_symm

/-- Fourier transforms of test-function approximations converge to the L² transform. -/
theorem localFourierL2_tendsto {ι : Type*} {l : Filter ι}
    {f : ι → SchwartzBruhat (Fin n → F)} {u : LocalL2 F n}
    (hf : Filter.Tendsto (fun i => schwartzToL2 μ (f i)) l (nhds u)) :
    Filter.Tendsto (fun i => schwartzToL2 μ (localFourierOperator F n ψ hψ μ (f i)))
      l (nhds (localFourierL2 F n ψ hψ u)) := by
  simpa only [Function.comp_def, localFourierL2_apply_test] using
    ((localFourierL2 F n ψ hψ).continuous.tendsto u).comp hf

end
end Char2Theta.Dyadic

/-!
## Basic unitary operators on the full L² space

The convention is `M_Q f(x) = ψ(Q(x)) f(x)` and
`D_e f(x) = √δ(e) f(e x)`, where mathlib's additive Haar character is
characterized by `δ(e) • map e μ = μ`. Thus `δ(e)` is the image-volume
factor, not the reciprocal pushforward factor. Both operators are defined on
all L² classes; their representative formulas hold almost everywhere.

The transpose uses the bilinear coordinate pairing `x·y`. With the existing
positive-sign Fourier kernel, `F D_e = D_(e⁻ᵀ) F`. The lower phase is defined
explicitly as `F⁻¹ M_Q F`; no metaplectic lift or Weil scalar is asserted here.
-/

namespace Char2Theta.Dyadic
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal ENNReal
variable (F : Type*) [NormedField F] [NormedAlgebra ℚ_[2] F]
  [FiniteDimensional ℚ_[2] F] (n : ℕ)

/-- Every quadratic form in finitely many local coordinates is continuous. -/
theorem quadraticForm_continuous (Q : QuadraticForm F (Fin n → F)) : Continuous Q := by
  letI : Invertible (2 : F) := invertibleOfNonzero (by norm_num)
  letI : NontriviallyNormedField F := NontriviallyNormedField.ofNormNeOne
    ⟨2, by norm_num, by
      have h := norm_algebraMap' F (2 : ℚ_[2])
      rw [map_ofNat] at h
      rw [h]
      exact (Padic.norm_natCast_lt_one_iff.mpr (dvd_refl 2)).ne⟩
  let B := Q.associated
  let C : (Fin n → F) →L[F] (Fin n → F) →L[F] F :=
    LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap.comp B)
  have h : (fun x => C x x) = Q := by
    funext x
    exact Q.associated_eq_self_apply F x
  rw [← h]
  exact C.continuous.clm_apply continuous_id

/-- Coordinate duality for the bilinear dot product (no complex conjugation). -/
def coordinateDual : (Fin n → F) ≃ₗ[F] Module.Dual F (Fin n → F) :=
  (Pi.basisFun F (Fin n)).toDualEquiv

omit [NormedAlgebra ℚ_[2] F] [FiniteDimensional ℚ_[2] F] in
@[simp] theorem coordinateDual_apply (x y : Fin n → F) :
    coordinateDual F n x y = ∑ i, x i * y i := by
  let b := Pi.basisFun F (Fin n)
  have h := b.sum_repr y
  conv_lhs => rw [← h]
  change b.toDual x (∑ i, (b.repr y) i • b i) = _
  simp only [map_sum, map_smul, b.toDual_apply_left]
  simp [b, mul_comm]

/-- Transpose with respect to `x·y`, constructed from mathlib's dual equivalence. -/
def linearTranspose (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    (Fin n → F) ≃ₗ[F] (Fin n → F) :=
  ((coordinateDual F n).trans e.dualMap).trans (coordinateDual F n).symm

omit [NormedAlgebra ℚ_[2] F] [FiniteDimensional ℚ_[2] F] in
theorem dot_linearTranspose (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) (x y : Fin n → F) :
    (∑ i, x i * linearTranspose F n e y i) = ∑ i, e x i * y i := by
  have h : coordinateDual F n (linearTranspose F n e y) x = coordinateDual F n y (e x) := by
    simp [linearTranspose, LinearEquiv.dualMap_apply]
  simpa only [coordinateDual_apply, mul_comm] using h

omit [NormedAlgebra ℚ_[2] F] [FiniteDimensional ℚ_[2] F] in
@[simp] theorem linearTranspose_symm (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    linearTranspose F n e.symm = (linearTranspose F n e).symm := by
  ext y : 1
  apply (coordinateDual F n).injective
  simp [linearTranspose, LinearEquiv.dualMap_symm]

variable [MeasurableSpace (Fin n → F)] [BorelSpace (Fin n → F)]
local notation "μ" => latticeFourierHaar F n

/-- Equality on local test functions determines a continuous map on the full L² space. -/
theorem localL2_ext {T S : LocalL2 F n → LocalL2 F n}
    (hT : Continuous T) (hS : Continuous S)
    (h : ∀ f : SchwartzBruhat (Fin n → F), T (schwartzToL2 μ f) = S (schwartzToL2 μ f)) :
    T = S := by
  funext u
  exact (schwartzToL2_denseRange μ).induction
    (by rintro _ ⟨f, rfl⟩; exact h f) (isClosed_eq hT hS) u

/-! ### Normalized linear changes and their full L² representative formula -/

/-- A local linear equivalence is automatically a homeomorphism. -/
def linearHomeomorph (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    (Fin n → F) ≃ₜ (Fin n → F) :=
  (e.restrictScalars ℚ_[2]).toContinuousLinearEquiv.toHomeomorph

/-- Haar modulus: `δ(e) • map e μ = μ`, independent of the Haar normalization. -/
def linearHaarModulus (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) : ℝ≥0 :=
  addEquivAddHaarChar (e.restrictScalars ℚ_[2]).toContinuousLinearEquiv.toContinuousAddEquiv

theorem linearHaarModulus_pos (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    0 < linearHaarModulus F n e := addEquivAddHaarChar_pos _

theorem linearHaarModulus_smul_map (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    linearHaarModulus F n e • Measure.map e μ = μ :=
  addEquivAddHaarChar_smul_map μ _

@[simp] theorem linearHaarModulus_refl :
    linearHaarModulus F n (LinearEquiv.refl F _) = 1 :=
  addEquivAddHaarChar_refl

@[simp] theorem linearHaarModulus_symm (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    linearHaarModulus F n e.symm = (linearHaarModulus F n e)⁻¹ :=
  by
    unfold linearHaarModulus
    rw [show (e.symm.restrictScalars ℚ_[2]).toContinuousLinearEquiv.toContinuousAddEquiv =
      (e.restrictScalars ℚ_[2]).toContinuousLinearEquiv.toContinuousAddEquiv.symm by ext x; rfl]
    exact addEquivAddHaarChar_symm

theorem linearHaarModulus_trans (e a : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    linearHaarModulus F n (e.trans a) = linearHaarModulus F n e * linearHaarModulus F n a :=
  by
    unfold linearHaarModulus
    rw [show ((e.trans a).restrictScalars ℚ_[2]).toContinuousLinearEquiv.toContinuousAddEquiv =
      ((e.restrictScalars ℚ_[2]).toContinuousLinearEquiv.toContinuousAddEquiv).trans
      ((a.restrictScalars ℚ_[2]).toContinuousLinearEquiv.toContinuousAddEquiv) by ext x; rfl]
    exact addEquivAddHaarChar_trans

/-- Positive square root of the Haar modulus, for the convention `f(x) ↦ f(e x)`. -/
def linearChangeScale (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) : ℝ :=
  Real.sqrt (linearHaarModulus F n e : ℝ)

theorem linearChangeScale_pos (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    0 < linearChangeScale F n e := Real.sqrt_pos.mpr (linearHaarModulus_pos F n e)

theorem linearChangeScale_sq (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    linearChangeScale F n e ^ 2 = (linearHaarModulus F n e : ℝ) := Real.sq_sqrt (by positivity)

@[simp] theorem linearChangeScale_symm (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    linearChangeScale F n e.symm = (linearChangeScale F n e)⁻¹ := by
  simp [linearChangeScale, Real.sqrt_inv]

theorem linearChangeScale_trans (e a : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    linearChangeScale F n (e.trans a) = linearChangeScale F n e * linearChangeScale F n a := by
  simp [linearChangeScale, linearHaarModulus_trans, Real.sqrt_mul (NNReal.coe_nonneg _)]

/-- Change of variables, stated with the factor on the left to avoid reciprocal ambiguity. -/
theorem linearHaarModulus_integral (e : (Fin n → F) ≃ₗ[F] (Fin n → F))
    (g : (Fin n → F) → ℂ) :
    (linearHaarModulus F n e : ℂ) * (∫ x, g (e x) ∂μ) = ∫ x, g x ∂μ := by
  have h := congrArg (fun ν : Measure (Fin n → F) => ∫ x, g x ∂ν)
    (linearHaarModulus_smul_map F n e)
  rw [integral_smul_nnreal_measure] at h
  have hm : (∫ x, g x ∂Measure.map e μ) = ∫ x, g (e x) ∂μ :=
    (linearHomeomorph F n e).isClosedEmbedding.integral_map g
  rw [hm] at h
  exact h

/-- The normalized pullback on the original test-function space. -/
def linearChange (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    SchwartzBruhat (Fin n → F) ≃ₗ[ℂ] SchwartzBruhat (Fin n → F) :=
  (schwartzPullback (linearHomeomorph F n e)).trans
    (LinearEquiv.smulOfNeZero ℂ (SchwartzBruhat (Fin n → F)) (linearChangeScale F n e : ℂ)
      (Complex.ofReal_ne_zero.mpr (linearChangeScale_pos F n e).ne'))

@[simp] theorem linearChange_apply (e : (Fin n → F) ≃ₗ[F] (Fin n → F))
    (f : SchwartzBruhat (Fin n → F)) (x : Fin n → F) :
    (linearChange F n e f).val x = (linearChangeScale F n e : ℂ) * f.val (e x) := rfl

/-- The square-root factor exactly compensates the Haar Jacobian. -/
theorem linearChange_L2_norm (e : (Fin n → F) ≃ₗ[F] (Fin n → F))
    (f : SchwartzBruhat (Fin n → F)) :
    ‖schwartzToL2 μ (linearChange F n e f)‖ = ‖schwartzToL2 μ f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
    InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), schwartzToL2_inner, schwartzToL2_inner]
  congr 1
  calc
    _ = ∫ x, (linearHaarModulus F n e : ℂ) *
        ((starRingEnd ℂ) (f.val (e x)) * f.val (e x)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [linearChange_apply, map_mul, Complex.conj_ofReal]
      rw [← linearChangeScale_sq F n e, Complex.ofReal_pow]
      ring
    _ = _ := by
      rw [integral_const_mul]
      exact linearHaarModulus_integral F n e (fun x => (starRingEnd ℂ) (f.val x) * f.val x)

/-- Normalized linear changes on the complete Hilbert space, for every `e ∈ GL(Fⁿ)`. -/
def linearChangeL2 (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) : LocalL2 F n ≃ₗᵢ[ℂ] LocalL2 F n :=
  (linearChange F n e).extendOfIsometry
    (schwartzToL2 μ) (schwartzToL2 μ)
    (schwartzToL2_denseRange μ) (schwartzToL2_denseRange μ)
    (linearChange_L2_norm F n e)

@[simp] theorem linearChangeL2_apply_test (e : (Fin n → F) ≃ₗ[F] (Fin n → F))
    (f : SchwartzBruhat (Fin n → F)) :
    linearChangeL2 F n e (schwartzToL2 μ f) = schwartzToL2 μ (linearChange F n e f) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ f

/-- The pushforward measure, with its precise reciprocal Haar factor. -/
theorem linearHaarModulus_map (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    Measure.map e μ = (linearHaarModulus F n e)⁻¹ • μ := by
  have h := congrArg (fun ν : Measure (Fin n → F) => (linearHaarModulus F n e)⁻¹ • ν)
    (linearHaarModulus_smul_map F n e)
  simpa only [smul_smul, inv_mul_cancel₀ (linearHaarModulus_pos F n e).ne', one_smul] using h

/-- The normalized change is the actual weighted composition on every L² representative. -/
theorem linearChangeL2_coeFn (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) (u : LocalL2 F n) :
    (linearChangeL2 F n e u : (Fin n → F) → ℂ) =ᵐ[μ]
      fun x => (linearChangeScale F n e : ℂ) * u (e x) := by
  let c : ℝ≥0∞ := ((linearHaarModulus F n e)⁻¹ : ℝ≥0)
  have hc : c ≠ ⊤ := ENNReal.coe_ne_top
  have he : Measure.map e μ ≤ c • μ := le_of_eq (linearHaarModulus_map F n e)
  have hm : Measurable e := (linearHomeomorph F n e).continuous.measurable
  let R : LocalL2 F n →L[ℝ] Lp ℂ 2 (Measure.map e μ) := Lp.LpToLpOfMeasureLeSMul hc he
  let P : Lp ℂ 2 (Measure.map e μ) →ₗᵢ[ℝ] LocalL2 F n :=
    Lp.compMeasurePreservingₗᵢ ℝ e ⟨hm, rfl⟩
  let T : LocalL2 F n →L[ℝ] LocalL2 F n :=
    linearChangeScale F n e • (P.toContinuousLinearMap.comp R)
  have hT (v : LocalL2 F n) : (T v : (Fin n → F) → ℂ) =ᵐ[μ]
      fun x => (linearChangeScale F n e : ℂ) * v (e x) := by
    filter_upwards [Lp.coeFn_smul (linearChangeScale F n e) (P (R v)),
      Lp.coeFn_compMeasurePreserving (R v) (show MeasurePreserving e μ (Measure.map e μ) from ⟨hm, rfl⟩),
      ae_eq_comp hm.aemeasurable (Lp.coeFn_LpToLpOfMeasureLeSMul hc he v)] with x hx hp hr
    change (P (R v) : (Fin n → F) → ℂ) x = (R v) (e x) at hp
    change (R v) (e x) = v (e x) at hr
    exact hx.trans (by rw [Pi.smul_apply, hp, hr]; rfl)
  have heq : (linearChangeL2 F n e : LocalL2 F n → LocalL2 F n) = T := by
    apply localL2_ext F n (linearChangeL2 F n e).continuous T.continuous
    intro f
    rw [linearChangeL2_apply_test]
    apply Lp.ext
    have hac : Measure.map e μ ≪ μ := Measure.absolutelyContinuous_of_le_smul he
    filter_upwards [schwartzToL2_coeFn μ (linearChange F n e f), hT (schwartzToL2 μ f),
      ae_eq_comp hm.aemeasurable (hac.ae_eq (schwartzToL2_coeFn μ f))] with x hf ht hx
    change (schwartzToL2 μ f : (Fin n → F) → ℂ) (e x) = f.val (e x) at hx
    rw [hf, ht, hx]
    rfl
  rw [congrFun heq u]
  exact hT u

/-- Pullback reverses composition: `D_e D_a = D_(a ∘ e)`. -/
theorem linearChangeL2_trans (e a : (Fin n → F) ≃ₗ[F] (Fin n → F)) (u : LocalL2 F n) :
    linearChangeL2 F n (e.trans a) u = linearChangeL2 F n e (linearChangeL2 F n a u) := by
  exact congrFun (localL2_ext F n
    (T := fun u => linearChangeL2 F n (e.trans a) u)
    (S := fun u => linearChangeL2 F n e (linearChangeL2 F n a u))
    (by fun_prop) (by fun_prop) (fun f => by
    simp only [linearChangeL2_apply_test]
    congr 1
    apply Subtype.ext
    ext x
    simp [linearChange_apply, linearChangeScale_trans, mul_assoc])) u

@[simp] theorem linearChangeL2_refl (u : LocalL2 F n) :
    linearChangeL2 F n (LinearEquiv.refl F _) u = u := by
  apply Lp.ext
  filter_upwards [linearChangeL2_coeFn F n (LinearEquiv.refl F _) u] with x hx
  simpa [linearChangeScale] using hx

/-- Inverting the linear change gives the inverse unitary operator. -/
theorem linearChangeL2_symm (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    (linearChangeL2 F n e).symm = linearChangeL2 F n e.symm := by
  ext u : 1
  apply (linearChangeL2 F n e).injective
  rw [LinearIsometryEquiv.apply_symm_apply, ← linearChangeL2_trans]
  simp

/-- Normalized linear change as an actual unitary bounded operator. -/
def linearChangeL2Unitary (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    unitary (LocalL2 F n →L[ℂ] LocalL2 F n) :=
  Unitary.linearIsometryEquiv.symm (linearChangeL2 F n e)

theorem linearChangeL2_adjoint (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    ContinuousLinearMap.adjoint (linearChangeL2 F n e : LocalL2 F n →L[ℂ] LocalL2 F n) =
      (linearChangeL2 F n e.symm : LocalL2 F n →L[ℂ] LocalL2 F n) := by
  rw [(linearChangeL2 F n e).adjoint_eq_symm, linearChangeL2_symm]

/-! ### Quadratic phase multipliers -/

variable (ψ : AddChar F ℂˣ) (hψ : HasConductorFour (Integers F).toSubring ψ)

/-- The quadratic multiplier on the original Schwartz–Bruhat space. -/
def quadraticPhase (Q : QuadraticForm F (Fin n → F)) :=
  schwartzMultiplier (polynomialPhase F n ψ hψ Q (quadraticForm_continuous F n Q))

omit [MeasurableSpace (Fin n → F)] [BorelSpace (Fin n → F)] in
@[simp] theorem quadraticPhase_apply (Q : QuadraticForm F (Fin n → F))
    (f : SchwartzBruhat (Fin n → F)) (x : Fin n → F) :
    (quadraticPhase F n ψ hψ Q f).val x = (ψ (Q x) : ℂ) * f.val x := rfl

/-- Unit-modulus phases preserve the actual L² norm of a test function. -/
theorem quadraticPhase_L2_norm (Q : QuadraticForm F (Fin n → F))
    (f : SchwartzBruhat (Fin n → F)) :
    ‖schwartzToL2 μ (quadraticPhase F n ψ hψ Q f)‖ = ‖schwartzToL2 μ f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
    InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), schwartzToL2_inner, schwartzToL2_inner]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [quadraticPhase_apply, map_mul]
  have hm : (starRingEnd ℂ) (ψ (Q x) : ℂ) * (ψ (Q x) : ℂ) = 1 := by
    rw [Complex.conj_mul', norm_character_of_hasConductorFour F ψ hψ]
    norm_num
  calc
    _ = ((starRingEnd ℂ) (ψ (Q x) : ℂ) * (ψ (Q x) : ℂ)) *
        ((starRingEnd ℂ) (f.val x) * f.val x) := by ring
    _ = _ := by rw [hm, one_mul]

/-- Multiplication by `ψ(Q(x))`, extended to the full L² space as a unitary equivalence. -/
def quadraticPhaseL2 (Q : QuadraticForm F (Fin n → F)) : LocalL2 F n ≃ₗᵢ[ℂ] LocalL2 F n :=
  (quadraticPhase F n ψ hψ Q).extendOfIsometry
    (schwartzToL2 μ) (schwartzToL2 μ)
    (schwartzToL2_denseRange μ) (schwartzToL2_denseRange μ)
    (quadraticPhase_L2_norm F n ψ hψ Q)

@[simp] theorem quadraticPhaseL2_apply_test (Q : QuadraticForm F (Fin n → F))
    (f : SchwartzBruhat (Fin n → F)) :
    quadraticPhaseL2 F n ψ hψ Q (schwartzToL2 μ f) =
      schwartzToL2 μ (quadraticPhase F n ψ hψ Q f) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ f

/-! ### Fourier covariance and reciprocal transpose modulus -/

/-- Fourier changes a linear pullback into the inverse transpose pullback.
This preliminary identity keeps the positive normalization factors explicit. -/
theorem localFourier_linearChange_scaled (e : (Fin n → F) ≃ₗ[F] (Fin n → F))
    (f : SchwartzBruhat (Fin n → F)) :
    (linearChangeScale F n e : ℂ) • localFourierOperator F n ψ hψ μ (linearChange F n e f) =
      schwartzPullback (linearHomeomorph F n (linearTranspose F n e.symm))
        (localFourierOperator F n ψ hψ μ f) := by
  apply Subtype.ext
  apply LocallyConstant.ext
  intro y
  change (linearChangeScale F n e : ℂ) *
    (∫ x, localFourierKernel F n ψ hψ y x *
      ((linearChangeScale F n e : ℂ) * f.val (e x)) ∂μ) =
    ∫ x, localFourierKernel F n ψ hψ (linearTranspose F n e.symm y) x * f.val x ∂μ
  have hk (x : Fin n → F) : localFourierKernel F n ψ hψ y x =
      localFourierKernel F n ψ hψ (linearTranspose F n e.symm y) (e x) := by
    simp only [localFourierKernel_apply, dot_linearTranspose, e.symm_apply_apply]
  simp_rw [hk, mul_left_comm _ (linearChangeScale F n e : ℂ)]
  rw [integral_const_mul, ← mul_assoc, ← pow_two, ← Complex.ofReal_pow, linearChangeScale_sq]
  exact linearHaarModulus_integral F n e
    (fun x => localFourierKernel F n ψ hψ (linearTranspose F n e.symm y) x * f.val x)

/-- The zero-coset indicator supplies a nonzero L² class, including in dimension zero. -/
theorem schwartzToL2_delta_ne_zero :
    schwartzToL2 μ (latticeDelta F n 0).val ≠ 0 := by
  intro h
  have hf := (schwartzToL2_injective μ) (h.trans (map_zero (schwartzToL2 μ)).symm)
  have h0 := congrArg (fun f : SchwartzBruhat (Fin n → F) => f.val (integralVector F n 0)) hf
  have hz : reduceVector F n 0 = 0 := by ext i; exact map_zero (Ideal.Quotient.mk _)
  simp [latticeDelta_integralVector, hz] at h0

/-- Self-duality forces the inverse transpose to have reciprocal Haar modulus.
The proof uses the already proved Plancherel theorem, without assuming a determinant formula. -/
theorem linearChangeScale_mul_inverseTranspose
    (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    linearChangeScale F n e * linearChangeScale F n (linearTranspose F n e.symm) = 1 := by
  let ψ := conductorFourCharacter F
  have hψ := conductorFourCharacter_hasConductorFour F
  let f := (latticeDelta F n 0).val
  let t := linearTranspose F n e.symm
  have h : ((linearChangeScale F n t : ℂ) * (linearChangeScale F n e : ℂ)) •
      localFourierOperator F n ψ hψ μ (linearChange F n e f) =
      linearChange F n t (localFourierOperator F n ψ hψ μ f) := by
    rw [mul_smul, localFourier_linearChange_scaled]
    rfl
  have hn := congrArg (fun g => ‖schwartzToL2 μ g‖) h
  simp only [map_smul, norm_smul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (linearChangeScale_pos F n t).le,
    Real.norm_of_nonneg (linearChangeScale_pos F n e).le,
    linearChange_L2_norm] at hn
  change _ * ‖schwartzToL2 μ (localFourierEquiv F n ψ hψ (linearChange F n e f))‖ =
    ‖schwartzToL2 μ (localFourierEquiv F n ψ hψ f)‖ at hn
  rw [schwartz_fourier_L2_norm, schwartz_fourier_L2_norm, linearChange_L2_norm] at hn
  have hne : ‖schwartzToL2 μ f‖ ≠ 0 := norm_ne_zero_iff.mpr (schwartzToL2_delta_ne_zero F n)
  have he := (mul_right_cancel₀ hne) (hn.trans (one_mul _).symm)
  simpa only [mul_comm] using he

/-- Exact normalized covariance on all local test functions. -/
theorem localFourier_linearChange (e : (Fin n → F) ≃ₗ[F] (Fin n → F))
    (f : SchwartzBruhat (Fin n → F)) :
    localFourierOperator F n ψ hψ μ (linearChange F n e f) =
      linearChange F n (linearTranspose F n e.symm) (localFourierOperator F n ψ hψ μ f) := by
  have h := congrArg (fun g => (linearChangeScale F n (linearTranspose F n e.symm) : ℂ) • g)
    (localFourier_linearChange_scaled F n ψ hψ e f)
  rw [smul_smul, ← Complex.ofReal_mul, mul_comm,
    linearChangeScale_mul_inverseTranspose F n, Complex.ofReal_one, one_smul] at h
  exact h

/-- Fourier intertwines a normalized linear change with its inverse transpose on all L². -/
theorem localFourierL2_linearChange (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) (u : LocalL2 F n) :
    localFourierL2 F n ψ hψ (linearChangeL2 F n e u) =
      linearChangeL2 F n (linearTranspose F n e.symm) (localFourierL2 F n ψ hψ u) := by
  exact congrFun (localL2_ext F n
    (T := fun u => localFourierL2 F n ψ hψ (linearChangeL2 F n e u))
    (S := fun u => linearChangeL2 F n (linearTranspose F n e.symm) (localFourierL2 F n ψ hψ u))
    (by fun_prop) (by fun_prop) (fun f => by
    simp only [linearChangeL2_apply_test, localFourierL2_apply_test, localFourier_linearChange])) u

/-! ### Phase algebra, coordinate covariance and Fourier conjugation -/

/-- The multiplier agrees a.e. with pointwise multiplication for every L² input. -/
theorem quadraticPhaseL2_coeFn (Q : QuadraticForm F (Fin n → F)) (u : LocalL2 F n) :
    (quadraticPhaseL2 F n ψ hψ Q u : (Fin n → F) → ℂ) =ᵐ[μ]
      fun x => (ψ (Q x) : ℂ) * u x := by
  let m : (Fin n → F) → ℂ := fun x => (ψ (Q x) : ℂ)
  have hm : MemLp m ⊤ μ := memLp_top_of_bound
    (((polynomialPhase F n ψ hψ Q (quadraticForm_continuous F n Q)).map (fun u : ℂˣ => (u : ℂ))).continuous.aestronglyMeasurable)
    1 (Filter.Eventually.of_forall (fun x => (norm_character_of_hasConductorFour F ψ hψ (Q x)).le))
  let T : LocalL2 F n →L[ℂ] LocalL2 F n :=
    (ContinuousLinearMap.mul ℂ ℂ).holderL μ ⊤ 2 2 (hm.toLp m)
  have hT (v : LocalL2 F n) : (T v : (Fin n → F) → ℂ) =ᵐ[μ] fun x => m x * v x := by
    filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) (hm.toLp m) v,
      hm.coeFn_toLp] with x hx hm'
    exact hx.trans (congrArg (fun c => c * v x) hm')
  have he : (quadraticPhaseL2 F n ψ hψ Q : LocalL2 F n → LocalL2 F n) = T := by
    apply localL2_ext F n (quadraticPhaseL2 F n ψ hψ Q).continuous T.continuous
    intro f
    rw [quadraticPhaseL2_apply_test]
    apply Lp.ext
    filter_upwards [schwartzToL2_coeFn μ (quadraticPhase F n ψ hψ Q f),
      hT (schwartzToL2 μ f), schwartzToL2_coeFn μ f] with x hf ht hx
    rw [hf, ht, hx]
    rfl
  rw [congrFun he u]
  exact hT u

/-- Quadratic phases form an additive family on the complete Hilbert space. -/
theorem quadraticPhaseL2_add (Q R : QuadraticForm F (Fin n → F)) (u : LocalL2 F n) :
    quadraticPhaseL2 F n ψ hψ (Q + R) u =
      quadraticPhaseL2 F n ψ hψ Q (quadraticPhaseL2 F n ψ hψ R u) := by
  apply Lp.ext
  filter_upwards [quadraticPhaseL2_coeFn F n ψ hψ (Q + R) u,
    quadraticPhaseL2_coeFn F n ψ hψ Q (quadraticPhaseL2 F n ψ hψ R u),
    quadraticPhaseL2_coeFn F n ψ hψ R u] with x h1 h2 h3
  rw [h1, h2, h3]
  simp [ψ.map_add_eq_mul, mul_assoc]

@[simp] theorem quadraticPhaseL2_zero (u : LocalL2 F n) :
    quadraticPhaseL2 F n ψ hψ 0 u = u := by
  apply Lp.ext
  filter_upwards [quadraticPhaseL2_coeFn F n ψ hψ 0 u] with x hx
  simpa using hx

/-- Negating the quadratic form gives the inverse, and therefore the Hilbert adjoint. -/
theorem quadraticPhaseL2_symm (Q : QuadraticForm F (Fin n → F)) :
    (quadraticPhaseL2 F n ψ hψ Q).symm = quadraticPhaseL2 F n ψ hψ (-Q) := by
  ext u : 1
  apply (quadraticPhaseL2 F n ψ hψ Q).injective
  rw [LinearIsometryEquiv.apply_symm_apply, ← quadraticPhaseL2_add, add_neg_cancel,
    quadraticPhaseL2_zero]

/-- The phase as an element of the actual unitary group of bounded operators. -/
def quadraticPhaseL2Unitary (Q : QuadraticForm F (Fin n → F)) :
    unitary (LocalL2 F n →L[ℂ] LocalL2 F n) :=
  Unitary.linearIsometryEquiv.symm (quadraticPhaseL2 F n ψ hψ Q)

theorem quadraticPhaseL2_adjoint (Q : QuadraticForm F (Fin n → F)) :
    ContinuousLinearMap.adjoint (quadraticPhaseL2 F n ψ hψ Q : LocalL2 F n →L[ℂ] LocalL2 F n) =
      (quadraticPhaseL2 F n ψ hψ (-Q) : LocalL2 F n →L[ℂ] LocalL2 F n) := by
  rw [(quadraticPhaseL2 F n ψ hψ Q).adjoint_eq_symm, quadraticPhaseL2_symm]

/-- Change of variables pulls the quadratic form back by the same linear map. -/
theorem linearChangeL2_quadraticPhase (e : (Fin n → F) ≃ₗ[F] (Fin n → F))
    (Q : QuadraticForm F (Fin n → F)) (u : LocalL2 F n) :
    linearChangeL2 F n e (quadraticPhaseL2 F n ψ hψ Q u) =
      quadraticPhaseL2 F n ψ hψ (Q.comp e.toLinearMap) (linearChangeL2 F n e u) := by
  exact congrFun (localL2_ext F n
    (T := fun u => linearChangeL2 F n e (quadraticPhaseL2 F n ψ hψ Q u))
    (S := fun u => quadraticPhaseL2 F n ψ hψ (Q.comp e.toLinearMap) (linearChangeL2 F n e u))
    (by fun_prop) (by fun_prop) (fun f => by
    simp only [quadraticPhaseL2_apply_test, linearChangeL2_apply_test]
    congr 1
    apply Subtype.ext
    ext x
    change (linearChangeScale F n e : ℂ) * ((ψ (Q (e x)) : ℂ) * f.val (e x)) =
      (ψ (Q (e x)) : ℂ) * ((linearChangeScale F n e : ℂ) * f.val (e x))
    ring)) u

/-- Lower quadratic phase, with the explicit convention `F⁻¹ M_Q F`. -/
def lowerQuadraticPhaseL2 (Q : QuadraticForm F (Fin n → F)) :
    LocalL2 F n ≃ₗᵢ[ℂ] LocalL2 F n :=
  ((localFourierL2 F n ψ hψ).trans (quadraticPhaseL2 F n ψ hψ Q)).trans
    (localFourierL2 F n ψ hψ).symm

/-- Fourier turns the lower phase into the upper multiplication operator. -/
theorem localFourierL2_lowerQuadraticPhase (Q : QuadraticForm F (Fin n → F)) (u : LocalL2 F n) :
    localFourierL2 F n ψ hψ (lowerQuadraticPhaseL2 F n ψ hψ Q u) =
      quadraticPhaseL2 F n ψ hψ Q (localFourierL2 F n ψ hψ u) :=
  (localFourierL2 F n ψ hψ).apply_symm_apply _

/-- The lower phase restricts to the original test-function operators. -/
theorem lowerQuadraticPhaseL2_apply_test (Q : QuadraticForm F (Fin n → F))
    (f : SchwartzBruhat (Fin n → F)) :
    lowerQuadraticPhaseL2 F n ψ hψ Q (schwartzToL2 μ f) =
      schwartzToL2 μ ((localFourierEquiv F n ψ hψ).symm
        (quadraticPhase F n ψ hψ Q (localFourierEquiv F n ψ hψ f))) := by
  simp [lowerQuadraticPhaseL2, localFourierEquiv_apply]

/-- Lower phases satisfy the same additive parameter law. -/
theorem lowerQuadraticPhaseL2_add (Q R : QuadraticForm F (Fin n → F)) (u : LocalL2 F n) :
    lowerQuadraticPhaseL2 F n ψ hψ (Q + R) u =
      lowerQuadraticPhaseL2 F n ψ hψ Q (lowerQuadraticPhaseL2 F n ψ hψ R u) := by
  simp [lowerQuadraticPhaseL2, quadraticPhaseL2_add]

/-- Long-root phases from the existing lattice model are instances of the full L² construction. -/
theorem quadraticPhaseL2_longRoot (i : Fin n) (t : Integers F)
    (f : SchwartzBruhat (Fin n → F)) :
    quadraticPhaseL2 F n ψ hψ ((t : F) • QuadraticMap.proj i i) (schwartzToL2 μ f) =
      schwartzToL2 μ (longRootOperator F n ψ hψ i t f) := by
  rw [quadraticPhaseL2_apply_test]
  congr 1
  apply Subtype.ext
  ext x
  simp [quadraticPhase_apply, longRootOperator, longRootPhase, polynomialPhase, pow_two]

/-- The upper short-root convention is `ψ(2t xᵢxⱼ)`, including its factor two. -/
theorem quadraticPhaseL2_shortRoot (i j : Fin n) (t : Integers F)
    (f : SchwartzBruhat (Fin n → F)) :
    quadraticPhaseL2 F n ψ hψ ((2 * (t : F)) • QuadraticMap.proj i j) (schwartzToL2 μ f) =
      schwartzToL2 μ (shortRootOperator F n ψ hψ i j t f) := by
  rw [quadraticPhaseL2_apply_test]
  congr 1
  apply Subtype.ext
  ext x
  simp [quadraticPhase_apply, shortRootOperator, shortRootPhase, polynomialPhase, mul_assoc]

/-- Quadratic phases commute with Fourier squared because `Q(-x)=Q(x)`. -/
theorem localFourierL2_sq_quadraticPhase (Q : QuadraticForm F (Fin n → F)) (u : LocalL2 F n) :
    localFourierL2 F n ψ hψ (localFourierL2 F n ψ hψ (quadraticPhaseL2 F n ψ hψ Q u)) =
      quadraticPhaseL2 F n ψ hψ Q (localFourierL2 F n ψ hψ (localFourierL2 F n ψ hψ u)) := by
  exact congrFun (localL2_ext F n
    (T := fun u => localFourierL2 F n ψ hψ (localFourierL2 F n ψ hψ (quadraticPhaseL2 F n ψ hψ Q u)))
    (S := fun u => quadraticPhaseL2 F n ψ hψ Q (localFourierL2 F n ψ hψ (localFourierL2 F n ψ hψ u)))
    (by fun_prop) (by fun_prop) (fun f => by
    simp only [quadraticPhaseL2_apply_test, localFourierL2_apply_test]
    congr 1
    apply Subtype.ext
    ext x
    simp only [quadraticPhase_apply, localFourierOperator_sq, Q.map_neg])) u

/-- The opposite conjugation gives the same lower phase with this positive-sign Fourier convention. -/
theorem localFourierL2_quadraticPhase (Q : QuadraticForm F (Fin n → F)) (u : LocalL2 F n) :
    localFourierL2 F n ψ hψ (quadraticPhaseL2 F n ψ hψ Q u) =
      lowerQuadraticPhaseL2 F n ψ hψ Q (localFourierL2 F n ψ hψ u) := by
  apply (localFourierL2 F n ψ hψ).injective
  rw [localFourierL2_lowerQuadraticPhase, localFourierL2_sq_quadraticPhase]

/-- The lower quadratic phase is also an element of the unitary group. -/
def lowerQuadraticPhaseL2Unitary (Q : QuadraticForm F (Fin n → F)) :
    unitary (LocalL2 F n →L[ℂ] LocalL2 F n) :=
  Unitary.linearIsometryEquiv.symm (lowerQuadraticPhaseL2 F n ψ hψ Q)

@[simp] theorem lowerQuadraticPhaseL2_zero (u : LocalL2 F n) :
    lowerQuadraticPhaseL2 F n ψ hψ 0 u = u := by
  simp [lowerQuadraticPhaseL2]

theorem lowerQuadraticPhaseL2_symm (Q : QuadraticForm F (Fin n → F)) :
    (lowerQuadraticPhaseL2 F n ψ hψ Q).symm = lowerQuadraticPhaseL2 F n ψ hψ (-Q) := by
  ext u : 1
  apply (lowerQuadraticPhaseL2 F n ψ hψ Q).injective
  rw [LinearIsometryEquiv.apply_symm_apply, ← lowerQuadraticPhaseL2_add, add_neg_cancel,
    lowerQuadraticPhaseL2_zero]

end
end Char2Theta.Dyadic

namespace Char2Theta.Dyadic
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

/-! ## Nondegenerate quadratic data and completion of the square -/

/-- A quadratic form together with its invertible polar map for the pairing `2x·y`. -/
@[ext] structure LocalQuadraticDatum (F : Type*) [Field F] (n : ℕ) where
  form : QuadraticForm F (Fin n → F)
  polarEquiv : (Fin n → F) ≃ₗ[F] (Fin n → F)
  map_add : ∀ x y, form (x + y) = form x + form y + 2 * ∑ i, x i * polarEquiv y i

variable (F : Type*) [NormedField F] [NormedAlgebra ℚ_[2] F]
  [FiniteDimensional ℚ_[2] F] (n : ℕ)

namespace LocalQuadraticDatum
variable {F n} (D : LocalQuadraticDatum F n)

/-- Dual quadratic form obtained by completing the square. -/
def dualForm : QuadraticForm F (Fin n → F) := D.form.comp D.polarEquiv.symm.toLinearMap

omit [NormedAlgebra ℚ_[2] F] [FiniteDimensional ℚ_[2] F] in
@[simp] theorem dualForm_apply (x : Fin n → F) : D.dualForm x = D.form (D.polarEquiv.symm x) := rfl

omit [NormedAlgebra ℚ_[2] F] [FiniteDimensional ℚ_[2] F] in
/-- Completion of the square with exactly the original Fourier factor two. -/
theorem complete_square (x y : Fin n → F) :
    D.form x + 2 * ∑ i, x i * y i = D.form (x + D.polarEquiv.symm y) - D.dualForm y := by
  rw [D.map_add, D.polarEquiv.apply_symm_apply, dualForm_apply]
  ring

omit [FiniteDimensional ℚ_[2] F] in
/-- The polar map is symmetric for the coordinate dot product. -/
theorem polar_symmetric (x y : Fin n → F) :
    ∑ i, x i * D.polarEquiv y i = ∑ i, y i * D.polarEquiv x i := by
  have h := D.map_add x y
  have h' := D.map_add y x
  rw [add_comm y x] at h'
  apply (mul_left_cancel₀ (two_ne_zero : (2 : F) ≠ 0))
  linear_combination h' - h

omit [FiniteDimensional ℚ_[2] F] in
/-- The inverse polar map is the polar map of the dual quadratic form. -/
theorem dualForm_map_add (x y : Fin n → F) :
    D.dualForm (x + y) = D.dualForm x + D.dualForm y +
      2 * ∑ i, x i * D.polarEquiv.symm y i := by
  simp only [dualForm_apply, LinearEquiv.map_add, D.map_add, D.polarEquiv.apply_symm_apply]
  congr 2
  have h := D.polar_symmetric (D.polarEquiv.symm x) (D.polarEquiv.symm y)
  simp only [D.polarEquiv.apply_symm_apply] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- Construct the polar equivalence from mathlib's nondegeneracy predicate and duality. -/
def ofNondegenerate (Q : QuadraticForm F (Fin n → F)) (hQ : Q.Nondegenerate) :
    LocalQuadraticDatum F n := by
  let B : LinearMap.BilinForm F (Fin n → F) := Q.associated
  have hB : B.Nondegenerate := (QuadraticMap.nondegenerate_associated_iff (Q := Q)).mpr hQ
  let e := (B.toDual hB).trans (coordinateDual F n).symm
  refine ⟨Q, e, fun x y => ?_⟩
  have hd : (∑ i, x i * e y i) = B y x := by
    have he : coordinateDual F n (e y) x = B y x := by
      simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
        LinearMap.BilinForm.toDual_def]
    simpa only [coordinateDual_apply, mul_comm] using he
  rw [hd, show B y x = B x y from QuadraticMap.associated_isSymm F Q y x]
  have hp := congrArg (fun b : LinearMap.BilinForm F (Fin n → F) => b x y)
    (QuadraticMap.two_nsmul_associated F Q)
  change 2 • B x y = Q (x + y) - Q x - Q y at hp
  simp only [two_smul] at hp
  linear_combination -hp

omit [FiniteDimensional ℚ_[2] F] in
@[simp] theorem ofNondegenerate_form (Q : QuadraticForm F (Fin n → F)) (hQ : Q.Nondegenerate) :
    (ofNondegenerate Q hQ).form = Q := rfl

end LocalQuadraticDatum

/-- The standard quadratic form, built from mathlib coordinate quadratic maps. -/
def standardLocalQuadraticForm : QuadraticForm F (Fin n → F) :=
  ∑ i : Fin n, QuadraticMap.proj i i

omit [NormedAlgebra ℚ_[2] F] [FiniteDimensional ℚ_[2] F] in
@[simp] theorem standardLocalQuadraticForm_apply (x : Fin n → F) :
    standardLocalQuadraticForm F n x = ∑ i, x i ^ 2 := by
  simp [standardLocalQuadraticForm, QuadraticMap.sum_apply, pow_two]

/-- Scalar nondegenerate forms `a∑xᵢ²`, including the rank-one Gaussian for every unit `a`. -/
def scalarQuadraticDatum (a : Fˣ) : LocalQuadraticDatum F n where
  form := (a : F) • standardLocalQuadraticForm F n
  polarEquiv := LinearEquiv.smulOfUnit a
  map_add x y := by
    change (a : F) * standardLocalQuadraticForm F n (x + y) =
      (a : F) * standardLocalQuadraticForm F n x +
      (a : F) * standardLocalQuadraticForm F n y + 2 * ∑ i, x i * ((a : F) * y i)
    simp only [standardLocalQuadraticForm_apply, Pi.add_apply, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The standard form has identity polar map. -/
def standardQuadraticDatum : LocalQuadraticDatum F n where
  form := standardLocalQuadraticForm F n
  polarEquiv := LinearEquiv.refl F _
  map_add x y := by
    simp only [standardLocalQuadraticForm_apply, Pi.add_apply, LinearEquiv.refl_apply,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring

omit [NormedAlgebra ℚ_[2] F] [FiniteDimensional ℚ_[2] F] in
@[simp] theorem standardQuadraticDatum_dualForm :
    (standardQuadraticDatum F n).dualForm = standardLocalQuadraticForm F n := by
  ext x
  rfl

omit [NormedAlgebra ℚ_[2] F] [FiniteDimensional ℚ_[2] F] in
@[simp] theorem standardQuadraticDatum_form :
    (standardQuadraticDatum F n).form = standardLocalQuadraticForm F n := rfl

omit [NormedAlgebra ℚ_[2] F] [FiniteDimensional ℚ_[2] F] in
@[simp] theorem standardQuadraticDatum_polarEquiv :
    (standardQuadraticDatum F n).polarEquiv = LinearEquiv.refl F _ := rfl

omit [NormedAlgebra ℚ_[2] F] [FiniteDimensional ℚ_[2] F] in
@[simp] theorem scalarQuadraticDatum_one :
    scalarQuadraticDatum F n 1 = standardQuadraticDatum F n := by
  apply LocalQuadraticDatum.ext
  · simp [scalarQuadraticDatum, standardQuadraticDatum]
  · ext x i
    change (1 : F) * x i = x i
    exact one_mul _

/-! ## Compact open cutoffs and stabilization of Gaussian integrals -/

/-- Compact open ball indicator, used only at positive radii. -/
def gaussianCutoff (r : ℝ) (hr : 0 < r) : SchwartzBruhat (Fin n → F) :=
  ⟨(LocallyConstant.const (Fin n → F) (1 : ℂ)).indicator
    ⟨Metric.isClosed_closedBall, IsUltrametricDist.isOpen_closedBall _ hr.ne'⟩,
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 r)
      Set.support_indicator_subset⟩

@[simp] theorem gaussianCutoff_apply (r : ℝ) (hr : 0 < r) (x : Fin n → F) :
    (gaussianCutoff F n r hr).val x = if ‖x‖ ≤ r then 1 else 0 := by
  change (Metric.closedBall (0 : Fin n → F) r).indicator (fun _ => (1 : ℂ)) x = _
  by_cases hx : ‖x‖ ≤ r
  · rw [Set.indicator_of_mem (by simpa using hx), if_pos hx]
  · rw [Set.indicator_of_notMem (by simpa using hx), if_neg hx]

/-- Ultrametric balls are invariant under translations by their own elements. -/
theorem gaussianCutoff_add (r : ℝ) (hr : 0 < r) (a x : Fin n → F) (ha : ‖a‖ ≤ r) :
    (gaussianCutoff F n r hr).val (x + a) = (gaussianCutoff F n r hr).val x := by
  have hx : ‖x + a‖ ≤ r ↔ ‖x‖ ≤ r := by
    constructor
    · intro h
      have hh := IsUltrametricDist.norm_add_le_max (x + a) (-a)
      simpa using hh.trans (max_le h (by simpa using ha))
    · intro h
      exact (IsUltrametricDist.norm_add_le_max x a).trans (max_le h ha)
  simp only [gaussianCutoff_apply, hx]

variable [MeasurableSpace (Fin n → F)] [BorelSpace (Fin n → F)]
  (ψ : AddChar F ℂˣ) (hψ : HasConductorFour (Integers F).toSubring ψ)
local notation "μ" => latticeFourierHaar F n
local notation "𝓕" => localFourierOperator F n ψ hψ μ

/-- A genuine finite integral: the oscillatory quadratic functional on test functions. -/
def gaussianFunctional (Q : QuadraticForm F (Fin n → F)) (f : SchwartzBruhat (Fin n → F)) : ℂ :=
  ∫ x, (ψ (Q x) : ℂ) * f.val x ∂μ

include hψ in
/-- The quadratic functional is always integrated against a compactly supported integrable function. -/
theorem gaussianFunctional_integrable (Q : QuadraticForm F (Fin n → F))
    (f : SchwartzBruhat (Fin n → F)) :
    Integrable (fun x => (ψ (Q x) : ℂ) * f.val x) μ :=
  (quadraticPhase F n ψ hψ Q f).val.continuous.integrable_of_hasCompactSupport
    (quadraticPhase F n ψ hψ Q f).property

/-- Gaussian integrals over compact open balls; the unrestricted phase is not integrated. -/
def gaussianTruncation (Q : QuadraticForm F (Fin n → F)) (r : ℝ) (hr : 0 < r) : ℂ :=
  gaussianFunctional F n ψ Q (gaussianCutoff F n r hr)

/-- Completing the square on a ball containing the required translation. -/
theorem fourier_gaussianCutoff (D : LocalQuadraticDatum F n) (r : ℝ) (hr : 0 < r)
    (y : Fin n → F) (hy : ‖D.polarEquiv.symm y‖ ≤ r) :
    (𝓕 (quadraticPhase F n ψ hψ D.form (gaussianCutoff F n r hr))).val y =
      (ψ (-D.dualForm y) : ℂ) * gaussianTruncation F n ψ D.form r hr := by
  change (∫ x, localFourierKernel F n ψ hψ y x *
    ((ψ (D.form x) : ℂ) * (gaussianCutoff F n r hr).val x) ∂μ) = _
  have hi (x : Fin n → F) : localFourierKernel F n ψ hψ y x * (ψ (D.form x) : ℂ) =
      (ψ (-D.dualForm y) : ℂ) * (ψ (D.form (x + D.polarEquiv.symm y)) : ℂ) := by
    simp only [localFourierKernel_apply, ← Units.val_mul, ← ψ.map_add_eq_mul]
    congr 2
    have h := D.complete_square x y
    linear_combination h
  calc
    _ = ∫ x, (ψ (-D.dualForm y) : ℂ) *
        ((ψ (D.form (x + D.polarEquiv.symm y)) : ℂ) *
          (gaussianCutoff F n r hr).val (x + D.polarEquiv.symm y)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [gaussianCutoff_add F n r hr _ _ hy, ← mul_assoc, hi, mul_assoc]
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      exact integral_add_right_eq_self
        (fun x => (ψ (D.form x) : ℂ) * (gaussianCutoff F n r hr).val x) _

/-- Truncated Fourier duality once both compact supports fit in the cutoff ball. -/
theorem gaussian_duality_truncated (D : LocalQuadraticDatum F n)
    (f : SchwartzBruhat (Fin n → F)) (r : ℝ) (hr : 0 < r)
    (hf : ∀ x ∈ Function.support (𝓕 f).val, ‖x‖ ≤ r)
    (he : ∀ y ∈ Function.support f.val, ‖D.polarEquiv.symm y‖ ≤ r) :
    gaussianFunctional F n ψ D.form (𝓕 f) =
      gaussianTruncation F n ψ D.form r hr * gaussianFunctional F n ψ (-D.dualForm) f := by
  let g := quadraticPhase F n ψ hψ D.form (gaussianCutoff F n r hr)
  calc
    _ = ∫ x, g.val x * (𝓕 f).val x ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : (𝓕 f).val x = 0
      · simp [hx]
      · simp [g, quadraticPhase_apply, gaussianCutoff_apply, hf x hx]
    _ = ∫ y, (𝓕 g).val y * f.val y ∂μ := (localFourierOperator_bilinear F n ψ hψ μ g f).symm
    _ = ∫ y, gaussianTruncation F n ψ D.form r hr *
        ((ψ ((-D.dualForm) y) : ℂ) * f.val y) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with y
      by_cases hy : f.val y = 0
      · simp [hy]
      · rw [show (𝓕 g).val y = (ψ (-D.dualForm y) : ℂ) *
          gaussianTruncation F n ψ D.form r hr from
          fourier_gaussianCutoff F n ψ hψ D r hr y (he y hy)]
        simp only [QuadraticMap.neg_apply]
        ring
    _ = _ := integral_const_mul _ _

/-- Compactness supplies a common cutoff for every larger radius. -/
theorem gaussian_duality_large_radius (D : LocalQuadraticDatum F n)
    (f : SchwartzBruhat (Fin n → F)) :
    ∃ R > 0, ∀ r, R ≤ r → ∀ hr : 0 < r,
      gaussianFunctional F n ψ D.form (𝓕 f) =
        gaussianTruncation F n ψ D.form r hr * gaussianFunctional F n ψ (-D.dualForm) f := by
  obtain ⟨a, ha, hfa⟩ := (𝓕 f).property.isBounded.exists_pos_norm_le
  obtain ⟨b, hb, hfb⟩ := (f.property.image
    (linearHomeomorph F n D.polarEquiv.symm).continuous).isBounded.exists_pos_norm_le
  refine ⟨max a b, lt_max_of_lt_left ha, fun r hr hrpos =>
    gaussian_duality_truncated F n ψ hψ D f r hrpos ?_ ?_⟩
  · intro x hx
    exact (hfa x (subset_tsupport _ hx)).trans ((le_max_left a b).trans hr)
  · intro y hy
    exact (hfb _ ⟨y, subset_tsupport _ hy, rfl⟩).trans ((le_max_right a b).trans hr)

/-- Opposite phases cancel inside the convergent test-function integral. -/
theorem gaussianFunctional_neg_phase (Q : QuadraticForm F (Fin n → F))
    (f : SchwartzBruhat (Fin n → F)) :
    gaussianFunctional F n ψ (-Q) (quadraticPhase F n ψ hψ Q f) = ∫ x, f.val x ∂μ := by
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [quadraticPhase_apply, QuadraticMap.neg_apply, ← mul_assoc,
    ← Units.val_mul, ← ψ.map_add_eq_mul, neg_add_cancel, ψ.map_zero_eq_one, Units.val_one, one_mul]

/-- A fixed reference test function with nonzero opposite-phase integral. -/
def gaussianReference (D : LocalQuadraticDatum F n) : SchwartzBruhat (Fin n → F) :=
  quadraticPhase F n ψ hψ D.dualForm (latticeDelta F n 0).val

theorem gaussianReference_integral_ne_zero (D : LocalQuadraticDatum F n) :
    gaussianFunctional F n ψ (-D.dualForm) (gaussianReference F n ψ hψ D) ≠ 0 := by
  rw [gaussianReference, gaussianFunctional_neg_phase]
  simpa [fourierTest, schwartzDilate, schwartzPullback] using integral_fourierTest_ne_zero F n (1 : Fˣ)

/-- The local oscillatory Gaussian integral, defined by convergent test-function integrals.
The stabilization theorem below identifies it with every sufficiently large ball integral. -/
def localGaussianIntegral (D : LocalQuadraticDatum F n) : ℂ :=
  gaussianFunctional F n ψ D.form (𝓕 (gaussianReference F n ψ hψ D)) /
    gaussianFunctional F n ψ (-D.dualForm) (gaussianReference F n ψ hψ D)

/-- Gaussian truncations are eventually exactly constant, not merely convergent. -/
theorem gaussianTruncation_stabilizes (D : LocalQuadraticDatum F n) :
    ∃ R > 0, ∀ r, R ≤ r → ∀ hr : 0 < r,
      gaussianTruncation F n ψ D.form r hr = localGaussianIntegral F n ψ hψ D := by
  obtain ⟨R, hR, h⟩ := gaussian_duality_large_radius F n ψ hψ D (gaussianReference F n ψ hψ D)
  refine ⟨R, hR, fun r hr hrpos => ?_⟩
  unfold localGaussianIntegral
  rw [h r hr hrpos, mul_div_cancel_right₀ _ (gaussianReference_integral_ne_zero F n ψ hψ D)]

/-- The Fourier transform of the Gaussian as a distribution on the original test space. -/
theorem gaussian_fourier_duality (D : LocalQuadraticDatum F n) (f : SchwartzBruhat (Fin n → F)) :
    gaussianFunctional F n ψ D.form (𝓕 f) =
      localGaussianIntegral F n ψ hψ D * gaussianFunctional F n ψ (-D.dualForm) f := by
  obtain ⟨R, hR, h⟩ := gaussian_duality_large_radius F n ψ hψ D f
  obtain ⟨S, hS, hstab⟩ := gaussianTruncation_stabilizes F n ψ hψ D
  have hp : 0 < max R S := lt_max_of_lt_left hR
  rw [h (max R S) (le_max_left _ _) hp, hstab (max R S) (le_max_right _ _) hp]

/-- The Fourier duality identity uniquely determines the Gaussian scalar. -/
theorem localGaussianIntegral_unique (D : LocalQuadraticDatum F n) (c : ℂ)
    (hc : ∀ f : SchwartzBruhat (Fin n → F),
      gaussianFunctional F n ψ D.form (𝓕 f) = c * gaussianFunctional F n ψ (-D.dualForm) f) :
    c = localGaussianIntegral F n ψ hψ D := by
  unfold localGaussianIntegral
  rw [hc, mul_div_cancel_right₀ _ (gaussianReference_integral_ne_zero F n ψ hψ D)]

/-! ## The Bruhat identity and the normalized Gaussian scalar -/

/-- Translation of the dual Gaussian functional is an inverse Fourier transform. -/
theorem gaussianFunctional_translate (D : LocalQuadraticDatum F n)
    (f : SchwartzBruhat (Fin n → F)) (y : Fin n → F) :
    gaussianFunctional F n ψ (-D.dualForm) (schwartzTranslate F n (-y) f) =
      (ψ (-D.dualForm y) : ℂ) *
        ((localFourierEquiv F n ψ hψ).symm (quadraticPhase F n ψ hψ (-D.dualForm) f)).val
          (D.polarEquiv.symm y) := by
  rw [localFourierEquiv_symm_apply]
  change (∫ x, (ψ (-D.dualForm x) : ℂ) * f.val (x + -y) ∂μ) =
    (ψ (-D.dualForm y) : ℂ) *
      ∫ x, localFourierKernel F n ψ hψ (-(D.polarEquiv.symm y)) x *
        ((ψ (-D.dualForm x) : ℂ) * f.val x) ∂μ
  rw [← integral_add_right_eq_self
    (fun x => (ψ (-D.dualForm x) : ℂ) * f.val (x + -y)) y, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [add_neg_cancel_right]
  have hp : (ψ (-D.dualForm (x + y)) : ℂ) =
      (ψ (-D.dualForm y) : ℂ) *
        (localFourierKernel F n ψ hψ (-(D.polarEquiv.symm y)) x * (ψ (-D.dualForm x) : ℂ)) := by
    simp only [localFourierKernel_apply, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib,
      ← Units.val_mul, ← ψ.map_add_eq_mul]
    congr 2
    rw [D.dualForm_map_add]
    ring
  rw [hp]
  ring

/-- The unnormalized Bruhat identity, with the actual stabilized Gaussian integral. -/
theorem localFourier_quadratic_bruhat_raw (D : LocalQuadraticDatum F n)
    (f : SchwartzBruhat (Fin n → F)) (y : Fin n → F) :
    (𝓕 (quadraticPhase F n ψ hψ D.form (𝓕 f))).val y =
      localGaussianIntegral F n ψ hψ D * (ψ (-D.dualForm y) : ℂ) *
        ((localFourierEquiv F n ψ hψ).symm (quadraticPhase F n ψ hψ (-D.dualForm) f)).val
          (D.polarEquiv.symm y) := by
  have ht : 𝓕 (schwartzTranslate F n (-y) f) = schwartzModulate F n ψ hψ y (𝓕 f) := by
    rw [localFourierOperator_translate, neg_neg]
  calc
    _ = gaussianFunctional F n ψ D.form (𝓕 (schwartzTranslate F n (-y) f)) := by
      rw [ht]
      apply integral_congr_ae
      filter_upwards [] with x
      change localFourierKernel F n ψ hψ y x * ((ψ (D.form x) : ℂ) * (𝓕 f).val x) =
        (ψ (D.form x) : ℂ) * (localFourierKernel F n ψ hψ y x * (𝓕 f).val x)
      ring
    _ = _ := by
      rw [gaussian_fourier_duality, gaussianFunctional_translate, mul_assoc]

/-- Weil index for the self-dual Haar measure and the positive kernel `ψ(2x·y)`.
The positive factor is the square root of the Haar modulus of the polar map. -/
def localWeilIndex (D : LocalQuadraticDatum F n) : ℂ :=
  (linearChangeScale F n D.polarEquiv : ℂ) * localGaussianIntegral F n ψ hψ D

/-- Normalized Bruhat relation on all Schwartz–Bruhat functions. -/
theorem localFourier_quadratic_bruhat (D : LocalQuadraticDatum F n)
    (f : SchwartzBruhat (Fin n → F)) :
    𝓕 (quadraticPhase F n ψ hψ D.form (𝓕 f)) =
      localWeilIndex F n ψ hψ D •
        quadraticPhase F n ψ hψ (-D.dualForm)
          (linearChange F n D.polarEquiv.symm
            ((localFourierEquiv F n ψ hψ).symm (quadraticPhase F n ψ hψ (-D.dualForm) f))) := by
  apply Subtype.ext
  apply LocallyConstant.ext
  intro y
  change _ = localWeilIndex F n ψ hψ D *
    (quadraticPhase F n ψ hψ (-D.dualForm)
      (linearChange F n D.polarEquiv.symm
        ((localFourierEquiv F n ψ hψ).symm (quadraticPhase F n ψ hψ (-D.dualForm) f)))).val y
  simp only [localFourier_quadratic_bruhat_raw, quadraticPhase_apply, linearChange_apply,
    QuadraticMap.neg_apply, localWeilIndex, linearChangeScale_symm, Complex.ofReal_inv]
  have hs : (linearChangeScale F n D.polarEquiv : ℂ) ≠ 0 := by
    exact_mod_cast (linearChangeScale_pos F n D.polarEquiv).ne'
  field_simp

/-- The same scalar and Bruhat identity on the full, completed L² space. -/
theorem localFourierL2_quadratic_bruhat (D : LocalQuadraticDatum F n) (u : LocalL2 F n) :
    localFourierL2 F n ψ hψ (quadraticPhaseL2 F n ψ hψ D.form (localFourierL2 F n ψ hψ u)) =
      localWeilIndex F n ψ hψ D •
        quadraticPhaseL2 F n ψ hψ (-D.dualForm)
          (linearChangeL2 F n D.polarEquiv.symm
            ((localFourierL2 F n ψ hψ).symm (quadraticPhaseL2 F n ψ hψ (-D.dualForm) u))) := by
  exact congrFun (localL2_ext F n
    (T := fun u => localFourierL2 F n ψ hψ
      (quadraticPhaseL2 F n ψ hψ D.form (localFourierL2 F n ψ hψ u)))
    (S := fun u => localWeilIndex F n ψ hψ D •
      quadraticPhaseL2 F n ψ hψ (-D.dualForm)
        (linearChangeL2 F n D.polarEquiv.symm
          ((localFourierL2 F n ψ hψ).symm (quadraticPhaseL2 F n ψ hψ (-D.dualForm) u))))
    (by fun_prop) (by fun_prop) (fun f => by
      simp only [localFourierL2_apply_test, quadraticPhaseL2_apply_test,
        localFourierL2_symm_apply_test, linearChangeL2_apply_test,
        localFourier_quadratic_bruhat, map_smul])) u

/-- The normalized Gaussian scalar has modulus one, forced by the unitary Bruhat identity. -/
theorem norm_localWeilIndex (D : LocalQuadraticDatum F n) :
    ‖localWeilIndex F n ψ hψ D‖ = 1 := by
  have h := congrArg norm (localFourierL2_quadratic_bruhat F n ψ hψ D
    (schwartzToL2 μ (latticeDelta F n 0).val))
  simp only [LinearIsometryEquiv.norm_map, norm_smul] at h
  exact mul_right_cancel₀ (norm_ne_zero_iff.mpr (schwartzToL2_delta_ne_zero F n))
    (h.symm.trans (one_mul _).symm)

/-- The oscillatory Gaussian integral is nonzero. -/
theorem localGaussianIntegral_ne_zero (D : LocalQuadraticDatum F n) :
    localGaussianIntegral F n ψ hψ D ≠ 0 := by
  intro hz
  have h := norm_localWeilIndex F n ψ hψ D
  simp [localWeilIndex, hz] at h

/-! ## Compact-domain limits, absolute values and cubic relations -/

/-- The cutoff definition equals the usual integral over the compact open ball. -/
theorem gaussianTruncation_eq_setIntegral (Q : QuadraticForm F (Fin n → F))
    (r : ℝ) (hr : 0 < r) :
    gaussianTruncation F n ψ Q r hr =
      ∫ x in Metric.closedBall (0 : Fin n → F) r, (ψ (Q x) : ℂ) ∂μ := by
  rw [← integral_indicator Metric.isClosed_closedBall.measurableSet]
  apply integral_congr_ae
  filter_upwards [] with x
  change (ψ (Q x) : ℂ) * (gaussianCutoff F n r hr).val x = _
  rw [gaussianCutoff_apply]
  by_cases hx : ‖x‖ ≤ r
  · rw [if_pos hx, mul_one, Set.indicator_of_mem (by simpa using hx)]
  · rw [if_neg hx, mul_zero, Set.indicator_of_notMem (by simpa using hx)]

/-- The oscillatory integral is the eventual value of genuine compact-domain integrals. -/
theorem localGaussianIntegral_eventually_eq (D : LocalQuadraticDatum F n) :
    (fun r : ℝ => ∫ x in Metric.closedBall (0 : Fin n → F) r, (ψ (D.form x) : ℂ) ∂μ)
      =ᶠ[atTop] fun _ => localGaussianIntegral F n ψ hψ D := by
  obtain ⟨R, hR, h⟩ := gaussianTruncation_stabilizes F n ψ hψ D
  filter_upwards [eventually_ge_atTop R] with r hr
  rw [← gaussianTruncation_eq_setIntegral F n ψ D.form r (hR.trans_le hr)]
  exact h r hr (hR.trans_le hr)

/-- In particular these ball integrals converge to the local Gaussian integral. -/
theorem tendsto_gaussianIntegral (D : LocalQuadraticDatum F n) :
    Tendsto (fun r : ℝ => ∫ x in Metric.closedBall (0 : Fin n → F) r, (ψ (D.form x) : ℂ) ∂μ)
      atTop (𝓝 (localGaussianIntegral F n ψ hψ D)) :=
  tendsto_const_nhds.congr' (localGaussianIntegral_eventually_eq F n ψ hψ D).symm

/-- The exact absolute value of the unnormalized Gaussian integral. -/
theorem norm_localGaussianIntegral (D : LocalQuadraticDatum F n) :
    ‖localGaussianIntegral F n ψ hψ D‖ = (linearChangeScale F n D.polarEquiv)⁻¹ := by
  have h := norm_localWeilIndex F n ψ hψ D
  rw [localWeilIndex, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (linearChangeScale_pos F n D.polarEquiv).le] at h
  apply (mul_left_cancel₀ (linearChangeScale_pos F n D.polarEquiv).ne')
  rw [h, mul_inv_cancel₀ (linearChangeScale_pos F n D.polarEquiv).ne']

/-- Cancelling a phase and its negative on the full Hilbert space. -/
theorem quadraticPhaseL2_neg_cancel (Q : QuadraticForm F (Fin n → F)) (u : LocalL2 F n) :
    quadraticPhaseL2 F n ψ hψ (-Q) (quadraticPhaseL2 F n ψ hψ Q u) = u := by
  rw [← quadraticPhaseL2_add, neg_add_cancel, quadraticPhaseL2_zero]

/-- With positive Fourier kernel, the standard Weyl–unipotent word has cube `γ(q)·Id`. -/
theorem localFourierL2_standard_cubic (u : LocalL2 F n) :
    localFourierL2 F n ψ hψ (quadraticPhaseL2 F n ψ hψ (standardLocalQuadraticForm F n)
      (localFourierL2 F n ψ hψ (quadraticPhaseL2 F n ψ hψ (standardLocalQuadraticForm F n)
        (localFourierL2 F n ψ hψ (quadraticPhaseL2 F n ψ hψ (standardLocalQuadraticForm F n) u))))) =
      localWeilIndex F n ψ hψ (standardQuadraticDatum F n) • u := by
  have h := localFourierL2_quadratic_bruhat F n ψ hψ (standardQuadraticDatum F n)
    (quadraticPhaseL2 F n ψ hψ (standardLocalQuadraticForm F n)
      (localFourierL2 F n ψ hψ (quadraticPhaseL2 F n ψ hψ (standardLocalQuadraticForm F n) u)))
  simpa only [standardQuadraticDatum_form, standardQuadraticDatum_dualForm,
    standardQuadraticDatum_polarEquiv, LinearEquiv.refl_symm, quadraticPhaseL2_neg_cancel,
    LinearIsometryEquiv.symm_apply_apply, linearChangeL2_refl] using h

/-- Standard cubic relation already holds on the original test-function space. -/
theorem localFourier_standard_cubic (f : SchwartzBruhat (Fin n → F)) :
    𝓕 (quadraticPhase F n ψ hψ (standardLocalQuadraticForm F n)
      (𝓕 (quadraticPhase F n ψ hψ (standardLocalQuadraticForm F n)
        (𝓕 (quadraticPhase F n ψ hψ (standardLocalQuadraticForm F n) f))))) =
      localWeilIndex F n ψ hψ (standardQuadraticDatum F n) • f := by
  apply schwartzToL2_injective μ
  simpa only [localFourierL2_apply_test, quadraticPhaseL2_apply_test, map_smul] using
    localFourierL2_standard_cubic F n ψ hψ (schwartzToL2 μ f)

/-! ## Relations in the actual unitary group -/

/-- The normalized Gaussian scalar belongs to mathlib's unitary group of complex scalars. -/
def localWeilScalar (D : LocalQuadraticDatum F n) : unitary ℂ := by
  refine ⟨localWeilIndex F n ψ hψ D, ?_, ?_⟩
  · change (starRingEnd ℂ) _ * _ = 1
    rw [Complex.conj_mul', norm_localWeilIndex]
    norm_num
  · change _ * (starRingEnd ℂ) _ = 1
    rw [mul_comm, Complex.conj_mul', norm_localWeilIndex]
    norm_num

/-- Central scalar operator associated to the Weil index. -/
def localWeilScalarL2 (D : LocalQuadraticDatum F n) :
    unitary (LocalL2 F n →L[ℂ] LocalL2 F n) :=
  Unitary.linearIsometryEquiv.symm
    (localWeilScalar F n ψ hψ D • LinearIsometryEquiv.refl ℂ (LocalL2 F n))

@[simp] theorem localWeilScalarL2_apply (D : LocalQuadraticDatum F n) (u : LocalL2 F n) :
    (localWeilScalarL2 F n ψ hψ D : LocalL2 F n →L[ℂ] LocalL2 F n) u =
      localWeilIndex F n ψ hψ D • u := rfl

/-- Bruhat relation in the actual unitary group; multiplication is operator composition. -/
theorem localFourierL2Unitary_quadratic_bruhat (D : LocalQuadraticDatum F n) :
    localFourierL2Unitary F n ψ hψ * quadraticPhaseL2Unitary F n ψ hψ D.form *
      localFourierL2Unitary F n ψ hψ =
    localWeilScalarL2 F n ψ hψ D * quadraticPhaseL2Unitary F n ψ hψ (-D.dualForm) *
      linearChangeL2Unitary F n D.polarEquiv.symm * (localFourierL2Unitary F n ψ hψ)⁻¹ *
        quadraticPhaseL2Unitary F n ψ hψ (-D.dualForm) := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro u
  change localFourierL2 F n ψ hψ (quadraticPhaseL2 F n ψ hψ D.form (localFourierL2 F n ψ hψ u)) =
    localWeilIndex F n ψ hψ D • quadraticPhaseL2 F n ψ hψ (-D.dualForm)
      (linearChangeL2 F n D.polarEquiv.symm
        (ContinuousLinearMap.adjoint (localFourierL2 F n ψ hψ : LocalL2 F n →L[ℂ] LocalL2 F n)
          (quadraticPhaseL2 F n ψ hψ (-D.dualForm) u)))
  rw [localFourierL2_adjoint]
  exact localFourierL2_quadratic_bruhat F n ψ hψ D u

/-- The standard cubic Weil relation as an equality of elements of the unitary group. -/
theorem localFourierL2Unitary_standard_cubic :
    (localFourierL2Unitary F n ψ hψ *
      quadraticPhaseL2Unitary F n ψ hψ (standardLocalQuadraticForm F n)) ^ 3 =
      localWeilScalarL2 F n ψ hψ (standardQuadraticDatum F n) := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro u
  exact localFourierL2_standard_cubic F n ψ hψ u

/-- The fourth-power Weyl relation on the completed Hilbert space. -/
theorem localFourierL2_four (u : LocalL2 F n) :
    localFourierL2 F n ψ hψ (localFourierL2 F n ψ hψ
      (localFourierL2 F n ψ hψ (localFourierL2 F n ψ hψ u))) = u := by
  exact congrFun (localL2_ext F n
    (T := fun u => localFourierL2 F n ψ hψ (localFourierL2 F n ψ hψ
      (localFourierL2 F n ψ hψ (localFourierL2 F n ψ hψ u))))
    (S := id) (by fun_prop) (by fun_prop) (fun f => by
      simp only [localFourierL2_apply_test, id_eq]
      congr 1
      apply Subtype.ext
      ext x
      rw [localFourierOperator_sq, localFourierOperator_sq, neg_neg])) u

/-- The fourth-power Weyl relation in mathlib's unitary group. -/
theorem localFourierL2Unitary_pow_four : (localFourierL2Unitary F n ψ hψ) ^ 4 = 1 := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro u
  exact localFourierL2_four F n ψ hψ u

end

/-! ## The normalized rank-one Weil index -/

noncomputable section
open MeasureTheory
variable (F : Type*) [NormedField F] [NormedAlgebra ℚ_[2] F] [FiniteDimensional ℚ_[2] F]
  [MeasurableSpace (Fin 1 → F)] [BorelSpace (Fin 1 → F)]
  (ψ : AddChar F ℂˣ) (hψ : HasConductorFour (Integers F).toSubring ψ)

/-- Rank-one Weil index normalized to equal one at the coefficient `1`.
This is a ratio of the two oscillatory indices, not the scalar of the Bruhat formula itself. -/
def normalizedRankOneWeilIndex (a : Fˣ) : ℂ :=
  localWeilIndex F 1 ψ hψ (scalarQuadraticDatum F 1 a) /
    localWeilIndex F 1 ψ hψ (standardQuadraticDatum F 1)

/-- The normalized rank-one index still has modulus one. -/
theorem norm_normalizedRankOneWeilIndex (a : Fˣ) :
    ‖normalizedRankOneWeilIndex F ψ hψ a‖ = 1 := by
  rw [normalizedRankOneWeilIndex, norm_div, norm_localWeilIndex, norm_localWeilIndex, div_self one_ne_zero]

@[simp] theorem normalizedRankOneWeilIndex_one :
    normalizedRankOneWeilIndex F ψ hψ 1 = 1 := by
  rw [normalizedRankOneWeilIndex, scalarQuadraticDatum_one, div_self]
  exact norm_ne_zero_iff.mp (by rw [norm_localWeilIndex]; exact one_ne_zero)

end
end Char2Theta.Dyadic
