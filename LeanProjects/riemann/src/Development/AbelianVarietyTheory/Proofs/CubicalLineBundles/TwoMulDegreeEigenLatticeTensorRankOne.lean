import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralTangentVectorCoordinates
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SingleMemSpanIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueExtendRingOfIntegersHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveLieCharacterOfAdjoinGenerator
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormSumSum
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieTensorLine
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegersOfCmFieldConjStructure
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieRepresentationEigenLatticesStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueCmHermitianLatticeFormStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TwoMulDegDualLineCmIdealStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraSquaredLengthCompPairingHomStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFractionalIdealTraceFormRankOneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.TensorDeg

theorem eq_zero_of_re_diag {L : Type} [AddCommGroup L] (B : L → L → ℂ) (W : L → L) (l : ℂ) (hl : l.im ≠ 0)
    (hadd : ∀ a b c, B a (b + c) = B a b + B a c) (hsym : ∀ a b, starRingEnd ℂ (B a b) = B b a)
    (hW : ∀ a b, B a (W b) = l * B a b) (hd : ∀ a, (B a a).re = 0) (a b : L) : B a b = 0 := by
  have hre : ∀ a b, (B a b).re = (B b a).re := fun a b => by rw [← hsym a b, Complex.conj_re]
  have h0 : ∀ a b, (B a b).re = 0 := fun a b => by
    have h1 := hd (a + b)
    rw [hadd, Complex.add_re, hre (a + b) a, hre (a + b) b, hadd, hadd, Complex.add_re, Complex.add_re, hd, hd,
      hre b a] at h1
    linarith
  have h2 := h0 a (W b)
  rw [hW, Complex.mul_re, h0, mul_zero, zero_sub, neg_eq_zero, mul_eq_zero] at h2
  exact Complex.ext (h0 a b) (h2.resolve_left hl)

theorem span_embeddings_eq_top {E K L I : Type} [Field E] [NumberField E] [Field K] [AddCommGroup L] [Module (𝓞 E) L]
    [Fintype I] (σ : I → (E →+* K)) (hσ : Function.Injective σ) (e : L →ₗ[𝓞 E] E) (a₀ : L) (h₀ : e a₀ ≠ 0) :
    Submodule.span K (Set.range fun a i => σ i (e a)) = ⊤ := by
  refine span_flip_eq_top_iff_linearIndependent.2 (?_ : LinearIndependent K fun i a => σ i (e a))
  have hinj : Function.Injective fun i => ((σ i).comp (algebraMap (𝓞 E) E)).toMonoidHom := fun i j hij =>
    hσ (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => DFunLike.congr_fun hij a))
  have hli := (linearIndependent_monoidHom (𝓞 E) K).comp _ hinj
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro g hg i
  have := hli (fun i => g i * σ i (e a₀)) (funext fun s => by
    have := congrFun hg (s • a₀)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_smul, Algebra.smul_def, map_mul, Pi.zero_apply] at this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Function.comp]
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Algebra.smul_def]
    ring) i
  exact (mul_eq_zero.1 this).resolve_right ((map_ne_zero _).2 h₀)

theorem form_eq_of_span {K V L I : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype I] (h : HermFam K V)
    (s : K →+* ℂ) (Φ : (I → K) →ₗ[K] V) (ev : L → I → K) (b : I → ℝ)
    (hsp : Submodule.span K (Set.range ev) = ⊤)
    (hf : ∀ x y, h.form s (Φ (ev x)) (Φ (ev y)) = ∑ i, b i * (starRingEnd ℂ (s (ev x i)) * s (ev y i))) (z w : I → K) :
    h.form s (Φ z) (Φ w) = ∑ i, b i * (starRingEnd ℂ (s (z i)) * s (w i)) := by
  have key : ∀ z, (∀ y, h.form s (Φ z) (Φ (ev y)) = ∑ i, b i * (starRingEnd ℂ (s (z i)) * s (ev y i))) →
      ∀ w, h.form s (Φ z) (Φ w) = ∑ i, b i * (starRingEnd ℂ (s (z i)) * s (w i)) := fun z hz w => by
    have hw : w ∈ Submodule.span K (Set.range ev) := hsp ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem v hv => obtain ⟨y, rfl⟩ := hv; exact hz y
    | zero => simpa using h.smul_right s 0 (Φ z) 0
    | add u v _ _ hu hv => simp only [map_add, h.add_right, hu, hv, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    | smul r u _ hu =>
      rw [map_smul, h.smul_right, hu, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp; ring
  refine key z (fun y => ?_) w
  rw [← h.conj_symm, key _ (hf y), map_sum]
  exact Finset.sum_congr rfl fun i _ => by simp [_root_.mul_comm]

theorem exists_eigenline {E K O L V I : Type} [Field E] [NumberField E] [IsCMField E] [Field K] [NumberField K]
    [CommRing O] [AddCommGroup L] [Module (𝓞 E) L] [Module O L] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Fintype I] (σ : I → (E →+* K)) (hσ : Function.Injective σ) (i₀ : I)
    (τ₀ : O →+* 𝓞 K) (w : O) (hw : ∀ s : K →+* ℂ, (s (τ₀ w)).im ≠ 0) (e : L →ₗ[𝓞 E] E)
    (he : ∀ i (k : O) a, σ i (e (k • a)) = τ₀ k * σ i (e a)) (a₀ : L) (h₀ : e a₀ ≠ 0) (β : E)
    (hβ : ∀ s : E →+* ℂ, 0 < (s β).re ∧ (s β).im = 0) (hK : L → L → O)
    (hh : ∀ a b, (τ₀ (hK a b) : K) = ∑ i, σ i (β * e a * IsCMField.complexConj E (e b)))
    (N : ℕ) (x y : Fin N → L) (hdual : ∀ a, a = ∑ m, hK a (y m) • x m) (h : HermFam K V) (n : (K →+* ℂ) → ℝ)
    (hn : ∀ s, 0 < n s) (c : L →+ V) (hc : ∀ (k : O) a, c (k • a) = (τ₀ k : K) • c a) (r : 𝓞 E → V →ₗ[K] V)
    (hr : ∀ s a, c (s • a) = r s (c a))
    (hnorm : ∀ s a, (h.form s (c a) (c a)).re = (s (τ₀ (hK a a))).re * n s) :
    ∃ v : V, v ≠ 0 ∧ (∀ s, (h.form s v v).re = (s (σ i₀ β)).re * n s) ∧
      ∀ z, (z ∈ Submodule.span (𝓞 K) (Set.range c) ∧ ∀ a : 𝓞 E, r a z = σ i₀ a • z) ↔
        ∃ t : K, z = t • v ∧ ∀ b, IsIntegral ℤ (t * σ i₀ (β * IsCMField.complexConj E (e b))) := by
  classical
  set ev : L → I → K := fun a i => σ i (e a) with hev
  set dv : L → I → K := fun b i => σ i (β * IsCMField.complexConj E (e b)) with hdv
  have hsp : Submodule.span K (Set.range ev) = ⊤ := span_embeddings_eq_top σ hσ e a₀ h₀
  have hh' : ∀ a b, algebraMap (𝓞 K) K (τ₀ (hK a b)) = ∑ i, ev a i * dv b i := fun a b =>
    (hh a b).trans (Finset.sum_congr rfl fun i _ => by simp only [hev, hdv, map_mul]; ring)
  have hexp : ∀ a, ev a = ∑ m, algebraMap (𝓞 K) K (τ₀ (hK a (y m))) • ev (x m) := fun a => by
    funext i
    conv_lhs => rw [hdual a]
    simp only [hev, map_sum, he, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  let Φ : (I → K) →ₗ[K] V :=
    { toFun := fun z => ∑ m, (∑ i, z i * dv (y m) i) • c (x m)
      map_add' := fun z z' => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, add_smul]
      map_smul' := fun t z => by
        simp only [Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, ← Finset.mul_sum, mul_smul, Finset.smul_sum,
          RingHom.id_apply] }
  have hΦ : ∀ a, Φ (ev a) = c a := fun a => by
    conv_rhs => rw [hdual a]
    simp only [map_sum, hc]
    change ∑ m, (∑ i, ev a i * dv (y m) i) • c (x m) = _
    simp only [← hh']
  let b : (K →+* ℂ) → I → ℝ := fun s i => (s (σ i β)).re * n s
  have hb : ∀ s i, 0 < b s i := fun s i => mul_pos (hβ (s.comp (σ i))).1 (hn s)
  have hb' : ∀ (s : K →+* ℂ) i, (b s i : ℂ) = s (σ i β) * n s := fun s i => by
    have : s (σ i β) = ((s (σ i β)).re : ℂ) := Complex.ext rfl (hβ (s.comp (σ i))).2
    rw [this]
    simp [b]
  have hform : ∀ s z z', h.form s (Φ z) (Φ z') = ∑ i, b s i * (starRingEnd ℂ (s (z i)) * s (z' i)) := fun s => by
    refine form_eq_of_span h s Φ ev (b s) hsp fun a a' => sub_eq_zero.1 ?_
    refine eq_zero_of_re_diag (fun a a' => h.form s (Φ (ev a)) (Φ (ev a')) -
      ∑ i, b s i * (starRingEnd ℂ (s (ev a i)) * s (ev a' i))) (fun a => w • a) (s (τ₀ w)) (hw s)
      (fun a a' a'' => ?_) (fun a a' => ?_) (fun a a' => ?_) (fun a => ?_) a a'
    · simp only [hΦ]
      simp only [map_add, h.add_right, hev, mul_add, Finset.sum_add_distrib]
      ring
    · rw [map_sub, h.conj_symm, map_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by simp [_root_.mul_comm]
    · simp only [hΦ]
      simp only [hc, h.smul_right, hev, he, mul_sub, Finset.mul_sum, map_mul]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    · have : ∑ i, b s i * (starRingEnd ℂ (s (ev a i)) * s (ev a i)) = s (τ₀ (hK a a)) * n s := by
        rw [hh, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        have := IsCMField.complexEmbedding_complexConj E (s.comp (σ i)) (e a)
        simp only [RingHom.comp_apply] at this
        rw [hb', map_mul, map_mul, map_mul, map_mul, this]
        simp only [hev]
        ring
      rw [this, hΦ, Complex.sub_re, hnorm, Complex.re_mul_ofReal, sub_self]
  obtain ⟨s₀⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hinj : ∀ z, Φ z = 0 → z = 0 := fun z hz => by
    have h1 := hform s₀ z z
    have h2 : h.form s₀ 0 0 = 0 := by simpa using h.smul_right s₀ 0 0 0
    rw [hz, h2] at h1
    have h3 : ∑ i, b s₀ i * Complex.normSq (s₀ (z i)) = 0 := by
      have : ((∑ i, b s₀ i * Complex.normSq (s₀ (z i)) : ℝ) : ℂ) = 0 := by
        rw [h1]
        push_cast
        exact Finset.sum_congr rfl fun i _ => by rw [Complex.normSq_eq_conj_mul_self]
      exact_mod_cast this
    rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hb s₀ i).le (Complex.normSq_nonneg _)] at h3
    funext i
    have := (mul_eq_zero.1 (h3 i (Finset.mem_univ i))).resolve_left (hb s₀ i).ne'
    simpa using this
  have hinj' : Function.Injective Φ := (injective_iff_map_eq_zero Φ).2 hinj
  have hact : ∀ (a : 𝓞 E) z, r a (Φ z) = Φ fun i => σ i a * z i := fun a z => by
    have hz : z ∈ Submodule.span K (Set.range ev) := hsp ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨u, rfl⟩ := hv
      rw [hΦ, ← hr, ← hΦ]
      congr 1
      funext i
      simp [hev, Algebra.smul_def]
    | zero => simp only [Pi.zero_apply, mul_zero, map_zero]; exact (map_zero Φ).symm
    | add u v _ _ hu hv =>
      rw [map_add, map_add, hu, hv, ← map_add]
      congr 1
      funext i
      simp [mul_add]
    | smul t u _ hu =>
      rw [map_smul, map_smul, hu, ← map_smul]
      congr 1
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  have hmap : Submodule.span (𝓞 K) (Set.range c) =
      (Submodule.span (𝓞 K) (Set.range ev)).map (Φ.restrictScalars (𝓞 K)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    exact funext fun a => (hΦ a).symm
  have hline := single_mem_span_iff_of_selfDual O (𝓞 K) K L I τ₀ hK ev dv N x y hh' hexp hsp i₀
  have hint : ∀ t : K, t ∈ (algebraMap (𝓞 K) K).range ↔ IsIntegral ℤ t := fun t =>
    ⟨fun ⟨u, hu⟩ => hu ▸ u.isIntegral_coe, fun ht => ⟨⟨t, ht⟩, rfl⟩⟩
  have hsing : ∀ t : K, t • Φ (Pi.single i₀ 1) = Φ (Pi.single i₀ t) := fun t => by
    rw [← map_smul, ← Pi.single_smul, smul_eq_mul, _root_.mul_one]
  refine ⟨Φ (Pi.single i₀ 1), fun hv => ?_, fun s => ?_, fun z => ⟨?_, ?_⟩⟩
  · simpa using congrFun (hinj _ hv) i₀
  · rw [hform, Finset.sum_eq_single i₀ (fun i _ hi => by simp [Pi.single_eq_of_ne hi]) (by simp)]
    simp [b]
  · rintro ⟨hz, hz'⟩
    rw [hmap] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    have hu' : u = Pi.single i₀ (u i₀) := by
      funext i
      by_cases hi : i = i₀
      · simp [hi]
      · rw [Pi.single_eq_of_ne hi]
        by_contra hne
        refine hi (hσ (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => ?_)))
        have := hz' a
        rw [LinearMap.restrictScalars_apply, hact, ← map_smul] at this
        exact mul_right_cancel₀ hne (congrFun (hinj' this) i)
    refine ⟨u i₀, by rw [hsing, ← hu']; rfl, fun a => (hint _).1 ((hline (u i₀)).1 (hu' ▸ hu) a)⟩
  · rintro ⟨t, rfl, ht⟩
    rw [hsing, hmap]
    refine ⟨⟨_, (hline t).2 fun a => (hint _).2 (ht a), rfl⟩, fun a => ?_⟩
    rw [hact, ← map_smul]
    congr 1
    funext i
    by_cases hi : i = i₀
    · simp [hi]
    · simp [Pi.single_eq_of_ne hi]

theorem two_mul_deg_eigLat : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ω : 𝓞 K) (C : Ell H (𝓞 K) ω) (D : Datum H) (ε : ℤˣ) (hK : D.La → D.La → OK H) (T : PAT H (Sp (𝓞 K))) (x : ℝ), Splits E K → D.p + D.q = 1 → IsKForm D ε hK → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → Nonempty (IsTen C D hK T) → C.HasPeriod x → ∀ (F : GenFib T.pol) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.w0 = ω → 2 * deg h (F.eigLat T.t.act τ) = x + Real.log H.d / 2 - Real.log (NumberField.rootDiscr E) := by
  intro hU hL E _ _ _ H K _ _ ω C D ε hK T x hsp hrk hKF hpos ⟨t⟩ ⟨n, hn, hx⟩ F h hh τ hτ
  classical
  obtain ⟨τ₀, hτ₀w, hτ₀⟩ := LieChar.ell_char E H (𝓞 K) ω C
  obtain ⟨τ', hτ'⟩ := (existsUnique_extend_ringOfIntegers_hom τ).exists
  have hext : ∀ σ : E →+* K, σ (H.rt : E) = τ' (H.rt : E) → ∀ k : OK H, σ ((k : 𝓞 E) : E) = τ₀ k := fun σ hσ k => by
    have h2 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E) := by
      simpa [map_ofNat] using congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
    have hw : σ (H.w0 : E) = τ₀ (wK H) := by
      rw [hτ₀w, ← hτ, ← hτ']
      have h3 := congrArg σ h2
      have h4 := congrArg τ' h2
      simp only [map_mul, map_add, map_one, map_ofNat] at h3 h4
      linear_combination (h3 - h4 + hσ) / 2
    obtain ⟨m, rfl, -⟩ := existsUnique_coord H k
    simp only [map_add, map_mul, map_intCast, ← hw]
    simp [wK]
  obtain ⟨𝔞, e, β, h𝔞, he, hrange, hβc, hβ, hform, hnorm⟩ := GlobalTheory.T.exists_fractionalIdeal_traceForm_rank_one E H D ε hK hrk hKF hpos
  obtain ⟨k, hk, hku, -, -, -, -, N, xs, ys, hdual⟩ := GlobalTheory.T.exists_unique_cmHermitianLatticeForm E H D ε
  obtain rfl := hku hK hKF
  obtain ⟨c1, c2, c3, c4, c5, -⟩ := integral_tangent_coordinates K T.pol F
  obtain ⟨r, hr, hr'⟩ := GlobalTheory.T.exists_lieRepresentation_eigenLattices K T.pol F (𝓞 E) T.t.act
  letI : Algebra (OK H) (𝓞 K) := τ₀.toAlgebra
  obtain ⟨hfin, hproj, -⟩ := (OK_isDedekindDomain_and_projective E H).2.2.2.2.2 D.La D.fin D.proj
  obtain ⟨f, -, f2, f3, f4, f5⟩ := lie_tensor_line (𝓞 K) (OK H) C.P.A T.t.G C.act _ D.La t.ten C.v hfin hproj C.basis hτ₀
  choose co hco hcou using fun z => c1 (f z) ((f2 _).2 ⟨z, rfl⟩)
  have coadd : ∀ z z', co (z + z') = co z + co z' := fun z z' =>
    (hcou _ _ (by rw [f3]; exact c3 _ _ _ _ (hco z) (hco z'))).symm
  have cosmul : ∀ (a : 𝓞 K) z, co (a • z) = a • co z := fun a z =>
    (hcou _ _ (c4 _ _ _ _ (hco z) (f4 a z))).symm
  let c : D.La →+ (Fin F.P₀.g → K) := AddMonoidHom.mk' (fun a => co (TensorProduct.tmul (OK H) 1 a)) fun a b => by
    rw [TensorProduct.tmul_add, coadd]
  have hc : ∀ a, F.IsCoord (C.v ≫ t.ten.tmul a) (c a) := fun a => f5 a ▸ hco _
  have hlat : F.lieLat = Submodule.span (𝓞 K) (Set.range c) := by
    refine le_antisymm (fun z hz => ?_) (Submodule.span_le.2 ?_)
    · obtain ⟨u, hu⟩ := (c5 z).1 hz
      obtain ⟨z', rfl⟩ := (f2 u).1 hu.1
      rw [hcou _ _ hu]
      clear hu hz
      induction z' with
      | zero =>
        have := cosmul 0 0
        rw [zero_smul, zero_smul] at this
        rw [this]
        exact zero_mem _
      | tmul a m =>
        rw [show TensorProduct.tmul (OK H) a m = a • TensorProduct.tmul (OK H) 1 m by
          simp [TensorProduct.smul_tmul'], cosmul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
      | add z z' hz hz' => rw [coadd]; exact add_mem hz hz'
    · rintro _ ⟨a, rfl⟩
      exact (c5 _).2 ⟨_, hc a⟩
  have hβ' : ∀ s : E →+* ℂ, 0 < (s β).re ∧ (s β).im = 0 := fun s => ⟨hβ s, by
    rw [← Complex.conj_eq_iff_im, ← IsCMField.complexEmbedding_complexConj E s, hβc]⟩
  obtain ⟨a₀, ha₀⟩ : ∃ a, e a ≠ 0 := by
    by_contra! h0
    refine h𝔞 (FractionalIdeal.coeToSubmodule_eq_bot.1 ?_)
    rw [← hrange, LinearMap.range_eq_bot]
    exact LinearMap.ext h0
  have : Finite (E →+* K) := Finite.of_equiv _ (RingHom.equivRatAlgHom E K).symm
  have := Fintype.ofFinite {σ : E →+* K // σ (H.rt : E) = τ' (H.rt : E)}
  obtain ⟨v, hv0, hvn, hv⟩ := exists_eigenline (I := {σ : E →+* K // σ (H.rt : E) = τ' (H.rt : E)}) Subtype.val
    Subtype.val_injective ⟨τ', rfl⟩ τ₀ (wK H) (fun s => by
      intro him
      have h2 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E) := by
        simpa [map_ofNat] using congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
      have h3 := congrArg (s.comp τ') h2
      have h4 := congrArg (s.comp τ') (HostModel.coe_sq_eq_neg H.rt_sq)
      have h5 : s (τ' (H.w0 : E)) = s (τ₀ (wK H)) := congrArg s (hext τ' rfl (wK H))
      simp only [map_mul, map_add, map_one, map_ofNat, map_pow, map_neg, map_natCast, RingHom.comp_apply] at h3 h4
      have h6 := congrArg Complex.im h3
      have h7 := congrArg Complex.re h4
      have h8 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      rw [h5] at h6
      simp [him] at h6
      simp [sq, ← h6] at h7
      nlinarith [mul_self_nonneg (s (τ' (H.rt : E))).re]) e
    (fun i a b => by
      rw [← hext i.1 i.2, ← map_mul, Subalgebra.smul_def, map_smul]
      rfl) a₀ ha₀ β hβ' (fun x y => k x y)
    (fun a b => by rw [← hext τ' rfl, hform K (splits_iff_card.1 hsp) τ' a b, finsum_eq_sum_of_fintype])
    N xs ys hdual h n (fun s => (hn s).1) c
    (fun a m => by
      change co _ = _ • co _
      rw [TensorProduct.tmul_smul, ← algebraMap_smul (𝓞 K) a, cosmul]
      rfl) (fun a => r a)
    (fun s a => by
      refine (c1 _ (hc _).1).unique (hc _) ?_
      rw [t.lin, ← Category.assoc]
      exact hr s _ _ (hc a))
    (fun s a => GlobalTheory.T.lieAlgebraSquaredLength_comp_pairing_hom hU hL (𝓞 K) C.P T.pol (t.ten.tmul a) (C.act.act (k a a)) C.v (τ₀ (k a a))
      (s.comp (algebraMap (𝓞 K) K)) (n s) _ inferInstance (C.act.hom _) (t.lam a a) (C.basis.1 0) (hτ₀ _)
      (((hn s).2 _).2 rfl) (HermNorm.isLieNormSq_form hU hL K T.pol F h hh s _ _ (hc a)))
  have hE : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  rw [GlobalTheory.T.two_mul_deg_dual_line_cmIdeal E K _ h _ v τ' 𝔞 β n h𝔞 hv0 (fun s => (hn s).1) hβ' hvn fun z => ?_, hnorm, ← hx]
  · field_simp
    ring
  · rw [(hr' τ z).1, hlat]
    refine Iff.trans (and_congr_right fun _ => forall_congr' fun a => by rw [hτ']; rfl) ((hv z).trans ?_)
    refine exists_congr fun s => and_congr_right fun _ => ⟨fun h1 b hb => ?_, fun h1 b => h1 _ ?_⟩
    · obtain ⟨a, rfl⟩ : b ∈ LinearMap.range e := hrange ▸ hb
      exact h1 a
    · exact (hrange.le ⟨b, rfl⟩ : e b ∈ (𝔞 : Submodule (𝓞 E) E))

end GlobalTheory.CM.TensorDeg
