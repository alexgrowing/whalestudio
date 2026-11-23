import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.GGPS

open MeasureTheory Set Filter Topology Function IsDedekindDomain
open AutomorphicForm CuspidalSpectrum
open scoped Pointwise

noncomputable section

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem continuous_of_rightInvariant {φ : AdelicGLn.AdelicGL K n → ℂ} (hs : IsArchSmooth φ)
    {U : Subgroup (AdelicGLn.integralFiniteGL K n)}
    (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)))
    (hinv : ∀ (g : AdelicGLn.AdelicGL K n) (u : U),
      φ (g * finEmb K n ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n)) = φ g) :
    Continuous φ := by
  set U' : Set (AdelicGLn.FiniteAdelicGL K n) :=
    Subtype.val '' (U : Set (AdelicGLn.integralFiniteGL K n))
  have hU' : IsOpen U' := (AdelicGLn.isOpen_integralFiniteGL K n).isOpenMap_subtype_val _ hU
  have h1U' : (1 : AdelicGLn.FiniteAdelicGL K n) ∈ U' := ⟨1, U.one_mem, rfl⟩
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  let e : AdelicGLn.AdelicGL K n → AdelicGLn.InfiniteAdelicGL K n × AdelicGLn.FiniteAdelicGL K n :=
    fun g => AdelicGLn.prodEquiv K n (g₀⁻¹ * g)
  have he : Continuous e :=
    (AdelicGLn.prodEquiv K n).continuous.comp (continuous_const.mul continuous_id)
  let F : AdelicGLn.InfiniteAdelicGL K n × AdelicGLn.FiniteAdelicGL K n → ℂ :=
    fun p => φ (g₀ * infEmb K n (archEquiv K n p.1) * finEmb K n p.2)
  have hφF : φ = F ∘ e := by
    funext g
    simp only [F, e, Function.comp_apply, mul_assoc]
    rw [infEmb_mul_finEmb, mul_inv_cancel_left]
  have hslice : Continuous (archSlice φ g₀) := by
    letI := (isExpLieAlgebra K n).chartedSpace
    exact (hs g₀).continuous
  have hF : ContinuousAt F (e g₀) := by
    have hFeq : F =ᶠ[𝓝 (e g₀)] fun p => archSlice φ g₀ (archEquiv K n p.1) := by
      have he1 : e g₀ = 1 := by simp only [e, inv_mul_cancel, map_one]
      have hmem : (univ ×ˢ U') ∈ 𝓝 (e g₀) := by
        rw [he1]
        exact prod_mem_nhds univ_mem (hU'.mem_nhds h1U')
      filter_upwards [hmem] with p hp
      obtain ⟨u, hu, hup⟩ := hp.2
      simp only [F, archSlice_apply]
      rw [← hup]
      exact hinv _ ⟨u, hu⟩
    refine ContinuousAt.congr ?_ hFeq.symm
    exact (hslice.comp ((archEquiv K n).continuous.comp continuous_fst)).continuousAt
  rw [hφF]
  exact hF.comp he.continuousAt

theorem conj_unipGL_eq_archExp {r : ℕ} (x : AdelicGLn.AdelicGL K n) (P : UPos n r → 𝔸[K])
    (hP : ∀ p, (P p).2 = 0) :
    x⁻¹ * unipGL P * x = archExp (conjArch K n x P) := by
  have h1 := infEmb_mul_finEmb (K := K) (n := n) (x⁻¹ * unipGL P * x)
  rw [prodEquiv_conj_snd x P hP, map_one, mul_one] at h1
  refine h1.symm.trans ?_
  rw [archExp]
  congr 1
  refine Subtype.ext (Units.ext ?_)
  rw [coe_expG_top, exp_eq_one_add_of_mul_self_eq_zero (conjArch_mul_conjArch x P P)]
  change archMat K n ((x⁻¹ * unipGL P * x : AdelicGLn.AdelicGL K n) :
    Matrix (Fin n) (Fin n) 𝔸[K]) = _
  rw [coe_conj_unipGL, map_add, map_one]
  rfl

theorem norm_le_of_altSum_inf {φ : AdelicGLn.AdelicGL K n → ℂ} (hφc : Continuous φ)
    (hφ : IsLeftInvariant φ) {r : ℕ} {M : ℕ} (hM : 0 < M) (x : AdelicGLn.AdelicGL K n)
    (hct : constantTerm r φ x = 0)
    (hfin : ∀ z : UPos n r → 𝔸[K], (∀ p, (z p).1 = 0) →
      (∀ p, ∃ a ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K,
        (z p).2 = (M : FiniteAdeleRing (𝓞 K) K) * a) →
      ∀ w, φ (w * (x⁻¹ * unipGL z * x)) = φ w)
    (k : ℕ) {B : ℝ}
    (hB : ∀ y : Fin k → UPos n r → 𝔸[K], (∀ i, y i ∈ scaledUnipFD K n r M) →
      ‖altSum k (fun s => φ (unipGL (truncInf s) * x)) y 0‖ ≤ B) :
    ‖φ x‖ ≤ B := by
  set H : (UPos n r → 𝔸[K]) → ℂ := fun s => φ (unipGL s * x)
  have hHc : Continuous H := hφc.comp (continuous_unipGL.mul continuous_const)
  have hper : ∀ ξ ∈ unipLattice K n r, ∀ s, H (ξ + s) = H s := fun ξ hξ s =>
    hφ.unipGL_vadd x ⟨ξ, hξ⟩ s
  have hD := isAddFundamentalDomain_scaledUnipFD (K := K) (n := n) (r := r) hM
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_scaledUnipFD (K := K) (n := n) r hM
  have hint : ∀ t, IntegrableOn (fun y => H (t + y)) (scaledUnipFD K n r M) (unipMeasure K n r) :=
    fun t => ((hHc.comp (continuous_const.add continuous_id)).continuousOn.integrableOn_compact
      hC).mono_set hDC
  have hmean : ∫ y in scaledUnipFD K n r M, H y ∂unipMeasure K n r = 0 := by
    rw [← constantTerm_eq_setIntegral hφ hD x]
    exact hct
  have h0 := norm_le_of_forall_altSum_le hD (unipMeasure_scaledUnipFD hM) k H hper hint hmean B
    (fun y hy => ?_)
  · simpa [H, unipGL_zero] using h0
  have key : ∀ ε : Fin k → Bool,
      H (0 + altPoint y ε) = φ (unipGL (truncInf (0 + altPoint y ε)) * x) := by
    intro ε
    rw [zero_add]
    have hfinP := hfin (truncFin (altPoint y ε)) (fun p => rfl) fun p => by
      obtain ⟨a, ha, hPa⟩ := exists_finite_altPoint_eq_natCast_mul hM y hy ε p
      exact ⟨a, ha, hPa⟩
    have hP : unipGL (altPoint y ε) * x = unipGL (truncInf (altPoint y ε)) * x *
        (x⁻¹ * unipGL (truncFin (altPoint y ε)) * x) := by
      simp only [mul_assoc, mul_inv_cancel_left]
      rw [← mul_assoc, ← unipGL_add, truncInf_add_truncFin]
    simp only [H]
    rw [hP]
    exact hfinP _
  have heq : altSum k H y 0 = altSum k (fun s => φ (unipGL (truncInf s) * x)) y 0 := by
    rw [altSum_eq_sum, altSum_eq_sum]
    exact Finset.sum_congr rfl fun ε _ => congrArg (altSign ε • ·) (key ε)
  rw [heq]
  exact hB y hy

theorem altSum_truncInf_eq_diffSum {r : ℕ} (φ : AdelicGLn.AdelicGL K n → ℂ)
    (x : AdelicGLn.AdelicGL K n) {k : ℕ} (y : Fin k → UPos n r → 𝔸[K]) :
    altSum k (fun s => φ (unipGL (truncInf s) * x)) y 0 =
      diffSum φ x (fun i => conjArch K n x (truncInf (y i))) := by
  rw [altSum_eq_sum, diffSum]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [zero_add, zsmul_eq_mul]
  congr 2
  have h1 := conj_unipGL_eq_archExp x (truncInf (altPoint y ε)) fun p => rfl
  have h2 : conjArch K n x (truncInf (altPoint y ε)) =
      altPoint (fun i => conjArch K n x (truncInf (y i))) ε := by
    rw [← truncInfHom_apply, map_altPoint (truncInfHom n r), map_altPoint (conjArch K n x)]
    rfl
  rw [← h2, ← h1]
  group

theorem rho_le_of_ratio_le {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) (hprod : ∏ i, ρ i = 1) {R : ℝ}
    (hR1 : 1 ≤ R) (hR : ∀ i j : Fin n, ρ i / ρ j ≤ R) (i : Fin n) : ρ i ≤ R ∧ (ρ i)⁻¹ ≤ R := by
  have hn : n ≠ 0 := (Fin.pos i).ne'
  have hR0 : 0 ≤ R := by linarith
  have hprodR : ∀ f : Fin n → ℝ, (∀ j, 0 ≤ f j) → (∀ j, f j ≤ R) → ∏ j, f j ≤ R ^ n := by
    intro f hf0 hfR
    calc ∏ j, f j ≤ ∏ _j : Fin n, R := Finset.prod_le_prod (fun j _ => hf0 j) fun j _ => hfR j
      _ = R ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  constructor
  · have e1 : ρ i ^ n = ∏ j, (ρ i / ρ j) := by
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hprod,
        div_one]
    have h1 : ρ i ^ n ≤ R ^ n := by
      rw [e1]
      exact hprodR _ (fun j => (div_pos (hρ i) (hρ j)).le) fun j => hR i j
    exact le_of_pow_le_pow_left₀ hn hR0 h1
  · have e1 : (ρ i)⁻¹ ^ n = ∏ j, (ρ j / ρ i) := by
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hprod,
        one_div, inv_pow]
    have h1 : (ρ i)⁻¹ ^ n ≤ R ^ n := by
      rw [e1]
      exact hprodR _ (fun j => (div_pos (hρ j) (hρ i)).le) fun j => hR j i
    exact le_of_pow_le_pow_left₀ hn hR0 h1

end

theorem smooth_automorphic_open_invariant : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (φ : AdelicGLn.AdelicGL K n → ℂ) (hs : φ ∈ AutomorphicForm.archSmooth K n),
  AutomorphicForm.IsLeftInvariant φ → (∃ U : Subgroup (AdelicGLn.integralFiniteGL K n), IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) ∧
    ∀ (g : AdelicGLn.AdelicGL K n) (u : U), φ (g * AutomorphicForm.finEmb K n ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n)) = φ g) → AutomorphicForm.IsCuspidal φ →
  (∀ [MeasurableSpace (AutomorphicForm.archGroup K n)] [BorelSpace (AutomorphicForm.archGroup K n)]
    (μ : MeasureTheory.Measure (AutomorphicForm.archGroup K n)) [μ.IsHaarMeasure]
    (k : ℕ) (J : Fin k → Fin (CuspidalSpectrum.archDim K n)),
    ∃ D : AutomorphicForm.archGroup K n → ℂ, Continuous D ∧ HasCompactSupport D ∧ ∀ g : AdelicGLn.AdelicGL K n,
      ((AutomorphicForm.uAction (CuspidalSpectrum.uJ (K := K) (n := n) k J) (⟨φ, hs⟩ : ↥(AutomorphicForm.archSmooth K n)) :
        ↥(AutomorphicForm.archSmooth K n)) : AdelicGLn.AdelicGL K n → ℂ) g = ∫ y, φ (g * AutomorphicForm.infEmb K n y) * D y ∂μ) → (∀ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω → ∃ N : ℕ, ∀ Q : Set (AutomorphicForm.archGroup K n), IsCompact Q → ∃ C : ℝ,
    ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i), ∀ kk ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)), ∀ y ∈ Q, ∀ L : ℝ, 1 ≤ L →
      (∀ i, ρ i ≤ L ∧ (ρ i)⁻¹ ≤ L) →
      ‖φ (b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * kk * AutomorphicForm.infEmb K n y)‖ ≤ C * L ^ N) → (∀ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω → ω ⊆ (adelicBorel (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n)) →
    (∀ b ∈ ω, (IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det b) : ℝ) = 1) → ∀ t : ℝ, 0 < t → ∀ (r : ℕ) (hr0 : 0 < r) (hrn : r < n), ∃ N : ℕ, ∀ k : ℕ, ∃ C : ℝ,
      ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i), (∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
        ∏ i, ρ i = 1 → ∀ kk ∈ maxCompact (K := K) (n := n), ∀ R : ℝ, 1 ≤ R → (∀ i j : Fin n, ρ i / ρ j ≤ R) →
          ‖φ (b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * kk)‖ ≤
            C * (ρ ⟨r, hrn⟩ / ρ ⟨r - 1, lt_of_le_of_lt (Nat.sub_le r 1) hrn⟩) ^ k * R ^ N) := by
  intro K _ _ n φ hs hL ⟨U, hU, hinv⟩ hcusp hHC hbox ω hω hωB _ t ht r hr0 hrn
  have hφc : Continuous φ := continuous_of_rightInvariant hs hU hinv
  obtain ⟨N, hN⟩ := hbox ω hω
  refine ⟨N, fun k => ?_⟩
  letI : MeasurableSpace (archGroup K n) := borel _
  haveI : BorelSpace (archGroup K n) := ⟨rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure (archGroup K n), μ.IsHaarMeasure :=
    ⟨Measure.haar, inferInstance⟩
  obtain ⟨M, hM, hMconj⟩ := exists_natCast_conj_unipGL_mem U hU hω r
  obtain ⟨C₁, hC₁⟩ := exists_norm_archMat_conj_le hω hωB ht hr0 hrn
    (isCompact_scaledInfSet (K := K) M)
  set C₁' := max C₁ 0
  have hC₁'0 : 0 ≤ C₁' := le_max_right _ _
  set T : ℝ := (k : ℝ) * (C₁' * t⁻¹)
  obtain ⟨c, hc0, hc⟩ := exists_abs_archBasis_repr_le (K := K) (n := n)
  set S : Set (archGroup K n) :=
    (fun Z : ArchMatrix K n => (isExpLieAlgebra K n).expG ⟨Z, Submodule.mem_top⟩) ''
      Metric.closedBall 0 T
  have hS : IsCompact S := (isCompact_closedBall _ _).image
    ((isExpLieAlgebra K n).continuous_expG.comp (continuous_id.subtype_mk _))
  choose D hDc hDs hDrep using hHC μ k
  have hQ : ∀ J, IsCompact (S * tsupport (D J)) := fun J => hS.mul (hDs J)
  choose CJ hCJ using fun J => hN (S * tsupport (D J)) (hQ J)
  set Cs : ℝ := ∑ J, |CJ J| * ∫ y, ‖D J y‖ ∂μ
  have hInt0 : ∀ J, 0 ≤ ∫ y, ‖D J y‖ ∂μ := fun J => integral_nonneg fun y => norm_nonneg _
  have hCs : 0 ≤ Cs := Finset.sum_nonneg fun J _ => mul_nonneg (abs_nonneg _) (hInt0 J)
  have hd0 : 0 ≤ (archDim K n : ℝ) * c := mul_nonneg (Nat.cast_nonneg _) hc0
  refine ⟨((archDim K n : ℝ) * c) ^ k * C₁' ^ k * Cs, ?_⟩
  intro b hb ρ hρ hsieg hprod kk hkk R hR1 hR
  have hρb := rho_le_of_ratio_le hρ hprod hR1 hR
  set x : AdelicGLn.AdelicGL K n := b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * kk
    with hx
  set gain := ρ ⟨r, hrn⟩ / ρ ⟨r - 1, lt_of_le_of_lt (Nat.sub_le r 1) hrn⟩
  have hgain0 : 0 ≤ gain := div_nonneg (hρ _).le (hρ _).le
  have hgain : gain ≤ t⁻¹ := by
    have h1 := hsieg ⟨r - 1, lt_of_le_of_lt (Nat.sub_le r 1) hrn⟩ ⟨r, hrn⟩ (by simp; omega)
    rw [div_le_iff₀ (hρ _), ← div_eq_inv_mul, le_div_iff₀ ht, mul_comm]
    exact h1
  have hRN : 0 ≤ R ^ N := pow_nonneg (by linarith) _
  set B₀ : ℝ := Cs * R ^ N
  have hB₀ : 0 ≤ B₀ := mul_nonneg hCs hRN
  have hfinal : ‖φ x‖ ≤ ((archDim K n : ℝ) * c) ^ k * (C₁' * gain) ^ k * B₀ := by
    refine norm_le_of_altSum_inf hφc hL hM x (hcusp r hr0 hrn x) ?_ k ?_
    · intro z hz1 hz2 w
      obtain ⟨u, hu⟩ := hMconj b hb ρ hρ kk hkk z hz1 hz2
      have hu' : x⁻¹ * unipGL z * x = finEmb K n
          ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n) := hu
      rw [hu']
      exact hinv w u
    · intro y hy
      rw [altSum_truncInf_eq_diffSum]
      set Y : Fin k → ArchMatrix K n := fun i => conjArch K n x (truncInf (y i))
      have hYY : ∀ i j, Y i * Y j = 0 := fun i j => conjArch_mul_conjArch _ _ _
      have hcomm : ∀ i j, Commute (Y i) (Y j) := fun i j => (hYY i j).trans (hYY j i).symm
      have hYn : ∀ i, ‖Y i‖ ≤ C₁' * gain := fun i =>
        (hC₁ b hb ρ hρ hsieg kk hkk (truncInf (y i)) (fun p => rfl)
          (fun p => infinite_mem_scaledInfSet hM (hy i) p)).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hgain0)
      have hYT : ∀ i, ‖Y i‖ ≤ C₁' * t⁻¹ := fun i =>
        (hYn i).trans (mul_le_mul_of_nonneg_left hgain hC₁'0)
      have hder : ∀ (J : Fin k → Fin (archDim K n)) (τ : Fin k → ℝ),
          (∀ i, τ i ∈ Icc (0 : ℝ) 1) →
          ‖(uAction (uJ k J) ⟨φ, hs⟩ : AdelicGLn.AdelicGL K n → ℂ)
            (x * archExp (∑ i, τ i • Y i))‖ ≤ B₀ := by
        intro J τ hτ
        have hZ : ‖∑ i, τ i • Y i‖ ≤ T := by
          refine (norm_sum_le _ _).trans ?_
          calc ∑ i, ‖τ i • Y i‖ ≤ ∑ _i : Fin k, C₁' * t⁻¹ := Finset.sum_le_sum fun i _ => by
                rw [norm_smul, Real.norm_of_nonneg (hτ i).1]
                calc τ i * ‖Y i‖ ≤ 1 * (C₁' * t⁻¹) :=
                      mul_le_mul (hτ i).2 (hYT i) (norm_nonneg _) zero_le_one
                  _ = C₁' * t⁻¹ := one_mul _
            _ = T := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        set Z := ∑ i, τ i • Y i
        set e : archGroup K n := (isExpLieAlgebra K n).expG ⟨Z, Submodule.mem_top⟩
        have he : e ∈ S := ⟨Z, mem_closedBall_zero_iff.2 hZ, rfl⟩
        have hbd : ∀ w : archGroup K n, ‖φ (x * archExp Z * infEmb K n w) * D J w‖ ≤
            |CJ J| * R ^ N * ‖D J w‖ := by
          intro w
          by_cases hw : w ∈ tsupport (D J)
          · rw [norm_mul]
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            have e1 : x * archExp Z * infEmb K n w = x * infEmb K n (e * w) := by
              rw [map_mul, mul_assoc]
              rfl
            rw [e1]
            exact (hCJ J b hb ρ hρ kk hkk (e * w) (Set.mul_mem_mul he hw) R hR1 hρb).trans
              (mul_le_mul_of_nonneg_right (le_abs_self _) hRN)
          · rw [image_eq_zero_of_notMem_tsupport hw, mul_zero, norm_zero, mul_zero]
        have hint : Integrable (fun w => ‖D J w‖) μ :=
          (hDc J).norm.integrable_of_hasCompactSupport (hDs J).norm
        rw [hDrep J (x * archExp Z)]
        calc ‖∫ w, φ (x * archExp Z * infEmb K n w) * D J w ∂μ‖
            ≤ ∫ w, |CJ J| * R ^ N * ‖D J w‖ ∂μ :=
              norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall hbd)
          _ = (|CJ J| * ∫ w, ‖D J w‖ ∂μ) * R ^ N := by
              rw [integral_const_mul]; ring
          _ ≤ B₀ := mul_le_mul_of_nonneg_right
              (Finset.single_le_sum (f := fun J => |CJ J| * ∫ y, ‖D J y‖ ∂μ)
                (fun J _ => mul_nonneg (abs_nonneg _) (hInt0 J)) (Finset.mem_univ J)) hRN
      have h := norm_diffSum_le hc0 hc k ⟨φ, hs⟩ x Y hcomm B₀ hB₀ hder
      refine h.trans ?_
      have hprodY : ∏ i, ‖Y i‖ ≤ (C₁' * gain) ^ k := by
        rw [← Fin.prod_const]
        exact Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hYn i
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hprodY (pow_nonneg hd0 _)) hB₀
  refine hfinal.trans (le_of_eq ?_)
  simp only [B₀, mul_pow]
  ring

end GlobalTheory.CompanionTheory.GGPS

theorem GlobalTheory.CompanionTheory.GGPS.ggps_bound : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (φ : AdelicGLn.AdelicGL K n → ℂ) (hs : φ ∈ AutomorphicForm.archSmooth K n),
  AutomorphicForm.IsLeftInvariant φ → (∃ U : Subgroup (AdelicGLn.integralFiniteGL K n), IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) ∧
    ∀ (g : AdelicGLn.AdelicGL K n) (u : U), φ (g * AutomorphicForm.finEmb K n ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n)) = φ g) → AutomorphicForm.IsCuspidal φ →
  (∀ [MeasurableSpace (AutomorphicForm.archGroup K n)] [BorelSpace (AutomorphicForm.archGroup K n)]
    (μ : MeasureTheory.Measure (AutomorphicForm.archGroup K n)) [μ.IsHaarMeasure]
    (k : ℕ) (J : Fin k → Fin (CuspidalSpectrum.archDim K n)),
    ∃ D : AutomorphicForm.archGroup K n → ℂ, Continuous D ∧ HasCompactSupport D ∧ ∀ g : AdelicGLn.AdelicGL K n,
      ((AutomorphicForm.uAction (CuspidalSpectrum.uJ (K := K) (n := n) k J) (⟨φ, hs⟩ : ↥(AutomorphicForm.archSmooth K n)) :
        ↥(AutomorphicForm.archSmooth K n)) : AdelicGLn.AdelicGL K n → ℂ) g = ∫ y, φ (g * AutomorphicForm.infEmb K n y) * D y ∂μ) → (∀ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω → ∃ N : ℕ, ∀ Q : Set (AutomorphicForm.archGroup K n), IsCompact Q → ∃ C : ℝ,
    ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i), ∀ kk ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)), ∀ y ∈ Q, ∀ L : ℝ, 1 ≤ L →
      (∀ i, ρ i ≤ L ∧ (ρ i)⁻¹ ≤ L) →
      ‖φ (b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * kk * AutomorphicForm.infEmb K n y)‖ ≤ C * L ^ N) → (∀ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω → ω ⊆ (adelicBorel (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n)) →
    (∀ b ∈ ω, (IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det b) : ℝ) = 1) → ∀ t : ℝ, 0 < t → ∀ (r : ℕ) (hr0 : 0 < r) (hrn : r < n), ∃ N : ℕ, ∀ k : ℕ, ∃ C : ℝ,
      ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i), (∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
        ∏ i, ρ i = 1 → ∀ kk ∈ maxCompact (K := K) (n := n), ∀ R : ℝ, 1 ≤ R → (∀ i j : Fin n, ρ i / ρ j ≤ R) →
          ‖φ (b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * kk)‖ ≤
            C * (ρ ⟨r, hrn⟩ / ρ ⟨r - 1, lt_of_le_of_lt (Nat.sub_le r 1) hrn⟩) ^ k * R ^ N) :=
  GlobalTheory.CompanionTheory.GGPS.smooth_automorphic_open_invariant
