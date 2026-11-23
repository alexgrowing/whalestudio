import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalDualComplementSandwichStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFundamentalDomainEqIteratedDecompStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotientSummableStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffSmearContinuousPeriodicFubiniStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedIntegralDecompContinuousPeriodicStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMean

private lemma symplO_eq_symplOH_add_symplOH {D : D7} (V W : HSp D) (x y : WO V W) :
    symplO V W x y = symplOH V W x y + symplOH V W x y := by
  unfold symplOH
  rw [← add_mul, ← map_add, add_halves, map_one, one_mul]

private lemma symplOH_swap' {D : D7} (V W : HSp D) (x y : WO V W) :
    symplOH V W y x = -symplOH V W x y := by
  unfold symplOH
  rw [GlobalTheory.OrientedHeis.symplO_skew, mul_neg]

theorem heisO_rat_add {D : D7} (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (G : WO V W → ℂ)
    (hG : IsThetaFunO ψ V W G) (γ₁ : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (ξ u : WO V W)
    (h : symplO V W (ratW W V γ₁) ξ = 0) :
    heisO ψ V W (ratW W V γ₁ + ξ) G u = ψ (symplO V W u (ratW W V γ₁)) * heisO ψ V W ξ G u := by
  have hq := hG.quasi γ₁ (u + ξ)
  have h0 : symplOH V W (ratW W V γ₁) ξ = 0 := by
    unfold symplOH
    rw [h, mul_zero]
  simp only [heisO]
  rw [show u + (ratW W V γ₁ + ξ) = ratW W V γ₁ + (u + ξ) by abel, hq, symplO_eq_symplOH_add_symplOH,
    GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right, h0,
    symplOH_swap' V W u (ratW W V γ₁), add_zero, neg_neg, ← mul_assoc, ← mul_assoc,
    ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  abel

private lemma symplO_add_left_twisted_operators {D : D7} (V W : HSp D) (x x' y : WO V W) :
    symplO V W (x + x') y = symplO V W x y + symplO V W x' y := by
  rw [symplO_eq_symplOH_add_symplOH V W (x + x') y, symplO_eq_symplOH_add_symplOH V W x y, symplO_eq_symplOH_add_symplOH V W x' y,
    GlobalTheory.OrientedHeis.symplOH_add_left]
  abel

private lemma symplO_add_right_twisted_operators {D : D7} (V W : HSp D) (x y y' : WO V W) :
    symplO V W x (y + y') = symplO V W x y + symplO V W x y' := by
  rw [symplO_eq_symplOH_add_symplOH V W x (y + y'), symplO_eq_symplOH_add_symplOH V W x y, symplO_eq_symplOH_add_symplOH V W x y',
    GlobalTheory.OrientedHeis.symplOH_add_right]
  abel

private lemma symplO_zero_left_twisted_operators {D : D7} (V W : HSp D) (y : WO V W) : symplO V W 0 y = 0 := by
  rw [symplO_eq_symplOH_add_symplOH, GlobalTheory.MixModel.symplOH_zero_left, add_zero]

private lemma symplO_zero_right_twisted_operators {D : D7} (V W : HSp D) (x : WO V W) : symplO V W x 0 = 0 := by
  rw [symplO_eq_symplOH_add_symplOH, GlobalTheory.MixModel.symplOH_zero_right, add_zero]

private lemma continuous_emb_twisted_operators {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) : Continuous (emb V W P Q) :=
  GlobalTheory.MixModel.continuous_sandwich (GlobalTheory.MixModel.rat P) (GlobalTheory.MixModel.rat Q)

private lemma emb_rat_eq_ratW_mul {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (r : Matrix (Fin a) (Fin b) D.host.E) :
    emb V W P Q (GlobalTheory.MixModel.rat r) = ratW W V (P * r * Q) := by
  rw [GlobalTheory.MixModel.ratW_eq, GlobalTheory.MixModel.rat_mul, GlobalTheory.MixModel.rat_mul]
  rfl

private lemma continuous_symplO_comp {D : D7} (V W : HSp D) {X : Type} [TopologicalSpace X] {x y : X → WO V W}
    (hx : Continuous x) (hy : Continuous y) : Continuous fun t => symplO V W (x t) (y t) := by
  simp only [symplO_eq_symplOH_add_symplOH]
  exact (GlobalTheory.OrientedHeis.continuous_symplOH hx hy).add (GlobalTheory.OrientedHeis.continuous_symplOH hx hy)

set_option maxHeartbeats 4000000 in

theorem integral_coef_eq_mul_meanX : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (k : ℕ) (B : Fin k → Matrix (Fin W.rank) (Fin V.rank) D.host.E), (∀ (z : Mx D 1 k) (y : Mx D a b), symplO V W (GlobalTheory.IsoMean.cplx V W B z) (GlobalTheory.IsoMean.emb V W P Q y) = 0) → (∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∃ (z : Mx D 1 k) (y : Mx D a b), x = GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y) → (∀ (z : Mx D 1 k) (y : Mx D a b), GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y = 0 → z = 0 ∧ y = 0) → (∀ (z : Mx D 1 k) (y : Mx D a b), GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y ∈ ratL W V → z ∈ GlobalTheory.MixModel.ratMx D 1 k ∧ y ∈ GlobalTheory.MixModel.ratMx D a b) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 → ∀ (η : Measure (Mx D 1 k)) (𝓩 : Set (Mx D 1 k)), η.IsAddHaarMeasure → IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D 1 k) 𝓩 η → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → (∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Integrable (fun y => ∫ u in 𝓕, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) μ) → ∃ κ : ℂ, κ ≠ 0 ∧ ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → ∫ y, (∫ u in 𝓕, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) ∂μ = κ * ∫ z in 𝓩, GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 G (GlobalTheory.IsoMean.cplx V W B z) * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 G' (GlobalTheory.IsoMean.cplx V W B z)) ∂η := by
  intro D V W a b P Q hP hQ hiso k B hZX hperp hdir hrat ψ hψ μ 𝓨 hμ η 𝓩 hη h𝓩 ν 𝓕 hν h𝓕 hint
  obtain ⟨hTA, hLC, hSC, hT2, hDisc, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D a b
  obtain ⟨hμH, hμF, hμ1⟩ : μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain (↥(GlobalTheory.MixModel.ratMx D a b)) 𝓨 μ ∧
    μ 𝓨 = 1 := id hμ
  have := hTA
  have := hLC
  have := hSC
  have := hT2
  have := hDisc
  obtain ⟨P', Q', hc1, hc2, hc3, hc4⟩ := GlobalTheory.T.exists_rational_dual_complement_sandwich D V W a b P Q hP hQ ψ hψ
  have hψc : IsCharAF D.host.F ψ := hψ.1
  have hcX := continuous_emb_twisted_operators V W P Q
  have hcX' := continuous_emb_twisted_operators V W P' Q'

  have hratX : ∀ (P₁ : Matrix (Fin W.rank) (Fin a) D.host.E) (Q₁ : Matrix (Fin b) (Fin V.rank) D.host.E),
      ∀ r ∈ GlobalTheory.MixModel.ratMx D a b, emb V W P₁ Q₁ r ∈ ratL W V := by
    intro P₁ Q₁ r hr
    obtain ⟨r₀, rfl⟩ := GlobalTheory.MixModel.mem_ratMx.1 hr
    rw [emb_rat_eq_ratW_mul]
    exact ⟨P₁ * r₀ * Q₁, rfl⟩
  have hratZ : ∀ z ∈ GlobalTheory.MixModel.ratMx D 1 k, cplx V W B z ∈ ratL W V := by
    intro z hz
    obtain ⟨z₀, rfl⟩ := GlobalTheory.MixModel.mem_ratMx.1 hz
    rw [show GlobalTheory.MixModel.rat z₀ = z₀.map (incA D) from rfl, cplx_rat]
    exact ⟨_, rfl⟩

  have hspan : ∀ x : WO V W, ∃ s z y, x = emb V W P' Q' s + cplx V W B z + emb V W P Q y := by
    intro x
    obtain ⟨s, hs⟩ := hc1 x
    obtain ⟨z, y, hzy⟩ := hperp _ hs
    refine ⟨s, z, y, ?_⟩
    rw [add_assoc, ← hzy]
    abel
  have hdir3 : ∀ s z y, emb V W P' Q' s + cplx V W B z + emb V W P Q y = 0 → s = 0 ∧ z = 0 ∧ y = 0 := by
    intro s z y h0
    have hs : ∀ y', symplO V W (emb V W P' Q' s) (emb V W P Q y') = 0 := by
      intro y'
      have h1 := congrArg (fun w => symplO V W w (emb V W P Q y')) h0
      simp only [symplO_add_left_twisted_operators, hZX, hiso, add_zero, symplO_zero_left_twisted_operators] at h1
      exact h1
    obtain rfl := hc2 s hs
    rw [emb_zero, zero_add] at h0
    exact ⟨rfl, hdir z y h0⟩
  have hriff : ∀ s z y, emb V W P' Q' s + cplx V W B z + emb V W P Q y ∈ ratL W V ↔
      s ∈ GlobalTheory.MixModel.ratMx D a b ∧ z ∈ GlobalTheory.MixModel.ratMx D 1 k ∧ y ∈ GlobalTheory.MixModel.ratMx D a b := by
    intro s z y
    constructor
    · intro hw
      have hs : s ∈ GlobalTheory.MixModel.ratMx D a b := by
        refine (hc3 s).1 fun γ hγ => ?_
        have h1 := ((GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ V W _).2 hw) _ (hratX P Q γ hγ)
        simpa only [symplO_add_left_twisted_operators, hZX, hiso, add_zero] using h1
      refine ⟨hs, hrat z y ?_⟩
      have h2 := (ratL W V).sub_mem hw (hratX P' Q' s hs)
      rwa [add_assoc, add_sub_cancel_left] at h2
    · rintro ⟨hs, hz, hy⟩
      exact (ratL W V).add_mem ((ratL W V).add_mem (hratX P' Q' s hs) (hratZ z hz)) (hratX P Q y hy)
  obtain ⟨κ, hκ0, hκ⟩ := GlobalTheory.T.integral_fundamentalDomain_eq_iterated_decomp D V W a b k (emb V W P' Q') (emb V W P Q) (cplx V W B) hcX'
    (continuous_cplx V W B) hcX (emb_add V W P' Q') (cplx_add V W B) (emb_add V W P Q) hspan hdir3 hriff
    μ 𝓨 hμ η 𝓩 hη h𝓩 ν 𝓕 hν h𝓕
  refine ⟨(κ : ℂ), by exact_mod_cast hκ0.ne', ?_⟩
  intro G G' hG hG'
  obtain ⟨hTc, hTper, hTfub⟩ := GlobalTheory.T.thetaMatrixCoeff_smear_continuous_periodic_fubini D V W a b P Q ψ hψ μ 𝓨 hμ ν 𝓕 hν h𝓕 G G' hG hG'
  obtain ⟨hΦc, hΦper⟩ := GlobalTheory.T.iteratedIntegral_decomp_continuous_periodic D V W a b k (emb V W P' Q') (emb V W P Q) (cplx V W B) hcX'
    (continuous_cplx V W B) hcX (emb_add V W P' Q') (hratX P' Q') μ 𝓨 hμ η 𝓩 hη h𝓩 _ hTc hTper
  beta_reduce at hΦc hΦper

  have : BorelSpace (Mx D a b) := ⟨rfl⟩
  have : MeasurableAdd (Mx D a b) :=
    ⟨fun c => (continuous_const_add c).measurable, fun c => (continuous_add_const c).measurable⟩
  have : MeasurableConstVAdd ↥(GlobalTheory.MixModel.ratMx D a b) (Mx D a b) :=
    ⟨fun g => (continuous_const_add (g : Mx D a b)).measurable⟩
  have : Countable ↥(GlobalTheory.MixModel.ratMx D a b) :=
    TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hsr : (Measure.sum fun γ : ↥(GlobalTheory.MixModel.ratMx D a b) => μ.restrict ((fun x => γ +ᵥ x) '' 𝓨)) = μ :=
    hμF.sum_restrict
  have hHS : HasSum (fun γ : ↥(GlobalTheory.MixModel.ratMx D a b) =>
      ∫ ξ in 𝓨, (∫ u in 𝓕, heisO ψ V W (emb V W P Q (γ +ᵥ ξ)) G u * star (G' u) ∂ν) ∂μ)
      (∫ y, (∫ u in 𝓕, heisO ψ V W (emb V W P Q y) G u * star (G' u) ∂ν) ∂μ) := by
    have h1 := MeasureTheory.hasSum_integral_measure
      (f := fun y => ∫ u in 𝓕, heisO ψ V W (emb V W P Q y) G u * star (G' u) ∂ν)
      (μ := fun γ : ↥(GlobalTheory.MixModel.ratMx D a b) => μ.restrict ((fun x => γ +ᵥ x) '' 𝓨))
      (by rw [hsr]; exact hint G G' hG hG')
    rw [hsr] at h1
    have e : ∀ γ : ↥(GlobalTheory.MixModel.ratMx D a b),
        ∫ y in (fun x => γ +ᵥ x) '' 𝓨, (∫ u in 𝓕, heisO ψ V W (emb V W P Q y) G u * star (G' u) ∂ν) ∂μ =
          ∫ ξ in 𝓨, (∫ u in 𝓕, heisO ψ V W (emb V W P Q (γ +ᵥ ξ)) G u * star (G' u) ∂ν) ∂μ :=
      fun γ => (MeasureTheory.measurePreserving_add_left μ (γ : Mx D a b)).setIntegral_image_emb
        (measurableEmbedding_const_vadd (γ : Mx D a b)) _ 𝓨
    simp only [e] at h1
    exact h1

  have hterm : ∀ γ : ↥(GlobalTheory.MixModel.ratMx D a b),
      ∫ ξ in 𝓨, (∫ u in 𝓕, heisO ψ V W (emb V W P Q (γ +ᵥ ξ)) G u * star (G' u) ∂ν) ∂μ =
        (κ : ℂ) * ∫ s in 𝓨, ψ (symplO V W (emb V W P' Q' s) (emb V W P Q γ)) *
          (∫ z in 𝓩, (∫ y in 𝓨, (∫ ξ in 𝓨, heisO ψ V W (emb V W P Q ξ) G
            (emb V W P' Q' s + cplx V W B z + emb V W P Q y) *
              star (G' (emb V W P' Q' s + cplx V W B z + emb V W P Q y)) ∂μ) ∂μ) ∂η) ∂μ := by
    intro γ
    obtain ⟨γ₀, hγ₀⟩ := GlobalTheory.MixModel.mem_ratMx.1 γ.2
    have hγr : emb V W P Q γ = ratW W V (P * γ₀ * Q) := by rw [← hγ₀, emb_rat_eq_ratW_mul]
    have e1 : ∀ ξ u, heisO ψ V W (emb V W P Q (γ +ᵥ ξ)) G u * star (G' u) =
        ψ (symplO V W u (emb V W P Q γ)) * (heisO ψ V W (emb V W P Q ξ) G u * star (G' u)) := by
      intro ξ u
      rw [show (γ +ᵥ ξ : Mx D a b) = (γ : Mx D a b) + ξ from rfl, emb_add, hγr,
        heisO_rat_add V W ψ G hG (P * γ₀ * Q) _ u (by rw [← hγr]; exact hiso _ _), mul_assoc]
    have hφc : Continuous fun u => ψ (symplO V W u (emb V W P Q γ)) :=
      hψc.1.comp (continuous_symplO_comp V W continuous_id continuous_const)
    simp_rw [e1]
    rw [hTfub _ hφc (fun u => (hψc.2.1 _).le)]
    have h3 := hκ (fun u => ψ (symplO V W u (emb V W P Q γ)) *
        ∫ ξ in 𝓨, heisO ψ V W (emb V W P Q ξ) G u * star (G' u) ∂μ) (hφc.mul hTc) (by
      intro δ hδ u
      rw [symplO_add_left_twisted_operators, AddChar.map_add_eq_mul,
        (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ V W δ).2 hδ _ (hratX P Q γ γ.2), one_mul, hTper δ hδ u])
    beta_reduce at h3
    rw [h3]
    congr 1
    refine congrArg (fun F : Mx D a b → ℂ => ∫ s in 𝓨, F s ∂μ) (funext fun s => ?_)
    simp only [symplO_add_left_twisted_operators, hZX, hiso, add_zero]
    simp_rw [MeasureTheory.integral_const_mul]
  have hκne : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ0.ne'
  have hsum := (summable_mul_left_iff hκne).1 (by simpa only [hterm] using hHS.summable)
  have hF := GlobalTheory.T.fourierInversion_zero_compactQuotient_summable (Mx D a b) (GlobalTheory.MixModel.ratMx D a b) K hK hKc (↥(GlobalTheory.MixModel.ratMx D a b))
    (fun γ s => ψ (symplO V W (emb V W P' Q' s) (emb V W P Q γ)))
    (fun γ => hψc.1.comp (continuous_symplO_comp V W hcX' continuous_const))
    (by intro γ x y; simp only [emb_add, symplO_add_left_twisted_operators, AddChar.map_add_eq_mul])
    (by intro γ δ x; simp only [AddSubgroup.coe_add, emb_add, symplO_add_right_twisted_operators, AddChar.map_add_eq_mul])
    (by intro x; simp only [ZeroMemClass.coe_zero, emb_zero, symplO_zero_right_twisted_operators, AddChar.map_zero_eq_one])
    (fun γ x => hψc.2.1 _)
    (fun x => ⟨fun h => (hc3 x).1 fun γ hγ => h ⟨γ, hγ⟩, fun h γ => (hc3 x).2 h γ γ.2⟩)
    (fun γ h => Subtype.ext (hc4 γ γ.2 h)) μ 𝓨 hμH hμF hμ1 _ hΦc hΦper hsum
  beta_reduce at hF
  rw [← hHS.tsum_eq, tsum_congr hterm, tsum_mul_left, hF]
  congr 1

  refine congrArg (fun F : Mx D 1 k → ℂ => ∫ z in 𝓩, F z ∂η) (funext fun z => ?_)
  simp only [emb_zero, zero_add]
  have e2 : ∀ y ξ, heisO ψ V W (emb V W P Q ξ) G (cplx V W B z + emb V W P Q y) =
      G (emb V W P Q ξ + (emb V W P Q y + cplx V W B z)) := by
    intro y ξ
    have h0 : symplOH V W (cplx V W B z + emb V W P Q y) (emb V W P Q ξ) = 0 := by
      unfold symplOH
      rw [symplO_add_left_twisted_operators, hZX, hiso, add_zero, mul_zero]
    simp only [heisO, h0, AddChar.map_zero_eq_one, one_mul]
    congr 1
    abel
  have e3 : ∀ y, ∫ ξ in 𝓨, G (emb V W P Q ξ + (emb V W P Q y + cplx V W B z)) ∂μ =
      meanX V W P Q μ 𝓨 G (cplx V W B z) :=
    fun y => meanX_translate D V W a b P Q hiso ψ hψ μ 𝓨 hμ G hG (cplx V W B z) (hZX z) y
  simp_rw [e2, MeasureTheory.integral_mul_const, e3, MeasureTheory.integral_const_mul]
  congr 1
  have e4 : ∀ f : Mx D a b → ℂ, ∫ y in 𝓨, star (f y) ∂μ = star (∫ y in 𝓨, f y ∂μ) :=
    fun f => integral_conj
  rw [e4]
  refine congrArg star (congrArg (fun F : Mx D a b → ℂ => ∫ y in 𝓨, F y ∂μ) (funext fun y => ?_))
  rw [add_comm]

end GlobalTheory.IsoMean

end
