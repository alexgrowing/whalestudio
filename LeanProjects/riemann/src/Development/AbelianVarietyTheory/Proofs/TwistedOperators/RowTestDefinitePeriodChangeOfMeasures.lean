import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelGridRationalLeftInvariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawWeilBiActionCommutes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryEmbeddingContinuousMulRational
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal

theorem fd_int_scale {D : D7} {V : HSp D} {μ μ' : Measure (GA D V)} (hμ : μ.IsHaarMeasure) (hμ' : μ'.IsHaarMeasure)
    {s : NNReal} (hs : μ = s • μ') {F F' : Set (GA D V)}
    (h : IsFundamentalDomain (GQ V) F μ) (h' : IsFundamentalDomain (GQ V) F' μ') (f : GA D V → ℂ)
    (hf : ∀ γ ∈ GQ V, ∀ x, f (γ * x) = f x) : ∫ x in F, f x ∂μ = ((s : ℝ) : ℂ) * ∫ x in F', f x ∂μ' := by
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hs
    exact NeZero.ne μ hs
  have h1 : IsFundamentalDomain (GQ V) F μ' := h.mono (by
    rw [hs]; exact Measure.absolutelyContinuous_smul (by exact_mod_cast hs0))
  rw [hs, Measure.restrict_smul, integral_smul_nnreal_measure, h1.setIntegral_eq h' fun γ x => hf γ γ.2 x]
  rw [NNReal.smul_def, Complex.real_smul]

theorem biTheta_slice1 {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {C : WO A S → WO S A' → ℂ}
    (h : IsBiTheta ψ A S A' C) (v : WO S A') : IsThetaFunO ψ A S fun u => C u v where
  quasi := fun γ u => h.quasiL γ u v
  level := by
    obtain ⟨U, hU, hl⟩ := h.levL
    exact ⟨U, hU, fun a ha h0 => hl a ha h0 v⟩
  cont := h.cont.comp (continuous_id.prodMk continuous_const)
  smooth := fun n L hL h0 u => by
    have := h.smooth n L 0 hL continuous_const h0 (fun _ => Matrix.map_zero _ (map_zero (finPart D))) u v
    simpa using this

theorem biTheta_slice2 {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {C : WO A S → WO S A' → ℂ}
    (h : IsBiTheta ψ A S A' C) (u : WO A S) : IsThetaFunO ψ S A' (C u) where
  quasi := fun γ v => h.quasiR γ u v
  level := by
    obtain ⟨U, hU, hl⟩ := h.levR
    exact ⟨U, hU, fun a ha h0 => hl a ha h0 u⟩
  cont := h.cont.comp (continuous_const.prodMk continuous_id)
  smooth := fun n L hL h0 v => by
    have := h.smooth n 0 L continuous_const hL (fun _ => Matrix.map_zero _ (map_zero (finPart D))) h0 u v
    simpa using this

section
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem om_fix_left (W : G.Weil) (p : Pair T) (hp : p.InRange D.R.m) (Y : WO (G.pS p) (G.pT p) → ℂ)
    (hY : IsThetaFunO W.ψ _ _ Y) (g : GA D (G.pS p)) (h : GA D (G.pT p)) (γ : GA D (G.pS p)) (hγ : γ ∈ GQ (G.pS p)) :
    W.om p (γ * g, h) Y 0 = W.om p (g, h) Y 0 := by
  have hw := W.om_is p hp
  have e : ((γ * g, h) : GA D (G.pS p) × GA D (G.pT p)) = (γ, 1) * (g, h) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hw.om_aut γ hγ 1 (one_mem _) _ (hw.om_pres _ Y hY)

theorem om_fix_right (W : G.Weil) (p : Pair T) (hp : p.InRange D.R.m) (Y : WO (G.pS p) (G.pT p) → ℂ)
    (hY : IsThetaFunO W.ψ _ _ Y) (g : GA D (G.pS p)) (h : GA D (G.pT p)) (γ : GA D (G.pT p)) (hγ : γ ∈ GQ (G.pT p)) :
    W.om p (g, γ * h) Y 0 = W.om p (g, h) Y 0 := by
  have hw := W.om_is p hp
  have e : ((g, γ * h) : GA D (G.pS p) × GA D (G.pT p)) = (1, γ) * (g, h) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hw.om_aut 1 (one_mem _) γ hγ _ (hw.om_pres _ Y hY)

theorem mid_theta (W : G.Weil) (t : T) (j : ℕ) (hj : j + 2 ≤ D.R.m)
    (C : WO (G.V (.top j)) (G.V (.top (j + 1))) → WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) → ℂ)
    (hC : IsBiTheta W.ψ _ _ _ C) (h₀ : GA D (G.V (.top j))) (h₁ : GA D (G.V (.top (j + 1)))) :
    IsThetaFunO W.ψ (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) fun v => W.om (.top t j) (h₀, h₁) (fun u => C u v) 0 :=
  biTheta_slice2 ((GlobalTheory.SeeSaw.biAct_all D W.ψ _ _ _ _ _ _ _ (W.om (.top t j)) (W.om (.top t (j + 1)))
    (W.om_is (.top t j) (show j + 1 ≤ D.R.m by omega)) (W.om_is (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega)) C hC).1 (h₀, h₁)) 0
end

section
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem int_scale {M M' : Vol G} {s : Node → NNReal} (hM : IsHaarDef M) (hM' : IsHaarDef M') (hs : Scales M M' s)
    {X : Node} (hX : DefNode D.R.m X) (hX' : X ≠ .top D.R.m) (f : GA D (G.V X) → ℂ)
    (hf : ∀ γ ∈ GQ (G.V X), ∀ x, f (γ * x) = f x) :
    ∫ x in M.fd X, f x ∂M.ν X = ((s X : ℝ) : ℂ) * ∫ x in M'.fd X, f x ∂M'.ν X := by
  obtain ⟨h1, h2⟩ := hM X hX hX'
  obtain ⟨h1', h2'⟩ := hM' X hX hX'
  exact fd_int_scale h1 h1' (hs X hX hX') h2 h2' f hf

theorem row_scale (W : G.Weil) {M M' : Vol G} {s : Node → NNReal} (hM : IsHaarDef M) (hM' : IsHaarDef M') (hs : Scales M M' s)
    (F : Fn G (.grid 0 D.R.m)) (hF : ∀ γ ∈ GQ (G.V (.grid 0 D.R.m)), ∀ x, F (γ * x) = F x) :
    ∀ n, n ≤ D.R.m → ∀ g : ∀ i : Fin n, Sch G (.right i D.R.m), (∀ i, IsThetaFunO W.ψ _ _ (g i)) →
      liftP W M (rowPath T D.R.m n) (rowFam D.R.m n g) F =
        (∏ i ∈ Finset.range n, ((s (.grid i D.R.m) : ℝ) : ℂ)) • liftP W M' (rowPath T D.R.m n) (rowFam D.R.m n g) F ∧
      ∀ γ ∈ GQ (G.V (.grid n D.R.m)), ∀ x, liftP W M' (rowPath T D.R.m n) (rowFam D.R.m n g) F (γ * x) =
        liftP W M' (rowPath T D.R.m n) (rowFam D.R.m n g) F x := by
  intro n
  induction n with
  | zero =>
    intro _ g _
    refine ⟨?_, hF⟩
    show F = (∏ i ∈ Finset.range 0, ((s (.grid i D.R.m) : ℝ) : ℂ)) • F
    rw [Finset.prod_range_zero, one_smul]
  | succ n ih =>
    intro hn g hg
    obtain ⟨e, hinv⟩ := ih (by omega) (fun i => g i.castSucc) (fun i => hg i.castSucc)
    have hp : Pair.InRange D.R.m (Pair.chi n D.R.m : Pair T) := show n + 1 ≤ D.R.m ∧ D.R.m ≤ D.R.m from ⟨hn, le_rfl⟩
    have hθ : IsThetaFunO W.ψ (G.pS (.chi n D.R.m)) (G.pT (.chi n D.R.m)) (g (Fin.last n)) := hg (Fin.last n)
    refine ⟨?_, ?_⟩
    · show liftA W M (.right n D.R.m) (g (Fin.last n))
          (liftP W M (rowPath T D.R.m n) (rowFam D.R.m n fun i => g i.castSucc) F) =
        _ • liftA W M' (.right n D.R.m) (g (Fin.last n))
          (liftP W M' (rowPath T D.R.m n) (rowFam D.R.m n fun i => g i.castSucc) F)
      rw [e, liftA_smul]
      funext h
      simp only [Pi.smul_apply, smul_eq_mul, liftA_apply]
      rw [int_scale hM hM' hs (X := (Arrow.right n D.R.m : Arrow T).src) (show n ≤ D.R.m ∧ D.R.m = D.R.m from ⟨by omega, rfl⟩)
        (fun e => by cases e) _ ?_, Finset.prod_range_succ]
      · ring
      · intro γ hγ x
        show W.ker (.chi n D.R.m) _ (γ * x) h * _ = W.ker (.chi n D.R.m) _ x h * _
        rw [hinv γ hγ x]
        congr 1
        have := ker_rat_left W _ hp _ hθ γ hγ 1 (one_mem _) x h
        rwa [one_mul] at this
    · intro γ hγ x
      show liftA W M' (.right n D.R.m) (g (Fin.last n))
          (liftP W M' (rowPath T D.R.m n) (rowFam D.R.m n fun i => g i.castSucc) F) (γ * x) =
        liftA W M' (.right n D.R.m) (g (Fin.last n))
          (liftP W M' (rowPath T D.R.m n) (rowFam D.R.m n fun i => g i.castSucc) F) x
      simp only [liftA_apply]
      congr 1; funext g'; congr 1
      have := ker_rat_left W _ hp _ hθ 1 (one_mem _) γ hγ g' x
      rwa [one_mul] at this

theorem biL_inv (W : G.Weil) (M : Vol G) (t : T) (j : ℕ) (hj : j + 2 ≤ D.R.m) (φ : Fn G (.top j))
    (C : WO (G.V (.top j)) (G.V (.top (j + 1))) → WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) → ℂ)
    (hC : IsBiTheta W.ψ _ _ _ C) :
    ∀ γ ∈ GQ (G.V (.top (j + 1 + 1))), ∀ x, biL W M t j φ C (γ * x) = biL W M t j φ C x := by
  intro γ hγ x
  unfold biL
  congr 1; funext h₁; congr 1; funext h₀; congr 1
  exact om_fix_right W (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega) _ (mid_theta W t j hj C hC h₀ h₁) h₁ x γ hγ

theorem biL_scale (W : G.Weil) {M M' : Vol G} {s : Node → NNReal} (hM : IsHaarDef M) (hM' : IsHaarDef M') (hs : Scales M M' s)
    (t : T) (j : ℕ) (hj : j + 2 ≤ D.R.m) (φ : Fn G (.top j)) (hφ : ∀ γ ∈ GQ (G.V (.top j)), ∀ x, φ (γ * x) = φ x)
    (C : WO (G.V (.top j)) (G.V (.top (j + 1))) → WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) → ℂ)
    (hC : IsBiTheta W.ψ _ _ _ C) :
    biL W M t j φ C = (((s (.top j) : ℝ) : ℂ) * ((s (.top (j + 1)) : ℝ) : ℂ)) • biL W M' t j φ C := by
  funext h₂
  have hA : Pair.InRange D.R.m (Pair.top t j : Pair T) := show j + 1 ≤ D.R.m by omega
  have hB : Pair.InRange D.R.m (Pair.top t (j + 1) : Pair T) := show j + 1 + 1 ≤ D.R.m by omega
  have inner : ∀ h₁, ∫ h₀ in M.fd (.top j), φ h₀ * W.om (.top t (j + 1)) (h₁, h₂)
      (fun v => W.om (.top t j) (h₀, h₁) (fun u => C u v) 0) 0 ∂M.ν (.top j) = ((s (.top j) : ℝ) : ℂ) *
      ∫ h₀ in M'.fd (.top j), φ h₀ * W.om (.top t (j + 1)) (h₁, h₂)
      (fun v => W.om (.top t j) (h₀, h₁) (fun u => C u v) 0) 0 ∂M'.ν (.top j) := fun h₁ =>
    int_scale hM hM' hs (X := .top j) (show j ≤ D.R.m by omega) (fun e => by injection e; omega) _ fun γ hγ h₀ => by
      have e : (fun v => W.om (.top t j) (γ * h₀, h₁) (fun u => C u v) 0) = fun v => W.om (.top t j) (h₀, h₁) (fun u => C u v) 0 :=
        funext fun v => om_fix_left W _ hA _ (biTheta_slice1 hC v) h₀ h₁ γ hγ
      simp only [e, hφ γ hγ h₀]
  show ∫ h₁ in M.fd (.top (j + 1)), (∫ h₀ in M.fd (.top j), φ h₀ * W.om (.top t (j + 1)) (h₁, h₂)
      (fun v => W.om (.top t j) (h₀, h₁) (fun u => C u v) 0) 0 ∂M.ν (.top j)) ∂M.ν (.top (j + 1)) =
    _ * ∫ h₁ in M'.fd (.top (j + 1)), (∫ h₀ in M'.fd (.top j), φ h₀ * W.om (.top t (j + 1)) (h₁, h₂)
      (fun v => W.om (.top t j) (h₀, h₁) (fun u => C u v) 0) 0 ∂M'.ν (.top j)) ∂M'.ν (.top (j + 1))
  simp_rw [inner]
  rw [integral_const_mul, int_scale hM hM' hs (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega) (fun e => by injection e; omega) _ ?_]
  · ring
  · intro γ hγ h₁
    congr 1; funext h₀; congr 1
    have e : (fun v => W.om (.top t j) (h₀, γ * h₁) (fun u => C u v) 0) = fun v => W.om (.top t j) (h₀, h₁) (fun u => C u v) 0 :=
      funext fun v => om_fix_right W _ hA _ (biTheta_slice1 hC v) h₀ h₁ γ hγ
    rw [e]
    exact om_fix_left W (.top t (j + 1)) hB _ (mid_theta W t j hj C hC h₀ h₁) h₁ h₂ γ hγ

theorem biL_smul (W : G.Weil) (M : Vol G) (t : T) (j : ℕ) (φ : Fn G (.top j))
    (C : WO (G.V (.top j)) (G.V (.top (j + 1))) → WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) → ℂ) (c : ℂ) :
    biL W M t j (c • φ) C = c • biL W M t j φ C := by
  funext h₂
  simp only [biL, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem jPer_smul_F (W : G.Weil) (M : Vol G) (t : T) (C : BiFam G) (F : Fn G (.grid D.R.m D.R.m)) (c : ℂ) :
    ∀ σ j (hj : j + 2 * σ + 2 = D.R.m) φ, jPer W M t C (c • F) σ j hj φ = c * jPer W M t C F σ j hj φ
  | 0, j, hj, φ => by
    simp only [jPer, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  | σ + 1, j, hj, φ => jPer_smul_F W M t C F c σ (j + 1 + 1) (by omega) _

theorem jPer_smul_φ (W : G.Weil) (M : Vol G) (t : T) (C : BiFam G) (F : Fn G (.grid D.R.m D.R.m)) :
    ∀ σ j (hj : j + 2 * σ + 2 = D.R.m) φ (c : ℂ), jPer W M t C F σ j hj (c • φ) = c * jPer W M t C F σ j hj φ
  | 0, j, hj, φ, c => by
    show ∫ h' in M.fd (.grid D.R.m D.R.m), F h' * biL W M t j (c • φ) (C j) (GlobalTheory.RowChain.topEmb G _ h') ∂M.ν (.grid D.R.m D.R.m) = _
    rw [biL_smul]
    simp only [jPer, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul]
  | σ + 1, j, hj, φ, c => by
    show jPer W M t C F σ (j + 1 + 1) _ (biL W M t j (c • φ) (C j)) = c * jPer W M t C F σ (j + 1 + 1) _ (biL W M t j φ (C j))
    rw [biL_smul]
    exact jPer_smul_φ W M t C F σ (j + 1 + 1) _ _ c

theorem topEmb_rat {n : ℕ} (h : D.R.m = n) (γ : GA D (G.V (.grid D.R.m D.R.m))) (hγ : γ ∈ GQ _)
    (x : GA D (G.V (.grid D.R.m D.R.m))) :
    ∃ γ' ∈ GQ (G.V (.top n)), GlobalTheory.RowChain.topEmb G h (γ * x) = γ' * GlobalTheory.RowChain.topEmb G h x := by
  subst h
  exact ⟨_, GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_rational _ γ hγ, GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul _ γ x⟩

theorem jPer_scale (W : G.Weil) {M M' : Vol G} {s : Node → NNReal} (hM : IsHaarDef M) (hM' : IsHaarDef M') (hs : Scales M M' s)
    (t : T) (C : BiFam G) (hC : ∀ k, Even k → k < D.R.m → IsBiTheta W.ψ _ _ _ (C k)) (F : Fn G (.grid D.R.m D.R.m))
    (hF : ∀ γ ∈ GQ (G.V (.grid D.R.m D.R.m)), ∀ x, F (γ * x) = F x) :
    ∀ σ j (hj : j + 2 * σ + 2 = D.R.m), Even j → ∀ φ : Fn G (.top j), (∀ γ ∈ GQ (G.V (.top j)), ∀ x, φ (γ * x) = φ x) →
      jPer W M t C F σ j hj φ = ((∏ k ∈ Finset.Ico j D.R.m, ((s (.top k) : ℝ) : ℂ)) * ((s (.grid D.R.m D.R.m) : ℝ) : ℂ)) *
        jPer W M' t C F σ j hj φ
  | 0, j, hj, hev, φ, hφ => by
    have hC' := hC j hev (by omega)
    show ∫ h' in M.fd (.grid D.R.m D.R.m), F h' * biL W M t j φ (C j) (GlobalTheory.RowChain.topEmb G _ h') ∂M.ν (.grid D.R.m D.R.m) =
      _ * ∫ h' in M'.fd (.grid D.R.m D.R.m), F h' * biL W M' t j φ (C j) (GlobalTheory.RowChain.topEmb G _ h') ∂M'.ν (.grid D.R.m D.R.m)
    rw [biL_scale W hM hM' hs t j (by omega) φ hφ _ hC']
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ (((s (.top j) : ℝ) : ℂ) * _), integral_const_mul]
    rw [int_scale hM hM' hs (X := .grid D.R.m D.R.m) ⟨le_rfl, rfl⟩ (by simp) _ ?_]
    · have e : Finset.Ico j D.R.m = {j, j + 1} := by
        ext k; simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]; omega
      rw [e, Finset.prod_pair (by omega)]
      ring
    · intro γ hγ x
      obtain ⟨γ', hγ', e⟩ := topEmb_rat (G := G) (show D.R.m = j + 1 + 1 by omega) γ hγ x
      rw [e, hF γ hγ x, biL_inv W M' t j (by omega) φ _ hC' γ' hγ']
  | σ + 1, j, hj, hev, φ, hφ => by
    have hC' := hC j hev (by omega)
    show jPer W M t C F σ (j + 1 + 1) _ (biL W M t j φ (C j)) = _ * jPer W M' t C F σ (j + 1 + 1) _ (biL W M' t j φ (C j))
    rw [biL_scale W hM hM' hs t j (by omega) φ hφ _ hC', jPer_smul_φ,
      jPer_scale W hM hM' hs t C hC F hF σ (j + 1 + 1) _ (by rw [add_assoc]; exact hev.add even_two) _
        (biL_inv W M' t j (by omega) φ _ hC'),
      Finset.prod_eq_prod_Ico_succ_bot (by omega : j < D.R.m), Finset.prod_eq_prod_Ico_succ_bot (by omega : j + 1 < D.R.m)]
    ring

theorem per_scale (W : G.Weil) {M M' : Vol G} {s : Node → NNReal} (hM : IsHaarDef M) (hM' : IsHaarDef M') (hs : Scales M M' s)
    (t : T) (φ : Fn G (.top 0)) (F : Fn G (.grid 0 D.R.m)) (hφ : GlobalTheory.Unf.IsContAut _ φ) (hF : GlobalTheory.Unf.IsContAut _ F)
    (C : BiFam G) (f : SchRow G) (hg : Good W C f) (P : PolRow G) :
    per W M t C f P φ F = sProd D s * per W M' t C f P φ F := by
  have hθ : ∀ i : Fin D.R.m, IsThetaFunO W.ψ _ _ (W.fock (.chi i D.R.m) (f i) (P i)) := fun i =>
    GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ (hg.2 i) (P i)
  obtain ⟨e1, hinv⟩ := row_scale W hM hM' hs F hF.1 D.R.m le_rfl _ hθ
  unfold per
  rw [e1, jPer_smul_F, jPer_scale W hM hM' hs t C hg.1 _ hinv _ 0 _ ⟨0, rfl⟩ φ hφ.1, sProd,
    Finset.prod_range_succ, Finset.range_eq_Ico]
  ring

end

theorem volAt_big : Big fun ch => VolAt ch := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intros
  intro t M M' s hM hM' hs φ F hφ hF C f hg P
  exact per_scale _ hM hM' hs t φ F hφ hF C f hg P

end GlobalTheory.RowVal
