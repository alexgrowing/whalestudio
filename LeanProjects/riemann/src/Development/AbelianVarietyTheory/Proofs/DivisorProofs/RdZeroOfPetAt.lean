import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Formalism.LocalToGlobal.ProjectiveLattices.ReadQuot
import Formalism.LocalToGlobal.ProjectiveLattices.ReadLeaves
import Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoreGoodMatch
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.LocClauseOfUnifPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelMulArchimedeanMemNhdsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfRestrictionsVanishStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.PetDef

open MeasureTheory Formalism.L2.Theta Formalism.BasicNotions.TH ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Topology TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

theorem adelAut_of_gamma {V : HSp D} {X : Comp → Data E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {mu : GA D V → ℂ} {Kf : Subgroup (GA D V)} {th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {hr : V.rank = r} (hχ : ∀ k la γ, γ ∈ (X k).Γ → (X k).χ la γ = 1) (hd : DictIsUnif V dict Kf th hr)
    (hm : MuUnit V dict mu) (hL : DictLoc V dict) (hmc : Continuous mu) : AdelAut V dict mu := by
  intro la P hP
  refine ⟨fun γ hγ g => ?_, ?_⟩
  · obtain ⟨γ', hγ', he⟩ := hd.1 γ hγ g
    have hE := (eqv_holSub X la (holCusp_mem_holSub X la hP)).2 (dict g).1 γ' hγ' (dict g).2 (hd.2.2.2.1 g)
    show mu (γ * g) * P (dict (γ * g)).1 (dict (γ * g)).2 = mu g * P (dict g).1 (dict g).2
    rw [he, hm.1, hm.2.2.1 γ hγ, one_mul]
    show mu g * P (dict g).1 (lact γ' (dict g).2) = _
    rw [hE, hχ _ _ _ hγ', one_mul]
  · rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨N, hN, k, x, hx, hs⟩ := hL g₀
    have hsec : (X k).IsSec (la k) (P k) := (hP k).1.1
    have hPc : ContinuousOn (P k) (X k).dom := hsec.1.continuousOn
    have hc : ContinuousOn (fun g => mu g * P k (x g)) N :=
      hmc.continuousOn.mul (hPc.comp hx fun g hg => (hs g hg).1)
    have heq : (fun g => mu g * P k (x g)) =ᶠ[𝓝 g₀] adel V dict mu P := by
      filter_upwards [hN] with g hg
      obtain ⟨hd', γ, hγ, he⟩ := hs g hg
      show mu g * P k (x g) = mu g * P (dict g).1 (dict g).2
      rw [he]
      show mu g * P k (x g) = mu g * P k (lact γ (x g))
      rw [hsec.2.2 γ hγ (x g) hd', hχ _ _ _ hγ, one_mul]
    exact (hc.continuousAt hN).congr heq

end Gen

section Cover

variable {D : D7} {T : Core D} {j : ℕ}

theorem dictLoc_of_good (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ)
    (hσ : GoodEmb Y.d.c₂ σ) : ∃ th hr, DictIsUnif (D.sp.W j) (Y.dict σ) Y.Kf th hr ∧ DictLoc (D.sp.W j) (Y.dict σ) := by
  obtain ⟨th, hr, hth, hd⟩ := h.dictU σ hσ
  refine ⟨th, hr, hd, ?_⟩
  have hN : 0 < D.host.g 0 * D.host.g 1 * Y.d.pd := by
    rw [h.pd]
    exact Nat.mul_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) (pow_pos (by norm_num) _)
  have hK : Y.Kf ≤ GfC (D.sp.W j) := fun k hk => ((h.levelK k).1 hk).1
  exact GlobalTheory.DictLocTest.locClause_of_unif_places hd hK (GlobalTheory.T.principalLevel_mul_archimedean_mem_nhds D _ _ Y.Kf hN h.levelK) (fun c τ => ⟨_, hth c τ⟩)

theorem muUnit_one (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) :
    MuUnit (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) :=
  ⟨fun _ _ => (mul_one 1).symm, fun _ => norm_one, fun _ _ => rfl, h.unit σ hσ⟩

theorem adelAut_good (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) :
    AdelAut (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) := by
  obtain ⟨th, hr, hd, hL⟩ := dictLoc_of_good Y h σ hσ
  exact adelAut_of_gamma (fun k la γ hγ => GlobalTheory.CovTop.Model.chi_eq_one h σ hσ k la γ hγ) hd (muUnit_one Y h σ hσ) hL
    continuous_const

theorem aeDom_good (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) :
    AeDom Y.U σ (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) := by
  obtain ⟨th, hr, hd, -⟩ := dictLoc_of_good Y h σ hσ
  obtain ⟨hP, hV⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D (D.sp.W j) (D.sp.W_sig j)
  exact aeDom_of_aut Y.d.Xo₂ Y.d.c₂ (adelAut_good Y h σ hσ) (quotSupp_of _ hV hP) (muUnit_one Y h σ hσ) hd

theorem rd_zero_of_petAt (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ)
    (hσ : GoodEmb Y.d.c₂ σ) (G : WTZ D.host.E) (f : Rul Y.d.Xo₂ Y.d.c₂) (hf : f ∈ GlobalTheory.AllWt.cuspW Y.d.Xo₂ Y.d.c₂ Y.U G)
    (h0 : GlobalTheory.AllWt.petAt (Y.U σ) (xiR D) (D.sp.W j) (Y.dict σ) (muQ1 (D.sp.W j)) G f = 0) :
    ∀ k, ∀ z ∈ ((Y.U σ).X k).dom, rdU (Y.U σ) f k z = 0 := by
  have hP : rdU (Y.U σ) f ∈ holSub (Y.U σ).X (GlobalTheory.AllWt.modelWt (Y.U σ) G) := (GlobalTheory.AllWt.mem_cuspW.1 hf).2 σ hσ
  obtain ⟨th, hr, hd, -⟩ := dictLoc_of_good Y h σ hσ
  have hfin := GlobalTheory.AllWt.petE_ne_top (D.sp.W j) (Y.dict σ) (muQ1 (D.sp.W j)) prob_le_one hd.2.2.2.1 hP
  have hE : GlobalTheory.AllWt.petE (D.sp.W j) (Y.dict σ) (muQ1 (D.sp.W j)) (GlobalTheory.AllWt.modelWt (Y.U σ) G) (rdU (Y.U σ) f) = 0 := by
    unfold GlobalTheory.AllWt.petAt at h0
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact absurd h1 (GlobalTheory.AllWt.lieFacZ_pos _ _).ne'
    · exact ((ENNReal.toReal_eq_zero_iff _).1 h1).resolve_right hfin
  have hmeas := aesm_of_holSub (adelMeas_of_aut Y.d.Xo₂ Y.d.c₂ (U := Y.U) (σ := σ) (adelAut_good Y h σ hσ)) _ hP
  have heqn : (fun q : AutQ (D.sp.W j) => GlobalTheory.AllWt.ptN (GlobalTheory.AllWt.modelWt (Y.U σ) G) (rdU (Y.U σ) f) (Y.dict σ q.out)) =
      fun q => ‖onQ (D.sp.W j) (adel (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) (rdU (Y.U σ) f)) q‖ := by
    funext q
    show ((Y.U σ).X _).pnorm _ _ _ = ‖(1 : ℂ) * rdU (Y.U σ) f _ _‖
    rw [pnorm_eq_of_unit _ _ _ _ (h.unit σ hσ q.out), one_mul]
  have hz : onQ (D.sp.W j) (adel (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) (rdU (Y.U σ) f)) =ᵐ[muQ1 (D.sp.W j)] 0 := by
    have h2 : eLpNorm (onQ (D.sp.W j) (adel (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) (rdU (Y.U σ) f))) 2
        (muQ1 (D.sp.W j)) = 0 := by
      rw [← eLpNorm_norm]
      unfold GlobalTheory.AllWt.petE at hE
      rw [heqn] at hE
      exact hE
    exact (eLpNorm_eq_zero_iff hmeas two_ne_zero).1 h2
  exact aeDom_good Y h σ hσ _ _ hP hz

end Cover

theorem nrm_eq_zero : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o →
    2 < Module.finrank ℚ D.host.E / 2 → ∀ (G : WTZ D.host.E) (v : InfinitePlace Y.d.c₂.F) (x : Y.V G),
    Y.nrm G v.embedding x = 0 → x = 0 := by
  intro D T j Y e o h _ G v x h0
  have hσ := goodEmb_goodOf Y.d.c₂ v.embedding
  exact GlobalTheory.T.eq_zero_of_restrictions_vanish D T j Y e o h _ hσ G x (rd_zero_of_petAt Y h _ hσ G x x.2 h0)

end GlobalTheory.PetDef
