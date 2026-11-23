import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TowerAtPre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfOrderDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EasyInputs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsInfFamFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharOfTrace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodParParBLast

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def comL (L : LevCh D Unit) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (P : LevelP L.Pg D.R.r ℂ) : Com D :=
  ⟨θ, ψ, L.mu (), L.eta, L.Pg, P, L.chi⟩

theorem mem_S {L : LevCh D Unit} (hL : L.Is ()) (θ ψ P) (k : Fin 2) (Q : Pl D.host.E)
    (hk : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal) : Q.under (𝓞 D.host.F) ∈ (comL L θ ψ P).S := by
  classical
  unfold Com.S
  rw [Finset.mem_image]
  rcases GlobalTheory.ConjOverQuad.div_or_conj_div D L.C.P k Q hk with h1 | ⟨Q', h1, hc⟩
  · exact ⟨Q, (hL.Pg Q).2 ⟨k, h1⟩, rfl⟩
  · refine ⟨Q', (hL.Pg Q').2 ⟨k, h1⟩, ?_⟩
    ext x
    show algebraMap _ _ x ∈ Q'.asIdeal ↔ algebraMap _ _ x ∈ Q.asIdeal
    rw [hc, Formalism.L2.Col.mem_conjIdeal]
    have : Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = algebraMap _ _ x := by
      apply RingOfIntegers.ext
      exact (D.sp.cm.fixed _).2 ⟨x, rfl⟩
    rw [this]

theorem comL_is {L : LevCh D Unit} (hL : L.Is ()) {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) (P : LevelP L.Pg D.R.r ℂ) : (comL L θ ψ P).Is := by
  have hμ : ∀ j : Fin D.R.m, ChrEq (L.mu () ((j : ℕ) + 1)) (L.C.mu0 j) := fun j => by
    have := GlobalTheory.Mem.TupChar.chrEq_mul (hL.mu0 j) (hL.xi ())
    rw [hL.xi_base, mul_one] at this
    exact this
  refine ⟨hθ, hψ, ⟨hL.eta.1, GlobalTheory.Mem.TupChar.unramEverywhere hL.eta L.C.isEta.unr, GlobalTheory.HeckeCharacterRestriction.resEta_eta hL, fun τ => ?_,
    fun j hj => ?_⟩, fun j τ => ?_, fun j w hw => ?_, fun j => ⟨_, hμ j, hL.chi j⟩, ?_⟩
  · exact GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
      (GlobalTheory.InnerSteps.hasInfQ_tauE (a := fun _ => 1 / 2) ⟨fun _ => 1, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  · obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact ⟨GlobalTheory.HeckeCharacterRestriction.isHecke_mu hL () ⟨i, by omega⟩, GlobalTheory.HeckeCharacterRestriction.resEta_mu hL () ⟨i, by omega⟩⟩
  · have h1 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hμ j) (GlobalTheory.InnerSteps.hasInfQ_tauE (L.C.isMu0 j).inf) τ
    simp only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at h1
    exact h1
  · exact (GlobalTheory.LFun.unrAt_iff_of_chrEq (hμ j) w).2 ((L.C.isMu0 j).unr w fun k hk => hw (mem_S hL θ ψ P k w hk))
  · exact GlobalTheory.CentralShift.exists_idemSum _ fun Q hQ Q' hQ' => GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hL () (Or.inl hQ) (Or.inl hQ')

theorem pg_nonempty {L : LevCh D Unit} (hL : L.Is ()) : L.Pg.Nonempty := by
  obtain ⟨⟨W, hW, hWQ⟩⟩ := (inferInstance : Nonempty ((L.C.P.pb 0).asIdeal.primesOver (𝓞 D.host.E)))
  have hne : W ≠ ⊥ := by
    rintro rfl
    have := hWQ.over
    rw [Ideal.under_def, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)] at this
    exact (L.C.P.pb 0).ne_bot this
  exact ⟨⟨W, hW, hne⟩, (hL.Pg _).2 ⟨0, HeightOneSpectrum.ext hWQ.over.symm⟩⟩

theorem exists_com (C : Formalism.L2.Host.CharFrame D) :
    ∃ c : Com D, c.Pg.Nonempty ∧ ∀ P : LevelP c.Pg D.R.r ℂ, Com.Is { c with P := P } := by
  obtain ⟨L, -, hL⟩ := GlobalTheory.LevelChoices.exists_levCh_unit D C
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨ψ, hψ⟩ := GlobalTheory.StdAdelicChar.exists_isStdChar D
  exact ⟨comL L θ ψ L.triv, pg_nonempty hL, fun P => comL_is hL hθ hψ P⟩

theorem exists_haar (V : HSp D) :
    ∃ (ν : Measure (GA D V)) (𝓖 : Set (GA D V)), ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ V) 𝓖 ν := by
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).1
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  obtain ⟨𝓖, h⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D V Measure.haar inferInstance
  exact ⟨Measure.haar, 𝓖, inferInstance, h⟩

theorem exists_stage (hN : GlobalTheory.Published.DiscreteSeriesExists) (c : Com D) (j : ℕ) (hj : j ≤ D.R.m) :
    ∃ s : PiLocalization₂ D, s.V = D.sp.Y j ∧ s.Is c j := by
  obtain ⟨M⟩ := GlobalTheory.Published.dsExists_of_discreteSeriesExists hN D _ _ (D.sp.Y_sig j) (GlobalTheory.ChainModels.goodPar_parB D j hj)
  obtain ⟨β, n, hβ⟩ := GlobalTheory.T.exists_selfDual_adelic_frame_level_one D (D.sp.Y j) _ (GlobalTheory.LevelChoices.coe_crdLat _) (GlobalTheory.LevelChoices.dualL_crdLat _)
  rw [one_pow] at hβ
  obtain ⟨ν, fd, hν, hfd⟩ := exists_haar (D := D) (D.sp.Y j)
  have hr : D.R.r ≤ (D.sp.Y j).rank := by rw [D.sp.Y_rank j hj]; exact Nat.le_add_right _ _
  refine ⟨⟨D.sp.Y j, _, M, _, β, Lev.datY _ D.R.r D.R.t j hr c.Pg ∅ c.P c.chi (fun _ => 1) Lev.Frm.B, ν, fd⟩, rfl,
    D.sp.Y_rank j hj, D.sp.Y_sig j, D.Y_sigval j hj, rfl, GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hβ, hβ.1,
    ⟨1, hβ, fun P _ h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h))⟩, ⟨hr, _, rfl⟩, hν, hfd⟩

theorem exists_reach (hN : GlobalTheory.Published.DiscreteSeriesExists) (c : Com D)
    (hstep : ∀ k < D.R.m, ∀ s s' : PiLocalization₂ D, s.Is c k → s'.Is c (k + 1) → ∃ p : Step c s s', p.Is (k + 1))
    (s₀ : PiLocalization₂ D) (h₀ : s₀.Is c 0) : ∀ k ≤ D.R.m, ∃ s : PiLocalization₂ D, s.Is c k ∧ ∃ Θ, Reach c s₀ k s Θ := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨s₀, h₀, _, Reach.zero⟩
  | succ k ih =>
    intro hk
    obtain ⟨s, hs, Θ, hΘ⟩ := ih (by omega)
    obtain ⟨s', -, hs'⟩ := exists_stage hN c (k + 1) hk
    obtain ⟨p, hp⟩ := hstep k (by omega) s s' hs hs'
    exact ⟨s', hs', _, hΘ.step hs' p hp⟩

theorem it_ne_zero {c : Com D} {s s' : PiLocalization₂ D} {p : Step c s s'} {j : ℕ} (h : p.Is j) : p.It ≠ 0 := h.it.ne

theorem chainPar_two (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (w) :
    (chainPar c B 2 w).card = (B w).card + 2 * D.R.t := by
  simp only [chainPar_succ, stepPar, Multiset.card_add, Multiset.card_map, GlobalTheory.LFun.seg, Finset.card_val, Finset.card_range]
  show (B w).card + _ + _ = _
  ring

end GlobalTheory.ChainOnto.Model

end
