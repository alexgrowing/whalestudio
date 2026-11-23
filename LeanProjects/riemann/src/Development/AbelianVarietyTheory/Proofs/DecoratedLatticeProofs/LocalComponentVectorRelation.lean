import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeNotMemPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormalFramesRationalDecompositionsOverLocaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureIdentityAltBis
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

theorem level_prime_not_mem_under_Pg {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word) :
    ∀ PP ∈ (pk W).Pg, (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ (PP.under (𝓞 D.host.F)).asIdeal := by
  intro PP hPP hmem
  obtain ⟨k, hk⟩ := (W.Q.charW.base.lev.Pg PP).1 hPP
  have h1 : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (PP.under (𝓞 D.host.K)).asIdeal := by
    have := (W.Q.Rl.C.P).pb_over k
    rw [← show PP.under (𝓞 D.host.K) = _ from hk] at this
    exact this
  have h2 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := h1
    simpa using this
  have h3 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal := hmem
    simpa using this
  have hc : IsCoprime (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes (D.mem u).A.T_prime (D.host.g_prime k)).2 (D.T_ne_g u k))
  obtain ⟨a, b, hab⟩ := hc
  exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ PP.asIdeal.add_mem (PP.asIdeal.mul_mem_left _ h3) (PP.asIdeal.mul_mem_left _ h2)))

theorem lattices_frames_basePoints_exist : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = PP.under (𝓞 D.host.F)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∃ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (b : ∀ j, GA D (Yc D j)) (dT : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ) (M : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀) (β₀ : ∀ j ρ h i, GlobalTheory.FinPl.Frame (o.p i) (y.bes j ρ h).V₀ (Fin (D.sp.X j).rank ⊕ Fin 1)), ShapeOff { v with N := N, dT := dT, RamAd := o.Ram } { o with M := M, β₀ := β₀ } ∧ (∀ j, b j ∈ GfC (Yc D j) ∧ GlobalTheory.FinPl.CombAt (· ∈ v.tP) (dT j)) ∧ (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j) ∧ ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) → GlobalTheory.FinPl.Moves (Yc D j) (b j) ((pk W).ΛY j) (N j) P) ∧ ∀ PP h, Nonempty (LocY (l PP h) y N (pk W).βY b (bas PP h)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a y m b₀ k _ _ _ _ ι v o l bas hIs hTau hT0 hτ hNT hζ hLT hgP htP hPre hLZ hbas
  have hPg : ∀ PP ∈ (pk W).Pg, (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ (PP.under (𝓞 D.host.F)).asIdeal :=
    level_prime_not_mem_under_Pg W u
  have hdisj : Disjoint v.gP v.tP := Finset.disjoint_left.2 fun p hp hp' => by
    obtain ⟨PP, hPP, rfl⟩ := (hgP p).1 hp
    exact hPg PP hPP ((htP _).1 hp')
  have hU := GlobalTheory.levelPrime_not_mem_places W u hW hPg
  have hA : ∀ PP h, ∃ (FY : FYFam (l PP h)) (sc : ℕ → (l PP h).k), IsNormalFr (l PP h) y FY sc :=
    fun PP h => GlobalTheory.T.exists_normalFrames_rationalDecompositions_over_local a y (l PP h) _ hTau hT0 (hU PP h)
  choose FY sc hFY using hA
  obtain ⟨N, dT, M, β₀, hShape, hdT, hSD, hInt⟩ :=
    GlobalTheory.T.local_component_measure_identity W u hW a y m b₀ k ι v o l bas hIs hTau hT0 hτ hNT hζ hLT hgP htP hdisj hPre hLZ hbas FY sc hFY
  obtain ⟨b, hbG, hbM, hbF⟩ :=
    GlobalTheory.T.local_component_measure_identity_alt W u hW a y m b₀ k ι v o l bas hIs hTau hT0 hτ hNT hζ hLT hgP htP hdisj hPre hLZ hbas FY N hSD hInt
  refine ⟨N, b, dT, M, β₀, hShape, fun j => ⟨hbG j, hdT j⟩, fun j hj => ⟨hSD j hj, hbM j hj⟩, fun PP h => ⟨?_⟩⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hFY PP h
  exact { FY := FY PP h, sc := sc PP h, sc_unit := h1, sc_step := h2, hz_unit := h3, bes := h4, jac := h5, tau := h6,
          latY := hInt PP h, frame := hbF PP h }

end GlobalTheory.Fam

end
