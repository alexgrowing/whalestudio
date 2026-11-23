import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnramifiedCharacter
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatNotSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDataLines
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.UnrWeil

theorem natCast_mem_of_isConjPl {D : D7} (n : ℕ) {PP PP' : Formalism.L2.DIV.Pl D.host.E} (h : Lev.IsConjPl PP' PP)
    (hn : ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : ((n : ℕ) : 𝓞 D.host.E) ∈ PP'.asIdeal := by
  by_contra hn'
  obtain ⟨y, c, hc, hyc⟩ := PP'.isMaximal.exists_inv hn'
  obtain ⟨c', hc', e⟩ := h c hc
  apply PP.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have key : (1 : 𝓞 D.host.E) = RingOfIntegers.mapRingHom (starRingEnd D.host.E) y * ((n : ℕ) : 𝓞 D.host.E) + c' := by
    have h1 := congrArg (fun z : 𝓞 D.host.E => star (algebraMap (𝓞 D.host.E) D.host.E z)) hyc
    simp only [map_add, map_mul, map_natCast, map_one, star_add, star_mul', star_natCast, star_one] at h1
    have hy : algebraMap (𝓞 D.host.E) D.host.E (RingOfIntegers.mapRingHom (starRingEnd D.host.E) y) =
        star (algebraMap (𝓞 D.host.E) D.host.E y) := rfl
    have hc2 : algebraMap (𝓞 D.host.E) D.host.E c' = star (algebraMap (𝓞 D.host.E) D.host.E c) := e
    apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
    simp only [map_add, map_mul, map_natCast, map_one, hy, hc2]
    rw [← h1]
  rw [key]
  exact PP.asIdeal.add_mem (PP.asIdeal.mul_mem_left _ hn) hc'

theorem not_both_mem {D : D7} {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (PP : Formalism.L2.DIV.Pl D.host.E)
    (h1 : ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (h2 : ((q : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : False := by
  obtain ⟨a, b, hab⟩ : IsCoprime ((p : ℕ) : 𝓞 D.host.E) ((q : ℕ) : 𝓞 D.host.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ PP.asIdeal.add_mem (PP.asIdeal.mul_mem_left a h1) (PP.asIdeal.mul_mem_left b h2)))

end GlobalTheory.Fam.UnrWeil

open GlobalTheory.Fam.UnrWeil in

theorem GlobalTheory.Fam.kom_weil_unram : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (f : FamCh W u) (v : VCom f.c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat f.c k ι), f.RowOK → f.ColOK → v.Is → VTie f v → ShapeOff v o → ∀ t j, j < D.R.m → ∃ μ, IsWeilDatumO f.c.ψ _ _ μ μ ((f.t t).kom j) ∧ ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D μ (o.p i).v := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW f v k _ _ _ _ ι o _ hC _ hV hS t j hj
  refine ⟨(pk W).toLevCh.mu t (j + 1), hC.kom t j hj, fun i => ?_⟩
  have lev : (pk W).toLevCh.Is W.P.A3.A.μ0 := hW.bot.hyp.2.2.2.1.lev
  have hp : (o.p i).v ∈ v.tP := (hS.pre.tP _).2 ⟨i, rfl⟩
  have hTF : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (o.p i).v.asIdeal := (hV.tP _).1 hp
  have hTw : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = (o.p i).v →
      (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
    intro w hw
    rw [← hw] at hTF
    have := Ideal.mem_comap.1 hTF
    simpa using this
  show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (Formalism.IndefR.Lift.tup (pk W).toLevCh.mu0 ((pk W).toLevCh.xi t) (j + 1)) (o.p i).v
  refine GlobalTheory.SeeSaw.WeilLines.charUnram_mul ?_ ?_
  · refine GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => ?_
    refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (lev.mu0 ⟨j, hj⟩) w).2 ?_
    refine ((pk W).toLevCh.C.isMu0 ⟨j, hj⟩).unr w fun kk hk => ?_
    exact not_both_mem (D.mem u).A.T_prime (D.host.g_prime kk) (D.T_ne_g u kk) w (hTw w hw) hk
  · refine GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => ?_
    refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (lev.xi t) w).2 ?_
    by_contra hr
    rcases (lev.Q_ram t w).1 hr with hq | ⟨PP', hq, hc⟩
    · exact (lev.Q_off t w hq).2 u (hTw w hw)
    · exact (lev.Q_off t PP' hq).2 u (natCast_mem_of_isConjPl _ hc (hTw w hw))
