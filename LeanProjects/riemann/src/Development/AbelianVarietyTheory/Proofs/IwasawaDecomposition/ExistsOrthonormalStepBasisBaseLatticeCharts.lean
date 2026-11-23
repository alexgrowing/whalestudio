import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ClsChartedLabAt
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LevelsGEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTwG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplittingFstMemIntegersStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocLEqIntVOfDvdUnitStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG
open scoped TensorProduct

namespace GlobalTheory.Mem.Top.KerTwLv

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem stepBasis_std : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      ∀ j (hj : j + 1 ≤ (w.D Z).R.m), ∃ B : GL (Fin ((w.D Z).sp.X (j + 1)).rank) (w.D Z).host.E,
        cT (sigD (w.D Z) : (w.D Z).host.E →+* (w.D Z).host.E)
          (reGL (rankN (w.D Z) (j + 1) hj) (w.D Z).host.E B).1 * gramN (w.D Z) (j + 1) hj *
          (reGL (rankN (w.D Z) (j + 1) hj) (w.D Z).host.E B).1 = 1 ∧
        ∀ (β : tt.ch.Ch u ((w.D Z).what₂.muAt v) (j + 1)) w' h (x : Fin ((w.D Z).sp.X (j + 1)).rank → w'.adicCompletion (w.D Z).host.F),
          (∃ y ∈ Formalism.L2.Herm.locL w' (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Lb,
            ∀ a, ((t.g.herm.g u v hg).spl w' h (y a)).1 = x a) ↔
          ∀ a, (((GlobalTheory.Mem.Top.KerTwLv.frOf t.g.herm u v hg B w' h)⁻¹ :
            GL (Fin ((w.D Z).sp.X (j + 1)).rank) (w'.adicCompletion (w.D Z).host.F)) :
              Matrix (Fin ((w.D Z).sp.X (j + 1)).rank) (Fin ((w.D Z).sp.X (j + 1)).rank) (w'.adicCompletion (w.D Z).host.F)).mulVec x a ∈
            w'.adicCompletionIntegers (w.D Z).host.F := by
  intro K B f T w hK hF hP Z t Wt nch n Y hmu hQp O hstdO hunf E hent Fl hfl hwt u v hg hμ tt hstd j hj
  have hsc := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates w.I w.ok w.pins w.l Z).2.2.2 (j+1) hj
  obtain ⟨k, hk⟩ := hstd.1.reads u ((w.D Z).what₂.muAt v) hμ (j+1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj
  have hcar := tt.forms.car u ((w.D Z).what₂.muAt v) hμ (j+1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj
  refine ⟨1, ?_, ?_⟩
  · rw [hsc.1]
    simp [cT, Matrix.map_one]
  · intro β w' h x
    have hfr : GlobalTheory.Mem.Top.KerTwLv.frOf t.g.herm u v hg (1 : GL (Fin ((w.D Z).sp.X (j + 1)).rank) (w.D Z).host.E) w' h = 1 :=
      map_one _
    rw [hfr, inv_one]
    simp only [Units.val_one, Matrix.one_mulVec]
    have hT : ((((w.D Z).mem u).A.T : ℕ) : 𝓞 (w.D Z).host.F) ∉ w'.asIdeal := by
      intro hT
      have hcop : Nat.Coprime ((w.D Z).what₂.places.resChar v) ((w.D Z).mem u).A.T :=
        (Nat.Prime.coprime_iff_not_dvd hg.1).2 hg.2.2.2.2.2
      obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
      apply w'.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have e : ((1 : ℤ) : 𝓞 (w.D Z).host.F) = (a : 𝓞 (w.D Z).host.F) * (((w.D Z).what₂.places.resChar v : ℕ) : 𝓞 (w.D Z).host.F)
          + (b : 𝓞 (w.D Z).host.F) * ((((w.D Z).mem u).A.T : ℕ) : 𝓞 (w.D Z).host.F) := by
        rw [← hab]; push_cast; ring
      rw [Int.cast_one] at e
      rw [e]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ hT)
    have hLb : ∀ y, y ∈ (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Lb ↔
        ∀ a, ∃ r : 𝓞 (w.D Z).host.E, y a = r ∧ (a.1 + 1 = ((w.D Z).sp.X (j + 1)).rank → (w.px.piT u : 𝓞 (w.D Z).host.E) ∣ r) := by
      intro y
      have e1 := (hcar β).Lb_eq
      have e2 := hk.lb β
      have hr := rankN (w.D Z) (j + 1) hj
      have hmap : y ∈ (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Lb ↔
          reV (rankN (w.D Z) (j + 1) hj) (w.D Z).host.E y ∈
            reL (rankN (w.D Z) (j + 1) hj) (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Lb := by
        constructor
        · intro hy
          exact ⟨y, hy, rfl⟩
        · rintro ⟨z, hz, hzy⟩
          have : z = y := (reV (rankN (w.D Z) (j + 1) hj) (w.D Z).host.E).injective hzy
          exact this ▸ hz
      rw [hmap, ← e1]
      refine (e2 _).trans ?_
      simp only [TC.baseL, Set.mem_setOf_eq, reV, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
      constructor
      · intro H a
        obtain ⟨r, hr1, hr2⟩ := H (finCongr hr a)
        refine ⟨r, ?_, fun ha => hr2 ?_⟩
        · rw [LinearMap.funLeft_apply, Equiv.symm_apply_apply] at hr1
          exact hr1
        · have e : ((finCongr hr a : Fin _) : ℕ) = a := rfl
          rw [e]
          exact ha.trans hr
      · intro H b
        obtain ⟨r, hr1, hr2⟩ := H ((finCongr hr).symm b)
        refine ⟨r, hr1, fun hb => hr2 ?_⟩
        have e : (((finCongr hr).symm b : Fin _) : ℕ) = b := rfl
        rw [e]
        exact hb.trans hr.symm
    have hπ : (w.px.piT u : 𝓞 (w.D Z).host.E) * (B.fields.conjO (w.px.piT u) : 𝓞 (w.D Z).host.E) =
        ((((w.D Z).mem u).A.T : ℕ) : 𝓞 (w.D Z).host.E) :=
      B.primes_piT_norm w.px u
    have L := @GlobalTheory.T.mem_locL_iff_forall_mem_intV_of_not_mem (w.D Z).host.F (w.D Z).host.E _ _ _ _ _ _ w' _ _ _ _ _ _ hT hπ hLb
    have PI := @GlobalTheory.T.splitting_fst_mem_integers' (w.D Z).host.F (w.D Z).host.E _ _ _ _ _ w' _ ((t.g.herm.g u v hg).spl_alg w' h)
    constructor
    · rintro ⟨y, hy, hyx⟩ a
      rw [← hyx a]
      exact PI _ ((L y).1 hy a)
    · intro hx
      refine ⟨fun a => (1 : (w.D Z).host.E) ⊗ₜ[(w.D Z).host.F] x a, (L _).2
        (fun a => Subring.subset_closure (Or.inr ⟨⟨x a, hx a⟩, rfl⟩)), fun a => ?_⟩
      rw [(t.g.herm.g u v hg).spl_alg]

end GlobalTheory.Mem.Top.KerTwLv
