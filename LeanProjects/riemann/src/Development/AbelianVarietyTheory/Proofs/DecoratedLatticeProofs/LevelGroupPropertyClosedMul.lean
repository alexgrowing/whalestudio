import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BesselCompatibility
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevDatYZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSymmetricDataConductorOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelGroupPropertyClosedMulAltBis
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevZeroInd

theorem redFn_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E) {x y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hx : x ∈ St β) (hy : y ∈ St β) : redFn β PP (x * y) = redFn β PP x * redFn β PP y := by
  unfold redFn ext1
  rw [dif_pos (mul_mem hx hy), dif_pos hx, dif_pos hy]
  rw [← map_mul]
  congr 1

theorem redFn_inv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E) {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hx : x ∈ St β) : redFn β PP x⁻¹ = (redFn β PP x)⁻¹ := by
  unfold redFn ext1
  rw [dif_pos (inv_mem hx), dif_pos hx]
  rw [← map_inv]
  congr 1

theorem reductionBlock_injective_of_eq {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (hn : n = r) :
    Function.Injective (upperLeftBlock (κ := κ) hr) := by
  subst hn
  intro a b h
  rwa [GlobalTheory.SeeConjRead.restrictedBlock_self_apply, GlobalTheory.SeeConjRead.restrictedBlock_self_apply] at h

theorem red_unique {D : D7} {u : D.what₂.Word} {d : GlobalTheory.SeeSaw.Dat D u}
    {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E} {PP : Pl D.host.E}
    (G : GlobalTheory.LocMod.GAt d τ PP) {x : G.S.P.J} {g g' : GL (Fin D.R.r) (kP PP)} (h : G.Red x g) (h' : G.Red x g') :
    g = g' := by
  have h1 := G.hs
  let e : Fin D.R.k ⊕ Fin (G.s + 1) ≃ Fin D.R.r := finSumFinEquiv.trans (finCongr (by unfold Ranks.r; omega))
  have he : ∀ a, (e a).val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a := by
    rintro (a | a) <;> simp [e, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos]
  refine Units.ext (Matrix.ext fun i j => ?_)
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (g.val (e i) (e j))
  obtain ⟨z', hz'⟩ := Ideal.Quotient.mk_surjective (g'.val (e i) (e j))
  have h2 := Valuation.map_sub_lt _ (h' i j _ _ (he i) (he j) z' hz') (h i j _ _ (he i) (he j) z hz)
  rw [sub_sub_sub_cancel_left] at h2
  rw [← hz, ← hz', Ideal.Quotient.eq, GlobalTheory.LocMod.SymChainAt.prO_lt G.q G.idem, map_sub]
  exact h2

end GlobalTheory.LevZeroInd

open GlobalTheory.LevZeroInd in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.LevZeroInd.gen : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d τ PP.1) (cG : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), d.Base → IsTypePlaces d.c.Pg → GlobalTheory.LocMod.PinGBy G cG → ∀ Q : GA D (d.st 0).V → Prop, (∀ k ∈ d.lev 0, ∀ k' ∈ d.lev 0, Q k → Q k' → Q (k * k')) → (∀ (PP : d.c.Pg) (n : GA D (d.st 0).V) (q : GL (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), n ∈ flagN (d.bes 0 D.R.rS h0).d → q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (GlobalTheory.LocMod.ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → (d.t 0)⁻¹ * n * d.t 0 ∈ d.lev 0 → Q ((d.t 0)⁻¹ * n * d.t 0)) → (∀ b ∈ GfC (D.sp.X 0), (d.t 0)⁻¹ * embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o b * d.t 0 ∈ d.lev 0 → Q ((d.t 0)⁻¹ * embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o b * d.t 0)) → (∀ k ∈ d.lev 0, (∀ PP ∈ d.c.Pg, redFn (d.st 0).β PP (finE (d.st 0).V k) = 1) → Q k) → ∀ k ∈ d.lev 0, Q k := by
  intro D u d τ G cG h0 hB hT hP Q hmul hN hU hred
  classical
  have hm : 0 < D.R.m := by omega
  have hst := hB.st 0 hm
  obtain ⟨hr, ξ, hL⟩ := hst.lev
  have hn : (d.st 0).V.rank = D.R.r := by rw [hst.rank]; show D.R.r + 0 * D.R.t = D.R.r; simp
  have key := fun x => GlobalTheory.LevYZero.lev_datY_zero _ (d.st 0).β _ D.R.r D.R.t hr hn d.c.Pg d.c.P d.c.chi ξ hL
    (Lev.finE (d.st 0).V x) (GlobalTheory.LevSplit.finE_mem_UA _ x)
  have hSt : ∀ x ∈ d.lev 0, Lev.finE (d.st 0).V x ∈ St (d.st 0).β := fun x hx => ((key x).1.1 hx.2).1
  have hRed : ∀ x ∈ d.lev 0, ∀ PP : d.c.Pg, ∃ z, (G PP).Red z (upperLeftBlock hr (redFn (d.st 0).β PP.1 (Lev.finE (d.st 0).V x))) :=
    fun x hx PP => (hP.grp _).1 ((key x).1.1 hx.2).2 PP
  have hmulm : ∀ x ∈ d.lev 0, ∀ y ∈ d.lev 0, x * y ∈ d.lev 0 := fun x hx y hy => by
    unfold GlobalTheory.SeeSaw.Dat.lev levS at *
    exact Subgroup.mul_mem _ hx hy
  have hinvm : ∀ x ∈ d.lev 0, x⁻¹ ∈ d.lev 0 := fun x hx => by
    unfold GlobalTheory.SeeSaw.Dat.lev levS at *
    exact Subgroup.inv_mem _ hx
  have claim : ∀ s : Finset (Pl D.host.E), ∀ k ∈ d.lev 0,
      (∀ PP ∈ d.c.Pg, PP ∉ s → redFn (d.st 0).β PP (Lev.finE (d.st 0).V k) = 1) → Q k := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro k hk h
      exact hred k hk fun PP hPP => h PP hPP (Finset.notMem_empty _)
    · intro a s ha ih k hk h
      by_cases haP : a ∈ d.c.Pg
      · obtain ⟨z, hz⟩ := hRed k hk ⟨a, haP⟩
        obtain ⟨m, hm0, hQm, hmr, hmo⟩ := GlobalTheory.T.level_group_property_closed_mul_alt D u d τ G cG h0 hB hT hP Q hmul hN hU ⟨a, haP⟩ z
        have e1 : redFn (d.st 0).β a (Lev.finE (d.st 0).V m) = redFn (d.st 0).β a (Lev.finE (d.st 0).V k) :=
          reductionBlock_injective_of_eq hr hn (red_unique (G ⟨a, haP⟩) (hmr hr) hz)
        have hk1 : m⁻¹ * k ∈ d.lev 0 := hmulm _ (hinvm m hm0) k hk
        have hred1 : ∀ PP, redFn (d.st 0).β PP (Lev.finE (d.st 0).V (m⁻¹ * k)) =
            (redFn (d.st 0).β PP (Lev.finE (d.st 0).V m))⁻¹ * redFn (d.st 0).β PP (Lev.finE (d.st 0).V k) := fun PP => by
          rw [map_mul, map_inv, redFn_mul _ _ (inv_mem (hSt m hm0)) (hSt k hk), redFn_inv _ _ (hSt m hm0)]
        have hQ1 := ih (m⁻¹ * k) hk1 fun PP hPP hPs => by
          rw [hred1]
          by_cases hPa : PP = a
          · subst hPa
            rw [e1, inv_mul_cancel]
          · rw [hmo PP hPP hPa, h PP hPP (by simp [hPa, hPs]), inv_one, one_mul]
        have := hmul m hm0 _ hk1 hQm hQ1
        simpa using this
      · exact ih k hk fun PP hPP hPs => h PP hPP (by
          simp only [Finset.mem_insert, not_or]
          exact ⟨fun e => haP (e ▸ hPP), hPs⟩)
  intro k hk
  exact claim d.c.Pg k hk fun PP hPP h => absurd hPP h
