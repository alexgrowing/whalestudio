import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedBy
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelGroupPropertyClosedMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIndexZeroLevelElementGivenReductionAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemOfRhoLt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevZeroInd in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.LevZero.gen : ∀ {D : D7} {c : Comm D} {v : VCom c} (cm : GlobalTheory.ChainOnto.Com D) (st : StAt (c.V 0)) (b : GA D (c.V 0)) (G : cm.Pg → GLoc v) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.LevZero.Bot cm st b G → ∀ Q : GA D (c.V 0) → Prop, (∀ k ∈ levS (c.V 0) st.β st.L, ∀ k' ∈ levS (c.V 0) st.β st.L, Q k → Q k' → Q (k * k')) → (∀ (PP : cm.Pg) (n : GA D (c.V 0)) (q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), n ∈ flagN (c.bes 0 D.R.rS h0).d → q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → b⁻¹ * n * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * n * b)) → (∀ x ∈ GfC (c.X 0), b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b)) → (∀ k ∈ levS (c.V 0) st.β st.L, (∀ PP ∈ cm.Pg, redFn st.β PP (finE (c.V 0) k) = 1) → Q k) → ∀ k ∈ levS (c.V 0) st.β st.L, Q k := by
  intro D c v cm st b G h0 hB Q hmul hN hU hred
  classical
  have hst := hB.mem
  obtain ⟨hr, ξ, hL⟩ := hst.lev
  have hn : (c.V 0).rank = D.R.r := by rw [hst.rank]; show D.R.r + 0 * D.R.t = D.R.r; simp
  have key := fun x => GlobalTheory.LevYZero.lev_datY_zero (c.V 0) st.β st.L D.R.r D.R.t hr hn cm.Pg cm.P cm.chi ξ hL
    (Lev.finE (c.V 0) x) (GlobalTheory.LevSplit.finE_mem_UA _ x)
  have hSt : ∀ x ∈ levS (c.V 0) st.β st.L, Lev.finE (c.V 0) x ∈ St st.β := fun x hx => ((key x).1.1 hx.2).1
  have hRed : ∀ x ∈ levS (c.V 0) st.β st.L, ∀ PP : cm.Pg, ∃ z, GlobalTheory.LevZero.Red (G PP) PP.1 z (upperLeftBlock hr (redFn st.β PP.1 (Lev.finE (c.V 0) x))) :=
    fun x hx PP => (hB.grp _).1 ((key x).1.1 hx.2).2 PP
  have hmulm : ∀ x ∈ levS (c.V 0) st.β st.L, ∀ y ∈ levS (c.V 0) st.β st.L, x * y ∈ levS (c.V 0) st.β st.L :=
    fun x hx y hy => Subgroup.mul_mem _ hx hy
  have hinvm : ∀ x ∈ levS (c.V 0) st.β st.L, x⁻¹ ∈ levS (c.V 0) st.β st.L := fun x hx => Subgroup.inv_mem _ hx
  have claim : ∀ s : Finset (Pl D.host.E), ∀ k ∈ levS (c.V 0) st.β st.L,
      (∀ PP ∈ cm.Pg, PP ∉ s → redFn st.β PP (Lev.finE (c.V 0) k) = 1) → Q k := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro k hk h
      exact hred k hk fun PP hPP => h PP hPP (Finset.notMem_empty _)
    · intro a s ha ih k hk h
      by_cases haP : a ∈ cm.Pg
      · obtain ⟨z, hz⟩ := hRed k hk ⟨a, haP⟩
        obtain ⟨m, hm0, hQm, hmr, hmo⟩ := GlobalTheory.T.exists_indexZeroLevel_element_given_reduction_at_place cm st b G h0 hB Q hmul hN hU ⟨a, haP⟩ z
        have e1 : redFn st.β a (Lev.finE (c.V 0) m) = redFn st.β a (Lev.finE (c.V 0) k) :=
          reductionBlock_injective_of_eq hr hn ((GlobalTheory.LevZeroUniq.main (G ⟨a, haP⟩) a (hB.loc ⟨a, haP⟩).idem).2 z z _ _ (hmr hr) hz
            (by rw [inv_mul_cancel]; exact one_mem _))
        have hk1 : m⁻¹ * k ∈ levS (c.V 0) st.β st.L := hmulm _ (hinvm m hm0) k hk
        have hred1 : ∀ PP, redFn st.β PP (Lev.finE (c.V 0) (m⁻¹ * k)) =
            (redFn st.β PP (Lev.finE (c.V 0) m))⁻¹ * redFn st.β PP (Lev.finE (c.V 0) k) := fun PP => by
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
  exact claim cm.Pg k hk fun PP hPP h => absurd hPP h
