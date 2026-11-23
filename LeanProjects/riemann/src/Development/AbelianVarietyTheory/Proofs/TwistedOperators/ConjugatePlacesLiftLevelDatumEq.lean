import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LamHomApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameAdjointPartAtMovedRationalPointRowStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeVectorAdjointRowIntegralStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointFrameRowReductionEqZeroIffMemStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowReductionSurjectiveLatticeVectorsPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointFrameRowReductionConjLinearIntegersStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegerConjPrescribedResiduesPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemConjugatePlacesProductIdealOfForallConjPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelDatumConjugatePlacesLevelEqCharactersStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftDat

theorem level_datum_eq : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) → ∃ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q ∧ IdemTwo Lv.w ∧ (∀ κ ∈ Lv.J, ∀ κ' : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E), κ'.map (Ideal.Quotient.mk Lv.𝔪) = (κ : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ Lv.𝔪)) → ∀ PP ∈ Pg, ∀ i j, κ' i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) i j ∈ conjI PP.asIdeal) ∧ ∀ y ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ), Lv.dat hn y = omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))))) * omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))))) := by
  intro D S T C hn ΛT hsd hAA βS βT hfS hfT Pg Q ξ hPg h2P e he a k₀ hab hmov hgen h1 h2 h3 h4
  have Irow := GlobalTheory.T.frameAdjoint_partAt_movedRationalPoint_row D S T C hn ΛT hsd hAA βS βT hfS hfT Pg Q ξ hPg h2P e he a k₀ hab hmov hgen h1 h2 h3 h4
  have Iint := GlobalTheory.T.latticeVector_adjointRow_integral D S T C hn ΛT hsd hAA βS βT hfS hfT Pg Q ξ hPg h2P e he a k₀ hab hmov hgen h1 h2 h3 h4
  have Iker := GlobalTheory.T.adjointFrameRowReduction_eq_zero_iff_mem D S T C hn ΛT hsd hAA βS βT hfS hfT Pg Q ξ hPg h2P e he a k₀ hab hmov hgen h1 h2 h3 h4
  have Isurj := GlobalTheory.T.rowReduction_surjective_latticeVectors_places D S T C hn ΛT hsd hAA βS βT hfS hfT Pg Q ξ hPg h2P e he a k₀ hab hmov hgen h1 h2 h3 h4
  have Ilin := GlobalTheory.T.adjointFrameRowReduction_conjLinear_integers D T βT a e
  set R := GlobalTheory.LiftDat.rowRed T βT a e with hR
  have hz : ∀ PP, R PP 0 = 0 := by
    intro PP
    have hi := Iint 0 (zero_mem _)
    have h := (Ilin PP 0 0 hi hi 1).2
    simp only [smul_zero, add_zero, map_one, one_mul] at h
    funext j
    have h' := congrFun h j
    simp only [Pi.zero_apply]
    linear_combination -h'
  have hsum : ∀ PP (s : Finset (Fin T.rank)) (c : Fin T.rank → 𝓞 D.host.E)
      (u : Fin T.rank → Fin T.rank → D.host.E) (v : Fin T.rank → D.host.E), (∀ j, u j ∈ C.X.Λ) → v ∈ C.X.Λ →
      R PP (∑ j ∈ s, c j • u j + v) = fun l => ∑ j ∈ s, Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar (c j)) *
        R PP (u j) l + R PP v l := by
    intro PP s c u v hu hv
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      have hm : ∑ j ∈ s, c j • u j + v ∈ C.X.Λ := add_mem (sum_mem fun j _ => Submodule.smul_mem _ _ (hu j)) hv
      rw [Finset.sum_insert hj, add_assoc]
      rw [show c j • u j = ((c j : D.host.E)) • u j from rfl]
      rw [(Ilin PP (u j) _ (Iint _ (hu j)) (Iint _ hm) (c j)).2, ih]
      funext l
      rw [Finset.sum_insert hj]
      ring
  choose β hβΛ hβred using fun j : Fin T.rank => Isurj (fun PP => Pi.single j 1)
  have hexp : ∀ PP ∈ Pg ∪ Q, ∀ (c : Fin T.rank → 𝓞 D.host.E) (w : Fin T.rank → D.host.E), w ∈ C.X.Λ →
      ∀ l, R PP (∑ j, c j • β j + w) l = Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar (c l)) + R PP w l := by
    intro PP hPP c w hw l
    rw [hsum PP Finset.univ c β w hβΛ hw]
    simp only [hβred _ PP hPP, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  have hsp : C.X.Λ ≤ Submodule.span (𝓞 D.host.E) (Set.range β) ⊔ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ := by
    intro v hv
    choose c hc using fun j => GlobalTheory.T.exists_integer_conj_prescribed_residues_places D (Pg ∪ Q) (fun PP => R PP v j)
    have hw : v - ∑ j, c j • β j ∈ C.X.Λ := sub_mem hv (sum_mem fun j _ => Submodule.smul_mem _ _ (hβΛ j))
    have hw0 : v - ∑ j, c j • β j ∈ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ := by
      refine (Iker _ hw).1 fun PP hPP => ?_
      funext l
      have h := hexp PP hPP c _ hw l
      rw [add_sub_cancel, hc l PP hPP] at h
      simp only [Pi.zero_apply]
      linear_combination -h
    have e1 : v = ∑ j, c j • β j + (v - ∑ j, c j • β j) := by abel
    rw [e1]
    exact Submodule.add_mem_sup (sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)) hw0
  obtain ⟨Lv0, hw⟩ := GlobalTheory.Ker.Base.exists_level C.X
  have hle : ∀ PP ∈ Pg ∪ Q, GlobalTheory.LiftLevel.liftI Pg Q ≤ conjI PP.asIdeal := fun PP h => GlobalTheory.LiftDat.liftI_le h
  have hnot : ∀ PP ∈ Pg ∪ Q, ∀ s : 𝓞 D.host.E, IsCoprime (Ideal.span {s}) (GlobalTheory.LiftLevel.liftI Pg Q) →
      GlobalTheory.SW.Lev.bar s ∉ PP.asIdeal := by
    intro PP hPP s hs hmem
    obtain ⟨x, m, hm, hxm⟩ := GlobalTheory.SW.Lev.cop_iff.1 hs
    have h1m : (1 : 𝓞 D.host.E) ∈ conjI PP.asIdeal := by
      rw [← hxm]
      exact add_mem (Ideal.mul_mem_left _ _ (GlobalTheory.SW.Lev.mem_conjI.2 hmem)) (hle PP hPP hm)
    have := GlobalTheory.SW.Lev.mem_conjI.1 h1m
    rw [map_one] at this
    exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  have hind : ∀ d : Fin T.rank → 𝓞 D.host.E, GlobalTheory.SW.Cong C.X (GlobalTheory.LiftLevel.liftI Pg Q) (∑ j, d j • β j) 0 →
      ∀ j, d j ∈ GlobalTheory.LiftLevel.liftI Pg Q := by
    intro d ⟨s, hs, hsm⟩ j
    rw [sub_zero, Finset.smul_sum] at hsm
    have e2 : ∑ j, s • d j • β j = ∑ j, (s * d j) • β j + 0 := by
      rw [add_zero]; exact Finset.sum_congr rfl fun j _ => (mul_smul _ _ _).symm
    rw [e2] at hsm
    refine GlobalTheory.T.mem_conjugatePlacesProductIdeal_of_forall_conj_place D Pg Q _ fun PP hPP => ?_
    have h0 := hexp PP hPP (fun j => s * d j) 0 (zero_mem _) j
    have hmemΛ : ∑ j, (s * d j) • β j + 0 ∈ C.X.Λ :=
      add_mem (sum_mem fun j _ => Submodule.smul_mem _ _ (hβΛ j)) (zero_mem _)
    rw [(Iker _ hmemΛ).2 hsm PP hPP, hz] at h0
    simp only [Pi.zero_apply, add_zero, map_mul] at h0
    have h0' : GlobalTheory.SW.Lev.bar s * GlobalTheory.SW.Lev.bar (d j) ∈ PP.asIdeal :=
      Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_mul]; exact h0.symm)
    rcases PP.isPrime.mem_or_mem h0' with h | h
    · exact absurd h (hnot PP hPP s hs)
    · exact GlobalTheory.SW.Lev.mem_conjI.2 h
  refine ⟨GlobalTheory.LiftDat.mkLevel C Pg Q ξ h1 h2 h3 h4 β hβΛ hsp Lv0, rfl, hw, ?_, ?_⟩
  · intro κ hκ κ' hκ' PP hPP i j
    have hm := GlobalTheory.LiftDat.mem_Jgrp.1 hκ PP hPP
    have hij := congrArg (fun g : GL (Fin T.rank) (𝓞 D.host.E ⧸ conjI PP.asIdeal) => g.val i j) hm
    have hk := congrFun (congrFun hκ' i) j
    change (GlobalTheory.LiftDat.toConj Pg Q PP (Finset.mem_union_left _ hPP)) (κ.val i j) =
      (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ conjI PP.asIdeal)) i j at hij
    simp only [Matrix.map_apply] at hk
    rw [← hk] at hij
    have hij2 : Ideal.Quotient.mk (conjI PP.asIdeal) (κ' i j) =
        (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ conjI PP.asIdeal)) i j := hij
    rw [← Ideal.Quotient.eq, hij2]
    by_cases hij' : i = j
    · subst hij'; simp
    · simp [Matrix.one_apply_ne hij']
  · intro y hy
    have hrow : ∀ i, y i ∈ C.X.Λ := by
      intro i
      have key : ∀ z ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI (GlobalTheory.LiftLevel.liftI Pg Q)) • C.X.Λ),
          z i ∈ C.X.Λ := by
        intro z hz
        induction hz using AddSubgroup.closure_induction with
        | mem z hz =>
          obtain ⟨v, hv, u, hu, rfl⟩ := hz
          have hvi : IsIntegral ℤ (v i) := (GlobalTheory.SW.Base.mem_stdL _).1 hv i
          have : vecMulVec v u i = (⟨v i, hvi⟩ : 𝓞 D.host.E) • u := by
            funext k; rw [vecMulVec_apply, Pi.smul_apply, Algebra.smul_def]; rfl
          rw [this]
          exact Submodule.smul_mem _ _ (Submodule.smul_le_right hu)
        | zero => exact zero_mem _
        | add x y _ _ hx hy => exact add_mem hx hy
        | neg x _ hx => exact neg_mem hx
      exact key y hy
    have hdec : ∀ i, ∃ c : Fin T.rank → 𝓞 D.host.E, y i - ∑ j, c j • β j ∈ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ := by
      intro i
      obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 (hsp (hrow i))
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hp
      refine ⟨c, ?_⟩
      rw [hc, ← hpq, add_sub_cancel_left]
      exact hq
    choose c hc using hdec
    refine GlobalTheory.T.levelDatum_conjugatePlacesLevel_eq_characters D S T C hn Pg Q ξ h1 h2 h3 h4 β hβΛ hsp Lv0 hind y c hc _ ?_
    intro PP hPP i j
    rw [Irow]
    have hw : y i - ∑ j, c i j • β j ∈ C.X.Λ := sub_mem (hrow i) (sum_mem fun j _ => Submodule.smul_mem _ _ (hβΛ j))
    have h := hexp PP hPP (c i) _ hw j
    rw [add_sub_cancel, (Iker _ hw).2 (hc i) PP hPP, Pi.zero_apply, add_zero] at h
    exact h

end GlobalTheory.LiftDat

end
