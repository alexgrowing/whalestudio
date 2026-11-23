import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMtCutPartCompl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OffPlacesPartMovedLevelKeepsStandardHomLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharTrivialOnIdempotentIntegralUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumFixesLatticeVacuaAtInertPlaces
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LawStep

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section

namespace GlobalTheory.OffPartVac

theorem unrOff_mu_locPl {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T)
    (j : Fin D.R.m) {e : AE D} (he : IsIdemSum e (locPl G t)) : Formalism.IndefR.Fin.UnrOff e (L.mu t ((j : ℕ) + 1)) := by

  have hbase : GlobalTheory.VecInv.UnrOff (e + cA D e) (L.mu0 ((j : ℕ) + 1)) := by
    refine GlobalTheory.ChrOff.unrOff_of_unrAt D _ (L.C.mu0 j) (locPl G t) e (hL.mu0 j) he ?_
    intro Q hQ hQc
    by_cases hg : ∀ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal
    · exact (L.C.isMu0 j).unr Q hg
    · exfalso
      push Not at hg
      obtain ⟨k, hk⟩ := hg
      have hk' := (GlobalTheory.FunObj.Good.natCast_mem_under Q (D.host.g k)).2 hk
      have hS1 : Q.under (𝓞 D.host.F) ∈ S1 D := by
        rw [GlobalTheory.ChiGrid.S1_mem_OmF]
        fin_cases k
        · exact Or.inl hk'
        · exact Or.inr (Or.inl hk')
      have hS0 : Q.under (𝓞 D.host.F) ∈ G.pl.S0 := G.pl.mem_S0_of_sum_eq.2 (Or.inr hS1)
      have hW0 : G.pl.w (Q.under (𝓞 D.host.F)) ∈ G.pl.W0 := by
        classical
        exact Finset.mem_image_of_mem _ hS0
      have hw : G.pl.w (Q.under (𝓞 D.host.F)) ∈ locPl G t := GlobalTheory.FunObj.GivenAdm.mem_locPl.2 (Or.inl hW0)
      rcases GlobalTheory.IdemSupport.eq_or_eq_cP (G.pl.under_w hS0).symm with h | h
      · exact hQ (by rw [h]; exact hw)
      · exact hQc _ hw ((GlobalTheory.IdemSupport.isConjPl_iff _ _).2 h)

  have htw : GlobalTheory.VecInv.UnrOff (e + cA D e) (L.xi t) := by
    refine GlobalTheory.ChrOff.unrOff_of_unrAt D _ (L.xiH t) (locPl G t) e (hL.xi t) he ?_
    intro Q hQ hQc
    by_contra hr
    rcases (hL.Q_ram t Q).1 hr with hq | ⟨Q', hQ', hc⟩
    · exact hQ (GlobalTheory.FunObj.GivenAdm.mem_locPl.2 (Or.inr hq))
    · exact hQc Q' (GlobalTheory.FunObj.GivenAdm.mem_locPl.2 (Or.inr hQ')) hc
  intro x h1 h2 h3 h4
  show (L.mu0 ((j : ℕ) + 1) * L.xi t) x = 1
  rw [MonoidHom.mul_apply, hbase x h1 h2 h3 h4, htw x h1 h2 h3 h4, one_mul]

private theorem cut_one_sub_eq_resG_one_sub_of_isIdempotentElem {D : D7} (V : HSp D) {ε : AF D.host.F} (hε : IsIdempotentElem ε) {f : AE D}
    (hf : algebraMap (AF D.host.F) (AE D) ε = f) (g : GA D V) :
    cutPart (1 - f) V g = Formalism.IndefR.Fin.LevelGroupLemmas.resG V (1 - ε) g := by
  have hid : IsIdempotentElem (1 - ε) := hε.one_sub
  have ha : algebraMap (AF D.host.F) (AE D) (1 - ε) = 1 - f := by rw [map_sub, map_one, hf]
  have h1 : (1 - f) * (1 - f) = 1 - f := by rw [← ha, ← map_mul, hid.eq]
  have h2 : cA D (1 - f) = 1 - f := by rw [← ha, GlobalTheory.IdemSupport.cA_algebraMap]
  apply Subtype.ext
  apply Units.ext
  change Formalism.L2.Theta.mt V _ = Formalism.L2.Theta.mt V _
  rw [mt_cutPart h1 h2, Formalism.IndefR.Fin.LevelGroupLemmas.mt_resG' hid, ha]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem cut_conj_unipotent_mem_St_succ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m)
    (k : FinPt G (.top (j + 1))) (hk : finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj) {e : AE D}
    (he : IsIdemSum e (locPl G t)) :
    Lev.finE (G.V (.top (j + 1))) (cutPart (1 - (e + cA D e)) (G.V (.top (j + 1)))
      ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))))
      ∈ Formalism.L2.DIV.St ((Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1)⁻¹ * S.βp (j + 1)) := by
  have hlev : finG (G.V (.top (j + 1))) k ∈ prodLev (S.βp (j + 1)) (locPl G t) _ _ := hk
  refine GlobalTheory.OffPartLattice.finE_cut_mem_St (G.V (.top (j + 1))) (S.βp (j + 1))
    (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1) (finG (G.V (.top (j + 1))) k) _ ?_ he ?_
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, finG, MonoidHom.comp_apply, Subgroup.coe_subtype]
  · intro Q hQ
    have h2 := (Subgroup.mem_inf.1 hlev).2
    exact Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h2 Q) hQ)

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove GlobalTheory.OffPartLattice in

theorem offPart_fixes_vac : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    W.om (.top t (j + 1)) (cutPart (1 - (e + cA D e)) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))), 1) (S.Z.vac (.top t (j + 1))) = S.Z.vac (.top t (j + 1)) := by
  intro D T L sc G W U S t μ₀ hL ht Φ β j hj k hk e he

  have hv := S.Z.vac_is (.top t (j + 1)) hj
  unfold IsVacO at hv
  obtain ⟨_, hv2⟩ := hv
  obtain ⟨_, hθ, hlat, _, hcov, hnrm⟩ := hv2

  obtain ⟨⟨es, hes, hesum⟩, hc⟩ := id he
  have hε : IsIdempotentElem (Formalism.IndefR.Fin.LevelGroupLemmas.epsP (locPl G t)) :=
    Formalism.IndefR.Fin.LevelGroupLemmas.isIdempotentElem_placeIdempotent hes hesum hc _ subset_rfl
  have halg := Formalism.IndefR.Fin.LevelGroupLemmas.algebraMap_epsP hes hesum
  set ε := Formalism.IndefR.Fin.LevelGroupLemmas.epsP (locPl G t)
  have hid : IsIdempotentElem (1 - ε) := hε.one_sub

  have hle1 : j + 1 ≤ D.R.m := by omega
  have hle2 : j + 1 + 1 ≤ D.R.m := hj
  have hr1 := rank_top G hle1
  have hr2 := rank_top G hle2

  set V := G.V (.top (j + 1))
  set g : GA D V := (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D V)
  have hgf : g ∈ GfC V := ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))).2
  have hcut : cutPart (1 - (e + cA D e)) V g = Formalism.IndefR.Fin.LevelGroupLemmas.resG V (1 - ε) g :=
    cut_one_sub_eq_resG_one_sub_of_isIdempotentElem V hε halg g

  have hnodd : ¬ Odd (G.pS (Pair.top t (j + 1))).rank := by
    rw [Nat.not_odd_iff_even]
    change Even (G.V (.top (j + 1))).rank
    rw [hr1]
    exact rankX_even D _
  have hnodd' : ¬ Odd (G.pT (Pair.top t (j + 1))).rank := by
    rw [Nat.not_odd_iff_even]
    change Even (G.V (.top (j + 1 + 1))).rank
    rw [hr2]
    exact rankX_even D _
  have hmu : Formalism.IndefR.Fin.UnrOff e (L.mu t (j + 1 + 1)) := unrOff_mu_locPl G hL t ⟨j + 1, hj⟩ he
  have hchS : G.chrS (Pair.top t (j + 1)) = L.mu t (j + 1 + 1) := by
    simp only [GridData.chrS, Formalism.IndefR.Lift.attChr, hnodd, if_false]
    rfl
  have hchT : G.chrT (Pair.top t (j + 1)) = L.mu t (j + 1 + 1) := by
    simp only [GridData.chrT, Formalism.IndefR.Lift.attChr, hnodd', if_false]
    rfl

  have hfrS := isFrame_moved (S.N.latS (Pair.top t (j + 1))) (G.Λ (.top (j + 1))) (S.βp (j + 1))
    (Lev.finE V (S.N.u (.top (j + 1))).1) (S.βp_is (j + 1) hle1) (S.N.u_lat (.top (j + 1)) hle1)
  have hfrT := isFrame_moved (S.N.latT (Pair.top t (j + 1))) (G.Λ (.top (j + 1 + 1))) (S.βp (j + 1 + 1))
    (Lev.finE (G.V (.top (j + 1 + 1))) (S.N.u (.top (j + 1 + 1))).1) (S.βp_is (j + 1 + 1) hle2)
    (S.N.u_lat (.top (j + 1 + 1)) hle2)
  have hst := cut_conj_unipotent_mem_St_succ S j hj k hk he

  have hVF := Formalism.IndefR.Fin.LevelGroupLemmas.vacFixOff (Formalism.IndefR.Fin.splitLinF D) (Formalism.IndefR.Fin.placeModelAtF D)
    (Formalism.IndefR.Fin.splitOrInert D)
  have hW := W.om_is (Pair.top t (j + 1)) hle2
  refine hVF W.ψ _ _ _ _ _ hW (GlobalTheory.InertAll.inertAllO D _ _ _ _ _ _ hW) ?_ ?_ _ _
    (GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on _ hle1))
    (GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on _ hle2))
    _ _ hfrS hfrT (locPl G t) e he (by rw [hchS]; exact hmu) (by rw [hchT]; exact hmu) _ hθ hlat ?_ _ 1 ?_
    (Subgroup.one_mem _) hst (by rw [map_one]; exact Subgroup.one_mem _) ?_ ?_
  · change (G.V (.top (j + 1))).rank ≠ (G.V (.top (j + 1 + 1))).rank
    rw [hr1, hr2]
    unfold GlobalTheory.ChiGrid.rankX
    rw [add_mul (j + 1) 1, one_mul]
    generalize (j + 1) * (D.R.t + 1) = a
    omega
  · left
    change Even (G.V (.top (j + 1))).rank
    rw [hr1]
    exact rankX_even D _
  · obtain ⟨⟨μ, 𝓕⟩, hμ⟩ := hcov
    exact ⟨μ, 𝓕, hμ, hnrm ⟨μ, 𝓕⟩ hμ⟩
  · change cutPart (1 - (e + cA D e)) V g ∈ GfC V
    rw [hcut]
    exact Formalism.IndefR.Fin.LevelGroupLemmas.resG_mem_GfC V hid hgf
  · intro i j'
    change (e + cA D e) * (Formalism.L2.Theta.mt V (cutPart (1 - (e + cA D e)) V g) - 1) i j' = 0
    rw [hcut, Formalism.IndefR.Fin.LevelGroupLemmas.mt_resG_sub hid, ← mul_assoc, ← halg, ← map_mul, mul_sub, mul_one, hε.eq,
      sub_self, map_zero, zero_mul]
  · intro i j'
    simp [Formalism.L2.Theta.mt]

end GlobalTheory.OffPartVac

end
