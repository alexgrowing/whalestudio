import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocUnramB
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.LocUnramB

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups MeasureTheory Formalism.L2.SG.Pf.AtPt
open Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Restr2

variable {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem thRestricted_of (hA : ∀ p, Agree δ M p) (hrows : IsRowReps D F0 what₂)
    (hN : PairVal.NormRepExists D u u' F0 what₂) (hRel : PCount.EligRel u u' F0 what₂) :
    ThRestricted M δ u u' F0 what₂ (LocModel.thTriv M) := by
  intro γ w h
  have hZ : PCount.AtMat w (zT γ) := PCount.atMat_zT hN hrows h (hRel γ w h)

  have hpt : ptT γ = w := by
    have h0 := h
    obtain ⟨⟨hgen, -⟩, hat⟩ := h
    obtain ⟨y, hy⟩ := hN γ w hat (hRel γ w h0) hgen
    have hex : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) ×
        PairVal.MatR D × PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 := ⟨(w, y), hy⟩
    have hn : nrep γ = some hex.choose := dif_pos hex
    obtain ⟨hRep, -, hL, hU, e⟩ := hex.choose_spec
    obtain ⟨F₁, hR₁, -, hc₁⟩ := hat
    have hw : w = hex.choose.1 := pt_eq_of_cells cell_point_uniqueness (Formalism.L2.SG.Closed.TermFun_holds D u u') hrows γ
      hR₁ hRep hc₁ ⟨_, _, hL, hU, e⟩
    unfold ptT
    rw [hn]
    exact hw.symm
  have hfin := PCount.tupZ_restr hA u u' hZ
    ((LocModel.good_cofinite δ M hA ∅).mono fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩)
    (fun x => LocModel.LM.iotaIntegral_almost_all D x)
  have hall := LocModel.good_cofinite δ M hA (w.1.map Prod.fst).toFinset
  rw [Filter.eventually_cofinite] at hall
  refine (hfin.union hall).subset fun p hp => ?_
  by_contra hq
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hq
  obtain ⟨htup, hg⟩ := hq
  have hg' : Good δ M w p := hg
  apply hp
  show thL M δ (D.mem u).A.T (D.mem u').A.T p (ptT γ) (CntLocal.ZZP (M := M) δ u u' p (zT γ)) = _
  rw [hpt]
  have hmem : CntLocal.ZZP (M := M) δ u u' p (zT γ) * LsDatumB.sgnP p ∈ x0L M δ (D.mem u).A.T (D.mem u').A.T p w := by
    rw [← htup]
    exact ⟨1, 1, one_intLow p, one_intUp p, by rw [Matrix.one_mul, Matrix.mul_one]⟩
  obtain ⟨l, ρ, hl, hρ, he⟩ := hmem
  have hZZ : CntLocal.ZZP (M := M) δ u u' p (zT γ) =
      l * modMat δ (D.mem u).A.T (D.mem u').A.T p w * ρ * LsDatumB.sgnP p := by
    rw [← he, Matrix.mul_assoc, permSign_mul_self₂, Matrix.mul_one]
  have e2 : CntLocal.ZZP (M := M) δ u u' p (zT γ) + cornerM p (cornerSh δ (D.mem u).A.T (D.mem u').A.T p w) =
      l * (modMat δ (D.mem u).A.T (D.mem u').A.T p w + cornerM p (cornerSh δ (D.mem u).A.T (D.mem u').A.T p w)) *
        ρ * LsDatumB.sgnP p := by
    rw [hZZ, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, loU_corner p _ ⟨hl.1, hl.2.1⟩ ⟨hρ.1, hρ.2.1⟩,
      corner_sgn]
  unfold thL
  apply clsOf_triv
  have e3 : (CntLocal.ZZP (M := M) δ u u' p (zT γ) + Matrix.of fun a b =>
      if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then cornerSh δ (D.mem u).A.T (D.mem u').A.T p w else 0) =
      l * (modMat δ (D.mem u).A.T (D.mem u').A.T p w + cornerM p (cornerSh δ (D.mem u).A.T (D.mem u').A.T p w)) *
        ρ * LsDatumB.sgnP p := e2
  rw [e3]
  refine isGL_mul _ (isGL_mul _ (isGL_mul _ (isGL_of_det_one _ hl.2.2 (det_loU ⟨hl.1, hl.2.1⟩))
    (shift_isGL _ _ w p (hA p) hg')) (isGL_of_det_one _ hρ.2.2 (det_upU ⟨hρ.1, hρ.2.1⟩))) (isGL_sgn p)

end Restr2

end Formalism.L2.SG.Pf.LocUnramB

namespace Formalism.L2.SG.Pf

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut

theorem thRestricted_holds_of {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (hA : ∀ p, Agree δ M p) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (hrows : IsRowReps D F0 what₂) (hN : Formalism.L2.SG.PairVal.NormRepExists D u u' F0 what₂)
    (hRel : PCount.EligRel u u' F0 what₂) :
    Formalism.L2.SG.LsDatumB.ThRestricted M δ u u' F0 what₂ (LocModel.thTriv M) :=
  LocUnramB.thRestricted_of hA hrows hN hRel

end Formalism.L2.SG.Pf
