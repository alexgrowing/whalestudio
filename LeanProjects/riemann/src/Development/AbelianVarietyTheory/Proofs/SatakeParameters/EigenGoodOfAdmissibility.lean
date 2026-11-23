import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowParamOfThetaLiftBaseChange
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EigGoodTypes

theorem tw_inv_eta {D : D7} (h0 : SumRepresentations.tie0 D) (h4 : SumRepresentations.ArchimedeanSignatureMatching D) (h5 : SumRepresentations.adm5 D) {a : ℕ} (ha : 1 ≤ a)
    (π : D.naut.CG a) : D.naut.tw (D.naut.tw π D.naut.etaTinv) D.naut.etaT = π := by
  have hLP : SumRepresentations.At.TieLP D.nd D.naut := h0.1
  have hC := h4.2.2
  have h := h5.1 [⟨a, D.naut.tw (D.naut.tw π D.naut.etaTinv) D.naut.etaT, 1⟩] [⟨a, π, 1⟩]
    (by simp [ha]) (by simp [ha]) (Filter.Eventually.of_forall fun w => by
      show isoLoc D.nd D.naut (twistIso D.nd D.naut (twistIso D.nd D.naut [⟨a, π, 1⟩] D.naut.etaTinv) D.naut.etaT) w = _
      rw [GlobalTheory.RowThetaParam.isoLoc_twistIso D.nd D.naut hLP hC, GlobalTheory.RowThetaParam.isoLoc_twistIso D.nd D.naut hLP hC,
        (GlobalTheory.RowThetaParam.lpChar_eta_inv D.nd D.naut hLP _).2])
  rw [List.singleton_perm_singleton] at h
  injection h with _ h2

theorem sig_parC {D : D7} (h0 : SumRepresentations.tie0 D) (h4 : SumRepresentations.ArchimedeanSignatureMatching D) (h5 : SumRepresentations.adm5 D) {i : D.nd.Loc} {P0 : D.naut.AV i}
    {Sig : List (Part D.naut.CG)}
    (hB : IsBCV D.nd D.naut i P0 (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv))
    (hg : goodSig D.nd D.naut Sig) :
    (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π) ∧
    (Sig.map fun p => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)).Nodup ∧
    rankIso D.nd D.naut Sig = D.R.r ∧
    ∀ (k : Fin 2) (v : D.nd.PlG k),
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).Monic ∧
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).natDegree = D.R.r := by
  obtain ⟨h1, h2, h3, -, -, -⟩ := hB
  refine ⟨fun p hp => ?_, ?_, ?_, fun k v => ⟨((hg k).1.1 v).1, ((hg k).1.1 v).2.1⟩⟩
  · have hm : (⟨p.a, D.naut.tw p.π D.naut.etaTinv, p.d⟩ : Part D.naut.CG) ∈
        twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv :=
      List.mem_map.2 ⟨p, List.mem_append_left _ hp, rfl⟩
    obtain ⟨ha, hd, hc⟩ := h1 _ hm
    refine ⟨ha, hd, ?_⟩
    have := D.naut.csd_tw _ _ h0.2.1.1.1 hc
    rwa [tw_inv_eta h0 h4 h5 ha] at this
  · have hinj : Function.Injective (fun p : Part D.naut.CG => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)) := by
      rintro ⟨a, π, d⟩ ⟨a', π', d'⟩ h
      simp only [Prod.mk.injEq, Sigma.mk.inj_iff] at h
      obtain ⟨⟨rfl, h⟩, rfl⟩ := h
      cases h
      rfl
    have hn : (Sig ++ [muPart D.nd D.naut i]).Nodup := by
      unfold twistIso at h2
      rw [List.map_map] at h2
      exact List.Nodup.of_map _ h2
    exact (hn.sublist (List.sublist_append_left _ _)).map hinj
  · have e1 : (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv).map (fun p => p.a * p.d) =
        (Sig ++ [muPart D.nd D.naut i]).map (fun p => p.a * p.d) := by
      unfold twistIso
      rw [List.map_map]
      rfl
    unfold rankIso at h3 ⊢
    rw [e1, List.map_append, List.sum_append] at h3
    simp only [muPart, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero] at h3
    have : D.R.nV = D.R.r + D.R.t := rfl
    omega

theorem eigC_le {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (P : Pin hL D) (h41 : Formalism.MainNotions.SumRepresentations.Conclusion41 D)
    (hMt : MtParTie D.nd D.naut D.ntypes) (hbc : Formalism.MainNotions.SumRepresentations.adm1 D) (h0 : SumRepresentations.tie0 D) (h4 : SumRepresentations.ArchimedeanSignatureMatching D)
    (h5 : SumRepresentations.adm5 D) (i : D.nd.Loc) (x : D.nd.X i) (hx : x ∈ ZgoodN D.nd D.naut i) :
    ∃ σ' : D.ntypes.Par, eigC D.nd D.naut i x ≤ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ' ∧ D.ntypes.goodPar σ' := by
  obtain ⟨-, Sig, ⟨P0, hP0, hB0⟩, hg⟩ := hx
  let σ' : D.ntypes.Par := P.ty.par.eP.symm ⟨Sig, sig_parC h0 h4 h5 hB0 hg⟩
  have hloc : ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut Sig w := fun w => by
    have e : P.ty.par.eP σ' = ⟨Sig, sig_parC h0 h4 h5 hB0 hg⟩ := Equiv.apply_symm_apply _ _
    rw [P.ty.par.locPar_def, e]
  refine ⟨σ', ?_, ?_⟩
  · rw [hMt i σ']
    refine iSup₂_le fun Q hQ => le_iSup₂_of_le Q ⟨Sig, fun w => (hloc w).symm, ?_⟩ le_rfl
    have hQ' : D.naut.ptV i Q = some x := hQ
    obtain ⟨Pa, hPa⟩ := hbc i Q
    have hperm := ((h41 i).2.1 P0 Q (by rw [hP0]; simp) (hP0.trans hQ'.symm)).1 _ _ hB0 hPa
    exact GlobalTheory.RowThetaParam.isBCV_of_perm D.nd D.naut hperm.symm hPa
  · intro k
    simp only [D.ntypes.labPar_def, hloc]
    exact hg k

theorem onMt_cast {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) (f : D.what₂.Mt μ a)
    (H : D.ntypes.onMt μ b D.ntypes.e0 (h ▸ f) = h ▸ f) : D.ntypes.onMt μ a D.ntypes.e0 f = f := by
  subst h
  exact H

theorem main : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp),
    Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.tieLab D → MtParTie D.nd D.naut D.ntypes → Formalism.MainNotions.SumRepresentations.adm1 D → Formalism.MainNotions.SumRepresentations.tie0 D →
    Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D → Formalism.MainNotions.SumRepresentations.adm5 D → GlobalTheory.NRows.GoodIdempotentFixesLocalisationForms D → GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector X → ∀ i, GlobalTheory.NJoin.EigGood X i := by
  intro hL D P X h41 _ hMt hbc h0 h4 h5 hE0 hRead i hμ j hj x hx f hf y hy
  obtain ⟨σ', hle, hgood⟩ := eigC_le P h41 hMt hbc h0 h4 h5 i x hx
  exact (hRead _ hμ j f y hy).1 (onMt_cast hj f (hE0 i σ' _ (hle hf) hgood))

end GlobalTheory.EigGoodTypes

end
