import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenNormalSubgroupUnderInertiaStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.ResSel.OddBound

theorem dec_le_of_frob_mem {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) {σ : G F Ω}
    (hσ : IsFrob A (normV v) σ) {L : Subgroup (G F Ω)} (hL : IsOpen (L : Set (G F Ω))) (hI : Ine (F := F) A ≤ L)
    (hm : σ ∈ L) : Dec (F := F) A ≤ L := by
  have h := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω A v hA ⟨σ, hσ.1⟩ hσ
  have hc : IsClosed ((L.subgroupOf (Dec (F := F) A) : Subgroup (Dec (F := F) A)) : Set (Dec (F := F) A)) :=
    (L.isClosed_of_isOpen hL).preimage continuous_subtype_val
  have h2 := Subgroup.topologicalClosure_minimal
    (Subgroup.zpowers (⟨σ, hσ.1⟩ : Dec (F := F) A) ⊔ (Ine (F := F) A).subgroupOf (Dec (F := F) A))
    (sup_le ((Subgroup.zpowers_le).2 (Subgroup.mem_subgroupOf.2 hm)) (fun x hx => hI hx)) hc
  rw [h] at h2
  intro g hg
  exact h2 (Subgroup.mem_top (⟨g, hg⟩ : Dec (F := F) A))

theorem residual_bound_of_parts : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), (∀ i, StepAB X i) → (∀ i, ChooseH bkP i) → (∀ i s, GalHyp bkP i s → ResBound bkP i s) → ResidualBoundOddPrimes bkP := by
  intro D N X bkP hAB hCh hRB i hl T hT
  obtain ⟨R, hR⟩ := hCh i T hT
  refine ⟨R, 4 * D.R.r * R, 4 * D.R.r * R + 2, fun M hM H S d hd z hz H' ho hn A => ?_⟩
  have hp : (X.l i).Prime := (X.lPrime i).out
  have hlt : 4 * D.R.r * R + 2 < X.l i ^ M := lt_of_le_of_lt hM (Nat.lt_pow_self hp.one_lt)
  obtain ⟨L, hLo, hLn, hLH, hLs, hLζ, -⟩ := GlobalTheory.T.exists_open_normal_subgroup_under_inertia D N X bkP i T hT z hz M H hd.1 hd.2.1 hd.2.2.1
  obtain ⟨h, U, hh, hUo, hUn, hUL, hco⟩ := hR z hz L hLo hLn hLs
  obtain ⟨P, hAux, hSt, hIne, hFr⟩ := hAB i M (by omega) H S d hd z hz (U ⊓ H') (hUo.inter ho) inferInstance A R h
    (fun a => ⟨hLH (hh a), hLζ _ (hh a)⟩)
  choose φ g hφ hg using hFr
  have mono : ∀ V : Subgroup (GE N), U ⊓ H' ≤ V → Steps X i M V z P (fun q => d (P q)) := fun V hV =>
    ⟨fun a σ hσ => (hSt.1 a σ hσ).imp fun _ hg => hV hg, hSt.2⟩
  have hUL' : U ⊓ H' ≤ L := inf_le_left.trans hUL
  refine ⟨P, hAux, mono H' inf_le_right, fun s hs Q hQ a Φ hΦ F hF => ?_⟩
  have hφL : ∀ a, φ a ∈ L := fun a => by
    have h1 := L.mul_mem (hUL' (hg a)) (hh a)
    rw [inv_mul_cancel_right] at h1
    simpa [mul_assoc] using hLn.conj_mem _ h1 (g a)⁻¹
  have hcj : ∀ a, IsCj X (φ a) (GlobalTheory.TwistDet.cConj X (φ a)) := fun a x => rfl
  have hPos : Position i s M P (fun q => d (P q)) φ (fun a => GlobalTheory.TwistDet.cConj X (φ a)) := by
    refine ⟨⟨fun q v hv => ?_, hAux.2⟩, ⟨z, L, hz, hLs s hs, mono L hUL'⟩, fun a => ⟨fun k hk => ?_, hφ a, hcj a⟩⟩
    · obtain ⟨h1, h2, h3, h4, -, h6⟩ := hAux.1 q v hv
      exact ⟨h1, h2, h3, h4, Finset.notMem_empty _, h6⟩
    · exact (hLs s hs).2.2.2.2 k (dec_le_of_frob_mem (N.plOm.2 _) (hφ a) hLo
        ((hIne _ _ (Or.inl rfl) _ (N.plOm.2 _)).trans hUL') (hφL a) hk)
  have hc := hco φ (fun a => GlobalTheory.TwistDet.cConj X (φ a)) (fun a => ⟨hcj a, g a, (hg a).1⟩) s hs
  rw [if_pos hl] at hc
  obtain ⟨m, hm, hu⟩ := (hRB i s (hT s hs) M R P _ φ _ Q hlt hPos hQ a Φ hΦ).1 hc F hF
  exact ⟨m, hm, (IsDiscreteValuationRing.addVal_eq_zero_iff.2 hu).le⟩

end GlobalTheory.ResSel.OddBound
