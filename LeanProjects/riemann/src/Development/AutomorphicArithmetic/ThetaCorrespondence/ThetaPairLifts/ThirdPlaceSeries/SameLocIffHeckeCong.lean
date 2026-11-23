import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocationsDistinguishedByGenerics
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForcedByAutomorphicSemisimpleData

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
noncomputable section
namespace GlobalTheory.CoefDuty
set_option synthInstance.maxHeartbeats 400000 in
theorem sameLoc_iff_heckeCong_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L → ∀ (j : ℕ) (w : D.what₂.places.Pl) (i i' : L.X.nd.Loc), i ∈ L.X.nd.locs j w → i' ∈ L.X.nd.locs j w → ∀ (x : L.X.nd.X i) (x' : L.X.nd.X i'), (i = i' ↔ ∀ (v : PlE D.host) (k : ℕ), GenAt D (D.what₂.places.resChar w) (C.Q w) v k → iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x) - iotaO L.X.nd L.Y.naut i' ((L.X.nd.hT i' v k : L.X.nd.X i' → L.X.nd.O i') x') ∈ (A.pl.plB w).nonunits) := by
  intro D cf jE A M C tup big L hB j w i i' hi hi' x x'
  obtain ⟨Sp, ⟨Au⟩, -⟩ := hB
  have hiC : ∀ (a : L.X.nd.Loc) (ha : a ∈ L.X.nd.locs j w) (z : L.X.nd.O a),
      iotaO L.X.nd L.Y.naut a z = Sp.iotaC j w (Sp.phO j w a ha z) := by
    intro a ha z
    rw [← Sp.iotaC_coh j w a ha z]
    show ((L.Y.naut.iotaQC a).toRingHom.comp (L.Y.naut.iotaQ a)) (algebraMap _ _ z) = _
    rw [RingHom.comp_apply, Au.iotaQ, Au.iotaQC]
    rfl
  have key : ∀ (a : L.X.nd.Loc) (ha : a ∈ L.X.nd.locs j w) (y : L.X.nd.O a),
      iotaO L.X.nd L.Y.naut a y ∈ (A.pl.plB w).nonunits ↔ y ∈ IsLocalRing.maximalIdeal (L.X.nd.O a) := by
    intro a ha y
    have hw : L.X.nd.w a = w := ((L.X.nd.locs_mem j w a).1 ha).2
    subst hw
    obtain ⟨h, e⟩ := Au.kFbar a y
    rw [ValuationSubring.mem_nonunits_iff]
    have e1 : (A.pl.plB (L.X.nd.w a)).valuation (iotaO L.X.nd L.Y.naut a y) =
        (A.pl.plB (L.X.nd.w a)).valuation ((⟨_, h⟩ : A.pl.plB (L.X.nd.w a)) : ℂ) := rfl
    rw [e1, ← ValuationSubring.valuation_lt_one_iff, ← IsLocalRing.residue_eq_zero_iff,
      ← IsLocalRing.residue_eq_zero_iff, ← map_eq_zero (L.Y.naut.kFbar a), ← e]
    simp only [EmbeddingLike.map_eq_zero_iff]
  have gen : ∀ v k, GenAt D (D.what₂.places.resChar w) (C.Q w) v k ↔
      GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k := by
    intro v k; rw [Sp.Qc_eq]
  constructor
  · rintro rfl v k hvk
    have hvk' := (gen v k).1 hvk
    have e1 := Sp.ptX_hT j w i hi x v k hvk'
    have e2 := Sp.ptX_hT j w i hi' x' v k hvk'
    have hc : Formalism.L2.NCov.cls (Sp.ptX j w i hi x).1 = Formalism.L2.NCov.cls (Sp.ptX j w i hi' x').1 :=
      (Sp.ptX j w i hi x).2.1.trans (Sp.ptX j w i hi' x').2.1.symm
    generalize (Sp.ptX j w i hi x).1 = ψ at e1 hc
    generalize (Sp.ptX j w i hi' x').1 = ψ' at e2 hc
    generalize (⟨Sp.B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk', rfl⟩⟩ : heckeAlg Sp.B j w) = t at e1 e2
    have hmem : t - algebraMap _ _ (ψ t) ∈ Formalism.L2.NCov.cls ψ' := by
      rw [← hc, Formalism.L2.NCov.cls, RingHom.mem_ker]
      change IsLocalRing.residue _ (ψ (t - algebraMap _ _ (ψ t))) = 0
      rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self, map_zero]
    rw [Formalism.L2.NCov.cls, RingHom.mem_ker] at hmem
    change IsLocalRing.residue _ (ψ' (t - algebraMap _ _ (ψ t))) = 0 at hmem
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, map_sub, sub_eq_zero, ← e1, ← e2] at hmem
    have r := GlobalTheory.PtLocalEig.residue_map_equiv (Sp.phO j w i hi).symm hmem
    simp only [RingEquiv.symm_apply_apply] at r
    rw [← map_sub]
    refine (key i hi _).2 ?_
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, r, sub_self]
  · intro H
    apply Sp.mx_inj j w hi hi'
    rw [← (Sp.ptX j w i hi x).2.1, ← (Sp.ptX j w i' hi' x').2.1]
    refine GlobalTheory.PtLocalEig.cls_eq_of_residue _ _ _ ?_
    rintro _ ⟨v, k, hvk, rfl⟩
    rw [← Sp.ptX_hT j w i hi x v k hvk, ← Sp.ptX_hT j w i' hi' x' v k hvk]
    have h1 := H v k ((gen v k).2 hvk)
    have hz : iotaO L.X.nd L.Y.naut i' ((L.X.nd.hT i' v k : L.X.nd.X i' → L.X.nd.O i') x') =
        iotaO L.X.nd L.Y.naut i ((Sp.phO j w i hi).symm
          (Sp.phO j w i' hi' ((L.X.nd.hT i' v k : L.X.nd.X i' → L.X.nd.O i') x'))) := by
      rw [hiC i hi, hiC i' hi', RingEquiv.apply_symm_apply]
    rw [hz, ← map_sub, key i hi, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at h1
    have h2 := GlobalTheory.PtLocalEig.residue_map_equiv (Sp.phO j w i hi) h1
    rwa [RingEquiv.apply_symm_apply] at h2
end GlobalTheory.CoefDuty
end
end
