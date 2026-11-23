import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FillPreservesIdempotent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOfFinOrderFbar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldHostConductorIsRayClassFieldStatement

noncomputable section

namespace GlobalTheory.ParRay

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_types : GlobalTheory.Published.RayClassFieldSt → GlobalTheory.Published.ChebotarevDegreeOne → ∀ (D : D7) (hE : IsEmpty D.nd.Loc)
    (jE : D.host.E →+* Qb) (Pl : PlSide D), (∀ k, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g k)) →
    ∃ X h1 h0, X.tg = D.ntypes.tg ∧ X.teichC = D.ntypes.teichC ∧ X.eSer = D.ntypes.eSer ∧ X.cenAmb = D.ntypes.cenAmb ∧
      X.cenMt = D.ntypes.cenMt ∧ Nonempty (ParSide (setTy D hE X h1 h0) jE) ∧
      (Nonempty (GrpSide D) → IotaOk (setTy D hE X h1 h0) ⟨Pl.ι, Pl.ι_w, Pl.plB, Pl.plB_eq, Pl.plκ⟩) := by
  intro hray _ D hE jE Pl hg
  obtain ⟨h, hf, hgal, hab, hunr, hsplit⟩ := GlobalTheory.T.rayClassFieldHostConductor_isRayClassField hray D jE
  letI := algK D jE h
  have := nfOf hf
  let X : NTypes D.naut :=
    { D.ntypes with
      Mray := MrayC D jE
      instMray := inferInstance
      nfMray := nfOf hf
      algKM := algK D jE h
      Mray_gal := hgal
      Mray_ab := hab
      Mray_unr := hunr
      g_Mray := fun k => hsplit _ (hg k)
      iota := fun k _ w =>
        haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
        redHom (Pl.plB w) (Pl.plκ w) (D.ntypes.teichC k)
      iota_inj := fun k _ w x y hx hy cx cy hxy =>
        haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
        redHom_inj (Pl.plB w) (Pl.plκ w) (D.ntypes.teichC k) (D.ntypes.teichC_inj k) x y hx hy cx cy hxy
      Par := ParC D
      labPar := fun k σ v => D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut σ.1 (D.naut.plGw k v))
      labPar_monic := fun k σ v => σ.2.2.2.2 k v
      locPar := fun σ w => isoLoc D.nd D.naut σ.1 w
      locPar_dim := fun σ w => (GlobalTheory.RowPar.lpDim_isoLoc D.naut σ.1 w).trans σ.2.2.2.1
      labPar_def := fun _ _ _ => rfl
      MtPar := fun _ _ _ => ⊥
      AmbPar := fun _ _ => ⊥ }
  refine ⟨X, D.nStage_trivialCharacter_compat, D.nStage_trivialCharacter_coeff_eq, rfl, rfl, rfl, rfl, rfl, ⟨?_⟩, fun _ => ?_⟩
  · exact
      { eM := RingEquiv.refl _
        eM_K := fun _ => rfl
        eP := Equiv.refl _
        locPar_def := fun _ _ => rfl }
  · intro lam k v x
    rfl

end GlobalTheory.ParRay

end
