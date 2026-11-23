import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRigidifiedIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TautologicalModel
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.UnifCoordPull

theorem exists_unif_psiCoord : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN R → IsCN V → ∀ ψ : R →+* V, IsLocalHom ψ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (W : Set (Sp R)), IsOpen W → (∀ y, PsiUnitOn D.toPre y W) → (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum R) ∈ W → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap ψ) β → IsAbelianScheme ((Over.pullback (jK V)).obj G') → Rigidified ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → Out.Sym ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → RelAmple ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → KTriv ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → ∃ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (ε : D'.toPre.X ≃+ D.toPre.X), LBIso (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) (U'.LG.L.pull (pullback.fst G'.hom (jK V))) ∧ ∀ y r, PsiCoord D.toPre (ε y) r → ∃ u : Vˣ, PsiCoord D'.toPre y (u * ψ r) := by
  intro R _ _ _ V _ _ _ hR hV ψ hψl G _ _ hG D A U W hWo hψ hker G' _ _ β hpb hab hrig hsym hamp hkt
  obtain ⟨-, -, -, h4, -⟩ := GlobalTheory.firstFiveLaws
  have aR := admissibleBase_of_completeNormalLocalCharZero hR
  have aV := admissibleBase_of_completeNormalLocalCharZero hV
  have hI : (maximalIdeal R).map ψ ≤ maximalIdeal V :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (map_mem_nonunits_iff ψ a).2 ha
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso hpb (isGrpPullback_pullback G (spMap ψ))
  subst hbc

  have := hG.smooth
  have := hG.geomConnected
  have : ConnectedSpace (Sp R) := inferInstanceAs (ConnectedSpace (PrimeSpectrum R))
  have : ConnectedSpace G.left := GeometricallyConnected.connectedSpace G.hom G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected G.hom (Classical.arbitrary _)
  have hgA := GlobalTheory.ThetaBaseChange.grp_generic U.toUnifPre
  have hgK := (isGrpPullback_pullback G' (jK V)).comp hpb
  have dA : d = A.g := H1.dim_unique _ ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hgA.1 hd)
    A.smoothDim (eSec A.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R)))
  have hdK : SmoothOfRelativeDimension A.g ((Over.pullback (jK V)).obj G').hom :=
    dA ▸ (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hgK.1 hd
  have he := GlobalTheory.PolBaseChange.eSec_comm hpb
  let A' : PolAV (Sp (FractionRing V)) :=
    { A := (Over.pullback (jK V)).obj G'
      isAb := hab
      g := A.g
      smoothDim := hdK
      L := U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ bc.hom.left ≫ pullback.fst G.hom (spMap ψ))
      isLB := pull_isLB U.LG.isLB _
      rigid := hrig
      sym := hsym
      ample := hamp
      ktriv := hkt }
  have eAm : IsMonHom (Iso.refl A'.A).hom := show IsMonHom (𝟙 A'.A) from inferInstance
  have wA : ∃ wA : LB.Iso (A'.L.pull (Iso.refl A'.A).hom.left)
      (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf ψ))), wA.IsGen := by
    have k : LBIso (A'.L.pull (𝟙 _)) (U.LG.L.pull (𝟙 _ ≫ pullback.fst G'.hom (jK V) ≫ bc.hom.left ≫
        pullback.fst G.hom (specOf ψ))) :=
      ⟨GlobalTheory.Proof.TautologicalModel.taut U.LG.L _ (𝟙 _), GlobalTheory.Proof.TautologicalModel.taut_isGen U.LG.isLB _ _⟩
    rw [Category.id_comp] at k
    exact k
  let L' : RigLB G' := ⟨U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (spMap ψ)),
    rigPullOf (G' := G') (G := G) (bc.hom.left ≫ pullback.fst G.hom (spMap ψ)) (spMap ψ) he U.LG.L U.LG.rig, pull_isLB U.LG.isLB _,
    GlobalTheory.Proof.TautologicalModel.rigPullOf_isGen (G' := G') (G := G) (bc.hom.left ≫ pullback.fst G.hom (spMap ψ)) (spMap ψ) he U.LG.L U.LG.rig U.LG.rigGen⟩
  obtain ⟨wL, gL, rL⟩ := GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso _ _ (spMap ψ) G G' _ he U.LG L'
    (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB U.LG.isLB _))
  have hgen : (specOf ψ).base (genericPoint (Spec (CommRingCat.of V))) ∈ (⟨W, hWo⟩ : (Sp R).Opens) := by
    have : (specOf ψ).base (genericPoint (Spec (CommRingCat.of V))) =
        (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum R) := by
      rw [genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext rfl
    rw [this]; exact hker
  obtain ⟨D', hD, U', hLG, -, -⟩ := h4.unifBaseChange R V _ _ aR aV ψ hI D A G hG U ⟨W, hWo⟩
    (GlobalTheory.PelCoordPull.nonempty_psiOn D.toPre ⟨W, hWo⟩ ⟨_, hker⟩ hψ) hgen G' bc mbc A' rfl (Iso.refl _) eAm wA
    L' wL he gL rL
  refine ⟨D', A', U', hD.xe, ?_, fun y r hr => GlobalTheory.PelCoordPull.psiCoord_pull hD y r hr⟩
  rw [hLG]
  exact LBIso.symm ⟨GlobalTheory.Proof.TautologicalModel.taut U.LG.L _ _, GlobalTheory.Proof.TautologicalModel.taut_isGen U.LG.isLB _ _⟩

end GlobalTheory.UnifCoordPull
