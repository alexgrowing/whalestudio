import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSymmetricFormAlongDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRingActionOfIsPullDeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartForm

section Balance

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ) (D : DegPre V)

include hϖ in

theorem bOf_balance {Q : D.X → ℤ} {O : Type} [Ring O] [StarRing O] [Module O D.X] (ιD : D.OAct O)
    (hQ : QForm.IsQ D ϖ Q) (a : O) (χ χ' : D.X) :
    QForm.bOf D Q (a • χ) χ' = QForm.bOf D Q χ (star a • χ') := by
  have hL := D.P.isLB
  have := ιD.onB.hom a
  have := ιD.onB.hom (star a)
  obtain ⟨u, hu, hnorm⟩ := exists_ros GlobalTheory.globalFns_holds D.P.isAb D.P.isLB _ _ (ιD.onB.rosati a)
  have hc := ιD.tau_bal a u hu hnorm χ χ'
  obtain ⟨_, _, hsA, hA⟩ := GlobalTheory.PreValForm.tau_val' hϖ D hQ (a • χ) χ'
  obtain ⟨_, _, hsB, hB⟩ := GlobalTheory.PreValForm.tau_val' hϖ D hQ χ (star a • χ')
  have hu0 := genHasVal_pullGen_of (ϖ := ϖ) D.P.L _ _ u hu (lift (D.c χ) (D.c χ')).left
    (D.pt2 χ χ') (by simp [DegPre.pt2, ← CartesianMonoidalCategory.comp_lift])
  have h1 := genHasVal_mulGen hϖ D.P.L hL _ _ _ _ _ _ _ _ _ _ hA hu0
  have := genHasVal_unique hϖ D.P.L hL _ _ _ _ _
    (genHasVal_corr hϖ D.P.L hL D.P.A.hom _ _ _ _ _ _ _ _
      (QForm.sumElim_sec hsA (fun k => by
        obtain ⟨q, hq⟩ := QForm.rosatiφ_over D.P.A (ιD.onB.act a) (ιD.onB.act (star a)) k
        show (_ ≫ rosatiφ D.P.A (ιD.onB.act a) (ιD.onB.act (star a)) k) ≫ _ = _
        rw [hq]; exact QForm.over_sec _ _)) hsB _ _
      (genHasVal_isGen D.P.L _ _ _ _ _ hB) hc h1) hB
  linarith

end Balance

theorem exists_balanced_formAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R]
    [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), IsCN R →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ ϖ : V, Irreducible ϖ →
      ∀ (ψ : R →+* V) (gam : FractionRing R →+* FractionRing V), (∀ r, gam (algebraMap R _ r) = algebraMap V _ (ψ r)) →
      ∃ be ∈ levelForms H 1 P.D.toPre.X, FormAt P.D.toPre ψ ϖ be := by
  intro E _ _ _ H R _ _ _ t P hR V _ _ _ hV ϖ hϖ f gam hgam
  obtain ⟨_, hIC, _, hch⟩ := hR
  obtain ⟨hdvr, _, _⟩ := hV
  haveI := hch
  haveI := hdvr
  have hf : Function.Injective f := by
    intro a b h
    apply IsFractionRing.injective R (FractionRing R)
    apply gam.injective
    rw [hgam, hgam, h]
  letI := H.starRing
  obtain ⟨W₀, hW₀, hψ⟩ := GlobalTheory.PsiSpread.exists_psiOn P.D.toPre P.D.tau_bimult
  have hη : (specOf f).base (genericPoint (Spec (CommRingCat.of V))) ∈ W₀ := by
    have : (specOf f).base (genericPoint (Spec (CommRingCat.of V))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective f hf)
    rw [this]; exact hW₀
  obtain ⟨D', hD, -, -⟩ := GlobalTheory.StrictPull.exists_isPullDeg_strict GlobalTheory.allSixLaws.1 R V f P.D.toPre W₀ hψ hη
  have hB : D'.TauBimult := GlobalTheory.TauPull.tauBimult_pull GlobalTheory.globalFns_holds hD P.D.tau_bimult
  have hE : D'.PsiEven := GlobalTheory.PsiEvenPull.psiEven_pull GlobalTheory.globalFns_holds R V f P.D.toPre D' hD P.D.psi_even
  obtain ⟨inst, ιD', hlin, -⟩ :=
    GlobalTheory.exists_oAct_of_isPullDeg GlobalTheory.globalFns_holds R V f P.D.toPre D' hD (𝓞 E) P.oD
  choose Q hQ using GlobalTheory.PreValForm.qVal_exists hϖ D'
  have hQ' : QForm.IsQ D' ϖ Q := hQ
  let B : D'.X →+ D'.X →+ ℤ :=
    AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun b => QForm.bOf D' Q a b) (fun b b' => by
        rw [GlobalTheory.PreValForm.bOf_comm' D' (Q := Q) a (b + b'), GlobalTheory.PreValForm.bOf_add_left' hϖ D' hB hQ',
          GlobalTheory.PreValForm.bOf_comm' D' (Q := Q) b a, GlobalTheory.PreValForm.bOf_comm' D' (Q := Q) b' a]))
      (fun a a' => by ext b; simp [GlobalTheory.PreValForm.bOf_add_left' hϖ D' hB hQ'])
  let be : LinearMap.BilinForm ℤ P.D.toPre.X :=
    LinearMap.mk₂ ℤ (fun y z => B (hD.xe.symm y) (hD.xe.symm z))
      (fun y y' z => by simp only [map_add, AddMonoidHom.add_apply])
      (fun c y z => by simp only [map_zsmul, AddMonoidHom.smul_apply, smul_eq_mul])
      (fun y z z' => by simp only [map_add])
      (fun c y z => by simp only [map_zsmul, smul_eq_mul])
  have hbe : ∀ y z, be y z = QForm.bOf D' Q (hD.xe.symm y) (hD.xe.symm z) := fun _ _ => rfl
  have hsm : ∀ (a : 𝓞 E) (y : P.D.toPre.X), hD.xe.symm (a • y) = a • hD.xe.symm y := fun a y =>
    hD.xe.symm_apply_eq.2 (by rw [hlin, AddEquiv.apply_symm_apply])
  refine ⟨be, (mem_levelForms).2 ⟨fun y z => by rw [hbe, hbe, GlobalTheory.PreValForm.bOf_comm'], fun a y z => ?_,
    fun y z => by simp⟩, fun y => ?_⟩
  · rw [hbe, hbe, hsm, hsm]
    exact GlobalTheory.ChartForm.bOf_balance hϖ D' ιD' hQ' a _ _
  · obtain ⟨r, hr, -⟩ := (GlobalTheory.PsiCoordLocal.main R P.D hIC y).1
    have hr' : Formalism.L2.Pj.PsiCoord P.D.toPre (hD.xe (hD.xe.symm y)) r := by
      rw [AddEquiv.apply_symm_apply]; exact hr
    obtain ⟨u, hu⟩ := GlobalTheory.PelCoordPull.psiCoord_pull hD (hD.xe.symm y) r hr'
    obtain ⟨h0, hassoc⟩ := GlobalTheory.PreValForm.assoc_of_hasVal hϖ (GlobalTheory.ValForm.hasVal_coord (hQ (hD.xe.symm y)) hu)
    refine ⟨r, (Q (hD.xe.symm y)).toNat, hr, ?_, ?_⟩
    · rw [hbe, ← GlobalTheory.PreValForm.two_Q_eq' hϖ D' hB hE hQ', Int.toNat_of_nonneg h0]
    · exact (associated_unit_mul_left (f r) (u : V) u.isUnit).symm.trans hassoc

end GlobalTheory.ChartForm
