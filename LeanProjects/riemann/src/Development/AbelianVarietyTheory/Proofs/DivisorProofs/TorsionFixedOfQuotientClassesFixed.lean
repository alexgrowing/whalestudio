import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramSub
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TorsFixed

theorem fixed_of_classes_fixed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ (V : Type) [CommRing V] [IsDomain V] (φ : R →+* V) [Algebra (FractionRing R) (AlgebraicClosure (FractionRing V))], (∀ r, algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ (φ r))) → ∀ k : ℕ, 1 ≤ k → ∀ σ : (AlgebraicClosure (FractionRing V)) ≃+* (AlgebraicClosure (FractionRing V)), (∀ v : V, σ (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ v)) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ v)) → (∀ p q : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k, QkExt σ.toRingHom p q → QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing V)) p q) → ∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ (Over.pullback (spMap φ)).obj G, x ^ k = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  intro R _ _ _ hB D A G _ _ hG U V _ _ φ _ hc k hk σ hσ hQ x hx
  haveI : CharZero R := hB.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws

  have sq : (jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V) ≫ spMap φ =
      jFK (R := R) (AlgebraicClosure (FractionRing V)) ≫ jK R := by
    show (spMap _ ≫ spMap _) ≫ spMap φ = spMap _ ≫ spMap _
    rw [← spMap_comp, ← spMap_comp, ← spMap_comp]
    congr 1
    ext r
    exact (hc r).symm
  have wx : x.left ≫ pullback.snd G.hom (spMap φ) = jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V := Over.w x
  have w₁ : (x.left ≫ pullback.fst G.hom (spMap φ)) ≫ G.hom = jFK (R := R) (AlgebraicClosure (FractionRing V)) ≫ jK R := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, wx, sq]
  let xG : Over.mk (jFK (R := R) (AlgebraicClosure (FractionRing V)) ≫ jK R) ⟶ G :=
    Over.homMk (x.left ≫ pullback.fst G.hom (spMap φ)) w₁
  have hxG : xG ^ k = 1 :=
    (GlobalTheory.PsiAbelian.pow_eq_one_iff_of_pull sq (isGrpPullback_pullback G (spMap φ)) (x := xG) (x' := x) rfl).1 hx

  have := U.gen_hom
  have : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have gp : IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) :=
    ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  let x₀ : TFK (R := R) (AlgebraicClosure (FractionRing V)) ⟶ A.A :=
    Over.homMk (gp.1.lift (x.left ≫ pullback.fst G.hom (spMap φ)) (jFK (R := R) (AlgebraicClosure (FractionRing V))) w₁)
      (gp.1.lift_snd _ _ _)
  have e₀ : x₀.left ≫ (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) = x.left ≫ pullback.fst G.hom (spMap φ) :=
    gp.1.lift_fst _ _ _
  have hx₀ : x₀ ^ k = 1 := (GlobalTheory.PsiAbelian.pow_eq_one_iff_of_pull rfl gp (x := xG) (x' := x₀) e₀).2 hxG

  have hσR : ∀ r : R, σ (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r)) =
      algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) := fun r => by
    rw [hc r, hσ]
  let σ' : AlgebraicClosure (FractionRing V) →ₐ[FractionRing R] AlgebraicClosure (FractionRing V) :=
    ⟨σ.toRingHom, fun a => RingHom.congr_fun
      (IsLocalization.ringHom_ext (nonZeroDivisors R)
        (j := σ.toRingHom.comp (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V))))
        (k := algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V))) (RingHom.ext hσR)) a⟩
  have hσf : σ.toRingHom.comp (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V))) =
      algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) := RingHom.ext σ'.commutes

  obtain ⟨f, hf, hsurj, hfi, -, -⟩ :=
    GlobalTheory.TorsionIso.torsion_eq hL R (maximalIdeal R) hB.1 D A G hG U (AlgebraicClosure (FractionRing V)) k hk
  obtain ⟨p, hp⟩ := hsurj x₀ hx₀
  let q := GlobalTheory.TorusExt.qkExt D.tau_bimult σ.toRingHom hσf p
  have hpq : QkExt σ.toRingHom p q := (GlobalTheory.TorusExt.qkExt_iff D.tau_bimult σ.toRingHom hσf p q).2 rfl
  have heq : f q = x₀ := ((hfi p q).2 (hQ p q hpq)).symm.trans hp
  have s₂ : spMap σ.toRingHom ≫ jFK (R := R) (AlgebraicClosure (FractionRing V)) =
      jFK (R := R) (AlgebraicClosure (FractionRing V)) := by
    refine (spMap_comp _ _).symm.trans ?_
    exact congrArg spMap hσf
  have wx₀ : x₀.left ≫ A.A.hom = jFK (R := R) (AlgebraicClosure (FractionRing V)) := Over.w x₀
  let x' : TFK (R := R) (AlgebraicClosure (FractionRing V)) ⟶ A.A :=
    Over.homMk (spMap σ.toRingHom ≫ x₀.left) (by rw [Category.assoc, wx₀, s₂]; rfl)
  have hq : QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) k q x' :=
    (GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt hL R (maximalIdeal R) hB.1 D A G hG U (AlgebraicClosure (FractionRing V))
      (AlgebraicClosure (FractionRing V)) σ' k hk p q x₀ x' hpq rfl).1 ((hf p x₀).2 hp.symm)
  have fix : spMap σ.toRingHom ≫ x₀.left = x₀.left := congrArg (fun z => z.left) (((hf q x').1 hq).trans heq)

  have sV : spMap σ.toRingHom ≫ jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V =
      jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V := by
    show spMap _ ≫ spMap _ ≫ spMap _ = spMap _ ≫ spMap _
    rw [← spMap_comp, ← spMap_comp]
    congr 1
    ext v
    exact hσ v
  refine pullback.hom_ext (f := G.hom) (g := spMap φ) ?_ ?_
  · rw [Category.assoc, ← e₀, ← Category.assoc, fix]
  · rw [Category.assoc, wx, sV]

end GlobalTheory.Mum.TorsFixed
