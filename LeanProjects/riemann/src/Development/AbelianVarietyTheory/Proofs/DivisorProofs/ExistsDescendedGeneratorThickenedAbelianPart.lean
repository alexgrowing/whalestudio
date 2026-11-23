import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MK
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordGeneratorAbelianPartAtLevelImports
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

noncomputable section
namespace GlobalTheory.HomMum

open GlobalTheory.EndRosati

set_option maxHeartbeats 800000 in

theorem exists_gen_thick_two : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f g : G₁ ⟶ G₂} [IsMonHom f] [IsMonHom g] {fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A} [IsMonHom fB] [IsMonHom gB], (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map fB → (Over.pullback (thick R I e)).map g ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map gB → ∀ (v : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => mφ (thickObj R I e G₁) (thickObj R I e G₂) ((Over.pullback (thick R I e)).map f) ((Over.pullback (thick R I e)).map g) k ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left) mε)), v.IsGen → (∀ (T : Over (Sp (R ⧸ I ^ (e + 1)))) (z : T.left) (J : (T.left ⟶ D₁.toPre.P.A.left ⨿ D₂.toPre.P.A.left) → (JN D₁.toPre D₂.toPre).ι), Good (JN D₁.toPre D₂.toPre) z J → ∀ x x' y y' : T ⟶ thickObj R I e G₁, x ≫ (U₁.gt e).q = x' ≫ (U₁.gt e).q → y ≫ (U₁.gt e).q = y' ≫ (U₁.gt e).q → val v (lift x y).left z J = val v (lift x' y').left z J) → ∃ t : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => pullback.fst (D₁.toPre.P.A ⊗ D₁.toPre.P.A).hom (thick R I e) ≫ mφ D₁.toPre.P.A D₂.toPre.P.A fB gB k) mε), t.IsGen := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ e f g _ _ fB gB _ _ hf hg v hv hi
  have hM := jn_isLB D₁.toPre D₂.toPre
  have := (U₁.gt e).q_affine
  have pp : ∀ {c : G₁ ⟶ G₂} {cB : D₁.toPre.P.A ⟶ D₂.toPre.P.A},
      (Over.pullback (thick R I e)).map c ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map cB →
      push (U₂.gt e).pG ((Over.pullback (thick R I e)).map c) = (U₁.gt e).pG ≫ cB := fun {c cB} h => by
    rw [push, GtCoord.pG, ← Functor.map_comp_assoc, h, Functor.map_comp_assoc, Category.assoc]
    exact congrArg _ (GlobalTheory.EndRosati.push_fstG e cB)
  let m := (U₁.gt e).q ⊗ₘ (U₁.gt e).q
  have : Flat m.left := MorphismProperty.pullbackMap (P := @Flat) (U₁.gt e).q_flat (U₁.gt e).q_flat
    (Over.w (U₁.gt e).q).symm (Over.w (U₁.gt e).q).symm
  have : Surjective m.left :=
    have : MorphismProperty.IsStableUnderComposition @Surjective.{0} := ⟨fun _ _ _ _ => inferInstance⟩
    MorphismProperty.pullbackMap (P := @Surjective) (U₁.gt e).q_surj (U₁.gt e).q_surj
      (Over.w (U₁.gt e).q).symm (Over.w (U₁.gt e).q).symm
  have qc : QuasiCompact (U₁.gt e).q.left := inferInstance
  have : QuasiCompact m.left := MorphismProperty.pullbackMap (P := @QuasiCompact) qc qc
    (Over.w (U₁.gt e).q).symm (Over.w (U₁.gt e).q).symm
  let Be := thickObj R I e D₁.toPre.P.A
  let π := lift (push (fstG I e D₁.toPre.P.A) (fst Be Be)) (push (fstG I e D₁.toPre.P.A) (snd Be Be))
  have hπ : m.left ≫ π.left = (lift (push (U₁.gt e).pG (fst _ _)) (push (U₁.gt e).pG (snd _ _))).left := by
    refine (GlobalTheory.EndRosati.lift_push (fstG I e D₁.toPre.P.A) (fst _ _ ≫ (U₁.gt e).q) (snd _ _ ≫ (U₁.gt e).q)).trans ?_
    simp only [push, Functor.map_comp, Category.assoc]
    rfl
  have hφ : ∀ k, mφ (thickObj R I e G₁) (thickObj R I e G₂) ((Over.pullback (thick R I e)).map f)
      ((Over.pullback (thick R I e)).map g) k ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left =
      m.left ≫ π.left ≫ mφ D₁.toPre.P.A D₂.toPre.P.A fB gB k := fun k => by
    rw [← Category.assoc, hπ, mφ_push (U₁.gt e).pG (U₂.gt e).pG (TorusCoord.im_mul (U₁.gt e))
      (TorusCoord.im_mul (U₂.gt e)) (pp hf) (pp hg) (fst _ _) (snd _ _) k, lift_fst_snd]
    exact (Category.id_comp _).symm
  obtain ⟨v', hv', vv⟩ := exists_gen hM (φ' := fun k => m.left ≫ π.left ≫ mφ D₁.toPre.P.A D₂.toPre.P.A fB gB k)
    (ε' := mε) (fun V _ h => Finset.prod_congr rfl fun k _ => congrArg (h · ^ mε k) (hφ k)) v hv
  obtain ⟨t, ht, -⟩ := CoordCompare.exists_gen_of_val_eq hM _ _ m.left v' hv' fun Z r r' z J hJ h => by
    have hw : r ≫ (thickObj R I e G₁ ⊗ thickObj R I e G₁).hom = r' ≫ (thickObj R I e G₁ ⊗ thickObj R I e G₁).hom := by
      rw [← Over.w m, reassoc_of% h]
    let T := Over.mk (r' ≫ (thickObj R I e G₁ ⊗ thickObj R I e G₁).hom)
    let s : T ⟶ thickObj R I e G₁ ⊗ thickObj R I e G₁ := Over.homMk r hw
    let s' : T ⟶ thickObj R I e G₁ ⊗ thickObj R I e G₁ := Over.homMk r' rfl
    have hs : s ≫ m = s' ≫ m := Over.OverMorphism.ext h
    have := hi T z J hJ (s ≫ fst _ _) (s' ≫ fst _ _) (s ≫ snd _ _) (s' ≫ snd _ _)
      (by simpa [m] using congrArg (· ≫ fst _ _) hs) (by simpa [m] using congrArg (· ≫ snd _ _) hs)
    rw [lift_comp_fst_snd, lift_comp_fst_snd] at this
    exact (vv _ r z J hJ).trans (this.trans (vv _ r' z J hJ).symm)
  have hn : (lift ((Over.pullback (thick R I e)).map (fst D₁.toPre.P.A D₁.toPre.P.A))
      ((Over.pullback (thick R I e)).map (snd D₁.toPre.P.A D₁.toPre.P.A))).left ≫ π.left =
      pullback.fst (D₁.toPre.P.A ⊗ D₁.toPre.P.A).hom (thick R I e) := by
    refine (GlobalTheory.EndRosati.lift_push (fstG I e D₁.toPre.P.A) _ _).trans ?_
    rw [GlobalTheory.EndRosati.push_fstG, GlobalTheory.EndRosati.push_fstG, lift_comp_fst_snd]
    rfl
  have := (GlobalTheory.EndRosati.gen_iff_sum hM _ _).1 ⟨_, DVR.pullGen_isGen _ _ _ _ ht (lift ((Over.pullback (thick R I e)).map
    (fst D₁.toPre.P.A D₁.toPre.P.A)) ((Over.pullback (thick R I e)).map (snd D₁.toPre.P.A D₁.toPre.P.A))).left⟩
  refine (GlobalTheory.EndRosati.gen_iff_sum hM _ _).2 (Eq.trans (Finset.sum_congr rfl fun k _ => ?_) this)
  rw [← hn, Category.assoc]

end GlobalTheory.HomMum
