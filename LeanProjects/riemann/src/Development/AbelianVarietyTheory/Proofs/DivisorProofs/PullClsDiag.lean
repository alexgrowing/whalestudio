import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectOddLevelRigid

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped CategoryTheory.Obj

namespace GlobalTheory.UPel.HT.Rigid

open GlobalTheory.CechPic GlobalTheory.AmpleRigid GlobalTheory.SiegRigid

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

theorem pull_cls_diag {b : Base D R} {N : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R}
    {o' : Obj b N s'} {o : Obj b N s} {f : S' ⟶ S} (m : ObjMap o' o f) :
    pull m.φ (cls _ (pull_isLB o.isLB (lift (𝟙 o.A) (𝟙 o.A)).left)) =
      cls _ (pull_isLB o'.isLB (lift (𝟙 o'.A) (𝟙 o'.A)).left) := by
  have hs := m.sq
  have e : (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ m.φ₂ = m.φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left := by
    have a₁ := congrArg (fun q => q.left) (lift_fst (𝟙 o.A) (𝟙 o.A))
    have a₂ := congrArg (fun q => q.left) (lift_snd (𝟙 o.A) (𝟙 o.A))
    have b₁ := congrArg (fun q => q.left) (lift_fst (𝟙 o'.A) (𝟙 o'.A))
    have b₂ := congrArg (fun q => q.left) (lift_snd (𝟙 o'.A) (𝟙 o'.A))
    simp only [Over.comp_left, Over.id_left] at a₁ a₂ b₁ b₂
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst o.A o.A).left = (_ ≫ _) ≫ (fst o.A o.A).left
      rw [Category.assoc, hs.1, ← Category.assoc, b₁, Category.assoc, a₁]; simp
    · show (_ ≫ _) ≫ (snd o.A o.A).left = (_ ≫ _) ≫ (snd o.A o.A).left
      rw [Category.assoc, hs.2, ← Category.assoc, b₂, Category.assoc, a₂]; simp
  have h1 : pull m.φ₂ (cls o.P o.isLB) = cls o'.P o'.isLB :=
    ((cls_eq_iff o'.isLB (pull_isLB o.isLB m.φ₂)).2 m.pol).symm
  rw [cls_pull o.isLB, cls_pull o'.isLB, ← pull_comp, ← e, pull_comp, h1]

theorem eq_on_torsion {b : Base D R} {N : ℕ} (hN : 0 < N) (hNp : N.Coprime p) {S S' : Scheme.{0}}
    {s : S ⟶ Sp R} (o : Obj b N s) {A' : Over S'} [GrpObj A'] {f : S' ⟶ S}
    {φ φ' : A'.left ⟶ o.A.left} (hφ : IsGrpPullback A' o.A f φ)
    (lv : D.La → (𝟙_ (Over S') ⟶ A'))
    (h₁ : ∀ a, (lv a).left ≫ φ = f ≫ (o.eta a).left) (h₂ : ∀ a, (lv a).left ≫ φ' = f ≫ (o.eta a).left)
    (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S') (y : Over.mk x ⟶ A') (hy : y ^ N = 1) :
    y.left ≫ φ = y.left ≫ φ' := by
  let β : R →+* k := (Spec.preimage ((x ≫ f) ≫ s)).hom
  obtain ⟨I, hI⟩ := o.geom k (x ≫ f) β (Spec.map_preimage _).symm
  have hy₁ : pushHom hφ (Over.mk x) y ^ N = 1 := by rw [← map_pow, hy, map_one]
  obtain ⟨a, ha⟩ := (I.onto N hN hNp _).1 hy₁
  have hu : (toUnit (Over.mk (x ≫ f))).left = x ≫ f := (Category.comp_id _).symm.trans (Over.w (toUnit _))
  have e : (x ≫ f) ≫ (o.eta a).left = y.left ≫ φ := by
    rw [← hu]
    exact congrArg (fun q => q.left) ((hI a).trans ha)
  have e₁ : y.left = x ≫ (lv a).left := by
    apply hφ.1.hom_ext
    · rw [Category.assoc]
      exact e.symm.trans ((Category.assoc _ _ _).trans (congrArg (x ≫ ·) (h₁ a).symm))
    · rw [Over.w, Category.assoc, Over.w]
      exact (Category.comp_id _).symm
  rw [e₁, Category.assoc, Category.assoc]
  exact congrArg (x ≫ ·) ((h₁ a).trans (h₂ a).symm)

theorem eq_id : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (m : ObjMap o o (𝟙 S)), m.φ = 𝟙 _ := by
  intro p _ D R _ b N hN hNp S s o m
  have hψ := m.cart
  have e₂ : m.φ ≫ o.A.hom = o.A.hom := hψ.1.w.trans (Category.comp_id _)
  haveI : IsIso m.φ := hψ.1.isIso_fst_of_isIso
  let σ : o.A ≅ o.A := Over.isoMk (asIso m.φ) e₂
  have hσ : IsMonHom σ.hom := isMonHom_of_mul_comp σ.hom fun T x y => mul_comp_of_grpPullback_id σ.hom hψ x y
  have key : σ.hom = 𝟙 _ := by
    refine eq_id_of_forall_geometric_fibre laws_without_cohomology.1 o.A o.ab σ.hom (IsMonHom.one_hom σ.hom)
      fun t => ?_
    let K : Type := AlgebraicClosure (S.residueField t)
    let j : Sp K ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField t) K)) ≫ S.fromSpecResidueField t
    have hp := isGrpPullback_pullback o.A j
    have := o.ab.smooth
    have := o.ab.proper
    have := o.ab.geomConnected
    have hab : IsAbelianScheme ((Over.pullback j).obj o.A) :=
      { comm := Functor.isCommMonObj_obj
        smooth := by change Smooth (pullback.snd o.A.hom j); infer_instance
        proper := by change IsProper (pullback.snd o.A.hom j); infer_instance
        geomConnected := by change GeometricallyConnected (pullback.snd o.A.hom j); infer_instance }
    have hNK : (N : K) ≠ 0 := by
      have hu := (b.unit N hNp).map (Spec.preimage (j ≫ s)).hom
      rw [map_natCast] at hu
      exact hu.ne_zero
    have g := hp.comp m.cart
    rw [Category.comp_id] at g
    have e' := eq_of_field (pull_isLB o.isLB _) o.ample hab g hp
      (by rw [pull_comp, pull_cls_diag m]) hN hNK
      fun Ω _ _ x y hy => by
        have hy₁ : pushHom hp (Over.mk x) y ^ N = 1 := by rw [← map_pow, hy, map_one]
        have e₁ := eq_on_torsion (φ' := 𝟙 _) (by omega) hNp o m.cart o.eta m.eta (fun a => by simp) Ω (x ≫ j) _ hy₁
        rw [← Category.assoc]
        exact e₁.trans (Category.comp_id _)
    refine ⟨_, _, j, _, _, (default : PrimeSpectrum K), ?_, hp.1, ?_⟩
    · exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply t _)
    · exact e'
  have := congrArg (fun q => q.left) key
  exact this

end GlobalTheory.UPel.HT.Rigid
