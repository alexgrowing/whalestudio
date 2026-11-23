import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsEigenvectorIffLieBasisCoordinates

noncomputable section

namespace ModelDimension.Near

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)
open scoped CategoryTheory.Obj

variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

def GT (G : Over X) [GrpObj G] (x : Sp R ⟶ X) (w : Sp (DualNumber R) ⟶ G.left) : Prop :=
  w ≫ G.hom = spMap (algebraMap R (DualNumber R)) ≫ x ∧
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ w = (1 : Over.mk x ⟶ G).left

def GC (G : Over X) [GrpObj G] (x : Sp R ⟶ X) {m : ℕ} (v : Fin m → (Sp (DualNumber R) ⟶ G.left)) (cf : Fin m → R)
    (w : Sp (DualNumber R) ⟶ G.left) : Prop :=
  ∃ u : Fin m → (Over.mk (spMap (algebraMap R (DualNumber R)) ≫ x) ⟶ G),
    (∀ i, (u i).left = spMap (epsScaleR (cf i)) ≫ v i) ∧ (List.ofFn u).prod.left = w

variable {G : Over X} [GrpObj G] {G' : Over X'} [GrpObj G'] {f : X' ⟶ X} {φ : G'.left ⟶ G.left}

theorem one_push (h : IsGrpPullback G' G f φ) {S : Scheme.{0}} (x : S ⟶ X') :
    (1 : Over.mk x ⟶ G').left ≫ φ = (1 : Over.mk (x ≫ f) ⟶ G).left := by
  have e := GlobalTheory.LieCombBaseChange.prod_left_comp h (T := Over.mk (x ≫ f)) (T' := Over.mk x) (𝟙 S)
    (Category.id_comp _) (n := 0) (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
  simp only [List.ofFn_zero, List.prod_nil] at e
  exact e.trans (Category.id_comp _)

theorem gt_push (h : IsGrpPullback G' G f φ) {x : Sp R ⟶ X'} {w : Sp (DualNumber R) ⟶ G'.left} (hw : GT G' x w) :
    GT G (x ≫ f) (w ≫ φ) :=
  ⟨by rw [Category.assoc, h.1.w, ← Category.assoc, hw.1, Category.assoc],
    by rw [← Category.assoc, hw.2, one_push h]⟩

theorem alg_fst : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
  rw [← spMap_comp]
  have : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
    ext r
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [this]
  exact Spec.map_id _

theorem gt_pull (h : IsGrpPullback G' G f φ) {x : Sp R ⟶ X'} {w : Sp (DualNumber R) ⟶ G'.left}
    (h1 : w ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ x) (hw : GT G (x ≫ f) (w ≫ φ)) : GT G' x w := by
  refine ⟨h1, h.1.hom_ext ?_ ?_⟩
  · rw [Category.assoc, hw.2, one_push h]
  · rw [Category.assoc, h1, ← Category.assoc, alg_fst, Category.id_comp]
    exact (Over.w (1 : Over.mk x ⟶ G')).symm

theorem gt_bc (ψ : R →+* R') {x : Sp R ⟶ X} {w : Sp (DualNumber R) ⟶ G.left} (hw : GT G x w) :
    GT G (spMap ψ ≫ x) (spMap (dualMapR ψ) ≫ w) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, hw.1, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ x) (GlobalTheory.LieCombBaseChange.dualMap_over ψ)
  · have e : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (dualMapR ψ) =
        spMap ψ ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
      rw [← spMap_comp, ← spMap_comp]
      congr 1
      refine RingHom.ext fun r => ?_
      simp [dualMapR]
    rw [← Category.assoc, e, Category.assoc, hw.2]
    let D : Over.mk (spMap ψ ≫ x) ⟶ Over.mk x := Over.homMk (spMap ψ) rfl
    exact congrArg CommaMorphism.left (MonObj.comp_one (M := G) D)

theorem gc_push (h : IsGrpPullback G' G f φ) {x : Sp R ⟶ X'} {m : ℕ} {v : Fin m → (Sp (DualNumber R) ⟶ G'.left)}
    {cf : Fin m → R} {w : Sp (DualNumber R) ⟶ G'.left} (hw : GC G' x v cf w) :
    GC G (x ≫ f) (fun i => v i ≫ φ) cf (w ≫ φ) := by
  obtain ⟨u, hu, rfl⟩ := hw
  let u' : Fin m → (Over.mk (spMap (algebraMap R (DualNumber R)) ≫ x ≫ f) ⟶ G) := fun i =>
    Over.homMk ((u i).left ≫ φ) (by
      have e : (u i).left ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ x := Over.w (u i)
      show ((u i).left ≫ φ) ≫ G.hom = spMap (algebraMap R (DualNumber R)) ≫ x ≫ f
      rw [Category.assoc, h.1.w, ← Category.assoc, e, Category.assoc])
  refine ⟨u', fun i => ?_, ?_⟩
  · show (u i).left ≫ φ = _
    rw [hu, Category.assoc]
  · have e := GlobalTheory.LieCombBaseChange.prod_left_comp h (𝟙 (Sp (DualNumber R)))
      ((Category.id_comp _).trans (Category.assoc _ _ _).symm) u' u (fun i => (Category.id_comp _).symm)
    exact (e.trans (Category.id_comp _)).symm

theorem gc_pull (h : IsGrpPullback G' G f φ) {x : Sp R ⟶ X'} {m : ℕ} {v : Fin m → (Sp (DualNumber R) ⟶ G'.left)}
    {cf : Fin m → R} {w : Sp (DualNumber R) ⟶ G'.left}
    (hv : ∀ i, v i ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ x)
    (h1 : w ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ x)
    (hw : GC G (x ≫ f) (fun i => v i ≫ φ) cf (w ≫ φ)) : GC G' x v cf w := by
  obtain ⟨u, hu, hw⟩ := hw
  let u' : Fin m → (Over.mk (spMap (algebraMap R (DualNumber R)) ≫ x) ⟶ G') := fun i =>
    Over.homMk (spMap (epsScaleR (cf i)) ≫ v i) (by
      show (spMap (epsScaleR (cf i)) ≫ v i) ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ x
      rw [Category.assoc, hv, ← Category.assoc]
      exact congrArg (· ≫ x) (GlobalTheory.LieCombBaseChange.epsScale_over (cf i)))
  refine ⟨u', fun i => rfl, h.1.hom_ext ?_ ?_⟩
  · have e := GlobalTheory.LieCombBaseChange.prod_left_comp h (𝟙 (Sp (DualNumber R)))
      ((Category.id_comp _).trans (Category.assoc _ _ _).symm) u u' (fun i =>
        (Category.assoc _ _ _).trans ((hu i).symm.trans (Category.id_comp _).symm))
    exact e.trans ((Category.id_comp _).trans hw)
  · rw [h1]
    exact Over.w _

theorem gc_bc (ψ : R →+* R') {x : Sp R ⟶ X} {m : ℕ} {v : Fin m → (Sp (DualNumber R) ⟶ G.left)}
    {cf : Fin m → R} {w : Sp (DualNumber R) ⟶ G.left} (hw : GC G x v cf w) :
    GC G (spMap ψ ≫ x) (fun i => spMap (dualMapR ψ) ≫ v i) (fun i => ψ (cf i)) (spMap (dualMapR ψ) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := hw
  let D : Over.mk (spMap (algebraMap R' (DualNumber R')) ≫ spMap ψ ≫ x) ⟶
      Over.mk (spMap (algebraMap R (DualNumber R)) ≫ x) := Over.homMk (spMap (dualMapR ψ)) (by
    show spMap (dualMapR ψ) ≫ spMap (algebraMap R (DualNumber R)) ≫ x = _ ≫ spMap ψ ≫ x
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ x) (GlobalTheory.LieCombBaseChange.dualMap_over ψ))
  refine ⟨fun i => D ≫ u i, fun i => ?_, ?_⟩
  · show spMap (dualMapR ψ) ≫ (u i).left = _
    rw [hu, ← Category.assoc, GlobalTheory.LieCombBaseChange.dualMap_epsScale, Category.assoc]
  · exact (congrArg (fun q => q.left) ((map_list_prod (preHom D) (List.ofFn u)).trans
      (by rw [List.map_ofFn]))).symm

section Ring

open GlobalTheory.Reg.VecEig GlobalTheory.GrpTangent

variable {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A]

theorem comb_comb {n r : ℕ} {v : Fin n → (epsR R ⟶ A)} (hv : ∀ i, IsTangent (v i)) (u : Matrix (Fin n) (Fin r) R)
    (a : Fin r → R) : comb (fun i => comb v fun j => u j i) a = comb v (u.mulVec a) := by
  rw [comb]
  simp only [epsScale_comb]
  simp only [comb, Matrix.mulVec, dotProduct, epsScale_sum_comp (hv _)]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, mul_comm]

theorem exists_prim [IsDomain R] {n r : ℕ} {v : Fin n → (epsR R ⟶ A)} (hv : IsLieBasis v) {I : Type}
    (g : I → (A ⟶ A)) (hg : ∀ i, IsMonHom (g i)) (z : I → R) (ub : Fin r → (epsR R ⟶ A)) (ht : ∀ i, IsTangent (ub i))
    (he : ∀ i k, (ub i ≫ g k).left = spMap (epsScaleR (z k)) ≫ (ub i).left)
    (hb : ∀ w : epsR R ⟶ A, IsTangent w → (∀ k, (w ≫ g k).left = spMap (epsScaleR (z k)) ≫ w.left) →
      ∃! a : Fin r → R, IsLieComb a ub w) :
    ∃ u : Matrix (Fin n) (Fin r) R, (∀ i, IsLieComb (fun j => u j i) v (ub i)) ∧
      ∀ (p : R) (a : Fin r → R) (cv : Fin n → R), p ≠ 0 → u.mulVec a = p • cv → ∃ a', a = p • a' := by
  choose cu hcu using fun i => (hv.2 _ (ht i)).exists
  let u : Matrix (Fin n) (Fin r) R := Matrix.of fun j i => cu i j
  have hub : ub = fun i => comb v fun j => u j i := funext fun i => (isLieComb_iff_comb _ _ _).1 (hcu i)
  refine ⟨u, hcu, fun p a cv hp hcv => ?_⟩
  choose ρ hρ using fun k j => (hv.2 _ (haveI := hg k; isTangent_comp (hv.1 j) (g k))).exists
  have eig : ∀ k (x : Fin n → R), ((comb v x ≫ g k).left = spMap (epsScaleR (z k)) ≫ (comb v x).left) ↔
      (Matrix.of fun i j => ρ k j i).mulVec x = z k • x := by
    intro k x
    haveI := hg k
    rw [← (comb_injective hv).eq_iff, ← epsScale_comb,
      ← comb_comp hv.1 (g k) (Matrix.of fun i j => ρ k j i) (fun j => (isLieComb_iff_comb _ _ _).1 (hρ k j)) x]
    exact ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg CommaMorphism.left h⟩
  have eigu : ∀ k (b : Fin r → R), (Matrix.of fun i j => ρ k j i).mulVec (u.mulVec b) = z k • u.mulVec b := by
    intro k b
    have e : u.mulVec b = ∑ i, b i • fun j => u j i := by
      funext j
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, _root_.mul_comm]
    rw [e, Matrix.mulVec_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := he i k
    rw [congrFun hub i] at h1
    rw [Matrix.mulVec_smul, (eig k _).1 h1, smul_comm]
  have key : ∀ x : Fin n → R, (∀ k, (Matrix.of fun i j => ρ k j i).mulVec x = z k • x) →
      ∃! b : Fin r → R, u.mulVec b = x := by
    intro x hx
    have h1 := hb (comb v x) (isTangent_comb hv.1 x) fun k => (eig k x).2 (hx k)
    refine (existsUnique_congr fun b => ?_).1 h1
    rw [isLieComb_iff_comb, hub, comb_comb hv.1, (comb_injective hv).eq_iff, eq_comm]
  obtain ⟨a', ha', -⟩ := key cv fun k => by
    have h1 := eigu k a
    rw [hcv, Matrix.mulVec_smul, smul_comm] at h1
    exact smul_right_injective _ hp h1
  refine ⟨a', (key _ fun k => eigu k a).unique rfl ?_⟩
  rw [Matrix.mulVec_smul, ha', hcv]

end Ring

section Coord

variable [IsCommMonObj G] {x : Sp R ⟶ X} {n : ℕ} {V : Fin n → (Sp (DualNumber R) ⟶ G.left)}

def IsBas (G : Over X) [GrpObj G] (x : Sp R ⟶ X) {n : ℕ} (V : Fin n → (Sp (DualNumber R) ⟶ G.left)) : Prop :=
  ∃ (A : Over (Sp R)) (_ : GrpObj A) (_ : IsCommMonObj A) (φ : A.left ⟶ G.left) (_ : IsGrpPullback A G x φ)
    (v : Fin n → (epsR R ⟶ A)), (∀ j, (v j).left ≫ φ = V j) ∧ IsLieBasis v

omit [IsCommMonObj G]

theorem gc_iff {A : Over (Sp R)} [GrpObj A] {φ : A.left ⟶ G.left} (h : IsGrpPullback A G x φ) {m : ℕ} (c : Fin m → R)
    (v : Fin m → (epsR R ⟶ A)) (w : epsR R ⟶ A) :
    IsLieComb c v w ↔ GC G x (fun i => (v i).left ≫ φ) c (w.left ≫ φ) :=
  ReciprocityTheory.ChartRestriction.G.Chart.comb_push h c v w

theorem exists_lift {A : Over (Sp R)} [GrpObj A] {φ : A.left ⟶ G.left} (h : IsGrpPullback A G x φ)
    {w : Sp (DualNumber R) ⟶ G.left} (hw : w ≫ G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) :
    ∃ w' : epsR R ⟶ A, w'.left ≫ φ = w :=
  ⟨Over.homMk (h.1.lift w (spMap (algebraMap R (DualNumber R))) hw) (h.1.lift_snd _ _ _), h.1.lift_fst _ _ _⟩

theorem GC.over {m : ℕ} {v : Fin m → (Sp (DualNumber R) ⟶ G.left)} {cf : Fin m → R}
    {w : Sp (DualNumber R) ⟶ G.left} (h : GC G x v cf w) :
    w ≫ G.hom = spMap (algebraMap R (DualNumber R)) ≫ x := by
  obtain ⟨u, -, rfl⟩ := h
  exact Over.w _

theorem IsBas.exists (hV : IsBas G x V) {w : Sp (DualNumber R) ⟶ G.left} (hw : GT G x w) : ∃ cv, GC G x V cv w := by
  obtain ⟨A, _, _, φ, h, v, hv, hb⟩ := hV
  obtain rfl : (fun j => (v j).left ≫ φ) = V := funext hv
  obtain ⟨w', rfl⟩ := exists_lift h hw.1
  obtain ⟨cv, hcv⟩ := (hb.2 w' ((ReciprocityTheory.ChartRestriction.G.Chart.tan_push h w').2 hw.2)).exists
  exact ⟨cv, (gc_iff h _ _ _).1 hcv⟩

theorem IsBas.unique (hV : IsBas G x V) {w : Sp (DualNumber R) ⟶ G.left} {a b : Fin n → R} (ha : GC G x V a w)
    (hb : GC G x V b w) : a = b := by
  obtain ⟨A, _, _, φ, h, v, hv, hB⟩ := hV
  obtain rfl : (fun j => (v j).left ≫ φ) = V := funext hv
  obtain ⟨w', rfl⟩ := exists_lift h ha.over
  exact GlobalTheory.Reg.VecEig.comb_injective hB
    (((GlobalTheory.Reg.VecEig.isLieComb_iff_comb _ _ _).1 ((gc_iff h _ _ _).2 ha)).symm.trans
      ((GlobalTheory.Reg.VecEig.isLieComb_iff_comb _ _ _).1 ((gc_iff h _ _ _).2 hb)))

theorem IsBas.comb (hV : IsBas G x V) {r : ℕ} {w : Fin r → (Sp (DualNumber R) ⟶ G.left)}
    {u : Matrix (Fin n) (Fin r) R} (hu : ∀ i, GC G x V (fun j => u j i) (w i)) {a : Fin r → R}
    {w' : Sp (DualNumber R) ⟶ G.left} (ha : GC G x w a w') : GC G x V (u.mulVec a) w' := by
  obtain ⟨A, _, _, φ, h, v, hv, hB⟩ := hV
  obtain rfl : (fun j => (v j).left ≫ φ) = V := funext hv
  choose w₁ hw₁ using fun i => exists_lift h (hu i).over
  obtain rfl : (fun j => (w₁ j).left ≫ φ) = w := funext hw₁
  obtain ⟨w₂, rfl⟩ := exists_lift h ha.over
  have e1 : w₁ = fun i => GlobalTheory.Reg.VecEig.comb v fun j => u j i :=
    funext fun i => (GlobalTheory.Reg.VecEig.isLieComb_iff_comb _ _ _).1 ((gc_iff h _ _ _).2 (hu i))
  have e2 := (GlobalTheory.Reg.VecEig.isLieComb_iff_comb _ _ _).1 ((gc_iff h _ _ _).2 ha)
  rw [e1, comb_comb hB.1] at e2
  exact (gc_iff h _ _ _).1 ((GlobalTheory.Reg.VecEig.isLieComb_iff_comb _ _ _).2 e2)

end Coord

end ModelDimension.Near
