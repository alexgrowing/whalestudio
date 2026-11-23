import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

noncomputable section

namespace GlobalTheory.Reg.VecEig

open GlobalTheory.GrpTangent

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def comb {n : ℕ} (v : Fin n → (epsR R ⟶ G)) (c : Fin n → R) : epsR R ⟶ G :=
  ∏ i, epsScale (c i) ≫ v i

theorem isLieComb_iff_comb {n : ℕ} (c : Fin n → R) (v : Fin n → (epsR R ⟶ G)) (w : epsR R ⟶ G) :
    IsLieComb c v w ↔ w = comb v c := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [List.prod_ofFn]
    refine Finset.prod_congr rfl fun i _ => ?_
    apply Over.OverMorphism.ext
    rw [hu i, Over.comp_left]
    rfl
  · rintro rfl
    refine ⟨fun i => epsScale (c i) ≫ v i, fun i => ?_, ?_⟩
    · rw [Over.comp_left]
      rfl
    · rw [List.prod_ofFn]
      rfl

theorem comp_finProd {X Y : Over (Sp R)} (g : X ⟶ Y) {κ : Type} (s : Finset κ) (u : κ → (Y ⟶ G)) :
    g ≫ ∏ i ∈ s, u i = ∏ i ∈ s, g ≫ u i := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.prod_empty]
    exact Chart.comp_one' g
  · intro a t ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, comp_mul, ih]

theorem finProd_comp {X : Over (Sp R)} (g : G ⟶ G) [IsMonHom g] {κ : Type} (s : Finset κ) (u : κ → (X ⟶ G)) :
    (∏ i ∈ s, u i) ≫ g = ∏ i ∈ s, u i ≫ g := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.prod_empty]
    exact one_comp g
  · intro a t ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, mul_comp, ih]

theorem epsScale_sum_comp {w : epsR R ⟶ G} (hw : IsTangent w) {κ : Type} (s : Finset κ) (a : κ → R) :
    epsScale (∑ i ∈ s, a i) ≫ w = ∏ i ∈ s, epsScale (a i) ≫ w := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.prod_empty]
    exact epsScale_zero_comp hw
  · intro b t hb ih
    rw [Finset.sum_insert hb, Finset.prod_insert hb, epsScale_add_comp _ _ hw, ih]

theorem epsScale_comb {n : ℕ} (v : Fin n → (epsR R ⟶ G)) (c : Fin n → R) (z : R) :
    epsScale z ≫ comb v c = comb v (z • c) := by
  unfold comb
  rw [comp_finProd]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Category.assoc, epsScale_mul, Pi.smul_apply, smul_eq_mul]

theorem comb_comp {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) (g : G ⟶ G) [IsMonHom g]
    (A : Matrix (Fin n) (Fin n) R) (hA : ∀ j, v j ≫ g = comb v fun i => A i j) (c : Fin n → R) :
    comb v c ≫ g = comb v (A.mulVec c) := by
  calc comb v c ≫ g = ∏ j, (epsScale (c j) ≫ v j) ≫ g := finProd_comp g _ _
    _ = ∏ j, comb v (c j • fun i => A i j) :=
        Finset.prod_congr rfl fun j _ => by rw [Category.assoc, hA j, epsScale_comb]
    _ = ∏ j, ∏ i, epsScale (A i j * c j) ≫ v i := Finset.prod_congr rfl fun j _ => by
        unfold comb
        exact Finset.prod_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul, mul_comm (c j)]
    _ = ∏ i, ∏ j, epsScale (A i j * c j) ≫ v i := Finset.prod_comm
    _ = comb v (A.mulVec c) := by
        unfold comb
        exact Finset.prod_congr rfl fun i _ => (epsScale_sum_comp (hv i) Finset.univ fun j => A i j * c j).symm

theorem isTangent_comb {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) (c : Fin n → R) :
    IsTangent (comb v c) := by
  rw [isTangent_iff]
  unfold comb
  rw [comp_finProd]
  exact Finset.prod_eq_one fun i _ => (isTangent_iff _).1 (isTangent_epsScale (c i) (hv i))

theorem comb_injective {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v) : Function.Injective (comb v) := by
  intro c d h
  have hc : IsLieComb c v (comb v c) := (isLieComb_iff_comb c v (comb v c)).2 rfl
  have hd : IsLieComb d v (comb v c) := (isLieComb_iff_comb d v (comb v c)).2 h
  exact (hv.2 _ (isTangent_comb hv.1 c)).unique hc hd

theorem pt_ext {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) {X : Over S'} {u u' : X ⟶ t'.G}
    (h : u.left ≫ m.φ = u'.left ≫ m.φ) : u = u' := by
  cases m with
  | mk cm cart base act lin =>
    apply Over.OverMorphism.ext
    refine cart.1.hom_ext h ?_
    rw [Over.w u, Over.w u']

end GlobalTheory.Reg.VecEig

open GlobalTheory.Reg.VecEig GlobalTheory.GrpTangent in

theorem GlobalTheory.Reg.isEigAt_iff_eig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ (τ : E →+* ℂ) (cv : Fin M.n → R) (w : Sp (DualNumber R) ⟶ Xo.univ.t.G.left), Λ.Vec cv w → (IsEigAt c τ w ↔ M.Eig f τ cv) := by
  intro E _ _ _ H Dw l Xo c O _ β Y M R _ _ f x Λ τ cv w hw
  obtain ⟨v', u', hv', hu', rfl⟩ := hw
  obtain ⟨v, hv0, hvb, hρ⟩ := M.lie R f Λ.t' Λ.m2
  obtain rfl : v' = v := funext fun j => pt_ext Λ.m2 ((hv' j).trans (hv0 j).symm)
  have hu := (isLieComb_iff_comb _ _ _).1 hu'
  have hA := fun a j => (isLieComb_iff_comb _ _ _).1 (hρ a j)
  unfold IsEigAt MChart.Eig
  refine forall_congr' fun a => ?_
  have : IsMonHom (Λ.t'.act.act a) := Λ.t'.act.hom a
  have e1 : (u'.left ≫ Λ.m1.φ) ≫ (Xo.univ.t.act.act a).left = (u' ≫ Λ.t'.act.act a).left ≫ Λ.m1.φ := by
    rw [Over.comp_left, Category.assoc, Category.assoc]
    exact congrArg (u'.left ≫ ·) (Λ.m1.act a).symm
  have e2 : spMap (epsMul (algebraMap c.F R (embK c τ a))) ≫ u'.left ≫ Λ.m1.φ =
      (epsScale (algebraMap c.F R (embK c τ a)) ≫ u').left ≫ Λ.m1.φ := by
    rw [Over.comp_left, Category.assoc]
    rfl
  rw [e1, e2, hu, comb_comp hvb.1 _ ((M.ρ a).map f) (hA a), epsScale_comb]
  constructor
  · intro h
    exact comb_injective hvb (pt_ext Λ.m1 h)
  · intro h
    rw [h]
