import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisRaynaudTangentInvariantFields
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffs
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SvalEqSumOfHasVal
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.InvComb

open TrivSqZeroExt (inl inr)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem tv_finsum {κ : Type} (s : Finset κ) (f : κ → TanM (𝟙 (Sp R)) G) :
    tv (∑ i ∈ s, f i) = ∏ i ∈ s, tv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty]; rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, PullbackSections.tv_add, ih]

theorem isField_comb (g : ℕ) (e : Fin g → Fld G.left) (he : ∀ c, IsField ⊤ (e c)) (a : Fin g → R) :
    IsField ⊤ (fun O f => ∑ c, constFn G.hom O (a c) * e c O f) := by
  refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h hW f => ?_⟩
  · have h1 := fun c => (he c).1 W hW f f'
    simp only [h1, mul_add, Finset.sum_add_distrib]
  · have h1 := fun c => (he c).2.1 W hW f f'
    simp only [h1, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun c _ => by ring
  · have h1 := fun c => (he c).2.2 W W' h hW f
    simp only [h1, map_sum, map_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← GlobalTheory.ArcPts.SecValue.res_constFn G.hom h (a c)]

theorem isInv_comb : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g : ℕ)
    (w : Fin g → TanM (𝟙 (Sp R)) G) (e : Fin g → Fld G.left), (∀ c, IsInv G (w c) (e c)) →
    ∀ a : Fin g → R, IsInv G (∑ c, a c • w c) (fun O f => ∑ c, constFn G.hom O (a c) * e c O f) := by
  intro R _ G _ _ g w e hw a
  refine ⟨isField_comb g e (fun c => (hw c).1) a, ?_⟩
  intro S _ φ x w' O f hx hO htr
  letI : Algebra R S := φ.toAlgebra
  have hG := GlobalTheory.Heat.CoeffWt.isGrpPullback_self G
  choose u hu using fun c => PullbackSections.push_surj hG (tv (w c))
  have hul : ∀ c, (u c).left = (tv (w c)).left := fun c =>
    (Category.comp_id _).symm.trans (congrArg (fun q => q.left) (hu c))
  have ht : ∀ c, IsTangent (u c) := fun c => (PullbackSections.isTangent_iff hG _).2 (by rw [hu c]; exact PullbackSections.tv_mem _)
  let z0 : Chart.sp (R₀ := R) S ⟶ G := Over.homMk x hx
  let z : Chart.sp (R₀ := R) (DualNumber S) ⟶ G := Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z0
  let ee : Fin g → DualNumber S := fun c => inr (φ (a c))
  have hee : ∀ i j, ee i * ee j = 0 := fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _
  obtain ⟨a₁, a₂⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (GlobalTheory.SqZero.inlS R S).toRingHom x O hO
  obtain ⟨b₁, b₂⟩ := GlobalTheory.Heat.CoeffWt.valR_prod hul ht hw ee hee z O a₁ Finset.univ

  choose U hU using PullbackSections.push_surj hG (tv (∑ c, a c • w c))
  have hU' : U = ∏ c, PullbackSections.scK (a c) (u c) := by
    refine PullbackSections.push_inj hG ?_
    rw [hU, map_prod, tv_finsum]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [PullbackSections.push_scK, hu c, PullbackSections.tv_smul]
  have hUl : U.left = (tv (∑ c, a c • w c)).left :=
    (Category.comp_id _).symm.trans (congrArg (fun q => q.left) hU)
  obtain ⟨g', v', hg', hv', rfl⟩ := htr
  let ρ : Chart.sp (R₀ := R) (DualNumber S) ⟶ tEpsG (x ≫ G.hom) := Over.homMk (𝟙 _) (by
    rw [hx]
    refine (Category.id_comp _).trans ?_
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom (algebraMap S (DualNumber S)))).symm)
  have k₁ : ρ ≫ g' = z := Over.OverMorphism.ext ((Category.id_comp _).trans hg')
  have k₂ : ρ ≫ v' = ∏ c, (Chart.spMap (GlobalTheory.SqZero.epsTo R (ee c) (hee c c)) ≫ u c :
      Chart.sp (R₀ := R) (DualNumber S) ⟶ G) := by
    have k₃ : ρ ≫ v' = Chart.spMap (GlobalTheory.SqZero.dualMap (Algebra.ofId R S)) ≫ U := by
      refine Over.OverMorphism.ext ((Category.id_comp _).trans (hv'.trans ?_))
      show _ = _ ≫ U.left
      rw [hUl]
      refine congrArg (fun q : DualNumber R →+* DualNumber S => spMap q ≫ _) (RingHom.ext fun r => ?_)
      ext <;> simp [dualMap, Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl] <;> rfl
    rw [k₃, hU', comp_prodT]
    refine Finset.prod_congr rfl fun c _ => Over.OverMorphism.ext ?_
    show _ ≫ spMap (epsScaleR (a c)) ≫ (u c).left = _ ≫ (u c).left
    rw [← Category.assoc]
    refine congrArg (· ≫ (u c).left) ?_
    simp only [Chart.spMap_left, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r <;> simp [epsScaleR, GlobalTheory.SqZero.epsTo, GlobalTheory.SqZero.dualTo_apply, ee, Algebra.smul_def] <;> rfl
  have key : (g' * v').left = ((∏ c, (Chart.spMap (GlobalTheory.SqZero.epsTo R (ee c) (hee c c)) ≫ u c :
      Chart.sp (R₀ := R) (DualNumber S) ⟶ G)) * z).left := by
    rw [← k₂, ← k₁, _root_.mul_comm, ← MonObj.comp_mul]
    exact (Category.id_comp _).symm
  rw [key, b₂ f]
  have a₃ : ∀ h, valR z.left O h = inl (valR x O h) := a₂
  simp only [a₃]
  show _ = valR x O (∑ c, constFn G.hom O (a c) * e c O f)
  conv_rhs => rw [GlobalTheory.ZH.CrdCalc.valR_eq x O hO, map_sum]
  simp only [map_mul, ← GlobalTheory.ZH.CrdCalc.valR_eq x O hO]
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, zero_add, TrivSqZeroExt.snd_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [GlobalTheory.ZH.CrdCalc.valR_mul x O hO, GlobalTheory.ArcPts.SecValue.valR_constFn G.hom φ x hx O hO]
  simp [ee, mul_comm]

end GlobalTheory.Heat.InvComb
