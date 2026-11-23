import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AwayToAwayRightEqOfComp

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp IsTan
open TrivSqZeroExt (inl inr)

namespace GlobalTheory.LieBaseChange

open GlobalTheory.SqZero

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  (G : Over (Spec (CommRingCat.of R))) [GrpObj G]

def pushRHom (P : Type) [CommRing P] [Algebra R' P] [Algebra R P] [IsScalarTower R R' P] :
    (sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) →* (sp (R₀ := R) P ⟶ G) where
  toFun := pushR G
  map_one' := pushR_one G
  map_mul' y y' := by
    have h := map_mul (pushHom (isGrpPullback_pullback G (fB R R')) (sp (R₀ := R') P)) y y'
    exact (congrArg (iotaB ≫ ·) h).trans (MonObj.comp_mul _ _ _)

theorem isTan_iff_mem (w : sp (R₀ := R') (DualNumber R') ⟶ (Over.pullback (fB R R')).obj G) :
    IsTan w ↔ pushR G w ∈ redKer G (RingHom.ker ((fstD R').restrictScalars R)) := by
  have e : IsTan w ↔ spMap ((fstD R').restrictScalars R) ≫ pushR G w = 1 := by
    rw [← pushR_spMap, IsTan]
    exact ⟨fun h => by rw [h, pushR_one], fun h => pushR_inj G (by rw [h, pushR_one])⟩
  rw [e]
  exact ⟨mem_redKer_of_section _ ((Algebra.ofId R' (DualNumber R')).restrictScalars R)
    (fun a => rfl), fun h => comp_eq_one_of_mem_redKer h _ fun a ha => ha⟩

variable {G} {n : ℕ}

def bcVec (R' : Type) [CommRing R'] [Algebra R R'] (v : Fin n → (epsR R ⟶ G)) (i : Fin n) :
    epsR R' ⟶ (Over.pullback (fB R R')).obj G :=
  pullR (R' := R') G (spMap (dualMapA R R') ≫ v i)

theorem pushR_bcVec (v : Fin n → (epsR R ⟶ G)) (i : Fin n) :
    pushR G (bcVec R' v i) = spMap (dualMapA R R') ≫ v i := pushR_pullR G _

theorem bcVec_left_fst (v : Fin n → (epsR R ⟶ G)) (i : Fin n) :
    (bcVec R' v i).left ≫ pullback.fst G.hom (fB R R') =
      Geo.Tor.spMap (dualMapR (algebraMap R R')) ≫ (v i).left := by
  rw [← pushR_left, pushR_bcVec]
  rfl

theorem pushR_prodPts [IsCommMonObj G] (v : Fin n → (epsR R ⟶ G)) (c : Fin n → R') :
    pushR G (prodPts c (bcVec R' v)) =
      lieExp v (fun i => (inr (c i) : DualNumber R')) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) := by
  refine (map_list_prod (pushRHom G (DualNumber R')) _).trans ?_
  rw [List.map_ofFn, List.prod_ofFn, lieExp]
  refine Finset.prod_congr rfl fun i _ => ?_
  change pushR G (spMap _ ≫ _) = _
  rw [pushR_spMap, pushR_bcVec, ← Category.assoc, spMap_comp]
  congr 2
  refine DualNumber.algHom_ext ?_
  rw [epsTo_eps, AlgHom.comp_apply]
  change TrivSqZeroExt.map _ (dualMapA R R' (inr 1)) = _
  rw [dualMapA_inr, TrivSqZeroExt.map_inr]
  simp

theorem isLieBasis_bcVec_of [IsCommMonObj G] {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i))
    (inj : ∀ c c' : Fin n → R',
      lieExp v (fun i => (inr (c i) : DualNumber R')) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) =
      lieExp v (fun i => (inr (c' i) : DualNumber R')) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) →
        c = c')
    (surj : ∀ y ∈ redKer G (RingHom.ker ((fstD R').restrictScalars R)), ∃ c : Fin n → R', y =
      lieExp v (fun i => (inr (c i) : DualNumber R')) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) :
    IsLieBasis (bcVec R' v) := by
  refine ⟨fun i => (isTan_iff _).1 ((isTan_iff_mem G _).2 ?_), fun w hw => ?_⟩
  · rw [pushR_bcVec]
    refine mem_redKer_of_section ((fstD R').restrictScalars R)
      ((Algebra.ofId R' (DualNumber R')).restrictScalars R) (fun a => rfl) ?_
    have : ((fstD R').restrictScalars R).comp (dualMapA R R') = (Algebra.ofId R R').comp (fstD R) := by
      refine DualNumber.algHom_ext ?_
      change (dualMapA R R' (inr 1)).fst = algebraMap R R' 0
      rw [dualMapA_inr]; simp
    rw [← Category.assoc, spMap_comp, this, ← spMap_comp, Category.assoc, (isTan_iff _).2 (hv i),
      comp_one']
  · obtain ⟨c, hc⟩ := surj _ ((isTan_iff_mem G _).1 ((isTan_iff _).2 hw))
    refine ⟨c, (isLieComb_iff _ _ _).2 (pushR_inj G (by rw [hc, pushR_prodPts])), fun c' hc' => ?_⟩
    refine inj _ _ ?_
    rw [← hc, (isLieComb_iff _ _ _).1 hc', pushR_prodPts]

theorem isLieBasis_bcVec [IsCommMonObj G] [Smooth G.hom] {v : Fin n → (epsR R ⟶ G)}
    (hv : IsLieBasis v) : IsLieBasis (bcVec R' v) := by
  obtain ⟨h₁, h₂⟩ := expBij (DualNumber R') hv (RingHom.ker ((fstD R').restrictScalars R))
    (ker_fst_sq (R := R) (S := R') R')
  refine isLieBasis_bcVec_of hv.1 (fun c c' h => funext fun i => ?_) fun y hy => ?_
  · exact congrArg TrivSqZeroExt.snd
      (congrFun (h₁ _ _ (fun i => inr_mem_kerD (c i)) (fun i => inr_mem_kerD (c' i)) _ _ h) i)
  · obtain ⟨c, hc, hcJ, e⟩ := h₂ y hy
    have hc' : ∀ i, c i = inr (c i).snd := fun i =>
      have h0 : (c i).fst = 0 := hcJ i
      TrivSqZeroExt.ext h0 rfl
    exact ⟨fun i => (c i).snd, e.trans (lieExp_congr v hc' _ _)⟩

end GlobalTheory.LieBaseChange

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (spMap)

theorem exists_isLieBasis_baseChange (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R')
    (G : Over (Sp R)) (G' : Over (Sp R')) [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G']
    (φ : G'.left ⟶ G.left) (h : IsGrpPullback G' G (Geo.Tor.spMap f) φ) (hs : Smooth G.hom) (n : ℕ)
    (v : Fin n → (epsR R ⟶ G)) (hv : IsLieBasis v) :
    ∃ v' : Fin n → (epsR R' ⟶ G'), IsLieBasis v' ∧
      ∀ i, (v' i).left ≫ φ = Geo.Tor.spMap (Chart.dualMapR f) ≫ (v i).left := by
  let _ := f.toAlgebra
  obtain ⟨e, he, heφ⟩ := grpPullback_iso h (isGrpPullback_pullback G (fB R R'))
  refine ⟨fun i => LieBaseChange.bcVec R' v i ≫ e.inv, isLieBasis_iso e ?_, fun i => ?_⟩
  · simpa only [Category.assoc, e.inv_hom_id, Category.comp_id] using
      LieBaseChange.isLieBasis_bcVec (R' := R') hv
  · rw [← heφ, ← Category.assoc, ← Over.comp_left, Category.assoc, e.inv_hom_id, Category.comp_id]
    exact LieBaseChange.bcVec_left_fst v i

end GlobalTheory
