import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilAdjoint

theorem weilIs_adjoint {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) {P : LB (A ⊗ A).left}
    (hP : P.IsLB) (f f' : A ⟶ A) [IsMonHom f] [IsMonHom f']
    (h : LBIso (ev P (fst A A ≫ f) (snd A A)) (ev P (fst A A) (snd A A ≫ f'))) {k : ℤ} {T : Over S} (x y : T ⟶ A)
    {c c' : Γ(T.left, ⊤)ˣ}
    (H : Out.WeilIs (A ⊗ A) P k (CartesianMonoidalCategory.lift (x ≫ f) 1) (CartesianMonoidalCategory.lift 1 y) c)
    (H' : Out.WeilIs (A ⊗ A) P k (CartesianMonoidalCategory.lift x 1) (CartesianMonoidalCategory.lift 1 (y ≫ f')) c') :
    c = c' := by
  have hG := GlobalTheory.globalFns_holds
  have hB := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have e₁ : CartesianMonoidalCategory.lift (fst A A ≫ f) (snd A A) = f ⊗ₘ 𝟙 A := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have e₂ : CartesianMonoidalCategory.lift (fst A A) (snd A A ≫ f') = 𝟙 A ⊗ₘ f' := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have h' : LBIso (P.pull (f ⊗ₘ 𝟙 A).left) (P.pull (𝟙 A ⊗ₘ f').left) := by
    rw [← e₁, ← e₂]; exact h
  have hL := pull_isLB hP (f ⊗ₘ 𝟙 A).left
  have i₁ := GlobalTheory.lbIso_lbPow_one hL
  have i₂ := LBIso.trans (GlobalTheory.isLB_lbPow hL 1) hL (pull_isLB hP _) i₁ h'
  refine CommutatorPairing.weilIs_unique hG hB hL
    (WeilIsogeny.weilIs_pull_hom hG hB hL hP (f ⊗ₘ 𝟙 A) i₁ (n := k) (x := CartesianMonoidalCategory.lift x 1)
      (y := CartesianMonoidalCategory.lift 1 y) ?_)
    (WeilIsogeny.weilIs_pull_hom hG hB hL hP (𝟙 A ⊗ₘ f') i₂ ?_)
  · rwa [lift_map, lift_map, Category.comp_id, Category.comp_id, MonObj.one_comp]
  · rwa [lift_map, lift_map, Category.comp_id, Category.comp_id, MonObj.one_comp]

theorem map_unitOn {A B : Type} [CommRing A] [CommRing B] (β : A →+* B) (c : Aˣ) :
    Units.map (spMap β).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map β.toMonoidHom c) :=
  Units.ext (congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm

theorem unitOn_injective {K : Type} [CommRing K] : Function.Injective (unitOn (R := K)) := fun _ _ h =>
  Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1 (congrArg Units.val h))

theorem weilIs_algHom {K : Type} [CommRing K] {B : Over (Sp K)} [GrpObj B] (hB : IsAbelianScheme B) {P : LB B.left}
    (hP : P.IsLB) {k : ℤ} {D E : Type} [CommRing D] [Algebra K D] [CommRing E] [Algebra K E] (α : D →ₐ[K] E)
    {x y : SpAlg K D ⟶ B} {x' y' : SpAlg K E ⟶ B} (hx : spOver α ≫ x = x') (hy : spOver α ≫ y = y') {U : Dˣ}
    (hU : Out.WeilIs B P k (T := SpAlg K D) x y (unitOn U)) :
    Out.WeilIs B P k (T := SpAlg K E) x' y' (unitOn (Units.map (α : D →+* E).toMonoidHom U)) := by
  rw [← map_unitOn, ← hx, ← hy]
  exact CommPairing.weilIs_pull GlobalTheory.globalFns_holds hB hP (T := SpAlg K D) (T' := SpAlg K E) (spOver α) hU

theorem map_unit_eq {K : Type} [CommRing K] {A : Over (Sp K)} [GrpObj A] (hA : IsAbelianScheme A)
    {P : LB (A ⊗ A).left} (hP : P.IsLB) (f f' : A ⟶ A) [IsMonHom f] [IsMonHom f']
    (h : LBIso (ev P (fst A A ≫ f) (snd A A)) (ev P (fst A A) (snd A A ≫ f'))) {k : ℤ}
    {D : Type} [CommRing D] [Algebra K D] (y : SpAlg K D ⟶ A) (φ φ' : D →ₐ[K] D)
    (hφ : spOver φ ≫ y = y ≫ f) (hφ' : spOver φ' ≫ y = y ≫ f') (U : (D ⊗[K] D)ˣ)
    (hU : Out.WeilIs (A ⊗ A) P k (T := SpAlg K (D ⊗[K] D))
      (CartesianMonoidalCategory.lift (spOver Algebra.TensorProduct.includeLeft ≫ y) 1)
      (CartesianMonoidalCategory.lift 1 (spOver Algebra.TensorProduct.includeRight ≫ y)) (unitOn U)) :
    Algebra.TensorProduct.map φ (AlgHom.id K D) U.val = Algebra.TensorProduct.map (AlgHom.id K D) φ' U.val := by
  have hB := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have l : ∀ a b : D →ₐ[K] D, spOver (Algebra.TensorProduct.map a b) ≫
      spOver (Algebra.TensorProduct.includeLeft : D →ₐ[K] D ⊗[K] D) ≫ y =
      spOver (Algebra.TensorProduct.includeLeft : D →ₐ[K] D ⊗[K] D) ≫ spOver a ≫ y := fun a b => by
    rw [← Category.assoc, ← Category.assoc, spOver_comp, spOver_comp, Algebra.TensorProduct.map_comp_includeLeft]
  have r : ∀ a b : D →ₐ[K] D, spOver (Algebra.TensorProduct.map a b) ≫
      spOver (Algebra.TensorProduct.includeRight : D →ₐ[K] D ⊗[K] D) ≫ y =
      spOver (Algebra.TensorProduct.includeRight : D →ₐ[K] D ⊗[K] D) ≫ spOver b ≫ y := fun a b => by
    rw [← Category.assoc, ← Category.assoc, spOver_comp, spOver_comp, Algebra.TensorProduct.map_comp_includeRight]
  have e := weilIs_adjoint hA hP f f' h (spOver Algebra.TensorProduct.includeLeft ≫ y)
    (spOver Algebra.TensorProduct.includeRight ≫ y)
    (weilIs_algHom hB hP (Algebra.TensorProduct.map φ (AlgHom.id K D))
      (by rw [comp_lift, MonObj.comp_one, l, hφ, Category.assoc])
      (by rw [comp_lift, MonObj.comp_one, r, spOver_id, Category.id_comp]) hU)
    (weilIs_algHom hB hP (Algebra.TensorProduct.map (AlgHom.id K D) φ')
      (by rw [comp_lift, MonObj.comp_one, l, spOver_id, Category.id_comp])
      (by rw [comp_lift, MonObj.comp_one, r, hφ', Category.assoc]) hU)
  exact congrArg Units.val (unitOn_injective e)

theorem rid_lTensor_map {K D : Type} [CommRing K] [CommRing D] [Algebra K D] (a b : D →ₐ[K] D) (χ : D →ₗ[K] K)
    (u : D ⊗[K] D) : TensorProduct.rid K D (χ.lTensor D (Algebra.TensorProduct.map a b u)) =
      a (TensorProduct.rid K D ((χ ∘ₗ b.toLinearMap).lTensor D u)) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul s t => simp
  | add s t hs ht => simp only [map_add, hs, ht]

theorem map_comp_weilHom : GlobalTheory.Published.CubeTheorem → ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (P : LB (A ⊗ A).left), IsDual A A P → ∀ (𝒜 : PDivGroup p K) (t : 𝒜.TorsionTower A) (w : 𝒜 ⟶ 𝒜.dual), IsWeilHom t t P w → ∀ (f f' : A ⟶ A) [IsMonHom f] [IsMonHom f'], LBIso (ev P (fst A A ≫ f) (snd A A)) (ev P (fst A A) (snd A A ≫ f')) → t.map t f ≫ w = w ≫ dualHom _ _ (t.map t f') := by
  intro _ p _ K _ A _ hA P hP 𝒜 t w hw f f' _ _ h
  refine PDivGroup.hom_ext fun n => BialgHom.ext fun χ => ?_
  obtain ⟨U, hU, hχ⟩ := hw n
  have e := map_unit_eq hA hP.isLB f f' h (t.y n) _ _ (t.map_y t f n) (t.map_y t f' n) U hU
  have e' := congrArg (fun u => TensorProduct.rid K (𝒜.A n) (LinearMap.lTensor (𝒜.A n) (WithConv.ofConv χ) u)) e
  simp only [rid_lTensor_map] at e'
  show (t.map t f).app n (w.app n χ) = w.app n (CartierDual.map ((t.map t f').app n) χ)
  rw [hχ, hχ]
  exact e'

end GlobalTheory.WeilAdjoint
