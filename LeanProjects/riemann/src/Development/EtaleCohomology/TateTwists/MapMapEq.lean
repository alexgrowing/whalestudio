import Development.EtaleCohomology.TateTwists.columnPf

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleFoundations.columnPf

def kerLoc : Prop :=
  ∀ (R : Type) [CommRing R] (M : Shv R) (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ M.obj),
    (∀ (U : Scheme.{0}) (y : Sec M U), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = Sec.res g y) →
    (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) →
    ∀ (G : Shv R) (V : Scheme.{0}) (u : Sec G V ⊗[ULift.{1} R] P.obj (op V)),
      TensorProduct.map LinearMap.id (φ.app (op V)).hom u = 0 →
      Loc V fun _ k => TensorProduct.map (G.obj.map k.op).hom (P.map k.op).hom u = 0

theorem map_map_eq {S : Type*} [CommRing S] {A B C D A' B' C' D' : Type*} [AddCommGroup A] [Module S A]
    [AddCommGroup B] [Module S B] [AddCommGroup C] [Module S C] [AddCommGroup D] [Module S D]
    [AddCommGroup A'] [Module S A'] [AddCommGroup B'] [Module S B'] [AddCommGroup C'] [Module S C']
    [AddCommGroup D'] [Module S D']
    (f1 : A →ₗ[S] A') (f2 : A' →ₗ[S] C) (f1' : A →ₗ[S] C') (f2' : C' →ₗ[S] C)
    (g1 : B →ₗ[S] B') (g2 : B' →ₗ[S] D) (g1' : B →ₗ[S] D') (g2' : D' →ₗ[S] D)
    (hf : f2 ∘ₗ f1 = f2' ∘ₗ f1') (hg : g2 ∘ₗ g1 = g2' ∘ₗ g1') (x : A ⊗[S] B) :
    TensorProduct.map f2 g2 (TensorProduct.map f1 g1 x) = TensorProduct.map f2' g2' (TensorProduct.map f1' g1' x) := by
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, hf, hg, TensorProduct.map_comp, LinearMap.comp_apply]

end LateralTheory.EtaleFoundations.columnPf

open LateralTheory.EtaleFoundations.columnPf in
theorem LateralTheory.EtaleFoundations.columnPf.lift_of (hK : kerLoc) : lift := by
  classical
  intro R _ M P φ hsurj hker F G δ U x hx
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset x
  refine loc_bind (loc_finset S fun i _ => hsurj U i.2) ?_
  intro V g hV
  choose p hp using hV
  let x' : Sec F V ⊗[ULift.{1} R] P.obj (op V) := ∑ i ∈ S.attach, (F.obj.map g.op).hom i.1.1 ⊗ₜ p i.1 i.2
  have h1 : TensorProduct.map LinearMap.id (φ.app (op V)).hom x' =
      TensorProduct.map (F.obj.map g.op).hom (M.obj.map g.op).hom x := by
    rw [hS, map_sum, map_sum, ← Finset.sum_attach S]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [TensorProduct.map_tmul, LinearMap.id_apply]
    rw [hp i.1 i.2]
  have nat : ∀ {V' V : Scheme.{0}} (k : V' ⟶ V), (G.obj.map k.op).hom ∘ₗ (δ.hom.app (op V)).hom =
      (δ.hom.app (op V')).hom ∘ₗ (F.obj.map k.op).hom := fun k => by
    rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, δ.hom.naturality]
  have h2 : TensorProduct.map LinearMap.id (φ.app (op V)).hom
      (TensorProduct.map (δ.hom.app (op V)).hom LinearMap.id x') = 0 := by
    rw [map_map_eq (f1 := (δ.hom.app (op V)).hom) (f2 := LinearMap.id) (g1 := LinearMap.id) (g2 := (φ.app (op V)).hom)
      (f1' := LinearMap.id) (f2' := (δ.hom.app (op V)).hom) (g1' := (φ.app (op V)).hom) (g2' := LinearMap.id)
      (by simp) (by simp), h1,
      map_map_eq (f1 := (F.obj.map g.op).hom) (f2 := (δ.hom.app (op V)).hom) (g1 := (M.obj.map g.op).hom)
      (g2 := LinearMap.id) (f1' := (δ.hom.app (op U)).hom) (f2' := (G.obj.map g.op).hom) (g1' := LinearMap.id)
      (g2' := (M.obj.map g.op).hom) (nat g).symm (by simp), hx, map_zero]
  refine loc_mono (hK R M P φ hsurj hker G V _ h2) ?_
  intro W k hk
  refine ⟨TensorProduct.map (F.obj.map k.op).hom (P.map k.op).hom x', ?_, ?_⟩
  · rw [map_map_eq (f1 := (F.obj.map k.op).hom) (f2 := (δ.hom.app (op W)).hom) (g1 := (P.map k.op).hom)
      (g2 := LinearMap.id) (f1' := (δ.hom.app (op V)).hom) (f2' := (G.obj.map k.op).hom) (g1' := LinearMap.id)
      (g2' := (P.map k.op).hom) (nat k).symm (by simp), hk]
  · have hφ : (φ.app (op W)).hom ∘ₗ (P.map k.op).hom = (M.obj.map k.op).hom ∘ₗ (φ.app (op V)).hom := by
      rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, φ.naturality]
    rw [map_map_eq (f1 := (F.obj.map k.op).hom) (f2 := LinearMap.id) (g1 := (P.map k.op).hom)
      (g2 := (φ.app (op W)).hom) (f1' := LinearMap.id) (f2' := (F.obj.map k.op).hom) (g1' := (φ.app (op V)).hom)
      (g2' := (M.obj.map k.op).hom) (by simp) hφ, h1, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
    simp only [op_comp, Functor.map_comp, ModuleCat.hom_comp]

open LateralTheory.EtaleFoundations.columnPf in
theorem LateralTheory.EtaleFoundations.columnPf.column_of' (hK : kerLoc) : LateralTheory.EtaleFoundations.acyc.column :=
  LateralTheory.EtaleFoundations.acyc.column_of_cut (lift_of hK) kill_of
