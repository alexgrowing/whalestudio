import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagCommonClosedPointOfGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixElementaryShearPropertiesStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.Meet

theorem val_spMap_pt {F : Type} [Field F] (Y : Var F) {K : Type} [Field K] (σ : Y.Fn →+* K) (x : Y.Fn) :
    (ratOf Y).val (spMap σ ≫ (ratOf Y).pt) x = σ x := by
  have hx : x ∈ (ratOf Y).O ((ratOf Y).pt (IsLocalRing.closedPoint Y.Fn)) := by
    refine (congrArg (fun z => x ∈ (ratOf Y).O z) ((ratOf Y).pt_apply _)).mpr ?_
    rw [RatModel.O_genericPoint]; exact Algebra.mem_top
  have h := RatModel.val_spMap_comp (M := ratOf Y) σ (ratOf Y).pt specializes_rfl ⟨x, hx⟩
  rw [RatModel.valLoc_eq_val] at h
  exact h.trans (congrArg σ (RatModel.val_pt x))

open GlobalTheory.FlagBundle.ClosedPt in

theorem meet : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ B ∈ E'.S (genericPoint Y.X), ∀ A ∈ E.S (f (genericPoint Y.X)), ∀ (τ : ι) (a b : Fin (m τ)), a < b → ∀ (K : Type) [Field K] (V : ValuationSubring K) (c : Y.Fn →+* V) (t : V), IsLocalRing.residue V t = 0 → ∀ v₂ : Sp V ⟶ Y.X, v₂ ≫ f = spMap c ≫ (ratOf Y).pt ≫ f → Bears E' φ A (shear τ a b (t : K) * (B * (A.map φ)⁻¹).map ((algebraMap V K).comp c)) (spMap (algebraMap V K) ≫ v₂) → spMap (IsLocalRing.residue V) ≫ spMap c ≫ (ratOf Y).pt = spMap (IsLocalRing.residue V) ≫ v₂ := by
  intro F _ X Y ι _ m E E' φ f hf B hB A hA τ a b hab K _ V c t ht v₂ e hbear
  have hM := hf.sub _ B hB A hA
  obtain ⟨-, -, -, hsm⟩ := GlobalTheory.T.blockMatrixElementaryShear_properties ι m τ a b hab V t
  obtain ⟨-, -, hs0, -⟩ := GlobalTheory.T.blockMatrixElementaryShear_properties ι m τ a b hab (IsLocalRing.ResidueField V) 0
  have hpt : ∀ (R : Type) [CommRing R] (g : Y.Fn →+* R) (w : Sp R),
      (spMap g ≫ (ratOf Y).pt) w = genericPoint Y.X := fun R _ g w =>
    (Scheme.Hom.comp_apply _ _ _).trans ((ratOf Y).pt_apply _)
  have hf₂ : f (v₂ (IsLocalRing.closedPoint V)) = f (genericPoint Y.X) := by
    refine (Scheme.Hom.comp_apply _ _ _).symm.trans ?_
    rw [e]
    exact (Scheme.Hom.comp_apply (spMap c ≫ (ratOf Y).pt) f _).trans (congrArg f (hpt _ c _))
  obtain ⟨A₂, hA₂⟩ := E'.nonempty (v₂ (IsLocalRing.closedPoint V))
  have hM₂ := hf.sub _ A₂ hA₂ A ((congrArg (fun z => A ∈ E.S z) hf₂).mpr hA)
  obtain ⟨A₂', hA₂', hpar⟩ := hbear
  have hA₂g : A₂ ∈ E'.S ((spMap (algebraMap V K) ≫ v₂) (IsLocalRing.closedPoint K)) :=
    Fr.mem_of_specializes hA₂ (gen_specializes v₂ _)
  have hsp₂ := gen_specializes (L := K) v₂ (IsLocalRing.closedPoint K)
  have hG := (Fr.mem_iff hA₂g).1 hA₂'
  have hM₂g : Par 0 ((ratOf Y).O ((spMap (algebraMap V K) ≫ v₂) (IsLocalRing.closedPoint K))).toSubring
      (A₂ * (A.map φ)⁻¹) :=
    hM₂.mono le_rfl fun _ hx => RatModel.O_le_of_specializes hsp₂ hx
  set ψ := RatModel.valHom (M := ratOf Y) (spMap (algebraMap V K) ≫ v₂) _
    (RatModel.range_eq_singleton _ (IsLocalRing.closedPoint K))
  have hv : ∀ x : ((ratOf Y).O ((spMap (algebraMap V K) ≫ v₂) (IsLocalRing.closedPoint K))).toSubring,
      (ratOf Y).val (spMap (algebraMap V K) ≫ v₂) x = ψ x := fun _ => rfl
  have heqM : A₂' * (A.map φ)⁻¹ = (A₂' * A₂⁻¹) * (A₂ * (A.map φ)⁻¹) := by
    rw [mul_assoc, ← mul_assoc A₂⁻¹, Mat.inv_mul (Fr.det_ne hA₂), one_mul]
  have hmap : (A₂' * (A.map φ)⁻¹).map ((ratOf Y).val (spMap (algebraMap V K) ≫ v₂)) =
      (A₂' * A₂⁻¹).map ((ratOf Y).val (spMap (algebraMap V K) ≫ v₂)) *
        (A₂ * (A.map φ)⁻¹).map ((ratOf Y).val (spMap (algebraMap V K) ≫ v₂)) := by
    rw [heqM]
    exact Par.map_mul_of hG hM₂g ((ratOf Y).val (spMap (algebraMap V K) ≫ v₂)) ψ hv
  have hGv := Par.map_of hG ((ratOf Y).val (spMap (algebraMap V K) ≫ v₂)) ψ hv
  have hpar2 := hpar
  erw [hmap] at hpar2
  rw [Mat.mul_inv_rev] at hpar2
  clear hpar
  have hL := hpar2.mul hGv
  rw [mul_assoc, mul_assoc, mul_assoc, Mat.inv_mul hGv.det_ne, mul_one, ← mul_assoc] at hL
  rw [map_val (algebraMap V K) v₂ _ (fun τ a b => (hM₂ τ).1 a b)] at hL
  have hN : ∀ (S : Type) [CommRing S] (g : V →+* S),
      (shear τ a b t * (B * (A.map φ)⁻¹).map c).map g =
        shear τ a b (g t) * (B * (A.map φ)⁻¹).map (g.comp c) := fun S _ g => by
    rw [← hsm S g]
    funext σ
    exact Matrix.map_mul
  have hN1 := hN K (algebraMap V K)
  have hN2 := hN _ (IsLocalRing.residue V)
  rw [ht, hs0, one_mul] at hN2
  have hh : Par 0 ⊤ ((B * (A.map φ)⁻¹).map ((IsLocalRing.residue V).comp c)) :=
    hM.map _ fun _ _ => trivial
  have hk₂ := par_val (IsLocalRing.residue V) v₂ hM₂
  have hD := descend (L := K) (shear τ a b t * (B * (A.map φ)⁻¹).map c)
    (vals v₂ _ (fun τ a b => (hM₂ τ).1 a b)) (by rw [hN2]; exact hh.det_ne)
    (by rw [← map_val]; exact hk₂.det_ne) (by rw [hN1]; exact hL)
  rw [hN2, ← map_val] at hD
  have ec : spMap (IsLocalRing.residue V) ≫ spMap c ≫ (ratOf Y).pt =
      spMap ((IsLocalRing.residue V).comp c) ≫ (ratOf Y).pt := by
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  have hb₂ : Bears E' φ A ((B * (A.map φ)⁻¹).map ((IsLocalRing.residue V).comp c))
      (spMap (IsLocalRing.residue V) ≫ v₂) :=
    ⟨A₂, (congrArg (fun z => A₂ ∈ E'.S z) (closedPt_comp v₂)).mpr hA₂, hD⟩
  have hb₁ : Bears E' φ A ((B * (A.map φ)⁻¹).map ((IsLocalRing.residue V).comp c))
      (spMap ((IsLocalRing.residue V).comp c) ≫ (ratOf Y).pt) := by
    refine ⟨B, (congrArg (fun z => B ∈ E'.S z) (hpt _ _ _)).mpr hB, ?_⟩
    rw [show (ratOf Y).val (spMap ((IsLocalRing.residue V).comp c) ≫ (ratOf Y).pt) =
      ⇑((IsLocalRing.residue V).comp c) from funext (val_spMap_pt Y _), Mat.mul_inv hh.det_ne]
    exact Par.one
  have hAk : A ∈ E.S (((spMap (IsLocalRing.residue V) ≫ v₂) ≫ f)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField V))) := by
    refine (congrArg (fun z => A ∈ E.S z) ?_).mpr hA
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg f (closedPt_comp v₂)).trans hf₂)
  obtain ⟨p, -, hp⟩ := hf.lifts _ _ A hAk _ hh
  refine (ec.trans (hp _ ⟨?_, hb₁⟩)).trans (hp _ ⟨rfl, hb₂⟩).symm
  rw [← ec]
  exact congrArg (spMap (IsLocalRing.residue V) ≫ ·) e.symm

end GlobalTheory.FlagPush.Meet
