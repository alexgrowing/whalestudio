import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatV

open GlobalTheory.LogKSBal GlobalTheory.KS GlobalTheory.TangentOrigin

theorem spMap_resV (R : Type) [CommRing R] (c : R) : spMap (resV R c) = chart (bo R c) := by
  have h := (isAffineOpen_top (Sp R)).map_fromSpec (bo R c).2
    (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c))).op
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  exact h

theorem exists_isTr {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {S : Type} [CommRing S]
    (φ : R →+* S) (g : Sp S ⟶ G.left) (hg : g ≫ G.hom = spMap φ) (v : TanM (𝟙 (Sp R)) G) : ∃ w, IsTr G φ g v w := by
  have e : (dualMap φ).comp (algebraMap R (DualNumber R)) = (algebraMap S (DualNumber S)).comp φ := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have h1 : (tv v).left ≫ G.hom = spMap (algebraMap R (DualNumber R)) := (Over.w (tv v)).trans (Category.comp_id _)
  have h2 : (spMap (dualMap φ) ≫ (tv v).left) ≫ G.hom = (tEpsG (g ≫ G.hom)).hom := by
    show _ = spMap (algebraMap S (DualNumber S)) ≫ g ≫ G.hom
    rw [Category.assoc, h1, hg, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]
  exact ⟨_, Over.homMk (spMap (algebraMap S (DualNumber S)) ≫ g) (Category.assoc _ _ _),
    Over.homMk (spMap (dualMap φ) ≫ (tv v).left) h2, rfl, rfl, rfl⟩

theorem spMap_dualMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (dualMap (g.comp f)) = spMap (dualMap g) ≫ spMap (dualMap f) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMap]

theorem ksRel_operators : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R), (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (c : R), c = ∏ i, tt i → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) → ∀ (DV : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), IsKS t (GlobalTheory.HeatV.bo R c).1 (GlobalTheory.HeatV.bo R c) (fun a => spMap (dualMap (GlobalTheory.HeatV.resV R c)) ≫ (tv (v' a)).left) DV Θ₁ → ∃ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → Fld t.G.left) (hW : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⨆ i, W i = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 ∧ (∀ i, W i ≤ t.PP.L.U (j i)) ∧ (∀ i, IsField (W i) (d i)) ∧ (∀ i O (h : O ≤ W i) (a : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), d i O (GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) a) = GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) (DV a)) ∧ (∀ i i' O (h : O ≤ W i ⊓ W i') (f : Γ(t.G.left, O)), d i O f - d i' O f = ∑ a, ∑ b, GlobalTheory.HeatV.cst t.G.hom (GlobalTheory.HeatV.bo R c).1 (h.trans (inf_le_left.trans (hW i))) (Θ₁ a b) * (dd' b O (rsT (t.PP.L.g (j i) (j i')).val O) * rsT (t.PP.L.g (j i) (j i'))⁻¹.val O) * dd' a O f) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt _ _ c _ n v' dd' hdd DV Θ₁ hKS
  obtain ⟨J, W, j, d, hcov, hWj, hfld, hlift, hdiff⟩ := hKS
  rw [inf_idem] at hcov
  have hW : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ (bo R c).1 := fun i => (le_iSup W i).trans hcov.le
  refine ⟨J, W, j, d, hW, hcov, hWj, hfld, fun i O h a => ?_, fun i i' O h f => ?_⟩
  · have e : ∀ s : Γ(Sp R, (bo R c).1), cst t.G.hom _ (h.trans (hW i)) s = resG _ h (cst t.G.hom _ (hW i) s) := fun s => by
      rw [← rsT_of_le h, ← pbT_of_le, ← pbT_of_le, rsT_pbT t.G.hom (hW i) h]
    rw [e, e, (hfld i).2.2 _ _ h le_rfl, hlift]
  · refine ext_valR _ _ fun S _ x hx => ?_
    have hO : O ≤ t.G.hom ⁻¹ᵁ (bo R c).1 := h.trans (inf_le_left.trans (hW i))
    have hr : Set.range (x ≫ t.G.hom) ⊆ Set.range (chart (bo R c)) := by
      rintro _ ⟨p, rfl⟩
      exact (bo R c).2.range_fromSpec.superset (hO (hx (Set.mem_univ p)))
    have : IsOpenImmersion (chart (bo R c)) := (bo R c).2.isOpenImmersion_fromSpec
    obtain ⟨φ, hφ⟩ : ∃ φ : Γ(Sp R, (bo R c).1) →+* S, x ≫ t.G.hom = spMap φ ≫ chart (bo R c) :=
      ⟨(Spec.preimage (IsOpenImmersion.lift _ _ hr)).hom, by
        rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]⟩
    have hφ' : x ≫ t.G.hom = spMap (φ.comp (resV R c)) := by
      rw [hφ, ← spMap_resV, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    choose w hw using fun a => exists_isTr t.G _ x hφ' (v' a)
    have key := hdiff i i' O h f S φ x w hφ hx fun a => by
      obtain ⟨g', u, h₁, h₂, h₃⟩ := hw a
      exact ⟨g', u, h₁, by rw [h₂, spMap_dualMap_comp_eq, Category.assoc], h₃⟩
    have hOg : O ≤ t.PP.L.U (j i) ⊓ t.PP.L.U (j i') := fun p hp => ⟨hWj i (h hp).1, hWj i' (h hp).2⟩
    have hxg : ⊤ ≤ x ⁻¹ᵁ (t.PP.L.U (j i) ⊓ t.PP.L.U (j i')) := fun p hp => hOg (hx hp)
    rw [key, valR_eq x hx, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, map_mul, map_mul, ← valR_eq, ← valR_eq, ← valR_eq, ← valR_eq,
      (hdd a).2 S _ x (w a) O f hφ' hx (hw a), (hdd b).2 S _ x (w b) _ _ hφ' hxg (hw b), valR_rsT x hOg hx,
      rsT_of_le hOg, (hdd b).1.2.2 _ _ hOg le_top, ← rsT_of_le hOg, valR_rsT x hOg hx, ← pbT_of_le,
      valR_pbT x _ hO hx, hφ, valR_chart]

end GlobalTheory.HeatV
