import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.SameB

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.GenericFibreSections

variable {X₁ X₂ Y Y' : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂}

theorem exists_transfer (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) (φ₁ : Y ⟶ X₁) (φ₂ : Y ⟶ X₂) (k : ℤ)
    (V : L₁.ι → L₂.ι → Y.Opens) (hV : ∀ i j y, φ₁ y ∈ L₁.U i → φ₂ y ∈ L₂.U j → y ∈ V i j)
    (u : ∀ i j, Γ(Y, V i j)ˣ)
    (hu : ∀ (y : Y) i i' j j', φ₁ y ∈ L₁.U i → φ₁ y ∈ L₁.U i' → φ₂ y ∈ L₂.U j → φ₂ y ∈ L₂.U j' →
      gm (𝟙 Y) y _ (u i j) * gm (𝟙 Y ≫ φ₁) y _ (L₁.g i i') ^ k =
        gm (𝟙 Y ≫ φ₂) y _ (L₂.g j j') ^ k * gm (𝟙 Y) y _ (u i' j'))
    (s : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => φ₁) (fun _ => k))) :
    ∃ s' : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => φ₂) (fun _ => k)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J₁ J₂, Good L₁ z J₁ → Good L₂ z J₂ →
        sval s' r z J₂ = (gm r z _ (u (J₁ (r ≫ φ₁)) (J₂ (r ≫ φ₂)))).val * sval s r z J₁ := by
  have glue : ∀ j : Fin 1 → L₂.ι, ∃ a : Γ(Y, LB.wchart L₂ (fun _ : Fin 1 => φ₂) j),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : L₁.ι),
      r z ∈ LB.wchart L₂ (fun _ : Fin 1 => φ₂) j → φ₁ (r z) ∈ L₁.U i →
      gs r z _ a = (gm r z _ (u i (j 0))).val *
        gs r z (LB.wchart L₁ (fun _ : Fin 1 => φ₁) (fun _ => i)) (s.f (fun _ => i)) := by
    intro j
    let W : L₁.ι → Y.Opens := fun i =>
      LB.wchart L₂ (fun _ : Fin 1 => φ₂) j ⊓ LB.wchart L₁ (fun _ : Fin 1 => φ₁) (fun _ => i)
    have l : ∀ i, W i ≤ V i (j 0) := fun i y hy =>
      hV i (j 0) y (Set.mem_iInter.1 hy.2 0) (Set.mem_iInter.1 hy.1 0)
    obtain ⟨b, hb⟩ : ∃ b : ∀ i, Γ(Y, W i), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) i, r z ∈ W i →
        gs r z (W i) (b i) = (gm r z _ (u i (j 0))).val *
          gs r z (LB.wchart L₁ (fun _ : Fin 1 => φ₁) (fun _ => i)) (s.f (fun _ => i)) :=
      ⟨fun i => (Y.presheaf.map (homOfLE (l i)).op).hom (u i (j 0)).val *
          (Y.presheaf.map (homOfLE (inf_le_right : W i ≤ LB.wchart L₁ (fun _ : Fin 1 => φ₁) (fun _ => i))).op).hom
            (s.f (fun _ => i)), fun Z r z i hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res r z _ hz _).trans (gs_unit r z _ (l i hz) _))
          (gs_res r z _ hz _))⟩
    obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' W (LB.wchart L₂ (fun _ : Fin 1 => φ₂) j)
      (fun i => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨i, hi⟩ := exists_chart hL₁ (φ₁ y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hy, Set.mem_iInter.2 fun _ => hi⟩) b
      (fun i i' => fn_ext (V := W i ⊓ W i') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        have m : φ₂ y ∈ L₂.U (j 0) := Set.mem_iInter.1 hy.1.1 0
        have e := hu y i i' (j 0) (j 0) (Set.mem_iInter.1 hy.1.2 0) (Set.mem_iInter.1 hy.2.2 0) m m
        rw [gm_self hL₂ (𝟙 Y ≫ φ₂) y m, _root_.one_zpow, _root_.one_mul] at e
        rw [hb _ _ y i hy.1, hb _ _ y i' hy.2, sec_trans s (𝟙 Y) y hy.1.2 hy.2.2, ← _root_.mul_assoc, ← Units.val_mul,
          ← e, trF, Fintype.prod_unique])
    refine ⟨a, fun Z r z i h₁ h₂ => ?_⟩
    have hz : r z ∈ W i := ⟨h₁, Set.mem_iInter.2 fun _ => h₂⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z (W i)) (ha i)).trans (hb Z r z i hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  · obtain ⟨i, hi⟩ := exists_chart hL₁ (φ₁ y)
    refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L₂ _ _ (𝟙 Y) y j j' hy.1 hy.2)))
      (gs_res (𝟙 Y) y _ hy _))).symm)
    refine (ha j _ (𝟙 Y) y i hy.1 hi).trans (Eq.trans ?_ (congrArg _ (ha j' _ (𝟙 Y) y i hy.2 hi)).symm)
    have e := hu y i i (j 0) (j' 0) hi hi (Set.mem_iInter.1 hy.1 0) (Set.mem_iInter.1 hy.2 0)
    rw [gm_self hL₁ (𝟙 Y ≫ φ₁) y hi, _root_.one_zpow, _root_.mul_one] at e
    rw [e, Fintype.prod_unique, Units.val_mul, _root_.mul_assoc]
    rfl
  · exact ha _ Z r z (J₁ (r ≫ φ₁)) (hJ₂.mem (fun _ : Fin 1 => φ₂) r) (hJ₁ (r ≫ φ₁))

theorem exists_pull (h : Y' ⟶ Y) (φ : Y ⟶ X₁) (φ' : Y' ⟶ X₁) (e : φ' = h ≫ φ) (k : ℤ)
    (s : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => φ) (fun _ => k))) :
    ∃ s' : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => φ') (fun _ => k)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J, Good L₁ z J → sval s' r z J = sval s (r ≫ h) z J := by
  subst e
  exact ⟨_, fun Z r z J hJ => H1.SectionArithmetic.sval_pullSec s h r z hJ⟩

theorem sec_ext {M : LB Y} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  obtain ⟨f, _⟩ := s
  obtain ⟨f', _⟩ := s'
  obtain rfl : f = f' := funext h
  rfl

theorem gw_trans {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} (hw : w.IsGen) (y : Y)
    {i i' : L₁.ι} {j j' : L₂.ι} (hi : f₁ y ∈ L₁.U i) (hi' : f₁ y ∈ L₁.U i') (hj : f₂ y ∈ L₂.U j) (hj' : f₂ y ∈ L₂.U j') :
    gw w (𝟙 Y) y j (fun _ => i) * gm (𝟙 Y ≫ f₁) y _ (L₁.g i i') =
      gm (𝟙 Y ≫ f₂) y _ (L₂.g j j') * gw w (𝟙 Y) y j' (fun _ => i') := by
  have e := (isGen_iff w).1 hw Y (𝟙 Y) y j j' (fun _ => i) (fun _ => i') hj hj' (mem_pull.2 hi) (mem_pull.2 hi')
  rw [gm_pull_g L₁ f₁ (𝟙 Y) y _ _ (mem_pull.2 hi) (mem_pull.2 hi')] at e
  rw [e, _root_.mul_right_comm, inv_mul_cancel_right]

theorem bijective_of_iso (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (p : Y' ⟶ X₁) [IsIso f₁] [IsIso p]
    (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (hw : w.IsGen) (k : ℕ)
    (Rel : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))) →
      LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => p) (fun _ => (k : ℤ))) → Prop)
    (hRel : ∀ σ t, Rel σ t ↔ ∀ (Z : Scheme.{0}) (rA : Z ⟶ Y') (y : Z ⟶ Y), rA ≫ p = y ≫ f₁ → ∀ (z : Z) J₁ J₂,
      Good L₁ z J₁ → Good L₂ z J₂ →
      (gw w y z (J₂ (y ≫ f₂)) (fun _ => J₁ (y ≫ f₁))).val ^ k * sval t rA z J₁ = sval σ y z J₂) :
    (∀ σ, ∃! t, Rel σ t) ∧ ∀ t, ∃! σ, Rel σ t := by
  have hV : ∀ i j (y : Y), f₁ y ∈ L₁.U i → f₂ y ∈ L₂.U j →
      y ∈ (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i) := fun i j y hi hj => ⟨mem_pull.2 hj, mem_pull.2 hi⟩
  refine ⟨fun σ => ?_, fun t => ?_⟩
  · obtain ⟨s, hs⟩ := exists_transfer hL₂ hL₁ f₂ f₁ k
      (fun j i => (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i)) (fun j i y hj hi => hV i j y hi hj)
      (fun j i => ((show Γ(Y, (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i))ˣ from
        w.s (fun _ => j, fun _ => i)) ^ k)⁻¹) (fun y j j' i i' hj hj' hi hi' => by
        have e := gw_trans hw y hi hi' hj hj'
        rw [map_inv, map_inv, map_pow, map_pow, zpow_natCast, zpow_natCast]
        change (gw w (𝟙 Y) y j (fun _ => i) ^ k)⁻¹ * _ = _ * (gw w (𝟙 Y) y j' (fun _ => i') ^ k)⁻¹
        rw [inv_mul_eq_iff_eq_mul, ← _root_.mul_assoc, ← mul_pow, e, mul_pow, mul_inv_cancel_right]) σ
    obtain ⟨t, ht⟩ := exists_pull (p ≫ inv f₁) f₁ p (by simp) k s
    refine ⟨t, (hRel _ _).2 fun Z rA y e z J₁ J₂ h₁ h₂ => ?_, fun t' H' => ?_⟩
    · have e' : rA ≫ p ≫ inv f₁ = y := by rw [← Category.assoc, e]; simp
      rw [ht Z rA z J₁ h₁, e', hs Z y z J₂ J₁ h₂ h₁, map_inv, map_pow, ← Units.val_pow_eq_pow_val]
      exact Units.mul_inv_cancel_left _ _
    · refine sec_ext (sec_ext_val hL₁ fun y J₁ h₁ => ?_)
      choose J₂ h₂ using fun χ : Y' ⟶ X₂ => exists_chart hL₂ (χ y)
      have e := (hRel _ _).1 H' Y' (𝟙 _) (p ≫ inv f₁) (by simp) y J₁ J₂ h₁ h₂
      rw [ht _ _ y J₁ h₁, Category.id_comp, hs _ _ y J₂ J₁ h₂ h₁, map_inv, map_pow, ← e, ← Units.val_pow_eq_pow_val]
      exact (Units.inv_mul_cancel_left _ _).symm
  · obtain ⟨s, hs⟩ := exists_pull (f₁ ≫ inv p) p f₁ (by simp) k t
    obtain ⟨σ, hσ⟩ := exists_transfer hL₁ hL₂ f₁ f₂ k
      (fun i j => (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i)) hV
      (fun i j => (show Γ(Y, (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i))ˣ from
        w.s (fun _ => j, fun _ => i)) ^ k) (fun y i i' j j' hi hi' hj hj' => by
        have e := gw_trans hw y hi hi' hj hj'
        rw [map_pow, map_pow, zpow_natCast, zpow_natCast, ← mul_pow, ← mul_pow]
        exact congrArg (· ^ k) e) s
    refine ⟨σ, (hRel _ _).2 fun Z rA y e z J₁ J₂ h₁ h₂ => ?_, fun σ' H' => ?_⟩
    · have e' : y ≫ f₁ ≫ inv p = rA := by rw [← Category.assoc, ← e]; simp
      rw [hσ Z y z J₁ J₂ h₁ h₂, hs Z y z J₁ h₁, e', map_pow, Units.val_pow_eq_pow_val]
      rfl
    · refine sec_ext (sec_ext_val hL₂ fun y J₂ h₂ => ?_)
      choose J₁ h₁ using fun χ : Y ⟶ X₁ => exists_chart hL₁ (χ y)
      have e := (hRel _ _).1 H' Y (𝟙 Y ≫ f₁ ≫ inv p) (𝟙 _) (by simp) y J₁ J₂ h₁ h₂
      rw [← e, hσ _ _ y J₁ J₂ h₁ h₂, hs _ _ y J₁ h₁, map_pow, Units.val_pow_eq_pow_val]
      rfl

theorem sameK_bijective : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (k : ℕ), (∀ σ, ∃! t, U.SameK (k := k) σ t) ∧ ∀ t, ∃! σ, U.SameK (k := k) σ t := by
  intro R _ _ I D A G _ _ U k
  have h₀ : IsIso (TFK (R := R) (FractionRing R)).hom := by
    show IsIso (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R))))
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    infer_instance
  have h₁ : IsIso (snd (TFK (R := R) (FractionRing R)) A.A).left :=
    inferInstanceAs (IsIso (pullback.snd (TFK (R := R) (FractionRing R)).hom A.A.hom))
  have h₂ : IsIso U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.hom))
  exact bijective_of_iso A.isLB U.P.L.isLB U.gen.hom.left (pullback.fst G.hom (jK R))
    (snd (TFK (R := R) (FractionRing R)) A.A).left U.wA U.wA_gen k (fun σ t => U.SameK (k := k) σ t)
    (fun _ _ => Iff.rfl)

end GlobalTheory.GenericFibreSections
end
