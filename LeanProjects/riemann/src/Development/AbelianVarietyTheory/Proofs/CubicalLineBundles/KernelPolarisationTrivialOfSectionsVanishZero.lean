import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIsGenTranslDiffComp

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem appLE_top_eq_zero_iff_gs {X Z : Scheme.{0}} (r : Z ⟶ X) (U : X.Opens) (h : ⊤ ≤ r ⁻¹ᵁ U) (a : Γ(X, U)) :
    (r.appLE U ⊤ h).hom a = 0 ↔ ∀ z, gs r z U a = 0 := by
  have e : ∀ z, gs (𝟙 Z) z ⊤ ((r.appLE U ⊤ h).hom a) = gs r z U a := fun z =>
    (gs_appLE r U ⊤ h (𝟙 Z) z trivial a).trans (by rw [Category.id_comp])
  have e0 : ∀ z : Z, gs (𝟙 Z) z ⊤ 0 = 0 := fun z => by
    rw [gs_eq (𝟙 Z) z ⊤ trivial, map_zero, map_zero]
  exact ⟨fun H z => by rw [← e z, H, e0], fun H => fn_ext fun z _ => by rw [e z, H z, e0]⟩

theorem exists_pull_sec_sval {X Y : Scheme.{0}} {L : LB X} (θ : L.Sec) (F : Y ⟶ X) :
    ∃ s : (L.pull F).Sec, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval s r z J = gs (r ≫ F) z (L.U (J (r ≫ F))) (θ.f (J (r ≫ F))) := by
  have le : ∀ J, (L.pull F).U J ≤ F ⁻¹ᵁ L.U (J PUnit.unit) := fun J => LB.wchart_le L _ J PUnit.unit
  have ev : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) z J, r z ∈ (L.pull F).U J →
      gs r z _ ((F.appLE _ _ (le J)).hom (θ.f _)) = gs (r ≫ F) z _ (θ.f (J PUnit.unit)) :=
    fun Z r z J h => gs_appLE F _ _ (le J) r z h _
  refine ⟨⟨fun J => (F.appLE _ _ (le J)).hom (θ.f _), fun J J' => fn_ext fun y hy => ?_⟩,
    fun Z r z J hJ => ev Z r z _ (hJ.mem _ r)⟩
  have hm : (𝟙 Y ≫ F) y ∈ L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit) := ⟨le J hy.1, le J' hy.2⟩
  have e := congrArg (gs (𝟙 Y ≫ F) y _) (θ.compat (J PUnit.unit) (J' PUnit.unit))
  rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_unit _ y _ hm] at e
  refine ((gs_res (𝟙 Y) y _ hy _).trans ((ev _ _ y J hy.1).trans e)).trans
    (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 Y) y J J' hy.1 hy.2)))
      ((gs_res (𝟙 Y) y _ hy _).trans (ev _ _ y J' hy.2)))).symm)
  simp

theorem exists_sec_of_gen_diff {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (θ : L.Sec) (ψ φ : Y ⟶ X)
    (d : LB.Gen (LB.LinComb L (K := Fin 2) ![ψ, φ] ![1, -1])) (hd : d.IsGen) :
    ∃ s : (L.pull φ).Sec, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval s r z J = 0 → gs (r ≫ ψ) z (L.U (J (r ≫ ψ))) (θ.f (J (r ≫ ψ))) = 0 := by
  obtain ⟨s₀, hs₀⟩ := exists_pull_sec_sval θ ψ
  have hF : FormEq (Sum.elim (fun _ : PUnit => 𝟙 Y ≫ ψ) ![ψ, φ])
      (Sum.elim (fun _ => 1) (fun k => -(![1, -1] : Fin 2 → ℤ) k)) (fun _ : PUnit => φ) (fun _ => 1) := by
    intro U _ h
    simp [Fintype.prod_sum_type, Fin.prod_univ_two]
  obtain ⟨s, hs⟩ := exists_sec hL hF (pullMulSec s₀ (𝟙 Y) (LB.invGen L _ _ d) (LB.isGen_invGen L _ _ d hd))
  refine ⟨s, fun Z r z J hJ H => ?_⟩
  rw [hs Z r z J hJ, sval_pullMulSec _ _ _ _ r z hJ, Category.comp_id, hs₀ Z r z J hJ] at H
  exact (Units.mul_left_eq_zero _).1 H

theorem kTriv_of_sections_vanish_on_zero : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left) (θ : L.Sec), L.IsLB → (∀ (T : Scheme.{0}) (t : T ⟶ A.left) (i : L.ι) (h : ⊤ ≤ t ⁻¹ᵁ L.U i), (t.appLE (L.U i) ⊤ h).hom (θ.f i) = 0 ↔ t = t ≫ A.hom ≫ eSec A) → (∀ (R' : Type) [CommRing R'] (f : Sp R' ⟶ S) (Y : Scheme.{0}) (φ : Y ⟶ A.left) (q : Y ⟶ Sp R'), IsPullback φ q A.hom f → ∀ (s : (L.pull φ).Sec) (T : Scheme.{0}) (t : T ⟶ Y) (j : (L.pull φ).ι) (h : ⊤ ≤ t ⁻¹ᵁ (L.pull φ).U j), t ≫ φ = t ≫ φ ≫ A.hom ≫ eSec A → (t.appLE ((L.pull φ).U j) ⊤ h).hom (s.f j) = 0) → Out.KTriv A L := by
  intro S A _ L θ hL hθ hs R _ t x hx
  have one : ∀ (T : Over S) (y : T ⟶ A), y.left ≫ A.hom ≫ eSec A = (1 : T ⟶ A).left := fun T y => by
    rw [← Category.assoc, Over.w y]; rfl
  have H' : ∀ (R' : CommRingCat.{0}) (t' : Spec R' ⟶ S) (y : Over.mk t' ⟶ A) (i i₀ : L.ι),
      ⊤ ≤ y.left ⁻¹ᵁ L.U i → ⊤ ≤ (1 : Over.mk t' ⟶ A).left ⁻¹ᵁ L.U i₀ →
      (∃ c : LB.Gen (Out.translDiff A L y), c.IsGen) → y = 1 := by
    rintro R' t' y i i₀ hi hi₀ ⟨c, hc⟩
    by_contra hne
    have hne' : y.left ≠ (1 : Over.mk t' ⟶ A).left := fun e => hne (Over.OverMorphism.ext e)
    obtain ⟨s, hs'⟩ := exists_sec_of_gen_diff hL θ _ _ c hc
    let r : Over.mk t' ⟶ Over.mk t' ⊗ A := lift (𝟙 _) 1
    have r₁ : r.left ≫ (lift (fst _ A ≫ y) (snd _ A) ≫ μ[A]).left = y.left := by
      rw [← Over.comp_left, comp_lift_assoc, lift_fst_assoc, lift_snd, Category.id_comp]
      exact congrArg (fun q : Over.mk t' ⟶ A => q.left) (_root_.mul_one y)
    have r₂ : r.left ≫ (snd _ A).left = (1 : Over.mk t' ⟶ A).left := by
      rw [← Over.comp_left, lift_snd]
    have hj : ⊤ ≤ r.left ⁻¹ᵁ (L.pull (snd (Over.mk t') A).left).U (fun _ => i₀) := fun z _ =>
      Set.mem_iInter.2 fun _ => (congrArg (fun q => q z ∈ L.U i₀) r₂).mpr (hi₀ trivial)
    have hz := hs R' t' _ (snd (Over.mk t') A).left (fst (Over.mk t') A).left
      (IsPullback.of_hasPullback t' A.hom).flip s _ r.left (fun _ => i₀) hj
      (by rw [← Category.assoc, r₂, one])
    refine hne' (((hθ _ y.left i hi).1 ((appLE_top_eq_zero_iff_gs _ _ hi _).2 fun z => ?_)).trans (one _ y))
    obtain ⟨J, hJ, e⟩ := exists_good L hL z (K := Bool)
      (fun b => cond b y.left (1 : Over.mk t' ⟶ A).left) (fun b => cond b i i₀) (by
        rintro (_ | _) (_ | _) e
        exacts [rfl, absurd e.symm hne', absurd e hne', rfl]) (by
        rintro (_ | _)
        exacts [hi₀ trivial, hi trivial])
    have := hs' _ r.left z J hJ ((sval_of s r.left z J (fun _ => i₀) (fun _ => by rw [r₂]; exact e false)).trans
      ((appLE_top_eq_zero_iff_gs _ _ hj _).1 hz z))
    rw [r₁] at this
    obtain rfl : J y.left = i := e true
    exact this
  change x = 1
  apply Over.OverMorphism.ext
  refine Scheme.hom_ext_of_forall _ _ fun p => ?_
  obtain ⟨V, hp, c, hc⟩ := hx p
  obtain ⟨i, hi⟩ := exists_chart hL (x.left p)
  obtain ⟨i₀, hi₀⟩ := exists_chart hL ((1 : Over.mk t ⟶ A).left p)
  obtain ⟨U, hU, hpU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (U := V ⊓ x.left ⁻¹ᵁ L.U i ⊓ (1 : Over.mk t ⟶ A).left ⁻¹ᵁ L.U i₀) (x := p) ⟨⟨hp, hi⟩, hi₀⟩
  refine ⟨U, hpU, ?_⟩
  let g : Over.mk (hU.fromSpec ≫ t) ⟶ Over.mk t := Over.homMk hU.fromSpec rfl
  have hq := fun q => hUV (hU.range_fromSpec.le ⟨q, rfl⟩)
  have h1 : g ≫ x = g ≫ 1 := by
    rw [MonObj.comp_one]
    refine H' _ _ _ i i₀ (fun q _ => (hq q).1.2) ?_ (exists_isGen_translDiff_comp A L x g V
      (fun q => (hq q).1.1) c hc)
    rw [← MonObj.comp_one g]
    exact fun q _ => (hq q).2
  have h2 : hU.fromSpec ≫ x.left = hU.fromSpec ≫ (1 : Over.mk t ⟶ A).left :=
    congrArg (·.left) h1
  rw [IsAffineOpen.fromSpec, Category.assoc, Category.assoc, cancel_epi] at h2
  exact h2

end GlobalTheory
