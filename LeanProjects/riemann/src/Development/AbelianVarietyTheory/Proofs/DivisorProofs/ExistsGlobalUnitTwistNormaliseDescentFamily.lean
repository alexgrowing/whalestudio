import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DescNormU

theorem germ_comp {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens)
    (h : q (r z) ∈ U) (a : Γ(X, U)ˣ) :
    gm (r ≫ q) z U a = Units.map (r.stalkMap z).hom.toMonoidHom (gm q (r z) U a) := by
  apply Units.ext
  rw [gm_val (r ≫ q) z U h]
  show _ = (r.stalkMap z).hom (gm q (r z) U a).val
  rw [gm_val q (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r (q ⁻¹ᵁ U) z h _).symm

variable {S : Scheme.{0}} {A A' B : Over S} [GrpObj A] [GrpObj B]

theorem zb_zb : zb A B ≫ zb A B = zb A B := by ext <;> simp [zb]
theorem zb_fst' : zb A B ≫ fst A B = fst A B := by simp [zb]
theorem fst_comp_lift_id_one_eq_prodSetSecondCoordZero : fst A B ≫ lift (𝟙 A) (1 : A ⟶ B) = zb A B := by ext <;> simp [zb]

theorem rhoZ_rhoZ (q : A ⟶ A') : rhoZ (B := B) q ≫ rhoZ q = rhoZ q := by
  have e : (zb A B).left ≫ (zb A B).left = (zb A B).left := by rw [← Over.comp_left, zb_zb]
  apply pullback.hom_ext <;> simp [e]

theorem rhoZ_a (q : A ⟶ A') : rhoZ (B := B) q ≫ pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left =
    pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left := by
  rw [rhoZ_fst_assoc, ← Over.comp_left, zb_fst']

theorem rhoZ_a' (q : A ⟶ A') : rhoZ (B := B) q ≫ pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left =
    pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left := by
  rw [rhoZ_snd_assoc, ← Over.comp_left, zb_fst']

theorem a_s (q : A ⟶ A') : (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) ≫ (lift (𝟙 A) (1 : A ⟶ B)).left =
    rhoZ q ≫ pullback.fst (q ▷ B).left (q ▷ B).left := by
  rw [rhoZ_fst, Category.assoc, ← Over.comp_left, fst_comp_lift_id_one_eq_prodSetSecondCoordZero]

theorem pullbackSnd_fst_comp_lift_id_one (q : A ⟶ A') : (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) ≫ (lift (𝟙 A) (1 : A ⟶ B)).left =
    rhoZ q ≫ pullback.snd (q ▷ B).left (q ▷ B).left := by
  rw [rhoZ_snd, Category.assoc, ← Over.comp_left, fst_comp_lift_id_one_eq_prodSetSecondCoordZero]

end GlobalTheory.DescNormU

namespace GlobalTheory.DescNormU

theorem germ_gen {X X' Y : Scheme.{0}} {L : LB X} {F : X' ⟶ X} (τ : LB.Gen (L.pull F)) (hτ : τ.IsGen)
    (g : Y ⟶ X') (y : Y) (i i' : L.ι) (hi : F (g y) ∈ L.U i) (hi' : F (g y) ∈ L.U i') :
    gm g y _ (τ.s fun _ => i) = gm (g ≫ F) y _ (L.g i i') * gm g y _ (τ.s fun _ => i') := by
  have hp : g y ∈ (L.pull F).U (fun _ => i) ⊓ (L.pull F).U (fun _ => i') := ⟨mem_pull.2 hi, mem_pull.2 hi'⟩
  have e : gm g y ((L.pull F).U (fun _ => i) ⊓ (L.pull F).U (fun _ => i')) ((L.pull F).g (fun _ => i) (fun _ => i')) =
      gm (g ≫ F) y _ (L.g i i') := by
    show gm g y _ (∏ _k : PUnit, (res _ (pullU F _ (L.g i i'))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res g y _ hp _).trans (gm_pull g F y (L.U i ⊓ L.U i') ⟨hi, hi'⟩ _)
  have := congrArg (gm g y ((L.pull F).U (fun _ => i) ⊓ (L.pull F).U (fun _ => i'))) (hτ (fun _ => i) (fun _ => i'))
  rw [map_mul, gm_res g y _ hp, gm_res g y _ hp, e] at this
  exact this

end GlobalTheory.DescNormU

namespace GlobalTheory.DescNormU

theorem pt_eq {X Y Z : Scheme.{0}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (e : f ≫ g = h) (x : X) : g (f x) = h x := by
  rw [← e]; rfl

theorem rhoZ_rhoZ_apply {S : Scheme.{0}} {A A' B : Over S} [GrpObj A] [GrpObj B] (q : A ⟶ A') (z) :
    rhoZ (B := B) q (rhoZ q z) = rhoZ q z := pt_eq (rhoZ_rhoZ q) z

set_option maxHeartbeats 800000 in

theorem normalise : ∀ (K : Type) [Field K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left) (τ : LB.Gen (ev P (𝟙 A) (1 : A ⟶ B))), P.IsLB → τ.IsGen → ∀ φ : ∀ i j, Γ(pullback (q ▷ B).left (q ▷ B).left, chart (q ▷ B).left P i j)ˣ, DescCompat (q ▷ B).left P φ → ∃ u : Γ(pullback (q ▷ B).left (q ▷ B).left, ⊤)ˣ, NormAlong q P τ (GlobalTheory.DescNorm.twist (q ▷ B).left P φ u) := by
  intro K _ A A' B _ _ q P τ hP hτ φ hφ
  let W : P.ι × P.ι → (pullback (q ▷ B).left (q ▷ B).left).Opens := fun p => rhoZ q ⁻¹ᵁ chart (q ▷ B).left P p.1 p.2
  have h2 : ∀ p, W p ≤ (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) ⁻¹ᵁ
      (P.pull (lift (𝟙 A) (1 : A ⟶ B)).left).U (fun _ => p.1) := fun p z hz =>
    mem_pull.2 (by rw [pt_eq (a_s q) z]; exact hz.1)
  have h3 : ∀ p, W p ≤ (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) ⁻¹ᵁ
      (P.pull (lift (𝟙 A) (1 : A ⟶ B)).left).U (fun _ => p.2) := fun p z hz =>
    mem_pull.2 (by rw [pt_eq (pullbackSnd_fst_comp_lift_id_one q) z]; exact hz.2)
  let v : ∀ p, Γ(pullback (q ▷ B).left (q ▷ B).left, W p)ˣ := fun p =>
    (pullU (rhoZ q) _ (φ p.1 p.2))⁻¹ *
      (res (h2 p) (pullU (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) _ (τ.s fun _ => p.1)))⁻¹ *
      res (h3 p) (pullU (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) _ (τ.s fun _ => p.2))
  have hv : ∀ (Y : Scheme.{0}) (g : Y ⟶ pullback (q ▷ B).left (q ▷ B).left) (y : Y) (p : P.ι × P.ι), g y ∈ W p →
      gm g y (W p) (v p) = (gm (g ≫ rhoZ q) y _ (φ p.1 p.2))⁻¹ *
        (gm (g ≫ pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) y _ (τ.s fun _ => p.1))⁻¹ *
        gm (g ≫ pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) y _ (τ.s fun _ => p.2) := by
    intro Y g y p hy
    simp only [v, map_mul, map_inv]
    rw [gm_pull g (rhoZ q) y _ hy, gm_res g y (h2 p) hy, gm_pull g (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) y _ (h2 p hy),
      gm_res g y (h3 p) hy, gm_pull g (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) y _ (h3 p hy)]

  have indep : ∀ p p', ∀ z ∈ W p ⊓ W p', gm (𝟙 _) z (W p) (v p) = gm (𝟙 _) z (W p') (v p') := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ z ⟨hz, hz'⟩
    rw [hv _ (𝟙 _) z _ hz, hv _ (𝟙 _) z _ hz']
    simp only [Category.id_comp]
    have hz1 : pullback.fst (q ▷ B).left (q ▷ B).left (rhoZ q z) ∈ P.U i := hz.1
    have hz2 : pullback.snd (q ▷ B).left (q ▷ B).left (rhoZ q z) ∈ P.U j := hz.2
    have hz1' : pullback.fst (q ▷ B).left (q ▷ B).left (rhoZ q z) ∈ P.U i' := hz'.1
    have hz2' : pullback.snd (q ▷ B).left (q ▷ B).left (rhoZ q z) ∈ P.U j' := hz'.2
    have c1 : gm (rhoZ q) z _ (φ i' j') = gm (rhoZ q ≫ pullback.fst (q ▷ B).left (q ▷ B).left) z _ (P.g i i') *
        gm (rhoZ q) z _ (φ i j) * gm (rhoZ q ≫ pullback.snd (q ▷ B).left (q ▷ B).left) z _ (P.g j' j) := by
      have e := congrArg (Units.map ((rhoZ q).stalkMap z).hom.toMonoidHom) (hφ (rhoZ q z) i i' j j' hz1 hz1' hz2 hz2')
      rw [map_mul, map_mul] at e
      have k1 := germ_comp (rhoZ q) (𝟙 _) z (chart (q ▷ B).left P i' j') ⟨hz1', hz2'⟩ (φ i' j')
      have k2 := germ_comp (rhoZ q) (𝟙 _) z (chart (q ▷ B).left P i j) ⟨hz1, hz2⟩ (φ i j)
      have k3 := germ_comp (rhoZ q) (pullback.fst (q ▷ B).left (q ▷ B).left) z (P.U i ⊓ P.U i') ⟨hz1, hz1'⟩ (P.g i i')
      have k4 := germ_comp (rhoZ q) (pullback.snd (q ▷ B).left (q ▷ B).left) z (P.U j' ⊓ P.U j) ⟨hz2', hz2⟩ (P.g j' j)
      rw [Category.comp_id] at k1 k2
      rw [k1, k2, k3, k4]
      exact e
    have t1 := germ_gen τ hτ (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) z i i'
      (by rw [pt_eq (a_s q) z]; exact hz1) (by rw [pt_eq (a_s q) z]; exact hz1')
    have t2 := germ_gen τ hτ (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) z j j'
      (by rw [pt_eq (pullbackSnd_fst_comp_lift_id_one q) z]; exact hz2) (by rw [pt_eq (pullbackSnd_fst_comp_lift_id_one q) z]; exact hz2')
    rw [a_s] at t1
    rw [pullbackSnd_fst_comp_lift_id_one] at t2
    have cc := gm_cocycle hP (rhoZ q ≫ pullback.snd (q ▷ B).left (q ▷ B).left) z hz2 hz2' hz2
    rw [gm_self hP _ z hz2] at cc
    rw [c1, t1, t2]
    generalize gm (rhoZ q) z _ (φ i j) = Φ
    generalize gm (rhoZ q ≫ pullback.fst (q ▷ B).left (q ▷ B).left) z _ (P.g i i') = G₁
    generalize gm (rhoZ q ≫ pullback.snd (q ▷ B).left (q ▷ B).left) z _ (P.g j' j) = G₂ at cc ⊢
    generalize gm (rhoZ q ≫ pullback.snd (q ▷ B).left (q ▷ B).left) z _ (P.g j j') = H at cc ⊢
    generalize gm (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) z _ (τ.s fun _ => i') = T₁
    generalize gm (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) z _ (τ.s fun _ => j') = T₂
    rw [eq_inv_of_mul_eq_one_left cc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have hc : (⊤ : (pullback (q ▷ B).left (q ▷ B).left).Opens) ≤ iSup W := fun z _ => by
    obtain ⟨i, hi⟩ := exists_chart hP (pullback.fst (q ▷ B).left (q ▷ B).left (rhoZ q z))
    obtain ⟨j, hj⟩ := exists_chart hP (pullback.snd (q ▷ B).left (q ▷ B).left (rhoZ q z))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), ⟨hi, hj⟩⟩
  obtain ⟨u, hu⟩ := glue_unit ⊤ W (fun _ => le_top) hc v indep
  refine ⟨u, fun T r t i j hi hj => ?_⟩
  have hm : (r ≫ rhoZ q) t ∈ chart (q ▷ B).left P i j := ⟨hi, hj⟩
  have hw : (r ≫ rhoZ q) t ∈ W (i, j) := by
    show rhoZ q (rhoZ q (r t)) ∈ chart (q ▷ B).left P i j
    rw [rhoZ_rhoZ_apply]; exact hm
  show gm _ t _ (φ i j * res le_top u) = _
  rw [map_mul, gm_res _ t le_top hm, ← gm_res _ t (le_top : W (i, j) ≤ ⊤) hw u, hu (i, j), hv T (r ≫ rhoZ q) t (i, j) hw]
  simp only [Category.assoc, rhoZ_rhoZ, rhoZ_a, rhoZ_a']
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, _root_.mul_inv_cancel, _root_.one_mul]

end GlobalTheory.DescNormU
