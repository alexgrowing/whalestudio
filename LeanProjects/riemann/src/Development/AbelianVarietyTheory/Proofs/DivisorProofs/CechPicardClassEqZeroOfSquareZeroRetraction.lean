import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.CechPic

theorem squareZero_localUnit_difference_ring_identity {R : Type*} [CommRing R] {Tj Tk Nj Nk H G G' Sj Sk Pj Pk Pj' Pk' M : R}
    (hT : Tj = G' * Tk) (hS : Sj = G * G * Sk) (hP : Pj = G' * G' * Pk) (hj' : Pj * Pj' = 1)
    (hk' : Pk * Pk' = 1) (hNj : Nj = Sj * Pj' - 1) (hNk : Nk = Sk * Pk' - 1) (hNj2 : Nj * Nj = 0)
    (hNk2 : Nk * Nk = 0) (hH : 2 * H = 1)
    (hM : M = Tj * (1 + Nj * H) - G * (Tk * (1 + Nk * H))) (hM2 : M * M = 0) :
    M * (G * (Tk * (1 + Nk * H))) = 0 := by
  have e1 : (Tj * (1 + Nj * H)) ^ 2 = Tj ^ 2 * Sj * Pj' := by
    linear_combination Tj ^ 2 * Nj * hH + Tj ^ 2 * H ^ 2 * hNj2 + Tj ^ 2 * hNj
  have e2 : (G * (Tk * (1 + Nk * H))) ^ 2 = G ^ 2 * Tk ^ 2 * Sk * Pk' := by
    linear_combination G ^ 2 * Tk ^ 2 * Nk * hH + G ^ 2 * Tk ^ 2 * H ^ 2 * hNk2 + G ^ 2 * Tk ^ 2 * hNk
  have e4 : Pj' * (G' * G') = Pk' := by
    linear_combination (-(Pj' * (G' * G'))) * hk' + Pk' * hj' - Pk' * Pj' * hP
  have e5 : (Tj * (1 + Nj * H)) ^ 2 = (G * (Tk * (1 + Nk * H))) ^ 2 := by
    rw [e1, e2, hT, hS]
    linear_combination G ^ 2 * Tk ^ 2 * Sk * e4
  linear_combination H * e5 - H * hM2 +
    H * (Tj * (1 + Nj * H) + G * (Tk * (1 + Nk * H)) + M) * hM - M * (G * (Tk * (1 + Nk * H))) * hH

end GlobalTheory.CechPic

open GlobalTheory.SmallExtLift in

theorem GlobalTheory.CechPic.eq_zero_of_sqZero_retract : ∀ {X X' : Scheme.{0}} (i : X ⟶ X') (q : X' ⟶ X), i ≫ q = 𝟙 X → (∀ x, i (q x) = x) → IsUnit (2 : Γ(X', ⊤)) → (∀ (W : X'.Opens) (f g : Γ(X', W)), (i.app W).hom f = 0 → (i.app W).hom g = 0 → f * g = 0) → ∀ (c : GlobalTheory.CechPic.Pic X'), GlobalTheory.CechPic.pull i c = 0 → 2 • c = 0 → c = 0 := by
  intro X X' i q e hiq h2 hsq c hc hc2
  obtain ⟨Q, hQ, rfl⟩ := GlobalTheory.CechPic.cls_surj c
  rw [two_nsmul, ← GlobalTheory.CechPic.cls_tens hQ hQ (GlobalTheory.CechPic.isLB_tens hQ hQ),
    GlobalTheory.CechPic.cls_eq_zero_iff] at hc2
  obtain ⟨s, hs⟩ := hc2
  rw [← GlobalTheory.CechPic.cls_pull hQ i (pull_isLB hQ i), GlobalTheory.CechPic.cls_eq_zero_iff] at hc
  obtain ⟨t₀, ht₀⟩ := hc
  refine (GlobalTheory.CechPic.cls_eq_zero_iff hQ).2 ?_

  have genLaw : ∀ {M : LB X'} (t : LB.Gen M), t.IsGen → ∀ {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z)
      (a b : M.ι) (ha : f z ∈ M.U a) (hb : f z ∈ M.U b),
      gr f z _ ha (t.s a).val = gr f z (M.U a ⊓ M.U b) ⟨ha, hb⟩ (M.g a b).val * gr f z _ hb (t.s b).val := by
    intro M t ht Z f z a b ha hb
    have hm : f z ∈ M.U a ⊓ M.U b := ⟨ha, hb⟩
    have := congrArg (fun u => gr f z _ hm u.val) (ht a b)
    simp only [Units.val_mul, map_mul] at this
    exact (gr_res f z _ hm _).symm.trans (this.trans (congrArg₂ (· * ·) rfl (gr_res f z _ hm _)))
  let W : Q.ι → X.Opens := fun j => (Q.pull i).U (fun _ => j)
  have hσ : ∀ j, Q.U j ≤ (q ≫ i) ⁻¹ᵁ Q.U j := fun j x hx => by
    simp only [Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply, hiq]; exact hx
  have hW : ∀ j, Q.U j ≤ q ⁻¹ᵁ W j := fun j x hx => pull_le Q i j le_rfl (hσ j hx)
  have hσf : ∀ j {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z), f z ∈ Q.U j → ((f ≫ q) ≫ i) z ∈ Q.U j := by
    intro j Z f z hz
    simp only [Scheme.Hom.comp_apply, hiq]; exact hz
  have hWf : ∀ j {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z), f z ∈ Q.U j → (f ≫ q) z ∈ W j :=
    fun j Z f z hz => hW j hz
  let sj : ∀ j, Γ(X', Q.U j)ˣ := fun j => res (le_inf le_rfl le_rfl) (s.s (j, j))
  let u : ∀ j, Γ(X', Q.U j) := fun j => (q.appLE (W j) (Q.U j) (hW j)).hom (t₀.s fun _ => j).val
  let σi : ∀ j, Γ(X', Q.U j) := fun j => ((q ≫ i).appLE (Q.U j) (Q.U j) (hσ j)).hom (sj j)⁻¹.val
  let n : ∀ j, Γ(X', Q.U j) := fun j => (sj j).val * σi j - 1
  let hh : ∀ j, Γ(X', Q.U j) := fun j => (X'.presheaf.map (homOfLE le_top).op).hom h2.unit⁻¹.val
  let t : ∀ j, Γ(X', Q.U j) := fun j => u j * (1 + n j * hh j)
  have gn : ∀ {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z) j (hz : f z ∈ Q.U j),
      gr f z _ hz (n j) = gr f z _ hz (sj j).val * gr ((f ≫ q) ≫ i) z (Q.U j) (hσf j f z hz) (sj j)⁻¹.val - 1 := by
    intro Z f z j hz
    simp only [n, σi, map_sub, map_mul, map_one]
    rw [gr_appLE]
    exact congrArg (fun w => _ * w - 1) (gr_congr (Category.assoc f q i).symm z _ _ _)
  have gt : ∀ {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z) j (hz : f z ∈ Q.U j),
      gr f z _ hz (t j) = gr (f ≫ q) z (W j) (hWf j f z hz) (t₀.s fun _ => j).val *
        (1 + gr f z _ hz (n j) * gr f z ⊤ trivial h2.unit⁻¹.val) := by
    intro Z f z j hz
    simp only [t, u, hh, map_mul, map_add, map_one]
    rw [gr_appLE, gr_res]
  have E1 : (𝟙 X ≫ i) ≫ q = 𝟙 X := by rw [Category.assoc, e, Category.id_comp]
  have E2 : ((𝟙 X ≫ i) ≫ q) ≫ i = 𝟙 X ≫ i := by rw [E1]
  have hn0 : ∀ j, (i.app (Q.U j)).hom (n j) = 0 := fun j => gr_ext fun y hy => by
    rw [gr_app, map_zero, gn (𝟙 X ≫ i) y j hy, gr_congr E2 y _ (hσf j _ y hy), ← map_mul, Units.mul_inv,
      map_one, sub_self]
  have hn2 : ∀ j, n j * n j = 0 := fun j => hsq _ _ _ (hn0 j) (hn0 j)
  have gti : ∀ j y (hy : (𝟙 X ≫ i) y ∈ Q.U j),
      gr (𝟙 X ≫ i) y _ hy (t j) = gr ((𝟙 X ≫ i) ≫ q) y (W j) (hWf j _ y hy) (t₀.s fun _ => j).val := by
    intro j y hy
    rw [gt (𝟙 X ≫ i) y j hy, gn (𝟙 X ≫ i) y j hy, gr_congr E2 y _ (hσf j _ y hy), ← map_mul, Units.mul_inv, map_one, sub_self, zero_mul,
      add_zero, mul_one]
  let m : ∀ j k, Γ(X', Q.U j ⊓ Q.U k) := fun j k =>
    (X'.presheaf.map (homOfLE inf_le_left).op).hom (t j) -
      (Q.g j k).val * (X'.presheaf.map (homOfLE inf_le_right).op).hom (t k)
  have gm' : ∀ {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z) j k (hz : f z ∈ Q.U j ⊓ Q.U k),
      gr f z _ hz (m j k) = gr f z _ hz.1 (t j) - gr f z _ hz (Q.g j k).val * gr f z _ hz.2 (t k) := by
    intro Z f z j k hz
    simp only [m, map_sub, map_mul]
    rw [gr_res, gr_res]
  have hm0 : ∀ j k, (i.app _).hom (m j k) = 0 := fun j k => gr_ext fun y hy => by
    rw [gr_app, map_zero, gm' (𝟙 X ≫ i) y j k hy, gti j y hy.1, gti k y hy.2, sub_eq_zero]
    have := gr_gen ht₀ ((𝟙 X ≫ i) ≫ q) y (hσf j _ y hy.1) (hσf k _ y hy.2)
    exact this.trans (congrArg (· * _) (gr_congr E2 y _ _ _))
  have gS : ∀ {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z) a b (ha : f z ∈ Q.U a) (hb : f z ∈ Q.U b),
      gr f z _ ha (sj a).val = gr f z (Q.U a ⊓ Q.U b) ⟨ha, hb⟩ (Q.g a b).val *
        gr f z (Q.U a ⊓ Q.U b) ⟨ha, hb⟩ (Q.g a b).val * gr f z _ hb (sj b).val := by
    intro Z f z a b ha hb
    have hS := genLaw s hs f z (a, a) (b, b) ⟨ha, ha⟩ ⟨hb, hb⟩
    have hm : f z ∈ (Q.U a ⊓ Q.U a) ⊓ (Q.U b ⊓ Q.U b) := ⟨⟨ha, ha⟩, ⟨hb, hb⟩⟩
    have hg : gr f z _ hm ((GlobalTheory.CechPic.tens Q Q).g (a, a) (b, b)).val =
        gr f z (Q.U a ⊓ Q.U b) ⟨ha, hb⟩ (Q.g a b).val * gr f z (Q.U a ⊓ Q.U b) ⟨ha, hb⟩ (Q.g a b).val := by
      show gr f z _ hm (res _ (Q.g a b) * res _ (Q.g a b)).val = _
      rw [Units.val_mul, map_mul]
      exact congrArg₂ (· * ·) (gr_res f z _ hm _) (gr_res f z _ hm _)
    refine (gr_res f z (le_inf le_rfl le_rfl : Q.U a ≤ Q.U a ⊓ Q.U a) ha (s.s (a, a)).val).trans (hS.trans ?_)
    exact congrArg₂ (· * ·) hg (gr_res f z (le_inf le_rfl le_rfl : Q.U b ≤ Q.U b ⊓ Q.U b) hb (s.s (b, b)).val).symm
  refine gen_of_refine hQ Q.U hQ.cover id (fun _ => le_rfl) t
    (fun j => ((Units.isUnit _).map _).mul (isUnit_one_add (hn2 j) _)) fun a b x ha hb => ?_
  have hab : (𝟙 X') x ∈ Q.U a ⊓ Q.U b := ⟨ha, hb⟩
  have hmx := gm' (𝟙 X') x a b hab
  have hm := hmx
  rw [gt (𝟙 X') x a ha, gt (𝟙 X') x b hb] at hm
  have hmm := congrArg (gr (𝟙 X') x _ hab) (hsq _ _ _ (hm0 a b) (hm0 a b))
  rw [map_mul, map_zero] at hmm
  have hT := gr_gen ht₀ (𝟙 X' ≫ q) x (hσf a _ x ha) (hσf b _ x hb)
  have hSx := gS (𝟙 X') x a b ha hb
  have hPx := gS ((𝟙 X' ≫ q) ≫ i) x a b (hσf a _ x ha) (hσf b _ x hb)
  have hj' : gr ((𝟙 X' ≫ q) ≫ i) x _ (hσf a _ x ha) (sj a).val * gr ((𝟙 X' ≫ q) ≫ i) x _ (hσf a _ x ha) (sj a)⁻¹.val = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hk' : gr ((𝟙 X' ≫ q) ≫ i) x _ (hσf b _ x hb) (sj b).val * gr ((𝟙 X' ≫ q) ≫ i) x _ (hσf b _ x hb) (sj b)⁻¹.val = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hNa := gn (𝟙 X') x a ha
  have hNb := gn (𝟙 X') x b hb
  have hNa2 := congrArg (gr (𝟙 X') x _ ha) (hn2 a)
  have hNb2 := congrArg (gr (𝟙 X') x _ hb) (hn2 b)
  rw [map_mul, map_zero] at hNa2 hNb2
  have hH : 2 * gr (𝟙 X') x ⊤ trivial h2.unit⁻¹.val = 1 := by
    have := congrArg (gr (𝟙 X') x ⊤ trivial) h2.val_inv_mul
    rw [map_mul, map_one, map_ofNat] at this
    linear_combination this
  have key := GlobalTheory.CechPic.squareZero_localUnit_difference_ring_identity hT hSx hPx hj' hk' hNa hNb hNa2 hNb2 hH hm hmm
  have hB := ((Units.isUnit (Q.g a b)).map (gr (𝟙 X') x (Q.U a ⊓ Q.U b) hab)).mul
    (((Units.isUnit (t₀.s fun _ => b)).map (gr (𝟙 X' ≫ q) x (W b) (hWf b _ x hb))).mul (isUnit_one_add hNb2 (gr (𝟙 X') x ⊤ trivial h2.unit⁻¹.val)))
  have h0 := hB.mul_left_eq_zero.1 key
  rw [hmx] at h0
  exact sub_eq_zero.1 h0
