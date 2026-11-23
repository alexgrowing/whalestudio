import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.AbLaw
namespace H1Iso
variable {X Y Z : Scheme.{0}}

def pb (f : Y ⟶ X) {U : X.Opens} {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U) : Γ(X, U) →+* Γ(Y, W) :=
  (f.appLE U W h).hom

theorem le_pre (f : Y ⟶ X) {U U' : X.Opens} {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U) (h' : U ≤ U') :
    W ≤ f ⁻¹ᵁ U' := fun _ hy => h' (h hy)

theorem le_pre_inf (f : Y ⟶ X) {U U' : X.Opens} {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U) (h' : W ≤ f ⁻¹ᵁ U') :
    W ≤ f ⁻¹ᵁ (U ⊓ U') := fun _ hy => ⟨h hy, h' hy⟩

theorem rs_pb (f : Y ⟶ X) {U : X.Opens} {W W' : Y.Opens} (h : W ≤ f ⁻¹ᵁ U) (h' : W' ≤ W)
    (x : Γ(X, U)) : rs Y h' (pb f h x) = pb f (h'.trans h) x := by
  change (f.appLE U W h ≫ Y.presheaf.map (homOfLE h').op).hom x = _
  rw [Scheme.Hom.appLE_map]
  rfl

theorem pb_rs (f : Y ⟶ X) {U U' : X.Opens} {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U) (h' : U ≤ U')
    (x : Γ(X, U')) : pb f h (rs X h' x) = pb f (le_pre f h h') x := by
  change (X.presheaf.map (homOfLE h').op ≫ f.appLE U W h).hom x = _
  rw [Scheme.Hom.map_appLE]
  rfl

theorem pb_of_eq_id (g : X ⟶ X) (hg : g = 𝟙 X) {U W : X.Opens} (h : W ≤ g ⁻¹ᵁ U) (h' : W ≤ U)
    (x : Γ(X, U)) : pb g h x = rs X h' x := by
  subst hg
  change (𝟙 _ ≫ X.presheaf.map (homOfLE h').op).hom x = _
  rw [Category.id_comp]

theorem le_of_comp_id {f : X ⟶ Y} {e : Y ⟶ X} (hfe : f ≫ e = 𝟙 X) {U W : X.Opens} {V : Y.Opens}
    (h : W ≤ f ⁻¹ᵁ V) (h' : V ≤ e ⁻¹ᵁ U) : W ≤ U := by
  have : W ≤ (f ≫ e) ⁻¹ᵁ U := fun _ hy => h' (h hy)
  rw [hfe] at this
  exact this

theorem pb_pb {f : X ⟶ Y} {e : Y ⟶ X} (hfe : f ≫ e = 𝟙 X) {U W : X.Opens} {V : Y.Opens}
    (h : W ≤ f ⁻¹ᵁ V) (h' : V ≤ e ⁻¹ᵁ U) (x : Γ(X, U)) :
    pb f h (pb e h' x) = rs X (le_of_comp_id hfe h h') x := by
  change (e.appLE U V h' ≫ f.appLE V W h).hom x = _
  rw [Scheme.Hom.appLE_comp_appLE]
  exact pb_of_eq_id (f ≫ e) hfe _ _ x

theorem pull_U_le (M : LB X) (e : Y ⟶ X) (j : (M.pull e).ι) :
    (M.pull e).U j ≤ e ⁻¹ᵁ M.U (j PUnit.unit) := LB.wchart_le M (fun _ : PUnit => e) j PUnit.unit

theorem pull_g (M : LB X) (e : Y ⟶ X) (j j' : (M.pull e).ι) :
    ((M.pull e).g j j').val =
      pb e (le_pre_inf e (inf_le_left.trans (pull_U_le M e j)) (inf_le_right.trans (pull_U_le M e j')) :
        (M.pull e).U j ⊓ (M.pull e).U j' ≤ e ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit)))
        (M.g (j PUnit.unit) (j' PUnit.unit)).val := by
  change ((∏ k : PUnit, _ : Γ(Y, _)ˣ)).val = _
  rw [Fintype.prod_unique, zpow_one]
  rfl

theorem firstCohomologyVanishes_pull_of_isIso (e : Y ⟶ X) [IsIso e] (M : LB X) (hM : FirstCohomologyVanishes M) : FirstCohomologyVanishes (M.pull e) := by
  intro I V c hV hc φ hφ
  have h1 : inv e ≫ e = 𝟙 X := IsIso.inv_hom_id e
  have h2 : e ≫ inv e = 𝟙 Y := IsIso.hom_inv_id e
  have hV' : ∀ a, inv e ⁻¹ᵁ V a ≤ M.U (c a PUnit.unit) := fun a =>
    le_of_comp_id h1 le_rfl ((hV a).trans (pull_U_le M e (c a)))
  have hb : ∀ a, V a ≤ e ⁻¹ᵁ (inv e ⁻¹ᵁ V a) := fun a => by
    have : V a ≤ (e ≫ inv e) ⁻¹ᵁ V a := by rw [h2]; exact le_rfl
    exact this
  have hc' : ⨆ a, inv e ⁻¹ᵁ V a = ⊤ := by
    apply top_unique
    intro x _
    have hx : (inv e).base x ∈ ⨆ a, V a := by rw [hc]; trivial
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, ha⟩
  obtain ⟨ψ, hψ⟩ := hM I (fun a => inv e ⁻¹ᵁ V a) (fun a => c a PUnit.unit) hV' hc'
    (fun a b => pb (inv e) (le_pre_inf _ inf_le_left inf_le_right : inv e ⁻¹ᵁ V a ⊓ inv e ⁻¹ᵁ V b ≤ inv e ⁻¹ᵁ (V a ⊓ V b)) (φ a b))
    (fun a b d => by
      have h := congrArg (pb (inv e) (le_pre_inf _ (le_pre_inf _ (inf_le_left.trans inf_le_left)
        (inf_le_left.trans inf_le_right)) inf_le_right : inv e ⁻¹ᵁ V a ⊓ inv e ⁻¹ᵁ V b ⊓ inv e ⁻¹ᵁ V d ≤
        inv e ⁻¹ᵁ (V a ⊓ V b ⊓ V d))) (hφ a b d)
      simp only [map_add, map_mul, pull_g, rs_pb, pb_rs, pb_pb h1] at h
      simp only [rs_pb]
      exact h)
  refine ⟨fun a => pb e (hb a) (ψ a), fun a b => ?_⟩
  have h := congrArg (pb e (le_pre_inf e (inf_le_left.trans (hb a)) (inf_le_right.trans (hb b)) :
    V a ⊓ V b ≤ e ⁻¹ᵁ (inv e ⁻¹ᵁ V a ⊓ inv e ⁻¹ᵁ V b))) (hψ a b)
  simp only [map_sub, map_mul, pb_rs, pb_pb h2, rs_self] at h
  simp only [pull_g, rs_pb]
  exact h

def wu {N M : LB X} (w : LB.Iso M N) (i : N.ι) (k : M.ι) : Γ(X, N.U i ⊓ M.U k)ˣ := w.s (i, k)

theorem val_res {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) : (res h u).val = rs X h u.val := rfl

theorem iso_rel {N M : LB X} (w : LB.Iso M N) (hw : w.IsGen) (i j : N.ι) (k l : M.ι) {W : X.Opens}
    (hi : W ≤ N.U i) (hj : W ≤ N.U j) (hk : W ≤ M.U k) (hl : W ≤ M.U l) :
    rs X (le_inf hi hk : W ≤ N.U i ⊓ M.U k) (wu w i k).val *
        rs X (le_inf hk hl : W ≤ M.U k ⊓ M.U l) (M.g k l).val =
      rs X (le_inf hi hj : W ≤ N.U i ⊓ N.U j) (N.g i j).val *
        rs X (le_inf hj hl : W ≤ N.U j ⊓ M.U l) (wu w j l).val := by
  have h : res (inf_le_left : N.U i ⊓ M.U k ⊓ (N.U j ⊓ M.U l) ≤ N.U i ⊓ M.U k) (wu w i k) =
      (res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        N.U i ⊓ M.U k ⊓ (N.U j ⊓ M.U l) ≤ N.U i ⊓ N.U j) (N.g i j) *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        N.U i ⊓ M.U k ⊓ (N.U j ⊓ M.U l) ≤ M.U k ⊓ M.U l) (M.g k l))⁻¹) *
      res (inf_le_right : N.U i ⊓ M.U k ⊓ (N.U j ⊓ M.U l) ≤ N.U j ⊓ M.U l) (wu w j l) :=
    hw (i, k) (j, l)
  rw [mul_right_comm, eq_mul_inv_iff_mul_eq] at h
  have h' := congrArg (fun u => rs X (le_inf (le_inf hi hk) (le_inf hj hl) :
    W ≤ N.U i ⊓ M.U k ⊓ (N.U j ⊓ M.U l)) (Units.val u)) h
  simp only [Units.val_mul, map_mul, val_res, rs_rs] at h'
  exact h'

theorem rs_g_self {M : LB X} (hM : M.IsLB) (k : M.ι) {W : X.Opens} (h : W ≤ M.U k ⊓ M.U k) :
    rs X h (M.g k k).val = 1 := by
  have h' := congrArg (fun u => rs X (h.trans inf_le_left : W ≤ M.U k) (Units.val u)) (hM.g_self k)
  simp only [val_res, rs_rs, Units.val_one, map_one] at h'
  exact h'

theorem rs_inv_mul {U W : X.Opens} (h : W ≤ U) (u : Γ(X, U)ˣ) :
    rs X h (u⁻¹).val * rs X h u.val = 1 := by
  rw [← map_mul, Units.inv_mul, map_one]

theorem firstCohomologyVanishes_of_iso_of_isGen {N M : LB X} (hN : ⨆ i, N.U i = ⊤) (hM : M.IsLB) (w : LB.Iso M N)
    (hw : w.IsGen) (h0 : FirstCohomologyVanishes N) : FirstCohomologyVanishes M := by
  intro I V c hV hc φ hφ
  have hcov : ∀ W : X.Opens, W ≤ ⨆ i, W ⊓ N.U i := fun W x hx => by
    have hx' : x ∈ ⨆ i, N.U i := by rw [hN]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hx, hi⟩
  have hc' : ⨆ p : I × N.ι, V p.1 ⊓ N.U p.2 = ⊤ := by
    apply top_unique
    intro x _
    have hx : x ∈ ⨆ a, V a := by rw [hc]; trivial
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov _ ha)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(a, i), hi⟩
  have hφ0 : ∀ a, φ a a = 0 := fun a => by
    have h := congrArg (rs X (le_inf le_rfl inf_le_left : V a ⊓ V a ≤ V a ⊓ V a ⊓ V a)) (hφ a a a)
    simp only [map_add, map_mul, rs_rs, rs_self, rs_g_self hM, _root_.one_mul] at h
    exact add_eq_left.1 h
  obtain ⟨ψ, hψ⟩ := h0 (I × N.ι) (fun p => V p.1 ⊓ N.U p.2) (fun p => p.2) (fun _ => inf_le_right) hc'
    (fun p q => rs X (le_inf (inf_le_left.trans inf_le_right) ((inf_le_left.trans inf_le_left).trans (hV p.1)) :
        V p.1 ⊓ N.U p.2 ⊓ (V q.1 ⊓ N.U q.2) ≤ N.U p.2 ⊓ M.U (c p.1)) (wu w p.2 (c p.1)).val *
      rs X (inf_le_inf inf_le_left inf_le_left : V p.1 ⊓ N.U p.2 ⊓ (V q.1 ⊓ N.U q.2) ≤ V p.1 ⊓ V q.1)
        (φ p.1 q.1))
    (fun p q r => by
      have h := congrArg (rs X (inf_le_inf (inf_le_inf inf_le_left inf_le_left) inf_le_left :
        V p.1 ⊓ N.U p.2 ⊓ (V q.1 ⊓ N.U q.2) ⊓ (V r.1 ⊓ N.U r.2) ≤ V p.1 ⊓ V q.1 ⊓ V r.1))
        (hφ p.1 q.1 r.1)
      have h' := iso_rel w hw p.2 q.2 (c p.1) (c q.1)
        (W := V p.1 ⊓ N.U p.2 ⊓ (V q.1 ⊓ N.U q.2) ⊓ (V r.1 ⊓ N.U r.2))
        (inf_le_left.trans (inf_le_left.trans inf_le_right))
        (inf_le_left.trans (inf_le_right.trans inf_le_right))
        (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans (hV _))))
        (inf_le_left.trans (inf_le_right.trans (inf_le_left.trans (hV _))))
      simp only [map_add, map_mul, rs_rs] at h
      simp only [map_mul, rs_rs]
      rw [← h, ← _root_.mul_assoc, ← h']
      ring)
  let χ : ∀ a i, Γ(X, V a ⊓ N.U i) := fun a i =>
    rs X (le_inf inf_le_right (inf_le_left.trans (hV a)) : V a ⊓ N.U i ≤ N.U i ⊓ M.U (c a))
      ((wu w i (c a))⁻¹).val * ψ (a, i)
  have hχ : ∀ a b i j (W : X.Opens) (ha : W ≤ V a) (hb : W ≤ V b) (hi : W ≤ N.U i) (hj : W ≤ N.U j),
      rs X (le_inf ha hb : W ≤ V a ⊓ V b) (φ a b) =
        rs X (le_inf ha hi : W ≤ V a ⊓ N.U i) (χ a i) -
          rs X (le_inf (ha.trans (hV a)) (hb.trans (hV b)) : W ≤ M.U (c a) ⊓ M.U (c b))
            (M.g (c a) (c b)).val * rs X (le_inf hb hj : W ≤ V b ⊓ N.U j) (χ b j) := by
    intro a b i j W ha hb hi hj
    have h := congrArg (rs X (le_inf (le_inf ha hi) (le_inf hb hj) :
      W ≤ V a ⊓ N.U i ⊓ (V b ⊓ N.U j))) (hψ (a, i) (b, j))
    have h' := iso_rel w hw i j (c a) (c b) hi hj (ha.trans (hV a)) (hb.trans (hV b))
    have u1 := rs_inv_mul (le_inf hi (ha.trans (hV a)) : W ≤ N.U i ⊓ M.U (c a)) (wu w i (c a))
    have u2 := rs_inv_mul (le_inf hj (hb.trans (hV b)) : W ≤ N.U j ⊓ M.U (c b)) (wu w j (c b))
    simp only [map_sub, map_mul, rs_rs] at h
    simp only [χ, map_mul, rs_rs]
    generalize rs X _ (φ a b) = F at *
    generalize rs X _ (ψ (a, i)) = A at *
    generalize rs X _ (ψ (b, j)) = B at *
    generalize rs X _ (wu w i (c a)).val = u at *
    generalize rs X _ (wu w j (c b)).val = v at *
    generalize rs X _ ((wu w i (c a))⁻¹).val = u' at *
    generalize rs X _ ((wu w j (c b))⁻¹).val = v' at *
    generalize rs X _ (M.g (c a) (c b)).val = m at *
    generalize rs X _ (N.g i j).val = n at *
    linear_combination u' * h - F * u1 + u' * v' * B * h' - m * v' * B * u1 + u' * n * B * u2
  have hg : ∀ a, ∃ s : Γ(X, V a), ∀ i, rs X (inf_le_left : V a ⊓ N.U i ≤ V a) s = χ a i := fun a => by
    obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun i => V a ⊓ N.U i) (V a)
      (fun i => homOfLE inf_le_left) (hcov _) (χ a) (fun i j => by
        have h := hχ a a i j (V a ⊓ N.U i ⊓ (V a ⊓ N.U j)) (inf_le_left.trans inf_le_left)
          (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
          (inf_le_right.trans inf_le_right)
        rw [hφ0, map_zero, rs_g_self hM, _root_.one_mul] at h
        exact sub_eq_zero.1 h.symm)
    exact ⟨s, hs⟩
  choose s hs using hg
  refine ⟨s, fun a b => ?_⟩
  refine X.sheaf.eq_of_locally_eq' (fun i => V a ⊓ V b ⊓ N.U i) (V a ⊓ V b)
    (fun i => homOfLE inf_le_left) (hcov _) _ _ fun i => ?_
  have h := hχ a b i i (V a ⊓ V b ⊓ N.U i) (inf_le_left.trans inf_le_left)
    (inf_le_left.trans inf_le_right) inf_le_right inf_le_right
  change rs X (inf_le_left : V a ⊓ V b ⊓ N.U i ≤ V a ⊓ V b) _ =
    rs X (inf_le_left : V a ⊓ V b ⊓ N.U i ≤ V a ⊓ V b) _
  rw [← hs, ← hs] at h
  simp only [rs_rs] at h
  simp only [map_sub, map_mul, rs_rs]
  exact h

end H1Iso

theorem h1Zero_of_isIso : ∀ (X X' : Scheme.{0}) (e : X' ⟶ X) (M : LB X) (M' : LB X'), IsIso e →
    M.IsLB → M'.IsLB → (∃ w : LB.Iso M' (M.pull e), w.IsGen) → FirstCohomologyVanishes M → FirstCohomologyVanishes M' := by
  rintro X X' e M M' he hM hM' ⟨w, hw⟩ h0
  refine H1Iso.firstCohomologyVanishes_of_iso_of_isGen ?_ hM' w hw (H1Iso.firstCohomologyVanishes_pull_of_isIso e M h0)
  apply top_unique
  intro x _
  have hx : e.base x ∈ ⨆ i, M.U i := by rw [hM.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, le_pull M e le_rfl hi⟩

end GlobalTheory.AbLaw
