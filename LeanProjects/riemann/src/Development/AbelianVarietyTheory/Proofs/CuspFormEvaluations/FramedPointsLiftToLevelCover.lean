import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocallyNoetherian

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace FrameLift

section Germs

open TopologicalSpace

variable {A A₂ Y Y' Y₂ B : Scheme.{0}}

abbrev LOne (L : LB A) (q : Y ⟶ A) : LB Y := LB.LinComb L (K := Fin 1) (fun _ => q) (fun _ => 1)

abbrev ch (L : LB A) (q : Y ⟶ A) (i : L.ι) : Y.Opens := (LOne L q).U (fun _ => i)

theorem mem_ch {L : LB A} {q : Y ⟶ A} {i : L.ι} {y : Y} : y ∈ ch L q i ↔ q y ∈ L.U i :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun _ => h⟩

theorem exists_const {I : Type} (j : Fin 1 → I) : ∃ i, j = fun _ => i :=
  ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩

def sv {L : LB A} {q : Y ⟶ A} (s : LB.Sec (LOne L q)) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (i : L.ι) :
    Z.presheaf.stalk z := gs r z (ch L q i) (s.f fun _ => i)

theorem sv_trans {L : LB A} {q : Y ⟶ A} (s : LB.Sec (LOne L q)) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {i i' : L.ι}
    (h : q (r z) ∈ L.U i) (h' : q (r z) ∈ L.U i') :
    sv s r z i = (gm (r ≫ q) z (L.U i ⊓ L.U i') (L.g i i')).val * sv s r z i' := by
  refine (sec_trans s r z (mem_ch.2 h) (mem_ch.2 h')).trans (congrArg (fun u : (Z.presheaf.stalk z)ˣ => u.val * _) ?_)
  rw [trF, Fintype.prod_unique, zpow_one]

theorem exists_move {L : LB A} {L' : LB A₂} (hL : L.IsLB) (hL' : L'.IsLB) {q : Y ⟶ A} {q' : Y' ⟶ A₂} (h : Y' ⟶ Y)
    (c : ∀ (i : L.ι) (j : L'.ι), Γ(Y', ch L' q' j ⊓ h ⁻¹ᵁ ch L q i)ˣ)
    (hc : ∀ (y : Y') i i' j j', q (h y) ∈ L.U i → q (h y) ∈ L.U i' → q' y ∈ L'.U j → q' y ∈ L'.U j' →
      gm (𝟙 Y') y _ (c i j) * gm (h ≫ q) y (L.U i ⊓ L.U i') (L.g i i') =
        gm q' y (L'.U j ⊓ L'.U j') (L'.g j j') * gm (𝟙 Y') y _ (c i' j'))
    (s : LB.Sec (LOne L q)) : ∃ s' : LB.Sec (LOne L' q'), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) i j,
      q (h (r z)) ∈ L.U i → q' (r z) ∈ L'.U j → sv s' r z j = (gm r z _ (c i j)).val * sv s (r ≫ h) z i := by
  have key : ∀ (y : Y') i i' j j', q (h y) ∈ L.U i → q (h y) ∈ L.U i' → q' y ∈ L'.U j → q' y ∈ L'.U j' →
      (gm (𝟙 Y') y _ (c i j)).val * sv s (𝟙 Y' ≫ h) y i =
        (gm q' y (L'.U j ⊓ L'.U j') (L'.g j j')).val * ((gm (𝟙 Y') y _ (c i' j')).val * sv s (𝟙 Y' ≫ h) y i') := by
    intro y i i' j j' hi hi' hj hj'
    rw [Category.id_comp, sv_trans s h y hi hi', ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul,
      ← Units.val_mul, hc y i i' j j' hi hi' hj hj']
  have glue : ∀ j : L'.ι, ∃ a : Γ(Y', ch L' q' j), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) i,
      q (h (r z)) ∈ L.U i → q' (r z) ∈ L'.U j → gs r z _ a = (gm r z _ (c i j)).val * sv s (r ≫ h) z i := by
    intro j
    obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(Y', ch L' q' j ⊓ h ⁻¹ᵁ ch L q i), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) i,
        r z ∈ ch L' q' j ⊓ h ⁻¹ᵁ ch L q i → gs r z _ (u i) = (gm r z _ (c i j)).val * sv s (r ≫ h) z i :=
      ⟨fun i => (c i j).val * (h.appLE (ch L q i) (ch L' q' j ⊓ h ⁻¹ᵁ ch L q i) inf_le_right).hom (s.f fun _ => i), fun Z r z i hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) (gs_unit r z _ hz _) (gs_appLE h _ _ _ r z hz _))⟩
    obtain ⟨a, ha, -⟩ := Y'.sheaf.existsUnique_gluing' (fun i => ch L' q' j ⊓ h ⁻¹ᵁ ch L q i) (ch L' q' j)
      (fun i => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨i, hi⟩ := exists_chart hL (q (h y))
        exact Opens.mem_iSup.2 ⟨i, hy, mem_ch.2 hi⟩) u
      (fun i i' => fn_ext (V := (ch L' q' j ⊓ h ⁻¹ᵁ ch L q i) ⊓ (ch L' q' j ⊓ h ⁻¹ᵁ ch L q i')) fun y hy => by
        refine (gs_res (𝟙 Y') y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y') y inf_le_right hy _).symm)
        rw [hu _ _ y i hy.1, hu _ _ y i' hy.2, key y i i' j j (mem_ch.1 hy.1.2) (mem_ch.1 hy.2.2) (mem_ch.1 hy.1.1)
          (mem_ch.1 hy.1.1), gm_self hL' q' y (mem_ch.1 hy.1.1), Units.val_one, _root_.one_mul])
    refine ⟨a, fun Z r z i h₁ h₂ => ?_⟩
    have hz : r z ∈ ch L' q' j ⊓ h ⁻¹ᵁ ch L q i := ⟨mem_ch.2 h₂, mem_ch.2 h₁⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z _) (ha i)).trans (hu Z r z i hz))
  choose a ha using glue
  have le : ∀ j : Fin 1 → L'.ι, (LOne L' q').U j ≤ ch L' q' (j 0) := fun j y hy => mem_ch.2 (Set.mem_iInter.1 hy 0)
  refine ⟨⟨fun j => resG Y' (le j) (a (j 0)), fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z i j h₁ h₂ => ?_⟩
  · obtain ⟨i, hi⟩ := exists_chart hL (q (h y))
    have hj : q' y ∈ L'.U (j 0) := mem_ch.1 (le j hy.1)
    have hj' : q' y ∈ L'.U (j' 0) := mem_ch.1 (le j' hy.2)
    refine ((gs_res _ y _ hy _).trans ((gs_res _ y _ hy.1 _).trans (ha _ _ _ y i hi hj))).trans
      ((key y i i _ _ hi hi hj hj').trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
        ((gs_unit _ y _ hy _).trans (congrArg Units.val ((gm_linComb L' _ _ (𝟙 Y') y j j' hy.1 hy.2).trans ?_)))
        ((gs_res _ y _ hy _).trans ((gs_res _ y _ hy.2 _).trans (ha _ _ _ y i hi hj')))))))
    rw [Fintype.prod_unique, zpow_one, Category.id_comp]
    rfl
  · exact (gs_res r z (le fun _ => j) (mem_ch.2 h₂) _).trans (ha j Z r z i h₁ h₂)

variable {L : LB A} {L₂ : LB A₂} {φ : A₂ ⟶ A}

def Rel (w : LB.Iso L₂ (L.pull φ)) {q₂ : Y₂ ⟶ A₂} {q : Y ⟶ A} (p : Y₂ ⟶ Y) (s₂ : LB.Sec (LOne L₂ q₂))
    (s : LB.Sec (LOne L q)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y₂) (z : Z) i j, φ (q₂ (r z)) ∈ L.U i → q₂ (r z) ∈ L₂.U j →
    sv s (r ≫ p) z i = (gw w (r ≫ q₂) z i j).val * sv s₂ r z j

theorem pt_eq {Z : Scheme.{0}} {f g : Z ⟶ A} (e : f = g) (z : Z) : f z = g z := by rw [e]

theorem exists_down (hL : L.IsLB) (hL₂ : L₂.IsLB) {w : LB.Iso L₂ (L.pull φ)} (hw : w.IsGen) {q₂ : Y₂ ⟶ A₂} {q : Y ⟶ A}
    {p : Y₂ ⟶ Y} (hp : p ≫ q = q₂ ≫ φ) (s : LB.Sec (LOne L q)) : ∃ s₂ : LB.Sec (LOne L₂ q₂), Rel w p s₂ s := by
  have e : ∀ y, q (p y) = φ (q₂ y) := fun y => pt_eq hp y
  have le : ∀ i j, ch L₂ q₂ j ⊓ p ⁻¹ᵁ ch L q i ≤ q₂ ⁻¹ᵁ ((L.pull φ).U (fun _ => i) ⊓ L₂.U j) := fun i j y hy =>
    ⟨mem_pull.2 (e y ▸ mem_ch.1 hy.2), mem_ch.1 hy.1⟩
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y₂) (z : Z) i j, q (p (r z)) ∈ L.U i → q₂ (r z) ∈ L₂.U j →
      gm r z _ (res (le i j) (pullU q₂ _ (w.s (fun _ => i, j))))⁻¹ = (gw w (r ≫ q₂) z i j)⁻¹ := fun Z r z i j hi hj =>
    have hz : r z ∈ ch L₂ q₂ j ⊓ p ⁻¹ᵁ ch L q i := ⟨mem_ch.2 hj, mem_ch.2 hi⟩
    (map_inv _ _).trans (congrArg (·⁻¹) ((gm_res r z _ hz _).trans (gm_pull r q₂ z _ (le i j hz) _)))
  obtain ⟨s₂, hs⟩ := exists_move hL hL₂ p (fun i j => (res (le i j) (pullU q₂ _ (w.s (fun _ => i, j))))⁻¹)
    (fun y i i' j j' hi hi' hj hj' => by
      rw [v _ _ y i j hi hj, v _ _ y i' j' hi' hj', Category.id_comp,
        (isGen_iff w).1 hw _ q₂ y i i' j j' (e y ▸ hi) (e y ▸ hi') hj hj', hp]
      simp only [mul_inv, inv_inv]
      rw [mul_right_comm, mul_right_comm _ _ (gm (q₂ ≫ φ) y _ _), inv_mul_cancel, _root_.one_mul]) s
  refine ⟨s₂, fun Z r z i j hi hj => ?_⟩
  rw [hs Z r z i j (e _ ▸ hi) hj, v Z r z i j (e _ ▸ hi) hj, Units.mul_inv_cancel_left]

theorem exists_up (hL : L.IsLB) (hL₂ : L₂.IsLB) {w : LB.Iso L₂ (L.pull φ)} (hw : w.IsGen) {q₂ : Y₂ ⟶ A₂} {q : Y ⟶ A}
    {p : Y₂ ⟶ Y} (hp : p ≫ q = q₂ ≫ φ) {n : Y ⟶ Y₂} (hn : n ≫ p = 𝟙 _) (hn' : p ≫ n = 𝟙 _)
    (s₂ : LB.Sec (LOne L₂ q₂)) : ∃ s : LB.Sec (LOne L q), Rel w p s₂ s := by
  have hq : (n ≫ q₂) ≫ φ = q := by rw [Category.assoc, ← hp, ← Category.assoc, hn, Category.id_comp]
  have e : ∀ y, φ (q₂ (n y)) = q y := fun y => pt_eq hq y
  have le : ∀ j i, ch L q i ⊓ n ⁻¹ᵁ ch L₂ q₂ j ≤ (n ≫ q₂) ⁻¹ᵁ ((L.pull φ).U (fun _ => i) ⊓ L₂.U j) := fun j i y hy =>
    ⟨mem_pull.2 ((congrArg (· ∈ L.U i) (e y)).mpr (mem_ch.1 hy.1)), (mem_ch (y := n y)).1 hy.2⟩
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) j i, q₂ (n (r z)) ∈ L₂.U j → q (r z) ∈ L.U i →
      gm r z _ (res (le j i) (pullU (n ≫ q₂) _ (w.s (fun _ => i, j)))) = gw w (r ≫ n ≫ q₂) z i j :=
    fun Z r z j i hj hi =>
    have hz : r z ∈ ch L q i ⊓ n ⁻¹ᵁ ch L₂ q₂ j := ⟨mem_ch.2 hi, mem_ch.2 hj⟩
    (gm_res r z _ hz _).trans (gm_pull r (n ≫ q₂) z _ (le j i hz) _)
  obtain ⟨s, hs⟩ := exists_move hL₂ hL n (fun j i => res (le j i) (pullU (n ≫ q₂) _ (w.s (fun _ => i, j))))
    (fun y j j' i i' hj hj' hi hi' => by
      rw [v _ _ y j i hj hi, v _ _ y j' i' hj' hi', Category.id_comp,
        (isGen_iff w).1 hw _ (n ≫ q₂) y i i' j j' ((congrArg (· ∈ L.U i) (e y)).mpr hi)
          ((congrArg (· ∈ L.U i') (e y)).mpr hi') hj hj', hq, mul_right_comm, inv_mul_cancel_right]) s₂
  refine ⟨s, fun Z r z i j hi hj => ?_⟩
  have e₁ : (r ≫ p) ≫ n = r := by rw [Category.assoc, hn', Category.comp_id]
  have hi' : q ((r ≫ p) z) ∈ L.U i := (congrArg (· ∈ L.U i) (pt_eq hp (r z))).mpr hi
  have hj' : q₂ (n ((r ≫ p) z)) ∈ L₂.U j := (congrArg (fun t => q₂ t ∈ L₂.U j) (pt_eq e₁ z)).mpr hj
  rw [hs Z (r ≫ p) z j i hj' hi', v Z (r ≫ p) z j i hj' hi', ← Category.assoc, e₁]

theorem gm_linCombIso_pull (w : LB.Iso L₂ (L.pull φ)) {K : Type} [Fintype K] (φ' : K → (Y₂ ⟶ A₂)) (ε : K → ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ Y₂) (z : Z) (p : K → L.ι) (q : K → L₂.ι)
    (hm : r z ∈ LB.wchart (L.pull φ) φ' (fun k _ => p k) ⊓ LB.wchart L₂ φ' q) :
    gm r z (LB.wchart (L.pull φ) φ' (fun k _ => p k) ⊓ LB.wchart L₂ φ' q)
      ((LB.linCombIso w φ' ε).s (fun k _ => p k, q)) = ∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  exact (gm_res r z _ hm _).trans (gm_pull r (φ' k) z ((L.pull φ).U (fun _ => p k) ⊓ L₂.U (q k))
    ⟨Set.mem_iInter.1 hm.1 k, Set.mem_iInter.1 hm.2 k⟩ _)

theorem rel_iff (w : LB.Iso L₂ (L.pull φ)) {q₂ : Y₂ ⟶ A₂} {q : Y ⟶ A} {p : Y₂ ⟶ Y} (hp : p ≫ q = q₂ ≫ φ)
    (s₂ : LB.Sec (LOne L₂ q₂)) (s : LB.Sec (LOne L q)) :
    (∃ t : LB.Sec (LOne (L.pull φ) q₂), SecMaps (LB.linCombIso w (K := Fin 1) (fun _ => q₂) (fun _ => 1)) s₂ t ∧
      ∀ (i : Fin 1 → L.ι) (h : (LOne (L.pull φ) q₂).U (fun _ _ => i 0) ≤ p ⁻¹ᵁ (LOne L q).U i),
        (p.appLE _ _ h).hom (s.f i) = t.f (fun _ _ => i 0)) ↔ Rel w p s₂ s := by
  have le : ∀ J : Fin 1 → PUnit → L.ι, (LOne (L.pull φ) q₂).U J ≤ p ⁻¹ᵁ ch L q (J 0 PUnit.unit) := fun J y hy =>
    mem_ch.2 ((congrArg (· ∈ L.U _) (pt_eq hp y)).mpr ((mem_pull (x := q₂ y)).1 (Set.mem_iInter.1 hy 0)))
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y₂) (z : Z) i j,
      r z ∈ ch (L.pull φ) q₂ (fun _ => i) ⊓ ch L₂ q₂ j →
      gm r z (ch (L.pull φ) q₂ (fun _ => i) ⊓ ch L₂ q₂ j)
        ((LB.linCombIso w (K := Fin 1) (fun _ => q₂) (fun _ => 1)).s (fun _ _ => i, fun _ => j)) =
        gw w (r ≫ q₂) z i j := fun Z r z i j hz => by
    exact (gm_linCombIso_pull w (fun _ : Fin 1 => q₂) (fun _ => 1) r z (fun _ => i) (fun _ => j) hz).trans
      (by rw [Fintype.prod_unique, zpow_one])
  constructor
  · rintro ⟨t, h₁, h₂⟩ Z r z i j hi hj
    have hz : r z ∈ ch (L.pull φ) q₂ (fun _ => i) ⊓ ch L₂ q₂ j := ⟨mem_ch.2 (mem_pull.2 hi), mem_ch.2 hj⟩
    have a := congrArg (gs r z _) (h₂ (fun _ => i) (le fun _ _ => i))
    have b := congrArg (gs r z (ch (L.pull φ) q₂ (fun _ => i) ⊓ ch L₂ q₂ j)) (h₁ (fun _ _ => i, fun _ => j))
    exact (gs_appLE p _ _ _ r z hz.1 _).symm.trans (a.trans ((gs_res r z _ hz _).symm.trans (b.trans
      ((gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_unit r z _ hz _).trans (congrArg Units.val (v Z r z i j hz)))
        (gs_res r z _ hz _))))))
  · intro H
    refine ⟨⟨fun J => (p.appLE _ _ (le J)).hom (s.f fun _ => J 0 PUnit.unit), fun J J' => fn_ext fun y hy => ?_⟩,
      ?_, fun i h => ?_⟩
    · refine ((gs_res _ y _ hy _).trans (gs_appLE p _ _ _ _ y hy.1 _)).trans
        ((sv_trans s (𝟙 Y₂ ≫ p) y (mem_ch.1 (le J hy.1)) (mem_ch.1 (le J' hy.2))).trans
        (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
        ((gs_unit _ y _ hy _).trans (congrArg Units.val ((gm_linComb _ _ _ (𝟙 Y₂) y J J' hy.1 hy.2).trans ?_)))
        ((gs_res _ y _ hy _).trans (gs_appLE p _ _ _ _ y hy.2 _))))))
      rw [Fintype.prod_unique, zpow_one]
      refine (gm_pull_g L φ (𝟙 Y₂ ≫ q₂) y _ _ (Set.mem_iInter.1 hy.1 0) (Set.mem_iInter.1 hy.2 0)).trans ?_
      rw [Category.assoc, Category.assoc, hp]
    · rintro ⟨J, j⟩
      obtain ⟨J, rfl⟩ := exists_const J
      obtain ⟨j, rfl⟩ := exists_const j
      obtain ⟨i, rfl⟩ : ∃ i, J = fun _ => i := ⟨J PUnit.unit, rfl⟩
      refine fn_ext (V := ch (L.pull φ) q₂ (fun _ => i) ⊓ ch L₂ q₂ j) fun y hy => ?_
      have a := H _ (𝟙 Y₂) y i j ((mem_pull (x := q₂ y)).1 (mem_ch.1 hy.1)) (mem_ch.1 hy.2)
      refine ((gs_res (𝟙 Y₂) y _ hy _).trans (gs_appLE p _ _ _ (𝟙 Y₂) y hy.1 _)).trans (a.trans (Eq.symm ?_))
      exact (gs_mul (𝟙 Y₂) y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit (𝟙 Y₂) y _ hy _).trans
        (congrArg Units.val (v _ (𝟙 Y₂) y i j hy))) (gs_res (𝟙 Y₂) y _ hy _))
    · obtain ⟨i, rfl⟩ := exists_const i
      rfl

theorem sv_of_pull {q : Y ⟶ A} {q' : Y' ⟶ A} {p : Y' ⟶ Y} (hp : p ≫ q = q') {s : LB.Sec (LOne L q)}
    {s' : LB.Sec (LOne L q')}
    (H : ∀ (i : Fin 1 → L.ι) (h : (LOne L q').U i ≤ p ⁻¹ᵁ (LOne L q).U i), (p.appLE _ _ h).hom (s.f i) = s'.f i)
    {Z : Scheme.{0}} (r : Z ⟶ Y') (z : Z) (i : L.ι) (hi : q' (r z) ∈ L.U i) : sv s' r z i = sv s (r ≫ p) z i := by
  have le : ch L q' i ≤ p ⁻¹ᵁ ch L q i := fun y hy => mem_ch.2 ((congrArg (· ∈ L.U i) (pt_eq hp y)).mpr (mem_ch.1 hy))
  exact (congrArg (gs r z _) (H (fun _ => i) le)).symm.trans (gs_appLE p _ _ _ r z (mem_ch.2 hi) _)

theorem gs_lift (b : Y ⟶ B) (a : Γ(B, ⊤)) (W : Y.Opens) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (hz : r z ∈ W) :
    gs r z W ((Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom (b.appTop.hom a)) = gs (r ≫ b) z ⊤ a :=
  (gs_res r z le_top hz _).trans (gs_pull r b z ⊤ trivial a)

theorem pull_scal_iff {q : Y ⟶ A} {q' : Y' ⟶ A} {p : Y' ⟶ Y} (hp : p ≫ q = q') (b : Y ⟶ B) (a : Γ(B, ⊤))
    (s : LB.Sec (LOne L q)) (s' : LB.Sec (LOne L q')) :
    (∀ (i : Fin 1 → L.ι) (h : (LOne L q').U i ≤ p ⁻¹ᵁ (LOne L q).U i), (p.appLE _ _ h).hom
      ((Y.presheaf.map (homOfLE (le_top : (LOne L q).U i ≤ ⊤)).op).hom (b.appTop.hom a) * s.f i) = s'.f i) ↔
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (i : L.ι), q' (r z) ∈ L.U i →
      sv s' r z i = gs ((r ≫ p) ≫ b) z ⊤ a * sv s (r ≫ p) z i := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (i : L.ι) (h : ch L q' i ≤ p ⁻¹ᵁ ch L q i), r z ∈ ch L q' i →
      gs r z _ ((p.appLE _ _ h).hom ((Y.presheaf.map (homOfLE (le_top : ch L q i ≤ ⊤)).op).hom (b.appTop.hom a) *
        s.f fun _ => i)) = gs ((r ≫ p) ≫ b) z ⊤ a * sv s (r ≫ p) z i := fun Z r z i h hz =>
    (gs_appLE p _ _ _ r z hz _).trans ((gs_mul (r ≫ p) z _ (h hz) _ _).trans
      (congrArg (· * _) (gs_lift b a _ (r ≫ p) z (h hz))))
  constructor
  · intro H Z r z i hi
    have le : ch L q' i ≤ p ⁻¹ᵁ ch L q i := fun y hy => mem_ch.2 ((congrArg (· ∈ L.U i) (pt_eq hp y)).mpr (mem_ch.1 hy))
    exact (congrArg (gs r z _) (H (fun _ => i) le)).symm.trans (key Z r z i le (mem_ch.2 hi))
  · intro H i h
    obtain ⟨i, rfl⟩ := exists_const i
    exact fn_ext fun y hy => (key _ _ y i h hy).trans (H _ _ y i (mem_ch.1 hy)).symm

theorem scal_iff {q : Y ⟶ A} (b : Y ⟶ B) (a : Γ(B, ⊤)) (s s' : LB.Sec (LOne L q)) :
    (∀ i : Fin 1 → L.ι, s'.f i =
      (Y.presheaf.map (homOfLE (le_top : (LOne L q).U i ≤ ⊤)).op).hom (b.appTop.hom a) * s.f i) ↔
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : L.ι), q (r z) ∈ L.U i →
      sv s' r z i = gs (r ≫ b) z ⊤ a * sv s r z i := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : L.ι), r z ∈ ch L q i →
      gs r z _ ((Y.presheaf.map (homOfLE (le_top : ch L q i ≤ ⊤)).op).hom (b.appTop.hom a) *
        s.f fun _ => i) = gs (r ≫ b) z ⊤ a * sv s r z i := fun Z r z i hz =>
    (gs_mul r z _ hz _ _).trans (congrArg (· * _) (gs_lift b a _ r z hz))
  constructor
  · intro H Z r z i hi
    exact (congrArg (gs r z _) (H (fun _ => i))).trans (key Z r z i (mem_ch.2 hi))
  · intro H i
    obtain ⟨i, rfl⟩ := exists_const i
    exact fn_ext fun y hy => (H _ _ y i (mem_ch.1 hy)).trans (key _ _ y i hy).symm

theorem rel_scal_iff (hL : L.IsLB) (hL₂ : L₂.IsLB) {w : LB.Iso L₂ (L.pull φ)} {q₂ : Y₂ ⟶ A₂} {q : Y ⟶ A}
    {p : Y₂ ⟶ Y} (hp : p ≫ q = q₂ ≫ φ) {n : Y ⟶ Y₂} (hn : n ≫ p = 𝟙 _) {b : Y ⟶ B} {b₂ : Y₂ ⟶ B} (hb : p ≫ b = b₂)
    (a : Γ(B, ⊤)) {s₂ s₂' : LB.Sec (LOne L₂ q₂)} {s s' : LB.Sec (LOne L q)} (H : Rel w p s₂ s) (H' : Rel w p s₂' s') :
    (∀ (Z : Scheme.{0}) (r : Z ⟶ Y₂) (z : Z) (j : L₂.ι), q₂ (r z) ∈ L₂.U j →
      sv s₂' r z j = gs (r ≫ b₂) z ⊤ a * sv s₂ r z j) ↔
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : L.ι), q (r z) ∈ L.U i →
      sv s' r z i = gs (r ≫ b) z ⊤ a * sv s r z i := by
  constructor
  · intro K Z r z i hi
    obtain ⟨j, hj⟩ := exists_chart hL₂ (q₂ ((r ≫ n) z))
    have e₁ : (r ≫ n) ≫ p = r := by rw [Category.assoc, hn, Category.comp_id]
    have hi' : φ (q₂ ((r ≫ n) z)) ∈ L.U i :=
      (congrArg (· ∈ L.U i) (pt_eq hp ((r ≫ n) z))).mp ((congrArg (fun t => q t ∈ L.U i) (pt_eq e₁ z)).mpr hi)
    have a₁ := H Z (r ≫ n) z i j hi' hj
    have a₂ := H' Z (r ≫ n) z i j hi' hj
    rw [e₁] at a₁ a₂
    rw [a₁, a₂, K Z (r ≫ n) z j hj, ← hb, ← Category.assoc, e₁, mul_left_comm]
  · intro K Z r z j hj
    obtain ⟨i, hi⟩ := exists_chart hL (φ (q₂ (r z)))
    have := K Z (r ≫ p) z i ((congrArg (· ∈ L.U i) (pt_eq hp (r z))).mpr hi)
    rw [H Z r z i j hi hj, H' Z r z i j hi hj, mul_left_comm, Category.assoc, hb] at this
    exact (Units.mul_right_inj _).1 this

end Germs

section Points

variable {X X₂ Z : Scheme.{0}} {G : Over X} {G₂ : Over X₂} [GrpObj G] [GrpObj G₂] {f : X₂ ⟶ X}
  {φ : G₂.left ⟶ G.left}

theorem exists_push (h : IsGrpPullback G₂ G f φ) {a₂ : Z ⟶ X₂} {a : Z ⟶ X} (e : a₂ ≫ f = a) :
    ∃ ρ : (Over.mk a₂ ⟶ G₂) →* (Over.mk a ⟶ G), ∀ u, (ρ u).left = u.left ≫ φ := by
  subst e
  exact ⟨pushHom h (Over.mk a₂), fun _ => rfl⟩

theorem one_push (h : IsGrpPullback G₂ G f φ) {a₂ : Z ⟶ X₂} {a : Z ⟶ X} (e : a₂ ≫ f = a) :
    (1 : Over.mk a₂ ⟶ G₂).left ≫ φ = (1 : Over.mk a ⟶ G).left := by
  obtain ⟨ρ, hρ⟩ := exists_push h e
  rw [← hρ, map_one]

theorem prod_push (h : IsGrpPullback G₂ G f φ) {a₂ : Z ⟶ X₂} {a : Z ⟶ X} (e : a₂ ≫ f = a) {m : ℕ}
    (u₂ : Fin m → (Over.mk a₂ ⟶ G₂)) (u : Fin m → (Over.mk a ⟶ G)) (hu : ∀ i, (u i).left = (u₂ i).left ≫ φ) :
    (List.ofFn u₂).prod.left ≫ φ = (List.ofFn u).prod.left := by
  obtain ⟨ρ, hρ⟩ := exists_push h e
  obtain rfl : u = ρ ∘ u₂ := funext fun i => Over.OverMorphism.ext ((hu i).trans (hρ _).symm)
  rw [← hρ, map_list_prod, List.map_ofFn]

omit [GrpObj G] [GrpObj G₂] in

theorem exists_pm {W W' : Scheme.{0}} {x : W ⟶ X} (a : W' ⟶ W) (g : W' ⟶ G.left) (e : a ≫ x = g ≫ G.hom) :
    ∃ p : W' ⟶ (Over.mk x ⊗ G).left, p ≫ (snd (Over.mk x) G).left = g ∧ p ≫ (fst (Over.mk x) G).left = a :=
  ⟨pullback.lift a g e, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩

omit [GrpObj G] [GrpObj G₂] in
theorem pm_ext {W W' : Scheme.{0}} {x : W ⟶ X} {p p' : W' ⟶ (Over.mk x ⊗ G).left}
    (h₁ : p ≫ (snd (Over.mk x) G).left = p' ≫ (snd (Over.mk x) G).left)
    (h₂ : p ≫ (fst (Over.mk x) G).left = p' ≫ (fst (Over.mk x) G).left) : p = p' :=
  pullback.hom_ext h₂ h₁

omit [GrpObj G] [GrpObj G₂] in
theorem pm_cond {W : Scheme.{0}} (x : W ⟶ X) :
    (fst (Over.mk x) G).left ≫ x = (snd (Over.mk x) G).left ≫ G.hom := pullback.condition

end Points

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l l₂ : Level H}
  {Xo : Moduli Dw l} {Xo₂ : Moduli Dw l₂} {r : Xo₂.X ⟶ Xo.X} (m : SABMap Xo₂.univ.t Xo.univ.t r)
  {S : Type} [CommRing S] {x₂ : Sp S ⟶ Xo₂.X} {x : Sp S ⟶ Xo.X}

theorem eps_alg (a : S) : spMap (epsMul a) ≫ spMap (algebraMap S (DualNumber S)) =
    spMap (algebraMap S (DualNumber S)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  refine congrArg spMap (RingHom.ext fun s => ?_)
  ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_alg : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
  refine congrArg spMap (RingHom.ext fun s => ?_)
  simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem tan_iff (e : x₂ ≫ r = x) {v : Sp (DualNumber S) ⟶ Xo₂.univ.t.G.left}
    (hv : v ≫ Xo₂.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x₂) :
    IsTanAt x₂ v ↔ IsTanAt x (v ≫ m.φ) := by
  constructor
  · rintro ⟨-, h⟩
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, m.cart.1.w, ← Category.assoc, hv, Category.assoc, e]
    · rw [← Category.assoc, h, one_push m.cart e]
  · rintro ⟨-, h⟩
    refine ⟨hv, m.cart.1.hom_ext ?_ ?_⟩
    · rw [Category.assoc, h, one_push m.cart e]
    · rw [Category.assoc, hv, ← Category.assoc, fst_alg, Category.id_comp]
      exact (Over.w (1 : Over.mk x₂ ⟶ Xo₂.univ.t.G)).symm

theorem eig_iff {c : Coeff l} {c₂ : Coeff l₂} [Algebra c.F S] [Algebra c₂.F S] (τ : E →+* ℂ)
    (hc : ∀ a, algebraMap c₂.F S (embK c₂ τ a) = algebraMap c.F S (embK c τ a))
    {v : Sp (DualNumber S) ⟶ Xo₂.univ.t.G.left}
    (hv : v ≫ Xo₂.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x₂) :
    IsEigAt c₂ τ v ↔ IsEigAt c τ (v ≫ m.φ) := by
  refine forall_congr' fun a => ?_
  rw [hc, Category.assoc, ← m.act a]
  constructor
  · intro h
    rw [← Category.assoc, h, Category.assoc]
  · intro h
    refine m.cart.1.hom_ext (by rw [Category.assoc, Category.assoc]; exact h) ?_
    rw [Category.assoc, Category.assoc, Over.w, hv, ← Category.assoc, eps_alg]

theorem comb_iff (e : x₂ ≫ r = x) {k : ℕ} {v : Fin k → (Sp (DualNumber S) ⟶ Xo₂.univ.t.G.left)}
    (hv : ∀ i, v i ≫ Xo₂.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x₂) (cf : Fin k → S)
    {w : Sp (DualNumber S) ⟶ Xo₂.univ.t.G.left}
    (hw : w ≫ Xo₂.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x₂) :
    IsCombAt x₂ v cf w ↔ IsCombAt x (fun i => v i ≫ m.φ) cf (w ≫ m.φ) := by
  have e' : (spMap (algebraMap S (DualNumber S)) ≫ x₂) ≫ r = spMap (algebraMap S (DualNumber S)) ≫ x := by
    rw [Category.assoc, e]
  constructor
  · rintro ⟨u₂, hu, rfl⟩
    obtain ⟨ρ, hρ⟩ := exists_push m.cart e'
    exact ⟨fun i => ρ (u₂ i), fun i => (hρ _).trans ((congrArg (· ≫ m.φ) (hu i)).trans (Category.assoc _ _ _)),
      (prod_push m.cart e' u₂ _ fun i => hρ _).symm⟩
  · rintro ⟨u, hu, hw'⟩
    let u₂ : Fin k → (tEps x₂ ⟶ Xo₂.univ.t.G) := fun i => Over.homMk (spMap (epsMul (cf i)) ≫ v i) (by
      show (spMap (epsMul (cf i)) ≫ v i) ≫ _ = spMap (algebraMap S (DualNumber S)) ≫ x₂
      rw [Category.assoc, hv, ← Category.assoc, eps_alg])
    refine ⟨u₂, fun i => rfl, m.cart.1.hom_ext ?_ ((Over.w _).trans hw.symm)⟩
    exact (prod_push m.cart e' u₂ u fun i => (hu i).trans (Category.assoc _ _ _).symm).trans hw'

theorem exists_lift (e : x₂ ≫ r = x) {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (hv : v ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x) :
    ∃ v₂ : Sp (DualNumber S) ⟶ Xo₂.univ.t.G.left, v₂ ≫ m.φ = v ∧
      v₂ ≫ Xo₂.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x₂ :=
  ⟨m.cart.1.lift v _ (by rw [hv, Category.assoc, e]), m.cart.1.lift_fst _ _ _, m.cart.1.lift_snd _ _ _⟩

theorem exists_pm_iso (e : x₂ ≫ r = x) : ∃ (p : Gx x₂ ⟶ Gx x) (n : Gx x ⟶ Gx x₂),
    p ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x₂) Xo₂.univ.t.G).left ≫ m.φ ∧
    p ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x₂) Xo₂.univ.t.G).left ∧ n ≫ p = 𝟙 _ ∧ p ≫ n = 𝟙 _ := by
  obtain ⟨p, p₁, p₂⟩ := exists_pm (G := Xo.univ.t.G) (x := x) (fst (Over.mk x₂) Xo₂.univ.t.G).left
    ((snd (Over.mk x₂) Xo₂.univ.t.G).left ≫ m.φ) (by
      rw [Category.assoc, m.cart.1.w, ← Category.assoc, ← pm_cond, Category.assoc, ← e])
  obtain ⟨g, g₁, g₂⟩ : ∃ g : Gx x ⟶ Xo₂.univ.t.G.left, g ≫ m.φ = (snd (Over.mk x) Xo.univ.t.G).left ∧
      g ≫ Xo₂.univ.t.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ x₂ :=
    ⟨m.cart.1.lift _ _ ((pm_cond x).symm.trans ((congrArg (_ ≫ ·) e.symm).trans (Category.assoc _ _ _).symm)),
      m.cart.1.lift_fst _ _ _, m.cart.1.lift_snd _ _ _⟩
  obtain ⟨n, n₁, n₂⟩ := exists_pm (G := Xo₂.univ.t.G) (x := x₂) (fst (Over.mk x) Xo.univ.t.G).left g g₂.symm
  refine ⟨p, n, p₁, p₂, pm_ext ?_ ?_, pm_ext (m.cart.1.hom_ext ?_ ?_) ?_⟩
  · rw [Category.assoc, p₁, ← Category.assoc, n₁, g₁, Category.id_comp]
  · rw [Category.assoc, p₂, n₂, Category.id_comp]
  · rw [Category.id_comp, Category.assoc p, n₁, Category.assoc, g₁, p₁]
  · rw [Category.id_comp, Category.assoc p, n₁, Category.assoc, g₂, ← Category.assoc, p₂]
    exact pm_cond x₂
  · rw [Category.assoc, n₂, p₂, Category.id_comp]

section Over

variable {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n)

def IsRig (w : LB.Iso d.Xo₂.univ.t.PP.L (Xo.univ.t.PP.L.pull d.m.φ)) : Prop :=
  w.IsGen ∧ LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec d.Xo₂.univ.t.G) (fun _ => 1))
    d.Xo₂.univ.t.PP.rig (d.m.cm.rigPull Xo.univ.t.PP.L Xo.univ.t.PP.rig)

theorem frOver_iff [Algebra c.F S] [Algebra d.c₂.F S] (y₂ : FrPt d.Xo₂ d.c₂ S) (y : FrPt Xo c S) :
    FrOver d y₂ y ↔ y₂.x ≫ d.r = y.x ∧ (∀ τ i, y₂.u τ i ≫ d.m.φ = y.u τ i) ∧
      ∃ (w : LB.Iso d.Xo₂.univ.t.PP.L (Xo.univ.t.PP.L.pull d.m.φ)) (p : Gx y₂.x ⟶ Gx y.x), IsRig d w ∧
        p ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left ≫ d.m.φ ∧
        p ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = (fst (Over.mk y₂.x) d.Xo₂.univ.t.G).left ∧
        Rel (q₂ := (snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left) (q := (snd (Over.mk y.x) Xo.univ.t.G).left)
          w p y₂.s y.s := by
  refine and_congr_right fun _ => and_congr_right fun _ => exists_congr fun w => exists_congr fun p => ?_
  constructor
  · rintro ⟨t, h₁, h₂, h₃, h₄, h₅, h₆⟩
    exact ⟨⟨h₁, h₂⟩, h₃, h₄, (rel_iff w h₃ y₂.s y.s).1 ⟨t, h₅, h₆⟩⟩
  · rintro ⟨⟨h₁, h₂⟩, h₃, h₄, h⟩
    obtain ⟨t, h₅, h₆⟩ := (rel_iff w h₃ y₂.s y.s).2 h
    exact ⟨t, h₁, h₂, h₃, h₄, h₅, h₆⟩

theorem embK_eF (τ : E →+* ℂ) (a : 𝓞 E) : d.eF (embK c τ a) = embK d.c₂ τ a := Subtype.ext rfl

theorem exists_frOver [Algebra c.F S] [Algebra d.c₂.F S]
    (hc : ∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a) (y : FrPt Xo c S) (x₂ : Sp S ⟶ d.Xo₂.X)
    (e : x₂ ≫ d.r = y.x) (hx : x₂ ≫ d.Xo₂.s = sOf d.c₂ S) : ∃ y₂ : FrPt d.Xo₂ d.c₂ S, y₂.x = x₂ ∧ FrOver d y₂ y := by
  have hc' : ∀ τ a, algebraMap d.c₂.F S (embK d.c₂ τ a) = algebraMap c.F S (embK c τ a) := fun τ a => by
    rw [← embK_eF, hc]
  choose u hu hu' using fun τ i => exists_lift d.m e (y.tan τ i).1
  obtain ⟨w, hw, hw', -⟩ := d.m.lin
  obtain ⟨p, k, p₁, p₂, hk, hk'⟩ := exists_pm_iso d.m e
  have hL := Xo.univ.t.PP.isLB
  have hL₂ := d.Xo₂.univ.t.PP.isLB
  obtain ⟨s₂, hs⟩ := exists_down hL hL₂ hw p₁ y.s
  refine ⟨⟨x₂, hx, u, fun τ i => (tan_iff d.m e (hu' τ i)).2 (hu τ i ▸ y.tan τ i),
    fun τ i => (eig_iff d.m τ (hc' τ) (hu' τ i)).2 (hu τ i ▸ y.eig τ i), fun τ v hv hv' => ?_, s₂, fun s₂' => ?_⟩,
    rfl, (frOver_iff d _ _).2 ⟨e, hu, w, p, ⟨hw, hw'⟩, p₁, p₂, hs⟩⟩
  · refine (existsUnique_congr fun a => ?_).1
      (y.basis τ (v ≫ d.m.φ) ((tan_iff d.m e hv.1).1 hv) ((eig_iff d.m τ (hc' τ) hv.1).1 hv'))
    rw [comb_iff d.m e (hu' τ) a hv.1, funext (hu τ)]
  · obtain ⟨s', hs'⟩ := exists_up hL hL₂ hw p₁ hk hk' s₂'
    refine (existsUnique_congr fun a => ?_).1 (y.gen s')
    exact (scal_iff (fst (Over.mk y.x) Xo.univ.t.G).left (toΓ S a) y.s s').trans
      ((rel_scal_iff hL hL₂ p₁ hk p₂ (toΓ S a) hs hs').symm.trans
        (scal_iff (fst (Over.mk x₂) d.Xo₂.univ.t.G).left (toΓ S a) s₂ s₂').symm)

theorem frOver_map [Algebra c.F S] [Algebra d.c₂.F S] {T : Type} [CommRing T] [Algebra c.F T] [Algebra d.c₂.F T]
    {ψ : S →ₐ[c.F] T} {ψ₂ : S →ₐ[d.c₂.F] T} (hψ : ψ₂.toRingHom = ψ.toRingHom) {y : FrPt Xo c S}
    {y₂ : FrPt d.Xo₂ d.c₂ S} {z : FrPt Xo c T} {z₂ : FrPt d.Xo₂ d.c₂ T} (h : FrOver d y₂ y) (hz : FrMap ψ y z)
    (hz₂ : FrMap ψ₂ y₂ z₂) : FrOver d z₂ z := by
  obtain ⟨e, hu, w, p, hw, p₁, p₂, H⟩ := (frOver_iff d _ _).1 h
  obtain ⟨a₀, au, a, a₁, a₂, ha⟩ := hz
  obtain ⟨b₀, bu, b, b₁, b₂, hb⟩ := hz₂
  rw [hψ] at b₀ bu b₂
  have e' : z₂.x ≫ d.r = z.x := by rw [b₀, a₀, Category.assoc, e]
  obtain ⟨p', -, p₁', p₂', -⟩ := exists_pm_iso d.m e'
  have sq : p' ≫ a = b ≫ p := by
    refine pm_ext ?_ ?_
    · rw [Category.assoc, a₁, p₁', Category.assoc, p₁, ← Category.assoc, b₁]
    · rw [Category.assoc, a₂, ← Category.assoc, p₂', Category.assoc, p₂, b₂]
  refine (frOver_iff d _ _).2 ⟨e', fun τ i => by rw [bu, au, Category.assoc, hu], w, p', hw, p₁', p₂',
    fun Z r z' i j hi hj => ?_⟩
  have k₁ := sv_of_pull a₁ ha (r ≫ p') z' i ((congrArg (· ∈ Xo.univ.t.PP.L.U i) (pt_eq p₁' (r z'))).mpr hi)
  have k₂ := sv_of_pull b₁ hb r z' j hj
  have k₃ := H Z (r ≫ b) z' i j ((congrArg (fun t => d.m.φ t ∈ Xo.univ.t.PP.L.U i) (pt_eq b₁ (r z'))).mpr hi)
    ((congrArg (· ∈ d.Xo₂.univ.t.PP.L.U j) (pt_eq b₁ (r z'))).mpr hj)
  rw [Category.assoc, sq] at k₁
  rw [Category.assoc, Category.assoc, b₁] at k₃
  exact k₁.trans (k₃.trans (congrArg _ k₂.symm))

theorem frBor_lift (hG : GlobalFnsSt) [Algebra c.F S] [Algebra d.c₂.F S] {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S}
    {y₂ y₂' : FrPt d.Xo₂ d.c₂ S} (h : FrOver d y₂ y) (h' : FrOver d y₂' y') (ex : y₂'.x = y₂.x) (hb : FrBor t y y') :
    FrBor t y₂ y₂' := by
  obtain ⟨e, hu, w, p, hw, p₁, p₂, H⟩ := (frOver_iff d _ _).1 h
  obtain ⟨e', hu', w', p', hw', p₁', p₂', H'⟩ := (frOver_iff d _ _).1 h'
  obtain rfl : w = w' := rigidified_iso_unique hG (UnivPol.pol d.Xo₂) Xo.univ.t.PP.isLB d.m.φ w w' hw.1 hw'.1 _ _
    hw.2 hw'.2
  obtain ⟨-, au, a, a₁, a₂, ha⟩ := hb
  obtain ⟨b, b₁, b₂⟩ := exists_pm (G := d.Xo₂.univ.t.G) (x := y₂.x) (fst (Over.mk y₂'.x) d.Xo₂.univ.t.G).left
    (snd (Over.mk y₂'.x) d.Xo₂.univ.t.G).left (by rw [← ex]; exact pm_cond _)
  have sq : p' ≫ a = b ≫ p := by
    refine pm_ext ?_ ?_
    · rw [Category.assoc, a₁, p₁', Category.assoc, p₁, ← Category.assoc, b₁]
    · rw [Category.assoc, a₂, p₂', Category.assoc, p₂, b₂]
  refine ⟨ex, fun τ i => ?_, b, b₁, b₂, ?_⟩
  · obtain ⟨cf, c₁, c₂, hcf⟩ := au τ i
    refine ⟨cf, c₁, c₂, (comb_iff d.m e (fun j => (y₂.tan τ j).1) cf (ex ▸ (y₂'.tan τ i).1)).2 ?_⟩
    rw [funext (hu τ), hu']
    exact hcf
  · refine (pull_scal_iff b₁ (fst (Over.mk y₂.x) d.Xo₂.univ.t.G).left (toΓ S (t none)) y₂.s y₂'.s).2
      fun Z r z j hj => ?_
    obtain ⟨i, hi⟩ := exists_chart Xo.univ.t.PP.isLB (d.m.φ ((snd (Over.mk y₂'.x) d.Xo₂.univ.t.G).left (r z)))
    have k₁ := (pull_scal_iff a₁ (fst (Over.mk y.x) Xo.univ.t.G).left (toΓ S (t none)) y.s y'.s).1 ha Z (r ≫ p') z i
      ((congrArg (· ∈ Xo.univ.t.PP.L.U i) (pt_eq p₁' (r z))).mpr hi)
    have k₂ := H' Z r z i j hi hj
    have k₃ := H Z (r ≫ b) z i j ((congrArg (fun t => d.m.φ t ∈ Xo.univ.t.PP.L.U i) (pt_eq b₁ (r z))).mpr hi)
      ((congrArg (· ∈ d.Xo₂.univ.t.PP.L.U j) (pt_eq b₁ (r z))).mpr hj)
    rw [Category.assoc r p' a, sq, ← Category.assoc r b p, Category.assoc (r ≫ b) p, p₂, k₂, k₃,
      Category.assoc r b (snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left, b₁, mul_left_comm] at k₁
    exact (Units.mul_right_inj _).1 k₁

end Over

end FrameLift

theorem frames_lift_to_cover :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), (∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S], (∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a) → ∀ (y : FrPt Xo c S) (x₂ : Sp S ⟶ d.Xo₂.X), x₂ ≫ d.r = y.x → x₂ ≫ d.Xo₂.s = sOf d.c₂ S → ∃ y₂ : FrPt d.Xo₂ d.c₂ S, y₂.x = x₂ ∧ FrOver d y₂ y) ∧ (∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S], (∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a) → ∀ (T : Type) [CommRing T] [Algebra c.F T] [Algebra d.c₂.F T], (∀ a : c.F, algebraMap d.c₂.F T (d.eF a) = algebraMap c.F T a) → ∀ (ψ : S →ₐ[c.F] T) (ψ₂ : S →ₐ[d.c₂.F] T), ψ₂.toRingHom = ψ.toRingHom → ∀ (y : FrPt Xo c S) (y₂ : FrPt d.Xo₂ d.c₂ S) (z : FrPt Xo c T) (z₂ : FrPt d.Xo₂ d.c₂ T), FrOver d y₂ y → FrMap ψ y z → FrMap ψ₂ y₂ z₂ → FrOver d z₂ z) ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S], (∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a) → ∀ (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S) (y₂ y₂' : FrPt d.Xo₂ d.c₂ S), FrOver d y₂ y → FrOver d y₂' y' → y₂'.x = y₂.x → FrBor t y y' → FrBor t y₂ y₂' :=
  fun hL _ _ _ _ _ _ _ _ _ _ d =>
    ⟨fun _ _ _ _ hc y x₂ e hx => FrameLift.exists_frOver d hc y x₂ e hx,
      fun _ _ _ _ _ _ _ _ _ _ _ _ hψ _ _ _ _ h hz hz₂ => FrameLift.frOver_map d hψ h hz hz₂,
      fun _ _ _ _ _ _ _ _ _ _ h h' ex hb => FrameLift.frBor_lift d hL.globalFns h h' ex hb⟩

end GlobalTheory
