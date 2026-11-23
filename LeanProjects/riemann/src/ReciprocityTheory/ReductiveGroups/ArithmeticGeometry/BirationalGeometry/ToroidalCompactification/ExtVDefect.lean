import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi

variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}
variable {K : Type} [Fintype K] {Y Y' : Scheme.{0}} {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X')} {ε : K → ℤ}

theorem gm_gen_change {Z : Scheme.{0}} (hL : L.IsLB) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (r : Z ⟶ Y) (z : Z)
    (p p' : K → L.ι) (hp : ∀ k, φ k (r z) ∈ L.U (p k)) (hp' : ∀ k, φ k (r z) ∈ L.U (p' k)) :
    gm r z (LB.wchart L φ p) (t.s p) =
      (∏ k, gm (r ≫ φ k) z (L.U (p k) ⊓ L.U (p' k)) (L.g (p k) (p' k)) ^ ε k) * gm r z (LB.wchart L φ p') (t.s p') := by
  have m : r z ∈ (LB.LinComb L φ ε).U p ⊓ (LB.LinComb L φ ε).U p' :=
    ⟨Set.mem_iInter.2 fun k => hp k, Set.mem_iInter.2 fun k => hp' k⟩
  have e := congrArg (gm r z _) (ht p p')
  rw [gm_res r z _ m, map_mul, gm_res r z _ m] at e
  refine e.trans ?_
  congr 1
  show gm r z _ (∏ k, (res _ (pullU (φ k) _ (L.g (p k) (p' k)))) ^ ε k) = _
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow]
  exact congrArg (· ^ ε k) ((gm_res r z _ m _).trans (gm_pull r (φ k) z (L.U (p k) ⊓ L.U (p' k)) ⟨hp k, hp' k⟩ _))

theorem exists_defect (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (hw : PGen w)
    (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (h : Y' ⟶ Y)
    (hc : ∀ k, φ' k ≫ F = h ≫ φ k) :
    ∃ u : Γ(Y', ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
      (∀ k, F (φ' k (r z)) ∈ L.U (p k)) → (∀ k, φ' k (r z) ∈ L'.U (q k)) →
      gm (r ≫ h) z (LB.wchart L φ p) (t.s p) =
        gm r z ⊤ u * ((∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k) * gm r z (LB.wchart L' φ' q) (a.s q)) := by
  classical
  have pt : ∀ k y, F (φ' k y) = φ k (h y) := fun k y => congrArg (fun g => g y) (hc k)
  let O : (K → L.ι) × (K → L'.ι) → Y'.Opens := fun pq => h ⁻¹ᵁ (LB.wchart L φ pq.1) ⊓ LB.wchart L' φ' pq.2
  have memO : ∀ pq x, x ∈ O pq ↔ (∀ k, φ k (h x) ∈ L.U (pq.1 k)) ∧ (∀ k, φ' k x ∈ L'.U (pq.2 k)) := fun pq x =>
    ⟨fun hx => ⟨fun k => Set.mem_iInter.1 hx.1 k, fun k => Set.mem_iInter.1 hx.2 k⟩,
      fun hx => ⟨Set.mem_iInter.2 hx.1, Set.mem_iInter.2 hx.2⟩⟩
  have l1 : ∀ pq k, O pq ≤ φ' k ⁻¹ᵁ ((L.pull F).U (fun _ => pq.1 k) ⊓ L'.U (pq.2 k)) := fun pq k x hx =>
    ⟨Set.mem_iInter.2 fun _ => show F (φ' k x) ∈ L.U (pq.1 k) by rw [pt k x]; exact ((memO pq x).1 hx).1 k,
      ((memO pq x).1 hx).2 k⟩
  have l2 : ∀ pq, O pq ≤ h ⁻¹ᵁ (LB.wchart L φ pq.1) := fun _ => inf_le_left
  have l3 : ∀ pq, O pq ≤ LB.wchart L' φ' pq.2 := fun _ => inf_le_right
  let v : ∀ pq, Γ(Y', O pq)ˣ := fun pq =>
    res (l2 pq) (pullU h _ (t.s pq.1)) *
      ((∏ k, (res (l1 pq k) (pullU (φ' k) _ (w.s (fun _ => pq.1 k, pq.2 k)))) ^ ε k) * res (l3 pq) (a.s pq.2))⁻¹
  have gv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (pq : (K → L.ι) × (K → L'.ι)), r z ∈ O pq →
      gm r z (O pq) (v pq) = gm (r ≫ h) z (LB.wchart L φ pq.1) (t.s pq.1) *
        ((∏ k, gw w (r ≫ φ' k) z (pq.1 k) (pq.2 k) ^ ε k) * gm r z (LB.wchart L' φ' pq.2) (a.s pq.2))⁻¹ := by
    intro Z r z pq hz
    show gm r z (O pq) (res _ _ * ((∏ k, (res _ _) ^ ε k) * res _ _)⁻¹) = _
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z _ hz _).trans (gm_pull r h z _ (l2 pq hz) _)) ?_)
    refine (map_inv _ _).trans (congrArg (·⁻¹) ?_)
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res r z _ hz _))
    refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => ?_)
    exact (map_zpow _ _ _).trans (congrArg (· ^ ε k) ((gm_res r z _ hz _).trans (gm_pull r (φ' k) z _ (l1 pq k hz) _)))
  obtain ⟨s, hs⟩ := glue_unit ⊤ O (fun _ => le_top) (fun x _ => by
      choose p hp using fun k => exists_chart hL (φ k (h x))
      choose q hq using fun k => exists_chart hL' (φ' k x)
      exact Opens.mem_iSup.2 ⟨(p, q), (memO (p, q) x).2 ⟨hp, hq⟩⟩) v (fun pq pq' x hx => by
      rw [gv Y' (𝟙 Y') x pq hx.1, gv Y' (𝟙 Y') x pq' hx.2]
      have m := (memO pq x).1 hx.1
      have m' := (memO pq' x).1 hx.2
      rw [gm_gen_change hL t ht (𝟙 Y' ≫ h) x pq.1 pq'.1 m.1 m'.1,
        gm_gen_change hL' a ha (𝟙 Y') x pq.2 pq'.2 m.2 m'.2]
      have hW : ∀ k, gw w (𝟙 Y' ≫ φ' k) x (pq.1 k) (pq.2 k) =
          gm ((𝟙 Y' ≫ h) ≫ φ k) x _ (L.g (pq.1 k) (pq'.1 k)) *
            (gm (𝟙 Y' ≫ φ' k) x _ (L'.g (pq.2 k) (pq'.2 k)))⁻¹ * gw w (𝟙 Y' ≫ φ' k) x (pq'.1 k) (pq'.2 k) := by
        intro k
        have e := hw Y' (𝟙 Y' ≫ φ' k) x (pq.1 k) (pq'.1 k) (pq.2 k) (pq'.2 k)
          (by show F (φ' k x) ∈ _; rw [pt]; exact m.1 k) (by show F (φ' k x) ∈ _; rw [pt]; exact m'.1 k)
          (m.2 k) (m'.2 k)
        rw [e, Category.assoc, Category.assoc, hc k]
      simp only [hW]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_prod, ofMul_zpow, inv_zpow', Finset.sum_add_distrib,
        smul_add, smul_neg, Finset.sum_neg_distrib, smul_eq_mul, neg_one_mul, neg_smul]
      abel)
  refine ⟨s, fun Z r z p q hp hq => ?_⟩
  have hz : r z ∈ O (p, q) := (memO (p, q) (r z)).2 ⟨fun k => by rw [← pt]; exact hp k, hq⟩
  have e := gv Z r z (p, q) hz
  rw [← hs (p, q), gm_res r z _ hz] at e
  rw [e, inv_mul_cancel_right]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
