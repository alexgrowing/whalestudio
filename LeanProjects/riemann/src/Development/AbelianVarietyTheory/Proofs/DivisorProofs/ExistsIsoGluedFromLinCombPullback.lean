import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFactorNontrivial
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteNormalising
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem trF_sum_elim {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    (φ₁ : K → (Y ⟶ X)) (φ₂ : K' → (Y ⟶ X)) (ε₁ : K → ℤ) (ε₂ : K' → ℤ) (r : Z ⟶ Y) (z : Z)
    (p p' : K → L.ι) (q q' : K' → L.ι) :
    trF (Sum.elim φ₁ φ₂) (Sum.elim ε₁ ε₂) r z (Sum.elim p q) (Sum.elim p' q') =
      trF φ₁ ε₁ r z p p' * trF φ₂ ε₂ r z q q' := by
  rw [trF, trF, trF, Fintype.prod_sum_type]; rfl

theorem trF_self' {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (hp : r z ∈ LB.wchart L φ p) :
    trF φ ε r z p p = 1 := by
  unfold trF
  refine Finset.prod_eq_one fun k _ => ?_
  rw [gm_self hL (r ≫ φ k) z (Set.mem_iInter.1 hp k), _root_.one_zpow]

theorem iso_linComb_pull_glue : ∀ {X X' Y : Scheme.{0}} {M : LB Y}, M.IsLB → ∀ {L' : LB X'}, L'.IsLB →
    ∀ {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (X' ⟶ Y)) (ε : K → ℤ) (ψ : K' → (X ⟶ Y)) (e : K' → ℤ)
    (F : X ⟶ X') (w₁ : LB.Iso L' (LB.LinComb M φ ε)), w₁.IsGen →
    ∀ (u : LB.Gen (LB.LinComb M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim ε (fun i => - e i)))), u.IsGen →
    ∃ w : LB.Iso (LB.LinComb M ψ e) (L'.pull F), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (J : (Z ⟶ Y) → M.ι), Good M z J → ∀ j' : L'.ι, F (f z) ∈ L'.U j' →
        gw w f z j' (fun i => J (f ≫ ψ i)) = (gv w₁ (f ≫ F) z (fun k => J ((f ≫ F) ≫ φ k)) j')⁻¹ * val u f z J := by
  intro X X' Y M hM L' hL' K K' _ _ φ ε ψ e F w₁ hw₁ u hu

  have memE : ∀ {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (p : K → M.ι) (q : K' → M.ι),
      F (f z) ∈ LB.wchart M φ p → f z ∈ LB.wchart M ψ q →
      f z ∈ LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p q) := by
    intro Z f z p q hp hq
    refine Set.mem_iInter.2 fun k => ?_
    cases k with
    | inl k => exact Set.mem_iInter.1 hp k
    | inr i => exact Set.mem_iInter.1 hq i

  have key : ∀ {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (j' : L'.ι) (q : K' → M.ι) (p p' : K → M.ι),
      F (f z) ∈ L'.U j' → f z ∈ LB.wchart M ψ q → F (f z) ∈ LB.wchart M φ p → F (f z) ∈ LB.wchart M φ p' →
      gm f z _ (u.s (Sum.elim p q)) * (gm (f ≫ F) z _ (w₁.s (p, j')))⁻¹ =
        gm f z _ (u.s (Sum.elim p' q)) * (gm (f ≫ F) z _ (w₁.s (p', j')))⁻¹ := by
    intro Z f z j' q p p' hj hq hp hp'
    have a := gen_trans hu f z (memE f z p q hp hq) (memE f z p' q hp' hq)
    rw [trF_sum_elim, trF_self' hM ψ _ f z q hq, _root_.mul_one] at a
    have b := gm_isGen hw₁ (f ≫ F) z p p' j' j' hp hp' hj hj
    have c : gm (f ≫ F) z _ ((LB.LinComb M φ ε).g p p') = trF (fun k => F ≫ φ k) ε f z p p' := by
      refine (gm_linComb M φ ε (f ≫ F) z p p' hp hp').trans ?_
      simp only [trF, Category.assoc]
    rw [c, gm_self hL' (f ≫ F) z hj, inv_one, _root_.mul_one] at b
    show gm f z (LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p q)) (u.s (Sum.elim p q)) * (gv w₁ (f ≫ F) z p j')⁻¹ =
      gm f z (LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p' q)) (u.s (Sum.elim p' q)) * (gv w₁ (f ≫ F) z p' j')⁻¹
    rw [a, b]
    generalize trF (fun k => F ≫ φ k) ε f z p p' = T
    generalize gm f z _ (u.s (Sum.elim p' q)) = U
    generalize gv w₁ (f ≫ F) z p' j' = V
    rw [_root_.mul_inv, _root_.mul_mul_mul_comm, _root_.mul_inv_cancel, _root_.one_mul]
  have glue : ∀ (j' : L'.ι) (q : K' → M.ι),
      ∃ s : Γ(X, (L'.pull F).U (fun _ => j') ⊓ (LB.LinComb M ψ e).U q)ˣ,
      ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (p : K → M.ι), F (f z) ∈ L'.U j' → f z ∈ LB.wchart M ψ q →
        F (f z) ∈ LB.wchart M φ p →
        gm f z _ s = gm f z _ (u.s (Sum.elim p q)) * (gm (f ≫ F) z _ (w₁.s (p, j')))⁻¹ := by
    intro j' q
    obtain ⟨W, hW⟩ : ∃ W : (K → M.ι) → X.Opens, ∀ p x, x ∈ W p ↔
        F x ∈ L'.U j' ∧ x ∈ LB.wchart M ψ q ∧ F x ∈ LB.wchart M φ p :=
      ⟨fun p => F ⁻¹ᵁ L'.U j' ⊓ (LB.wchart M ψ q ⊓ F ⁻¹ᵁ LB.wchart M φ p), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ p, W p ≤ (L'.pull F).U (fun _ => j') ⊓ (LB.LinComb M ψ e).U q := fun p x hx =>
      ⟨mem_pull.2 ((hW p x).1 hx).1, ((hW p x).1 hx).2.1⟩
    have l₁ : ∀ p, W p ≤ LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p q) := fun p x hx =>
      memE (𝟙 X) x p q ((hW p x).1 hx).2.2 ((hW p x).1 hx).2.1
    have l₂ : ∀ p, W p ≤ F ⁻¹ᵁ (LB.wchart M φ p ⊓ L'.U j') := fun p x hx =>
      ⟨((hW p x).1 hx).2.2, ((hW p x).1 hx).1⟩
    obtain ⟨v, hv⟩ : ∃ v : ∀ p, Γ(X, W p)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (p : K → M.ι), f z ∈ W p →
        gm f z (W p) (v p) = gm f z _ (u.s (Sum.elim p q)) * (gm (f ≫ F) z _ (w₁.s (p, j')))⁻¹ :=
      ⟨fun p => res (l₁ p) (u.s (Sum.elim p q)) * (res (l₂ p) (pullU F _ (w₁.s (p, j'))))⁻¹,
        fun Z f z p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f z (l₁ p) hz _)
          ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res f z (l₂ p) hz _).trans (gm_pull f F z _ (l₂ p hz) _)))))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        choose p hp using fun k => exists_chart hM (φ k (F x))
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, (hW p x).2 ⟨mem_pull.1 hx.1, hx.2, Set.mem_iInter.2 hp⟩⟩) v (fun p p' x hx => by
        have h₁ := (hW p x).1 hx.1
        have h₂ := (hW p' x).1 hx.2
        exact (hv _ (𝟙 X) x p hx.1).trans ((key (𝟙 X) x j' q p p' h₁.1 h₁.2.1 h₁.2.2 h₂.2.2).trans
          (hv _ (𝟙 X) x p' hx.2).symm))
    refine ⟨s, fun Z f z p hj hq hp => ?_⟩
    have hz := (hW p (f z)).2 ⟨hj, hq, hp⟩
    exact (gm_res f z (l₀ p) hz s).symm.trans ((congrArg (gm f z (W p)) (hs p)).trans (hv Z f z p hz))
  choose s hs using glue
  refine ⟨⟨fun P => s (P.1 PUnit.unit) P.2⟩, (isGen_iff _).2 ?_, ?_⟩
  · intro Z f z j j' (k : K' → M.ι) (k' : K' → M.ι) hj hj' hk hk'
    choose p hp using fun a => exists_chart hM (φ a (F (f z)))
    have hpm : F (f z) ∈ LB.wchart M φ p := Set.mem_iInter.2 hp
    show gm f z _ (s j k) = gm (f ≫ F) z _ (L'.g j j') * (gm f z _ ((LB.LinComb M ψ e).g k k'))⁻¹ *
      gm f z _ (s j' k')
    rw [hs j k Z f z p hj hk hpm, hs j' k' Z f z p hj' hk' hpm]
    have a := gen_trans hu f z (memE f z p k hpm hk) (memE f z p k' hpm hk')
    rw [trF_sum_elim, trF_self' hM (fun a => F ≫ φ a) ε f z p (Set.mem_iInter.2 fun a => Set.mem_iInter.1 hpm a), _root_.one_mul] at a
    have c : gm f z _ ((LB.LinComb M ψ e).g k k') = trF ψ e f z k k' := gm_linComb M ψ e f z k k' hk hk'
    have d : trF ψ (fun i => - e i) f z k k' = (trF ψ e f z k k')⁻¹ := by
      simp only [trF, zpow_neg, Finset.prod_inv_distrib]
    rw [d] at a
    have b := gm_isGen hw₁ (f ≫ F) z p p j j' hpm hpm hj hj'
    have c' : gm (f ≫ F) z _ ((LB.LinComb M φ ε).g p p) = 1 :=
      (gm_linComb M φ ε (f ≫ F) z p p hpm hpm).trans (trF_self' hM φ ε (f ≫ F) z p hpm)
    rw [c', _root_.one_mul] at b
    show gm f z (LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p k)) (u.s (Sum.elim p k)) * (gv w₁ (f ≫ F) z p j)⁻¹ =
      gm (f ≫ F) z _ (L'.g j j') * (gm f z _ ((LB.LinComb M ψ e).g k k'))⁻¹ *
      (gm f z (LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p k')) (u.s (Sum.elim p k')) * (gv w₁ (f ≫ F) z p j')⁻¹)
    rw [a, b, c]
    generalize trF ψ e f z k k' = T
    generalize gm f z _ (u.s (Sum.elim p k')) = U
    generalize gv w₁ (f ≫ F) z p j' = V
    generalize gm (f ≫ F) z _ (L'.g j j') = G
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · intro Z f z J hJ j' hj
    have hp : F (f z) ∈ LB.wchart M φ (fun k => J ((f ≫ F) ≫ φ k)) :=
      Set.mem_iInter.2 fun k => hJ ((f ≫ F) ≫ φ k)
    show gm f z _ (s j' (fun i => J (f ≫ ψ i))) = _
    rw [hs j' _ Z f z _ hj (hJ.mem ψ f) hp,
      val_of u f z J (Sum.elim (fun k => J ((f ≫ F) ≫ φ k)) (fun i => J (f ≫ ψ i)))
        (by rintro (k | i) <;> simp only [Sum.elim_inl, Sum.elim_inr, Category.assoc])]
    exact mul_comm _ _

end GlobalTheory.Mum
