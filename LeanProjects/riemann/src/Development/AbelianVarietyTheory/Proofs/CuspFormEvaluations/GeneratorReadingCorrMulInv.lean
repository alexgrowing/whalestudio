import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnValGenCorr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem chart_iff {X Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Z ⟶ X)) (j : K → L.ι)
    (x : Sp ℂ ⟶ Z) : ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j ↔ ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k) := by
  constructor
  · intro h k p _
    have hp := h (Set.mem_univ p)
    exact Set.mem_iInter.1 hp k
  · intro h p _
    exact Set.mem_iInter.2 fun k => h k (Set.mem_univ p)

theorem exists_chart {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (x : Sp ℂ ⟶ X) : ∃ i, ⊤ ≤ x ⁻¹ᵁ L.U i := by
  have h : x cpt ∈ (⨆ i, L.U i : X.Opens) := by
    rw [hL.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ⟨i, ReciprocityTheory.ChartRestriction.G.PullbackSections.top_le_of_mem hi⟩

theorem corr_val {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (hc : LB.Gen.Corr L φ ε φ' ε' t t')
    (J : (Y ⟶ X) → L.ι) (p : Sp ℂ ⟶ Y) (hJ : ∀ ψ, ⊤ ≤ (p ≫ ψ) ⁻¹ᵁ L.U (J ψ)) :
    valAt' p (LB.wchart L φ fun k => J (φ k)) (t.s fun k => J (φ k)).val =
      valAt' p (LB.wchart L φ' fun k => J (φ' k)) (t'.s fun k => J (φ' k)).val := by
  have h1 := (chart_iff L φ (fun k => J (φ k)) p).2 fun k => hJ _
  have h2 := (chart_iff L φ' (fun k => J (φ' k)) p).2 fun k => hJ _
  have h : ⊤ ≤ p ⁻¹ᵁ (LB.wchart L φ (fun k => J (φ k)) ⊓ LB.wchart L φ' fun k => J (φ' k)) :=
    fun z hz => ⟨h1 hz, h2 hz⟩
  have e0 := hc (fun k => J (φ k)) (fun k => J (φ' k)) (fun _ _ e => congrArg J e) (fun _ _ e => congrArg J e)
    (fun _ _ e => congrArg J e)
  have e := congrArg (fun u : Γ(Y, LB.wchart L φ (fun k => J (φ k)) ⊓ LB.wchart L φ' fun k => J (φ' k))ˣ =>
    valAt' p _ u.val) e0
  exact (vtf_val_res p _ h _).symm.trans (e.trans (vtf_val_res p _ h _))

theorem val_inv {Z : Scheme.{0}} (p : Sp ℂ ⟶ Z) {V : Z.Opens} (h : ⊤ ≤ p ⁻¹ᵁ V) (u : Γ(Z, V)ˣ) :
    valAt' p V (u⁻¹).val = (valAt' p V u.val)⁻¹ := by
  have e := vtf_valU p h u (-1)
  rwa [zpow_neg_one, zpow_neg_one] at e

open scoped Classical in
theorem prod_fibre {T K : Type} [Fintype K] (φ : K → T) (ε : K → ℤ) (f : T → ℂ) (s : Finset T)
    (hs : ∀ k, φ k ∈ s) (hf : ∀ ψ ∈ s, f ψ ≠ 0) :
    ∏ k, f (φ k) ^ ε k = ∏ ψ ∈ s, f ψ ^ (∑ k, if φ k = ψ then ε k else 0) := by
  have key : ∀ ψ ∈ s, f ψ ^ (∑ k, if φ k = ψ then ε k else 0) =
      ∏ k, if φ k = ψ then f (φ k) ^ ε k else 1 := by
    intro ψ hψ
    have h : ∀ u : Finset K, f ψ ^ (∑ k ∈ u, if φ k = ψ then ε k else 0) =
        ∏ k ∈ u, if φ k = ψ then f (φ k) ^ ε k else 1 := by
      intro u
      induction u using Finset.induction_on with
      | empty => simp
      | insert a u ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ (hf ψ hψ), ih]
        congr 1
        split_ifs with h
        · rw [h]
        · simp
    exact h _
  rw [Finset.prod_congr rfl key, Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_ite_eq, if_pos (hs k)]

theorem genRd_corr_mul_inv : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (Z : Scheme.{0}) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (φ' : K' → (Z ⟶ A.left)) (ε' : K' → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)) (t' : LB.Gen (LB.LinComb L.L φ' ε')) (q : Sp ℂ ⟶ Z) (p : K → Fin g → ℂ) (p' : K' → Fin g → ℂ) (v v' : ℂ), Φ.GenRd φ ε t q p v → Φ.GenRd φ' ε' t' q p' v' → (LB.Gen.Corr L.L φ ε φ' ε' t t' → ∃ J : (Z ⟶ A.left) → L.L.ι, (∀ ψ, ⊤ ≤ (q ≫ ψ) ⁻¹ᵁ L.L.U (J ψ)) ∧ v * ∏ k, Φ.fr (J (φ k)) (p k) ^ ε k = v' * ∏ k, Φ.fr (J (φ' k)) (p' k) ^ ε' k) ∧ (LB.Gen.Corr L.L φ ε φ' ε' t t' → LB.SameSum φ ε φ' ε' → (∃ π : (Z ⟶ A.left) → Fin g → ℂ, (∀ k, p k = π (φ k)) ∧ ∀ k, p' k = π (φ' k)) → v = v') ∧ Φ.GenRd (Sum.elim φ φ') (Sum.elim ε ε') (LB.mulGen L.L φ ε φ' ε' t t') q (Sum.elim p p') (v * v') ∧ Φ.GenRd φ (fun k => -ε k) (LB.invGen L.L φ ε t) q p v⁻¹ := by
  classical
  intro S A _ _ L x0 g Φ Z K K' _ _ φ ε φ' ε' t t' q p p' v v' h h'
  have hA : LB.Gen.Corr L.L φ ε φ' ε' t t' → ∃ J : (Z ⟶ A.left) → L.L.ι,
      (∀ ψ, ⊤ ≤ (q ≫ ψ) ⁻¹ᵁ L.L.U (J ψ)) ∧
      v * ∏ k, Φ.fr (J (φ k)) (p k) ^ ε k = v' * ∏ k, Φ.fr (J (φ' k)) (p' k) ^ ε' k := by
    intro hc
    choose J hJ using fun ψ : Z ⟶ A.left => exists_chart L.L L.isLB (q ≫ ψ)
    refine ⟨J, hJ, ?_⟩
    have e := corr_val L.L φ ε φ' ε' t t' hc J q hJ
    have e1 := h.2 (fun k => J (φ k)) ((chart_iff L.L φ _ q).2 fun k => hJ _)
    have e2 := h'.2 (fun k => J (φ' k)) ((chart_iff L.L φ' _ q).2 fun k => hJ _)
    exact e1.symm.trans (e.trans e2)
  refine ⟨hA, ?_, ⟨?_, ?_⟩, ⟨h.1, ?_⟩⟩
  · rintro hc hs ⟨π, hπ, hπ'⟩
    obtain ⟨J, hJ, e⟩ := hA hc
    have n1 : ∀ k, Φ.fr (J (φ k)) (π (φ k)) ≠ 0 := fun k => by
      rw [← hπ k]; apply Φ.fr_ne; rw [← h.1 k]; exact hJ _
    have n2 : ∀ k, Φ.fr (J (φ' k)) (π (φ' k)) ≠ 0 := fun k => by
      rw [← hπ' k]; apply Φ.fr_ne; rw [← h'.1 k]; exact hJ _
    let s : Finset (Z ⟶ A.left) := Finset.univ.image φ ∪ Finset.univ.image φ'
    have hf : ∀ ψ ∈ s, Φ.fr (J ψ) (π ψ) ≠ 0 := by
      intro ψ hψ
      rcases Finset.mem_union.1 hψ with hψ | hψ
      · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hψ
        exact n1 k
      · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hψ
        exact n2 k
    have p1 := prod_fibre φ ε (fun ψ => Φ.fr (J ψ) (π ψ)) s
      (fun k => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))) hf
    have p2 := prod_fibre φ' ε' (fun ψ => Φ.fr (J ψ) (π ψ)) s
      (fun k => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))) hf
    have p3 : ∏ k, Φ.fr (J (φ k)) (π (φ k)) ^ ε k = ∏ k, Φ.fr (J (φ' k)) (π (φ' k)) ^ ε' k := by
      refine p1.trans (Eq.trans ?_ p2.symm)
      refine Finset.prod_congr rfl fun ψ _ => ?_
      congr 1
      exact hs ψ
    simp only [hπ, hπ'] at e
    rw [p3] at e
    exact mul_right_cancel₀ (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (n2 k)) e
  · rintro (k | k)
    · exact h.1 k
    · exact h'.1 k
  · intro j hj
    have hj0 := (chart_iff L.L _ j q).1 hj
    have e1 := h.2 (j ∘ Sum.inl) ((chart_iff L.L φ _ q).2 fun k => hj0 (Sum.inl k))
    have e2 := h'.2 (j ∘ Sum.inr) ((chart_iff L.L φ' _ q).2 fun k => hj0 (Sum.inr k))
    refine (ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_mul q _ _ _).trans ?_
    refine (congrArg₂ (· * ·) ((vtf_val_res q _ hj _).trans e1) ((vtf_val_res q _ hj _).trans e2)).trans ?_
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
    ring
  · intro j hj
    have e1 := h.2 j hj
    have e2 := val_inv q hj (t.s j)
    refine e2.trans ?_
    refine (congrArg (·⁻¹) e1).trans ?_
    simp only [mul_inv, zpow_neg, Finset.prod_inv_distrib]

end GlobalTheory.AnValGenCorr
