import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRootInvolutionParabolicStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjectionEraseRootFormulaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GramRootDeterminantEraseStatement

open GlobalTheory.Chamber Finset
open scoped InnerProductSpace ContDiff Classical

noncomputable section
namespace GlobalTheory.Chamber.ResM
variable {k : ℕ}

def flipOf (W : Finset (SV k)) : SV k → SV k :=
  if h : IsPar W then Classical.choose (GlobalTheory.T.exists_root_involution_parabolic W h) else id

theorem flipOf_spec {W : Finset (SV k)} (h : IsPar W) {u : SV k} (hu : u ∉ W) (hp : IsPar (insert u W)) :
    flipOf W u ∉ W ∧ flipOf W u ≠ u ∧ IsPar (insert (flipOf W u) W) ∧ vec u + vec (flipOf W u) ∈ aP W ∧
      flipOf W (flipOf W u) = u := by
  simp only [flipOf, dif_pos h]
  exact Classical.choose_spec (GlobalTheory.T.exists_root_involution_parabolic W h) u hu hp

theorem vecSpan_insert_eq_of_add_mem {W : Finset (SV k)} {u u' : SV k} (h : vec u + vec u' ∈ aP W) :
    aP (insert u' W) = aP (insert u W) := by
  have key : ∀ a, aP (insert a W) = Submodule.span ℝ {vec a} ⊔ aP W := fun a => by
    rw [aP, coe_insert, Set.image_insert_eq, Submodule.span_insert]; rfl
  rw [key, key]
  have h1 : vec u' ∈ Submodule.span ℝ {vec u} ⊔ aP W := by
    rw [show vec u' = (vec u + vec u') - vec u by abel]
    exact sub_mem (Submodule.mem_sup_right h) (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
  have h2 : vec u ∈ Submodule.span ℝ {vec u'} ⊔ aP W := by
    rw [show vec u = (vec u + vec u') - vec u' by abel]
    exact sub_mem (Submodule.mem_sup_right h) (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
  exact le_antisymm (sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 h1) le_sup_right)
    (sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 h2) le_sup_right)

theorem rt_flip {W : Finset (SV k)} {u u' : SV k} (hu : u ∉ W) (hu' : u' ∉ W) (h : vec u + vec u' ∈ aP W) :
    rt (insert u' W) u' = - rt (insert u W) u := by
  have hy : pr W (vec u + vec u') = vec u + vec u' := Submodule.starProjection_eq_self_iff.2 h
  rw [map_add] at hy
  simp only [rt, wt, erase_insert hu, erase_insert hu']
  rw [neg_sub, sub_eq_sub_iff_add_eq_add, hy, add_comm]

theorem erase_sdiff_eq (P Q : Finset (SV k)) (u : SV k) : (P \ Q).erase u = P.erase u \ Q := by
  ext v; simp only [mem_erase, mem_sdiff]; tauto

def term (Q : Finset (SV k)) (c : Finset (SV k) → A0 k → ℂ) (b x : A0 k) (P : Finset (SV k)) (u : SV k) : ℂ :=
  ((√(Matrix.gram ℝ fun v : ↥(P \ Q) => rt P v).det : ℝ) : ℂ) * (∏ _v ∈ P \ Q, Complex.I)⁻¹ * c P x *
      ((⟪rt P u, b⟫_ℝ : ℂ)⁻¹ * ∏ v ∈ (P \ Q).erase u, (⟪x, rt P v⟫_ℝ : ℂ)⁻¹)

def wallFac (Q W : Finset (SV k)) (x : A0 k) : ℝ :=
  √(Matrix.gram ℝ fun v : ↥(W \ Q) => rt W v).det * ∏ v ∈ W \ Q, (⟪x, rt W v⟫_ℝ)⁻¹

theorem term_eq {𝔞 : Submodule ℝ (A0 k)} {Q : Finset (SV k)} {c : Finset (SV k) → A0 k → ℂ} (hc : IsGMFam 𝔞 c)
    {b x : A0 k} {P : Finset (SV k)} (hP : P ∈ parP 𝔞 Q) {u : SV k} (hu : u ∈ P \ Q) (hx : ⟪x, rt P u⟫_ℝ = 0) :
    term Q c b x P u = ((wallFac Q (P.erase u) x : ℝ) : ℂ) * ((‖rt P u‖ : ℝ) : ℂ) *
      (Complex.I ^ ((P.erase u \ Q).card + 1))⁻¹ * c (P.erase u) x * ((⟪rt P u, b⟫_ℝ : ℝ) : ℂ)⁻¹ := by
  obtain ⟨hPp, hPa, -⟩ := mem_parP.1 hP
  have huP := (mem_sdiff.1 hu).1
  have hF : P ∈ parF 𝔞 ∅ := mem_parF.2 ⟨hPp, hPa.le, empty_subset _⟩
  have hs : (P \ Q).erase u ⊆ P.erase u := erase_subset_erase _ sdiff_subset
  have hR := GlobalTheory.T.gram_root_determinant_erase ((P \ Q).erase u) hPp huP hs x hx
  rw [insert_erase hu, erase_sdiff_eq] at hR
  have hpr : pr P x = pr (P.erase u) x := by
    rw [GlobalTheory.T.projection_erase_root_formula hPp huP x, real_inner_comm, hx, zero_div, zero_smul, add_zero]
  have hcP : c P x = c (P.erase u) x := by
    rw [(hc P hF).2 P subset_rfl x, hpr, ← (hc P hF).2 _ (erase_subset _ _) x]
  have hcard : (P \ Q).card = (P.erase u \ Q).card + 1 := by
    rw [← card_erase_add_one hu, erase_sdiff_eq]
  have hR' := congrArg (fun t : ℝ => (t : ℂ)) hR
  simp only [wallFac] at hR' ⊢
  push_cast at hR' ⊢
  rw [term, hcP, prod_const, hcard, erase_sdiff_eq]
  linear_combination (Complex.I ^ ((P.erase u \ Q).card + 1))⁻¹ * c (P.erase u) x * ((⟪rt P u, b⟫_ℝ : ℂ))⁻¹ * hR'

theorem flip_facts {𝔞 : Submodule ℝ (A0 k)} {Q P : Finset (SV k)} (hP : P ∈ parP 𝔞 Q) {u : SV k} (hu : u ∈ P \ Q) :
    insert (flipOf (P.erase u) u) (P.erase u) ∈ parP 𝔞 Q ∧
      flipOf (P.erase u) u ∈ insert (flipOf (P.erase u) u) (P.erase u) \ Q ∧
      rt (insert (flipOf (P.erase u) u) (P.erase u)) (flipOf (P.erase u) u) = - rt P u ∧
      (insert (flipOf (P.erase u) u) (P.erase u)).erase (flipOf (P.erase u) u) = P.erase u ∧
      flipOf (P.erase u) u ≠ u ∧ flipOf (P.erase u) (flipOf (P.erase u) u) = u := by
  obtain ⟨hPp, hPa, hQ⟩ := mem_parP.1 hP
  obtain ⟨huP, huQ⟩ := mem_sdiff.1 hu
  have hQW : Q ⊆ P.erase u := fun v hv => mem_erase.2 ⟨fun e => huQ (e ▸ hv), hQ hv⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := flipOf_spec (hPp.mono (erase_subset u P)) (notMem_erase u P)
    ((insert_erase huP).symm ▸ hPp)
  refine ⟨mem_parP.2 ⟨h3, ?_, hQW.trans (subset_insert _ _)⟩, mem_sdiff.2 ⟨mem_insert_self _ _, fun h => h1 (hQW h)⟩,
    ?_, erase_insert h1, h2, h5⟩
  · rw [vecSpan_insert_eq_of_add_mem h4, insert_erase huP, hPa]
  · rw [rt_flip (notMem_erase u P) h1 h4, insert_erase huP]

theorem residues_cancel {k : ℕ} (𝔞 : Submodule ℝ (A0 k)) (c : Finset (SV k) → A0 k → ℂ) (hc : IsGMFam 𝔞 c)
    (Q : Finset (SV k)) (_hQ : Q ∈ parF 𝔞 ∅) (b : A0 k) (_hb : b ≠ 0) (x : A0 k) (hx : ⟪x, b⟫_ℝ = 0) :
    ∑ P ∈ parP 𝔞 Q, ∑ u ∈ (P \ Q).filter (fun u => ∃ r : ℝ, rt P u = r • b),
      ((√(Matrix.gram ℝ fun v : ↥(P \ Q) => rt P v).det : ℝ) : ℂ) * (∏ _v ∈ P \ Q, Complex.I)⁻¹ * c P x *
        ((⟪rt P u, b⟫_ℝ : ℂ)⁻¹ * ∏ v ∈ (P \ Q).erase u, (⟪x, rt P v⟫_ℝ : ℂ)⁻¹) = 0 := by
  change ∑ P ∈ parP 𝔞 Q, ∑ u ∈ (P \ Q).filter (fun u => ∃ r : ℝ, rt P u = r • b), term Q c b x P u = 0
  rw [sum_sigma']
  refine sum_involution
    (fun a _ => ⟨insert (flipOf (a.1.erase a.2) a.2) (a.1.erase a.2), flipOf (a.1.erase a.2) a.2⟩) ?_ ?_ ?_ ?_
  · rintro ⟨P, u⟩ ha
    obtain ⟨hP, hu⟩ := mem_sigma.1 ha
    obtain ⟨hu, r, hr⟩ := mem_filter.1 hu
    obtain ⟨h1, h2, h3, h4, -, -⟩ := flip_facts hP hu
    dsimp only at *
    have hx' : ⟪x, rt P u⟫_ℝ = 0 := by rw [hr, inner_smul_right, hx, mul_zero]
    rw [term_eq hc hP hu hx', term_eq hc h1 h2 (by rw [h3, inner_neg_right, hx', neg_zero]), h3, h4, norm_neg,
      inner_neg_left]
    push_cast
    rw [inv_neg]
    ring
  · rintro ⟨P, u⟩ ha _ e
    obtain ⟨hP, hu⟩ := mem_sigma.1 ha
    obtain ⟨-, -, -, -, h5, -⟩ := flip_facts hP (mem_filter.1 hu).1
    exact h5 (congrArg (fun a : (_ : Finset (SV k)) × SV k => a.2) e)
  · rintro ⟨P, u⟩ ha
    obtain ⟨hP, hu⟩ := mem_sigma.1 ha
    obtain ⟨hu, r, hr⟩ := mem_filter.1 hu
    obtain ⟨h1, h2, h3, -, -, -⟩ := flip_facts hP hu
    exact mem_sigma.2 ⟨h1, mem_filter.2 ⟨h2, -r, by rw [h3, hr, neg_smul]⟩⟩
  · rintro ⟨P, u⟩ ha
    obtain ⟨hP, hu⟩ := mem_sigma.1 ha
    have hu' := (mem_filter.1 hu).1
    obtain ⟨-, -, -, h4, -, h6⟩ := flip_facts hP hu'
    dsimp only at *
    rw [h4, h6, insert_erase (mem_sdiff.1 hu').1]

end GlobalTheory.Chamber.ResM
