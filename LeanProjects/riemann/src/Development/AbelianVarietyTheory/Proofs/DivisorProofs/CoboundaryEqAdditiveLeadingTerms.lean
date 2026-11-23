import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstLeadingOfAgreeDegreeOneStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

namespace GlobalTheory.CobLead

open CategoryTheory TensorProduct MvPowerSeries in
set_option autoImplicit false in
private lemma subst_constantCoeff_zero_and_linear_coeff_eq {R : Type} [CommRing R] {d : ℕ} {τ : Type}
    (w : Fin d ⊕ Fin d → MvPowerSeries τ R) (hw : ∀ s, constantCoeff (w s) = 0)
    (F G : MvPowerSeries (Fin d ⊕ Fin d) R)
    (hFG : ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree ≤ 1 → coeff α F = coeff α G)
    (hG : constantCoeff G = 0) :
    constantCoeff (subst w F) = 0 ∧ constantCoeff (subst w G) = 0 ∧
      ∀ γ : τ →₀ ℕ, γ.degree = 1 → coeff γ (subst w F) = coeff γ (subst w G) := by
  have hlow : ∀ H : MvPowerSeries (Fin d ⊕ Fin d) R, (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < 1 → coeff α H = 0) →
      constantCoeff (subst w H) = 0 := by
    intro H hH
    have h := (_root_.GlobalTheory.coeff_subst_leading R _ τ w w 1 H hw hw (fun _ _ _ => rfl) hH 0).1
      (by simp)
    rwa [coeff_zero_eq_constantCoeff_apply] at h
  have hG0 : ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < 1 → coeff α G = 0 := by
    intro α hα
    have : α = 0 := (Finsupp.degree_eq_zero_iff α).mp (by omega)
    rw [this, coeff_zero_eq_constantCoeff_apply, hG]
  refine ⟨hlow F (fun α hα => by rw [hFG α hα.le]; exact hG0 α hα), hlow G hG0, ?_⟩
  intro γ hγ
  have hdiff := (_root_.GlobalTheory.coeff_subst_leading R _ τ w w 2 (F - G) hw hw (fun _ _ _ => rfl)
    (fun α hα => by rw [map_sub, hFG α (by omega), sub_self]) γ).1 (by omega)
  rw [subst_sub (hasSubst_of_constantCoeff_zero hw), map_sub, sub_eq_zero] at hdiff
  exact hdiff

open CategoryTheory TensorProduct MvPowerSeries in
set_option autoImplicit false in
theorem _root_.GlobalTheory.CobLead.cob_eq_additive_lead : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (N : ℕ), (∀ i (α : Fin d ⊕ Fin d →₀ ℕ), α.degree ≤ 1 → coeff α (μ i) = coeff α (_root_.GlobalTheory.Katz.addLaw R d i)) → (∀ f : MvPowerSeries (Fin d) R, (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α f = 0) → ∀ γ : Fin d ⊕ Fin d →₀ ℕ, (γ.degree < N → coeff γ (_root_.GlobalTheory.Katz.cob1 μ f) = 0) ∧ (γ.degree ≤ N → coeff γ (_root_.GlobalTheory.Katz.cob1 μ f) = coeff γ (_root_.GlobalTheory.Katz.cob1 (_root_.GlobalTheory.Katz.addLaw R d) f))) ∧ ∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < N → coeff α c = 0) → ∀ γ : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, γ.degree ≤ N → coeff γ (_root_.GlobalTheory.Katz.cob2 μ c) = coeff γ (_root_.GlobalTheory.Katz.cob2 (_root_.GlobalTheory.Katz.addLaw R d) c) := by
  intro R _ d μ N hμ
  have hadd0 : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.addLaw R d i) = 0 := by
    intro i
    simp [_root_.GlobalTheory.Katz.addLaw]
  have hμ0 : ∀ i, constantCoeff (μ i) = 0 := by
    intro i
    rw [← coeff_zero_eq_constantCoeff_apply, hμ i 0 (by simp), coeff_zero_eq_constantCoeff_apply, hadd0]
  have hX : ∀ {ι κ : Type} (e : ι → κ) (s : ι), constantCoeff (X (e s) : MvPowerSeries κ R) = 0 :=
    fun _ _ => by simp
  refine ⟨fun f hf γ => ⟨fun hγ => ?_, fun hγ => ?_⟩, fun c hc γ hγ => ?_⟩
  · unfold _root_.GlobalTheory.Katz.cob1 _root_.GlobalTheory.Katz.inL _root_.GlobalTheory.Katz.inR
    rw [map_sub, map_sub,
      (_root_.GlobalTheory.coeff_subst_leading R _ _ μ μ N f hμ0 hμ0 (fun _ _ _ => rfl) hf γ).1 hγ,
      (_root_.GlobalTheory.coeff_subst_leading R _ _ _ _ N f (hX Sum.inl) (hX Sum.inl)
        (fun _ _ _ => rfl) hf γ).1 hγ,
      (_root_.GlobalTheory.coeff_subst_leading R _ _ _ _ N f (hX Sum.inr) (hX Sum.inr)
        (fun _ _ _ => rfl) hf γ).1 hγ]
    simp
  · unfold _root_.GlobalTheory.Katz.cob1
    rw [map_sub, map_sub, map_sub, map_sub,
      (_root_.GlobalTheory.coeff_subst_leading R _ _ μ (_root_.GlobalTheory.Katz.addLaw R d) N f hμ0 hadd0
        (fun i γ' hγ' => hμ i γ' hγ'.le) hf γ).2 hγ]
  · have hpts : ∀ {τ : Type} (a b : Fin d → MvPowerSeries τ R), (∀ s, constantCoeff (a s) = 0) →
        (∀ s, constantCoeff (b s) = 0) → ∀ i,
          constantCoeff (_root_.GlobalTheory.Katz.op μ a b i) = 0 ∧
          constantCoeff (_root_.GlobalTheory.Katz.op (_root_.GlobalTheory.Katz.addLaw R d) a b i) = 0 ∧
          ∀ γ' : τ →₀ ℕ, γ'.degree = 1 → coeff γ' (_root_.GlobalTheory.Katz.op μ a b i) =
            coeff γ' (_root_.GlobalTheory.Katz.op (_root_.GlobalTheory.Katz.addLaw R d) a b i) := by
      intro τ a b ha hb i
      exact subst_constantCoeff_zero_and_linear_coeff_eq (Sum.elim a b) (fun s => by cases s <;> simp [ha, hb])
        (μ i) (_root_.GlobalTheory.Katz.addLaw R d i) (hμ i) (hadd0 i)
    have hs1 : ∀ s, constantCoeff (_root_.GlobalTheory.Katz.x1 (R := R) (d := d) s) = 0 := fun s => by
      simp [_root_.GlobalTheory.Katz.x1]
    have hs2 : ∀ s, constantCoeff (_root_.GlobalTheory.Katz.x2 (R := R) (d := d) s) = 0 := fun s => by
      simp [_root_.GlobalTheory.Katz.x2]
    have hs3 : ∀ s, constantCoeff (_root_.GlobalTheory.Katz.x3 (R := R) (d := d) s) = 0 := fun s => by
      simp [_root_.GlobalTheory.Katz.x3]
    have h12 := hpts _ _ hs1 hs2
    have h23 := hpts _ _ hs2 hs3
    unfold _root_.GlobalTheory.Katz.cob2 _root_.GlobalTheory.Katz.at2
    rw [map_sub, map_add, map_sub, map_sub, map_add, map_sub,
      (_root_.GlobalTheory.coeff_subst_leading R _ _
        (Sum.elim (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x1 _root_.GlobalTheory.Katz.x2)
          _root_.GlobalTheory.Katz.x3)
        (Sum.elim (_root_.GlobalTheory.Katz.op (_root_.GlobalTheory.Katz.addLaw R d) _root_.GlobalTheory.Katz.x1
          _root_.GlobalTheory.Katz.x2) _root_.GlobalTheory.Katz.x3) N c
        (fun s => by rcases s with s | s; exacts [(h12 s).1, hs3 s])
        (fun s => by rcases s with s | s; exacts [(h12 s).2.1, hs3 s])
        (fun s γ' hγ' => by rcases s with s | s; exacts [(h12 s).2.2 γ' hγ', rfl]) hc γ).2 hγ,
      (_root_.GlobalTheory.coeff_subst_leading R _ _
        (Sum.elim _root_.GlobalTheory.Katz.x1
          (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x2 _root_.GlobalTheory.Katz.x3))
        (Sum.elim _root_.GlobalTheory.Katz.x1 (_root_.GlobalTheory.Katz.op (_root_.GlobalTheory.Katz.addLaw R d)
          _root_.GlobalTheory.Katz.x2 _root_.GlobalTheory.Katz.x3)) N c
        (fun s => by rcases s with s | s; exacts [hs1 s, (h23 s).1])
        (fun s => by rcases s with s | s; exacts [hs1 s, (h23 s).2.1])
        (fun s γ' hγ' => by rcases s with s | s; exacts [rfl, (h23 s).2.2 γ' hγ']) hc γ).2 hγ]

end GlobalTheory.CobLead
