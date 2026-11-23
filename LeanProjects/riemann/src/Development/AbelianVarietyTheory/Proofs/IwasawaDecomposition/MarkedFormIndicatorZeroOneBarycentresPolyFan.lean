import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkValEqZeroOrOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMarkedBalancedIntFormPullbackIffSplitSurjectioStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormIndicatorValueInvariantHostFixingAutStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanMarkedFormUniqueInCellStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanExistsMarkedFormInCellStatement

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan.Mark

theorem exists_markFun {O : Type} [CommRing O] (bar : O → O) (ψ lab : InvFun O) (i : ℕ) :
    ∃ w : InvFun O, ∀ n B, w.toFun n B = markVal bar ψ lab i n B := by
  classical
  refine ⟨{ toFun := markVal bar ψ lab i, inv := ?_, zero := ?_ }, fun _ _ => rfl⟩
  · intro n m r hr B
    obtain ⟨s, hs⟩ := Module.projective_lifting_property r LinearMap.id hr
    have hrs : ∀ a, r (s a) = a := fun a => LinearMap.congr_fun hs a
    unfold markVal
    by_cases h : ∃ β : LinearMap.BilinForm ℤ (Fin m → O), ∀ a b, B a b = β a b
    · have h' : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b, B (r a) (r b) = β a b :=
        ⟨pull r h.choose, fun a b => h.choose_spec _ _⟩
      rw [dif_pos h, dif_pos h']
      have e : h'.choose = pull r h.choose := LinearMap.ext₂ fun a b => by
        have h1 := h'.choose_spec a b
        have h2 := h.choose_spec (r a) (r b)
        rw [pull_apply]
        exact_mod_cast h1.symm.trans h2
      rw [e, GlobalTheory.T.isMarkedBalancedIntForm_pullback_iff_splitSurjection O bar ψ lab i _ _ r s hrs]
    · have h' : ¬ ∃ β : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b, B (r a) (r b) = β a b := by
        rintro ⟨β, h3⟩
        exact h ⟨pull s β, fun a b => by rw [pull_apply, ← h3, hrs, hrs]⟩
      rw [dif_neg h, dif_neg h']
  · intro B
    unfold markVal
    split_ifs with h h2
    · exfalso
      have := h2.2.2.2.1
      rw [InvFun.evalZ, lab.eval_of_subsingleton] at this
      exact absurd this (by positivity)
    · rfl
    · rfl

open Classical in

theorem evalZ_markFun {O : Type} [CommRing O] {bar : O → O} {ψ lab : InvFun O} {i : ℕ} {w : InvFun O}
    (hw : ∀ n B, w.toFun n B = markVal bar ψ lab i n B) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    [Module.Projective O X] (β : LinearMap.BilinForm ℤ X) :
    w.evalZ β = if IsMarked bar ψ lab i X β then 1 else 0 := by
  classical
  obtain ⟨n, t, ht⟩ := Module.Finite.exists_fin' O X
  obtain ⟨u, hu⟩ := Module.projective_lifting_property t LinearMap.id ht
  have htu : ∀ a, t (u a) = a := fun a => LinearMap.congr_fun hu a
  rw [InvFun.evalZ, w.eval_eq ht, hw]
  have e := markVal_int (bar := bar) (ψ := ψ) (lab := lab) (i := i) n (pull t β)
  simp only [pull_apply] at e
  rw [e, GlobalTheory.T.isMarkedBalancedIntForm_pullback_iff_splitSurjection O bar ψ lab i _ _ t u htu]

theorem exists_markFun_props : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab : InvFun (𝓞 E)) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → IsTwInv H lab → IsCarrierDim H.bar q ψ lab → ∃ w : InvFun (𝓞 E), IsTwInv H w ∧ ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 0 ∨ w.evalZ β = 1) ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1) ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → lab.evalZ β = ((i + 1 : ℕ) : ℝ)) ∧ (∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ v → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms H.bar X, (∀ y, 0 ≤ β' y y) → w.evalZ β = 1 → w.evalZ β' = 1 → InRCone v β → InRCone v β' → β = β') ∧ (∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ v → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β = ((i + 1 : ℕ) : ℝ) → ∃ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) ∧ w.evalZ β₀ = 1 ∧ InRCone v β₀) := by
  intro E _ _ _ H q ψ lab i hD hψ htψ htlab hlab
  classical
  obtain ⟨w, hw⟩ := exists_markFun H.bar ψ lab i
  have ev := fun {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X]
    (β : LinearMap.BilinForm ℤ X) => evalZ_markFun hw (X := X) β
  have mk : ∀ {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X]
      (β : LinearMap.BilinForm ℤ X), w.evalZ β = 1 → IsMarked H.bar ψ lab i X β := fun β h => by
    rw [ev] at h
    split_ifs at h with h'
    · exact h'
    · norm_num at h
  refine ⟨w, fun σ hσ n B => by rw [hw, hw]; exact GlobalTheory.T.markedFormIndicatorValue_invariant_hostFixingAut E H ψ lab i htψ htlab σ hσ n B, ?_⟩
  intro X _ _ _ _ hX
  refine ⟨fun β _ _ => ?_, fun β _ _ h1 => (mk β h1).2.2.1, fun β _ _ h1 => (mk β h1).2.2.2.1,
    fun m v hv hle β _ _ β' _ _ h1 h1' hc hc' =>
      GlobalTheory.T.polFan_marked_form_unique_in_cell E H q ψ lab i hD hψ hlab X hX m v hv hle β β' (mk β h1) (mk β' h1') hc hc',
    fun m v hv β hβ hp hc hl => ?_⟩
  · rw [ev]
    split_ifs <;> simp
  · obtain ⟨β₀, h0, hc0⟩ := GlobalTheory.T.polFan_exists_marked_form_in_cell E H q ψ lab i hD hψ hlab X hX m v hv β hβ hp hc hl
    exact ⟨β₀, h0.1, h0.2.1, by rw [ev, if_pos h0], hc0⟩

end GlobalTheory.PolFan.Mark
