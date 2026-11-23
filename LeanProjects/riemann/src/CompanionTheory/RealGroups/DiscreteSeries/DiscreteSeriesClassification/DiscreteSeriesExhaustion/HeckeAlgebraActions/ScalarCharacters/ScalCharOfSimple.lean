import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable

noncomputable section

namespace CompanionTheory.RgExh.Hk

open Formalism.REAL (GlRel qdet)

variable {n : ℕ}

private theorem eq_zero_of_pow_eq_zero_of_commute_of_isSimple {X : GMod n} (hS : IsSimple X) (N : Module.End ℂ X.V)
    (hc : ∀ a b, Commute (X.E a b) N) (k : ℕ) (hk : N ^ k = 0) : N = 0 := by
  have hker : ∀ a b, ∀ x ∈ LinearMap.ker N, X.E a b x ∈ LinearMap.ker N := by
    intro a b x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← Module.End.mul_apply, ← (hc a b).eq, Module.End.mul_apply, hx, map_zero]
  rcases hS.2 (LinearMap.ker N) hker with h | h
  · exfalso
    have hinj : Function.Injective N := LinearMap.ker_eq_bot.1 h
    have hinjk : Function.Injective ⇑(N ^ k) := by
      rw [Module.End.coe_pow]
      exact hinj.iterate k
    obtain ⟨x, y, hxy⟩ := hS.1.exists_pair_ne
    apply hxy
    apply hinjk
    simp [hk]
  · exact LinearMap.ker_eq_top.1 h

theorem scalChar_of_simple (hQ : QdetEq) {X : GMod n} {χ : Fin n → ℂ} (hS : IsSimple X) (hH : HasChar X χ) :
    ScalChar X χ := by
  unfold CompanionTheory.RgExh.ScalChar
  obtain ⟨k, hk⟩ := hH
  intro Y
  rw [← sub_eq_zero]
  refine eq_zero_of_pow_eq_zero_of_commute_of_isSimple hS _ (fun a b => ?_) k (hk Y)
  have hc : Commute (X.E a b) (Formalism.REAL.qdet X.E (Y + ((n : ℂ) - 1) / 2)) := by
    rw [hQ n X.V X.E (Y + ((n : ℂ) - 1) / 2)]
    exact ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.capelliC_central X.E X.gl _ a b
  exact hc.sub_right ((Commute.one_right _).smul_right _)

theorem nontrivial_step (hV : NonVan) {X : GMod n} {χ : Fin n → ℂ} {s : Fin n} (hH : HasChar X χ)
    (hN : Nontrivial X.V) (hf : ∀ r, χ r ≠ χ s + 1) : Nontrivial (step X (χ s)).V := by
  have h := hV n X χ s hH hN hf
  show Nontrivial ↥(stepSub X (χ s))
  exact (Submodule.nontrivial_iff_ne_bot).2 h

theorem backPath (hC : StepChar) (hV : NonVan) (hNS : NonScal) (hB : Back) :
    ∀ (ss : List (Fin n)) (X : GMod n) (χ : Fin n → ℂ), GoodPath χ ss → HasChar X χ → Nontrivial X.V →
      ScalChar (path X χ ss) (pathEnd χ ss) → ScalChar X χ ∧ SimplePath χ ss := by
  intro ss
  induction ss with
  | nil =>
    intro X χ _ _ _ hS
    change ScalChar X χ at hS
    refine ⟨hS, ?_⟩
    change True
    trivial
  | cons s ss ih =>
    intro X χ hG hH hN hS
    change (∀ r, χ r ≠ χ s + 1) ∧ GoodPath (χ + Pi.single s 1) ss at hG
    change ScalChar (path (step X (χ s)) (χ + Pi.single s 1) ss) (pathEnd (χ + Pi.single s 1) ss) at hS
    obtain ⟨hf, hG'⟩ := hG
    have hH' := hC n X χ s hH
    have hN' := nontrivial_step hV hH hN hf
    obtain ⟨hS1, hSP⟩ := ih (step X (χ s)) (χ + Pi.single s 1) hG' hH' hN' hS
    obtain ⟨hSX, hom⟩ := hB n X χ s hH hf hS1
    refine ⟨hSX, ?_⟩
    change (∀ r, r ≠ s → χ r ≠ χ s) ∧ SimplePath (χ + Pi.single s 1) ss
    refine ⟨?_, hSP⟩
    intro r hrs heq
    obtain ⟨f, hf1, hf2⟩ := hNS n X χ s hSX hN hf ⟨r, hrs, heq⟩
    exact hf2 (hom f hf1)

theorem fwdPath (hQ : QdetEq) (hC : StepChar) (hOS : OmScal) (hF : FwdSimple) (hR : Reflect) :
    ∀ (ss : List (Fin n)) (X : GMod n) (χ : Fin n → ℂ), GoodPath χ ss → SimplePath χ ss → IsSimple X →
      HasChar X χ → IsSimple (path X χ ss) ∧
        ∀ X' : GMod n, IsSimple X' → HasChar X' χ → Iso (path X χ ss) (path X' χ ss) → Iso X X' := by
  intro ss
  induction ss with
  | nil =>
    intro X χ _ _ hS _
    refine ⟨?_, fun X' _ _ hI => ?_⟩
    · change IsSimple X
      exact hS
    · change Iso X X' at hI
      exact hI
  | cons s ss ih =>
    intro X χ hG hSP hS hH
    change (∀ r, χ r ≠ χ s + 1) ∧ GoodPath (χ + Pi.single s 1) ss at hG
    change (∀ r, r ≠ s → χ r ≠ χ s) ∧ SimplePath (χ + Pi.single s 1) ss at hSP
    obtain ⟨hf, hG'⟩ := hG
    obtain ⟨hd, hSP'⟩ := hSP
    have hSc := scalChar_of_simple hQ hS hH
    have hS1 : IsSimple (step X (χ s)) := hF n X χ s hS hSc hf hd (hOS n X χ s hSc hd)
    have hH1 := hC n X χ s hH
    obtain ⟨hP, hRefl⟩ := ih (step X (χ s)) (χ + Pi.single s 1) hG' hSP' hS1 hH1
    refine ⟨?_, fun X' hS' hH' hI => ?_⟩
    · change IsSimple (path (step X (χ s)) (χ + Pi.single s 1) ss)
      exact hP
    · change Iso (path (step X (χ s)) (χ + Pi.single s 1) ss) (path (step X' (χ s)) (χ + Pi.single s 1) ss) at hI
      have hSc' := scalChar_of_simple hQ hS' hH'
      have hS1' : IsSimple (step X' (χ s)) := hF n X' χ s hS' hSc' hf hd (hOS n X' χ s hSc' hd)
      have hI1 := hRefl (step X' (χ s)) hS1' (hC n X' χ s hH') hI
      exact hR n X X' χ s hSc hSc' hf hd hI1

theorem hecke_of' (hQ : QdetEq) (hC : StepChar) (_hCH : CayleyHam) (hV : NonVan) (hNS : NonScal) (hB : Back)
    (hOS : OmScal) (hF : FwdSimple) (hR : Reflect) : Hecke := by
  unfold CompanionTheory.RgExh.Hecke
  intro m X χ ss hG hS hH hSc
  have hb := backPath hC hV hNS hB ss X χ hG hH hS.1 hSc
  have hf := fwdPath hQ hC hOS hF hR ss X χ hG hb.2 hS hH
  exact ⟨hb.2, hf.1, hf.2⟩

end CompanionTheory.RgExh.Hk
