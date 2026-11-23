import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLiftAt
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem isotIn_detect_by_eqv_map : ∀ (D : D7) {n : ℕ} (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (π : NG.FinTyp D.host.E n) (y : A), y ∈ principalLevelFrame.isotIn ρ C π → y ≠ 0 → ∃ q : A →ₗ[ℂ] (GAf D.host.E n → ℂ), q y ≠ 0 ∧ ∀ z ∈ principalLevelFrame.isotIn ρ C π, q z ∈ π.S ∧ ∀ h, q (ρ h z) = NG.rt D.host.E n h (q z) := by
  intro D n A _ _ ρ C π y hy hy0
  let St : Submodule ℂ A → Prop := fun K => ∀ h, ∀ x ∈ K, ρ h x ∈ K
  have rangeSt : ∀ Φ : π.S →ₗ[ℂ] A, principalLevelFrame.IsEqvA ρ π Φ → St (LinearMap.range Φ) := by
    rintro Φ hΦ h _ ⟨f, rfl⟩
    exact ⟨_, hΦ h f⟩
  have rangeLe : ∀ Φ : π.S →ₗ[ℂ] A, principalLevelFrame.IsEqvA ρ π Φ → LinearMap.range Φ ≤ C →
      LinearMap.range Φ ≤ principalLevelFrame.isotIn (D := D) ρ C π := fun Φ hΦ hC =>
    le_iSup₂ (f := fun (Ψ : π.S →ₗ[ℂ] A) (_ : principalLevelFrame.IsEqvA ρ π Ψ ∧ LinearMap.range Ψ ≤ C) => LinearMap.range Ψ) Φ ⟨hΦ, hC⟩
  have supSt : ∀ K1 K2 : Submodule ℂ A, St K1 → St K2 → St (K1 ⊔ K2) := by
    intro K1 K2 h1 h2 h x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]; exact Submodule.add_mem_sup (h1 h a ha) (h2 h b hb)
  have atom : ∀ K : Submodule ℂ A, St K → ∀ Φ : π.S →ₗ[ℂ] A, principalLevelFrame.IsEqvA ρ π Φ →
      LinearMap.range Φ ≤ K ∨ ∀ f, Φ f ∈ K → f = 0 := by
    intro K hK Φ hΦ
    rcases π.irr ((K.comap Φ).map π.S.subtype) (by
        rintro _ ⟨f, -, rfl⟩; exact f.2)
      (by
        rintro h _ ⟨f, hf, rfl⟩
        refine ⟨⟨NG.rt D.host.E n h f, π.stable h f f.2⟩, ?_, rfl⟩
        show Φ _ ∈ K
        rw [hΦ h f]; exact hK h _ hf) with h0 | h1
    · right; intro f hf
      have : (f : GAf D.host.E n → ℂ) ∈ (K.comap Φ).map π.S.subtype := ⟨f, hf, rfl⟩
      rw [h0] at this
      exact Subtype.ext ((Submodule.mem_bot ℂ).1 this)
    · left; rintro _ ⟨f, rfl⟩
      have : (f : GAf D.host.E n → ℂ) ∈ (K.comap Φ).map π.S.subtype := by rw [h1]; exact f.2
      obtain ⟨f', hf', he⟩ := this
      have : f' = f := Subtype.ext he
      subst this; exact hf'
  obtain ⟨K, hKmax⟩ := zorn_le₀ {K : Submodule ℂ A | K ≤ principalLevelFrame.isotIn (D := D) ρ C π ∧ St K ∧ y ∉ K} (by
    intro c hc hch
    rcases c.eq_empty_or_nonempty with rfl | hne
    · refine ⟨⊥, ⟨bot_le, fun h x hx => ?_, fun h => hy0 ((Submodule.mem_bot ℂ).1 h)⟩, by simp⟩
      rw [(Submodule.mem_bot ℂ).1 hx, map_zero]; exact zero_mem _
    · refine ⟨sSup c, ⟨sSup_le fun K hK => (hc hK).1, ?_, ?_⟩, fun K hK => le_sSup hK⟩
      · intro h x hx
        have : sSup c ≤ (sSup c).comap (ρ h) := sSup_le fun K hK z hz => le_sSup hK ((hc hK).2.1 h z hz)
        exact this hx
      · intro hyc
        obtain ⟨K, hK, hyK⟩ := (Submodule.mem_sSup_of_directed hne hch.directedOn).1 hyc
        exact (hc hK).2.2 hyK)
  obtain ⟨⟨hKN, hKSt, hyK⟩, hKm⟩ := hKmax
  have grow : ∀ K' : Submodule ℂ A, K' ≤ principalLevelFrame.isotIn (D := D) ρ C π → St K' → K ≤ K' → ¬ K' ≤ K → y ∈ K' :=
    fun K' h1 h2 h3 h4 => by
      by_contra hyK'; exact h4 (hKm ⟨h1, h2, hyK'⟩ h3)
  obtain ⟨Φ, ⟨hΦ, hΦC⟩, hΦK⟩ : ∃ Φ : π.S →ₗ[ℂ] A, (principalLevelFrame.IsEqvA ρ π Φ ∧ LinearMap.range Φ ≤ C) ∧
      ¬ LinearMap.range Φ ≤ K := by
    by_contra hcon
    push_neg at hcon
    exact hyK ((iSup₂_le fun Φ hΦ => hcon Φ hΦ : principalLevelFrame.isotIn (D := D) ρ C π ≤ K) hy)
  have hΦK' : ∀ f, Φ f ∈ K → f = 0 := (atom K hKSt Φ hΦ).resolve_left hΦK
  have hyK2 : y ∈ K ⊔ LinearMap.range Φ := grow _ (sup_le hKN (rangeLe Φ hΦ hΦC))
    (supSt _ _ hKSt (rangeSt Φ hΦ)) le_sup_left (fun h => hΦK (le_sup_right.trans h))
  have hN2 : principalLevelFrame.isotIn (D := D) ρ C π ≤ K ⊔ LinearMap.range Φ := by
    refine iSup₂_le fun Φ' hΦ' => ?_
    by_contra hnot
    have h3 := (atom _ (supSt _ _ hKSt (rangeSt Φ hΦ)) Φ' hΦ'.1).resolve_left hnot
    have hyK3 : y ∈ K ⊔ LinearMap.range Φ' := grow _ (sup_le hKN (rangeLe Φ' hΦ'.1 hΦ'.2))
      (supSt _ _ hKSt (rangeSt Φ' hΦ'.1)) le_sup_left
      (fun h => hnot ((le_sup_right.trans h).trans le_sup_left))
    obtain ⟨k, hk, _, ⟨f', rfl⟩, hsum⟩ := Submodule.mem_sup.1 hyK3
    have hf' : f' = 0 := h3 f' (by
      have : Φ' f' = y - k := by rw [← hsum]; abel
      rw [this]; exact Submodule.sub_mem _ hyK2 (Submodule.mem_sup_left hk))
    apply hyK; rw [← hsum, hf', map_zero, add_zero]; exact hk
  let Ψ : (K × π.S) →ₗ[ℂ] A := K.subtype.coprod Φ
  have hΨ : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨k, f⟩ h0
    simp only [Ψ, LinearMap.coprod_apply, Submodule.subtype_apply] at h0
    have hneg : Φ f = -(k : A) := eq_neg_iff_add_eq_zero.2 (by rw [add_comm]; exact h0)
    have hf : f = 0 := hΦK' f (by rw [hneg]; exact K.neg_mem k.2)
    subst hf
    rw [map_zero, add_zero] at h0
    have hk : k = 0 := Subtype.ext h0
    subst hk; rfl
  let E := LinearEquiv.ofInjective Ψ hΨ
  let q0 : LinearMap.range Ψ →ₗ[ℂ] π.S := (LinearMap.snd ℂ K π.S).comp E.symm.toLinearMap
  obtain ⟨g, hg⟩ := LinearMap.exists_extend q0
  have hq0 : ∀ (k : K) (f : π.S), g (k + Φ f) = f := by
    intro k f
    have hmem : (k : A) + Φ f ∈ LinearMap.range Ψ := ⟨(k, f), rfl⟩
    have h1 := LinearMap.congr_fun hg ⟨_, hmem⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    rw [h1]
    have h2 : (⟨_, hmem⟩ : LinearMap.range Ψ) = E (k, f) := Subtype.ext (by simp only [E, LinearEquiv.ofInjective_apply]; rfl)
    show (E.symm _).2 = f
    rw [h2, LinearEquiv.symm_apply_apply]
  have dec : ∀ z ∈ principalLevelFrame.isotIn (D := D) ρ C π, ∃ (k : K) (f : π.S), z = k + Φ f := by
    intro z hz
    obtain ⟨a, ha, _, ⟨f, rfl⟩, rfl⟩ := Submodule.mem_sup.1 (hN2 hz)
    exact ⟨⟨a, ha⟩, f, rfl⟩
  refine ⟨π.S.subtype ∘ₗ g, ?_, ?_⟩
  · obtain ⟨k, f, rfl⟩ := dec y hy
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, hq0]
    intro hf
    have : f = 0 := Subtype.ext hf
    subst this
    apply hyK; rw [map_zero, add_zero]; exact k.2
  · intro z hz
    obtain ⟨k, f, rfl⟩ := dec z hz
    refine ⟨by simp [hq0], fun h => ?_⟩
    have : ρ h ((k : A) + Φ f) = ((⟨ρ h k, hKSt h k k.2⟩ : K) : A) + Φ ⟨NG.rt D.host.E n h f, π.stable h f f.2⟩ := by
      rw [map_add, hΦ h f]
    have e1 := hq0 ⟨ρ h k, hKSt h k k.2⟩ ⟨NG.rt D.host.E n h f, π.stable h f f.2⟩
    have e2 := hq0 k f
    rw [this, LinearMap.comp_apply, LinearMap.comp_apply, e1, e2]
    rfl

end GlobalTheory
