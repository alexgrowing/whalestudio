import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne

noncomputable section

namespace GlobalTheory.ThetaFacW

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaFac

theorem exists_max_not_mem {T : Type*} [AddCommGroup T] [Module ℂ T] (St : Submodule ℂ T → Prop) (D K : Submodule ℂ T)
    (hK : St K) (hKD : K ≤ D)
    (hchain : ∀ c : Set (Submodule ℂ T), c.Nonempty → IsChain (· ≤ ·) c → (∀ N ∈ c, St N) → St (sSup c))
    (hsup : ∀ N₁ N₂, St N₁ → St N₂ → N₁ ≤ D → N₂ ≤ D → St (N₁ ⊔ N₂))
    (hcompl : ∀ N, St N → K ≤ N → N ≤ D → ∃ C, St C ∧ C ≤ D ∧ N ⊔ C = D ∧ N ⊓ C = K)
    (x : T) (hxD : x ∈ D) (hxK : x ∉ K) :
    ∃ N, St N ∧ K ≤ N ∧ N ≤ D ∧ x ∉ N ∧ ∀ N', N ≤ N' → N' ≤ D → St N' → N' = N ∨ N' = D := by
  set S : Set (Submodule ℂ T) := {N | St N ∧ K ≤ N ∧ N ≤ D ∧ x ∉ N} with hS
  have hKS : K ∈ S := ⟨hK, le_rfl, hKD, hxK⟩
  obtain ⟨N, -, hN⟩ := zorn_le_nonempty₀ S (fun c hcS hc y hy => by
    have hne : c.Nonempty := ⟨y, hy⟩
    refine ⟨sSup c, ⟨hchain c hne hc (fun N hN => (hcS hN).1), (hcS hy).2.1.trans (le_sSup hy),
      sSup_le fun N hN => (hcS hN).2.2.1, fun hx => ?_⟩, fun z hz => le_sSup hz⟩
    obtain ⟨N, hN, hxN⟩ := (Submodule.mem_sSup_of_directed hne hc.directedOn).1 hx
    exact (hcS hN).2.2.2 hxN) K hKS
  obtain ⟨hNSt, hKN, hND, hxN⟩ := hN.prop
  refine ⟨N, hNSt, hKN, hND, hxN, fun N' hNN' hN'D hN'St => ?_⟩
  by_cases e1 : N' = N
  · exact Or.inl e1
  by_cases e2 : N' = D
  · exact Or.inr e2
  exfalso
  have hxN' : x ∈ N' := by
    by_contra hx
    exact e1 (le_antisymm (hN.le_of_ge ⟨hN'St, hKN.trans hNN', hN'D, hx⟩ hNN') hNN')
  obtain ⟨C, hCSt, hCD, hsupC, hinfC⟩ := hcompl N' hN'St (hKN.trans hNN') hN'D
  have hCN : ¬ C ≤ N := fun h => e2 (by rw [← hsupC, sup_eq_left.2 (h.trans hNN')])
  have hxNC : x ∈ N ⊔ C := by
    by_contra hx
    have := hN.le_of_ge ⟨hsup N C hNSt hCSt hND hCD, hKN.trans le_sup_left, sup_le hND hCD, hx⟩ le_sup_left
    exact hCN (le_sup_right.trans this)
  have : x ∈ (N ⊔ C) ⊓ N' := ⟨hxNC, hxN'⟩
  rw [sup_inf_assoc_of_le C hNN', inf_comm, hinfC, sup_eq_left.2 hKN] at this
  exact hxN this

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

theorem wStable_sSup (B : Base F E) (om : Rep σ Y W) (D : Submodule ℂ (Fn F n d)) (c : Set (Submodule ℂ (Fn F n d)))
    (hne : c.Nonempty) (hc : IsChain (· ≤ ·) c) (h : ∀ N ∈ c, WStable B om D N) : WStable B om D (sSup c) := by
  have mem := fun Φ => Submodule.mem_sSup_of_directed (z := Φ) hne hc.directedOn
  refine ⟨fun v g hg Φ hΦ => ?_, fun γ hγ Φ hΦ Φ₁ hΦ₁ hd => ?_, fun k hk Φ hΦ => ?_⟩
  · obtain ⟨N, hN, hΦN⟩ := (mem Φ).1 hΦ
    exact (mem _).2 ⟨N, hN, (h N hN).fin v g hg Φ hΦN⟩
  · obtain ⟨N, hN, hΦN⟩ := (mem Φ).1 hΦ
    exact (mem _).2 ⟨N, hN, (h N hN).lie γ hγ Φ hΦN Φ₁ hΦ₁ hd⟩
  · obtain ⟨N, hN, hΦN⟩ := (mem Φ).1 hΦ
    exact (mem _).2 ⟨N, hN, (h N hN).cpt k hk Φ hΦN⟩

theorem wStable_sup (B : Base F E) (om : Rep σ Y W) (D : Submodule ℂ (Fn F n d))
    (hD : ∀ γ ∈ Lines σ W, ∀ Φ ∈ D, ∃ Φ₁ ∈ D, ∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0)
    (N₁ N₂ : Submodule ℂ (Fn F n d)) (h₁ : WStable B om D N₁) (h₂ : WStable B om D N₂) (hN₁ : N₁ ≤ D) (hN₂ : N₂ ≤ D) :
    WStable B om D (N₁ ⊔ N₂) := by
  refine ⟨fun v g hg Φ hΦ => ?_, fun γ hγ Φ hΦ Φ₁ hΦ₁ hd => ?_, fun k hk Φ hΦ => ?_⟩
  · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hΦ
    rw [map_add]
    exact Submodule.add_mem_sup (h₁.fin v g hg y hy) (h₂.fin v g hg z hz)
  · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hΦ
    obtain ⟨y₁, hy₁D, hy₁⟩ := hD γ hγ y (hN₁ hy)
    obtain ⟨z₁, hz₁D, hz₁⟩ := hD γ hγ z (hN₂ hz)
    have e : Φ₁ = y₁ + z₁ := funext fun x => by
      rw [Pi.add_apply]
      refine (hd x).unique ?_
      have := (hy₁ x).add (hz₁ x)
      convert this using 1
      funext t
      simp only [map_add, Pi.add_apply]
    rw [e]
    exact Submodule.add_mem_sup (h₁.lie γ hγ y hy y₁ hy₁D hy₁) (h₂.lie γ hγ z hz z₁ hz₁D hz₁)
  · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hΦ
    rw [map_add]
    exact Submodule.add_mem_sup (h₁.cpt k hk y hy) (h₂.cpt k hk z hz)

theorem CoinvLe.mono {B : Base F E} {om : Rep σ Y W} {D N N' : Submodule ℂ (Fn F n d)} (h : CoinvLe B om D N)
    (hN : N ≤ N') : CoinvLe B om D N' :=
  ⟨fun v g hg Φ hΦ => hN (h.fin v g hg Φ hΦ), fun γ hγ Φ hΦ Φ₁ hΦ₁ hd => hN (h.lie γ hγ Φ hΦ Φ₁ hΦ₁ hd),
    fun k hk Φ hΦ => hN (h.cpt k hk Φ hΦ)⟩

end GlobalTheory.ThetaFacW

end
