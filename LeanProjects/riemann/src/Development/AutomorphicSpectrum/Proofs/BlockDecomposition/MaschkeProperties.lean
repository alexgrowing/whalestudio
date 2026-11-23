import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleIffIrreducibleStatement

open CategoryTheory
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.Maschke

section Avg

variable {Γ : Type} [Group Γ] [Fintype Γ]
variable {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

def avg (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W) (f : V →ₗ[ℂ] W) : V →ₗ[ℂ] W :=
  (Fintype.card Γ : ℂ)⁻¹ • ∑ g : Γ, σ g ∘ₗ f ∘ₗ ρ g⁻¹

theorem avg_apply (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W) (f : V →ₗ[ℂ] W) (v : V) :
    avg ρ σ f v = (Fintype.card Γ : ℂ)⁻¹ • ∑ g : Γ, σ g (f (ρ g⁻¹ v)) := by
  simp [avg, LinearMap.sum_apply]

theorem mem_intw_apply {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} {φ : V →ₗ[ℂ] W}
    (h : φ ∈ Intw ρ σ) (g : Γ) (v : V) : φ (ρ g v) = σ g (φ v) :=
  LinearMap.congr_fun (h g) v

theorem rep_inv_apply (ρ : Representation ℂ Γ V) (g : Γ) (v : V) : ρ g (ρ g⁻¹ v) = v := by
  have h : ρ (g * g⁻¹) v = v := by simp
  rwa [map_mul] at h

theorem avg_mem (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W) (f : V →ₗ[ℂ] W) :
    avg ρ σ f ∈ Intw ρ σ := by
  intro h
  ext v
  simp only [LinearMap.comp_apply, avg_apply, map_smul, map_sum]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ fun g => ?_
  have e1 : ρ (h⁻¹ * g)⁻¹ v = ρ g⁻¹ (ρ h v) := by
    rw [mul_inv_rev, inv_inv, map_mul]; rfl
  have e2 : ∀ w, σ h (σ (h⁻¹ * g) w) = σ g w := fun w => by
    have h2 : σ (h * (h⁻¹ * g)) w = σ g w := by simp
    rw [map_mul σ h (h⁻¹ * g)] at h2
    exact h2
  simp only [Equiv.coe_mulLeft]
  rw [e1, e2]

theorem avg_of_mem {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} {f : V →ₗ[ℂ] W}
    (hf : f ∈ Intw ρ σ) : avg ρ σ f = f := by
  ext v
  have hc : (Fintype.card Γ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h : ∀ g : Γ, σ g (f (ρ g⁻¹ v)) = f v := fun g => by
    rw [← mem_intw_apply hf, rep_inv_apply]
  simp only [avg_apply, h, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem id_mem (ρ : Representation ℂ Γ V) : (LinearMap.id : V →ₗ[ℂ] V) ∈ Intw ρ ρ := by
  intro g
  simp

theorem comp_mem {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} {τ : Representation ℂ Γ U}
    {φ : V →ₗ[ℂ] W} {ψ : W →ₗ[ℂ] U} (hφ : φ ∈ Intw ρ σ) (hψ : ψ ∈ Intw σ τ) :
    ψ ∘ₗ φ ∈ Intw ρ τ := by
  intro g
  ext v
  simp only [LinearMap.comp_apply]
  rw [mem_intw_apply hφ, mem_intw_apply hψ]

theorem avg_comp {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} (τ : Representation ℂ Γ U)
    {φ : V →ₗ[ℂ] W} (hφ : φ ∈ Intw ρ σ) (f : W →ₗ[ℂ] U) :
    avg σ τ f ∘ₗ φ = avg ρ τ (f ∘ₗ φ) := by
  ext v
  simp only [LinearMap.comp_apply, avg_apply]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [mem_intw_apply hφ]

theorem comp_avg {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} (τ : Representation ℂ Γ U)
    {φ : V →ₗ[ℂ] W} (hφ : φ ∈ Intw ρ σ) (f : U →ₗ[ℂ] V) :
    φ ∘ₗ avg τ ρ f = avg τ σ (φ ∘ₗ f) := by
  ext v
  simp only [LinearMap.comp_apply, avg_apply, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [mem_intw_apply hφ]

theorem exists_left_inverse {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} {φ : V →ₗ[ℂ] W}
    (hφ : φ ∈ Intw ρ σ) (hinj : Function.Injective φ) :
    ∃ ψ ∈ Intw σ ρ, ψ ∘ₗ φ = LinearMap.id := by
  obtain ⟨q, hq⟩ := φ.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  refine ⟨avg σ ρ q, avg_mem σ ρ q, ?_⟩
  rw [avg_comp ρ hφ, hq, avg_of_mem (id_mem ρ)]

theorem exists_right_inverse {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} {φ : V →ₗ[ℂ] W}
    (hφ : φ ∈ Intw ρ σ) (hsurj : Function.Surjective φ) :
    ∃ ψ ∈ Intw σ ρ, φ ∘ₗ ψ = LinearMap.id := by
  obtain ⟨q, hq⟩ := φ.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  refine ⟨avg σ ρ q, avg_mem σ ρ q, ?_⟩
  rw [comp_avg σ hφ, hq, avg_of_mem (id_mem σ)]

end Avg

section Schur

variable {Γ : Type} [Group Γ]
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem injective_of_irr {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} {φ : V →ₗ[ℂ] W}
    (hρ : IsIrr ρ) (hφ : φ ∈ Intw ρ σ) (h0 : φ ≠ 0) : Function.Injective φ := by
  have hinv : ∀ g, ∀ v ∈ LinearMap.ker φ, ρ g v ∈ LinearMap.ker φ := fun g v hv => by
    have h1 : φ (ρ g v) = σ g (φ v) := LinearMap.congr_fun (hφ g) v
    rw [LinearMap.mem_ker] at hv ⊢
    rw [h1, hv, map_zero]
  rcases hρ.2 _ hinv with h | h
  · exact LinearMap.ker_eq_bot.mp h
  · exact absurd (LinearMap.ker_eq_top.mp h) h0

theorem surjective_of_irr {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} {φ : V →ₗ[ℂ] W}
    (hσ : IsIrr σ) (hφ : φ ∈ Intw ρ σ) (h0 : φ ≠ 0) : Function.Surjective φ := by
  have hinv : ∀ g, ∀ w ∈ LinearMap.range φ, σ g w ∈ LinearMap.range φ := fun g w hw => by
    obtain ⟨v, rfl⟩ := hw
    exact ⟨ρ g v, LinearMap.congr_fun (hφ g) v⟩
  rcases hσ.2 _ hinv with h | h
  · exact absurd (LinearMap.range_eq_bot.mp h) h0
  · exact LinearMap.range_eq_top.mp h

end Schur

section Main

variable {Γ : Type} [Group Γ] [Fintype Γ]
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem irr_of_finrank_one [FiniteDimensional ℂ V] (ρ : Representation ℂ Γ V)
    (h : Module.finrank ℂ (Intw ρ ρ) = 1) : IsIrr ρ := by
  have hV : Nontrivial V := by
    by_contra hn
    have : Subsingleton V := not_nontrivial_iff_subsingleton.mp hn
    have : Subsingleton (Intw ρ ρ) := inferInstance
    rw [Module.finrank_zero_of_subsingleton] at h
    exact zero_ne_one h
  refine ⟨hV, fun S hS => ?_⟩
  obtain ⟨q, hq⟩ := S.subtype.exists_leftInverse_of_injective S.ker_subtype
  set p := avg ρ ρ (S.subtype ∘ₗ q) with hp
  have hpS : ∀ v, p v ∈ S := fun v => by
    rw [hp, avg_apply]
    refine S.smul_mem _ (S.sum_mem fun g _ => hS g _ ?_)
    exact (q (ρ g⁻¹ v)).2
  have hq' : ∀ w (hw : w ∈ S), ((q w : S) : V) = w := fun w hw => by
    have := LinearMap.congr_fun hq ⟨w, hw⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply] at this
    rw [this]
  have hc : (Fintype.card Γ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hfix : ∀ w ∈ S, p w = w := fun w hw => by
    have h1 : ∀ g : Γ, ρ g ((S.subtype ∘ₗ q) (ρ g⁻¹ w)) = w := fun g => by
      simp only [LinearMap.comp_apply, Submodule.subtype_apply]
      rw [hq' _ (hS _ _ hw), rep_inv_apply]
    rw [hp, avg_apply]
    simp only [h1, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hne : (⟨LinearMap.id, id_mem ρ⟩ : Intw ρ ρ) ≠ 0 := fun h0 => by
    have h1 : (LinearMap.id : V →ₗ[ℂ] V) = 0 := congrArg Subtype.val h0
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    exact hx (LinearMap.congr_fun h1 x)
  obtain ⟨c, hcp⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp h ⟨p, avg_mem ρ ρ _⟩
  have hpc : ∀ v, p v = c • v := fun v => by
    have h1 : c • (LinearMap.id : V →ₗ[ℂ] V) = p := congrArg Subtype.val hcp
    rw [← h1]; rfl
  by_cases hc0 : c = 0
  · left
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_bot, ← hfix w hw, hpc, hc0, zero_smul]
  · right
    rw [eq_top_iff]
    intro v _
    have h1 : v = c⁻¹ • p v := by rw [hpc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [h1]
    exact S.smul_mem _ (hpS v)

theorem maschkeFacts_of_simpleIffIrr (hs : ReciprocityTheory.Ty.Fin.St.SimpleIffIrr) :
    ReciprocityTheory.Ty.Fin.St.MaschkeFacts := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Γ _ _ τ V _ _ _ ρ hτ
    have hirr : IsIrr τ.ρ := (hs.1 Γ τ).1 hτ
    constructor
    · rintro ⟨φ, hφ, h0⟩
      obtain ⟨ψ, hψ, hl⟩ := exists_left_inverse hφ (injective_of_irr hirr hφ h0)
      refine ⟨ψ, hψ, fun hz => ?_⟩
      have := hirr.1
      obtain ⟨x, hx⟩ := exists_ne (0 : τ)
      have h1 := LinearMap.congr_fun hl x
      simp [hz] at h1
      exact hx h1.symm
    · rintro ⟨ψ, hψ, h0⟩
      obtain ⟨φ, hφ, hr⟩ := exists_right_inverse hψ (surjective_of_irr hirr hψ h0)
      refine ⟨φ, hφ, fun hz => ?_⟩
      have := hirr.1
      obtain ⟨x, hx⟩ := exists_ne (0 : τ)
      have h1 := LinearMap.congr_fun hr x
      simp [hz] at h1
      exact hx h1.symm
  · rintro Γ _ _ τ V _ _ _ W _ _ _ ρ σ hτ ⟨φ, hφ, h0⟩ ⟨φ', hφ', h0'⟩ hfin
    have hirr : IsIrr τ.ρ := (hs.1 Γ τ).1 hτ
    obtain ⟨ψ, hψ, hl⟩ := exists_left_inverse hφ (injective_of_irr hirr hφ h0)
    rw [Submodule.finrank_eq_zero] at hfin
    have hmem : φ' ∘ₗ ψ ∈ Intw ρ σ := comp_mem hψ hφ'
    rw [hfin, Submodule.mem_bot] at hmem
    apply h0'
    have h1 : (φ' ∘ₗ ψ) ∘ₗ φ = φ' := by rw [LinearMap.comp_assoc, hl, LinearMap.comp_id]
    rw [← h1, hmem, LinearMap.zero_comp]
  · intro Γ _ _ V _ _ _ ρ h
    exact irr_of_finrank_one ρ h
  · intro Γ _ _ V _ _ _ W _ _ _ ρ σ hρ hσ hfin
    have hne : Intw ρ σ ≠ ⊥ := fun hb => hfin (by rw [hb]; exact finrank_bot ℂ _)
    obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).mp hne
    exact ⟨LinearEquiv.ofBijective φ
        ⟨injective_of_irr hρ hφ h0, surjective_of_irr hσ hφ h0⟩,
      fun γ v => LinearMap.congr_fun (hφ γ) v⟩

theorem maschkeFacts : ReciprocityTheory.Ty.Fin.St.MaschkeFacts :=
  maschkeFacts_of_simpleIffIrr GlobalTheory.T.simple_iff_irreducible

end Main

end GlobalTheory.CompanionTheory.TyFin.Maschke
