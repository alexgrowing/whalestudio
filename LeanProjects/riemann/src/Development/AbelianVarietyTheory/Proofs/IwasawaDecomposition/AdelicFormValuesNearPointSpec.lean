import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelHecke.ValAt

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem atV_mul {v : HeightOneSpectrum (𝓞 F)} {η η' : GA σ J} (h : AtV v η) (h' : AtV v η') : AtV v (η * η') := by
  intro v' hv'
  rw [Subgroup.coe_mul, map_mul, h v' hv', h' v' hv', one_mul]

theorem atV_inv {v : HeightOneSpectrum (𝓞 F)} {η : GA σ J} (h : AtV v η) : AtV v η⁻¹ := by
  intro v' hv'
  rw [Subgroup.coe_inv, map_inv, h v' hv', inv_one]

theorem inv_loc {ι : Type} [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (hb : v ∉ bad) (g) (hg : g ∈ AdFun S emb) (x κ : GA σ J) (hκ : AtV v κ)
    (hU : bc (prV (E := E) v) κ.1 ∈ S.Uloc v) : g (x * κ) = g x := by
  have hm : κ.1 ∈ S.U := by
    refine (S.U_eq _).2 ⟨κ.2, fun v' => ?_⟩
    by_cases h : v' = v
    · subst h; exact hU
    · rw [hκ v' h]; exact Subgroup.one_mem _
  have hc : S.chi ⟨κ.1, hm⟩ = 1 := S.chi_triv _ (fun v' hv' => hκ v' (fun h => hb (h ▸ hv')))
  funext y
  have := hg 1 (Subgroup.one_mem _) x (x * κ) ⟨κ.1, hm⟩ (by rw [map_one, one_mul]; rfl) y y
    (fun τ => by simp [atInf])
  rw [this, hc, Units.val_one, one_mul]

theorem val_self {ι : Type} [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) {k : Type} [Field k]
    (p : GA σ J → Pr (𝓞 E) (Fin n → E) k) (hb : v ∉ bad) (hp : PMap S v hv p) (g) (hg : g ∈ AdFun S emb)
    (x η : GA σ J) (hη : AtV v η) : valAt v p g x (p (x * η)) = g (x * η) := by
  have h : ∃ η', AtV v η' ∧ p (x * η') = p (x * η) := ⟨η, hη, rfl⟩
  unfold valAt
  rw [dif_pos h]
  obtain ⟨h1, h2⟩ := h.choose_spec
  generalize h.choose = η0 at h1 h2
  have e : x * η = x * η0 * (η0⁻¹ * η) := by group
  rw [e]
  refine (inv_loc S emb v hb g hg _ _ (atV_mul (atV_inv h1) hη) ?_).symm
  exact (hp.2.1 (x * η0) _).1 (by rw [← e, h2])

end

theorem valAt_spec : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (ι : Type) [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : Type) [Field k] (p : GA σ J → Pr (𝓞 E) (Fin n → E) k), v ∉ bad → PMap S v hv p → ∀ g ∈ AdFun S emb, (∀ x η : GA σ J, AtV v η → valAt v p g x (p (x * η)) = g (x * η)) ∧ (∀ x η : GA σ J, AtV v η → valAt v p g (x * η) = valAt v p g x) ∧ ∀ (a : ℤ) (δ x : GA σ J) (q : Pr (𝓞 E) (Fin n → E) k), (a : k) ≠ 0 → IsDia S v hv a δ → valAt v p g x (q.dil (a : k)) = valAt v p (fun y => g (y * δ)) x q := by
  intro F E _ _ _ _ _ σ n J T f bad ι _ S emb v hv k _ p hb hp g hg
  have key := val_self S emb v hv p hb hp g hg
  refine ⟨key, fun x η hη => ?_, fun a δ x q ha hδ => ?_⟩
  · funext q
    by_cases h : ∃ η', AtV v η' ∧ p (x * η * η') = q
    · obtain ⟨η', h1, rfl⟩ := h
      rw [key _ _ h1, mul_assoc, key _ _ (atV_mul hη h1)]
    · have h' : ¬ ∃ η', AtV v η' ∧ p (x * η') = q := by
        rintro ⟨η', h1, h2⟩
        refine h ⟨η⁻¹ * η', atV_mul (atV_inv hη) h1, ?_⟩
        rw [← h2]; congr 1; group
      unfold valAt
      rw [dif_neg h, dif_neg h']
  · have hδv : AtV v δ := hδ.1
    by_cases h : ∃ η', AtV v η' ∧ p (x * η') = q
    · have hR : valAt v p (fun y => g (y * δ)) x q = g (x * h.choose * δ) := by
        unfold valAt
        rw [dif_pos h]
      obtain ⟨h1, h2⟩ := h.choose_spec
      rw [hR]
      generalize h.choose = η0 at h1 h2
      rw [← h2, ← hp.2.2 _ δ a hδ, mul_assoc, key _ _ (atV_mul h1 hδv)]
    · have h' : ¬ ∃ η', AtV v η' ∧ p (x * η') = q.dil (a : k) := by
        rintro ⟨η', h1, h2⟩
        refine h ⟨η' * δ⁻¹, atV_mul h1 (atV_inv hδv), ?_⟩
        have h3 := hp.2.2 (x * (η' * δ⁻¹)) δ a hδ
        have e : x * (η' * δ⁻¹) * δ = x * η' := by group
        rw [e, h2] at h3
        have h4 := congrArg (Pr.dil (a : k)⁻¹) h3
        rw [Pr.dil_dil, Pr.dil_dil, inv_mul_cancel₀ ha, Pr.dil_one, Pr.dil_one] at h4
        exact h4.symm
      unfold valAt
      rw [dif_neg h, dif_neg h']

end GlobalTheory.LevelHecke.ValAt
