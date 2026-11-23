import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RootDown

variable {k : Type} [Field k]

theorem blk_stdBlocks_eq_zero {n a b : ℕ} (h : ∑ i, ![a, b] i = n) (p : Fin n) :
    GlobalTheory.SmGL.blk (stdBlocks ![a, b] h) p = 0 ↔ p.val < a := by
  obtain ⟨⟨c, r⟩, rfl⟩ := (stdBlocks ![a, b] h).surjective p
  rw [GlobalTheory.SmGL.blk_apply, stdBlocks_val]
  rcases c with ⟨_ | _ | c, hc⟩
  · have := r.isLt
    simp at this ⊢
    omega
  · have := r.isLt
    simp
  · omega

theorem unip_entry {n a b : ℕ} (h : ∑ i, ![a, b] i = n) {u : GL (Fin n) k}
    (hu : u ∈ unipRad k (stdBlocks ![a, b] h)) (p q : Fin n) (hpq : ¬ (p.val < a ∧ a ≤ q.val)) :
    (u : Matrix (Fin n) (Fin n) k) p q = (1 : Matrix (Fin n) (Fin n) k) p q := by
  obtain ⟨hP, hD⟩ := mem_unipRad.1 hu
  rcases lt_trichotomy (GlobalTheory.SmGL.blk (stdBlocks ![a, b] h) q) (GlobalTheory.SmGL.blk (stdBlocks ![a, b] h) p)
    with hlt | heq | hgt
  · rw [mem_parab.1 hP p q hlt]
    have : p ≠ q := by rintro rfl; exact lt_irrefl _ hlt
    simp [Matrix.one_apply_ne this]
  · obtain ⟨⟨c, r⟩, rfl⟩ := (stdBlocks ![a, b] h).surjective p
    obtain ⟨⟨c', s⟩, rfl⟩ := (stdBlocks ![a, b] h).surjective q
    simp only [GlobalTheory.SmGL.blk_apply] at heq
    subst heq
    rw [hD c' r s]
    simp [Matrix.one_apply]
  · exfalso
    apply hpq
    have h1 := Fin.lt_def.1 hgt
    have h2 := (GlobalTheory.SmGL.blk (stdBlocks ![a, b] h) q).isLt
    have hp0 : GlobalTheory.SmGL.blk (stdBlocks ![a, b] h) p = 0 := Fin.ext (by simp; omega)
    have hq0 : GlobalTheory.SmGL.blk (stdBlocks ![a, b] h) q ≠ 0 := fun h0 => by
      rw [h0] at h1; simp at h1
    exact ⟨(blk_stdBlocks_eq_zero h p).1 hp0,
      not_lt.1 fun hq => hq0 ((blk_stdBlocks_eq_zero h q).2 hq)⟩

theorem conj_entry {n : ℕ} (t : Fin n → kˣ) (u : GL (Fin n) k) (p q : Fin n) :
    ((diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q =
      (t p : k) * (u : Matrix (Fin n) (Fin n) k) p q * (((t q)⁻¹ : kˣ) : k) := by
  rw [← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, Matrix.mul_diagonal,
    Matrix.diagonal_mul]
  simp

end GlobalTheory.RootDown

open GlobalTheory.RootDown in
theorem GlobalTheory.whittaker_torus_twKer_rootBound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V) (l : Module.Dual ℂ V), IsFunctional ψ ρ l → ∀ (a b : ℕ) (h : ∑ i, ![a, b] i = n) (i j : Fin n), i.val + 1 = a → j.val = a → ∀ x ∈ twKer ρ (unipRad k (stdBlocks ![a, b] h)) 1, ∃ r : kˣ, ∀ t : Fin n → kˣ, l (ρ (diagT k (Fin n) t) x) ≠ 0 → valuation k (r : k) ≤ valuation k ((t i : k) / t j) := by
  intro k _ _ _ _ ψ hψ n V _ _ ρ l hl a b h i j hi hj x hx
  obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_addChar_eq_one ψ hψ
  unfold twKer at hx
  induction hx using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨u, hu⟩, y, rfl⟩ := hw
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    have key : ∀ t : Fin n → kˣ, l (ρ (diagT k (Fin n) t) (ρ u y - y)) =
        ((ψ ((t i : k) / t j * (u : Matrix (Fin n) (Fin n) k) i j) : ℂ) - 1) *
          l (ρ (diagT k (Fin n) t) y) := by
      intro t
      have hmem : diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹ ∈ unipB k (Fin n) := by
        refine (mem_unipB k).2 ⟨fun p q hqp => ?_, fun p => ?_⟩
        · have hqp' := Fin.lt_def.1 hqp
          rw [conj_entry, unip_entry h hu p q (by omega), Matrix.one_apply_ne hqp.ne']
          simp
        · rw [conj_entry, unip_entry h hu p p (by omega), Matrix.one_apply_eq]
          simp
      have hsd : GlobalTheory.Whittaker.superDiag (diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹) =
          (t i : k) / t j * (u : Matrix (Fin n) (Fin n) k) i j := by
        unfold GlobalTheory.Whittaker.superDiag
        rw [Finset.sum_eq_single i]
        · rw [Finset.sum_eq_single_of_mem j (by simp; omega)]
          · rw [conj_entry, Units.val_inv_eq_inv_val, div_eq_mul_inv]
            ring
          · intro q hq hqj
            simp at hq
            exact absurd (Fin.ext (by omega)) hqj
        · intro p _ hpi
          refine Finset.sum_eq_zero fun q hq => ?_
          simp at hq
          have hpq : p ≠ q := fun e => by rw [e] at hq; omega
          rw [conj_entry, unip_entry h hu p q ?_, Matrix.one_apply_ne hpq]
          · simp
          · rintro ⟨h1, h2⟩
            exact hpi (Fin.ext (by omega))
        · intro hi'
          simp at hi'
      have hρ : ρ (diagT k (Fin n) t) (ρ u y) =
          ρ (diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹) (ρ (diagT k (Fin n) t) y) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, hρ, hl _ hmem, hsd]
      ring
    by_cases hu0 : (u : Matrix (Fin n) (Fin n) k) i j = 0
    · refine ⟨1, fun t ht => absurd ?_ ht⟩
      rw [key, hu0, mul_zero, AddChar.map_zero_eq_one]
      simp
    · refine ⟨s * (Units.mk0 _ hu0)⁻¹, fun t ht => ?_⟩
      rw [key] at ht
      have hψ1 : ψ ((t i : k) / t j * (u : Matrix (Fin n) (Fin n) k) i j) ≠ 1 := fun h1 =>
        ht (by rw [h1]; simp)
      have hlt : valuation k (s : k) <
          valuation k ((t i : k) / t j * (u : Matrix (Fin n) (Fin n) k) i j) :=
        lt_of_not_ge fun hle => hψ1 (hs _ hle)
      rw [map_mul] at hlt
      have hpos : 0 < valuation k ((u : Matrix (Fin n) (Fin n) k) i j) := by
        simp [zero_lt_iff, hu0]
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, map_mul, map_inv₀]
      exact ((mul_inv_lt_iff₀ hpos).2 hlt).le
  | zero => exact ⟨1, fun t ht => absurd (by simp) ht⟩
  | add x y _ _ hx hy =>
    obtain ⟨r₁, h₁⟩ := hx
    obtain ⟨r₂, h₂⟩ := hy
    rcases le_total (valuation k (r₁ : k)) (valuation k (r₂ : k)) with h12 | h21
    · refine ⟨r₁, fun t ht => ?_⟩
      rw [map_add, map_add] at ht
      by_cases h0 : l (ρ (diagT k (Fin n) t) x) = 0
      · rw [h0, zero_add] at ht
        exact h12.trans (h₂ t ht)
      · exact h₁ t h0
    · refine ⟨r₂, fun t ht => ?_⟩
      rw [map_add, map_add] at ht
      by_cases h0 : l (ρ (diagT k (Fin n) t) y) = 0
      · rw [h0, add_zero] at ht
        exact h21.trans (h₁ t ht)
      · exact h₂ t h0
  | smul c x _ hx =>
    obtain ⟨r, hr⟩ := hx
    exact ⟨r, fun t ht => hr t fun h0 => ht (by rw [map_smul, map_smul, h0, smul_zero])⟩
