import Mathlib
import Formalism.LocalToGlobal.Columns.DecoFin
import Formalism.LocalToGlobal.Columns.SmulMemTrpSet
import Formalism.HermitianLattices.HermitianLatticesProofs.NeighbourConstruct

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.HermitianLatticesTheory

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem localization_linear_extension_exists (N : Submodule (𝓞 E) (Sp E n)) (P : HeightOneSpectrum (𝓞 E))
    (f0 : N →ₗ[𝓞 E] (𝓞 E ⧸ P.asIdeal)) (x : Sp E n) (hx : x ∈ localization₂ P.asIdeal N) :
    ∃ c : 𝓞 E ⧸ P.asIdeal, ∀ (s : 𝓞 E) (_ : s ∉ P.asIdeal) (h : s • x ∈ N),
      Ideal.Quotient.mk P.asIdeal s * c = f0 ⟨s • x, h⟩ := by
  obtain ⟨s0, hs0, h0⟩ := (mem_locP _ _ _).1 hx
  have := P.isMaximal
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv (mk_ne_zero hs0)
  refine ⟨b * f0 ⟨s0 • x, h0⟩, fun s _ h => ?_⟩
  have e1 : Ideal.Quotient.mk P.asIdeal s * f0 ⟨s0 • x, h0⟩ = Ideal.Quotient.mk P.asIdeal s0 * f0 ⟨s • x, h⟩ := by
    have a1 : f0 (s • ⟨s0 • x, h0⟩) = s • f0 ⟨s0 • x, h0⟩ := map_smul _ _ _
    have a2 : f0 (s0 • ⟨s • x, h⟩) = s0 • f0 ⟨s • x, h⟩ := map_smul _ _ _
    have a3 : (s • (⟨s0 • x, h0⟩ : N)) = s0 • ⟨s • x, h⟩ := Subtype.ext (smul_comm _ _ _)
    rw [a3, a2] at a1
    rw [Algebra.smul_def, Algebra.smul_def] at a1
    exact a1.symm
  calc _ = b * (Ideal.Quotient.mk P.asIdeal s * f0 ⟨s0 • x, h0⟩) := by ring
    _ = (Ideal.Quotient.mk P.asIdeal s0 * b) * f0 ⟨s • x, h⟩ := by rw [e1]; ring
    _ = _ := by rw [hb, one_mul]

theorem FunAt.exists_ext (N : Submodule (𝓞 E) (Sp E n)) (P : HeightOneSpectrum (𝓞 E))
    (f0 : N →ₗ[𝓞 E] (𝓞 E ⧸ P.asIdeal)) : ∃ F : Sp E n → 𝓞 E ⧸ P.asIdeal,
      FunAt P N F ∧ ∀ x (hx : x ∈ N), F x = f0 ⟨x, hx⟩ := by
  classical
  let F : Sp E n → 𝓞 E ⧸ P.asIdeal := fun x =>
    if h : x ∈ localization₂ P.asIdeal N then (localization_linear_extension_exists N P f0 x h).choose else 0
  have hF : ∀ x (_ : x ∈ localization₂ P.asIdeal N) (s : 𝓞 E) (_ : s ∉ P.asIdeal) (h : s • x ∈ N),
      Ideal.Quotient.mk P.asIdeal s * F x = f0 ⟨s • x, h⟩ := by
    intro x hx s hs h
    simp only [F, dif_pos hx]
    exact (localization_linear_extension_exists N P f0 x hx).choose_spec s hs h
  refine ⟨F, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hx y hy
    obtain ⟨s, hs, h⟩ := (mem_locP _ _ _).1 hx
    obtain ⟨t, ht, h'⟩ := (mem_locP _ _ _).1 hy
    have hst : s * t ∉ P.asIdeal := fun h' => (P.isPrime.mem_or_mem h').elim hs ht
    have m1 : (s * t) • x ∈ N := by rw [mul_comm, mul_smul]; exact N.smul_mem _ h
    have m2 : (s * t) • y ∈ N := by rw [mul_smul]; exact N.smul_mem _ h'
    have m3 : (s * t) • (x + y) ∈ N := by rw [smul_add]; exact N.add_mem m1 m2
    apply mul_left_cancel₀ (mk_ne_zero hst)
    rw [mul_add, hF _ hx _ hst m1, hF _ hy _ hst m2, hF _ (Submodule.add_mem _ hx hy) _ hst m3, ← map_add]
    congr 1
    exact Subtype.ext (smul_add _ _ _)
  · intro a x hx
    obtain ⟨s, hs, h⟩ := (mem_locP _ _ _).1 hx
    have m1 : s • (a • x) ∈ N := by rw [smul_comm]; exact N.smul_mem _ h
    apply mul_left_cancel₀ (mk_ne_zero hs)
    rw [hF _ (Submodule.smul_mem _ a hx) _ hs m1, mul_left_comm, hF _ hx _ hs h]
    have : (⟨s • a • x, m1⟩ : N) = a • ⟨s • x, h⟩ := Subtype.ext (smul_comm _ _ _)
    rw [this, map_smul, Algebra.smul_def]; rfl
  · intro x hx
    simp only [F, dif_neg hx]
  · intro x hx
    have := hF x (le_locP _ _ hx) 1 (one_notMem P) (by simpa using hx)
    rw [map_one, one_mul] at this
    rw [this]; congr 1; exact Subtype.ext (one_smul _ _)

end Formalism.L2.Col
