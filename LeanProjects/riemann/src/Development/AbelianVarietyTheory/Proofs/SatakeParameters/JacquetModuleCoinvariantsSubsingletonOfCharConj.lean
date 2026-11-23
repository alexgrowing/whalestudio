import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong

namespace GlobalTheory

theorem jacquet_subsingleton_of_char_nontrivial_on_conj :
    ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), π.IsIrreducible →
      ∀ (N H : Subgroup G) (χ : H →* ℂˣ) (v : V), v ≠ 0 → (∀ h : H, π h v = (χ h : ℂ) • v) →
      (∀ g : G, ∃ h : H, g * h * g⁻¹ ∈ N ∧ χ h ≠ 1) → Subsingleton (Jacquet π N) := by
  intro G V _ _ _ π hπ N H χ v hv0 hv hconj
  set K : Submodule ℂ V := twKer π N 1 with hK

  have hgv : ∀ g : G, π g v ∈ K := by
    intro g
    obtain ⟨h, hn, hχ⟩ := hconj g
    have hmem : π (g * h * g⁻¹) (π g v) - (1 : ℂ) • π g v ∈ K := by
      refine Submodule.subset_span ⟨⟨_, hn⟩, π g v, ?_⟩
      simp
    have hcalc : π (g * h * g⁻¹) (π g v) = (χ h : ℂ) • π g v := by
      rw [← Module.End.mul_apply, ← map_mul]
      have : g * (h : G) * g⁻¹ * g = g * h := by group
      rw [this, map_mul, Module.End.mul_apply, hv h, map_smul]
    rw [hcalc, ← sub_smul] at hmem
    have hne : (χ h : ℂ) - 1 ≠ 0 := by
      intro e
      apply hχ
      ext
      simpa [sub_eq_zero] using e
    have := K.smul_mem ((χ h : ℂ) - 1)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  let S : Submodule ℂ V := ⨅ g : G, K.comap (π g)
  have hS : ∀ w, w ∈ S ↔ ∀ g : G, π g w ∈ K := by
    intro w; simp [S, Submodule.mem_iInf]
  let Wr : Subrepresentation π :=
    { toSubmodule := S
      apply_mem_toSubmodule := by
        intro g w hw
        rw [hS] at hw ⊢
        intro g'
        rw [← Module.End.mul_apply, ← map_mul]
        exact hw _ }
  have hvW : v ∈ S := (hS v).2 hgv
  have htop : K = ⊤ := by
    rcases hπ.eq_bot_or_eq_top Wr with e | e
    · exfalso
      have : v ∈ Wr.toSubmodule := hvW
      rw [e] at this
      exact hv0 this
    · rw [eq_top_iff]
      intro w _
      have : w ∈ Wr.toSubmodule := by rw [e]; trivial
      have := (hS w).1 this 1
      simpa using this
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective K a
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective K b
  exact (Submodule.Quotient.eq K).2 (by rw [htop]; trivial)
end GlobalTheory
