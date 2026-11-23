import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.AbsGood
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.PowNeZero

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg
open UpperTheory.V.W UpperTheory.V.Pr

namespace UpperTheory.V.J

private theorem coef_inj {l : ℕ} [Fact l.Prime] (c : Coef l) : Function.Injective (algebraMap c.O (Qbar l)) :=
  Subtype.val_injective

theorem endJ : End := by
  intro Ω _ _ _ l _ c η Ψ σ g₁ B M L _ _ _ _ _ Φ k c₁ _ f ka R φ hφ hs J ξ w hJ hTI har hirr hann D hD D' hD' h1 h2
  have key : ∀ E ∈ PtDer ξ (↥c₁.O),
      (∀ (v : (Φ.ext f).V) (i : Fin 3), ∀ g ∈ (Φ.ext f).Iv v, E ((R.S.ρ.ψ v i) g : R.S.R) = 0) →
      ∀ a ∈ R.S.B, E a = 0 := by
    intro E hE hI a ha
    have hmul : ∀ x y : R.S.R, E (x * y) = ξ x * E y + ξ y * E x := fun x y => hE x y
    have hone : E 1 = 0 := by
      have h := hmul 1 1
      simp at h
      exact h
    have halg : ∀ (r : ↥c₁.O), E (algebraMap (↥c₁.O) R.S.R r) = 0 := by
      intro r
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hone, smul_zero]
    have hJa : ∀ a ∈ J, ξ ((φ a : R.S.B) : R.S.R) = 0 ∧ E ((φ a : R.S.B) : R.S.R) = 0 := by
      intro x hx
      obtain ⟨s, hs1, hs2⟩ := hann x hx
      have e : (s : R.S.R) * ((φ x : R.S.B) : R.S.R) = 0 := by
        have h := congrArg Subtype.val hs2
        simpa [Fr.Space.inc] using h
      have hξs : ξ (s : R.S.R) ≠ 0 := by
        intro h0
        apply hs1
        simp [ptA, h0]
      have hξ : ξ ((φ x : R.S.B) : R.S.R) = 0 := by
        have h := congrArg ξ e
        rw [map_mul, map_zero] at h
        exact (mul_eq_zero.mp h).resolve_left hξs
      refine ⟨hξ, ?_⟩
      have h := hmul (s : R.S.R) ((φ x : R.S.B) : R.S.R)
      rw [e, map_zero, hξ, zero_mul, add_zero] at h
      exact (mul_eq_zero.mp h.symm).resolve_left hξs
    let δ : R.B₀.B →ₗ[↥c₁.O] Qbar l :=
      (Algebra.ofId (↥c₁.O) (Qbar l)).toLinearMap ∘ₗ E ∘ₗ (R.S.B.val.comp φ).toLinearMap
    have hδ : δ ∈ PtDer (ptOf R φ ξ) (Qbar l) := by
      intro x y
      simp [δ, ptOf, hmul]
    have hle : J ≤ RingHom.ker (ptOf R φ ξ) := by
      intro x hx
      simp [ptOf, (hJa x hx).1]
    have hδJ : ∀ x ∈ J, δ x = 0 := by
      intro x hx
      simp [δ, (hJa x hx).2]
    have hδψ : ∀ (v : R.V.frame.Vl) (i : Fin 3), ∀ g ∈ R.V.frame.Iv v, δ ((R.B₀.u.ψ v i) g : R.B₀.B) = 0 := by
      intro v i g hg
      have hm := congrArg (fun χ => ((χ g : (R.S.R)ˣ) : R.S.R)) (hφ.2 v i)
      simp only [pushCh, TwLink.twψ, TwLink.κA] at hm
      have hm' : ((φ ((R.B₀.u.ψ v i) g : R.B₀.B) : R.S.B) : R.S.R) =
          ((R.S.ρ.ψ (R.K.e v) i ((R.K.lam v) g) : R.S.Rˣ) : R.S.R) *
            algebraMap (↥c₁.O) R.S.R ((R.K.κ (R.V.frame.φ v g) : (↥c₁.O)ˣ) : ↥c₁.O) := hm
      have hin : (R.K.lam v) g ∈ (Φ.ext f).Iv (R.K.e v) := (R.K.lam_I v g).mpr hg
      simp only [δ, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, AlgHom.coe_comp,
        Subalgebra.coe_val]
      rw [hm', hmul, halg, hI _ _ _ hin]
      simp
    have h0 := hJ (ptOf R φ ξ) w hle har hirr δ hδ hδJ hδψ
    obtain ⟨b, hb⟩ := hs ⟨a, ha⟩
    have h := LinearMap.congr_fun h0 b
    have h' : algebraMap (↥c₁.O) (Qbar l) (E a) = 0 := by
      simpa [δ, hb] using h
    exact coef_inj c₁ (by rw [h', map_zero])
  exact tor l (↥c₁.O) (Φ.ext f) R.S ξ hTI D hD D' hD' (key D hD h1) (key D' hD' h2)

end UpperTheory.V.J
