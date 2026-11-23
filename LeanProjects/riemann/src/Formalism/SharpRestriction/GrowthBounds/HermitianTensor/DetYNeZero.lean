import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DetFactsPAlt
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.NuOfLoZero

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem detY_ne_zero (K : Type) [Field K] (r : ℕ) : detY K r ≠ 0 :=
  Matrix.det_mvPolynomialX_ne_zero (Fin r) K

theorem qPh_of (hTau : TauP) (hSm : SmithP) (hBil : BilinP) (hDet : DetFactsP) (hNum : NumP) (hDD : DetDivP) : QPh := by
  intro p n' R r hr a c N α hαA hαN hc hca
  letI := R.charZeroO
  haveI := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  obtain ⟨e, he_def⟩ : ∃ e, α (Fin.last m) = e := ⟨_, rfl⟩
  have he : ∀ i, e ≤ α i := fun i => he_def ▸ hαA (Fin.le_last i)
  have hex : ∃ i, α i = e := ⟨_, he_def⟩
  have heN : e ≤ N := he_def ▸ hαN _
  have hγA : Antitone (fun i => α i - e) := by
    intro i j hij
    have := hαA hij
    show α j - e ≤ α i - e
    omega
  have wtK : ∀ {ν ν' : Fin (m + 1) → ℕ} {f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf},
      ν = ν' → f ∈ dualWeyl R.Kf (m + 1) (m + 1) ν → f ∈ dualWeyl R.Kf (m + 1) (m + 1) ν' := by
    rintro _ _ _ rfl h
    exact h
  have wtO : ∀ {ν ν' : Fin (m + 1) → ℕ} {f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.O},
      ν = ν' → f ∈ dualWeyl R.O (m + 1) (m + 1) ν → f ∈ dualWeyl R.O (m + 1) (m + 1) ν' := by
    rintro _ _ _ rfl h
    exact h
  have hwα : (fun j => (fun i => α i - e) j + e) = α := by
    funext j
    have := he j
    simp only
    omega
  obtain ⟨τ, hτK, hτO, hτsurj, hτeq⟩ := hTau R.O R.Kf hinj (m + 1) N e α (by omega) hαA hαN he hex
  obtain ⟨B, hBeq, hBint, nb, x, x', ka, hnb, hka, hx, hx', hdual⟩ :=
    hSm p n' R m (fun i => α i - e) hγA (by simp [he_def])
  set D : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf := detY R.Kf (m + 1) ^ e with hD_def
  have hD0 : D ≠ 0 := pow_ne_zero _ (detY_ne_zero R.Kf _)
  let μ : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf]
      MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf := LinearMap.mulLeft R.Kf D
  have hμ : Function.Injective μ := fun u v h => mul_left_cancel₀ hD0 h
  obtain ⟨Cc, hCc⟩ := Submodule.exists_isCompl (LinearMap.range μ)
  let σ : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf]
      MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf :=
    (LinearEquiv.ofInjective μ hμ).symm.toLinearMap ∘ₗ (LinearMap.range μ).projectionOnto Cc hCc
  have hσ : ∀ g, σ (D * g) = g := by
    intro g
    have hmem : D * g ∈ LinearMap.range μ := ⟨g, rfl⟩
    show (LinearEquiv.ofInjective μ hμ).symm ((LinearMap.range μ).projectionOnto Cc hCc (D * g)) = g
    rw [show D * g = ((⟨D * g, hmem⟩ : LinearMap.range μ) : MvPolynomial _ _) from rfl,
      Submodule.linearProjOfIsCompl_apply_left hCc, LinearEquiv.symm_apply_eq]
    ext1
    rw [LinearEquiv.ofInjective_apply]
    rfl
  obtain ⟨L, hL⟩ := hBil R.Kf (m + 1) ((B.compl₂ τ) ∘ₗ σ)
  have hL' : ∀ f f', L ((blockEmb R.Kf true) f * (blockEmb R.Kf false) f') = B (σ f) (τ f') := by
    intro f f'
    rw [hL]
    rfl
  have hmapD : map (algebraMap R.O R.Kf) (detY R.O (m + 1) ^ e) = D := by
    rw [map_pow, detY_map]
  have hdivK : ∀ f ∈ dualWeyl R.Kf (m + 1) (m + 1) α,
      ∃ g ∈ dualWeyl R.Kf (m + 1) (m + 1) (fun i => α i - e), f = D * g := by
    intro f hf
    exact hDD R.Kf (m + 1) e (fun i => α i - e) (by omega) hγA f (wtK hwα.symm hf)
  have hdivO : ∀ f ∈ intO R.O (m + 1) α,
      ∃ g ∈ intO R.O (m + 1) (fun i => α i - e), f = D * g := by
    intro f hf
    obtain ⟨fO, hfO, rfl⟩ := Submodule.mem_map.1 hf
    obtain ⟨gO, hgO, hfg⟩ := hDD R.O (m + 1) e (fun i => α i - e) (by omega) hγA fO (wtO hwα.symm hfO)
    refine ⟨map (algebraMap R.O R.Kf) gO, Submodule.mem_map.2 ⟨gO, hgO, rfl⟩, ?_⟩
    show map (algebraMap R.O R.Kf) fO = _
    rw [hfg, map_mul, hmapD]
  choose U hU hτU using fun a' => hτsurj (x' a') (hx' a')
  refine ⟨L, ?_, ?_, nb, fun b => D * x b, U, ka, ?_, ?_, ?_, hU, ?_⟩
  · intro l hl f hf f' hf'
    obtain ⟨g, hg, rfl⟩ := hdivK f hf
    rw [hL', hL', hσ]
    have hrD : rowAct R.Kf l (D * g) = D * (l.det ^ e • rowAct R.Kf l g) := by
      rw [map_mul, hD_def, map_pow, (hDet R.Kf (m + 1) e).2 l, MvPolynomial.smul_eq_C_mul, map_pow]
      ring
    rw [hrD, hσ, map_smul, LinearMap.smul_apply, hBeq, hτeq l hl f' hf', map_smul, smul_eq_mul,
      smul_eq_mul, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' heN]
  · intro f hf f' hf'
    obtain ⟨g, hg, rfl⟩ := hdivO f hf
    rw [hL', hσ]
    exact hBint g hg (τ f') (hτO f' hf')
  · rw [hnb]
    unfold weylDim
    refine Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j _ => ?_))
    simp only [Nat.cast_sub (he i), Nat.cast_sub (he j), sub_sub_sub_cancel_right]
  · intro b
    refine (hka b).trans ?_
    have h1 := hc 0 (Fin.last m)
    exact hNum p a c (m + 1) (α 0 - e) R.std.1.prime.two_le (by omega) (by omega) hca
  · intro b
    obtain ⟨xO, hxO, hxe⟩ := Submodule.mem_map.1 (hx b)
    refine Submodule.mem_map.2 ⟨detY R.O (m + 1) ^ e * xO,
      wtO (by funext j; have := he j; simp only [Pi.add_apply]; omega)
        (dualWeyl_mul R.O (m + 1) (m + 1) _ _ (hDet R.O (m + 1) e).1 hxO), ?_⟩
    show map (algebraMap R.O R.Kf) (detY R.O (m + 1) ^ e * xO) = D * x b
    rw [map_mul, hmapD, ← hxe]
    rfl
  · intro a' b
    rw [hL', hσ, hτU]
    exact hdual a' b

end Formalism.MainNotions.flipOneThree.Pf

end
