import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.IdCell

noncomputable section

namespace PI.UnitNormRootW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem hT_span_left (S : HSpace E) {s : Set S.V} {y : S.V} (hy : ∀ a ∈ s, S.hT a y = 0)
    {x : S.V} (hx : x ∈ Submodule.span E s) : S.hT x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem a ha => exact hy a ha
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul c a _ ha => simp [ha]

theorem hT_span_right (S : HSpace E) {s : Set S.V} {x : S.V} (hx : ∀ a ∈ s, S.hT x a = 0)
    {y : S.V} (hy : y ∈ Submodule.span E s) : S.hT x y = 0 := by
  induction hy using Submodule.span_induction with
  | mem a ha => exact hx a ha
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul c a _ ha => simp [ha]

theorem norm_shift {S : HSpace E} {r : ℕ} {T T' : E} (F : FlagG S r T) (F' : FlagG S r T')
    (ζ : E) (h : F'.fvec (Fin.last r) - ζ • F.fvec (Fin.last r) ∈ F.Xa r) :
    T' = star ζ * ζ * T := by
  have h1 : F'.z - ζ • F.z ∈ F.Xa r := by simpa [FlagG.fvec] using h
  have hz : F'.z - ζ • F.z ∈ Submodule.span E (Set.range F.e) :=
    Submodule.span_mono (Set.image_subset_range F.e {i | i.1 < r}) h1
  obtain ⟨x, hx, hzx⟩ : ∃ x ∈ Submodule.span E (Set.range F.e), F'.z = ζ • F.z + x :=
    ⟨_, hz, by abel⟩
  have hxz : S.hT x F.z = 0 :=
    hT_span_left S (by rintro _ ⟨a, rfl⟩; exact F.z_orth a) hx
  have hzx' : S.hT F.z x = 0 := by rw [← S.herm.eq x F.z, hxz, map_zero]
  have hxx : S.hT x x = 0 :=
    hT_span_left S (fun a ha => by
      obtain ⟨a', rfl⟩ := ha
      exact hT_span_right S (by rintro _ ⟨b, rfl⟩; exact F.e_iso a' b) hx) hx
  have h2 := F'.z_norm
  rw [hzx] at h2
  simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
    smul_eq_mul, hxz, hzx', hxx, F.z_norm, starRingEnd_apply] at h2
  linear_combination h2

theorem nat_eq_of (ζ : (𝓞 E)ˣ) {T T' : ℕ}
    (h : ((T' : ℕ) : E) = star ((ζ : 𝓞 E) : E) * ((ζ : 𝓞 E) : E) * (T : E)) : T = T' := by
  have hn := congrArg (Algebra.norm ℚ) h
  rw [map_mul, map_mul, Algebra.norm_natCast, Algebra.norm_natCast] at hn
  have hs : Algebra.norm ℚ (star ((ζ : 𝓞 E) : E)) = Algebra.norm ℚ ((ζ : 𝓞 E) : E) := by
    have := Algebra.norm_eq_of_algEquiv (R := ℚ) (starRingAut (R := E)).toRatAlgEquiv
      ((ζ : 𝓞 E) : E)
    simpa using this
  have hu := NumberField.Units.norm E ζ
  have h1 : Algebra.norm ℚ ((ζ : 𝓞 E) : E) * Algebra.norm ℚ ((ζ : 𝓞 E) : E) = 1 := by
    rw [← abs_mul_abs_self, hu, one_mul]
  rw [hs, h1, one_mul] at hn
  have hd : Module.finrank ℚ E ≠ 0 := Module.finrank_pos.ne'
  have h3 : T' ^ Module.finrank ℚ E = T ^ Module.finrank ℚ E := by exact_mod_cast hn
  exact (Nat.pow_left_injective hd h3).symm

theorem root_of (hC : Formalism.L2.SG.IdCell.StarIsConj E) (ζ : (𝓞 E)ˣ)
    (h : star ((ζ : 𝓞 E) : E) * ((ζ : 𝓞 E) : E) = 1) : ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1 := by
  have hnorm : ∀ φ : E →+* ℂ, ‖φ ((ζ : 𝓞 E) : E)‖ = 1 := by
    intro φ
    have h1 := congrArg φ h
    rw [map_mul, hC φ, map_one, ← Complex.normSq_eq_conj_mul_self] at h1
    have h2 : ‖φ ((ζ : 𝓞 E) : E)‖ ^ 2 = 1 := by
      rw [Complex.sq_norm]; exact_mod_cast h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  obtain ⟨n, hn, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one E ℂ
    (RingOfIntegers.isIntegral_coe (ζ : 𝓞 E)) hnorm
  refine ⟨n, hn, Units.ext ?_⟩
  apply RingOfIntegers.coe_injective
  rw [Units.val_pow_eq_pow_val, Units.val_one, map_pow, map_one]
  exact hpow

theorem unitNormRoot_main : Formalism.L2.SG.IdCell.NormRoot E := by
  intro S r T T' F F' c ζ hC hT _ hS hc
  have h := norm_shift F F' (c (Fin.last r)) (hS (Fin.last r))
  rw [hc] at h
  have hTT := nat_eq_of ζ h
  subst hTT
  refine ⟨rfl, root_of hC ζ ?_⟩
  have hT0 : (T : E) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  exact mul_right_cancel₀ hT0 (h.symm.trans (one_mul _).symm)

end PI.UnitNormRootW
