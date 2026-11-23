import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.LocRingPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAD
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsMvPolynomialSubMapMem
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightParameterMemUnitInterval

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory.GaussCompletion

open IsLocalRing

section
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))

theorem mem_maximalIdeal_iff (x : la.adicCompletionIntegers K) :
    x ∈ maximalIdeal (la.adicCompletionIntegers K) ↔
      Valued.v (x : la.adicCompletion K) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  rw [mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have h1 : Valued.v (x : la.adicCompletion K) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K la).1 x.2
  constructor
  · intro h
    have h2 := lt_of_le_of_ne h1 h
    rcases eq_or_ne (Valued.v (x : la.adicCompletion K)) 0 with h0 | h0
    · rw [h0]; exact zero_le'
    · rw [← WithZero.exp_log h0] at h2 ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h2
      rw [WithZero.exp_le_exp]
      omega
  · intro h h2
    rw [h2, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
    omega

theorem algebraMap_injective :
    Function.Injective (algebraMap (𝓞 K) (la.adicCompletionIntegers K)) := by
  intro a b h
  have h1 := congrArg (fun x : la.adicCompletionIntegers K => (x : la.adicCompletion K)) h
  simp only [Formalism.MainNotions.Gaps.LocalGlobalPassage.coe_algO] at h1
  exact IsFractionRing.injective (𝓞 K) K ((algebraMap K (la.adicCompletion K)).injective h1)

theorem map_asIdeal :
    Ideal.map (algebraMap (𝓞 K) (la.adicCompletionIntegers K)) la.asIdeal =
      maximalIdeal (la.adicCompletionIntegers K) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_maximalIdeal_iff, Formalism.MainNotions.Gaps.LocalGlobalPassage.coe_algO, Formalism.MainNotions.Gaps.LocalGlobalPassage.val_alg,
      HeightOneSpectrum.valuation_of_algebraMap, la.intValuation_le_pow_iff_mem, pow_one]
    exact ha
  · intro x hx
    obtain ⟨π, hπ⟩ := la.intValuation_exists_uniformizer
    obtain ⟨d, hd⟩ := Formalism.MainNotions.Gaps.LocalGlobalPassage.exists_factor (K := K) la hπ 1 x
      ((mem_maximalIdeal_iff la x).1 hx)
    rw [hd, pow_one]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    rw [← la.intValuation_lt_one_iff_mem, hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num

theorem exists_sub_mem (x : la.adicCompletionIntegers K) :
    ∃ a : 𝓞 K, x - algebraMap (𝓞 K) (la.adicCompletionIntegers K) a ∈
      maximalIdeal (la.adicCompletionIntegers K) := by
  obtain ⟨r, hr⟩ := Formalism.MainNotions.Gaps.LocalGlobalPassage.approx (K := K) la x 1
  exact ⟨r, (mem_maximalIdeal_iff la _).2 hr⟩

end

theorem isLocalization_rename {σ τ O₁ O₂ : Type} [CommRing O₁] [CommRing O₂] (I : Ideal O₁)
    (e : σ ≃ τ) (Q : Ideal (MvPolynomial τ O₁)) [Q.IsPrime] (hQ : Q = Ideal.map MvPolynomial.C I)
    (P : Ideal (MvPolynomial σ O₁)) [P.IsPrime] (hP : P = Ideal.map MvPolynomial.C I)
    [Algebra (MvPolynomial τ O₁) O₂] [IsLocalization.AtPrime O₂ Q] :
    letI : Algebra (MvPolynomial σ O₁) O₂ :=
      ((algebraMap (MvPolynomial τ O₁) O₂).comp
        (MvPolynomial.renameEquiv O₁ e).toRingEquiv.toRingHom).toAlgebra
    IsLocalization.AtPrime O₂ P := by
  have h := IsLocalization.isLocalization_of_base_ringEquiv Q.primeCompl O₂
    (MvPolynomial.renameEquiv O₁ e).toRingEquiv.symm
  have hmap : Ideal.map (MvPolynomial.renameEquiv O₁ e).toRingEquiv.toRingHom P = Q := by
    rw [hP, hQ, Ideal.map_map]
    congr 1
    ext a
    simp
  have hmem : ∀ x, (MvPolynomial.renameEquiv O₁ e).toRingEquiv x ∈ Q ↔ x ∈ P := by
    intro x
    have hb := Ideal.comap_map_of_bijective (MvPolynomial.renameEquiv O₁ e).toRingEquiv.toRingHom
      (MvPolynomial.renameEquiv O₁ e).toRingEquiv.bijective (I := P)
    rw [hmap] at hb
    rw [← hb]
    exact Iff.rfl
  have hM : Q.primeCompl.map (MvPolynomial.renameEquiv O₁ e).toRingEquiv.symm = P.primeCompl := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ hx
      apply hy
      have := (hmem _).2 hx
      rwa [RingEquiv.apply_symm_apply] at this
    · intro hx
      exact ⟨_, fun hy => hx ((hmem x).1 hy), RingEquiv.symm_apply_apply _ _⟩
  rw [hM] at h
  exact h

theorem gaussRing_completion_rename :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N D' N' : ℕ) (e : ReciprocityTheory.ChartRestriction.G.T0.TVar D' N' ≃ Idx D j N), ∃ (f : ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la →+* Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (φ : ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N' →+* Kp X la N), f.Flat ∧ IsLocalHom f ∧ Ideal.map f (IsLocalRing.maximalIdeal (ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la)) = IsLocalRing.maximalIdeal (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) ∧ (∀ x : Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N, ∃ a, x - f a ∈ IsLocalRing.maximalIdeal (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N)) ∧ (∀ r, φ (ReciprocityTheory.ChartRestriction.G.T0.OpToKT D' N' la r) = algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N) (f r)) ∧ (∀ a : B.KO, φ (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (MvPolynomial.C a)) = algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) ∧ ∀ p, φ (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (MvPolynomial.X p)) = algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N) (Tv X la N (e p)) := by
  intro D B P j X la N D' N' e
  letI alg : Algebra (MvPolynomial (ReciprocityTheory.ChartRestriction.G.T0.TVar D' N') (X.Ol la))
      (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) :=
    ((algebraMap (Pol X la N) (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N)).comp
      (MvPolynomial.renameEquiv (X.Ol la) e).toRingEquiv.toRingHom).toAlgebra
  have halg : ∀ p, algebraMap (MvPolynomial (ReciprocityTheory.ChartRestriction.G.T0.TVar D' N') (X.Ol la))
      (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) p =
      algebraMap (Pol X la N) (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (MvPolynomial.rename e p) := fun _ => rfl
  haveI hprime := Formalism.DV.GaussP.gaussIdeal_isPrime (ReciprocityTheory.ChartRestriction.G.T0.TVar D' N') (X.Ol la)
  haveI hloc : IsLocalization.AtPrime (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N)
      (Formalism.DV.gaussIdeal (ReciprocityTheory.ChartRestriction.G.T0.TVar D' N') (X.Ol la)) :=
    isLocalization_rename (maximalIdeal (X.Ol la)) e (gI X la N) rfl
      (Formalism.DV.gaussIdeal (ReciprocityTheory.ChartRestriction.G.T0.TVar D' N') (X.Ol la)) rfl
  obtain ⟨-, f, hf, hflat, hloc', hmax, hres⟩ := GlobalTheory.gaussRing_completion B.KO D' N' la (X.Ol la)
    (algebraMap_injective la) (map_asIdeal la) (exists_sub_mem la)
    (Formalism.DV.gaussIdeal (ReciprocityTheory.ChartRestriction.G.T0.TVar D' N') (X.Ol la)) rfl (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N)
  have hinj₂ : Function.Injective (algebraMap (Pol X la N) (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N)) :=
    IsLocalization.injective _ (gI X la N).primeCompl_le_nonZeroDivisors
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨p, s⟩, h⟩ := IsLocalization.surj (ReciprocityTheory.ChartRestriction.G.T0.laT D' N' la).primeCompl x
    have h1 := congrArg f h
    rw [map_mul, hx, zero_mul, hf, halg] at h1
    have h2 : p = 0 := by
      have h3 := hinj₂ (h1.symm.trans (map_zero _).symm)
      have h4 := MvPolynomial.rename_injective e e.injective (h3.trans (map_zero _).symm)
      exact MvPolynomial.map_injective _ (algebraMap_injective la) (h4.trans (map_zero _).symm)
    simp only [h2, map_zero] at h
    exact (IsLocalization.map_units (ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la) s).mul_left_eq_zero.mp h
  letI := ReciprocityTheory.ChartRestriction.G.T0.algOpKT (K := B.KO) D' N' la
  haveI := ReciprocityTheory.ChartRestriction.G.T0.isFractionRing_Op (K := B.KO) D' N' la
  have hg : Function.Injective
      ((algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N)).comp f) :=
    (IsFractionRing.injective (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N)).comp hfinj
  let φ : ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N' →+* Kp X la N :=
    IsFractionRing.lift (A := ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la) hg
  have hφ : ∀ r, φ (ReciprocityTheory.ChartRestriction.G.T0.OpToKT D' N' la r) =
      algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N) (f r) := fun r =>
    IsFractionRing.lift_algebraMap (A := ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la) hg r
  have hφp : ∀ p : ReciprocityTheory.ChartRestriction.G.T0.OT B.KO D' N',
      φ (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N')
        (MvPolynomial.map (algebraMap (𝓞 B.KO) B.KO) p)) =
      algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N)
        (algebraMap (Pol X la N) (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N)
          (MvPolynomial.rename e (MvPolynomial.map (algebraMap (𝓞 B.KO) (X.Ol la)) p))) := by
    intro p
    rw [← halg, ← hf, ← hφ, ReciprocityTheory.ChartRestriction.G.T0.OpToKT, IsLocalization.lift_eq]
    rfl
  refine ⟨f, φ, hflat, hloc', hmax, hres, hφ, ?_, ?_⟩
  · have key : (φ.comp ((algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N')
        (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N')).comp MvPolynomial.C)) =
        (algebraMap (X.Kl la) (Kp X la N)).comp (algebraMap B.KO (X.Kl la)) := by
      refine IsFractionRing.ringHom_ext (A := 𝓞 B.KO) fun a => ?_
      have h1 := hφp (MvPolynomial.C a)
      rw [MvPolynomial.map_C, MvPolynomial.map_C, MvPolynomial.rename_C] at h1
      simp only [RingHom.comp_apply]
      rw [h1, ← Formalism.MainNotions.Gaps.LocalGlobalPassage.coe_algO]
      change _ = algebraMap (X.Kl la) (Kp X la N)
        (algebraMap (X.Ol la) (X.Kl la) (algebraMap (𝓞 B.KO) (X.Ol la) a))
      rw [← IsScalarTower.algebraMap_apply (X.Ol la) (X.Kl la) (Kp X la N),
        IsScalarTower.algebraMap_apply (X.Ol la) (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N),
        IsScalarTower.algebraMap_apply (X.Ol la) (Pol X la N) (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N),
        MvPolynomial.algebraMap_eq]
    intro a
    exact DFunLike.congr_fun key a
  · intro p
    have h1 := hφp (MvPolynomial.X p)
    rw [MvPolynomial.map_X, MvPolynomial.map_X, MvPolynomial.rename_X] at h1
    exact h1

end GlobalTheory.GaussCompletion
