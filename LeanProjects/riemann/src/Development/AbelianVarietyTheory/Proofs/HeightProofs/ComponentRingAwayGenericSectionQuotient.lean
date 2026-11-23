import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAE
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
import Development.AbelianVarietyTheory.Proofs.AlgebraicCurves.ExistsMulEqMapOfIsAlgebraic

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory

theorem exists_away_algHom_ker {K R Q : Type*} [CommRing K] [CommRing R] [CommRing Q] [Algebra K R] [Algebra K Q]
    {n : ℕ} (Ψ : R →ₐ[K] Q) (a : Fin (n + 1) → R) (hs : Function.Surjective Ψ)
    (hk : RingHom.ker Ψ = Ideal.span (Set.range fun i : Fin n => a i.succ)) (hu : IsUnit (Ψ (a 0))) :
    ∃ χ : Localization.Away (a 0) →ₐ[K] Q, Function.Surjective χ ∧
      RingHom.ker χ = Ideal.span (Set.range fun i : Fin n =>
        algebraMap R (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0)) ∧
      ∀ r, χ (algebraMap R (Localization.Away (a 0)) r) = Ψ r := by
  have hunit : ∀ y : Submonoid.powers (a 0), IsUnit (Ψ y) := by
    rintro ⟨_, m, rfl⟩
    simpa using hu.pow m
  let χ : Localization.Away (a 0) →ₐ[K] Q := IsLocalization.liftAlgHom (M := Submonoid.powers (a 0)) hunit
  have hχ : ∀ r, χ (algebraMap R (Localization.Away (a 0)) r) = Ψ r := fun r => by
    simp [χ]
  refine ⟨χ, fun q => ?_, le_antisymm ?_ ?_, hχ⟩
  · obtain ⟨r, rfl⟩ := hs q
    exact ⟨_, hχ r⟩
  · intro z hz
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (Submonoid.powers (a 0)) z
    have hr : r ∈ RingHom.ker Ψ := by
      rw [RingHom.mem_ker] at hz ⊢
      have := congrArg χ hrs
      rw [map_mul, hz, zero_mul, hχ] at this
      exact this.symm
    rw [hk] at hr
    have hle : Ideal.span (Set.range fun i : Fin n => a i.succ) ≤
        (Ideal.span (Set.range fun i : Fin n =>
          algebraMap R (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0))).comap
          (algebraMap R (Localization.Away (a 0))) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      have e : algebraMap R (Localization.Away (a 0)) (a i.succ) =
          algebraMap R (Localization.Away (a 0)) (a 0) *
            (algebraMap R (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0)) := by
        rw [mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one]
      show algebraMap R (Localization.Away (a 0)) (a i.succ) ∈ Ideal.span _
      rw [e]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    have h2 := hle hr
    rw [Ideal.mem_comap] at h2
    simp only at hrs
    rw [← hrs] at h2
    exact (Ideal.mul_unit_mem_iff_mem _ (IsLocalization.map_units _ s)).1 h2
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have : Ψ (a i.succ) = 0 := by
      rw [← RingHom.mem_ker, hk]
      exact Ideal.subset_span ⟨i, rfl⟩
    show χ _ = 0
    rw [map_mul, hχ, this, zero_mul]

open ReciprocityTheory.ChartRestriction.G.T0 in

theorem genericSection_away_quotient {K Ω Kl K' : Type} [Field K] [Field Ω] [Algebra K Ω] [Field Kl] [Field K']
    [Algebra K Kl] [Algebra Kl K'] {Dd m D' N' : ℕ} (hD : D' + 1 = Dd + 1) (eN : Fin (N' + 1) ≃ Fin m)
    (j₀ : Fin (N' + 1)) (x : Fin N' → Ω) [Algebra (KTf K D' N') (OmS Ω D' N')]
    [FiniteDimensional (KTf K D' N') (OmS Ω D' N')] [Algebra (KTf K D' N') K']
    (t : Fin (Dd + 1) × Fin m → K') (v : Fin m → Ω)
    (hs : ∀ p : KTp K D' N', algebraMap (KTf K D' N') (OmS Ω D' N') (algebraMap (KTp K D' N') (KTf K D' N') p) =
      sHom j₀ x p)
    (hK : ∀ a : K, algebraMap (KTf K D' N') K' (algebraMap K (KTf K D' N') a) = algebraMap Kl K' (algebraMap K Kl a))
    (ht : ∀ q : TVar D' N', algebraMap (KTf K D' N') K' (algebraMap (KTp K D' N') (KTf K D' N') (MvPolynomial.X q)) =
      t (Fin.cast hD q.1, eN q.2))
    (hv : v (eN j₀) ≠ 0) (hx : ∀ k, x k * v (eN j₀) = v (eN (j₀.succAbove k)))
    (a : Fin (Dd + 1) → K' ⊗[Kl] (Kl ⊗[K] Ω)) (ha : ∀ i, a i = ∑ k, t (i, k) ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] v k)) :
    ∃ χ : Localization.Away (a 0) →ₐ[K'] K' ⊗[KTf K D' N'] OmS Ω D' N', Function.Surjective χ ∧
      RingHom.ker χ = Ideal.span (Set.range fun i : Fin Dd =>
        algebraMap _ (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0)) ∧
      ∀ ω : Ω, χ (algebraMap (K' ⊗[Kl] (Kl ⊗[K] Ω)) (Localization.Away (a 0)) ((1 : K') ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] ω))) =
        (1 : K') ⊗ₜ[KTf K D' N'] algebraMap Ω (OmS Ω D' N') ω := by
  obtain rfl : D' = Dd := by omega
  letI : Algebra K K' := ((algebraMap Kl K').comp (algebraMap K Kl)).toAlgebra
  haveI : IsScalarTower K Kl K' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower K (KTf K D' N') K' := IsScalarTower.of_algebraMap_eq fun c => (hK c).symm
  obtain ⟨Φ, hΦ, hsurj, hker, hunit⟩ := genericSection_quotient K Ω K' D' N' j₀ x
    (fun q => t (q.1, eN q.2)) (fun k => v (eN k) / v (eN j₀)) hs (fun q => (ht q).symm) (div_self hv)
    (fun k => by rw [div_eq_iff hv, hx])
  let Φ' : K' ⊗[K] Ω →ₐ[K'] K' ⊗[KTf K D' N'] OmS Ω D' N' :=
    { Φ with
      commutes' := fun c => by
        show Φ (c ⊗ₜ[K] 1) = c ⊗ₜ 1
        rw [hΦ, map_one] }
  let e : K' ⊗[Kl] (Kl ⊗[K] Ω) ≃ₐ[K'] K' ⊗[K] Ω := Algebra.TensorProduct.cancelBaseChange K Kl K' K' Ω
  have he : ∀ (c : K') (ω : Ω), e (c ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] ω)) = c ⊗ₜ[K] ω := fun c ω => by
    simp [e]
  let u : K' ⊗[K] Ω := (1 : K') ⊗ₜ[K] v (eN j₀)
  have hu : IsUnit u :=
    (IsUnit.mk0 _ hv).map (Algebra.TensorProduct.includeRight (R := K) (A := K') (B := Ω))
  have hea : ∀ i, e (a i) = u * ∑ k, t (i, eN k) ⊗ₜ[K] (v (eN k) / v (eN j₀)) := fun i => by
    rw [ha, map_sum, Finset.mul_sum, ← Equiv.sum_comp eN]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [he, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_div_cancel₀ _ hv]
  have hΨ : ∀ r, (Φ'.comp e.toAlgHom) r = Φ (e r) := fun _ => rfl
  obtain ⟨χ, h1, h2, h3⟩ := exists_away_algHom_ker (Φ'.comp e.toAlgHom) a (hsurj.comp e.surjective)
    (by
      apply le_antisymm
      · intro r hr
        have hr' : e r ∈ RingHom.ker Φ := hr
        rw [hker] at hr'
        have hle : Ideal.span (Set.range fun i : Fin D' =>
            (∑ k, t (i.succ, eN k) ⊗ₜ[K] (v (eN k) / v (eN j₀)) : K' ⊗[K] Ω)) ≤
            (Ideal.span (Set.range fun i : Fin D' => a i.succ)).comap e.symm := by
          rw [Ideal.span_le]
          rintro _ ⟨i, rfl⟩
          have h0 : a i.succ ∈ Ideal.span (Set.range fun i : Fin D' => a i.succ) := Ideal.subset_span ⟨i, rfl⟩
          rw [← e.symm_apply_apply (a i.succ), hea, map_mul,
            Ideal.unit_mul_mem_iff_mem _ (hu.map e.symm)] at h0
          exact h0
        have := hle hr'
        rwa [Ideal.mem_comap, AlgEquiv.symm_apply_apply] at this
      · rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        show Φ (e (a i.succ)) = 0
        have : Φ (∑ k, t (i.succ, eN k) ⊗ₜ[K] (v (eN k) / v (eN j₀))) = 0 := by
          rw [← RingHom.mem_ker, hker]
          exact Ideal.subset_span ⟨i, rfl⟩
        rw [hea, map_mul, this, mul_zero])
    (by rw [hΨ, hea, map_mul]; exact (hu.map Φ).mul hunit)
  exact ⟨χ, h1, h2, fun ω => by rw [h3, hΨ, he, hΦ]⟩

section Rec

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) (Ω : Type) [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω) {wL : WeightFamilies.Wt D j}
  (w : Fin N → B.Cusp j wL)

theorem componentRing_sec_eq_sum (i : Fin (WeightFamilies.dimY D j + 1)) :
    rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i) =
      ∑ k, algebraMap (Op X la N) (Kp X la N) (Tv X la N (i, k)) ⊗ₜ[X.Kl la]
        ((1 : X.Kl la) ⊗ₜ[B.KO] gF (X.inc wL (w k))) := by
  rw [Formalism.MainNotions.Gaps.EtaleWeightGaps.sec, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, rzMap_emb, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem componentRing_map_sectionIdeal : Ideal.map (phiZ X la N Ω gF w) (Jid X la w) =
    Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
      algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i.succ)) *
        IsLocalization.Away.invSelf (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))) := by
  have key : ∀ {R : Type} [CommRing R] {a b c : R}, a * b = 1 → a * c = 1 → b = c :=
    fun {_} _ {_} {b} {c} h1 h2 => by linear_combination c * h1 - b * h2
  rw [Jid, Ideal.map_span, ← Set.range_comp]
  refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
  show phiZ X la N Ω gF w (sfr X la w i.succ) = _
  rw [phiZ_apply, coe_sfr, frac_apply, pow_one, map_mul, lwZ_alg]
  congr 1
  have h1 := congrArg (lwZ X la N Ω gF w) (section_mul_inverse_eq_one X la w)
  rw [map_mul, lwZ_alg, map_one] at h1
  exact key h1 (IsLocalization.Away.mul_invSelf _)

end Rec

theorem componentRing_away_quotient :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (wL : WeightFamilies.Wt D j) (w : Fin N → B.Cusp j wL) (Ω : Type) [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω) (D' N' : ℕ) (hD : D' + 1 = WeightFamilies.dimY D j + 1) (eN : Fin (N' + 1) ≃ Fin N) (j₀ : Fin (N' + 1)) (x : Fin N' → Ω) [Algebra (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N')] [FiniteDimensional (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N')] [Algebra (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (Kp X la N)], (∀ p : ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N', algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N') (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') p) = ReciprocityTheory.ChartRestriction.G.T0.sHom j₀ x p) → (∀ a : B.KO, algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (Kp X la N) (algebraMap B.KO (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') a) = algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) → (∀ q : ReciprocityTheory.ChartRestriction.G.T0.TVar D' N', algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (Kp X la N) (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (MvPolynomial.X q)) = algebraMap (Op X la N) (Kp X la N) (Tv X la N (Fin.cast hD q.1, eN q.2))) → gF (X.inc wL (w (eN j₀))) ≠ 0 → (∀ k, x k * gF (X.inc wL (w (eN j₀))) = gF (X.inc wL (w (eN (j₀.succAbove k))))) → ∃ χ : RZs X la N Ω gF w →ₐ[Kp X la N] Kp X la N ⊗[ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N'] ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N', Function.Surjective χ ∧ RingHom.ker χ = Ideal.map (phiZ X la N Ω gF w) (Jid X la w) ∧ ∀ ω : Ω, χ (CurveLoc.psiZ X la N w gF ω) = (1 : Kp X la N) ⊗ₜ[ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N'] algebraMap Ω (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N') ω := by
  intro D B P j X la N wL w Ω _ _ gF D' N' hD eN j₀ x _ _ _ hs hK ht hv hx
  rw [componentRing_map_sectionIdeal]
  exact genericSection_away_quotient (Kl := X.Kl la) hD eN j₀ x
    (fun p => algebraMap (Op X la N) (Kp X la N) (Tv X la N p)) (fun k => gF (X.inc wL (w k))) hs hK ht hv hx
    (fun i => rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i))
    (fun i => componentRing_sec_eq_sum X la N Ω gF w i)

end GlobalTheory
