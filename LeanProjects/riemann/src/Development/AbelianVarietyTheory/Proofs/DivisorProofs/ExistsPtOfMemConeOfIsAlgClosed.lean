import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedLatticeZeroCycleHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NullstellensatzPointOfSystem

set_option autoImplicit false
noncomputable section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort
open GlobalTheory.CompHt

namespace GlobalTheory.ConeOnto

theorem exists_pt_of_mem_cone_of_isAlgClosed : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → S.BasePointFree → ∀ (K : Type) [Field K] [Algebra F K] [IsAlgClosed K] (y : Fin S.N → K), y ≠ 0 → (∀ g ∈ S.imageIdeal, aeval y g = 0) → ∃ (x : S.Pt K) (c : K), c ≠ 0 ∧ S.coords x.1 = c • y := by
  intro F _ S hS hb K _ _ _ y hy hI
  classical
  by_contra hno
  push_neg at hno
  have hT : (S.baseChange K).IsVariety := hS.baseChange K
  have hbT : (S.baseChange K).BasePointFree := hb.baseChange K
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hy
  change y i₀ ≠ 0 at hi₀
  let u : Fin S.N → Fin S.N → K := fun j => y i₀ • Pi.single j 1 - y j • Pi.single i₀ 1
  have hu : ∀ (j : Fin S.N) (c : Fin S.N → K), ∑ l, u j l * c l = y i₀ * c j - y j * c i₀ := fun j c => by
    simp [u, sub_mul, Finset.sum_sub_distrib, Pi.single_apply, mul_assoc]

  have hcov : ∀ z : (S.baseChange K).Y, ∃ j, z ∈ nonzeroLocus ((S.baseChange K).comb (u j)) := by
    by_contra hc
    push_neg at hc
    obtain ⟨z, hz⟩ := hc
    have := hT.smooth
    have : Smooth (S.baseChange K).str := SmoothOfRelativeDimension.smooth (S.baseChange K).D _
    have hZ : IsClosed (⋂ j, ((nonzeroLocus ((S.baseChange K).comb (u j)) : Set (S.baseChange K).Y)ᶜ)) :=
      isClosed_iInter fun j => (nonzeroLocus ((S.baseChange K).comb (u j))).isOpen.isClosed_compl
    obtain ⟨a, ha, haZ⟩ := GlobalTheory.ConeOnto.exists_rat_pt (S.baseChange K).str hZ.isLocallyClosed
      (x := z) (Set.mem_iInter.2 hz)
    let xa : (S.baseChange K).Pt K := ⟨a, ha.trans (Spec.map_id _).symm⟩
    have hbase : (S.baseChange K).baseHom a = RingHom.id K := LinSys.baseHom_ptOver xa
    have hv : ∀ j, y i₀ * (S.baseChange K).coords a j - y j * (S.baseChange K).coords a i₀ = 0 := fun j => by
      have h0 := Set.mem_iInter.1 (haZ (IsLocalRing.closedPoint K)) j
      have h1 : (S.baseChange K).val a ((S.baseChange K).comb (u j)) = 0 :=
        not_not.1 fun h => h0 (((S.baseChange K).val_ne_zero_iff a _).1 h)
      have h2 := ((S.baseChange K).val_comb a (u j)).symm.trans h1
      rw [hbase] at h2
      simp only [RingHom.id_apply] at h2
      exact (hu j ((S.baseChange K).coords a)).symm.trans h2
    have hc0 : (S.baseChange K).coords a i₀ ≠ 0 := fun h0 => hbT.coords_ne_zero a (funext fun j => by
      have := hv j
      rw [h0, mul_zero, sub_zero] at this
      exact (mul_eq_zero.1 this).resolve_left hi₀)
    obtain ⟨c, hc, e⟩ := S.exists_coords_baseChange K a
    refine hno (LinSys.toBase xa) (c⁻¹ * ((S.baseChange K).coords a i₀ / y i₀))
      (mul_ne_zero (inv_ne_zero hc) (div_ne_zero hc0 hi₀)) (funext fun j => ?_)
    have ej := congrFun e j
    have hvj := hv j
    change S.coords (a ≫ S.bcFst K) j = _
    simp only [Pi.smul_apply, smul_eq_mul] at ej ⊢
    have e1 : S.coords (a ≫ S.bcFst K) j = c⁻¹ * (S.baseChange K).coords a j := by
      rw [ej, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    have e2 : (S.baseChange K).coords a j = (S.baseChange K).coords a i₀ / y i₀ * y j := by
      field_simp
      linear_combination hvj
    rw [e1, e2]
    ring

  have hX : (X i₀ : MvPolynomial (Fin (S.baseChange K).N) K).IsHomogeneous 1 := isHomogeneous_X K i₀
  obtain ⟨m, A, hA, hrel⟩ := GlobalTheory.SecIntegral.exists_integral_relation K (S.baseChange K) hT S.N 1 u
    ((S.baseChange K).form hX) hcov
  let σ : Fin S.N → MvPolynomial (Fin S.N) K := fun i => ∑ j, C (u i j) * X j
  have hσ : ∀ i, (σ i).IsHomogeneous 1 := fun i =>
    IsHomogeneous.sum _ _ _ fun j _ => by
      simpa using (isHomogeneous_C (Fin S.N) (u i j)).mul (isHomogeneous_X K j)
  let G : MvPolynomial (Fin S.N) K := X i₀ ^ m + ∑ k : Fin m, bind₁ σ (A k) * X i₀ ^ (k : ℕ)
  have hG : G.IsHomogeneous m := by
    refine (isHomogeneous_X_pow i₀ m).add (IsHomogeneous.sum _ _ _ fun k _ => ?_)
    have h1 : (bind₁ σ (A k)).IsHomogeneous (1 * (1 * (m - k))) :=
      (hA k).eval₂ C σ (fun r => isHomogeneous_C _ r) hσ
    have h2 := h1.mul (isHomogeneous_X_pow i₀ (k : ℕ))
    have e : 1 * (1 * (m - (k : ℕ))) + k = m := by omega
    rwa [e] at h2

  haveI := HeightExists.isIntegral hT
  obtain ⟨Ω, _, _, xg, hxg, -⟩ := HeightExists.exists_generic hT
  have hmem : G ∈ (S.baseChange K).imageIdeal := by
    rw [imageIdeal_eq_coneIdeal_of_generic K Ω _ xg hxg 1 _ one_ne_zero (one_smul _ _).symm]
    refine (mem_coneIdeal_of_isHomogeneous (K := K) (N := S.N) _ hG).2 ?_
    have h := hrel Ω xg
    rw [LinSys.powVal_form, LinSys.baseHom_ptOver] at h
    erw [eval₂_X] at h
    let cg : Fin S.N → Ω := (S.baseChange K).coords xg.1
    have h' : cg i₀ ^ m + ∑ k : Fin m, aeval (fun i : Fin S.N => ∑ j : Fin S.N, algebraMap K Ω (u i j) * cg j) (A k) *
        cg i₀ ^ (k : ℕ) = 0 := h
    show aeval cg G = 0
    simp only [G, σ, map_add, map_pow, map_sum, map_mul, aeval_X, aeval_bind₁, aeval_C]
    exact h'

  rw [← HeightExists.map_imageIdeal hS K] at hmem
  have hker : S.imageIdeal.map (MvPolynomial.map (algebraMap F K)) ≤ RingHom.ker (eval y) :=
    Ideal.map_le_iff_le_comap.2 fun g hg => by
      rw [Ideal.mem_comap, RingHom.mem_ker, MvPolynomial.eval_map, ← aeval_def]
      exact hI g hg
  have h0 : eval y G = 0 := hker hmem
  have hA0 : ∀ k : Fin m, eval y (bind₁ σ (A k)) = 0 := fun k => by
    show aeval y (bind₁ σ (A k)) = 0
    rw [aeval_bind₁]
    have e : (fun i => aeval y (σ i)) = 0 := funext fun i => by
      simp only [σ, map_sum, map_mul, aeval_C, aeval_X, Algebra.algebraMap_self, RingHom.id_apply, Pi.zero_apply]
      rw [hu i y]
      ring
    rw [e, aeval_zero, Algebra.algebraMap_self, RingHom.id_apply, constantCoeff, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk]
    exact (hA k).coeff_eq_zero (d := 0) (by simp; omega)
  have h3 : eval y G = y i₀ ^ m := by
    simp only [G, map_add, map_pow, map_sum, map_mul, eval_X, hA0, zero_mul, Finset.sum_const_zero, add_zero]
  exact pow_ne_zero m hi₀ (h3.symm.trans h0)

end GlobalTheory.ConeOnto
