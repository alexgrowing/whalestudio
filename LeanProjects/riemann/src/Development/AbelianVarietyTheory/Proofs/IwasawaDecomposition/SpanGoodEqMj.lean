import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.LocalRingCardinality.DataKap
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidualCharacterDetValuesMemCoeffField

noncomputable section

open NumberField IsDedekindDomain Module

namespace GlobalTheory.GoodLatDescent

section General

variable {K L V : Type} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module L V] [Module K V]
  [IsScalarTower K L V] {ι : Type} [Fintype ι]

def coordMap (b : Basis ι L V) (φ : L →ₗ[K] K) : V →ₗ[K] V :=
  ∑ i, (φ ∘ₗ (b.coord i).restrictScalars K).smulRight (b i)

theorem coordMap_apply (b : Basis ι L V) (φ : L →ₗ[K] K) (x : V) :
    coordMap b φ x = ∑ i, φ (b.repr x i) • b i := by
  simp [coordMap, LinearMap.sum_apply, Basis.coord_apply]

theorem coordMap_smul (b : Basis ι L V) (φ : L →ₗ[K] K) {w : V} (hw : w ∈ Submodule.span K (Set.range b)) (a : L) :
    coordMap b φ (a • w) = φ a • w := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    rw [coordMap_apply, map_smul, Basis.repr_self]
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [Finsupp.single_apply, Ne.symm hi]) (by simp)]
    simp
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add, map_add, hx, hy, smul_add]
  | smul c x _ hx => rw [smul_comm a c x, LinearMap.map_smul, hx, smul_comm]

theorem coordMap_comm (b : Basis ι L V) (φ : L →ₗ[K] K) (T : V →ₗ[L] V)
    (hT : ∀ w ∈ Submodule.span K (Set.range b), T w ∈ Submodule.span K (Set.range b)) (x : V) :
    T (coordMap b φ x) = coordMap b φ (T x) := by
  rw [coordMap_apply, map_sum]
  conv_rhs => rw [← b.sum_repr x, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smul_of_tower T (φ (b.repr x i)) (b i), LinearMap.map_smul T (b.repr x i) (b i),
    coordMap_smul b φ (hT _ (Submodule.subset_span ⟨i, rfl⟩))]

end General

section Forms

open Formalism.IndefR.Arith

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G0 : Type} [Group G0] [Fintype G0]
variable (A : FormsL LL Ks WL W G0)

private theorem coordMap_mem_Wgood (hρ : ∀ g, ∀ f ∈ A.WK, A.ρ g f ∈ A.WK) (hχ : A.ChiKs)
    (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL)
    (hl : ∀ p, ((lam0 p : LLˣ) : LL) ∈ (algebraMap Ks LL).range) (he : ∀ g, eC g ∈ (algebraMap Ks LL).range)
    {n : ℕ} (B : Basis (Fin n) LL WL) (hWK : Submodule.span Ks (Set.range B) = A.WK)
    (φ : LL →ₗ[Ks] Ks) (y : WL) (hy : y ∈ A.Wgood J0 lam0 eC) : coordMap B φ y ∈ A.Wgood J0 lam0 eC := by
  have smulK : ∀ (c : Ks) (y : WL),
      coordMap B φ (algebraMap Ks LL c • y) = algebraMap Ks LL c • coordMap B φ y := by
    intro c y
    rw [algebraMap_smul, algebraMap_smul, LinearMap.map_smul]
  have hT : ∀ T : WL →ₗ[LL] WL, (∀ w ∈ A.WK, T w ∈ A.WK) →
      ∀ w ∈ Submodule.span Ks (Set.range B), T w ∈ Submodule.span Ks (Set.range B) := by
    intro T hT w hw
    rw [hWK] at hw ⊢
    exact hT w hw
  have hE : ∀ w ∈ A.WK, A.eOp eC w ∈ A.WK := by
    intro w hw
    show (∑ g, (eC g * ((A.chi g)⁻¹ : LLˣ)) • A.ρ g) w ∈ A.WK
    rw [LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun g _ => ?_
    obtain ⟨c1, hc1⟩ := he g
    obtain ⟨c2, hc2⟩ := hχ g
    have : (eC g * ((A.chi g)⁻¹ : LLˣ)) = algebraMap Ks LL (c1 * c2⁻¹) := by
      rw [map_mul, map_inv₀, hc1, hc2, Units.val_inv_eq_inv_val]
    rw [LinearMap.smul_apply, this, algebraMap_smul]
    exact Submodule.smul_mem _ _ (hρ g w hw)
  obtain ⟨hy1, z, hz⟩ := hy
  refine ⟨?_, coordMap B φ z, ?_⟩
  · intro p
    have hp : ∀ q : J0, (y : WL) ∈ A.typeP J0 lam0 → A.ρ q y = ((A.chi q * lam0 q : LLˣ) : LL) • y := fun q h => h q
    obtain ⟨c1, hc1⟩ := hχ p
    obtain ⟨c2, hc2⟩ := (RingHom.mem_range).1 (hl p)
    have hc : ((A.chi p * lam0 p : LLˣ) : LL) = algebraMap Ks LL (c1 * c2) := by
      rw [Units.val_mul, map_mul, hc1, hc2]
    rw [coordMap_comm B φ (A.ρ p) (hT _ (hρ p)), hp p hy1, hc, smulK]
  · rw [← hz]
    exact coordMap_comm B φ (A.eOp eC) (hT _ hE) z

variable [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]

theorem span_MK_good (hK : A.IsKsForm) (hρ : ∀ g, ∀ f ∈ A.WK, A.ρ g f ∈ A.WK) (hχ : A.ChiKs)
    (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL)
    (hl : ∀ p, ((lam0 p : LLˣ) : LL) ∈ (algebraMap Ks LL).range) (he : ∀ g, eC g ∈ (algebraMap Ks LL).range) :
    Submodule.span (𝓞 LL) {y | y ∈ A.MK ∧ y ∈ A.Wgood J0 lam0 eC} = A.Mj J0 lam0 eC := by
  obtain ⟨n, b, -, -, hspK, hbL, hspL⟩ := hK
  let B : Basis (Fin n) LL WL := Basis.mk hbL (by rw [hspL])
  have hB : (B : Fin n → WL) = b := Basis.coe_mk _ _
  have hWK : Submodule.span Ks (Set.range B) = A.WK := by rw [hB, hspK]
  have hMW : ∀ m ∈ A.MK, m ∈ A.WK := by
    intro m hm
    obtain ⟨h, -⟩ := hm
    exact h
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y ⟨hyM, hyT, hyG⟩
    exact ⟨⟨Submodule.subset_span hyM, hyT⟩, hyG⟩
  rintro z ⟨⟨hzM, hzT⟩, hzG⟩
  have hzW : z ∈ A.Wgood J0 lam0 eC := ⟨hzT, hzG⟩
  obtain ⟨r, a, g, rfl⟩ := (Submodule.mem_span_set').1 hzM

  have sOL : ∀ (c : 𝓞 LL) (w : WL), c • w = (c : LL) • w := fun c w => (algebraMap_smul LL c w).symm
  have sOK : ∀ (c : 𝓞 Ks) (w : WL), c • w = algebraMap Ks LL (c : Ks) • w := by
    intro c w
    rw [algebraMap_smul LL (c : Ks) w]
    exact (algebraMap_smul Ks c w).symm
  have sOKL : ∀ (c : 𝓞 Ks) (x : LL), c • x = algebraMap Ks LL (c : Ks) * x := by
    intro c x
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply (𝓞 Ks) Ks LL]
  haveI : Module.Finite Ks LL := Module.Finite.of_restrictScalars_finite ℚ Ks LL
  haveI : Module.Finite LL WL := Module.Finite.of_basis B
  haveI : Module.Finite Ks WL := Module.Finite.trans LL WL
  set Wg : Submodule Ks WL := (A.Wgood J0 lam0 eC).restrictScalars Ks with hWg
  set v := Module.finBasis Ks (WL ⧸ Wg) with hv
  set l := Module.finBasis Ks LL with hl'
  set m : Fin r → WL := fun j => (g j : WL) with hm
  have hmW : ∀ j, m j ∈ A.WK := fun j => hMW _ (g j).2
  set q : Fin r → Fin (Module.finrank Ks (WL ⧸ Wg)) → Ks := fun j t => v.repr (Wg.mkQ (m j)) t with hq

  have hrel : ∀ t, ∑ j, q j t • (a j : LL) = 0 := by
    intro t
    refine l.ext_elem fun k => ?_
    have hc := coordMap_mem_Wgood A hρ hχ J0 lam0 eC hl he B hWK (l.coord k) _ hzW
    have hc' : coordMap B (l.coord k) (∑ j, a j • m j) = ∑ j, l.coord k (a j : LL) • m j := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [sOL, coordMap_smul B (l.coord k) (by rw [hWK]; exact hmW j)]
    rw [hc'] at hc
    have h0 : Wg.mkQ (∑ j, l.coord k (a j : LL) • m j) = 0 := (Submodule.Quotient.mk_eq_zero Wg).2 hc
    have h1 := congrArg (fun u => v.repr u t) h0
    simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
      map_zero, Finsupp.coe_zero, Pi.zero_apply] at h1
    simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
      map_zero, Finsupp.coe_zero, Pi.zero_apply, Basis.coord_apply] at h1 ⊢
    rw [← h1]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 Ks))
    (fun p : Fin r × Fin (Module.finrank Ks (WL ⧸ Wg)) => q p.1 p.2)
  have hd' : ∀ p : Fin r × Fin (Module.finrank Ks (WL ⧸ Wg)),
      ∃ c : 𝓞 Ks, algebraMap (𝓞 Ks) Ks c = (d : 𝓞 Ks) • q p.1 p.2 := fun p => hd p
  choose rr hrr using hd'
  have hd0 : algebraMap (𝓞 Ks) Ks d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 Ks) Ks)).2 (nonZeroDivisors.coe_ne_zero d)
  have hr : ∀ j t, algebraMap (𝓞 Ks) Ks (rr (j, t)) = algebraMap (𝓞 Ks) Ks d * q j t := by
    intro j t
    rw [hrr (j, t), Algebra.smul_def]

  let I : Submodule (𝓞 Ks) LL := Submodule.span (𝓞 Ks) (Set.range (fun c : 𝓞 LL => (c : LL)))
  have hI : ∀ x ∈ I, IsIntegral ℤ x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      exact RingOfIntegers.isIntegral_coe c
    | zero => exact isIntegral_zero
    | add x y _ _ hx hy => exact hx.add hy
    | smul c x _ hx =>
      rw [sOKL]
      exact ((RingOfIntegers.isIntegral_coe c).algebraMap).mul hx
  haveI : Module.IsTorsionFree (𝓞 Ks) I := ⟨fun c hc x y hxy => by
    have hc0 : algebraMap (𝓞 Ks) Ks c ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 Ks) Ks)).2 hc.ne_zero
    apply Subtype.ext
    have h2 := congrArg Subtype.val hxy
    simp only [Submodule.coe_smul, sOKL] at h2
    exact mul_left_cancel₀ ((map_ne_zero_iff _ (algebraMap Ks LL).injective).2 hc0) h2⟩
  let aI : Fin r → I := fun j => ⟨(a j : LL), Submodule.subset_span ⟨a j, rfl⟩⟩
  let X : (Fin r →₀ 𝓞 Ks) →ₗ[𝓞 Ks] I := Finsupp.linearCombination (𝓞 Ks) aI
  let F : (Fin (Module.finrank Ks (WL ⧸ Wg)) →₀ 𝓞 Ks) →ₗ[𝓞 Ks] (Fin r →₀ 𝓞 Ks) :=
    Finsupp.linearCombination (𝓞 Ks) (fun t => ∑ j, rr (j, t) • Finsupp.single j (1 : 𝓞 Ks))
  have hsum : ∀ t, ∑ j, rr (j, t) • aI j = 0 := by
    intro t
    apply Subtype.ext
    rw [Submodule.coe_sum, Submodule.coe_zero]
    simp only [Submodule.coe_smul, sOKL, aI]
    have h3 := congrArg (fun u => algebraMap Ks LL (algebraMap (𝓞 Ks) Ks d) * u) (hrel t)
    simp only [mul_zero, Finset.mul_sum, Algebra.smul_def] at h3
    rw [← h3]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, ← map_mul, ← hr j t]
  have hXF : X ∘ₗ F = 0 := by
    apply Finsupp.lhom_ext
    intro t c
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, F, X, Finsupp.linearCombination_single, map_smul,
      map_sum, one_smul]
    rw [hsum t, smul_zero]
  obtain ⟨k, Am, Y, hXY, hAF⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free hXF
  let Aj : Fin r → Fin k → 𝓞 Ks := fun j κ => Am (Finsupp.single j 1) κ
  let yy : Fin k → 𝓞 LL := fun κ => ⟨(Y (Finsupp.single κ 1) : LL), hI _ (Y _).2⟩
  let w : Fin k → WL := fun κ => ∑ j, Aj j κ • m j
  have ha : ∀ j, (a j : LL) = ∑ κ, Aj j κ • (Y (Finsupp.single κ 1) : LL) := by
    intro j
    have h1 : X (Finsupp.single j 1) = Y (Am (Finsupp.single j 1)) := LinearMap.congr_fun hXY _
    have h2 : (X (Finsupp.single j 1) : LL) = (a j : LL) := by simp [X, aI]
    rw [← h2, h1]
    conv_lhs => rw [← Finsupp.univ_sum_single (Am (Finsupp.single j 1))]
    rw [map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [show Finsupp.single κ (Am (Finsupp.single j 1) κ) = Am (Finsupp.single j 1) κ • Finsupp.single κ 1 by simp,
      map_smul, Submodule.coe_smul]
  have hA : ∀ t κ, ∑ j, algebraMap (𝓞 Ks) Ks (Aj j κ) * q j t = 0 := by
    intro t κ
    have h1 := congrArg (fun u => algebraMap (𝓞 Ks) Ks (u κ)) (LinearMap.congr_fun hAF (Finsupp.single t 1))
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, F, Finsupp.linearCombination_single, one_smul, map_sum,
      map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero,
      Pi.zero_apply, map_zero, map_mul, hr] at h1
    have h2 : algebraMap (𝓞 Ks) Ks d * ∑ j, algebraMap (𝓞 Ks) Ks (Aj j κ) * q j t = 0 := by
      rw [Finset.mul_sum, ← h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Aj]
      ring
    exact (mul_eq_zero.1 h2).resolve_left hd0
  have sKs : ∀ (c : 𝓞 Ks) (u : WL), c • u = algebraMap (𝓞 Ks) Ks c • u := fun c u => (algebraMap_smul Ks c u).symm
  have hwG : ∀ κ, w κ ∈ A.Wgood J0 lam0 eC := by
    intro κ
    have h0 : Wg.mkQ (w κ) = 0 := by
      refine v.repr.injective (Finsupp.ext fun t => ?_)
      simp only [w, map_sum, sKs, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
        map_zero, Finsupp.coe_zero, Pi.zero_apply]
      exact hA t κ
    exact (Submodule.Quotient.mk_eq_zero Wg).1 h0
  have hz : ∑ j, a j • m j = ∑ κ, yy κ • w κ := by
    simp only [w, Finset.smul_sum, sOL, sOK]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ha j, Finset.sum_smul]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [sOKL, smul_smul, mul_comm]
    rfl
  rw [hz]
  refine Submodule.sum_mem _ fun κ _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨?_, hwG κ⟩)
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (g j).2

omit [NumberField LL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] in

theorem fg_MK_good (hM : A.MKFull) (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL) :
    ∃ S : Finset WL, (Submodule.span (𝓞 Ks) (S : Set WL) : Set WL) = {y | y ∈ A.MK ∧ y ∈ A.Wgood J0 lam0 eC} := by
  obtain ⟨hfg, -⟩ := hM
  let N : Submodule (𝓞 Ks) WL :=
    A.MK ⊓ ((A.Wgood J0 lam0 eC).restrictScalars Ks).restrictScalars (𝓞 Ks)
  have hN : N.FG := by
    haveI := isNoetherian_of_fg_of_noetherian A.MK hfg
    have h1 : (N.comap A.MK.subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map A.MK.subtype
    rwa [Submodule.map_comap_subtype, inf_of_le_right inf_le_left] at h2
  obtain ⟨S, hS⟩ := hN
  exact ⟨S, by rw [hS]; rfl⟩

end Forms

section Record

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Record

end GlobalTheory.GoodLatDescent
