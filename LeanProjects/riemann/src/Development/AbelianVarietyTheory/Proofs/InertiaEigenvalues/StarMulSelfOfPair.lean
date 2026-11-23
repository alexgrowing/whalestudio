import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolynomialModelCoefficientSpaceRealPoints
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
import Formalism.LocalToGlobal.Columns.CoefModAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjFormsRescale
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVanishesSingleCoefficientOfKernelKills
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.CoefUniq

open GlobalTheory.CoefModel

theorem schur_scalar : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (c : CoefA V) (lam : D.what₂.Tau → DomWeight V.rank)
    (c0 c0' : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.coef.W), IsInfFam θ → c.Is →
    Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam) → Bridge.CoefMapTie V c.coef c0' (rhoVr (labLL D) lam) →
    ∃ ζ : ℂ, ∀ F, c0' F = ζ • c0 F := by
  intro D V θ c lam c0 c0' hθ hc ht ht'
  obtain ⟨E, hE, hEρ⟩ := GlobalTheory.CoefReal.exists_real_model V θ c lam c0 hθ hc ht
  obtain ⟨E', hE', hEρ'⟩ := GlobalTheory.CoefReal.exists_real_model V θ c lam c0' hθ hc ht'
  let ψ : Module.End ℂ c.W := E'.toLinearMap ∘ₗ E.symm.toLinearMap
  have hψ : ∀ u ∈ GinfC V, ∀ w, ψ (c.ρ u w) = c.ρ u (ψ w) := fun u hu w => by
    obtain ⟨v, rfl⟩ := E.surjective w
    change E' (E.symm (c.ρ u (E v))) = c.ρ u (E' (E.symm (E v)))
    rw [hEρ u hu, E.symm_apply_apply, E.symm_apply_apply, hEρ' u hu]
  haveI := hc.2.2.2.1
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ψ
  have hU := GlobalTheory.GenRealSchur.irr_real c hc (Module.End.eigenspace ψ μ) fun u hu => by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : ψ w = μ • w := Module.End.mem_eigenspace_iff.1 hw
    exact Module.End.mem_eigenspace_iff.2 (by rw [hψ u hu, hw', map_smul])
  rcases hU with h0 | h0
  · exact absurd h0 hμ
  refine ⟨μ, fun F => ?_⟩
  have h1 : E (mapVV D.what₂.embLL lam F) ∈ Module.End.eigenspace ψ μ := h0 ▸ Submodule.mem_top
  rw [Module.End.mem_eigenspace_iff] at h1
  rw [← hE, ← hE']
  exact (congrArg E' (E.symm_apply_apply _)).symm.trans h1

theorem scalar_of_basis : ∀ {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    [Fintype ι] [Nonempty ι] (σ : K →+* ℂ) (b : Module.Basis ι K V) (c : V →ₛₗ[σ] W),
    LinearIndependent ℂ (fun i => c (b i)) → ∀ (φ : V →ₗ[K] V) (ζ : ℂ), (∀ v, c (φ v) = ζ • c v) →
    ∃ a : K, σ a = ζ ∧ ∀ v, φ v = a • v := by
  intro K V W ι _ _ _ _ _ _ _ σ b c hli φ ζ hφ
  classical
  have key : ∀ i k, σ (b.repr (φ (b i)) k) = if k = i then ζ else 0 := by
    intro i
    have e1 : c (φ (b i)) = ∑ k, σ (b.repr (φ (b i)) k) • c (b k) := by
      conv_lhs => rw [← b.sum_repr (φ (b i))]
      rw [map_sum]
      simp only [LinearMap.map_smulₛₗ]
    have e2 : ∑ k, (if k = i then ζ else 0) • c (b k) = ζ • c (b i) := by
      simp [ite_smul]
    have h1 : ∑ k, (σ (b.repr (φ (b i)) k) - if k = i then ζ else 0) • c (b k) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← e1, e2, hφ, sub_self]
    intro k
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h1 k)
  obtain ⟨i0⟩ := ‹Nonempty ι›
  set a := b.repr (φ (b i0)) i0 with ha
  have hd : ∀ i, b.repr (φ (b i)) i = a := fun i => σ.injective (by rw [key, key, if_pos rfl, if_pos rfl])
  have ho : ∀ i k, k ≠ i → b.repr (φ (b i)) k = 0 := fun i k hk => σ.injective (by rw [key, if_neg hk, map_zero])
  have hb : ∀ i, φ (b i) = a • b i := by
    intro i
    refine b.repr.injective (Finsupp.ext fun k => ?_)
    rw [map_smul, Finsupp.smul_apply, b.repr_self, Finsupp.single_apply, smul_eq_mul]
    by_cases hk : i = k
    · subst hk
      rw [if_pos rfl, mul_one, hd]
    · rw [if_neg hk, mul_zero, ho i k (Ne.symm hk)]
  have hφa : φ = a • LinearMap.id := b.ext fun i => by rw [hb i]; rfl
  refine ⟨a, (key i0 i0).trans (if_pos rfl), fun v => ?_⟩
  rw [hφa]
  rfl

theorem pow_eq_one_of_cmMax {K : Type} [Field K] [NumberField K] [StarRing K] {a : K} (hm : a ∈ Formalism.DivisionValues.cmMax K)
    (hs : star a * a = 1) (hi : IsIntegral ℤ a) : ∃ n : ℕ, n ≠ 0 ∧ a ^ n = 1 := by
  obtain ⟨n, hn, h⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ hi (fun φ => by
    have h1 := congrArg φ hs
    rw [map_mul, map_one, show φ (star a) = starRingEnd ℂ (φ a) from hm φ, Complex.conj_mul'] at h1
    have h2 : ‖φ a‖ ^ 2 = 1 := by exact_mod_cast h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2)
  exact ⟨n, hn.ne', h⟩

theorem mem_of_coords {K V ι : Type} [Field K] [AddCommGroup V] [Module K V] (K0 : Subfield K) (b : Module.Basis ι K V)
    {y : V} (a : K) (hy : y ≠ 0) (h1 : ∀ k, b.repr (a • y) k ∈ K0) (h2 : ∀ k, b.repr y k ∈ K0) : a ∈ K0 := by
  obtain ⟨k, hk⟩ : ∃ k, b.repr y k ≠ 0 := by
    by_contra hc
    exact hy (b.repr.injective (Finsupp.ext fun k => by simpa using not_not.1 (fun h => hc ⟨k, h⟩)))
  have e1 : a = b.repr (a • y) k * (b.repr y k)⁻¹ := by
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_inv_cancel_right₀ hk]
  rw [e1]
  exact K0.mul_mem (h1 k) (K0.inv_mem (h2 k))

theorem star_mul_self_of_pair {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (pair : V →ₗ⋆[K] V →ₗ[K] K) (a : K) {y : V} (hy : pair y y ≠ 0) (h : pair (a • y) (a • y) = pair y y) :
    star a * a = 1 := by
  have e1 : pair (a • y) (a • y) = star a * a * pair y y := by
    rw [map_smul, LinearMap.map_smulₛₗ₂, smul_eq_mul, smul_eq_mul, starRingEnd_apply]
    ring
  rw [e1] at h
  exact mul_right_cancel₀ hy (h.trans (one_mul _).symm)

theorem pair_ne_zero {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (σ : K →+* ℂ) (coef : V →ₛₗ[σ] W) (hinj : Function.Injective coef) (q : V → V → K)
    (hq : ∀ x x', inner ℂ (coef x) (coef x') = σ (q x x')) {x : V} (hx : x ≠ 0) : q x x ≠ 0 := fun h0 => by
  have h1 := hq x x
  rw [h0, map_zero] at h1
  exact hx (hinj ((inner_self_eq_zero.1 h1).trans (map_zero coef).symm))

theorem isIntegral_of_keeps {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) (hne : L ≠ ⊥) (hfg : L.FG) (a : K) (h : ∀ n ∈ L, a • n ∈ L) :
    IsIntegral ℤ a := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (isIntegral_of_smul_mem_submodule L hne hfg a h)
  rw [← hy]
  exact NumberField.RingOfIntegers.isIntegral_coe y

theorem exists_root_of_unity : ∀ (D : D7) (X : RealSide D) (c c₂ : ∀ j : Fin D.R.m, VV D.what₂.LL (FWT.lamV D j) →ₛₗ[D.what₂.embLL] (X.R.cV j).W), IsCoef X c → IsCoef X c₂ → ∀ j, ∃ (ζ : ℂ) (n : ℕ), n ≠ 0 ∧ ζ ^ n = 1 ∧ ∀ F, c₂ j F = ζ • c j F := by
  intro D X c c₂ hc hc₂ j
  obtain ⟨g, c0R, h⟩ := hc
  obtain ⟨g₂, c0R₂, h₂⟩ := hc₂
  obtain ⟨ζ, hζ⟩ := schur_scalar D (Vc D j) X.R.θ (X.R.cV j) (FWT.lamV D j) (c j) (c₂ j) X.char.models.inf
    (X.char.models.cV j) (h.mapL j) (h₂.mapL j)
  rcases subsingleton_or_nontrivial (VV D.what₂.LL (FWT.lamV D j)) with hs | hs
  · refine ⟨1, 1, one_ne_zero, one_pow _, fun F => ?_⟩
    rw [Subsingleton.elim F 0, map_zero, map_zero, smul_zero]
  obtain ⟨e, hrat, hco, hpa, hnab, -⟩ := h.coefL j X.A3.A.μ0
  obtain ⟨e₂, hrat₂, hco₂, hpa₂, hnab₂, -⟩ := h₂.coefL j X.A3.A.μ0

  have hφ : ∀ v, c j ((e₂.symm.trans e) v) = ζ • c j v := fun v =>
    (hco (e₂.symm v)).symm.trans ((hco₂ _).trans ((congrArg (c₂ j) (e₂.apply_symm_apply v)).trans (hζ v)))
  haveI : Nonempty _ := (bVV D.what₂.LL (FWT.lamV D j)).index_nonempty
  obtain ⟨a, hζa, ha⟩ := scalar_of_basis D.what₂.embLL (bVV D.what₂.LL (FWT.lamV D j)) (c j) (h.mapL j).2.1
    (e₂.symm.trans e).toLinearMap ζ hφ
  have hea : ∀ x, e x = a • e₂ x := fun x =>
    (congrArg e (e₂.symm_apply_apply x)).symm.trans (ha (e₂ x))
  haveI := e.toEquiv.nontrivial
  obtain ⟨i0⟩ := (X.A3.A.MtCSD j X.A3.A.μ0).bV.index_nonempty
  have hx0 := (X.A3.A.MtCSD j X.A3.A.μ0).bV.ne_zero i0
  have hy0 : e₂ ((X.A3.A.MtCSD j X.A3.A.μ0).bV i0) ≠ 0 := fun h0 => hx0 (e₂.injective (h0.trans (map_zero e₂).symm))
  have hm : a ∈ Formalism.DivisionValues.cmMax D.what₂.LL :=
    mem_of_coords _ (bVV D.what₂.LL (FWT.lamV D j)) a hy0 (fun k => hea _ ▸ hrat i0 k) (hrat₂ i0)
  have hs : star a * a = 1 := by
    have hinj := GlobalTheory.GalLift.rescale_inj _ D.what₂.embLL _ (X.R.B.L j X.A3.A.μ0).pres.coef_li
    have hp0 := pair_ne_zero D.what₂.embLL _ hinj _ (X.R.B.L j X.A3.A.μ0).pres.coef_pair hx0
    refine star_mul_self_of_pair _ a ((hpa₂ _ _).trans_ne hp0) ?_
    rw [← hea, hpa, hpa₂]
  have hi : IsIntegral ℤ a := by
    obtain ⟨cl, -⟩ := ((X.R.B.L j X.A3.A.μ0).pres.reps 1).exists
    have hL := nabAtr_isLattice (labLL D) (FWT.lamV D j) _
      (GlobalTheory.RepsCompare.isLattice_hLat (Vc D j) ((X.R.B.L j X.A3.A.μ0).pres.y cl))
    refine isIntegral_of_keeps _ (fun h0 => ?_) hL.fg a (fun n hn => ?_)
    · have h1 := hL.span_eq_top
      rw [h0, Submodule.bot_coe, Submodule.span_zero_singleton] at h1
      exact bot_ne_top h1
    · rw [← hnab₂ cl] at hn
      obtain ⟨m, hm, rfl⟩ := hn
      rw [← hnab cl]
      exact ⟨m, hm, hea m⟩
  obtain ⟨n, hn, han⟩ := pow_eq_one_of_cmMax hm hs hi
  exact ⟨ζ, n, hn, by rw [← hζa, ← map_pow, han, map_one], hζ⟩

end GlobalTheory.CoefUniq

end
