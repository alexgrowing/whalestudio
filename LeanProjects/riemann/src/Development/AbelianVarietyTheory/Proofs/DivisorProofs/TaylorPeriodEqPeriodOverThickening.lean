import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentOfComap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdEqZeroOfSuccLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallChartPairAlongLinearMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicPointExtOfIsSeparatedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAnalyticChartsRealizationOfAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassLinearRelationUniqueOfNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodOverRingRestrictFamilyClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodConstExtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CloseTaylorShiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsParameterTaylorExpansionHomApplyOfParamOnlyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsParameterTaylorExpansionHomFibreDerivationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSliceZeroIsTayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorRestrictionSubMemIdealMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTaylorAlgHomHolomorphicNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointsTranslationFamilyChartsThickeningsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GaussManinTaylor

theorem prod_zero_of_pow_eq_bot {R : Type} [CommRing R] (J : Ideal R) (n₀ : ℕ) (h : J ^ n₀ = ⊥) (N' : ℕ)
    (hN : n₀ ≤ N' + 1) (s : Fin (N' + 1) → R) (hs : ∀ a, s a ∈ J) : ∏ a, s a = 0 := by
  have h1 : ∏ a, s a ∈ ∏ _a ∈ (Finset.univ : Finset (Fin (N' + 1))), J := Ideal.prod_mem_prod (fun a _ ↦ hs a)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  have h2 := Ideal.pow_le_pow_right hN h1
  rw [h] at h2
  simpa using h2

end GlobalTheory.GaussManinTaylor

open GlobalTheory.GaussManinTaylor in
theorem GlobalTheory.GaussManinTaylor.taylor_period_eq_period_over_thickening : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} {B D : Type} [CommRing B] [CommRing D] [Algebra ℂ D] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp ℂ} {σ : B →+* Hol F.V} (e : Unif F s σ) (u₀ : Unif F₀ s₀ (algebraMap ℂ (Hol F₀.V))), X.IsSeparated → X₀.IsSeparated → 0 ∈ F.V → (∀ z, z ∈ F₀.V) → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (φ₀ : X₀ ⟶ X), (∀ p : Tot Empty g, u₀.E p ≫ φ₀ = e.E (0, p.2)) → ∀ (π : D →ₐ[ℂ] ℂ), IsNilpotent (RingHom.ker π) → ∀ {J : Ideal D} (dl : DividedPowers J), (∀ d ∈ J, π d = 0) → ∀ (N : ℕ) (t : I → D), (∀ i, π (t i) = 0) → (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (j : B →+* D), (∀ b, j b = GlobalTheory.PeriodFamily.taylor N t (σ b).fn) → ∀ (s' : X₀ ⟶ Sp D), s' = s₀ ≫ spMap (π : D →+* ℂ) → ∀ (n : IsMor (dp0 B) s dl s' j φ₀) (ψ : X₀ ⟶ X₀) (k : IsMor (dp0 ℂ) s₀ dl s' (algebraMap ℂ D) ψ), ψ = 𝟙 X₀ → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V), IsPeriod e c per → ∀ {io : Type} (S : Finset io) (d : io → D) (a : io → FirstDeRham s₀) (p : io → Λ → ℂ) (p' : io → (Λ →+ Hol F₀.V)), (∀ i l, p' i l = algebraMap ℂ _ (p i l)) → (∀ i, IsPeriod u₀ (a i) (p' i)) → n.pull1 c = ∑ i ∈ S, d i • k.pull1 (a i) → ∀ l, ∑ i ∈ S, d i * algebraMap ℂ D (p i l) = GlobalTheory.PeriodFamily.taylor N t (per l).fn := by
  intro I _ _ g Λ _ F F₀ B D _ _ _ X X₀ s s₀ σ e u₀ hX hX₀ h0V hV₀ hτ φ₀ hφ₀ π hπ J dl hJ N t ht hprod j hj s' hs' n ψ kk hψ c per hper ιo S d a p p' hp' hpa hsum l

  obtain ⟨R, _, _, io, π', m, hinj, hπ', hnil, hm0, hmm, hmsum⟩ :=
    GlobalTheory.SquareZeroSum.exists_sum_sq_zero N D π t hπ ht hprod
  set t' : I → R := fun i ↦ ∑ j, m j i with ht'def
  have ht' : (fun i ↦ io (t i)) = t' := funext hmsum
  have hprod' : ∀ s : Fin (N + 1) → I, ∏ a, t' (s a) = 0 := by
    intro s
    rw [← ht']
    simp only
    rw [← map_prod, hprod, map_zero]
  obtain ⟨n₀, hn₀⟩ := hnil
  set N' := N + n₀ with hN'
  have hker : ∀ s : Fin (N' + 1) → R, (∀ a, s a ∈ RingHom.ker (π' : R →+* ℂ)) → ∏ a, s a = 0 :=
    fun s hs ↦ prod_zero_of_pow_eq_bot _ n₀ hn₀ N' (by omega) s hs
  have ht'ker : ∀ i, t' i ∈ RingHom.ker (π' : R →+* ℂ) := fun i ↦ by
    have h1 : io (t i) = t' i := congrFun ht' i
    rw [RingHom.mem_ker, ← h1]
    change π' (io (t i)) = 0
    rw [hπ', ht]
  have hprodN' : ∀ s : Fin (N' + 1) → I, ∏ a, t' (s a) = 0 := fun s ↦ hker _ fun a ↦ ht'ker (s a)

  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_taylor_algHom_holomorphic_nilpotent N' t' hprodN' F.V h0V
  have hθio : ∀ f : Hol F.V, θ f = io (GlobalTheory.PeriodFamily.taylor N t f.fn) := by
    intro f
    rw [hθ, GlobalTheory.PeriodFamily.taylor_eq_of_le N t' hprod' N' (by omega),
      (GlobalTheory.PeriodFamily.taylor_formal_properties N t).2.2.2.2.1 R io f.fn, ht']

  have hdef : (default : Empty → ℂ) ∈ F₀.V := hV₀ _
  obtain ⟨K₀, K, ka, hRich, hU₀, hU, hmemk, hka⟩ := GlobalTheory.T.exists_small_chart_pair_along_linear_map u₀ e (fun _ ↦ (0 : I → ℂ))
    (fun _ _ ↦ analyticAt_const) (fun _ _ ↦ h0V) (LinearMap.id) (AddMonoidHom.id Λ)
    (fun l z _ ↦ (hτ l z).symm)
  have hmem0 : ∀ k, ∀ q ∈ K₀.W k, (((0 : I → ℂ), q.2) : Tot I g) ∈ K.W (ka k) := fun k q hq ↦ hmemk k q hq
  have hka' : ∀ {l k' k}, K₀.le l k' k → K.le l (ka k') (ka k) := fun h ↦ hka _ _ _ h
  obtain ⟨r₀, hr₀, -⟩ := GlobalTheory.T.exists_analyticChartsRealization_of_affine u₀ hX₀ K₀ hU₀
  obtain ⟨r, hr, -⟩ := GlobalTheory.T.exists_analyticChartsRealization_of_affine e hX K hU
  have han : AnalyticOnNhd ℂ (fun q : Tot Empty g ↦ (((0 : I → ℂ), q.2) : Tot I g)) ⊤ :=
    fun _ _ ↦ analyticAt_const.prod analyticAt_snd
  let res : ∀ k, Hol (K.W (ka k)) →+* Hol (K₀.W k) := fun k ↦
    (Hol.comap (fun q : Tot Empty g ↦ (((0 : I → ℂ), q.2) : Tot I g)) (fun q _ ↦ han q trivial) (hmem0 k)).toRingHom
  have hres : ∀ k (h : Hol (K.W (ka k))) {q : Tot Empty g}, q ∈ K₀.W k → (res k h).fn q = h.fn ((0 : I → ℂ), q.2) :=
    fun k h q hq ↦ Hol.fn_comap _ _ _ h hq

  choose ρ hρ using fun k ↦ GlobalTheory.T.exists_ringHom_isTay_of_slice_zero N' t' hprodN' (K.W (ka k)) (K₀.W k) (hmem0 k)
  let M : Ideal R := RingHom.ker (π' : R →+* ℂ)
  let et : Hol F₀.V →ₐ[ℂ] R := (Algebra.ofId ℂ R).comp (Hol.ev default hdef)
  have hcst : ∀ k f, ρ k (K.cst (ka k) f) = θ.toRingHom f ⊗ₜ[ℂ] 1 := fun k f ↦ by
    rw [GlobalTheory.T.isParameterTaylorExpansionHom_apply_of_param_only N' t' _ _ (hmem0 k) (ρ k) (hρ k) _ f.fn (fun q hq ↦ Charts.fn_cst _ _ _ hq)]
    exact congrArg (· ⊗ₜ[ℂ] (1 : Hol (K₀.W k))) (hθ f).symm
  have hdw : ∀ k a h, ρ k (dw a h) = LinearMap.lTensor R (dw a).toLinearMap (ρ k h) := fun k a h ↦
    GlobalTheory.T.isParameterTaylorExpansionHom_fibreDerivation N' t' _ _ (hmem0 k) (ρ k) (hρ k) a h
  have hclose : ∀ l k' k (h : K₀.le l k' k), Close (M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k'))) ((ρ k').comp (Charts.sh (hka' h))) ((Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h)).toRingHom.comp (ρ k)) := by
    intro l k' k h
    have hρk := hρ k
    have hρk' := hρ k'
    rw [ht'def] at hρk hρk'
    exact GlobalTheory.T.close_taylor_shift_alt K K₀ M N' hker N m (fun j i ↦ hm0 j i) hmm hτ l (ka k) (ka k') k k' (hka' h) h (hmem0 k') (ρ k) (ρ k') hρk hρk'
  have hred : ∀ k h, ρ k h - 1 ⊗ₜ[ℂ] res k h ∈ M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k)) :=
    fun k h ↦ GlobalTheory.T.taylor_restriction_sub_mem_ideal_map N' t' π' (fun i ↦ ht'ker i) _ _ (hmem0 k) (ρ k) (hρ k) h (res k h) (fun q hq ↦ hres k h hq)
  obtain ⟨ρ', hρ'1, hρ'2, hρ'3⟩ := GlobalTheory.T.exists_points_translationFamilyCharts_thickenings K K₀ et M θ.toRingHom ka hka' ρ hcst hdw hclose res hred
  have hetc : ∀ x : ℂ, et (algebraMap ℂ (Hol F₀.V) x) = algebraMap ℂ R x := fun x ↦ et.commutes x
  have H : IsOver (et : Hol F₀.V →+* R) M s₀ (algebraMap ℂ (Hol F₀.V)) J s' (π : D →+* ℂ) (io : D →+* R) :=
    { w := hs'
      mem := fun d hd ↦ by
        rw [RingHom.mem_ker]
        change π' (io d) = 0
        rw [hπ', hJ d hd]
      red := fun d ↦ by
        rw [RingHom.mem_ker, map_sub]
        change π' (io d) - π' (et (algebraMap ℂ (Hol F₀.V) (π d))) = 0
        rw [hetc, AlgHom.commutes, hπ']
        simp }
  have hpt : ∀ k, spMap (res k) ≫ r.x (ka k) = r₀.x k ≫ φ₀ := fun k ↦ by
    refine GlobalTheory.T.holomorphicPoint_ext_of_isSeparated (K₀.W k) hX _ _ (fun q hq ↦ ?_)
    have hq' := hmem0 k q hq
    have hev : (Hol.ev q hq).toRingHom.comp (res k) = (Hol.ev (((0 : I → ℂ), q.2) : Tot I g) hq').toRingHom :=
      RingHom.ext fun h ↦ by
        change Hol.ev q hq (res k h) = Hol.ev _ hq' h
        rw [Hol.ev_apply, Hol.ev_apply, hres k h hq]
    rw [← Category.assoc, ← GlobalTheory.Cris.spMap_comp, hev, hr (ka k) _ hq', ← Category.assoc, hr₀ k q hq, hφ₀ q]
  have hθj : ∀ b, θ.toRingHom (σ b) = io (j b) := fun b ↦ by
    rw [hj]
    exact hθio (σ b)
  have hfam := GlobalTheory.T.period_over_ring_restrict_family_class K K₀ (et : Hol F₀.V →+* R) M θ.toRingHom ka hka' res ρ' hρ'1 hρ'2 hρ'3 r r₀ dl H j φ₀ n hθj hpt c per (hper K r hr)
  have hfib : ∀ i, (r₀.coefD dl H).pull1 (kk.pull1 (a i)) = K₀.perClD (et : Hol F₀.V →+* R) M ((et : Hol F₀.V →+* R).toAddMonoidHom.comp (p' i)) :=
    fun i ↦ GlobalTheory.T.coefD_pull1_eq_perClD_of_pull1_eq_perCl K₀ (et : Hol F₀.V →+* R) M r₀ dl H (algebraMap ℂ D) ψ kk hψ
      (fun b ↦ by
        change et (algebraMap ℂ (Hol F₀.V) b) = io (algebraMap ℂ D b)
        rw [hetc, AlgHom.commutes]) (a i) (p' i) (hpa i K₀ r₀ hr₀)
  have hmain := congrArg (r₀.coefD dl H).pull1 hsum
  rw [hfam, map_sum] at hmain
  simp only [map_smulₛₗ, hfib] at hmain
  have het : ∀ (f : Hol F₀.V), ∀ z ∈ F₀.V, (et : Hol F₀.V →+* R) f = algebraMap ℂ R (f.fn z) := fun f z hz ↦ by
    have : z = default := Subsingleton.elim _ _
    subst this
    change algebraMap ℂ R (Hol.ev default hdef f) = _
    rw [Hol.ev_apply]
  have hdu := GlobalTheory.T.periodClass_linear_relation_unique_of_nilpotent K₀ (et : Hol F₀.V →+* R) M hRich hV₀ ⟨n₀, hn₀⟩ het S _ _ _ hmain l
  apply hinj
  rw [map_sum, ← hθio]
  refine Eq.trans ?_ hdu.symm
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  change io (d i * algebraMap ℂ D (p i l)) = io (d i) * et (p' i l)
  rw [map_mul, AlgHom.commutes, hp', hetc]
