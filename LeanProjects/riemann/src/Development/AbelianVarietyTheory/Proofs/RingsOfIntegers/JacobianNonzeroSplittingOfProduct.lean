import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogChain
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.CoeffEqZeroOfMemSpanPow
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPowSpanXLeSpanFormalModuleMatrixStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpecStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsFiniteBasisPowerSeriesSubstFiniteColengthStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.InvariantsAndTraceFiniteFreeDomainEndomorphismsStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalSeriesDescendsOfSplitKernelInvariantStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DetJacobianFormalModuleMatrixEqConstMulUnitStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalMatrixKernelFiniteNcardEqRankStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalModuleMatrixApplyPointsActionLawsStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupTranslateAutomorphismAndMatrixKernelStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantDvdTraceOfJacobianFiniteColengthStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ImportsTer

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt.KerTrace

theorem exists_basis {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {r : ℕ} (b : Fin r → R)
    (h : ∀ f, ∃! cf : Fin r → A, f = ∑ i, algebraMap A R (cf i) * b i) :
    ∃ e : Module.Basis (Fin r) A R, ∀ i, e i = b i := by
  first
  | exact @_root_.GlobalTheory.SmoothEvaluation.main
  | exact _root_.GlobalTheory.SmoothEvaluation.main
  | (apply _root_.GlobalTheory.SmoothEvaluation.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmoothEvaluation.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmoothEvaluation.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmoothEvaluation.main ..)

theorem sum_tower {A₀ A₁ R : Type} [CommRing A₀] [IsDomain A₀] [CommRing A₁] [IsDomain A₁] [CommRing R] [IsDomain R]
    (φ : A₀ →+* A₁) (ψ : A₁ →+* R) {r r' r'' : ℕ} (b : Fin r → A₁) (b' : Fin r' → R) (b'' : Fin r'' → R)
    (h : ∀ f, ∃! cf : Fin r → A₀, f = ∑ i, φ (cf i) * b i)
    (h' : ∀ f, ∃! cf : Fin r' → A₁, f = ∑ i, ψ (cf i) * b' i)
    (h'' : ∀ f, ∃! cf : Fin r'' → A₀, f = ∑ i, ψ (φ (cf i)) * b'' i)
    {J : Type} (S : Finset J) (hS : S.card = r'') (g : J → R → R)
    (hg : ∀ α ∈ S, ∃ χ : R →+* R, ∀ f, g α f = χ f) (hfix : ∀ α ∈ S, ∀ a, g α (ψ (φ a)) = ψ (φ a))
    (hinj : ∀ α ∈ S, ∀ β ∈ S, (∀ f, g α f = g β f) → α = β)
    (x : A₁) (M : Matrix (Fin r) (Fin r) A₀) (hM : ∀ j, x * b j = ∑ i, φ (M i j) * b i) :
    ∑ α ∈ S, g α (ψ x) = ψ (φ ((r' : A₀) * M.trace)) := by
  classical
  letI := φ.toAlgebra
  letI := ψ.toAlgebra
  letI := (ψ.comp φ).toAlgebra
  haveI : IsScalarTower A₀ A₁ R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨e, he⟩ := exists_basis (A := A₀) b h
  obtain ⟨e', -⟩ := exists_basis (A := A₁) b' h'
  obtain ⟨e'', -⟩ := exists_basis (A := A₀) b'' h''
  haveI := Module.Free.of_basis e
  haveI := Module.Free.of_basis e'
  haveI := Module.Free.of_basis e''
  haveI := Module.Finite.of_basis e
  haveI := Module.Finite.of_basis e'
  haveI := Module.Finite.of_basis e''
  choose χ hχ using hg
  let G : S → (R →ₐ[A₀] R) := fun α =>
    { χ α.1 α.2 with commutes' := fun a => (hχ α.1 α.2 _).symm.trans (hfix α.1 α.2 a) }
  have hG : ∀ α f, G α f = g α.1 f := fun α f => (hχ α.1 α.2 f).symm
  have hGi : Function.Injective G := by
    intro α β hab
    exact Subtype.ext (hinj _ α.2 _ β.2 fun f => by rw [← hG, ← hG, hab])
  have hcard : (Finset.univ.map ⟨G, hGi⟩).card = Module.finrank A₀ R := by
    rw [Finset.card_map, Module.finrank_eq_card_basis e'']
    simp [hS]
  have key := (GlobalTheory.T.invariants_and_trace_finite_free_domain_endomorphisms A₀ R _ hcard).2 (ψ x)
  rw [Finset.sum_map] at key
  have h1 : ∑ α ∈ S, g α (ψ x) = ∑ α : S, G α (ψ x) := by
    simp only [hG]
    exact (Finset.sum_coe_sort S fun α => g α (ψ x)).symm
  have h2 : Algebra.trace A₀ A₁ x = M.trace := by
    rw [Algebra.trace_eq_matrix_trace e]
    congr 1
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, he, hM]
    have : ∑ i, φ (M i j) * b i = ∑ i, M i j • e i := Finset.sum_congr rfl fun i _ => by
      rw [he, Algebra.smul_def]; rfl
    rw [this, e.repr_sum_self]
  have h3 : Algebra.trace A₀ R (ψ x) = (r' : A₀) * M.trace := by
    rw [← Algebra.trace_trace (S := A₁), show ψ x = algebraMap A₁ R x from rfl, Algebra.trace_algebraMap,
      Module.finrank_eq_card_basis e', Fintype.card_fin, map_nsmul, h2, nsmul_eq_mul]
  rw [h1, ← h3]
  exact key.symm

theorem coeff_one_subst {k σ τ : Type} [CommRing k] [Fintype σ] {a : σ → MvPowerSeries τ k}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ k) (t : τ) :
    MvPowerSeries.coeff (Finsupp.single t 1) (MvPowerSeries.subst a f) =
      ∑ s, MvPowerSeries.coeff (Finsupp.single s 1) f * MvPowerSeries.coeff (Finsupp.single t 1) (a s) := by
  have h0 : ∀ {ρ : Type} (u : ρ) (g : MvPowerSeries ρ k), MvPowerSeries.constantCoeff (MvPowerSeries.pderiv k u g) =
      MvPowerSeries.coeff (Finsupp.single u 1) g := by
    intro ρ u g
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
    simp
  have h1 : ∀ g : MvPowerSeries σ k, MvPowerSeries.constantCoeff (MvPowerSeries.subst a g) =
      MvPowerSeries.constantCoeff g := by
    intro g
    rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha),
      finsum_eq_single _ 0]
    · simp
    · intro e he
      obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.2 he
      rw [Finsupp.prod, map_prod, Finset.prod_eq_zero hs, smul_zero]
      rw [map_pow, ha, zero_pow (Finsupp.mem_support_iff.1 hs)]
  rw [← h0, ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst ha, map_sum]
  simp only [map_mul, h1, h0]

theorem map_subst_eq_zero {k σ τ Ω : Type} [CommRing k] [CommRing Ω] [Algebra k Ω] [Fintype σ]
    {a : σ → MvPowerSeries τ k} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (χ : MvPowerSeries τ k →ₐ[k] Ω)
    (hχ : ∀ s, χ (a s) = 0) {g : MvPowerSeries σ k} (hg : MvPowerSeries.constantCoeff g = 0) :
    χ (MvPowerSeries.subst a g) = 0 := by
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have h1 := GlobalTheory.SocleDet.mem_span_X_of_coeff (Finset.univ : Finset σ) g fun m hm => by
    have : m = 0 := Finsupp.ext fun j => hm j (Finset.mem_univ j)
    rw [this]; exact hg
  have h2 : Ideal.span ((fun i => (MvPowerSeries.X i : MvPowerSeries σ k)) '' (Finset.univ : Finset σ)) ≤
      RingHom.ker (χ.comp (MvPowerSeries.substAlgHom hs)) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, -, rfl⟩
    simp [RingHom.mem_ker, MvPowerSeries.subst_X hs, hχ]
  have h3 := h2 h1
  rw [RingHom.mem_ker, AlgHom.comp_apply, MvPowerSeries.substAlgHom_apply] at h3
  exact h3

theorem left_inv_of_right {O : Type} [CommRing O] [IsDomain O] {n : ℕ} (p q s : Matrix (Fin n) (Fin n) O) (c : O)
    (hc : c ≠ 0) (h1 : s * (p * q) = c • (1 : Matrix (Fin n) (Fin n) O))
    (h2 : (p * q) * s = c • (1 : Matrix (Fin n) (Fin n) O)) : (q * s) * p = c • (1 : Matrix (Fin n) (Fin n) O) := by
  have hd : q.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one] at this
    exact pow_ne_zero _ hc (by simpa using this.symm)
  have h3 : (q * s * p - c • (1 : Matrix (Fin n) (Fin n) O)) * q = 0 := by
    rw [sub_mul, _root_.mul_assoc, _root_.mul_assoc, h1]; simp
  have h4 : q.det • (q * s * p - c • (1 : Matrix (Fin n) (Fin n) O)) = 0 := by
    have := congrArg (· * q.adjugate) h3
    simpa only [_root_.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, _root_.mul_one, zero_mul] using this
  exact sub_eq_zero.1 ((smul_eq_zero.1 h4).resolve_left hd)

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V]
  {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB V d O) {n : ℕ}

abbrev crd (p : Matrix (Fin n) (Fin n) O) : Fin n × Fin d → PS V n d :=
  fun s => matV B p (fun j => pt V (n := n) d j) s.1 s.2

omit [IsAdicComplete (maximalIdeal V) V] [CharZero V] in
theorem pt_small (b : Fin n) (i : Fin d) : MvPowerSeries.constantCoeff (pt V (n := n) d b i) ∈ maximalIdeal V := by
  simp [pt]

theorem crd_const (p : Matrix (Fin n) (Fin n) O) (s : Fin n × Fin d) : MvPowerSeries.constantCoeff (crd B p s) = 0 :=
  (GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n n p p _ _ pt_small pt_small).2.2.2.2.2.1 s.1 s.2

theorem pullM_eq (p : Matrix (Fin n) (Fin n) O) (f : PS V n d) : pullM B p f = MvPowerSeries.subst (crd B p) f :=
  (GlobalTheory.T.mvPowerSeriesSubstConstTerms_local_algHom_spec V _ _ Unit (crd B p) fun j => by rw [crd_const]; exact zero_mem _).2.2.1 (crd_const B p) f

theorem crd_mul (p q : Matrix (Fin n) (Fin n) O) (s : Fin n × Fin d) :
    crd B (p * q) s = MvPowerSeries.subst (crd B q) (crd B p s) := by
  have h1 := (GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n n p q _ _ pt_small pt_small).2.1
  have hq : ∀ b i, MvPowerSeries.constantCoeff (matV B q (fun j => pt V (n := n) d j) b i) ∈ maximalIdeal V :=
    fun b i => by rw [crd_const B q (b, i)]; exact zero_mem _
  have h2 := (GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n n p q _ _ hq hq).2.2.2.2.1 s.1 s.2
  rw [← pullM_eq]
  exact (congrFun (congrFun h1 s.1) s.2).trans h2.symm

theorem jacM_mul (p q : Matrix (Fin n) (Fin n) O) : jacM B (p * q) = jacM B p * jacM B q := by
  unfold jacM
  rw [← Matrix.det_mul]
  congr 1
  ext s t
  rw [Matrix.mul_apply]
  exact (congrArg _ (crd_mul B p q s)).trans (coeff_one_subst (crd_const B q) _ t)

theorem splitKer_right (p q : Matrix (Fin n) (Fin n) O) (h : SplitKer B (p * q)) : SplitKer B q := by
  intro Ω _ _ hi χ hχ
  refine h Ω hi χ fun b i => ?_
  exact (congrArg χ (crd_mul B p q (b, i))).trans
    (map_subst_eq_zero (crd_const B q) χ (fun s => hχ s.1 s.2) (crd_const B p _))

def pullHom (p : Matrix (Fin n) (Fin n) O) : PS V n d →ₐ[V] PS V n d :=
  MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero (crd_const B p))

theorem pullHom_apply (p : Matrix (Fin n) (Fin n) O) (f : PS V n d) :
    pullHom B p f = MvPowerSeries.subst (crd B p) f := MvPowerSeries.substAlgHom_apply _ _

theorem pullHom_mul (p q : Matrix (Fin n) (Fin n) O) (f : PS V n d) :
    pullHom B q (pullHom B p f) = pullM B (p * q) f := by
  rw [(GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n n p q _ _ pt_small pt_small).2.2.2.2.2.2 f, pullM_eq, pullM_eq, pullHom_apply,
    pullHom_apply]

end

theorem sum_shift_kerM_mul : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O), FinHt B → ∀ (n : ℕ) (p q s : Matrix (Fin n) (Fin n) O) (N : ℕ), 1 ≤ N → s * (p * q) = (N : O) • (1 : Matrix (Fin n) (Fin n) O) → (p * q) * s = (N : O) • (1 : Matrix (Fin n) (Fin n) O) → IsDomain O → (N : O) ≠ 0 → jacM B (p * q) ≠ 0 → SplitKer B (p * q) → ∀ f : PS V n d, (∀ α ∈ kerM B q, shift B.G.F α f = f) → (kerM B (p * q)).Finite ∧ ∃ g : PS V n d, ∑ᶠ α ∈ kerM B (p * q), shift B.G.F α f = MvPowerSeries.C (((kerM B q).ncard : V) * jacM B p) * pullM B (p * q) g := by
  intro V _ _ _ _ _ d O _ _ B hB n p q s N hN h1 h2 hO hN0 hj hsp f hf
  have hq : (s * p) * q = (N : O) • (1 : Matrix (Fin n) (Fin n) O) := by rw [_root_.mul_assoc, h1]
  have hp := left_inv_of_right p q s _ hN0 h1 h2
  have hjm := jacM_mul B p q
  have hjp : jacM B p ≠ 0 := fun h => hj (by rw [hjm, h, zero_mul])
  have hjq : jacM B q ≠ 0 := fun h => hj (by rw [hjm, h, mul_zero])
  have hsq := splitKer_right B p q hsp
  obtain ⟨f', rfl⟩ := GlobalTheory.T.formalSeries_descends_of_splitKernel_invariant V d O B hB n q _ N hN hq hjq hsq f hf
  obtain ⟨hfin, hcard⟩ := GlobalTheory.T.formalMatrixKernel_finite_ncard_eq_rank V d O B hB n (p * q) s N hN h1 hj hsp
  obtain ⟨-, hcardq⟩ := GlobalTheory.T.formalMatrixKernel_finite_ncard_eq_rank V d O B hB n q _ N hN hq hjq hsq
  have cp := GlobalTheory.T.exists_pow_span_X_le_span_formalModuleMatrix V d O B hB n p _ N hN hp
  obtain ⟨r, b, -, hb⟩ := GlobalTheory.T.exists_finite_basis_powerSeries_subst_finite_colength V _ (crd B p) (crd_const B p) cp
  obtain ⟨r', b', hr', hb'⟩ := GlobalTheory.T.exists_finite_basis_powerSeries_subst_finite_colength V _ (crd B q) (crd_const B q) (GlobalTheory.T.exists_pow_span_X_le_span_formalModuleMatrix V d O B hB n q _ N hN hq)
  obtain ⟨r'', b'', hr'', hb''⟩ := GlobalTheory.T.exists_finite_basis_powerSeries_subst_finite_colength V _ (crd B (p * q)) (crd_const B _)
    (GlobalTheory.T.exists_pow_span_X_le_span_formalModuleMatrix V d O B hB n _ s N hN h1)
  refine ⟨hfin, ?_⟩
  choose M hM using fun j => (hb (f' * b j)).exists
  obtain ⟨U, hU⟩ := GlobalTheory.T.det_jacobian_formal_module_matrix_eq_const_mul_unit V d O B n p
  obtain ⟨g, hg⟩ := GlobalTheory.T.constant_dvd_trace_of_jacobian_finite_colength V _ (crd B p) (crd_const B p) cp _ U hjp hU r b hb f' (Matrix.of fun i j => M j i) hM
  refine ⟨g, ?_⟩
  haveI : IsDomain (PS V n d) := NoZeroDivisors.to_isDomain _
  have hsm : ∀ α ∈ hfin.toFinset, ∀ b, Small (α b) := fun α hα => (hfin.mem_toFinset.1 hα).1
  have hsh := (GlobalTheory.T.formalGroupTranslate_automorphism_and_matrixKernel V d O B n (p * q)).2.2
  have key := sum_tower (pullHom B p : PS V n d →+* PS V n d) (pullHom B q : PS V n d →+* PS V n d) b b' b''
    (by simpa only [RingHom.coe_coe, pullHom_apply] using hb)
    (by simpa only [RingHom.coe_coe, pullHom_apply] using hb')
    (by simpa only [RingHom.coe_coe, pullHom_mul, pullM_eq] using hb'')
    hfin.toFinset (by rw [← Set.ncard_eq_toFinset_card _ hfin, hcard]; exact hr'') (shift B.G.F)
    (fun α hα => by
      obtain ⟨ψ, hψ⟩ := (hsh α α (hsm α hα) (hsm α hα)).1
      exact ⟨(ψ : PS V n d →+* PS V n d), hψ⟩)
    (fun α hα a => by
      simp only [RingHom.coe_coe, pullHom_mul]
      exact (hsh α α (hsm α hα) (hsm α hα)).2.1.1 (hfin.mem_toFinset.1 hα) a)
    (fun α hα β hβ => (hsh α β (hsm α hα) (hsm β hβ)).2.2.1)
    f' (Matrix.of fun i j => M j i) (by simpa only [RingHom.coe_coe, pullHom_apply, Matrix.of_apply] using hM)
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, pullM_eq B q, ← pullHom_apply]
  refine key.trans ?_
  have hC : ∀ (m : Matrix (Fin n) (Fin n) O) (c : V), pullHom B m (MvPowerSeries.C c) = MvPowerSeries.C c :=
    fun m c => (pullHom B m).commutes c
  rw [hg, hcardq.trans hr', ← pullHom_mul]
  simp only [RingHom.coe_coe, map_mul, map_natCast, hC, _root_.mul_assoc]

end GlobalTheory.PlaceInt.KerTrace
