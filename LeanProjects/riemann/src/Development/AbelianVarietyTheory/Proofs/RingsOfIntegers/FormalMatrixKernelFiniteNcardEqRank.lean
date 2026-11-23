import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JacobianSmulKaehlerEqZero
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MapMaximalIdealEqKerMapResidue
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesExistsPolynomialTotalDegreeLeSubMemStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardAlgHomReducedTraceSum
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPowSpanXLeSpanFormalModuleMatrixStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpecStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DetJacobianFormalModuleMatrixEqConstMulUnitStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalModuleMatrixApplyPointsActionLawsStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open scoped TensorProduct

namespace GlobalTheory.KerCard

theorem isReduced_baseChange_of_smul_kaehler_eq_zero (T Q C : Type) [CommRing T] [CommRing Q]
    [Algebra T Q] [Module.Finite T Q] [Field C] [Algebra T C] (δ : T) (hδ : algebraMap T C δ ≠ 0)
    (h : ∀ ω : KaehlerDifferential T Q, δ • ω = 0) : IsReduced (C ⊗[T] Q) := by
  letI : Algebra Q (C ⊗[T] Q) := Algebra.TensorProduct.rightAlgebra
  have hsub : Subsingleton (C ⊗[T] KaehlerDifferential T Q) := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | add x y hx hy => rw [hx, hy, add_zero]
    | tmul c ω =>
      have hc : c = δ • ((algebraMap T C δ)⁻¹ * c) := by
        rw [Algebra.smul_def, ← _root_.mul_assoc, mul_inv_cancel₀ hδ, _root_.one_mul]
      rw [hc, TensorProduct.smul_tmul, h, TensorProduct.tmul_zero]
  have : Algebra.FormallyUnramified C (C ⊗[T] Q) :=
    ⟨(KaehlerDifferential.tensorKaehlerEquivBase T C Q (C ⊗[T] Q)).symm.subsingleton⟩
  exact Algebra.FormallyUnramified.isReduced_of_field C (C ⊗[T] Q)

theorem algHom_ext_of_mem_maximalIdeal {V σ A : Type} [CommRing V] [IsLocalRing V]
    [IsNoetherianRing V] [IsAdicComplete (maximalIdeal V) V] [Finite σ] [CommRing A] [Algebra V A]
    (a : σ → V) (ha : ∀ j, a j ∈ maximalIdeal V) (φ φ' : MvPowerSeries σ V →ₐ[V] A)
    (h : ∀ j, φ (MvPowerSeries.X j) = algebraMap V A (a j))
    (h' : ∀ j, φ' (MvPowerSeries.X j) = algebraMap V A (a j)) : φ = φ' := by
  have hCa : ∀ c : V, (MvPowerSeries.C c : MvPowerSeries σ V) = algebraMap V _ c := fun c => rfl
  have hP := GlobalTheory.T.mvPowerSeries_exists_polynomial_totalDegree_le_sub_mem V (maximalIdeal V) (IsNoetherian.noetherian _) inferInstance σ σ
    (fun j => (MvPowerSeries.X j - MvPowerSeries.C (a j) : MvPowerSeries σ V)) 1 (by
      rw [pow_one, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      have : (MvPowerSeries.X j : MvPowerSeries σ V) =
          (MvPowerSeries.X j - MvPowerSeries.C (a j)) + MvPowerSeries.C (a j) := by ring
      rw [this]
      exact Submodule.add_mem_sup (Ideal.subset_span ⟨j, rfl⟩)
        (Ideal.mem_map_of_mem _ (ha j)))
  have hk : ∀ ψ : MvPowerSeries σ V →ₐ[V] A,
      (∀ j, ψ (MvPowerSeries.X j) = algebraMap V A (a j)) → ∀ g ∈ Ideal.span (Set.range fun j =>
        (MvPowerSeries.X j - MvPowerSeries.C (a j) : MvPowerSeries σ V)), ψ g = 0 := by
    intro ψ hψ g hg
    have : Ideal.span (Set.range fun j =>
        (MvPowerSeries.X j - MvPowerSeries.C (a j) : MvPowerSeries σ V)) ≤ RingHom.ker ψ := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, hψ, hCa, AlgHom.commutes, sub_self]
    exact this hg
  have hpol : ∀ P : MvPolynomial σ V, φ (P : MvPowerSeries σ V) = φ' (P : MvPowerSeries σ V) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C c => rw [MvPolynomial.coe_C, hCa, AlgHom.commutes, AlgHom.commutes]
    | add p q hp hq => rw [MvPolynomial.coe_add, map_add, map_add, hp, hq]
    | mul_X p j hp => rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, map_mul, hp, h, h']
  ext g
  obtain ⟨P, -, hP⟩ := hP g
  have h1 := hk φ h _ hP
  have h2 := hk φ' h' _ hP
  rw [map_sub, sub_eq_zero] at h1 h2
  rw [h1, h2, hpol]

theorem mem_maximalIdeal_of_map_X {V σ A : Type} [CommRing V] [IsLocalRing V] [CommRing A]
    [Nontrivial A] [Algebra V A] (φ : MvPowerSeries σ V →ₐ[V] A) (j : σ) (a : V)
    (h : φ (MvPowerSeries.X j) = algebraMap V A a) : a ∈ maximalIdeal V := by
  have hCa : ∀ c : V, (MvPowerSeries.C c : MvPowerSeries σ V) = algebraMap V _ c := fun c => rfl
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h1 : IsUnit (MvPowerSeries.C a - MvPowerSeries.X j : MvPowerSeries σ V) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff]; simpa using hu
  have h2 := h1.map φ
  rw [map_sub, h, hCa, AlgHom.commutes, sub_self] at h2
  exact not_isUnit_zero h2

noncomputable def constAlgHom (V σ : Type) [CommRing V] : MvPowerSeries σ V →ₐ[V] V :=
  { (MvPowerSeries.constantCoeff : MvPowerSeries σ V →+* V) with
    commutes' := fun c => MvPowerSeries.constantCoeff_C c }

theorem eq_zero_of_constantCoeff {V σ : Type} [CommRing V] [IsEmpty σ] (g : MvPowerSeries σ V)
    (h : MvPowerSeries.constantCoeff g = 0) : g = 0 := by
  ext e
  have : e = 0 := Subsingleton.elim _ _
  subst this
  simpa using h

theorem finite_ncard_kerM : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O), FinHt B → ∀ (n : ℕ) (p p' : Matrix (Fin n) (Fin n) O) (N : ℕ), 1 ≤ N → p' * p = (N : O) • (1 : Matrix (Fin n) (Fin n) O) → jacM B p ≠ 0 → SplitKer B p → (kerM B p).Finite ∧ (kerM B p).ncard = Module.finrank V (PS V n d ⧸ Ideal.span (Set.range fun s : Fin n × Fin d => matV B p (fun j => pt V (n := n) d j) s.1 s.2)) := by
  intro V _ _ _ _ _ d O _ _ B hB n p p' N hN hp hjac hsplit
  classical
  have hcol := GlobalTheory.T.exists_pow_span_X_le_span_formalModuleMatrix V d O B hB n p p' N hN hp
  obtain ⟨U, hU⟩ := GlobalTheory.T.det_jacobian_formal_module_matrix_eq_const_mul_unit V d O B n p
  have hmat : ∀ x : Fin n → Pt V 0 d,
      (∀ b i, MvPowerSeries.constantCoeff (x b i) ∈ maximalIdeal V) →
      (∀ b i, evV x (matV B p (fun j => pt V (n := n) d j) b i) = matV B p x b i) ∧
      (∀ b i, MvPowerSeries.constantCoeff (matV B p (fun j => pt V (n := n) d j) b i) = 0) :=
    fun x hx => ⟨(GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n 0 p p x x hx hx).2.2.2.2.1,
      (GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n 0 p p x x hx hx).2.2.2.2.2.1⟩
  have h0 := (hmat 0 (fun b i => by simp)).2
  set f : Fin n × Fin d → PS V n d :=
    fun s => matV B p (fun j => pt V (n := n) d j) s.1 s.2 with hf
  let e := (Fintype.equivFin (Fin n × Fin d)).symm
  have hff := GlobalTheory.FiniteColength.free_finite_quotient V inferInstance (Fin n × Fin d) _ e
    (fun j => f (e j)) (fun j => h0 _ _) (by
      have : (Set.range fun j => MvPowerSeries.map (σ := Fin n × Fin d) (residue V) (f (e j))) =
          Set.range fun s => MvPowerSeries.map (σ := Fin n × Fin d) (residue V) (f s) :=
        e.surjective.range_comp fun s => MvPowerSeries.map (σ := Fin n × Fin d) (residue V) (f s)
      rw [this]; exact hcol)
  have hr : (Set.range fun j => f (e j)) = Set.range f := e.surjective.range_comp f
  rw [hr] at hff
  obtain ⟨hfree, hfin⟩ := hff
  let Ω := AlgebraicClosure (FractionRing V)
  have hinj : Function.Injective (algebraMap V Ω) := by
    rw [IsScalarTower.algebraMap_eq V (FractionRing V) Ω]
    exact (algebraMap (FractionRing V) Ω).injective.comp (IsFractionRing.injective V _)
  set I := Ideal.span (Set.range f) with hI
  have hred : IsReduced (Ω ⊗[V] (PS V n d ⧸ I)) := by
    refine isReduced_baseChange_of_smul_kaehler_eq_zero V _ Ω (jacM B p)
      (fun h => hjac (hinj (by rw [h, map_zero]))) fun ω => ?_
    have h1 := GlobalTheory.FiniteQuotOmega.jacobian_smul_kaehler_eq_zero V (Fin n × Fin d) f hfin
      (Ideal.Quotient.mk I (↑U⁻¹ : PS V n d) • ω)
    rw [hU, smul_smul, ← map_mul, _root_.mul_assoc, Units.mul_inv, _root_.mul_one] at h1
    rw [← h1]
    exact (algebraMap_smul (PS V n d ⧸ I) (jacM B p) ω).symm
  obtain ⟨hF, hcard, -⟩ := GlobalTheory.finite_card_trace_algHom_of_isReduced_baseChange V
    (PS V n d ⧸ I) Ω hred
  have hfI : ∀ b i, Ideal.Quotient.mk I (matV B p (fun j => pt V (n := n) d j) b i) = 0 :=
    fun b i => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨(b, i), rfl⟩)
  have hex : ∀ (χ : (PS V n d ⧸ I) →ₐ[V] Ω) (s : Fin n × Fin d), ∃ a : V,
      algebraMap V Ω a = χ.comp (Ideal.Quotient.mkₐ V I) (MvPowerSeries.X s) := fun χ s =>
    hsplit Ω hinj (χ.comp (Ideal.Quotient.mkₐ V I)) (fun b i => by
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hfI, map_zero]) s
  choose G hG using hex
  have hGm : ∀ χ s, G χ s ∈ maximalIdeal V := fun χ s =>
    mem_maximalIdeal_of_map_X _ s _ (hG χ s).symm
  have hpt : ∀ α : Fin n → Fin d → V, (∀ b i, α b i ∈ maximalIdeal V) →
      ∃ ψ : PS V n d →ₐ[V] Ω, (∀ s, ψ (MvPowerSeries.X s) = algebraMap V Ω (α s.1 s.2)) ∧
        ∀ b i, ψ (matV B p (fun j => pt V (n := n) d j) b i) = algebraMap V Ω
          (MvPowerSeries.constantCoeff (matV B (m := 0) p (fun j => cpt (α j)) b i)) := by
    intro α hα
    have hx : ∀ b i, MvPowerSeries.constantCoeff ((fun j => cpt (n := 0) (α j)) b i) ∈
        maximalIdeal V := fun b i => by simpa [cpt] using hα b i
    obtain ⟨ψ, hψ, hψ'⟩ := (GlobalTheory.T.mvPowerSeriesSubstConstTerms_local_algHom_spec V (Fin n × Fin d) (Fin 0 × Fin d) (Fin 0 × Fin d)
      (fun s => cpt (n := 0) (α s.1) s.2) (fun s => hx s.1 s.2)).1
    refine ⟨(Algebra.ofId V Ω).comp ((constAlgHom V _).comp ψ), fun s => ?_, fun b i => ?_⟩
    · rw [AlgHom.comp_apply, AlgHom.comp_apply, hψ]
      exact congrArg (algebraMap V Ω) (MvPowerSeries.constantCoeff_C _)
    · rw [AlgHom.comp_apply, AlgHom.comp_apply, ← hψ', ← (hmat _ hx).1 b i]
      rfl
  let G' : ((PS V n d ⧸ I) →ₐ[V] Ω) → (Fin n → Fin d → V) := fun χ b i => G χ (b, i)
  have hG'inj : Function.Injective G' := by
    intro χ χ' h
    have h1 := algHom_ext_of_mem_maximalIdeal (G χ) (hGm χ) _ (χ'.comp (Ideal.Quotient.mkₐ V I))
      (fun s => (hG χ s).symm) (fun s => by
        rw [← hG χ' s]; exact congrArg (algebraMap V Ω) (congrFun (congrFun h s.1) s.2).symm)
    exact Ideal.Quotient.algHom_ext V h1
  have hrange : kerM B p = Set.range G' := by
    ext α
    constructor
    · rintro ⟨hs, hz⟩
      obtain ⟨ψ, hψ, hψ'⟩ := hpt α hs
      have hker : ∀ g ∈ I, ψ g = 0 := by
        have : I ≤ RingHom.ker ψ := by
          rw [hI, Ideal.span_le]
          rintro _ ⟨s, rfl⟩
          rw [SetLike.mem_coe, RingHom.mem_ker]
          refine (hψ' s.1 s.2).trans ?_
          rw [hz]; simp
        exact fun g hg => this hg
      refine ⟨Ideal.Quotient.liftₐ I ψ hker, ?_⟩
      funext b i
      apply hinj
      refine (hG _ (b, i)).trans ?_
      exact hψ (b, i)
    · rintro ⟨χ, rfl⟩
      refine ⟨fun b i => hGm χ (b, i), ?_⟩
      obtain ⟨ψ, hψ, hψ'⟩ := hpt (G' χ) fun b i => hGm χ (b, i)
      have h1 := algHom_ext_of_mem_maximalIdeal (G χ) (hGm χ) _ ψ
        (fun s => (hG χ s).symm) hψ
      funext b i
      refine eq_zero_of_constantCoeff _ (hinj ?_)
      rw [← hψ', ← h1, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hfI, map_zero, map_zero]
  rw [hrange]
  refine ⟨Set.finite_range _, ?_⟩
  rw [← hcard, ← Nat.card_coe_set_eq, Nat.card_range_of_injective hG'inj]

end GlobalTheory.KerCard
