import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousSetIntegralConstTermOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterEnvelopingCommutesLieStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightTranslationLieConjugateStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryExponentialPathExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionContinuousCompactSupportStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionDerivativeIsTestStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterCommutesOneParameterFlowStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvolutionRightInvariantOpenCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvolutionMaximalCompactEquivariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalConvolutionSplitCentreInvariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteIrreducibleFixedVectorsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvolutionSmoothLieDerivativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTestFunctionFixedSubspaceStatement
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep.Rep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

omit μ in
theorem continuous_tst {U : Subgroup (GL (Fin a) (Af E))} (hUo : IsOpen (U : Set (GL (Fin a) (Af E))))
    (hUc : IsCompact (U : Set (GL (Fin a) (Af E)))) {β : Lie E a → ℂ} (hβ : IsTest β) :
    Continuous (tst U β) ∧ HasCompactSupport (tst U β) := GlobalTheory.T.test_function_continuous_compact_support E a U hUo hUc β hβ

theorem cv_mem_Sm {U : Subgroup (GL (Fin a) (Af E))} (hUo : IsOpen (U : Set (GL (Fin a) (Af E))))
    (hUc : IsCompact (U : Set (GL (Fin a) (Af E)))) {β : Lie E a → ℂ} (hβ : IsTest β) {Fl : GA E a → ℂ}
    (hFl : LocallyIntegrable Fl μ) : convR μ (tst U β) Fl ∈ Sm E a :=
  (GlobalTheory.T.convolution_smooth_lie_derivative E a μ U hUo hUc β hβ Fl hFl).1

omit μ in
theorem isTest_dTest {β : Lie E a → ℂ} (hβ : IsTest β) (X : Lie E a) : IsTest (dTest X β) := GlobalTheory.T.test_function_derivative_is_test E a β hβ X

theorem lieD_cv {U : Subgroup (GL (Fin a) (Af E))} (hUo : IsOpen (U : Set (GL (Fin a) (Af E))))
    (hUc : IsCompact (U : Set (GL (Fin a) (Af E)))) {β : Lie E a → ℂ} (hβ : IsTest β) {Fl : GA E a → ℂ}
    (hFl : LocallyIntegrable Fl μ) (X : Lie E a) (g : GA E a) :
    lieD X (convR μ (tst U β) Fl) g = convR μ (tst U (dTest X β)) Fl g :=
  (GlobalTheory.T.convolution_smooth_lie_derivative E a μ U hUo hUc β hβ Fl hFl).2 X g

theorem cv_fin (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ) (Fl : GA E a → ℂ) {u : GL (Fin a) (Af E)} (hu : u ∈ U)
    (x : GA E a) : convR μ (tst U β) Fl (x * finGL E a u) = convR μ (tst U β) Fl x := GlobalTheory.T.convolution_right_invariant_open_compact E a μ U β Fl u hu x

theorem cv_cpt (U : Subgroup (GL (Fin a) (Af E))) {β : Lie E a → ℂ} (hβ : ConjInv β) (F : L2 (latticeGL E a) μ) (k : Kinf E a)
    (x : GA E a) :
    convR μ (tst U β) (lift (latticeGL E a) (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) F)) x =
      convR μ (tst U β) (lift (latticeGL E a) F) (x * infGL E a (Unitary.toUnits k)) := GlobalTheory.T.convolution_maximal_compact_equivariant E a μ U β hβ F k x

theorem cv_split (f : GA E a → ℂ) {F : L2 (latticeGL E a) μ} (hF : F ∈ L2cusp μ) (t : ℝ) (x : GA E a) :
    convR μ f (lift (latticeGL E a) F) (splitCentre E a t * x) = convR μ f (lift (latticeGL E a) F) x :=
  GlobalTheory.T.cuspidal_convolution_split_centre_invariant E a μ f F hF t x

theorem exists_injective (U : Subgroup (GL (Fin a) (Af E))) (hUo : IsOpen (U : Set (GL (Fin a) (Af E))))
    (hUc : IsCompact (U : Set (GL (Fin a) (Af E)))) (X : Submodule ℂ (L2 (latticeGL E a) μ)) [hX' : FiniteDimensional ℂ X]
    (hX : ∀ u ∈ U, ∀ v ∈ X, R (latticeGL E a) μ (finGL E a u) v = v) :
    ∃ β : Lie E a → ℂ, IsTest β ∧ ConjInv β ∧ ∀ v ∈ X, Rop (latticeGL E a) μ (tst U β) v = 0 → v = 0 :=
  GlobalTheory.T.exists_test_function_fixed_subspace E a μ U hUo hUc X hX' hX

theorem exists_typeSpace (H : Submodule ℂ (L2 (latticeGL E a) μ)) (hH : H ≤ L2cusp μ)
    (hI : IsIrredSubrep (R (latticeGL E a) μ) H) (F : L2 (latticeGL E a) μ) (hFH : F ∈ H) (hF : IsKFinL2 μ F) :
    ∃ U : Subgroup (GL (Fin a) (Af E)), IsOpen (U : Set (GL (Fin a) (Af E))) ∧ IsCompact (U : Set (GL (Fin a) (Af E))) ∧
      ∃ X : Submodule ℂ (L2 (latticeGL E a) μ), FiniteDimensional ℂ X ∧ F ∈ X ∧ X ≤ H ∧
        (∀ (k : Kinf E a), ∀ v ∈ X, R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) v ∈ X) ∧
        (∀ u ∈ U, ∀ v ∈ X, R (latticeGL E a) μ (finGL E a u) v = v) ∧
        ∀ B : L2 (latticeGL E a) μ →ₗ[ℂ] L2 (latticeGL E a) μ,
          (∀ (k : Kinf E a) v, B (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) v) =
            R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (B v)) →
          (∀ v ∈ H, (∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v) →
            B v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) (B v) = B v) →
          ∀ v ∈ X, B v ∈ X := GlobalTheory.T.k_finite_irreducible_fixed_vectors E a μ H hH hI F hFH hF

omit μ in

theorem Zalg_comm_cptRep {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (k : Kinf E a) :
    z * cptRep E a k = cptRep E a k * z := by
  obtain ⟨c, Y, h0, h1, hd, hi⟩ := GlobalTheory.T.unitary_exponential_path_exists E a k
  have h := GlobalTheory.T.center_commutes_one_parameter_flow E a (GlobalTheory.T.right_translation_lie_conjugate E a) z hz (GlobalTheory.T.center_enveloping_commutes_lie E a z hz) c Y h0 hd hi
  rw [h1] at h
  exact h

omit μ in

theorem Zalg_le (S : Subalgebra ℂ (Module.End ℂ (Sm E a))) (h : ∀ X, lie E a X ∈ S) : Zalg E a ≤ S := by
  have hE : ∀ τ i j, Eop (a := a) τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (h _) (S.smul_mem (h _) _)) _
  refine Algebra.adjoin_le ?_
  rintro _ ⟨τ, u, rfl⟩
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hE _ _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

theorem fd_span (X : Submodule ℂ (L2 (latticeGL E a) μ)) [FiniteDimensional ℂ X] (S : Set (Sm E a))
    (hS : ∀ ψ ∈ S, Continuous ψ.1 ∧ LeftInv (latticeGL E a) ψ.1 ∧ ∃ v ∈ X, lift (latticeGL E a) v =ᵐ[μ] ψ.1) :
    FiniteDimensional ℂ (Submodule.span ℂ S) := by
  let V : Submodule ℂ (Sm E a) :=
    { carrier := {ψ | Continuous ψ.1 ∧ LeftInv (latticeGL E a) ψ.1 ∧ ∃ v ∈ X, lift (latticeGL E a) v =ᵐ[μ] ψ.1}
      zero_mem' := ⟨continuous_zero, fun _ _ _ => rfl, 0, zero_mem _, ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 _)⟩
      add_mem' := fun {φ ψ} ⟨h1, h2, v, hv, e⟩ ⟨h1', h2', v', hv', e'⟩ =>
        ⟨h1.add h1', fun γ hγ g => congrArg₂ (· + ·) (h2 γ hγ g) (h2' γ hγ g), v + v', add_mem hv hv',
          Filter.EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_add v v')) (e.add e')⟩
      smul_mem' := fun c φ ⟨h1, h2, v, hv, e⟩ =>
        ⟨h1.const_smul c, fun γ hγ g => congrArg (c • ·) (h2 γ hγ g), c • v, Submodule.smul_mem _ c hv,
          Filter.EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_smul c v)) (e.const_smul c)⟩ }
  have hm : ∀ φ ∈ V, MemL2Quotient (latticeGL E a) μ φ.1 := fun φ ⟨_, h2, v, _, e⟩ => memL2_of_ae_eq h2 e
  have hinj := toL2ₗ_injective hm fun φ hφ => hφ.1
  have hr : ∀ φ : V, toL2ₗ μ V hm φ ∈ X := fun φ => by
    obtain ⟨_, _, v, hv, e⟩ := φ.2
    have : toL2ₗ μ V hm φ = v := l2DiscreteQuotient_ext_iff_lift_ae_eq.2 ((lift_toL2ₗ hm φ).trans e.symm)
    rwa [this]
  have : FiniteDimensional ℂ V :=
    FiniteDimensional.of_injective ((toL2ₗ μ V hm).codRestrict X hr) fun x y e => hinj (congrArg Subtype.val e)
  exact Submodule.finiteDimensional_of_le (S₂ := V) (Submodule.span_le.2 hS)

variable {μ}
variable {U : Subgroup (GL (Fin a) (Af E))}

theorem locallyIntegrable_mul_left {Fl : GA E a → ℂ} (hFl : LocallyIntegrable Fl μ) (x : GA E a) :
    LocallyIntegrable (fun y => Fl (x * y)) μ := by
  refine locallyIntegrable_iff.2 fun K hK => ?_
  have h1 := locallyIntegrable_iff.1 hFl _ (hK.image (continuous_mul_left x))
  have h2 := ((measurePreserving_mul_left μ x).integrableOn_comp_preimage
    (Homeomorph.mulLeft x).measurableEmbedding).2 h1
  refine h2.mono_set fun y hy => ⟨y, hy, rfl⟩

theorem integrable_tst_mul (hUo : IsOpen (U : Set (GL (Fin a) (Af E)))) (hUc : IsCompact (U : Set (GL (Fin a) (Af E))))
    {β : Lie E a → ℂ} (hβ : IsTest β) {Fl : GA E a → ℂ} (hFl : LocallyIntegrable Fl μ) (x : GA E a) :
    Integrable (fun y => tst U β y * Fl (x * y)) μ := by
  obtain ⟨h1, h2⟩ := continuous_tst hUo hUc hβ
  exact (locallyIntegrable_mul_left hFl x).integrable_smul_left_of_hasCompactSupport h1 h2

theorem tst_add (β β' : Lie E a → ℂ) (y : GA E a) : tst U (β + β') y = tst U β y + tst U β' y := by
  unfold tst ker
  split_ifs <;> simp

theorem tst_smul (c : ℂ) (β : Lie E a → ℂ) (y : GA E a) : tst U (c • β) y = c * tst U β y := by
  unfold tst ker
  split_ifs <;> simp

theorem IsTest.add {β β' : Lie E a → ℂ} (h : IsTest β) (h' : IsTest β') : IsTest (β + β') :=
  ⟨h.contDiff.add h'.contDiff, h.compact.add h'.compact, (closure_mono (Function.support_add β β')).trans (by
    rw [closure_union]; exact Set.union_subset h.support h'.support)⟩

theorem IsTest.smul {β : Lie E a → ℂ} (h : IsTest β) (c : ℂ) : IsTest (c • β) :=
  ⟨h.contDiff.const_smul c, h.compact.mono (Function.support_const_smul_subset c β),
    (closure_mono (Function.support_const_smul_subset c β)).trans h.support⟩

theorem Zalg_cv (hUo : IsOpen (U : Set (GL (Fin a) (Af E)))) (hUc : IsCompact (U : Set (GL (Fin a) (Af E))))
    {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] :
    ∀ (β : Lie E a → ℂ) (hβ : IsTest β), ∃ β', IsTest β' ∧ ∀ (Fl : GA E a → ℂ) (hFl : LocallyIntegrable Fl μ),
      (z ⟨_, cv_mem_Sm μ hUo hUc hβ hFl⟩).1 = convR μ (tst U β') Fl := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) :=
    { carrier := {z | ∀ (β : Lie E a → ℂ) (hβ : IsTest β), ∃ β', IsTest β' ∧
        ∀ (Fl : GA E a → ℂ) (hFl : LocallyIntegrable Fl μ),
          (z ⟨_, cv_mem_Sm μ hUo hUc hβ hFl⟩).1 = convR μ (tst U β') Fl}
      mul_mem' := fun {x y} hx hy β hβ => by
        obtain ⟨β₁, h1, e1⟩ := hy β hβ
        obtain ⟨β₂, h2, e2⟩ := hx β₁ h1
        refine ⟨β₂, h2, fun Fl hFl => ?_⟩
        have e : y ⟨_, cv_mem_Sm μ hUo hUc hβ hFl⟩ = ⟨_, cv_mem_Sm μ hUo hUc h1 hFl⟩ := Subtype.ext (e1 Fl hFl)
        change (x (y _)).1 = _
        rw [e]
        exact e2 Fl hFl
      add_mem' := fun {x y} hx hy β hβ => by
        obtain ⟨β₁, h1, e1⟩ := hx β hβ
        obtain ⟨β₂, h2, e2⟩ := hy β hβ
        refine ⟨β₁ + β₂, IsTest.add h1 h2, fun Fl hFl => ?_⟩
        change (x _).1 + (y _).1 = _
        rw [e1 Fl hFl, e2 Fl hFl]
        funext g
        simp only [convR, tst_add, add_mul, Pi.add_apply]
        exact (integral_add (integrable_tst_mul hUo hUc h1 hFl g) (integrable_tst_mul hUo hUc h2 hFl g)).symm
      algebraMap_mem' := fun c β hβ => by
        refine ⟨c • β, IsTest.smul hβ c, fun Fl hFl => ?_⟩
        funext g
        change c * _ = _
        simp only [convR, tst_smul, mul_assoc]
        exact (integral_const_mul _ _).symm }
  refine Zalg_le S (fun X β hβ => ⟨dTest X β, isTest_dTest hβ X, fun Fl hFl => ?_⟩) hz
  funext g
  exact lieD_cv μ hUo hUc hβ hFl X g

theorem lift_Rop_tst (hUo : IsOpen (U : Set (GL (Fin a) (Af E)))) (hUc : IsCompact (U : Set (GL (Fin a) (Af E))))
    {β : Lie E a → ℂ} (hβ : IsTest β) (G : L2 (latticeGL E a) μ) :
    lift (latticeGL E a) (Rop (latticeGL E a) μ (tst U β) G) =ᵐ[μ] convR μ (tst U β) (lift (latticeGL E a) G) := by
  obtain ⟨h1, h2⟩ := continuous_tst hUo hUc hβ
  exact (GlobalTheory.AutomorphicL2Pointwise.lift_Rop_eq_convR (GA E a) (latticeGL E a) μ _ (h1.integrable_of_hasCompactSupport h2) G).2

theorem R_Rop_fin (hUo : IsOpen (U : Set (GL (Fin a) (Af E)))) (hUc : IsCompact (U : Set (GL (Fin a) (Af E))))
    {β : Lie E a → ℂ} (hβ : IsTest β) (G : L2 (latticeGL E a) μ) {u : GL (Fin a) (Af E)} (hu : u ∈ U) :
    R (latticeGL E a) μ (finGL E a u) (Rop (latticeGL E a) μ (tst U β) G) = Rop (latticeGL E a) μ (tst U β) G := by
  refine l2DiscreteQuotient_ext_iff_lift_ae_eq.2 ?_
  have h := lift_Rop_tst hUo hUc hβ G
  filter_upwards [lift_R (finGL E a u) (Rop (latticeGL E a) μ (tst U β) G),
    (measurePreserving_mul_right μ (finGL E a u)).quasiMeasurePreserving.ae h, h] with x e1 e2 e3
  rw [e1, e2, cv_fin μ U β _ hu, e3]

theorem Rop_R_comm (hUo : IsOpen (U : Set (GL (Fin a) (Af E)))) (hUc : IsCompact (U : Set (GL (Fin a) (Af E))))
    {β : Lie E a → ℂ} (hβ : IsTest β) (g : GA E a)
    (hK : ∀ (G : L2 (latticeGL E a) μ) (x : GA E a),
      convR μ (tst U β) (lift (latticeGL E a) (R (latticeGL E a) μ g G)) x =
        convR μ (tst U β) (lift (latticeGL E a) G) (x * g)) (G : L2 (latticeGL E a) μ) :
    Rop (latticeGL E a) μ (tst U β) (R (latticeGL E a) μ g G) =
      R (latticeGL E a) μ g (Rop (latticeGL E a) μ (tst U β) G) := by
  refine l2DiscreteQuotient_ext_iff_lift_ae_eq.2 ?_
  have h := lift_Rop_tst hUo hUc hβ G
  filter_upwards [lift_R g (Rop (latticeGL E a) μ (tst U β) G),
    (measurePreserving_mul_right μ g).quasiMeasurePreserving.ae h,
    lift_Rop_tst hUo hUc hβ (R (latticeGL E a) μ g G)] with x e1 e2 e3
  rw [e1, e2, e3, hK]

variable (μ) in
theorem isOpen_level (hUo : IsOpen (U : Set (GL (Fin a) (Af E)))) (hUc : IsCompact (U : Set (GL (Fin a) (Af E))))
    {β : Lie E a → ℂ} (hβ : IsTest β) {Fl : GA E a → ℂ} (hFl : LocallyIntegrable Fl μ) :
    IsOpen {k | finRep E a k ⟨_, cv_mem_Sm μ hUo hUc hβ hFl⟩ = ⟨_, cv_mem_Sm μ hUo hUc hβ hFl⟩} :=
  isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (hUo.mem_nhds U.one_mem) fun u hu =>
    Subtype.ext (funext fun x => cv_fin μ U β Fl hu x))

theorem smooth_rep (H : Submodule ℂ (L2 (latticeGL E a) μ)) (hH : H ≤ L2cusp μ)
    (hI : IsIrredSubrep (R (latticeGL E a) μ) H) (F : L2 (latticeGL E a) μ) (hFH : F ∈ H) (hF : IsKFinL2 μ F) :
    ∃ φ : Sm E a, lift (latticeGL E a) F =ᵐ[μ] φ.1 ∧ MemL2Quotient (latticeGL E a) μ φ.1 ∧ (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) ∧
      (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧ IsOpen {k | finRep E a k φ = φ} ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) ∧
      FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)) := by
  obtain ⟨U, hUo, hUc, X, hXf, hFX, hXH, hXk, hXu, hXB⟩ := exists_typeSpace μ H hH hI F hFH hF
  obtain ⟨β, hβ, hβc, hinj⟩ := exists_injective μ U hUo hUc X hXu
  have hloc : ∀ G : L2 (latticeGL E a) μ, LocallyIntegrable (lift (latticeGL E a) G) μ := fun G =>
    GlobalTheory.CuspAE.locallyIntegrable_lift G
  have hint : ∀ β' : Lie E a → ℂ, IsTest β' → Integrable (tst U β') μ := fun β' h =>
    (continuous_tst hUo hUc h).1.integrable_of_hasCompactSupport (continuous_tst hUo hUc h).2
  have hstab : ∀ β' : Lie E a → ℂ, IsTest β' →
      (∀ (k : Kinf E a) (G : L2 (latticeGL E a) μ) (x : GA E a),
        convR μ (tst U β') (lift (latticeGL E a) (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) G)) x =
        convR μ (tst U β') (lift (latticeGL E a) G) (x * infGL E a (Unitary.toUnits k))) →
      ∀ v ∈ X, Rop (latticeGL E a) μ (tst U β') v ∈ X := fun β' h hK =>
    hXB (Rop (latticeGL E a) μ (tst U β')).toLinearMap (fun k v => Rop_R_comm hUo hUc h _ (hK k) v)
      fun v hv _ => ⟨hI.1.Rop_mem (hint β' h) hv, fun u hu => R_Rop_fin hUo hUc h v hu⟩
  have hKβ := fun k G x => cv_cpt μ U hβc G k x
  let A : X →ₗ[ℂ] X := LinearMap.restrict (Rop (latticeGL E a) μ (tst U β)).toLinearMap (hstab β hβ hKβ)
  have hAi : Function.Injective A := (injective_iff_map_eq_zero A).2 fun v hv =>
    Subtype.ext (hinj v.1 v.2 (congrArg Subtype.val hv))
  obtain ⟨G, hG⟩ := LinearMap.injective_iff_surjective.1 hAi ⟨F, hFX⟩
  have hGF : Rop (latticeGL E a) μ (tst U β) G.1 = F := congrArg Subtype.val hG
  have hGc : G.1 ∈ L2cusp μ := hH (hXH G.2)
  have hrep := lift_Rop_tst hUo hUc hβ G.1
  rw [hGF] at hrep
  have hcv : ∀ (β' : Lie E a → ℂ) (h : IsTest β') (v : L2 (latticeGL E a) μ), v ∈ X →
      (∀ (k : Kinf E a) (G : L2 (latticeGL E a) μ) (x : GA E a),
        convR μ (tst U β') (lift (latticeGL E a) (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) G)) x =
        convR μ (tst U β') (lift (latticeGL E a) G) (x * infGL E a (Unitary.toUnits k))) →
      Continuous (convR μ (tst U β') (lift (latticeGL E a) v)) ∧
        LeftInv (latticeGL E a) (convR μ (tst U β') (lift (latticeGL E a) v)) ∧
        ∃ w ∈ X, lift (latticeGL E a) w =ᵐ[μ] convR μ (tst U β') (lift (latticeGL E a) v) := fun β' h v hv hK =>
    ⟨ContAut.continuous_of_isOpen_stab E a ⟨_, cv_mem_Sm μ hUo hUc h (hloc v)⟩ (isOpen_level μ hUo hUc h (hloc v)),
      (leftInv_lift v).convR _, _, hstab β' h hK v hv, lift_Rop_tst hUo hUc h v⟩
  refine ⟨⟨_, cv_mem_Sm μ hUo hUc hβ (hloc G.1)⟩, hrep, memL2_of_ae_eq ((leftInv_lift G.1).convR _) hrep,
    fun γ g => (leftInv_lift G.1).convR _ _ (ratGL_mem_latticeGL γ) g, fun t g => cv_split μ _ hGc t g,
    isOpen_level μ hUo hUc hβ (hloc G.1), ?_, ?_⟩
  · refine fd_span μ X _ ?_
    rintro _ ⟨k, rfl⟩
    have e : cptRep E a k ⟨_, cv_mem_Sm μ hUo hUc hβ (hloc G.1)⟩ =
        ⟨_, cv_mem_Sm μ hUo hUc hβ (hloc (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) G.1))⟩ :=
      Subtype.ext (funext fun x => (hKβ k G.1 x).symm)
    beta_reduce
    rw [e]
    exact hcv β hβ _ (hXk k _ G.2) hKβ
  · refine fd_span μ X _ ?_
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨β', h', e'⟩ := Zalg_cv hUo hUc hz μ β hβ
    have hK' : ∀ (k : Kinf E a) (G : L2 (latticeGL E a) μ) (x : GA E a),
        convR μ (tst U β') (lift (latticeGL E a) (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) G)) x =
        convR μ (tst U β') (lift (latticeGL E a) G) (x * infGL E a (Unitary.toUnits k)) := fun k G x => by
      have e : cptRep E a k ⟨_, cv_mem_Sm μ hUo hUc hβ (hloc G)⟩ =
          ⟨_, cv_mem_Sm μ hUo hUc hβ (hloc (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) G))⟩ :=
        Subtype.ext (funext fun x => (hKβ k G x).symm)
      have h1 := LinearMap.congr_fun (Zalg_comm_cptRep hz k) ⟨_, cv_mem_Sm μ hUo hUc hβ (hloc G)⟩
      simp only [Module.End.mul_apply, e] at h1
      have h2 := congrFun (congrArg Subtype.val h1) x
      rw [e' _ (hloc _)] at h2
      refine h2.trans ?_
      have h3 := congrFun (e' _ (hloc G)) (x * infGL E a (Unitary.toUnits k))
      exact h3
    have e2 : z ⟨_, cv_mem_Sm μ hUo hUc hβ (hloc G.1)⟩ = ⟨_, cv_mem_Sm μ hUo hUc h' (hloc G.1)⟩ :=
      Subtype.ext (e' _ (hloc G.1))
    beta_reduce
    rw [e2]
    exact hcv β' h' _ G.2 hK'

end GlobalTheory.CompanionTheory.SmoothRep.Rep

theorem GlobalTheory.CompanionTheory.SmoothRep.smoothRep : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∀ F ∈ H, IsKFinL2 μ F → ∃ φ : Sm E a, lift (latticeGL E a) F =ᵐ[μ] φ.1 ∧ MemL2Quotient (latticeGL E a) μ φ.1 ∧ (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧ IsOpen {k | finRep E a k φ = φ} ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) ∧ FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)) :=
  fun _ _ _ _ _ _ _ _ H hH hI F hFH hF => GlobalTheory.CompanionTheory.SmoothRep.Rep.smooth_rep H hH hI F hFH hF
