import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmMemArchSmooth
import Development.AutomorphicSpectrum.Proofs.HermitianForms.CasOfCapelliVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaOpCommLiB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchLieDerivativeExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactSpanFiniteDimStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaOperatorEqCasimirSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirMemCenterEnveloping
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMonicAevalMemOfLeSup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AveragePreservesKFiniteness
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicGLHomeomorphInfiniteFinite

set_option maxSynthPendingDepth 1

open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction MeasureTheory PositivityTheory.Affgl
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.UnifAlpha

open AutomorphicForm GlobalTheory.CompanionTheory.ArchSmooth GlobalTheory.CompanionTheory.HCRep

theorem exists_monic_aeval_add_of_kill {M : Type*} [AddCommGroup M] [Module ℂ M]
    (A B : Module.End ℂ M) (hc : Commute A B) (q r : Polynomial ℂ) (hq : q.Monic) (hr : r.Monic) :
    ∃ P : Polynomial ℂ, P.Monic ∧ 0 < P.natDegree ∧ ∀ m, Polynomial.aeval A q m = 0 →
      Polynomial.aeval B r m = 0 → Polynomial.aeval (A + B) P m = 0 := by
  classical
  let N : Submodule ℂ M :=
    LinearMap.ker (Polynomial.aeval A q) ⊓ LinearMap.ker (Polynomial.aeval B r)
  have hcAB : ∀ m, A (B m) = B (A m) := fun m => LinearMap.congr_fun hc.eq m
  have hA : ∀ m ∈ N, A m ∈ N := by
    intro m hm
    refine ⟨?_, ?_⟩
    · have := AutomorphicForm.map_aeval_apply_of_intertwine A (A := A) (B := A) (fun _ => rfl) q m
      rw [LinearMap.mem_ker.1 hm.1, map_zero] at this
      exact LinearMap.mem_ker.2 this.symm
    · have := AutomorphicForm.map_aeval_apply_of_intertwine A (A := B) (B := B) hcAB r m
      rw [LinearMap.mem_ker.1 hm.2, map_zero] at this
      exact LinearMap.mem_ker.2 this.symm
  have hB : ∀ m ∈ N, B m ∈ N := by
    intro m hm
    refine ⟨?_, ?_⟩
    · have := AutomorphicForm.map_aeval_apply_of_intertwine B (A := A) (B := A)
        (fun m => (hcAB m).symm) q m
      rw [LinearMap.mem_ker.1 hm.1, map_zero] at this
      exact LinearMap.mem_ker.2 this.symm
    · have := AutomorphicForm.map_aeval_apply_of_intertwine B (A := B) (B := B) (fun _ => rfl) r m
      rw [LinearMap.mem_ker.1 hm.2, map_zero] at this
      exact LinearMap.mem_ker.2 this.symm
  let A' : Module.End ℂ N := A.restrict hA
  let B' : Module.End ℂ N := B.restrict hB
  have hq0 : Polynomial.aeval A' q = 0 := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have := AutomorphicForm.map_aeval_apply_of_intertwine N.subtype (A := A') (B := A)
      (fun _ => rfl) q x
    exact this.trans (LinearMap.mem_ker.1 x.2.1)
  have hr0 : Polynomial.aeval B' r = 0 := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have := AutomorphicForm.map_aeval_apply_of_intertwine N.subtype (A := B') (B := B)
      (fun _ => rfl) r x
    exact this.trans (LinearMap.mem_ker.1 x.2.2)
  have hc' : A' * B' = B' * A' := LinearMap.ext fun x => Subtype.ext (hcAB x.1)
  have hcomm : ∀ x ∈ ({A', B'} : Set (Module.End ℂ N)), ∀ y ∈ ({A', B'} : Set (Module.End ℂ N)),
      x * y = y * x := by
    rintro x (rfl | rfl) y (rfl | rfl)
    · rfl
    · exact hc'
    · exact hc'.symm
    · rfl
  letI : CommRing (Algebra.adjoin ℂ ({A', B'} : Set (Module.End ℂ N))) :=
    Algebra.adjoinCommRingOfComm ℂ hcomm
  let a' : Algebra.adjoin ℂ ({A', B'} : Set (Module.End ℂ N)) :=
    ⟨A', Algebra.subset_adjoin (Set.mem_insert _ _)⟩
  let b' : Algebra.adjoin ℂ ({A', B'} : Set (Module.End ℂ N)) :=
    ⟨B', Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)⟩
  have ha : IsIntegral ℂ a' := ⟨q, hq, by
    rw [← Polynomial.aeval_def]
    apply Subtype.ext
    have := Polynomial.aeval_algHom_apply (Algebra.adjoin ℂ ({A', B'} : Set (Module.End ℂ N))).val a' q
    exact this.symm.trans hq0⟩
  have hb : IsIntegral ℂ b' := ⟨r, hr, by
    rw [← Polynomial.aeval_def]
    apply Subtype.ext
    have := Polynomial.aeval_algHom_apply (Algebra.adjoin ℂ ({A', B'} : Set (Module.End ℂ N))).val b' r
    exact this.symm.trans hr0⟩
  obtain ⟨P, hPm, hP⟩ := ha.add hb
  have hP0 : Polynomial.aeval (A' + B') P = 0 := by
    rw [← Polynomial.aeval_def] at hP
    have := Polynomial.aeval_algHom_apply (Algebra.adjoin ℂ ({A', B'} : Set (Module.End ℂ N))).val (a' + b') P
    rw [hP, map_zero] at this
    exact this
  refine ⟨P * Polynomial.X, hPm.mul Polynomial.monic_X, ?_, fun m h1 h2 => ?_⟩
  · rw [hPm.natDegree_mul Polynomial.monic_X, Polynomial.natDegree_X]; omega
  · have hm : m ∈ N := ⟨LinearMap.mem_ker.2 h1, LinearMap.mem_ker.2 h2⟩
    have hAB : ∀ x : N, N.subtype ((A' + B') x) = (A + B) (N.subtype x) := fun _ => rfl
    have h3 := AutomorphicForm.map_aeval_apply_of_intertwine N.subtype hAB P ⟨(A + B) m, N.add_mem (hA m hm) (hB m hm)⟩
    rw [hP0] at h3
    rw [map_mul, Module.End.mul_apply, Polynomial.aeval_X]
    exact h3.symm

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def evK (g : GA E a) : Sm E a →ₗ[ℂ] (Kinf E a → ℂ) where
  toFun φ k := (cptRep E a k φ).1 g
  map_add' φ ψ := by funext k; simp
  map_smul' c φ := by funext k; simp

theorem evK_one (g : GA E a) (φ : Sm E a) : evK g φ 1 = φ.1 g := by
  change (cptRep E a 1 φ).1 g = φ.1 g
  rw [map_one]
  rfl

theorem exists_K_curve (Z : (isExpLieAlgebra E a).lieSubalgebra) (hZ : Z ∈ archSkew E a) :
    ∃ κ : ℝ → Kinf E a, ∀ (φ : Sm E a) (g : GA E a) (k : Kinf E a),
      HasDerivAt (fun t => evK g φ (k * κ t)) (evK g (liB Z φ) k) 0 := by
  let S : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.of (mMap E a (Z : ArchMatrix E a))
  have hS : S.conjTranspose = -S := by
    ext i j w
    have h := congrFun (congrFun (mem_archSkew.1 hZ) i) j
    have h2 := congrFun (congrArg Prod.snd h) ⟨w, IsTotallyComplex.isComplex w⟩
    exact h2
  obtain ⟨c, h0, hc, hu⟩ := exists_skew_curve S
  refine ⟨fun t => ⟨(c t).val, hu hS t⟩, fun φ g k => ?_⟩
  have hd := hasDerivAt_curve φ (g * infGL E a (Unitary.toUnits k)) c (toL S) h0 hc
  have e : ∀ t, evK g φ (k * ⟨(c t).val, hu hS t⟩) =
      φ.1 (g * infGL E a (Unitary.toUnits k) * infGL E a (c t)) := by
    intro t
    have e1 : Unitary.toUnits (⟨(c t).val, hu hS t⟩ : Kinf E a) = c t := Units.ext rfl
    change φ.1 (g * infGL E a (Unitary.toUnits (k * ⟨(c t).val, hu hS t⟩))) = _
    rw [map_mul, e1, map_mul, mul_assoc]
  simp_rw [e]
  exact hd

def typeSub {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W) :
    Submodule ℂ (Sm E a) where
  carrier := {φ | ∀ g : GA E a, evK g φ ∈ GlobalTheory.Published.AutFin.coeffSpan ρ}
  add_mem' hx hy g := by rw [map_add]; exact Submodule.add_mem _ (hx g) (hy g)
  zero_mem' g := by rw [map_zero]; exact Submodule.zero_mem _
  smul_mem' c _ hx g := by rw [map_smul]; exact Submodule.smul_mem _ c (hx g)

theorem liB_mem_typeSub {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (Kinf E a) W) (Z : (isExpLieAlgebra E a).lieSubalgebra)
    (hZ : Z ∈ archSkew E a) {φ : Sm E a} (hφ : φ ∈ typeSub ρ) : liB Z φ ∈ typeSub ρ := by
  intro g
  obtain ⟨κ, hκ⟩ := exists_K_curve Z hZ
  haveI := GlobalTheory.AvgCoeff.coeffSpan_finiteDimensional ρ
  exact AutomorphicForm.mem_of_hasDerivAt (GlobalTheory.Published.AutFin.coeffSpan ρ)
    (c := fun t k => evK g φ (k * κ t))
    (fun t => GlobalTheory.AvgCoeff.coeffSpan_mulRight ρ (κ t) (hφ g)) (fun k => hκ φ g k)

def evSpan {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W) :
    Submodule ℂ (Kinf E a → ℂ) :=
  Submodule.span ℂ {c | ∃ g : GA E a, ∃ φ ∈ typeSub ρ, c = evK g φ}

theorem evK_mem_evSpan {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W)
    (g : GA E a) {φ : Sm E a} (hφ : φ ∈ typeSub ρ) : evK g φ ∈ evSpan ρ :=
  Submodule.subset_span ⟨g, φ, hφ, rfl⟩

theorem exists_evSpan_deriv {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (Kinf E a) W) (Z : (isExpLieAlgebra E a).lieSubalgebra)
    (hZ : Z ∈ archSkew E a) :
    ∃ D : Module.End ℂ (evSpan ρ), ∀ (g : GA E a) (φ : Sm E a) (hφ : φ ∈ typeSub ρ),
      ((D ⟨evK g φ, evK_mem_evSpan ρ g hφ⟩ : evSpan ρ) : Kinf E a → ℂ) = evK g (liB Z φ) := by
  classical
  obtain ⟨κ, hκ⟩ := exists_K_curve Z hZ
  have key : ∀ c ∈ evSpan ρ, ∃ c' ∈ evSpan ρ, ∀ k,
      HasDerivAt (fun t => c (k * κ t)) (c' k) 0 := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨g, φ, hφ, rfl⟩ := hc
      exact ⟨_, evK_mem_evSpan ρ g (liB_mem_typeSub ρ Z hZ hφ), fun k => hκ φ g k⟩
    | zero => exact ⟨0, Submodule.zero_mem _, fun k => by simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)⟩
    | add x y _ _ hx hy =>
      obtain ⟨x', hx', hdx⟩ := hx
      obtain ⟨y', hy', hdy⟩ := hy
      exact ⟨x' + y', Submodule.add_mem _ hx' hy', fun k => (hdx k).add (hdy k)⟩
    | smul r x _ hx =>
      obtain ⟨x', hx', hdx⟩ := hx
      exact ⟨r • x', Submodule.smul_mem _ r hx', fun k => (hdx k).const_mul r⟩
  choose f hf hfd using key
  refine ⟨{ toFun := fun c => ⟨f c.1 c.2, hf c.1 c.2⟩
            map_add' := fun x y => Subtype.ext (funext fun k =>
              (hfd _ (x + y).2 k).unique ((hfd _ x.2 k).add (hfd _ y.2 k)))
            map_smul' := fun r x => Subtype.ext (funext fun k =>
              (hfd _ (r • x).2 k).unique ((hfd _ x.2 k).const_mul r)) }, fun g φ hφ => ?_⟩
  funext k
  exact (hfd _ (evK_mem_evSpan ρ g hφ) k).unique (hκ φ g k)

theorem exists_monic_compact_part {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (Kinf E a) W) {d : ℕ}
    (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (hskew : ∀ i, ε i = -1 → b i ∈ archSkew E a) :
    ∃ r : Polynomial ℂ, r.Monic ∧ ∀ φ ∈ typeSub ρ,
      Polynomial.aeval (lapOp (E := E) (a := a) (⇑b) - omegaOp (⇑b) ε) r φ = 0 := by
  classical
  set T := lapOp (E := E) (a := a) (⇑b) - omegaOp (⇑b) ε with hT
  have hTe : ∀ w : Sm E a, T w = ∑ i, ((1 : ℂ) - (ε i : ℂ)) • liB (b i) (liB (b i) w) := by
    intro w
    simp only [hT, lapOp, omegaOp, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      Module.End.mul_apply]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    module
  have hfd : FiniteDimensional ℂ (evSpan ρ) := by
    haveI := GlobalTheory.AvgCoeff.coeffSpan_finiteDimensional ρ
    refine Submodule.finiteDimensional_of_le (S₂ := GlobalTheory.Published.AutFin.coeffSpan ρ) ?_
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, φ, hφ, rfl⟩
    exact hφ g
  have hD : ∀ i, ∃ D : Module.End ℂ (evSpan ρ), ε i = -1 →
      ∀ (g : GA E a) (φ : Sm E a) (hφ : φ ∈ typeSub ρ),
        ((D ⟨evK g φ, evK_mem_evSpan ρ g hφ⟩ : evSpan ρ) : Kinf E a → ℂ) = evK g (liB (b i) φ) := by
    intro i
    by_cases h : ε i = -1
    · obtain ⟨D, hD⟩ := exists_evSpan_deriv ρ (b i) (hskew i h)
      exact ⟨D, fun _ => hD⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose D hDe using hD
  let T' : Module.End ℂ (evSpan ρ) := ∑ i, ((1 : ℂ) - (ε i : ℂ)) • (D i * D i)
  have hTS : ∀ w ∈ typeSub ρ, T w ∈ typeSub ρ := by
    intro w hw
    rw [hTe]
    refine Submodule.sum_mem _ fun i _ => ?_
    rcases hε i with h | h
    · simp [h]
    · exact Submodule.smul_mem _ _ (liB_mem_typeSub ρ _ (hskew i h)
        (liB_mem_typeSub ρ _ (hskew i h) hw))
  let TS : Module.End ℂ (typeSub ρ) := T.restrict hTS
  have hint : ∀ (g : GA E a) (m : typeSub ρ),
      (⟨evK g (TS m).1, evK_mem_evSpan ρ g (TS m).2⟩ : evSpan ρ) =
        T' ⟨evK g m.1, evK_mem_evSpan ρ g m.2⟩ := by
    intro g m
    apply Subtype.ext
    change evK g (T m.1) = _
    rw [hTe, map_sum]
    simp only [T', LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
      Submodule.coe_sum, Submodule.coe_smul_of_tower, map_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases hε i with h | h
    · simp [h]
    · congr 1
      have h1 : D i ⟨evK g m.1, evK_mem_evSpan ρ g m.2⟩ =
          ⟨evK g (liB (b i) m.1), evK_mem_evSpan ρ g (liB_mem_typeSub ρ _ (hskew i h) m.2)⟩ :=
        Subtype.ext (hDe i h g m.1 m.2)
      rw [h1]
      exact (hDe i h g _ (liB_mem_typeSub ρ _ (hskew i h) m.2)).symm
  refine ⟨LinearMap.charpoly T', LinearMap.charpoly_monic T', fun φ hφ => ?_⟩
  let m : typeSub ρ := ⟨φ, hφ⟩
  have e1 := AutomorphicForm.map_aeval_apply_of_intertwine (typeSub ρ).subtype (A := TS) (B := T)
    (fun _ => rfl) (LinearMap.charpoly T') m
  change _ = Polynomial.aeval T (LinearMap.charpoly T') φ at e1
  rw [← e1]
  apply Subtype.ext
  funext g
  let Ev : typeSub ρ →ₗ[ℂ] evSpan ρ :=
    { toFun := fun m => ⟨evK g m.1, evK_mem_evSpan ρ g m.2⟩
      map_add' := fun x y => Subtype.ext (map_add (evK g) x.1 y.1)
      map_smul' := fun c x => Subtype.ext (map_smul (evK g) c x.1) }
  have e2 := AutomorphicForm.map_aeval_apply_of_intertwine Ev (A := TS) (B := T') (hint g)
    (LinearMap.charpoly T') m
  rw [LinearMap.aeval_self_charpoly, LinearMap.zero_apply] at e2
  have e3 := congrFun (congrArg Subtype.val e2) 1
  have e4 : evK g ((typeSub ρ).subtype (Polynomial.aeval TS (LinearMap.charpoly T') m)) 1 = 0 := e3
  rw [evK_one] at e4
  exact e4

variable (E a) in

def archHomeo : archGroup E a ≃ₜ* GL (Fin a) (Cinf E) where
  toFun := toGL E a
  invFun y := archEquiv E a (Matrix.GeneralLinearGroup.map (infEq E).toRingHom y)
  left_inv u := by
    obtain ⟨x, rfl⟩ := (archEquiv E a).surjective u
    simp only [toGL, ContinuousMulEquiv.symm_apply_apply]
    congr 1
    ext i j
    simp
  right_inv y := by
    simp only [toGL, ContinuousMulEquiv.symm_apply_apply]
    ext i j
    simp
  map_mul' u v := by simp only [toGL, map_mul]
  continuous_toFun := by
    have c1 : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (infEq E).symm.toRingHom) :=
      Continuous.units_map _ (continuous_id.matrix_map (GlobalTheory.CuspRep.GASplit.continuous_infEq_symm E))
    exact c1.comp (archEquiv E a).symm.continuous
  continuous_invFun := by
    have c1 : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (infEq E).toRingHom) :=
      Continuous.units_map _ (continuous_id.matrix_map (continuous_infEq E))
    exact (archEquiv E a).continuous.comp c1

theorem unifAlpha : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), UnifAlpha E a := by
  intro E _ _ _ a W _ _ _ ρ _ J hJ _ _ μ hμ
  obtain ⟨d, b, ε, hε, horth, hskew⟩ := exists_archCartanBasis (K := E) (n := a)
  set Ω := omegaOp (E := E) (a := a) (⇑b) ε with hΩ
  have hZ : Ω ∈ Zalg E a := by
    rw [hΩ, GlobalTheory.CompanionTheory.HCRep.TraceCas.omegaOp_eq_two_cas E a d b ε hε horth]
    refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun w _ => Subalgebra.add_mem _ ?_ ?_) _
    · exact GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg E a _
    · exact GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg E a _
  obtain ⟨q, hq, hqJ⟩ := GlobalTheory.CompanionTheory.Affgl.exists_monic_aeval_apply_eq_zero E a J hJ Ω hZ
  obtain ⟨r, hr, hrT⟩ := exists_monic_compact_part ρ b ε hε hskew
  have hlap : Commute Ω (lapOp (⇑b)) := by
    simp only [lapOp, Commute, SemiconjBy]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : Ω * liB (b i) = liB (b i) * Ω := omegaOp_comm_liB b ε hε horth (b i)
    rw [← mul_assoc, h1, mul_assoc, h1, mul_assoc]
  have hc : Commute Ω (lapOp (⇑b) - Ω) := by
    refine LinearMap.ext fun x => ?_
    have h2 := LinearMap.congr_fun hlap.eq x
    simp only [Module.End.mul_apply] at h2 ⊢
    rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, h2]
  obtain ⟨P, hPm, hPd, hP⟩ := exists_monic_aeval_add_of_kill Ω (lapOp (⇑b) - Ω) hc q r hq hr
  have hsum : Ω + (lapOp (⇑b) - Ω) = lapOp (⇑b) := LinearMap.ext fun x => by simp
  rw [hsum] at hP
  letI : MeasurableSpace (archGroup E a) := borel _
  haveI : BorelSpace (archGroup E a) := ⟨rfl⟩
  haveI := hμ
  let e := archHomeo E a
  let em : GL (Fin a) (Cinf E) ≃ᵐ archGroup E a := e.symm.toHomeomorph.toMeasurableEquiv
  let ν : Measure (archGroup E a) := μ.map em
  haveI : ν.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ e.symm
  obtain ⟨κ, hκs, hκc, -, hκ⟩ := (isExpLieAlgebra E a).exists_kernel_eq_conv_of_aeval_laplacian ν b P
    hPm hPd Filter.univ_mem
  refine ⟨fun y => κ (e.symm y),
    (IsExpLieAlgebra.continuous_of_isSmoothFun hκs).comp e.symm.continuous,
    hκc.comp_homeomorph e.symm.toHomeomorph, fun L φ hφ g => ?_⟩
  obtain ⟨-, -, hK, hJφ⟩ := hφ
  have hl : Polynomial.aeval (lapOp (⇑b)) P φ = 0 := hP φ (hqJ φ hJφ) (hrT φ hK)
  have h1 := hκ (sliceL g (smL E a φ)) (by rw [← sliceL_aeval_lapOp, hl, map_zero, map_zero]) 1
  have h2 : φ.1 g = ∫ y, φ.1 (g * infEmb E a y) * κ y ∂ν := by
    simpa [archSlice_apply, smL] using h1
  rw [h2, integral_map_equiv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have e1 : infEmb E a (em y) = infGL E a y := by
    rw [infEmb_eq]
    exact congrArg (infGL E a) (e.apply_symm_apply y)
  simp only [e1]
  rfl

end GlobalTheory.CompanionTheory.UnifAlpha

end
