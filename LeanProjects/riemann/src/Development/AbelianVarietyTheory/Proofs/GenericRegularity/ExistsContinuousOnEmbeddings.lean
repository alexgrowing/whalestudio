import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
import Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsLinearIndependentDIffTrdegAdjoinEq
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AeEvalCircleMapNeZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AemeasurableFinsumSection
import Development.AbelianVarietyTheory.Proofs.AlgebraicCurves.AlgebraicIndependentFreeVar
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IntegralAndRationalOfPolynomialGrowth
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ContDiffEvalFun

namespace GlobalTheory

namespace SectionLocal

open Filter Topology

theorem exists_continuousOn_root {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ))
    (x₀ : Fin d → ℂ) (a : ℂ) (ha : (p.map (MvPolynomial.eval x₀)).eval a = 0)
    (ha' : (p.map (MvPolynomial.eval x₀)).derivative.eval a ≠ 0) :
    ∃ y : (Fin d → ℂ) → ℂ, y x₀ = a ∧ (∃ s ∈ 𝓝 x₀, ContinuousOn y s) ∧
      ∀ᶠ x in 𝓝 x₀, (p.map (MvPolynomial.eval x)).eval (y x) = 0 :=
  _root_.GlobalTheory.SmoothPolynomialEvaluation.main p x₀ a ha ha'

theorem exists_continuousOn_roots {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (hp : p.Monic)
    (x₀ : Fin d → ℂ) (hs : (p.map (MvPolynomial.eval x₀)).Separable) :
    ∃ (y : Fin p.natDegree → (Fin d → ℂ) → ℂ) (V : Set (Fin d → ℂ)), V ∈ 𝓝 x₀ ∧
      (∀ i, ContinuousOn (y i) V) ∧
      ∀ x ∈ V, Function.Injective (fun i => y i x) ∧
        ∀ z, (p.map (MvPolynomial.eval x)).eval z = 0 ↔ ∃ i, y i x = z := by
  classical
  have hc := FiniteCoverGrowth.card_roots (hp.map (MvPolynomial.eval x₀)) hs
  rw [hp.natDegree_map] at hc
  let e := (Finset.equivFinOfCardEq hc).symm
  have hroot : ∀ i, (p.map (MvPolynomial.eval x₀)).eval (e i : ℂ) = 0 := fun i =>
    Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.1 (e i).2)
  choose y hy0 hyd hyr using fun i => exists_continuousOn_root p x₀ (e i) (hroot i)
    (by simpa using hs.eval₂_derivative_ne_zero (RingHom.id ℂ) (x := (e i : ℂ)) (by simpa using hroot i))
  choose s hs hyd using hyd
  have hne : ∀ᶠ x in 𝓝 x₀, ∀ i j, i ≠ j → y i x ≠ y j x := by
    simp only [eventually_all]
    intro i j hij
    refine (((hyd i).continuousAt (hs i)).ne_iff_eventually_ne ((hyd j).continuousAt (hs j))).1 ?_
    rw [hy0, hy0]
    exact fun h => hij (e.injective (Subtype.ext h))
  have hall := (hne.and (eventually_all.2 hyr)).and (eventually_all.2 hs)
  refine ⟨y, _, hall, fun i => (hyd i).mono fun x hx => hx.2 i, ?_⟩
  rintro x ⟨⟨h1, h2⟩, -⟩
  have hinj : Function.Injective (fun i => y i x) := fun i j h => by
    by_contra hij; exact h1 i j hij h
  have hset : (p.map (MvPolynomial.eval x)).roots.toFinset =
      Finset.univ.image (fun i => y i x) := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro a ha
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ha
      exact Multiset.mem_toFinset.2 ((Polynomial.mem_roots (hp.map _).ne_zero).2 (h2 i))
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      refine (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans ?_)
      rw [hp.natDegree_map]
  refine ⟨hinj, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · have : z ∈ (p.map (MvPolynomial.eval x)).roots.toFinset :=
      Multiset.mem_toFinset.2 ((Polynomial.mem_roots (hp.map _).ne_zero).2 hz)
    rw [hset] at this
    simpa using this
  · rintro ⟨i, rfl⟩
    exact h2 i

open Polynomial in

theorem exists_embeddings_of_roots {F L : Type} [Field F] [Field L] [Algebra F L]
    (pb : PowerBasis F L) (τ : F →+* ℂ) {n : ℕ} (r : Fin n → ℂ)
    (hr : ∀ z, ((minpoly F pb.gen).map τ).eval z = 0 ↔ ∃ i, r i = z) :
    ∃ P : Fin n → (L →+* ℂ), (∀ k, P k pb.gen = r k) ∧
      Set.range P = {P : L →+* ℂ | P.comp (algebraMap F L) = τ} := by
  letI : Algebra F ℂ := τ.toAlgebra
  have hτ : algebraMap F ℂ = τ := rfl
  have hroot : ∀ k, aeval (r k) (minpoly F pb.gen) = 0 := by
    intro k
    rw [aeval_def, eval₂_eq_eval_map, hτ]
    exact (hr _).2 ⟨k, rfl⟩
  refine ⟨fun k => (pb.lift (r k) (hroot k)).toRingHom, fun k => pb.lift_gen (r k) (hroot k), ?_⟩
  ext Q
  constructor
  · rintro ⟨k, rfl⟩
    ext x
    exact (pb.lift (r k) (hroot k)).commutes x
  · intro hQ
    have hQ' : Q.comp (algebraMap F L) = τ := hQ
    let Q' : L →ₐ[F] ℂ := { Q with commutes' := fun x => by rw [hτ, ← hQ']; rfl }
    have h0 : aeval (Q' pb.gen) (minpoly F pb.gen) = 0 := by
      rw [aeval_algHom_apply, minpoly.aeval, map_zero]
    rw [aeval_def, eval₂_eq_eval_map, hτ] at h0
    obtain ⟨k, hk⟩ := (hr _).1 h0
    refine ⟨k, ?_⟩
    have : pb.lift (r k) (hroot k) = Q' := by
      apply pb.algHom_ext
      rw [pb.lift_gen, hk]
    show (pb.lift (r k) (hroot k)).toRingHom = Q
    rw [this]

theorem exists_continuousOn_embeddings (K : Type) [Field K] [CharZero K] (σ : Type) (L : Type)
    [Field L] [Algebra (FractionRing (MvPolynomial σ K)) L]
    [FiniteDimensional (FractionRing (MvPolynomial σ K)) L] (sg : K →+* ℂ)
    (G : Set (σ → ℂ))
    (hG : ∀ t ∈ G, ∀ p : MvPolynomial σ K, p ≠ 0 → MvPolynomial.eval₂ sg t p ≠ 0)
    (t₀ : σ → ℂ) (ht₀ : t₀ ∈ G) :
    ∃ U ∈ 𝓝 t₀, ∃ (n : ℕ) (Q : Fin n → (σ → ℂ) → (L →+* ℂ)),
      (∀ k a, ContinuousOn (fun t => Q k t a) (U ∩ G)) ∧
      ∀ t ∈ U ∩ G, Function.Injective (fun k => Q k t) ∧
        Set.range (fun k => Q k t) = {P : L →+* ℂ | ∀ p : MvPolynomial σ K,
          P (algebraMap (FractionRing (MvPolynomial σ K)) L
            (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) p)) =
            MvPolynomial.eval₂ sg t p} := by
  classical
  set R := MvPolynomial σ K with hR
  set F := FractionRing R with hF
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective R F)
  let pb : PowerBasis F L := Field.powerBasisOfFiniteOfSeparable F L
  choose nu de hde hfr using fun z : F => IsFractionRing.div_surjective (A := R) z
  let ev : F → (σ → ℂ) → ℂ := fun f t =>
    MvPolynomial.eval₂ sg t (nu f) / MvPolynomial.eval₂ sg t (de f)
  have hpc : ∀ p : R, Continuous fun t : σ → ℂ => MvPolynomial.eval₂ sg t p := by
    intro p
    simp_rw [MvPolynomial.eval₂_eq_eval_map]
    exact MvPolynomial.continuous_eval _
  have hev : ∀ f, ∀ t ∈ G, ContinuousAt (ev f) t := fun f t ht =>
    (hpc _).continuousAt.div (hpc _).continuousAt (hG t ht _ (nonZeroDivisors.ne_zero (hde f)))
  let cf : (σ → ℂ) → Fin pb.dim → ℂ := fun t i => ev ((minpoly F pb.gen).coeff i) t
  have hcf : ∀ t ∈ G, ContinuousAt cf t := fun t ht => continuousAt_pi.2 fun i => hev _ t ht
  let p : Polynomial (MvPolynomial (Fin pb.dim) ℂ) :=
    Polynomial.X ^ pb.dim + ∑ i : Fin pb.dim, Polynomial.C (MvPolynomial.X i) * Polynomial.X ^ (i : ℕ)
  have hp : p.Monic := Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)
  have hτ : ∀ t ∈ G, ∃ τ : F →+* ℂ, (∀ q : R, τ (algebraMap R F q) = MvPolynomial.eval₂ sg t q) ∧
      (∀ f, τ f = ev f t) ∧ p.map (MvPolynomial.eval (cf t)) = (minpoly F pb.gen).map τ := by
    intro t ht
    have hinj : Function.Injective (MvPolynomial.eval₂Hom sg t : R →+* ℂ) := by
      rw [injective_iff_map_eq_zero]
      intro q hq
      by_contra h
      exact hG t ht q h hq
    have hτa : ∀ q : R, (IsFractionRing.lift hinj : F →+* ℂ) (algebraMap R F q) =
        MvPolynomial.eval₂ sg t q := fun q => IsFractionRing.lift_algebraMap hinj q
    have hτ : ∀ f, (IsFractionRing.lift hinj : F →+* ℂ) f = ev f t := by
      intro f
      conv_lhs => rw [← hfr f]
      rw [map_div₀, hτa, hτa]
    refine ⟨IsFractionRing.lift hinj, hτa, hτ, ?_⟩
    have hmon : (minpoly F pb.gen).Monic := minpoly.monic pb.isIntegral_gen
    conv_rhs => rw [hmon.as_sum, pb.natDegree_minpoly]
    rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
      Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
      Finset.sum_range]
    simp [cf, hτ]
  obtain ⟨y, V, hV, hyc, hy⟩ := exists_continuousOn_roots p hp (cf t₀) (by
    obtain ⟨τ, -, -, h⟩ := hτ t₀ ht₀
    rw [h]
    exact Polynomial.Separable.map (Algebra.IsSeparable.isSeparable F pb.gen))
  have key : ∀ t ∈ cf ⁻¹' V ∩ G, ∃ P : Fin p.natDegree → (L →+* ℂ),
      (∀ k, P k pb.gen = y k (cf t)) ∧ (∀ k f, P k (algebraMap F L f) = ev f t) ∧
      Set.range P = {P : L →+* ℂ | ∀ q : R, P (algebraMap F L (algebraMap R F q)) =
        MvPolynomial.eval₂ sg t q} := by
    intro t ht
    obtain ⟨τ, hτa, hτe, h⟩ := hτ t ht.2
    obtain ⟨P, hP, hPr⟩ := exists_embeddings_of_roots pb τ (fun k => y k (cf t))
      (by rw [← h]; exact (hy _ ht.1).2)
    refine ⟨P, hP, fun k f => ?_, ?_⟩
    · have hk : P k ∈ Set.range P := ⟨k, rfl⟩
      rw [hPr] at hk
      rw [← hτe]
      exact DFunLike.congr_fun hk f
    · rw [hPr]
      ext Q
      constructor
      · intro hQ q
        rw [← hτa]
        exact DFunLike.congr_fun hQ _
      · intro hQ
        apply IsFractionRing.ringHom_ext (A := R)
        intro q
        rw [hτa]
        exact hQ q
  have hU : cf ⁻¹' V ∈ 𝓝 t₀ := hcf t₀ ht₀ hV
  haveI : Nonempty (Fin p.natDegree → (L →+* ℂ)) :=
    ⟨(key t₀ ⟨mem_of_mem_nhds hU, ht₀⟩).choose⟩
  choose! P hP1 hP2 hP3 using key
  refine ⟨_, hU, p.natDegree, fun k t => P t k, fun k a => ?_, fun t ht => ⟨?_, hP3 t ht⟩⟩
  · have hc : ContinuousOn (fun t => ∑ l : Fin pb.dim,
        ev (pb.basis.repr a l) t * y k (cf t) ^ (l : ℕ)) (cf ⁻¹' V ∩ G) := by
      refine continuousOn_finsetSum _ fun l _ => ContinuousOn.mul
        (fun t ht => (hev _ t ht.2).continuousWithinAt) (ContinuousOn.pow ?_ _)
      exact (hyc k).comp (fun t ht => (hcf t ht.2).continuousWithinAt) fun t ht => ht.1
    refine hc.congr fun t ht => ?_
    show P t k a = _
    conv_lhs => rw [← pb.basis.sum_repr a]
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Algebra.smul_def, map_mul, pb.basis_eq_pow, map_pow, hP1 t ht, hP2 t ht]
  · intro k l hkl
    apply (hy _ ht.1).1
    show y k (cf t) = y l (cf t)
    rw [← hP1 t ht, ← hP1 t ht]
    exact DFunLike.congr_fun hkl _

open MeasureTheory ReciprocityTheory.ChartRestriction.G.T0 SectionSum in

theorem exists_local_families (K Ω : Type) [Field K] [CharZero K] [Countable K] [Field Ω]
    [Algebra K Ω] (D N : ℕ) (j₀ : Fin (N + 1)) (w : Fin (N + 1) → Ω) (hw : w j₀ = 1)
    (hfg : (⊤ : IntermediateField K Ω).FG) (htr : Algebra.trdeg K Ω = D)
    (hw' : Algebra.trdeg K (IntermediateField.adjoin K (Set.range w)) = D) (sg : K →+* ℂ) :
    ∃ S : Set (Fin D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1),
      MeasurableSet S ∧
      Measure.pi (fun _ => (volume : Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere) S = 0 ∧
      ∀ t0 ∈ Sᶜ, ∃ U ∈ 𝓝 t0, ∃ (n : ℕ)
        (Q : Fin n → (Fin D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) → (Ω →+* ℂ)),
        (∀ k (a : Ω), ContinuousOn (fun t => Q k t a) (U ∩ Sᶜ)) ∧
        ∀ t ∈ U ∩ Sᶜ, Function.Injective (fun k => Q k t) ∧
          Set.range (fun k => Q k t) = {P : Ω →+* ℂ | P ∈ PT sg ∧ ∀ i, ∑ j,
            (t i : EuclideanSpace ℂ (Fin (N + 1))) j * P (w j) = 0} := by
  let x : Fin N → Ω := fun k => w (j₀.succAbove k)
  have hadj : IntermediateField.adjoin K (Set.range w) = IntermediateField.adjoin K (Set.range x) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨j, rfl⟩
      obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove j₀ j
      · rw [hw]; exact one_mem _
      · exact IntermediateField.subset_adjoin K _ ⟨k, rfl⟩
    · apply IntermediateField.adjoin.mono
      rintro _ ⟨k, rfl⟩
      exact ⟨_, rfl⟩
  rw [hadj] at hw'
  have hJ := (exists_linearIndependent_D_iff_trdeg_adjoin_eq htr x).2 hw'
  obtain ⟨hinj, hfin⟩ := sImg_indep_finite K Ω D N j₀ x hfg htr hJ
  letI : Algebra (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N) := (liftS hinj).toAlgebra
  haveI := liftS_finite hinj hfin
  obtain ⟨s₀, hs₀⟩ := exists_ae_cons _ (Measure.toSphere_ne_zero _) D _
    (ae_eval₂_ne_zero_pi_toSphere K sg (D + 1) N)
  let F : (Fin D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) → TVar D N → ℂ :=
    fun t q =>
      ((Fin.cons s₀ t : Fin (D + 1) → Metric.sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) q.1 :
        EuclideanSpace ℂ (Fin (N + 1))) q.2
  have hF : Continuous F := by
    refine continuous_pi fun q => ?_
    obtain ⟨i, j⟩ := q
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [F, Fin.cons_zero]
      exact continuous_const
    · simp only [F, Fin.cons_succ]
      fun_prop
  let G : Set (TVar D N → ℂ) :=
    {τ | ∀ p : MvPolynomial (TVar D N) K, p ≠ 0 → MvPolynomial.eval₂ sg τ p ≠ 0}
  have hGm : MeasurableSet G := by
    haveI := NPB.countable_mvPoly (σ := TVar D N) (R := K)
    have : G = ⋂ p : MvPolynomial (TVar D N) K, ⋂ _ : p ≠ 0,
        {τ | MvPolynomial.eval τ (MvPolynomial.map sg p) ≠ 0} := by
      ext τ
      simp only [G, Set.mem_setOf_eq, Set.mem_iInter, MvPolynomial.eval_map]
    rw [this]
    exact MeasurableSet.iInter fun p => MeasurableSet.iInter fun _ =>
      (isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const).measurableSet
  refine ⟨(F ⁻¹' G)ᶜ, (hF.measurable hGm).compl, hs₀, ?_⟩
  rw [compl_compl]
  intro t0 ht0
  obtain ⟨U, hU, n, Q, hQc, hQ⟩ := exists_continuousOn_embeddings K (TVar D N) (OmS Ω D N) sg G
    (fun _ h => h) (F t0) ht0
  refine ⟨F ⁻¹' U, hF.continuousAt hU, n,
    fun k t => (Q k (F t)).comp (algebraMap Ω (OmS Ω D N)), fun k a => ?_, fun t ht => ?_⟩
  · exact (hQc k (algebraMap Ω (OmS Ω D N) a)).comp hF.continuousOn fun t ht => ht
  have hb := bijOn_restrict (K := K) j₀ x sg (F t) (fun Q hQ hrel => by
    letI : Algebra K ℂ := sg.toAlgebra
    let φ : Ω →ₐ[K] ℂ := { Q with commutes' := fun r => DFunLike.congr_fun hQ r }
    refine existsUnique_ringHom_OmS K Ω ℂ D N j₀ x (F t) φ htr ?_ hrel
    rw [algebraicIndependent_iff]
    intro p hp
    by_contra h0
    exact ht.2 p h0 hp)
  obtain ⟨hQi, hQr⟩ := hQ (F t) ht
  have hset : Set.range (fun k => Q k (F t)) = {P | ∀ p : MvPolynomial (TVar D N) K,
      P (sHom (K := K) j₀ x p) = MvPolynomial.eval₂ sg (F t) p} := by
    rw [hQr]
    ext P
    refine forall_congr' fun p => ?_
    rw [← liftS_algebraMap hinj p]
    rfl
  rw [← hset] at hb
  refine ⟨fun k l hkl => hQi (hb.injOn ⟨k, rfl⟩ ⟨l, rfl⟩ hkl), ?_⟩
  have := hb.image_eq
  rw [← Set.range_comp] at this
  refine Eq.trans this ?_
  ext P
  simp only [Set.mem_setOf_eq, F, Fin.cons_succ]
  refine and_congr_right fun _ => forall_congr' fun i => ?_
  rw [Fin.sum_univ_succAbove _ j₀, hw, map_one, mul_one]

end SectionLocal

end GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem stLoc_of_trdeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ [Fintype (Comp Xo c)] (h : GenFrEx Xo c) (Dd N : ℕ) (uL : WtR E) (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1)), FnFG Xo c → FnTrdeg Xo c Dd → (∀ Z, evC h Z (wR (jc Z)) ≠ 0) → (∀ Z, Algebra.trdeg c.F (IntermediateField.adjoin c.F (Set.range fun j => evC h Z (wR j) / evC h Z (wR (jc Z)))) = Dd) → STLoc h Dd N uL wR jc := by
  intro E _ _ _ H Dw l Xo c _ h Dd N uL wR jc hfg htr hw hw' _ _ _ Z sg
  haveI : Countable c.F := Countable.of_equiv _ (Module.finBasis ℚ c.F).equivFun.toEquiv.symm
  have hr : ∀ j, T0.ratio (Ω := Om Z) (valG h uL (wR j) Z) (valG h uL (wR (jc Z)) Z) =
      evC h Z (wR j) / evC h Z (wR (jc Z)) := by
    intro j
    apply T0.ValuationResidueLemmas.ratio_eq (valC_ne_zero (hw Z))
    simp only [valG, valC]
    rw [AddMonoidAlgebra.smul_single', div_mul_cancel₀ _ (hw Z)]
  simp only [hr]
  exact SectionLocal.exists_local_families c.F (Om Z) Dd N (jc Z)
    (fun j => evC h Z (wR j) / evC h Z (wR (jc Z))) (div_self (hw Z)) (hfg Z) (htr Z) (hw' Z) sg

end GlobalTheory.Reg
