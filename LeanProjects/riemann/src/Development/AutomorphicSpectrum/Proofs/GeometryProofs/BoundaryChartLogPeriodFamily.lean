import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DifferentiableOnStarStar
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLogPeriodFamily
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramComplexConjugateStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExponentialConjugateStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodsConjugateExistsStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateRootZeroThird
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.Conj

open GroundTheory.Heights₂.Heights.Regular GlobalTheory.CompanionTheory.Ar.Flat.Link

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f)
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem dualMap_conj_over :
    spMap (dualMap (starRingEnd ℂ)) ≫ spMap (algebraMap ℂ (DualNumber ℂ)) =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (starRingEnd ℂ) := by
  have h : (dualMap (starRingEnd ℂ)).comp (algebraMap ℂ (DualNumber ℂ)) =
      (algebraMap ℂ (DualNumber ℂ)).comp (starRingEnd ℂ) := by
    ext c
    · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  rw [← spMap_comp', ← spMap_comp', h]

theorem dualMap_comp_ring {R : Type} [CommRing R] (f : R →+* ℂ) :
    spMap (dualMap ((starRingEnd ℂ).comp f)) = spMap (dualMap (starRingEnd ℂ)) ≫ spMap (dualMap f) := by
  have h : dualMap ((starRingEnd ℂ).comp f) = (dualMap (starRingEnd ℂ)).comp (dualMap f) := by
    ext c <;> simp [dualMap]
  rw [h, spMap_comp']

theorem spMap_dualMap_conj_conj :
    spMap (dualMap (starRingEnd ℂ)) ≫ spMap (dualMap (starRingEnd ℂ)) = 𝟙 _ := by
  have h : (dualMap (starRingEnd ℂ)).comp (dualMap (starRingEnd ℂ)) = RingHom.id (DualNumber ℂ) := by
    ext c <;> simp [dualMap]
  rw [← spMap_comp', h]
  exact Spec.map_id _

theorem spMap_conj_conj : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 (Sp ℂ) := by
  have h : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by
    ext c
    simp
  rw [← spMap_comp', h]
  exact Spec.map_id _

def conjTan {S : Scheme.{0}} {G : Over S} {x x' : Sp ℂ ⟶ S} (h : x' = spMap (starRingEnd ℂ) ≫ x)
    (v : epsAt x ⟶ G) : epsAt x' ⟶ G :=
  Over.homMk (spMap (dualMap (starRingEnd ℂ)) ≫ v.left) (by
    subst h
    have hv := Over.w v
    simp only [Over.mk_hom] at hv ⊢
    rw [Category.assoc, hv, ← Category.assoc]
    have := dualMap_conj_over
    simp only [spMap] at this
    rw [this, Category.assoc])

theorem conj_hermForm' {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) :
    hermForm (Hm.map (starRingEnd ℂ)) a b = (starRingEnd ℂ) (hermForm Hm (star a) (star b)) := by
  simp [hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem isRiem_of_chart {Xo : Moduli D l} {σ : KA l →+* ℂ} {n a : ℕ} (C : BdryChart Xo σ n a) (z : Fin n → ℂ)
    (Hm : Matrix (Fin C.g) (Fin C.g) ℂ) (h : (chart C).IsRiem (star z) Hm) :
    C.IsRiem z (Hm.map (starRingEnd ℂ)) := by
  intro m u v Γ hv
  have hψ : conjPts C.ψ (star z) = (starRingEnd ℂ).comp (C.ψ z) := by simp [conjPts]
  have hx : spMap (conjPts C.ψ (star z)) = spMap (starRingEnd ℂ) ≫ spMap (C.ψ z) := by
    rw [hψ, spMap_comp']
  have hx' : spMap (C.ψ z) = spMap (starRingEnd ℂ) ≫ spMap (conjPts C.ψ (star z)) := by
    rw [hx, ← Category.assoc, spMap_conj_conj, Category.id_comp]
  let v' : Fin m → (epsAt (spMap (conjPts C.ψ (star z))) ⟶ C.t.G) := fun i => conjTan hx (v i)
  have hv' : (chart C).IsVal (star z) u v' := by
    intro i
    show spMap (dualMap (starRingEnd ℂ)) ≫ (v i).left = spMap (dualMap (conjPts C.ψ (star z))) ≫ (C.M.pt (u i)).left
    rw [hv i, hψ, dualMap_comp_ring, Category.assoc]
  have hback : ∀ i, (v i).left = spMap (dualMap (starRingEnd ℂ)) ≫ (v' i).left := fun i => by
    show (v i).left = spMap (dualMap (starRingEnd ℂ)) ≫ spMap (dualMap (starRingEnd ℂ)) ≫ (v i).left
    rw [← Category.assoc, spMap_dualMap_conj_conj, Category.id_comp]
  have hform : ∀ i j, hermForm Hm (fun b => conjPts C.ψ (star z) (u i b)) (fun b => conjPts C.ψ (star z) (u j b)) =
      (starRingEnd ℂ) (hermForm (Hm.map (starRingEnd ℂ)) (fun b => C.ψ z (u i b)) (fun b => C.ψ z (u j b))) := by
    intro i j
    rw [conj_hermForm', Complex.conj_conj, hψ]
    rfl
  have hform' : ∀ i j, (Real.pi : ℂ) * hermForm Hm (fun b => conjPts C.ψ (star z) (u i b))
      (fun b => conjPts C.ψ (star z) (u j b)) = (starRingEnd ℂ) ((Real.pi : ℂ) *
        hermForm (Hm.map (starRingEnd ℂ)) (fun b => C.ψ z (u i b)) (fun b => C.ψ z (u j b))) := by
    intro i j
    rw [hform, map_mul, Complex.conj_ofReal]
  have key := h m u v' (Γ.map (starRingEnd ℂ)) hv'
  constructor
  · intro hG i j
    have h1 := key.1 (GlobalTheory.T.hodge_gram_complex_conjugate _ _ _ _ _ _ _ _ _ hx (fun _ => rfl) hG) i j
    have h2 : (starRingEnd ℂ) (Γ i j) = _ := h1.trans (hform' i j)
    have h3 := congrArg (starRingEnd ℂ) h2
    simpa only [Complex.conj_conj] using h3
  · intro hE
    have h1 : Fl.IsHodgeGram C.t.G C.t.PP.L (spMap (conjPts C.ψ (star z))) v' (Γ.map (starRingEnd ℂ)) := by
      refine key.2 fun i j => ?_
      exact (congrArg (starRingEnd ℂ) (hE i j)).trans (hform' i j).symm
    have h2 := GlobalTheory.T.hodge_gram_complex_conjugate _ _ _ _ _ _ _ _ _ hx' hback h1
    have h3 : (Γ.map (starRingEnd ℂ)).map (starRingEnd ℂ) = Γ := by
      ext i j
      simp
    rwa [h3] at h2

theorem exists_log_periods_of_root : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → ∃ (ρ : ℝ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a C.g Λ) (e : Flat.FamExp C.t.G C.M (Metric.ball 0 ρ) C.ψ), 0 < ρ ∧ ρ ≤ 1 ∧ (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ p, p ∈ e.per ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ↔ ∃ x, L.P w x = p) ∧ ∀ z ∈ Flat.punct n a 1, C.IsRiem ((ρ : ℂ) • z) (L.H z) := by
  intro E _ _ _ H D l Xo σ n a C hpq hσ
  obtain ⟨g', ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  obtain ⟨FU⟩ := GlobalTheory.familyUnif_of_laws GlobalTheory.abelianSchemeLaws_all.1 E H D l Xo σ g' ty hpq hσ hty
  have hsemi : IsSemiAbelian C.t.G := C.t.semi
  obtain ⟨ε, hε, hεB, ⟨e₀⟩⟩ := GlobalTheory.T.exists_family_exponential_locally C.R C.t.G C.g n C.M (Metric.ball 0 1) C.ψ hsemi.smooth C.hol 0
    (Metric.mem_ball_self one_pos)
  have h0ε : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ε := Metric.mem_ball_self hε
  obtain ⟨Γ₀, hΓ₀, -, hfin, hfree⟩ := GlobalTheory.T.period_lattice_discrete_free C.R C.t.G C.g n C.M _ C.ψ e₀ 0 h0ε
  let Q : (Fin n → ℂ) → AddSubgroup (Fin C.g → ℂ) := fun b => AddSubgroup.closure (e₀.per b)
  have hQ : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ε, ∀ p, p ∈ Q b ↔ p ∈ e₀.per b := fun b hb p =>
    mem_closure_per e₀ hb p
  have hsp : ∀ x : Γ₀, ∃ (ε' : ℝ) (s : (Fin n → ℂ) → (Fin C.g → ℂ)), 0 < ε' ∧
      DifferentiableOn ℂ s (Metric.ball 0 ε') ∧ s 0 = x ∧ ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ε', s b ∈ Q b := by
    intro x
    obtain ⟨ε', s, h0, hsub, hd, hs0, hs⟩ := GlobalTheory.T.period_holomorphic_continuation C.R C.t.G C.g n C.M _ C.ψ e₀ Metric.isOpen_ball 0 h0ε x
      (by rw [← hΓ₀]; exact x.2)
    exact ⟨ε', s, h0, hd, hs0, fun b hb => (hQ b (hsub hb) _).2 (hs b hb)⟩
  obtain ⟨ρ, hρ0, hρc, S, hSd, hS0, hSa, hSq⟩ := exists_additive_sections Γ₀ Q (min 1 ε) (lt_min one_pos hε) hsp
  have hρ1 : ρ ≤ 1 := hρc.trans (min_le_left _ _)
  have hball : Metric.ball (0 : Fin n → ℂ) ρ ⊆ Metric.ball 0 ε :=
    Metric.ball_subset_ball (hρc.trans (min_le_right _ _))
  have hball1 : Metric.ball (0 : Fin n → ℂ) ρ ⊆ Metric.ball 0 1 := Metric.ball_subset_ball hρ1
  have h0ρ : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ρ := Metric.mem_ball_self hρ0
  let e : FamExp C.t.G C.M (Metric.ball 0 ρ) C.ψ := restrict e₀ Metric.isOpen_ball hball
  have hQ' : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ p, p ∈ Q b ↔ p ∈ e.per b := fun b hb p => hQ b (hball hb) p
  have hΓ₀' : (Γ₀ : Set (Fin C.g → ℂ)) = e.per 0 := hΓ₀
  have hSp : ∀ x, ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, S x b ∈ e.per b := fun x b hb =>
    (hQ' b hb _).1 (hSq x b hb)
  obtain ⟨i, Hf, hrank, hopen, hloc⟩ := GlobalTheory.T.boundary_chart_hodge_matrix E H D l Xo σ n a C g' ty FU ρ e hρ0 hρ1
  obtain ⟨hfreeL, hfinL, -⟩ := GlobalTheory.Coisotropic.lattice_rank E H (FU.Di i)
  have hU : ∀ z ∈ punct n a 1, (ρ : ℂ) • z ∈ punct n a ρ := fun z hz => (smul_mem_punct hρ0).2 hz
  have hsm : Differentiable ℂ (fun z : Fin n → ℂ => (ρ : ℂ) • z) := differentiable_id.fun_const_smul _
  have key : ∃ L : Flat.LogPeriods n a C.g (FU.Di i).La, L.H = (fun z => Hf ((ρ : ℂ) • z)) ∧
      ∀ w ∈ logCover L.a_le, (L.P w).range = Q ((ρ : ℂ) • expCover a w) := by
    refine GlobalTheory.T.period_lattice_on_punctured_disc n a C.g C.a_le (FU.Di i).La (FU.Di i).EF (fun z => Q ((ρ : ℂ) • z))
      (fun z => Hf ((ρ : ℂ) • z)) (punct n a 1) Γ₀ (fun x z => S x ((ρ : ℂ) • z)) rfl hrank (FU.Di i).alt
      (FU.Di i).unimod ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact fun z hz => ⟨(hopen _ (hU z hz)).1, fun x hx => (hopen _ (hU z hz)).2.1 x hx⟩
    · intro z₀ hz₀
      obtain ⟨N, hNo, hzN, hNp, P, hPd, hP⟩ := hloc _ (hU z₀ hz₀)
      refine ⟨(fun z => (ρ : ℂ) • z) ⁻¹' N, hNo.preimage hsm.continuous, hzN,
        fun z hz => (smul_mem_punct hρ0).1 (hNp hz), fun z => P ((ρ : ℂ) • z), fun x => ?_, fun z hz => ?_⟩
      · exact (hPd x).comp hsm.differentiableOn (fun z hz => hz)
      · obtain ⟨h1, h2, h3⟩ := hP _ hz
        refine ⟨h1, ?_, h3⟩
        ext p
        have h4 : p ∈ (P ((ρ : ℂ) • z)).range ↔ p ∈ e.per ((ρ : ℂ) • z) := by
          rw [← SetLike.mem_coe, h2]
        rw [h4]
        exact (hQ' _ (punct_subset_ball (hNp hz)) p).symm
    · intro x
      refine ⟨(hSd x).comp hsm.differentiableOn (fun z hz => smul_mem_ball hρ0 hz), ?_,
        fun z hz => hSq x _ (smul_mem_ball hρ0 hz.1)⟩
      show S x ((ρ : ℂ) • 0) = x
      rw [smul_zero]
      exact hS0 x
    · exact fun x y z => hSa x y _
    · intro s hs hsU
      obtain ⟨u, hu, huU⟩ := exists_seq_punct (n := n) (a := a)
      have hρc' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
      have htend : Tendsto (fun k => (ρ : ℂ) • u k) atTop (𝓝 0) := by
        have h := hu.const_smul (ρ : ℂ)
        rwa [smul_zero] at h
      have hcl := GlobalTheory.T.period_set_closed C.R C.t.G C.g n C.M (Metric.ball 0 ρ) C.ψ e hsemi.separated
        ⟨Metric.isOpen_ball, fun r => (C.hol.2 r).mono hball1⟩ 0 h0ρ (fun b => s ((ρ : ℂ)⁻¹ • b))
        (ContinuousAt.comp_of_eq hs (continuous_const_smul _).continuousAt (smul_zero _))
        (htend.frequently (Eventually.frequently (Eventually.of_forall fun k => by
          refine ⟨punct_subset_ball (hU _ (huU k)), ?_⟩
          show s ((ρ : ℂ)⁻¹ • (ρ : ℂ) • u k) ∈ e.per ((ρ : ℂ) • u k)
          rw [smul_smul, inv_mul_cancel₀ hρc', _root_.one_smul]
          exact (hQ' _ (punct_subset_ball (hU _ (huU k))) _).1 (hsU _ (huU k)))))
      have h0 : s 0 ∈ e.per 0 := by simpa using hcl
      rw [← hΓ₀'] at h0
      exact h0
    · rw [hΓ₀']
      exact GlobalTheory.T.period_lattice_spans C.R C.t.G C.g n C.M _ C.ψ e hsemi 0 h0ρ
    · intro N hN
      obtain ⟨T, hT, hTw⟩ := GlobalTheory.T.torsion_periods_finite_quotient E H C.R C.t C.g n C.M (Metric.ball 0 ρ) C.ψ e C.dim 0 h0ρ Γ₀ hΓ₀' N hN
      refine ⟨T, hT, fun x y hx z hz => ?_⟩
      have hb := hU z hz
      have hbm := punct_subset_ball hb
      have hc := cubWeil_carry e hρ0 N hN (S x) (S y) (hSd x) (hSd y) (hSp x) (hSp y) 1 (by
        rw [hS0 x, hS0 y]
        have h1 : unitOn (1 : ℂˣ) = 1 := map_one _
        rw [h1]
        exact hTw x y hx) _ hbm
      have hz' := (hopen _ hb).2.2.2 N 1 hN _ (hSp x _ hbm) _ (hSp y _ hbm) hc
      exact exists_int_of_exp_eq_one hN hz'
  obtain ⟨L, hLH, hLr⟩ := key
  refine ⟨ρ, (FU.Di i).La, inferInstance, L, e, hρ0, hρ1, fun w hw p => ?_, fun z hz => ?_⟩
  · have hzρ := hU _ (expCover_mem_punct L.a_le hw)
    have hzb := punct_subset_ball hzρ
    constructor
    · intro hp
      have h : p ∈ (L.P w).range := by
        rw [hLr w hw]
        exact (hQ' _ hzb _).2 hp
      exact h
    · rintro ⟨x, rfl⟩
      have h : L.P w x ∈ (L.P w).range := ⟨x, rfl⟩
      rw [hLr w hw] at h
      exact (hQ' _ hzb _).1 h
  · rw [hLH]
    exact (hopen _ (hU z hz)).2.2.1

theorem rt0_conj_neg_ne_zero (H : Host E) : (starRingEnd ℂ) H.rt0 = -H.rt0 :=
  _root_.UpperTheory.Reformulated.B.StarRingEndRootEqNeg.rt0_conj_neg_ne_zero H

theorem exists_logPeriods_famExp_isRiem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a), 1 ≤ D.p + D.q → ∃ (ρ : ℝ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a C.g Λ) (e : Flat.FamExp C.t.G C.M (Metric.ball 0 ρ) C.ψ), 0 < ρ ∧ ρ ≤ 1 ∧ (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ p, p ∈ e.per ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ↔ ∃ x, L.P w x = p) ∧ ∀ z ∈ Flat.punct n a 1, C.IsRiem ((ρ : ℂ) • z) (L.H z) := by
  intro E _ _ _ H D l Xo σ n a C hpq
  have h1 : (σ (baseKA l).ρ) ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, (baseKA l).ρ_sq]
    simp
  have h2 : (σ (baseKA l).ρ - H.rt0) * (σ (baseKA l).ρ + H.rt0) = 0 := by
    have := H.sqrt_neg_disc_sq
    linear_combination h1 - this
  rcases mul_eq_zero.1 h2 with h | h
  · exact exists_log_periods_of_root E H D l Xo σ n a C hpq (sub_eq_zero.1 h)
  have hσ' : ((starRingEnd ℂ).comp σ) (baseKA l).ρ = H.rt0 := by
    have h3 : σ (baseKA l).ρ = -H.rt0 := eq_neg_of_add_eq_zero_left h
    show (starRingEnd ℂ) (σ (baseKA l).ρ) = H.rt0
    rw [h3, map_neg, rt0_conj_neg_ne_zero, neg_neg]
  obtain ⟨ρ, Λ, iΛ, L', e', hρ0, hρ1, hper, hriem⟩ :=
    exists_log_periods_of_root E H D l Xo ((starRingEnd ℂ).comp σ) n a (chart C) hpq hσ'
  obtain ⟨L, hLP, hLH⟩ := GlobalTheory.T.log_periods_conjugate_exists n a C.g Λ L'
  obtain ⟨e, hper'⟩ := GlobalTheory.T.family_exponential_conjugate C.R C.t.G C.g n C.M ρ C.ψ e'
  refine ⟨ρ, Λ, iΛ, L, e, hρ0, hρ1, fun w hw p => ?_, fun z hz => ?_⟩
  · have hw' : star w ∈ logCover L'.a_le := (star_mem_logCover _).2 hw
    rw [hper', star_real_smul, star_expCover]
    have h4 := hper (star w) hw' (star p)
    refine h4.trans ?_
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, (hLP w x).trans ((congrArg star hx).trans (star_star p))⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, ((congrArg star (hLP w x)).trans (star_star _)).symm⟩
  · have h := hriem (star z) (star_mem_punct.2 hz)
    rw [hLH]
    refine isRiem_of_chart C _ _ ?_
    rw [star_real_smul]
    exact h

end GlobalTheory.CompanionTheory.Ar.Flat.Conj
