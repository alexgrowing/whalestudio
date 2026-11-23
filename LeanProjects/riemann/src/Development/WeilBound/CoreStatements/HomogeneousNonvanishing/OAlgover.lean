import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SplitComps
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.OAlgoverAlg
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptMultihomogFormStatement
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.NonvanishingDense
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace PositivityTheory.UnitarySelfGeneration

theorem ao_fderiv {I I' : Type} [Fintype I] [Fintype I'] {n : ℕ} (e : I' ≃ I) (f : (Fin n → ℂ) → I → ℂ)
    (x : Fin n → ℂ) (h : (fderiv ℂ f x).ker = ⊥) : (fderiv ℂ (fun z i => f z (e i)) x).ker = ⊥ := by
  have := (LinearEquiv.funCongrLeft ℂ ℂ e).toContinuousLinearEquiv.comp_fderiv (f := f) (x := x)
  rw [eq_bot_iff] at h ⊢
  intro v hv
  refine h ?_
  have hv' : fderiv ℂ ((LinearEquiv.funCongrLeft ℂ ℂ e).toContinuousLinearEquiv ∘ f) x v = 0 := hv
  rw [this] at hv'
  exact (LinearEquiv.funCongrLeft ℂ ℂ e).toContinuousLinearEquiv.map_eq_zero_iff.1 hv'

theorem o_algover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : Top.RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (x : Sp RM.Ω ⟶ Xo.XF c), Or.𝔐.ξ ≫ Or.𝔐.f = x ≫ Y.j → Mono (spMap β) → (∀ x : Sys.X, ∃ (U : Set Sys.X) (lam : Sys.X → Fin (Fx.m + 1) → ℂ), IsOpen U ∧ x ∈ U ∧ (∀ i, Sys.A.HoloOn U fun y => lam y i) ∧ (∀ y ∈ U, ∃ a₀ : ℂ, a₀ ≠ 0 ∧ lam y = a₀ • Fx.pt y) ∧ ∀ p, lam x p ≠ 0 → ∀ j, x ∈ (Sys.A.chart j).source → (fderiv ℂ (fun z i => lam ((Sys.A.chart j).symm z) i / lam ((Sys.A.chart j).symm z) p) (Sys.A.chart j x)).ker = ⊥) → AlgOver (Or.Re.comap some) := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx Or x hx hβ hloc
  choose U lam hU hmem hholo hpt himm using hloc
  have hP : IsMultiHomogIdeal (mCoordIdeal RM.y) := RM.arith.2.1.2.1
  have hl : ∀ x, Or.Re.R.lift x x ∈ mcPts (mCoordIdeal RM.y) := fun x => Or.Re.R.mem x x (Or.Re.R.mem_U x)
  have honto : Function.Surjective Or.Re.π := by
    have hc : IsClosed (Set.range Or.Re.π) := (isCompact_range Or.Re.holo.1).isClosed
    have hd : Dense (Or.Re.br)ᶜ := interior_eq_empty_iff_dense_compl.1 Or.Re.degree.2.1
    have hs : (Or.Re.br)ᶜ ⊆ Set.range Or.Re.π := fun x hx =>
      Set.nonempty_of_ncard_ne_zero (s := Or.Re.π ⁻¹' {x}) (by
        rw [Or.Re.degree.2.2.2.2.1 x hx]; exact Or.Re.deg_pos.ne')
    rw [← Set.range_eq_univ, ← hc.closure_eq]
    exact (hd.mono hs).closure_eq

  have hπ : ∀ x' x, Or.Re.π x' ∈ U x → ∃ a : ℂ, a ≠ 0 ∧
      ∀ i, lam x (Or.Re.π x') i = a * Or.Re.R.lift x' x' ⟨Or.k₀, Or.ix i⟩ := fun x' x h => by
    obtain ⟨a, ha⟩ := Or.π_pt x'
    obtain ⟨a₀, h0, e⟩ := hpt x _ h
    have ha0 : a ≠ 0 := by
      rintro rfl
      obtain ⟨i, hi⟩ := (hl x').1 Or.k₀
      obtain ⟨i, rfl⟩ := Or.ix.surjective i
      exact hi (by simpa using congrFun ha i)
    refine ⟨a₀ / a, div_ne_zero h0 ha0, fun i => ?_⟩
    have := congrFun ha i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [e, this, Pi.smul_apply, smul_eq_mul]
    field_simp
  obtain ⟨b, d, hbd, hb, hint⟩ := GlobalTheory.T.hodge_cpt_multihomog_form E H D l Xo c O β Y S RM.Ω RM.K RM.ι RM.y Or.𝔐 x hx hβ
  letI := Or.g.toAlgebra
  have : FiniteDimensional Fx.Ωf RM.Ω := Module.finite_of_finrank_pos (by
    rw [Or.g_deg, ← Or.Re_deg]; exact Or.Re.deg_pos)
  obtain ⟨n, s, hs, hsQ, hs0⟩ := AlgOv.norm_form Or.k₀ Or.ix Fx.yf Or.y_eq Fx.generate hbd hb
  have hQ := AlgOv.imageZ_blk Or.k₀ Or.ix RM.y
  refine ⟨Unit, inferInstance, fun _ => Fin (Fx.m + 1), inferInstance, fun _ => Or.k₀, AlgOv.blk Or.k₀ Or.ix, U,
    fun x y p => lam x y p.2, s, fun _ => n, ⟨fun _ _ _ => rfl, ?_, fun _ => rfl, ?_⟩,
    ⟨hU, hmem, fun x p => hholo x p.2, ?_, ?_, ?_, ?_, ?_⟩, ?_, hs, fun h => hsQ (hQ ▸ h), ?_⟩
  · rintro ⟨_, i⟩ ⟨_, j⟩ h
    have : Or.ix i = Or.ix j := eq_of_heq (Sigma.mk.inj h).2
    rw [Or.ix.injective this]
  · rintro ⟨k, i⟩ ⟨_, rfl⟩
    exact ⟨⟨(), Or.ix.symm i⟩, by simp [AlgOv.blk]⟩
  · intro x y hy
    obtain ⟨x', rfl⟩ := honto y
    obtain ⟨a, ha, e⟩ := hπ x' x hy
    have hw := AlgOv.scale_mem hP (hl x') ha
    refine ⟨fun k => ?_, fun f hf => ?_⟩
    · obtain ⟨i, hi⟩ := hw.1 Or.k₀
      obtain ⟨i, rfl⟩ := Or.ix.surjective i
      exact ⟨i, fun h => hi ((e i).symm.trans h)⟩
    · have := hw.2 _ hf
      rw [AlgOv.evC_eq] at this ⊢
      refine Eq.trans ?_ ((aeval_rename _ _ f).symm.trans this)
      congr 2
      exact funext fun p => e p.2
  · intro x x' y hy
    obtain ⟨a, ha, e⟩ := hpt x y hy.1
    obtain ⟨a', ha', e'⟩ := hpt x' y hy.2
    refine ⟨fun _ => a / a', fun _ => div_ne_zero ha ha', funext fun p => ?_⟩
    simp only [e, e', Pi.smul_apply, smul_eq_mul]
    field_simp
  · intro z hz
    obtain ⟨w, hw, a, ha, e⟩ := AlgOv.blk_onto Or.k₀ Or.ix
      (fun k => (hl (honto Or.Re.nonempty_base.some).choose).1 k |>.imp fun i hi =>
        AlgOv.coord_ne (hl _) hi) (hQ ▸ hz)
    obtain ⟨x', t, ht, e'⟩ := r_onto RM.K RM.ι _ _ _ Or.Re.R RM.arith w hw
    obtain ⟨a', ha', e''⟩ := hπ x' _ (hmem _)
    refine ⟨Or.Re.π x', fun _ => a' * t Or.k₀ / a, fun _ => div_ne_zero (mul_ne_zero ha' (ht _)) ha,
      funext fun p => ?_⟩
    have h1 : Or.Re.R.lift x' x' ⟨Or.k₀, Or.ix p.2⟩ = t Or.k₀ * w (AlgOv.blk Or.k₀ Or.ix p) := congrFun e' _
    show lam _ _ p.2 = _ * z p
    rw [e'', h1, e p]
    field_simp
  · rintro x x' ⟨t, ht, e⟩
    obtain ⟨a, ha, e1⟩ := hpt x x (hmem x)
    obtain ⟨a', ha', e2⟩ := hpt x' x' (hmem x')
    refine Fx.pt_inj x x' (t () * a' / a) (funext fun i => ?_)
    have : lam x x i = t () * lam x' x' i := congrFun e ⟨(), i⟩
    simp only [e1, e2, Pi.smul_apply, smul_eq_mul] at this ⊢
    field_simp
    linear_combination this
  · intro x p hp j hj
    exact ao_fderiv (Equiv.uniqueSigma fun _ : Unit => Fin (Fx.m + 1)) _ _ (himm x (p ()) (hp ()) j hj)
  · intro x'
    obtain ⟨a, ha, e⟩ := hπ x' _ (hmem _)
    exact ⟨fun _ => a, fun _ => ha, funext fun p => e p.2⟩
  · intro x hxb
    obtain ⟨x', rfl⟩ := honto x
    obtain ⟨a, ha, e⟩ := hπ x' _ (hmem _)
    have hb0 : aeval (Or.Re.R.lift x' x') b = 0 := by
      by_contra h
      obtain ⟨z, hz1, hz2⟩ := hint _ (hl x') (fun h' => h ((AlgOv.evC_eq _ _).symm.trans h'))
      exact (Or.interior x' z hz1).1 hz2 hxb
    refine (AlgOv.evC_eq _ _).trans ?_
    have h1 := aeval_blockScale hs (fun _ => a) (Or.Re.R.lift x' x' ∘ AlgOv.blk Or.k₀ Or.ix)
    rw [hs0 _ (hl x') hb0, mul_zero] at h1
    refine Eq.trans ?_ h1
    congr 2
    exact funext fun p => e p.2

end PositivityTheory.UnitarySelfGeneration
