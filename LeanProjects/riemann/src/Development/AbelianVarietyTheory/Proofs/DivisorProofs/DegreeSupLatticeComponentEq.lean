import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeDegreeEqNegLogFrameHeightStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegreeLieLatticeHermitianInvariant
import Formalism.HarderNarasimhan.ShiftInvariance
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

section General

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]

theorem finrank_eq_two_mul_nPl : Module.finrank ℚ K = 2 * Formalism.HN.nPl K := by
  rw [IsTotallyComplex.finrank, Formalism.HN.nPl, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]

theorem rkK_mul_muDef [StarRing K] {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) {L : Submodule (𝓞 K) V} (hL : L.FG)
    (hr : Formalism.HN.rkK L ≠ 0) :
    (Formalism.HN.rkK L : ℝ) * (Formalism.HN.muDef b X L / 2) = -Real.log (Formalism.HN.ht b X L) / (2 * (Formalism.HN.nPl K : ℝ)) := by
  obtain ⟨-, hrk, hht⟩ := Formalism.HN.plLat K V ι b X hX L hL
  have hd : (0 : ℝ) < |(NumberField.discr K : ℝ)| := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero K)
  have hf : (0 : ℝ) < (Formalism.HN.nPl K : ℝ) := by
    have : 0 < Formalism.HN.nPl K := Fintype.card_pos
    exact_mod_cast this
  have hj : (0 : ℝ) < (Formalism.HN.rkK L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hr
  have e₁ : Formalism.HN.ht b X L = (2 : ℝ) ^ (Formalism.HN.nPl K * Formalism.HN.rkK L) *
      |(NumberField.discr K : ℝ)| ^ (-(Formalism.HN.rkK L : ℝ) / 2) *
      Formalism.F.covol (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) L) := rfl
  have hC : 0 < Formalism.F.covol (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) L) := by
    rw [e₁] at hht
    exact pos_of_mul_pos_right hht (by positivity)
  have hlog : Real.log (Formalism.HN.ht b X L) = ((Formalism.HN.nPl K : ℝ) * Formalism.HN.rkK L) * Real.log 2 +
      (-(Formalism.HN.rkK L : ℝ) / 2) * Real.log |(NumberField.discr K : ℝ)| +
      Real.log (Formalism.F.covol (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) L)) := by
    rw [e₁, Real.log_mul (by positivity) hC.ne', Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_rpow hd]
    push_cast; ring
  have hrk' : (Formalism.F.rk (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) L) : ℝ) =
      2 * (Formalism.HN.nPl K : ℝ) * Formalism.HN.rkK L := by
    have : Formalism.F.rk (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) L) = Module.finrank ℚ K * Formalism.HN.rkK L := hrk
    rw [this, finrank_eq_two_mul_nPl]; push_cast; ring
  have hmu : Formalism.HN.muDef b X L = 2 * (-Real.log (Formalism.F.covol (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) L)) /
      (2 * (Formalism.HN.nPl K : ℝ) * Formalism.HN.rkK L)) - Real.log 2 +
      Real.log |(NumberField.discr K : ℝ)| / (2 * (Formalism.HN.nPl K : ℝ)) := by
    rw [Formalism.HN.muDef, Formalism.HN.slope, Formalism.F.slope, Formalism.F.deg, hrk', Formalism.HN.logDisc, finrank_eq_two_mul_nPl]
    push_cast; ring
  rw [hmu, hlog]
  field_simp
  ring

theorem pgeoDeg_eq_deg {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K V) (hinv : h.IsConjInv) {N : (K →+* ℂ) → V → ℝ} (hN : ∀ σ x, h.nrm σ x = N σ x)
    (hg : AllWt.HasGram N) {L : Submodule (𝓞 K) V} (hL : L.FG) : ReciprocityTheory.GeometryOfNumbersTheory.deg h L = AllWt.deg N L := by
  by_cases h0 : L = ⊥
  · subst h0
    have hv : ReciprocityTheory.GeometryOfNumbersTheory.IsFrame K (⊥ : Submodule (𝓞 K) V) (Fin.elim0 : Fin 0 → V) :=
      ⟨fun i => i.elim0, linearIndependent_empty_type, by simp⟩
    rw [AllWt.deg_bot, ReciprocityTheory.GeometryOfNumbersTheory.arakelovDegree_eq_degreeOfFamily h hL hv]
    simp [ReciprocityTheory.GeometryOfNumbersTheory.degreeOfFamily, ReciprocityTheory.GeometryOfNumbersTheory.HermFam.gram]
  letI : StarRing K := starRingOfComm
  obtain ⟨n, ⟨b, X⟩, hG⟩ := hg.some
  haveI : FiniteDimensional K V := Module.Basis.finiteDimensional_of_finite b
  have hr : Formalism.HN.rkK L ≠ 0 := by
    intro hr
    apply h0
    rw [Formalism.HN.rkK, Submodule.finrank_eq_zero] at hr
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ Submodule.span K (L : Set V) := Submodule.subset_span hx
    rw [hr, Submodule.mem_bot] at hx'
    rw [hx']
    exact zero_mem _
  rw [GlobalTheory.T.hermitian_lattice_degree_eq_neg_log_frame_height K V h hinv (Fin n) b X (fun v => (hG v).1) (fun v x => ((hG v).2 x).trans (hN _ x).symm) L hL,
    AllWt.deg, AllWt.slope, AllWt.slope_sq_eq hG hL, rkK_mul_muDef b X (fun v => (hG v).1) hL hr]

end General

theorem isTotallyComplex_coeff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}
    (c : Coeff l) : IsTotallyComplex c.F :=
  ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => CompHt.conj_comp_ne (c := c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩

theorem Ready.degM_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice X Z U P) (ω : CanId R.toModif) (x : ℝ) (D : Formalism.BasicNotions.D7) (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), ∀ j ≤ P.T, (h.data f₁ f₂ th k).degM j = GlobalTheory.AllWt.degOn U x V dict Z (GlobalTheory.AllWt.wtOf Dw (P.wt j) 0) := by
  intro E _ _ _ H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k j hj
  haveI : IsTotallyComplex c.F := isTotallyComplex_coeff c
  have hM : (h.data f₁ f₂ th k).M j = (GlobalTheory.AllWt.latOn U Z (GlobalTheory.AllWt.wtOf Dw (P.wt j) 0)).map
      ((h.equivV f₁ f₂ th k hj).toLinearMap.restrictScalars (𝓞 c.F)) := by
    ext y
    constructor
    · intro hy
      refine ⟨(h.equivV f₁ f₂ th k hj).symm y, ?_, (h.equivV f₁ f₂ th k hj).apply_symm_apply y⟩
      refine (h.equivV_mem f₁ f₂ th k hj _).1 ?_
      rw [LinearEquiv.apply_symm_apply]
      exact hy
    · rintro ⟨g, hg, rfl⟩
      exact (h.equivV_mem f₁ f₂ th k hj g).2 hg
  rw [HilbertSamuel.Data.degM, hM, ← FibIndep.deg_map_of_isometry
    (HermTools.comap ((h.data f₁ f₂ th k).nm j) (h.equivV f₁ f₂ th k hj).toLinearMap
      (h.equivV f₁ f₂ th k hj).injective) _ (h.equivV f₁ f₂ th k hj).toLinearMap (fun _ _ _ => rfl)
    (h.good j hj).2.1]
  exact pgeoDeg_eq_deg _ (HermTools.isConjInv_comap ((h.data f₁ f₂ th k).conjInv j) _ _)
    (fun σ x => h.nrm_equivV f₁ f₂ th k hj σ x) (h.good j hj).1 (h.good j hj).2.1

end GlobalTheory.CompHS
