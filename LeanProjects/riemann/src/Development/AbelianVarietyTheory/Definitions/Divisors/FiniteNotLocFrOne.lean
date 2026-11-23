import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NvalDetFrChgConst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetIntegralOfDefinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenImmersionOfSection
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PosDefOneSubOfSumSqLt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MetricDataUnique
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MetricChangeOfFrame
import Development.AbelianVarietyTheory.Counterexamples.MetricPositivity.PosSemidefOfIsMetric
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongrOfDvdModulus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisationDataNonemptyComponent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDatumSumAndAllSignatures
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelGoodAtAllPrimesAndIdx
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSpanningHypotheses
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LinearIndependentOfIsLieBasis
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroupStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisationDataNonemptyComponentStatement

noncomputable section

namespace GlobalTheory.DefPt.Model

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.Frames
  GlobalTheory.CompHt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_root (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    ∃ ξ : E, cc ξ = -ξ ∧ ξ ^ 2 = -(H.d : E) ∧ ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ).im < 0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have key : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → z.re = 0 ∧ z.im ≠ 0 := by
    intro z hz
    have h1 := congrArg Complex.re hz
    have h2 := congrArg Complex.im hz
    simp [sq] at h1 h2
    have him : z.im ≠ 0 := by
      intro h; rw [h] at h1; nlinarith [mul_self_nonneg z.re]
    refine ⟨?_, him⟩
    have : z.re * z.im = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right him
  have hE : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
    simpa using this
  have hcc : cc (H.rt : E) = -(H.rt : E) := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    have hk := key (τ (H.rt : E)) (by rw [← map_pow, hE, map_neg, map_natCast])
    have : τ (cc (H.rt : E)) = starRingEnd ℂ (τ (H.rt : E)) := IsCMField.complexEmbedding_complexConj E τ _
    rw [this, map_neg]
    apply Complex.ext <;> simp [hk.1]
  rcases lt_or_gt_of_ne (key _ H.sqrt_neg_disc_sq).2 with h | h
  · exact ⟨H.rt, hcc, hE, fun τ hτ => hτ ▸ h⟩
  · refine ⟨-(H.rt : E), ?_, by rw [neg_sq, hE], fun τ hτ => by rw [map_neg, hτ]; simpa using h⟩
    rw [show cc (-(H.rt : E)) = -cc (H.rt : E) by simp [cc], hcc]

theorem exists_defCase (p : ℕ) (hp : 1 ≤ p) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
      (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ),
      Dw.p = p ∧ 0 < ξ ∧ Nonempty (Comp Xo c) ∧ DefCase U ξ := by
  obtain ⟨E, i1, i2, i3, H, -, hD⟩ := GlobalTheory.exists_datum_sum_and_all_signatures.2
  obtain ⟨D, rfl, hq⟩ := hD p 0
  have hpq : 1 ≤ D.p + D.q := by omega
  obtain ⟨l, hA, hg, -⟩ := GlobalTheory.exists_level_goodAt_all_primes_and_idx E H 1 one_pos
  obtain ⟨Xo⟩ := GlobalTheory.Moduli.moduli_scheme_exists _ _ D l hpq
  obtain ⟨c₀⟩ : Nonempty (Coeff l) := inferInstance
  obtain ⟨-, c, -, hc⟩ := GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ D l Xo c₀ hpq
  obtain ⟨ξ, hξ, hsq, hneg⟩ := exists_root H
  have hξ0 : ξ ≠ 0 := fun h => by
    rw [h] at hsq
    have : (H.d : E) = 0 := by linear_combination hsq
    exact H.d_prime.ne_zero (by exact_mod_cast this)
  obtain ⟨Gm, φ, hφ⟩ := GlobalTheory.exists_herm_coord_of_datum E H D (-ξ)
    (by rw [show cc (-ξ) = -cc ξ by simp [cc], hξ]) (neg_ne_zero.2 hξ0) _ rfl
  have key : ∀ σ : c.F →+* ℂ, ∃ U : Unf Xo c σ (D.p + D.q), GoodEmb c σ →
      IsUnf U ∧ Nonempty U.Comp ∧ ∀ k, (U.X k).ξ0 = ξ := by
    intro σ
    by_cases hσ : GoodEmb c σ
    · obtain ⟨U, hu, -, hk, -, hG, -⟩ := GlobalTheory.FrameUnif.exists_unf_hasPrinc E H D l Xo c σ _ ξ Gm φ hpq hσ hξ hneg hφ
      exact ⟨U.toPj, fun _ => ⟨hu, hk, fun k => (hG k).2⟩⟩
    · obtain ⟨U, -⟩ := GlobalTheory.T.exists_uniformisationData_nonempty_component E H D l Xo c hpq σ
      exact ⟨U.toPj, fun h => absurd h hσ⟩
  choose U hU using key
  have habs : ∀ τ : E →+* ℂ, ‖τ ξ‖ = Real.sqrt H.d := fun τ => by
    have h1 : ‖τ ξ‖ ^ 2 = H.d := by
      rw [← norm_pow, ← map_pow, hsq, map_neg, map_natCast, norm_neg, Complex.norm_natCast]
    rw [← h1, Real.sqrt_sq (norm_nonneg _)]
  exact ⟨E, i1, i2, i3, H, D, l, Xo, c, _, U, Real.sqrt H.d, rfl, Real.sqrt_pos.2 (by exact_mod_cast H.d_prime.pos),
    (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ D l Xo c hpq).1,
    ⟨hq, hp, hg, hA, hc c le_rfl, fun σ h => (hU σ h).1, fun σ h k τ => by rw [(hU σ h).2.2 k]; exact habs τ⟩⟩

open scoped ComplexOrder in

theorem posDef_of_isMetric {σ : c.F →+* ℂ} {y : FrPt Xo c (CAt σ)} {N : ℝ} {Gr : Mats Dw ℂ}
    (h : GlobalTheory.LamT.IsMetric y N Gr) (b : E →+* ℂ) : (Gr b).PosDef := by
  obtain ⟨Φ, u, Hm, χ, θ, Fd, w, W, -, hA, -, -, -, -, h7, h8⟩ := h
  obtain ⟨-, -, -, -, -, t2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH GlobalTheory.thetaUnifAV_all Φ.key.P _ u Hm χ hA
  obtain ⟨l1, l2⟩ := GlobalTheory.MetricChange.lift_comb Φ.m.cart
  obtain ⟨M, _, _, v, ρ, -, htan, hcomb, -, -⟩ := GlobalTheory.T.exists_tangent_module_universal_group E H Dw l Xo (CAt σ) y.x
  choose β hβ using fun i => (htan (y.u b i)).1 (y.tan b i)
  have hu : y.u b = fun i => v (β i) := funext fun i => (hβ i).symm
  have hw : y.u b = fun i => (w b i).left ≫ Φ.m.φ := funext fun i => (h7 b i).1.symm
  have ht : ∀ j, IsTangent (w b j) := fun j => l1 _ ((h7 b j).1.symm ▸ y.tan b j)
  have hli : LinearIndependent ℂ (W b) := by
    rw [Fintype.linearIndependent_iff]
    intro cf hcf i
    let d : Fin (Dw.mult b) → ℂ := Pi.single i 1 + cf
    have h1 : IsCombAt y.x (y.u b) (S := CAt σ) d (v (∑ j, (show CAt σ from d j) • β j)) := by
      rw [hu]; exact (hcomb _ β d _).2 rfl
    obtain ⟨w', e1, e2⟩ := l2 _ d (w b) _ (hw ▸ h1)
    have h2 := (GlobalTheory.LamT.existsUnique_isDiff_and_linear Φ.key u).2 _ (w b) (W b) d w' ht (fun j => (h7 b j).2) e2
    have h3 : ∑ j, d j • W b j = W b i := by
      simp only [d, Pi.add_apply, add_smul, Finset.sum_add_distrib, hcf, add_zero]
      simp [Pi.single_apply]
    rw [h3] at h2
    have h4 : w' = w b i := (t2 _).unique ⟨l1 _ (e1 ▸ (htan _).2 ⟨_, rfl⟩), h2⟩ ⟨ht i, (h7 b i).2⟩
    rw [← e1, h4, (h7 b i).1] at h1
    have h5 := ((frChg_refl_and_comp E H Dw l Xo c _ y y y).1).2.1 b i
    have h6 := congrFun ((y.basis b _ (y.tan b i) (y.eig b i)).unique h1 h5) i
    have h9 : (1 : ℂ) + cf i = 1 := by
      have e : d i = 1 + cf i := by simp [d]
      rw [← e]
      exact h6.trans (Matrix.one_apply_eq i)
    simpa using h9
  have := GlobalTheory.CM.LieMetric.posDef_gram hA.1 hA.2.1 hli
  convert this using 1
  ext i k
  exact h8 b i k

theorem exists_archFr (hr : 1 ≤ Dw.p + Dw.q) (y₀ : FrPt Xo c c.F) (σ : c.F →+* ℂ) : ∃ N X, ArchFr y₀ σ N X := by
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c c.F (CAt σ)
    (Algebra.ofId _ _) y₀
  obtain ⟨N, Gr, h⟩ := GlobalTheory.MetricTest.exists_isMetric hr z₀
  choose X hX hX' using fun b => GlobalTheory.HolDS.exists_congr_one_of_posDef (posDef_of_isMetric h b)
  refine ⟨N, X, GlobalTheory.MetricTest.pos_of_isMetric h, fun τ => (hX τ).ne_zero, fun z y hz hy => ?_⟩
  obtain rfl := (frMap_unique_refl_iff E H Dw l Xo c _ _ _ y₀).1 _ _ hz hz₀
  have := GlobalTheory.MetricChange.isMetric_frChg E H Dw l Xo c σ z y N Gr X 1 one_ne_zero hy h
  simpa [hX'] using this

theorem archFr_unique (hr : 1 ≤ Dw.p + Dw.q) {y₀ : FrPt Xo c c.F} {σ : c.F →+* ℂ} {N N' : ℝ} {X X' : Mats Dw ℂ}
    (h : ArchFr y₀ σ N X) (h' : ArchFr y₀ σ N' X') : N = N' ∧ ∀ τ, ‖(X τ).det‖ = ‖(X' τ).det‖ := by
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c c.F (CAt σ)
    (Algebra.ofId _ _) y₀
  obtain ⟨N₀, Gr, h₀⟩ := GlobalTheory.MetricTest.exists_isMetric hr z
  have key : ∀ {N : ℝ} {X : Mats Dw ℂ}, ArchFr y₀ σ N X → N = N₀ ∧ ∀ τ, ‖(X τ).det‖ ^ 2 * ‖(Gr τ).det‖ = 1 := by
    intro N X h
    obtain ⟨y, hy, -⟩ := existsUnique_frChg E H Dw l Xo c (CAt σ) z (fun τ => (X τ)ᵀ) 1 fun τ => by
      have : IsUnit ((X τ)ᵀ).det := by rw [Matrix.det_transpose]; exact (h.2.1 τ).isUnit
      exact this
    have h1 := GlobalTheory.MetricChange.isMetric_frChg E H Dw l Xo c σ z y N₀ Gr X 1 one_ne_zero hy h₀
    obtain ⟨e1, e2⟩ := GlobalTheory.LamT.MetUniq.isMetric_unique E H Dw l Xo c σ y _ _ _ _ (h.2.2 z y hz hy) h1
    refine ⟨by simpa using e1, fun τ => ?_⟩
    have e3 := congrArg (fun M => ‖Matrix.det M‖) (congrFun e2 τ)
    simp only [Matrix.det_one, norm_one, Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star] at e3
    linarith
  obtain ⟨a1, a2⟩ := key h
  obtain ⟨b1, b2⟩ := key h'
  refine ⟨a1.trans b1.symm, fun τ => ?_⟩
  have hg : ‖(Gr τ).det‖ ≠ 0 := fun e => by simpa [e] using a2 τ
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (mul_right_cancel₀ hg ((a2 τ).trans (b2 τ).symm))

section Dense

def DenseIn {K : Type} [Field K] (T : CDVR) (io : K →+* T.Fr) : Prop :=
  ∀ (x : T.Fr) (d : T.V), d ≠ 0 → ∃ (k : K) (h : T.V), x = io k + algebraMap T.V T.Fr (d * h)

theorem denseIn_of_residue {K : Type} [Field K] (T : CDVR) (io : K →+* T.Fr) (π : T.V) (hπ : Irreducible π) (p : K)
    (hp : algebraMap T.V T.Fr π = io p)
    (h1 : ∀ v : T.V, ∃ (k : K) (h : T.V), algebraMap T.V T.Fr v = io k + algebraMap T.V T.Fr (π * h)) :
    DenseIn T io := by
  have h2 : ∀ (m : ℕ) (v : T.V), ∃ (k : K) (h : T.V),
      algebraMap T.V T.Fr v = io k + algebraMap T.V T.Fr (π ^ m * h) := by
    intro m
    induction m with
    | zero => exact fun v => ⟨0, v, by simp⟩
    | succ m ih =>
      intro v
      obtain ⟨k, h, e⟩ := ih v
      obtain ⟨k', h', e'⟩ := h1 h
      refine ⟨k + p ^ m * k', h', ?_⟩
      rw [e, map_mul, e']
      simp only [map_add, map_mul, map_pow, hp]
      ring
  intro x d hd
  obtain ⟨v, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := T.V) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hπ
  obtain ⟨m, u', rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hπ
  obtain ⟨k, h, e⟩ := h2 (m + n) (v * ↑u⁻¹)
  have hp0 : io p ≠ 0 := hp ▸ (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 hπ.ne_zero
  have hu : algebraMap T.V T.Fr u * algebraMap T.V T.Fr ↑u⁻¹ = 1 := by rw [← map_mul]; simp
  have hu0 : algebraMap T.V T.Fr u ≠ 0 := left_ne_zero_of_mul_eq_one hu
  refine ⟨k / p ^ n, ↑u'⁻¹ * h, ?_⟩
  have e2 : (u' : T.V) * π ^ m * (↑u'⁻¹ * h) = π ^ m * h := by
    rw [mul_comm (u' : T.V), mul_assoc, Units.mul_inv_cancel_left]
  rw [e2]
  simp only [map_mul, map_pow, hp, map_div₀] at e ⊢
  field_simp
  linear_combination (algebraMap T.V T.Fr u) * e - (algebraMap T.V T.Fr v) * hu

theorem denseIn_of_initial {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (T₀ : CDVR)
    (io₀ : K →+* T₀.Fr)
    (hini : ∀ (T : CDVR) (io : K →+* T.Fr) (e : ℕ), OverLa w T.V io e → ∃ (g : T₀.V →+* T.V) (χ : T₀.Fr →+* T.Fr),
      IsLocalHom g ∧ χ.comp io₀ = io ∧ χ.comp (algebraMap T₀.V T₀.Fr) = (algebraMap T.V T.Fr).comp g ∧
        ∀ ϖ : T₀.V, Irreducible ϖ → vV (K' := T.Fr) T.V (algebraMap T.V T.Fr (g ϖ)) = e) : DenseIn T₀ io₀ := by
  obtain ⟨hdvr, -⟩ := isDiscreteValuationRing_and_finite_residueField_valuationSubringAtPrime K w
    (Ring.HasFiniteQuotients.finiteQuotient w.ne_bot)
  let O := w.valuationSubringAtPrime K
  let V := AdicCompletion (IsLocalRing.maximalIdeal O) O
  have hinj0 : Function.Injective (algebraMap O V) := algebraMap_adicCompletion_injective_of_dvr O
  have hch : CharZero V := charZero_of_injective_algebraMap hinj0
  let T : CDVR := { V := V }
  have hinj : Function.Injective ((algebraMap V (FractionRing V)).comp (algebraMap O V)) :=
    (IsFractionRing.injective V (FractionRing V)).comp hinj0
  let io : K →+* FractionRing V := IsFractionRing.lift (K := K) hinj
  have hio : ∀ x : O, algebraMap V (FractionRing V) (algebraMap O V x) = io x := fun x =>
    (IsFractionRing.lift_algebraMap hinj x).symm
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπV : Irreducible (algebraMap O V π) := irreducible_algebraMap_adicCompletion_of_dvr hπ
  have ho : OverLa w T.V io 1 := GlobalTheory.PlaceCompletion.overLa_one_of_irreducible io (algebraMap O V) hio hπ hπV
  have hD : DenseIn T io := denseIn_of_residue T io _ hπV π (hio π) fun v => by
    obtain ⟨r, hr⟩ := (AdicCompletion.residueField_map_bijective O).2 (IsLocalRing.residue V v)
    obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective r
    have h1 : v - algebraMap O V o ∈ IsLocalRing.maximalIdeal V := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hr, sub_eq_zero]
      rfl
    rw [hπV.maximalIdeal_eq, Ideal.mem_span_singleton] at h1
    obtain ⟨h, e⟩ := h1
    refine ⟨o, h, ?_⟩
    have e' : v = algebraMap O V o + algebraMap O V π * h := by rw [← e]; ring
    exact (congrArg (algebraMap V (FractionRing V)) e').trans (by rw [map_add, hio])
  obtain ⟨g, χ, -, h1, h2, h3⟩ := hini T io 1 ho
  have h2' : ∀ a, χ (algebraMap T₀.V T₀.Fr a) = algebraMap T.V T.Fr (g a) := fun a => RingHom.congr_fun h2 a
  intro x d hd
  have hd0 : algebraMap T₀.V T₀.Fr d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hd
  have hgd : g d ≠ 0 := fun h => (map_ne_zero χ).2 hd0 (by rw [h2', h, map_zero])
  obtain ⟨k, h, e⟩ := hD (χ x) (g d) hgd
  have e1 : χ ((x - io₀ k) / algebraMap T₀.V T₀.Fr d) = algebraMap T.V T.Fr h := by
    have e2 : χ (io₀ k) = io k := RingHom.congr_fun h1 k
    rw [map_div₀, map_sub, e, e2, div_eq_iff ((map_ne_zero χ).2 hd0), h2', map_mul]
    ring
  have e3 := PlaceConst.vV_map_eq g χ h2 1 h3 ((x - io₀ k) / algebraMap T₀.V T₀.Fr d)
  have e4 : 0 ≤ vV T.V (algebraMap T.V T.Fr h) := by
    by_cases h0 : algebraMap T.V T.Fr h = 0
    · simp [h0, vV]
    · have := (WithZero.log_le_log (valV_ne_zero h0) one_ne_zero).2 (GlobalTheory.PlaceCompletion.valV_algebraMap_le_one h)
      simp only [vV]
      rw [WithZero.log_one] at this
      omega
  rw [e1, Nat.cast_one, one_mul] at e3
  obtain ⟨h', e5⟩ := Formalism.L2.PjFree.mem_range_of_vV_nonneg (e3 ▸ e4)
  refine ⟨k, h', ?_⟩
  rw [map_mul, e5]
  field_simp
  ring

theorem DenseIn.matrix {K : Type} [Field K] {T : CDVR} {io : K →+* T.Fr} (hD : DenseIn T io) {n : Type} [Fintype n]
    [DecidableEq n] (g : Matrix n n T.Fr) (hg : g.det ≠ 0) :
    ∃ (B : Matrix n n K) (Y : Matrix n n T.V), B.det ≠ 0 ∧ IsUnit Y.det ∧
      g = B.map io * Y.map (algebraMap T.V T.Fr) := by
  obtain ⟨d₀, hd₀⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors T.V)
    fun p : n × n => g⁻¹ p.1 p.2
  choose A hA using hd₀
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  choose B h hB using fun i j => hD (g i j) (π * d₀) (mul_ne_zero hπ.ne_zero (nonZeroDivisors.ne_zero d₀.2))
  let A' : Matrix n n T.V := Matrix.of fun i j => A (i, j)
  let Y' : Matrix n n T.V := 1 - π • (A' * Matrix.of h)
  have hA' : A'.map (algebraMap T.V T.Fr) = algebraMap T.V T.Fr d₀ • g⁻¹ := by
    ext i j
    simp [A', hA, Algebra.smul_def]
  have hY : IsUnit Y'.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    have hπ0 : IsLocalRing.residue T.V π = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hπ.not_isUnit
    have : (IsLocalRing.residue T.V).mapMatrix Y' = 1 := by
      ext i j
      simp [Y', hπ0, Matrix.one_apply, apply_ite (IsLocalRing.residue T.V)]
    rw [this]
    simp
  have e1 : (Matrix.of B).map io = g * Y'.map (algebraMap T.V T.Fr) := by
    have e2 : Y'.map (algebraMap T.V T.Fr) = 1 - algebraMap T.V T.Fr π •
        (A'.map (algebraMap T.V T.Fr) * (Matrix.of h).map (algebraMap T.V T.Fr)) := by
      rw [← Matrix.map_mul]
      ext i j
      simp only [Y', Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, map_mul,
        Matrix.one_apply, apply_ite (algebraMap T.V T.Fr), map_one, map_zero]
    rw [e2, hA', Matrix.mul_sub, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hg.isUnit, Matrix.one_mul]
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hB i j]
    simp only [map_mul]
    ring
  refine ⟨Matrix.of B, Y'⁻¹, fun h0 => ?_, Matrix.isUnit_nonsing_inv_det _ hY, ?_⟩
  · have e3 := congrArg Matrix.det e1
    rw [Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det] at e3
    exact mul_ne_zero hg (hY.map _).ne_zero e3.symm
  · rw [e1, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hY]
    simp

end Dense

theorem frChg_of_integral (T : CDVR) (io : c.F →+* T.Fr) : letI := io.toAlgebra
    ∀ y y' : FrPt Xo c T.Fr, Integral T io y → Integral T io y' → y'.x = y.x →
      ∃ (A : Mats Dw T.V) (u : T.Vˣ), (∀ τ, IsUnit (A τ).det) ∧
        FrChg (fun τ => (A τ).map (algebraMap T.V T.Fr)) (algebraMap T.V T.Fr u) y y' := by
  letI := io.toAlgebra
  intro y y' hy hy' hx
  have hA := allTest_of_secBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c T.Fr
  obtain ⟨h1, h2⟩ := intLatU_holds E H Dw l Xo c T io ⟨y, hA y, hy⟩ ⟨y', hA y', hy'⟩ hx
  choose A hAu hAc using h1
  obtain ⟨g, a, -, hc⟩ := (frChg_exists_unique E H Dw l Xo c T.Fr y y').1 hx
  obtain ⟨pm, p1, p2, p3⟩ := hc.2.2
  have hid : spMap (RingHom.id T.Fr) = 𝟙 _ := by simp [spMap]
  have hv := h2 a pm p1 (p2.trans (by rw [hid]; exact Category.comp_id _)) p3
  obtain ⟨u, hu⟩ := GlobalTheory.PlaceCompletion.exists_algebraMap_eq_of_valV_le_one hv.le
  obtain ⟨u, rfl⟩ := GlobalTheory.Reg.GenInt.isUnit_of_vV T u (hu ▸ a.ne_zero) (by rw [hu]; simp [vV, hv])
  exact ⟨A, u, hAu, hx, hAc, hu ▸ hc.2.2⟩

theorem exists_integral (hr : 1 ≤ Dw.p + Dw.q) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (y₀ : FrPt Xo c c.F)
    (w : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (ho : OverLa w T.V io e) :
    letI := io.toAlgebra
    ∃ y z : FrPt Xo c T.Fr, Integral T io y ∧ FrMap (Algebra.ofId c.F T.Fr) y₀ z ∧ y.x = z.x := by
  have hB := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hT := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨O, _, β, Y, -, hY, hb⟩ :=
    modelAtSt_of_good GlobalTheory.partI_closed GlobalTheory.Moduli.moduli_scheme_exists E H Dw l Xo c hr hg w
  obtain ⟨b₀, hb₀⟩ := hb T io e ho
  letI := io.toAlgebra
  obtain ⟨z₀, hz₀⟩ :=
    GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c c.F T.Fr (Algebra.ofId c.F T.Fr) y₀
  obtain ⟨y₁, t, hbor⟩ := intFr_of_model (GlobalTheory.intFrames_of_laws hB hT E H Dw l Xo c) T io Y hY b₀ hb₀ z₀
  exact ⟨y₁.1, z₀, y₁.2.2, hz₀, hbor.1⟩

theorem exists_locFr (hr : 1 ≤ Dw.p + Dw.q) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (y₀ : FrPt Xo c c.F)
    (w : HeightOneSpectrum (𝓞 c.F)) : ∃ a B, LocFr y₀ w a B := by
  have hB := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  obtain ⟨T₀, io₀, ho₀, -, hini⟩ := GlobalTheory.PlaceCompletion.exists_initial_completion c.F w
  have hD := denseIn_of_initial w T₀ io₀ hini
  letI := io₀.toAlgebra
  obtain ⟨y₁, z₀, hy₁, hz₀, hx₁⟩ := exists_integral hr hg y₀ w T₀ io₀ 1 ho₀
  obtain ⟨g₁, a₁, hg₁, hc₁⟩ := (frChg_exists_unique E H Dw l Xo c T₀.Fr z₀ y₁).1 hx₁
  choose B Y₁ hB0 hY₁ hBY using fun τ => hD.matrix (g₁ τ)ᵀ (by rw [Matrix.det_transpose]; exact (hg₁ τ).ne_zero)
  obtain ⟨a, u₁, ha, hu₁, hau⟩ := hD.matrix (Matrix.of fun _ _ : Unit => (a₁ : T₀.Fr)) (by simp)
  rw [Matrix.det_unique] at ha hu₁
  have hau' : (a₁ : T₀.Fr) = io₀ (a default default) * algebraMap T₀.V T₀.Fr (u₁ default default) := by
    simpa [Matrix.mul_apply] using congrFun (congrFun hau default) default
  refine ⟨a default default, B, ha, hB0, fun T io e ho => ?_⟩
  obtain ⟨φ, χ, -, hio, hχ, -⟩ := hini T io e ho
  subst hio
  letI := (χ.comp io₀).toAlgebra
  intro y z hy hz hx
  have hχ' : ∀ s, χ (algebraMap T₀.V T₀.Fr s) = algebraMap T.V T.Fr (φ s) := fun s => RingHom.congr_fun hχ s
  let ψ : T₀.Fr →ₐ[c.F] T.Fr := { χ with commutes' := fun _ => rfl }
  obtain ⟨y₂, hy₂⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c T₀.Fr T.Fr ψ y₁
  have hi₂ : Integral T (χ.comp io₀) y₂ :=
    GlobalTheory.PlaceInt.Ext.integral_of_frMap T₀ T io₀ χ φ (fun s => (hχ' s).symm) ψ y₁ y₂ rfl hy₂ hy₁
  obtain ⟨z', hz'⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c T₀.Fr T.Fr ψ z₀
  have hzz : z' = z := by
    have h1 := Formalism.L2.Pj.frMap_trans (Xo := Xo) (c := c) _ _ _ _ ψ y₀ z₀ z' hz₀ hz'
    have h2 : ψ.comp (Algebra.ofId c.F T₀.Fr) = Algebra.ofId c.F T.Fr := Subsingleton.elim _ _
    rw [h2] at h1
    exact (frMap_unique_refl_iff E H Dw l Xo c c.F T.Fr _ y₀).1 _ _ h1 hz
  subst hzz
  have hc₂ := (ChgBC.frChg_baseChange E H Dw l Xo c T₀.Fr T.Fr ψ z₀ y₁ z' y₂ g₁ a₁ hc₁ hz').1 hy₂
  obtain ⟨A, u, hA, hc₃⟩ := frChg_of_integral T (χ.comp io₀) y₂ y hi₂ hy (hx.trans hc₂.1.symm)
  have h4 := (frChg_refl_and_comp E H Dw l Xo c T.Fr z' y₂ y).2 _ _ _ _ hc₂ hc₃
  obtain ⟨u₂, hu₂⟩ := hu₁.map φ
  refine ⟨fun τ => (Y₁ τ).map φ * (A τ)ᵀ, u₂ * u, fun τ => ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((hY₁ τ).map φ).mul (hA τ)
  · convert h4 using 1
    · funext τ
      have e1 : (g₁ τ).map ψ = ((B τ).map (χ.comp io₀) * ((Y₁ τ).map φ).map (algebraMap T.V T.Fr))ᵀ := by
        have e2 : ((g₁ τ)ᵀ).map χ = (B τ).map (χ.comp io₀) * ((Y₁ τ).map φ).map (algebraMap T.V T.Fr) := by
          rw [hBY τ, Matrix.map_mul, Matrix.map_map, Matrix.map_map, Matrix.map_map]
          congr 2
          exact funext hχ'
        rw [← e2]
        rfl
      rw [e1, Matrix.map_mul, ← Matrix.mul_assoc, Matrix.transpose_mul]
      rfl
    · have e3 : ψ a₁ = χ a₁ := rfl
      rw [e3, hau', map_mul χ, hχ', ← hu₂, Units.val_mul, map_mul, RingHom.comp_apply]
      ring

theorem finite_not_locFr_one (hq : Dw.q = 0) (hp : 1 ≤ Dw.p) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (y₀ : FrPt Xo c c.F) :
    {w | ¬ LocFr y₀ w 1 1}.Finite := by
  obtain ⟨S, hS, h⟩ := exists_finset_integral_of_definite E H Dw l Xo c hq hp hg y₀
  refine (S.finite_toSet.biUnion fun s hs => finite_vAdd (hS s hs)).subset fun w hw => ?_
  by_contra hn
  simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at hn
  refine hw ⟨one_ne_zero, fun τ => by simp, fun T io e ho => ?_⟩
  letI := io.toAlgebra
  intro y z hy hz hx
  have hz' := h T io (fun s hs => by
    have h0 : vLa w s = 0 := by exact_mod_cast hn s hs
    rw [ho.2, h0, mul_zero]) z hz
  obtain ⟨A, u, hA, hc⟩ := frChg_of_integral T io z y hz' hy hx
  refine ⟨fun τ => (A τ)ᵀ, u, fun τ => by rw [Matrix.det_transpose]; exact hA τ, ?_⟩
  convert hc using 1
  · funext τ
    simp [Matrix.transpose_map]
  · simp

theorem locFr_unique (hr : 1 ≤ Dw.p + Dw.q) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) {y₀ : FrPt Xo c c.F}
    {w : HeightOneSpectrum (𝓞 c.F)} {a a' : c.F} {B B' : Mats Dw c.F} (h : LocFr y₀ w a B) (h' : LocFr y₀ w a' B') :
    vAdd w a = vAdd w a' ∧ ∀ τ, vAdd w (B τ).det = vAdd w (B' τ).det := by
  obtain ⟨T, io, ho, -, -⟩ := GlobalTheory.PlaceCompletion.exists_initial_completion c.F w
  letI := io.toAlgebra
  obtain ⟨y, z, hy, hz, hx⟩ := exists_integral hr hg y₀ w T io 1 ho
  obtain ⟨Y, u, hY, hc⟩ := h.2.2 T io 1 ho y z hy hz hx
  obtain ⟨Y', u', hY', hc'⟩ := h'.2.2 T io 1 ho y z hy hz hx
  obtain ⟨e1, e2⟩ := (frChg_exists_unique E H Dw l Xo c T.Fr z y).2 _ _ _ _ hc hc'
  have key : ∀ (s : c.F) (v : T.V), s ≠ 0 → IsUnit v → vV T.V (io s * algebraMap T.V T.Fr v) = vAdd w s := by
    intro s v hs hv
    rw [vV_mul ((map_ne_zero io).2 hs) (hv.map _).ne_zero, ho.2]
    simp [vV, valV_algebraMap_unit T hv, vLa, vAdd]
  refine ⟨by rw [← key a u h.1 u.isUnit, e2, key a' u' h'.1 u'.isUnit], fun τ => ?_⟩
  have e3 := congrArg Matrix.det (congrFun e1 τ)
  simp only [Matrix.det_transpose, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at e3
  rw [← key _ _ (h.2.1 τ) (hY τ), e3, key _ _ (h'.2.1 τ) (hY' τ)]

variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {ξ : ℝ}

theorem nonempty_ptData (h : DefCase U ξ) (Z : Comp Xo c) : Nonempty (PtData Z) := by
  have hr : 1 ≤ Dw.p + Dw.q := h.p.trans (Nat.le_add_right _ _)
  obtain ⟨y₀, h1, h2⟩ := DefinitePoint.main E H Dw l Xo c h.q h.geo Z
  have key : ∀ w, ∃ a B, LocFr y₀ w a B ∧ (LocFr y₀ w 1 1 → a = 1 ∧ B = 1) := fun w => by
    by_cases hw : LocFr y₀ w 1 1
    · exact ⟨1, 1, hw, fun _ => ⟨rfl, rfl⟩⟩
    · obtain ⟨a, B, hl⟩ := exists_locFr hr h.good y₀ w
      exact ⟨a, B, hl, fun h' => absurd h' hw⟩
  choose a B hl hl' using key
  choose N X hX using exists_archFr hr y₀
  exact ⟨⟨y₀, h1, h2, a, B, hl, (finite_not_locFr_one h.q h.p h.good y₀).subset fun w hw h' => hw (hl' w h'), N, X, hX⟩⟩

theorem deg_eq (h : DefCase U ξ) {Z : Comp Xo c} (P P' : PtData Z) (e : P.y₀ = P'.y₀) :
    P.degTh = P'.degTh ∧ ∀ τ, P.degLie τ = P'.degLie τ := by
  have hr : 1 ≤ Dw.p + Dw.q := h.p.trans (Nat.le_add_right _ _)
  have a := fun σ => archFr_unique hr (P.arch σ) (e ▸ P'.arch σ)
  have b := fun w => locFr_unique hr h.good (P.loc w) (e ▸ P'.loc w)
  refine ⟨?_, fun τ => ?_⟩
  · simp only [PtData.degTh, fun σ => (a σ).1, fun w => (b w).1]
  · simp only [PtData.degLie, detDeg, fun σ => (a σ).2 τ, fun w => (b w).2 τ]

theorem exists_ptData (p : ℕ) (hp : 1 ≤ p) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
      (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : Comp Xo c), Dw.p = p ∧ Nonempty (PtData Z) := by
  obtain ⟨E, i1, i2, i3, H, D, l, Xo, c, r, U, ξ, e, -, ⟨Z⟩, h⟩ := exists_defCase p hp
  exact ⟨E, i1, i2, i3, H, D, l, Xo, c, Z, e, nonempty_ptData h Z⟩

theorem nonempty_ptData_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ),
    DefCase U ξ → ∀ Z : Comp Xo c, Nonempty (PtData Z) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ h Z => nonempty_ptData h Z

theorem not_locFr_mul (hr : 1 ≤ Dw.p + Dw.q) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) {y₀ : FrPt Xo c c.F}
    {w : HeightOneSpectrum (𝓞 c.F)} {a t : c.F} {B : Mats Dw c.F} (h : LocFr y₀ w a B) (ht : vAdd w t ≠ 0) :
    ¬ LocFr y₀ w (t * a) B := fun h' => by
  have e := (locFr_unique hr hg h h').1
  have h0 : t ≠ 0 := left_ne_zero_of_mul h'.1
  have h1 : w.valuation c.F t ≠ 0 := by simpa using h0
  have h2 : w.valuation c.F a ≠ 0 := by simpa using h.1
  simp only [vAdd, map_mul, WithZero.log_mul h1 h2] at e ht
  omega

theorem tval_eq_of_reads {Z : Comp Xo c} {y₀ : FrPt Xo c c.F} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {x x' : TIdx (part Dw a) → c.F} {f : Rul Xo c} (h : Reads Z y₀ a n x f) (h' : Reads Z y₀ a n x' f)
    (Y : Mats Dw c.F) (hY : ∀ τ, IsUnit (Y τ).det) : tval (part Dw a) x Y = tval (part Dw a) x' Y := by
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c c.F c.F
    (Algebra.ofId _ _) y₀
  obtain ⟨y, hy, -⟩ := existsUnique_frChg E H Dw l Xo c c.F z (fun τ => (Y τ)ᵀ) 1 fun τ => by
    rw [Matrix.det_transpose]; exact hY τ
  have e := (h.2 c.F z y Y 1 hY isUnit_one hz hy).symm.trans (h'.2 c.F z y Y 1 hY isUnit_one hz hy)
  simpa using e

end GlobalTheory.DefPt.Model

end
