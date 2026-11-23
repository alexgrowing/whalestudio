import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeGaussianSumOfLengthEqTsumStabilizerCosets
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeStabiliserIsCompactIsOpen
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeVolumeUnitaryGroupEqStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.DefiniteVolume

variable (I : AutInst)

theorem eps_eq {r : ℕ} (h : HasSig I r 0) (v : InfinitePlace I.F) : I.ε v = allPos I.n := by
  funext a
  have h0 := (h v).2
  unfold AutInst.qAt at h0
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  have ha := h0 (Finset.mem_univ a)
  simp only [allPos]
  revert ha
  cases I.ε v a <;> simp

theorem rank_eq {r : ℕ} (h : HasSig I r 0) : r = I.n := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace I.F) := inferInstance
  have hp := (h v).1
  rw [AutInst.pAt, eps_eq I h v] at hp
  simpa [allPos] using hp.symm

theorem card_places : Fintype.card (InfinitePlace I.F) = I.f := by
  haveI := I.cm.totReal
  have h2 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank I.F
  rw [NumberField.IsTotallyReal.nrComplexPlaces_eq_zero] at h2
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, AutInst.f]
  omega

theorem pos_at (v : InfinitePlace I.F) (hv : I.ε v = allPos I.n) (y : Fin I.n → I.E) (hy : y ≠ 0) :
    0 < (I.φ v (star y ⬝ᵥ (I.J *ᵥ y))).re := by
  have hconj : ∀ a, I.φ v (star a) = starRingEnd ℂ (I.φ v a) := fun a => I.cm.cmUnram.2.1 (I.φ v) a
  have hdet : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hspec : (I.P v)ᴴ * I.J.map (I.φ v) * I.P v = 1 := by
    rw [I.P_spec v, hv, GlobalTheory.UnitaryVolume.Jm_allPos]
  have hmap : I.φ v (star y ⬝ᵥ (I.J *ᵥ y)) =
      star (fun i => I.φ v (y i)) ⬝ᵥ (I.J.map (I.φ v) *ᵥ fun i => I.φ v (y i)) := by
    simp only [dotProduct, mulVec, map_sum, map_mul, Pi.star_apply, hconj, Matrix.map_apply,
      starRingEnd_apply]
  have hne : (fun i => I.φ v (y i)) ≠ 0 := by
    intro h0
    apply hy
    funext i
    exact (I.φ v).injective (by simpa using congrFun h0 i)
  rw [hmap]
  generalize (fun i => I.φ v (y i)) = w at hne ⊢
  have hwz : w = I.P v *ᵥ ((I.P v)⁻¹ *ᵥ w) := by
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, one_mulVec]
  have hz0 : (I.P v)⁻¹ *ᵥ w ≠ 0 := by
    intro h0
    apply hne
    rw [hwz, h0, mulVec_zero]
  rw [hwz, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hspec, one_mulVec]
  exact (Complex.pos_iff.1 (Matrix.dotProduct_star_self_pos_iff.2 hz0)).1

theorem pos_all {r : ℕ} (h : HasSig I r 0) (φ : I.E →+* ℂ) (y : Fin I.n → I.E) (hy : y ≠ 0) :
    0 < (φ (star y ⬝ᵥ (I.J *ᵥ y))).re := by
  have hJ : I.Jᴴ = I.J := by rw [← GlobalTheory.StabCosets.cT_star]; exact I.J_herm
  have hstar : star (star y ⬝ᵥ (I.J *ᵥ y)) = star y ⬝ᵥ (I.J *ᵥ y) := by
    rw [← star_dotProduct_star, star_star, star_mulVec, ← dotProduct_mulVec, hJ]
  obtain ⟨b, hb⟩ := (I.cm.fixed _).1 hstar
  haveI := I.cm.totReal
  have hreal : (InfinitePlace.mk (φ.comp (algebraMap I.F I.E))).IsReal :=
    NumberField.IsTotallyReal.isReal _
  have hemb := NumberField.InfinitePlace.embedding_mk_eq_of_isReal
    (NumberField.InfinitePlace.isReal_mk_iff.1 hreal)
  have hval : φ (star y ⬝ᵥ (I.J *ᵥ y)) =
      I.φ (InfinitePlace.mk (φ.comp (algebraMap I.F I.E))) (star y ⬝ᵥ (I.J *ᵥ y)) := by
    rw [← hb, I.φ_over, hemb]
    rfl
  rw [hval]
  exact pos_at I _ (eps_eq I h _) y hy

theorem hform_eq (z x : Fin I.n → I.E) :
    Formalism.UG.hform (starRingEnd I.E) I.J z x = star z ⬝ᵥ (I.J *ᵥ x) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, starRingEnd_apply, Pi.star_apply,
    mul_assoc]

abbrev DefLat (E : Type) [Field E] [NumberField E] [StarRing E] (r : ℕ) : Type :=
  {X : Matrix (Fin r) (Fin r) E × Submodule (𝓞 E) (Fin r → E) //
      X.1ᴴ = X.1 ∧ (∀ (φ : E →+* ℂ) (y : Fin r → E), y ≠ 0 → 0 < (φ (star y ⬝ᵥ (X.1 *ᵥ y))).re) ∧
      Submodule.IsLattice E X.2 ∧
      ∀ x, x ∈ X.2 ↔ ∀ y ∈ X.2, star y ⬝ᵥ (X.1 *ᵥ x) ∈ (algebraMap (𝓞 E) E).range}

abbrev Isom (E : Type) [Field E] [NumberField E] [StarRing E] (r : ℕ) (X Y : DefLat E r) : Prop :=
  ∃ γ : GL (Fin r) E, (γ : Matrix (Fin r) (Fin r) E)ᴴ * Y.1.1 * (γ : Matrix (Fin r) (Fin r) E) = X.1.1 ∧
      ∀ y, (γ : Matrix (Fin r) (Fin r) E) *ᵥ y ∈ Y.1.2 ↔ y ∈ X.1.2

theorem isom_equivalence (E : Type) [Field E] [NumberField E] [StarRing E] (r : ℕ) :
    Equivalence (Isom E r) where
  refl X := ⟨1, by simp, fun y => by simp⟩
  symm := by
    rintro X Y ⟨γ, h1, h2⟩
    refine ⟨γ⁻¹, ?_, fun y => ?_⟩
    · have hu : (γ : Matrix (Fin r) (Fin r) E) * ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = 1 := by
        simp
      calc ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)ᴴ * X.1.1 *
            ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)
          = ((γ : Matrix (Fin r) (Fin r) E) * ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E))ᴴ * Y.1.1 *
              ((γ : Matrix (Fin r) (Fin r) E) * ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)) := by
            rw [← h1, conjTranspose_mul]
            simp only [Matrix.mul_assoc]
        _ = Y.1.1 := by rw [hu]; simp
    · have h3 := h2 (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ y)
      rw [mulVec_mulVec, Units.mul_inv, one_mulVec] at h3
      exact h3.symm
  trans := by
    rintro X Y Z ⟨γ, h1, h2⟩ ⟨δ, h3, h4⟩
    refine ⟨δ * γ, ?_, fun y => ?_⟩
    · rw [Units.val_mul, conjTranspose_mul, ← h1, ← h3]
      simp only [Matrix.mul_assoc]
    · rw [Units.val_mul, ← mulVec_mulVec, h4, h2]

def latOf {r : ℕ} (h : HasSig I r 0) (x : I.GA) : DefLat I.E I.n :=
  ⟨(I.J, lamX I x), by rw [← GlobalTheory.StabCosets.cT_star]; exact I.J_herm, pos_all I h,
    ⟨(GlobalTheory.PointLattice.lamX_selfDual I x).2.1, (GlobalTheory.PointLattice.lamX_selfDual I x).2.2.1⟩,
    fun y => by
      simpa only [hform_eq] using (GlobalTheory.PointLattice.lamX_selfDual I x).2.2.2.1 y⟩

theorem coset_of_isom {r : ℕ} (h : HasSig I r 0) (x y : I.GA)
    (e : Isom I.E I.n (latOf I h y) (latOf I h x)) :
    ∃ a ∈ I.GFset, x.2⁻¹ * (a * y).2 ∈ I.Kset := by
  obtain ⟨γ, h1, h2⟩ := e
  change (γ : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ * I.J * γ = I.J at h1
  change ∀ z, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z ∈ lamX I x ↔ z ∈ lamX I y at h2
  have hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J := by
    show Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E) * I.J * γ = I.J
    rw [GlobalTheory.StabCosets.cT_star]
    exact h1
  obtain ⟨a, ha1, ha2⟩ := GlobalTheory.StabCosets.exists_isImage I γ hγ
  refine ⟨a, ⟨γ, hγ, ha1, ha2⟩, ?_⟩
  have hl : lamX I (a * y) = lamX I x := by
    rw [(GlobalTheory.PointEquivariance.equivariance I y γ a hγ ha1 ha2).1]
    ext z
    simp only [Submodule.mem_map, LinearMap.restrictScalars_apply, Matrix.toLin'_apply]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (h2 u).2 hu
    · intro hz
      refine ⟨((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z, (h2 _).1 ?_, ?_⟩
      · rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
        exact hz
      · rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
  exact (GlobalTheory.PointEquivariance.lamX_mul_eq_iff I x (x⁻¹ * (a * y))).2 (by rw [mul_inv_cancel_left]; exact hl)

theorem covol_le {r : ℕ} (h : HasSig I r 0) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
    [Fintype (Quot (Isom I.E I.n))] :
    covol I.GFset (I.muA μf) Set.univ ≤
      (∏ v, Formalism.REAL.muG (I.ε v) Set.univ) * (Fintype.card (Quot (Isom I.E I.n)) * μf I.Kset) := by
  classical
  let pt : Quot (Isom I.E I.n) → I.GA := fun q =>
    if hq : ∃ x, Quot.mk (Isom I.E I.n) (latOf I h x) = q then hq.choose else 1
  let D : Quot (Isom I.E I.n) → Set I.GA := fun q =>
    Set.univ ×ˢ ((fun g => (pt q).2⁻¹ * g) ⁻¹' I.Kset)
  have hKo : IsOpen I.Kset := (GlobalTheory.adelicStab_isCompact_isOpen I).2.1
  have hDm : ∀ q, MeasurableSet (D q) := fun q =>
    MeasurableSet.univ.prod (hKo.preimage (continuous_const.mul continuous_id)).measurableSet
  have hcover : ∀ z ∈ (Set.univ : Set I.GA), ∃ γ ∈ I.GFset, γ * z ∈ ⋃ q, D q := by
    intro z _
    have hq : ∃ x, Quot.mk (Isom I.E I.n) (latOf I h x) = Quot.mk (Isom I.E I.n) (latOf I h z) :=
      ⟨z, rfl⟩
    have hpt : pt (Quot.mk (Isom I.E I.n) (latOf I h z)) = hq.choose := dif_pos hq
    have e : Isom I.E I.n (latOf I h z) (latOf I h hq.choose) :=
      (isom_equivalence I.E I.n).symm
        ((Equivalence.eqvGen_iff (isom_equivalence I.E I.n)).1 (Quot.eqvGen_exact hq.choose_spec))
    obtain ⟨a, ha, hk⟩ := coset_of_isom I h hq.choose z e
    refine ⟨a, ha, Set.mem_iUnion.2 ⟨Quot.mk (Isom I.E I.n) (latOf I h z), Set.mem_univ _, ?_⟩⟩
    show (pt (Quot.mk (Isom I.E I.n) (latOf I h z))).2⁻¹ * (a * z).2 ∈ I.Kset
    rw [hpt]
    exact hk
  calc covol I.GFset (I.muA μf) Set.univ ≤ I.muA μf (⋃ q, D q) := by
        unfold covol
        exact iInf_le_of_le _ (iInf_le_of_le (MeasurableSet.iUnion hDm) (iInf_le_of_le hcover le_rfl))
    _ ≤ ∑ q, I.muA μf (D q) := measure_iUnion_fintype_le _ _
    _ = ∑ _q : Quot (Isom I.E I.n), (∏ v, Formalism.REAL.muG (I.ε v) Set.univ) * μf I.Kset := by
        refine Finset.sum_congr rfl fun q _ => ?_
        simp only [D, AutInst.muA]
        rw [Measure.prod_prod, Measure.pi_univ, measure_preimage_mul]
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

theorem volU_pos (i : ℕ) : 0 < volU i := by
  unfold volU sphV
  exact mul_pos (Finset.prod_pos fun l _ => by positivity) (by positivity)

theorem gauge_local (N : ℕ) (ε : Fin N → Bool) (hε : ε = allPos N) (c : ℝ) (hc : IsGauge ε c) :
    0 ≤ c ∧ ENNReal.ofReal c * Formalism.REAL.muG ε Set.univ = ENNReal.ofReal (volU N) := by
  subst hε
  have h1 := GlobalTheory.T.riemannianHaarGauge_volume_unitaryGroup_eq N c hc
  have hlt := GlobalTheory.UnitaryVolume.muG_univ_lt_top N
  have hne := GlobalTheory.UnitaryVolume.muG_univ_ne_zero N
  have ht : 0 < (Formalism.REAL.muG (allPos N) Set.univ).toReal := ENNReal.toReal_pos hne hlt.ne
  have hc0 : 0 < c := by
    by_contra hle
    push_neg at hle
    nlinarith [volU_pos N]
  refine ⟨hc0.le, ?_⟩
  rw [← ENNReal.ofReal_toReal hlt.ne, ← ENNReal.ofReal_mul hc0.le, h1]

theorem gaugeVol_le : ∀ (I : AutInst) (r : ℕ), HasSig I r 0 → ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure], IsGaugeAll I c → gaugeVol I c μf ≤ ENNReal.ofReal (volU r ^ I.f) * ((defClassNum I.E r : ENat) : ENNReal) := by
  intro I r h c μf _ _ hc
  obtain rfl := rank_eq I h
  have hK := GlobalTheory.adelicStab_isCompact_isOpen I
  have h1K : (1 : I.Gf) ∈ I.Kset :=
    (GlobalTheory.PointEquivariance.lamX_mul_eq_iff I 1 1).2 (by rw [mul_one])
  have hKpos : μf I.Kset ≠ 0 := (hK.2.1.measure_pos μf ⟨1, h1K⟩).ne'
  have hKtop : μf I.Kset ≠ ⊤ := hK.1.measure_lt_top.ne
  have hloc : ∀ v, 0 ≤ c v ∧
      ENNReal.ofReal (c v) * Formalism.REAL.muG (I.ε v) Set.univ = ENNReal.ofReal (volU I.n) :=
    fun v => gauge_local I.n (I.ε v) (eps_eq I h v) (c v) (hc v)
  have hV : ENNReal.ofReal (volU I.n ^ I.f) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (pow_pos (volU_pos _) _)).ne'
  have hprod : ENNReal.ofReal (∏ v, c v) * ∏ v, Formalism.REAL.muG (I.ε v) Set.univ =
      ENNReal.ofReal (volU I.n ^ I.f) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun v _ => (hloc v).1), ← Finset.prod_mul_distrib,
      Finset.prod_congr rfl (fun v _ => (hloc v).2), Finset.prod_const, Finset.card_univ, card_places,
      ENNReal.ofReal_pow (volU_pos _).le]
  by_cases hfin : Finite (Quot (Isom I.E I.n))
  · haveI := Fintype.ofFinite (Quot (Isom I.E I.n))
    have hcv := covol_le I h μf
    unfold gaugeVol
    calc ENNReal.ofReal (∏ v, c v) * covol I.GFset (I.muA μf) Set.univ / μf I.Kset
        ≤ ENNReal.ofReal (∏ v, c v) * ((∏ v, Formalism.REAL.muG (I.ε v) Set.univ) *
            ((Fintype.card (Quot (Isom I.E I.n)) : ENNReal) * μf I.Kset)) / μf I.Kset := by
          gcongr
      _ = ENNReal.ofReal (volU I.n ^ I.f) * (Fintype.card (Quot (Isom I.E I.n)) : ENNReal) := by
          rw [← mul_assoc, hprod, ← mul_assoc, ENNReal.mul_div_cancel_right hKpos hKtop]
      _ = ENNReal.ofReal (volU I.n ^ I.f) * ((defClassNum I.E I.n : ENat) : ENNReal) := by
          rw [defClassNum, ENat.card_eq_coe_fintype_card, ENat.toENNReal_coe]
  · haveI := not_finite_iff_infinite.1 hfin
    rw [defClassNum, ENat.card_eq_top_of_infinite, ENat.toENNReal_top, ENNReal.mul_top hV]
    exact le_top

end GlobalTheory.DefiniteVolume
