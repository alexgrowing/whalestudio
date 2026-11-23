import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreRelLift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace FibreRelLift

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (ℓ : ℕ)

def ratio (p : Σ k, ι k) : chartRingZ y c :=
  ⟨y p / y ⟨p.1, c p.1⟩, Algebra.subset_adjoin ⟨p, rfl⟩⟩

def dehom : MRing ι →ₐ[ℤ] chartRingZ y c := aeval (ratio y c)

theorem coe_dehom (f : MRing ι) :
    ((dehom y c f : chartRingZ y c) : Ω) = aeval (fun k => (y ⟨k, c k⟩)⁻¹) (mConeMap y f) := by
  show ((chartRingZ y c).val.toRingHom.comp (dehom y c).toRingHom) f =
    ((aeval (fun k => (y ⟨k, c k⟩)⁻¹) : MvPolynomial K Ω →ₐ[Ω] Ω).toRingHom.comp (mConeMap y).toRingHom) f
  refine RingHom.congr_fun (MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)) f
  · simp
  · simp [dehom, ratio, mConeMap, div_eq_mul_inv]

theorem coe_dehom_of_homog {f : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d) :
    ((dehom y c f : chartRingZ y c) : Ω) = aeval y f * ∏ k, (y ⟨k, c k⟩)⁻¹ ^ d k := by
  rw [coe_dehom, ProjLine.mConeMap_eq_of_isMultiHomog y hf, map_mul, aeval_C, map_prod]
  simp only [map_pow, aeval_X, Algebra.algebraMap_self, RingHom.id_apply]

theorem dehom_eq_zero {f : MRing ι} (hf : f ∈ mCoordIdeal y) : dehom y c f = 0 := by
  have h0 : mConeMap y f = 0 := RingHom.mem_ker.mp hf
  apply Subtype.ext
  rw [coe_dehom, h0]
  simp

abbrev ChartQ := chartRingZ y c ⧸ Ideal.span {((ℓ : ℕ) : chartRingZ y c)}

theorem natCast_chartQ : ((ℓ : ℕ) : ChartQ y c ℓ) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : chartRingZ y c)})) ℓ]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

def dehomMod : MRingOver (ZMod ℓ) ι →+* ChartQ y c ℓ :=
  eval₂Hom (ZMod.castHom (ringChar.dvd (natCast_chartQ y c ℓ)) (ChartQ y c ℓ))
    (fun p => Ideal.Quotient.mk _ (ratio y c p))

theorem dehomMod_map (f : MRing ι) :
    dehomMod y c ℓ (MvPolynomial.map (Int.castRingHom (ZMod ℓ)) f) =
      Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : chartRingZ y c)}) (dehom y c f) := by
  show ((dehomMod y c ℓ).comp (MvPolynomial.map (Int.castRingHom (ZMod ℓ)))) f =
    ((Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : chartRingZ y c)})).comp (dehom y c).toRingHom) f
  refine RingHom.congr_fun (MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)) f
  · simp [dehomMod]
  · simp [dehomMod, dehom]

theorem idealOver_le_ker : GenOnFibres.idealOver y (ZMod ℓ) ≤ RingHom.ker (dehomMod y c ℓ) := by
  refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
  rw [Ideal.mem_comap, RingHom.mem_ker, dehomMod_map, dehom_eq_zero y c hf, map_zero]

def dehomQuot : MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ) →+* ChartQ y c ℓ :=
  Ideal.Quotient.lift _ (dehomMod y c ℓ) fun _ hf => RingHom.mem_ker.mp (idealOver_le_ker y c ℓ hf)

theorem dehomQuot_smul (r : MRingOver (ZMod ℓ) ι) (m : MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ)) :
    dehomQuot y c ℓ (r • m) = dehomMod y c ℓ r * dehomQuot y c ℓ m := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [GenOnFibres.smul_mk, dehomQuot, Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk, map_mul]

theorem dehomMod_cellMon (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {I : ∀ k, Finset (ι k)} (hI : ∀ k, ∀ i ∈ I k, i = c k)
    {t : MRingOver (ZMod ℓ) ι} (ht : t ∈ KH.cellMon (ZMod ℓ) I) : dehomMod y c ℓ t = 1 := by
  have hle : KH.cellMon (ZMod ℓ) I ≤ (⊥ : Submonoid (ChartQ y c ℓ)).comap (dehomMod y c ℓ).toMonoidHom := by
    unfold KH.cellMon
    refine Submonoid.closure_le.mpr ?_
    rintro f ⟨k, i, hi, rfl⟩
    obtain rfl := hI k i hi
    have h1 : ratio y c ⟨k, c k⟩ = 1 := Subtype.ext (by simp [ratio, div_self (hc k)])
    rw [SetLike.mem_coe, Submonoid.mem_comap, Submonoid.mem_bot]
    simp [dehomMod, h1]
  exact Submonoid.mem_bot.mp (hle ht)

variable {y c ℓ}

def dehomLocFun (T : Submonoid (MRingOver (ZMod ℓ) ι)) (hT : ∀ t ∈ T, dehomMod y c ℓ t = 1)
    (x : LocalizedModule T (MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ))) : ChartQ y c ℓ :=
  x.liftOn (fun p => dehomQuot y c ℓ p.1) (by
    rintro ⟨m, s⟩ ⟨m', s'⟩ ⟨u, hu⟩
    have h := congrArg (dehomQuot y c ℓ) hu
    simp only [Submonoid.smul_def, dehomQuot_smul, hT _ u.2, hT _ s.2, hT _ s'.2, one_mul] at h
    exact h)

theorem dehomLocFun_mk (T : Submonoid (MRingOver (ZMod ℓ) ι)) (hT : ∀ t ∈ T, dehomMod y c ℓ t = 1)
    (m : MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ)) (t : T) :
    dehomLocFun T hT (LocalizedModule.mk m t) = dehomQuot y c ℓ m := by
  unfold dehomLocFun
  rw [LocalizedModule.liftOn_mk]

def dehomLoc (T : Submonoid (MRingOver (ZMod ℓ) ι)) (hT : ∀ t ∈ T, dehomMod y c ℓ t = 1) :
    LocalizedModule T (MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ)) →+* ChartQ y c ℓ where
  toFun := dehomLocFun T hT
  map_one' := by
    rw [show (1 : LocalizedModule T (MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ))) =
      LocalizedModule.mk 1 1 by rw [OreLocalization.one_def], dehomLocFun_mk, map_one]
  map_mul' x x' := by
    induction x, x' using LocalizedModule.induction_on₂ with
    | h m m' s s' =>
      rw [LocalizedModule.mk_mul_mk, dehomLocFun_mk, dehomLocFun_mk, dehomLocFun_mk, map_mul]
  map_zero' := by
    rw [← LocalizedModule.zero_mk 1, dehomLocFun_mk, map_zero]
  map_add' x x' := by
    induction x, x' using LocalizedModule.induction_on₂ with
    | h m m' s s' =>
      rw [LocalizedModule.mk_add_mk, dehomLocFun_mk, dehomLocFun_mk, dehomLocFun_mk, map_add,
        Submonoid.smul_def, Submonoid.smul_def, dehomQuot_smul, dehomQuot_smul, hT _ s.2, hT _ s'.2,
        one_mul, one_mul]

theorem dehomLoc_mk (T : Submonoid (MRingOver (ZMod ℓ) ι)) (hT : ∀ t ∈ T, dehomMod y c ℓ t = 1)
    (m : MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ)) (t : T) :
    dehomLoc T hT (LocalizedModule.mk m t) = dehomQuot y c ℓ m :=
  dehomLocFun_mk T hT m t

end FibreRelLift

open FibreRelLift in

theorem FibreRelLift.proof : FibreRelLift.Statement := by
  intro K _ _ ι _ _ Ω _ y ℓ a r s J u hs hc _ hrel
  set c := GenOnFibres.cellChart J with hcdef
  have hI : ∀ k, ∀ i ∈ J.1 k, i = c k := by
    intro k i hi
    have h1 : (J.1 k).card - 1 = 0 := (Finset.sum_eq_zero_iff.mp J.2.2) k (Finset.mem_univ k)
    exact Finset.card_le_one.mp (by omega) i hi (c k) (GenOnFibres.cellChart_mem J k)
  have hT : ∀ t ∈ KH.cellMon (ZMod ℓ) J.1, dehomMod y c ℓ t = 1 := fun t ht =>
    dehomMod_cellMon y c ℓ hc hI ht
  have hw : ∀ j, s j * ∏ k, y ⟨k, c k⟩ ^ (-a k) ∈ chartRingZ y c := fun j => by
    simpa using hs j c hc
  have hz : ∀ j, dehomLoc _ hT (GenOnFibres.secCoch y (ZMod ℓ) (s j) a J) =
      Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : chartRingZ y c)}) ⟨_, hw j⟩ := by
    intro j
    obtain ⟨e, F, ⟨d, hF, hd, hv⟩, h, he⟩ := GenOnFibres.secCoch_spec (S := ZMod ℓ) (hs j) J hc
    rw [he, dehomLoc_mk, dehomQuot, Ideal.Quotient.lift_mk, dehomMod_map]
    congr 1
    apply Subtype.ext
    rw [coe_dehom_of_homog y c hF, hv, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ (hc k)]
    congr 1
    have := hd k
    omega
  have h1 := congrArg (dehomLoc _ hT) hrel
  rw [map_sum, map_one] at h1
  simp only [map_mul, hz] at h1
  choose b hb using fun j => Ideal.Quotient.mk_surjective (dehomLoc _ hT (u j))
  simp only [← hb, ← map_mul, ← map_sum] at h1
  rw [← map_one (Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : chartRingZ y c)})), Ideal.Quotient.eq,
    Ideal.mem_span_singleton'] at h1
  obtain ⟨q, hq⟩ := h1
  refine ⟨fun j => (b j : Ω), -(q : Ω), fun j => (b j).2, neg_mem q.2, ?_⟩
  have h2 := congrArg (fun x : chartRingZ y c => (x : Ω)) hq
  push_cast at h2
  linear_combination (-1 : Ω) * h2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
