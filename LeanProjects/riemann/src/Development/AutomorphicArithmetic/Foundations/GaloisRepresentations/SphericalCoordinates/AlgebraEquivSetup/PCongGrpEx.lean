import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.TrivOfLe

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open GlobalTheory.LFun (KGL satEig)
open GlobalTheory.CongL (SatU)
open GlobalTheory.Cong (Apart)
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.W2.Seed

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private theorem vN_le_one (N : ℕ) (w : Plc E) : Valued.v (N : w.adicCompletion E) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).1 (natCast_mem (w.adicCompletionIntegers E) N)

private theorem vN_ne_zero {N : ℕ} (hN : 0 < N) (w : Plc E) : Valued.v (N : w.adicCompletion E) ≠ 0 := by
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  exact (Valuation.ne_zero_iff _).2 (Nat.cast_ne_zero.2 hN.ne')

private theorem vN_lt_one {N : ℕ} (w : Plc E) (h : (N : 𝓞 E) ∈ w.asIdeal) :
    Valued.v (N : w.adicCompletion E) < 1 := by
  have h1 : Valued.v (algebraMap E (w.adicCompletion E) ((N : 𝓞 E) : E)) = w.valuation E ((N : 𝓞 E) : E) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  have h2 : algebraMap E (w.adicCompletion E) ((N : 𝓞 E) : E) = (N : w.adicCompletion E) := by simp
  rw [← h2, h1]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem w _).2 h

private theorem entry_mul_le {w : Plc E} {A B : Matrix (Fin n) (Fin n) (w.adicCompletion E)}
    {r s : WithZero (Multiplicative ℤ)} (hA : ∀ i j, Valued.v (A i j) ≤ r) (hB : ∀ i j, Valued.v (B i j) ≤ s)
    (i j : Fin n) : Valued.v ((A * B) i j) ≤ r * s := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  exact mul_le_mul' (hA _ _) (hB _ _)

private theorem cong_one (N : ℕ) (w : Plc E) : Cong1 N w (1 : GL (Fin n) (w.adicCompletion E)) := fun i k => by
  simp

private theorem cong_mul {N : ℕ} {w : Plc E} {x y : GL (Fin n) (w.adicCompletion E)}
    (hx : Cong1 N w x) (hy : Cong1 N w y) : Cong1 N w (x * y) := fun i k => by
  have e : (x * y).val - 1 = (x.val - 1) * (y.val - 1) + (x.val - 1) + (y.val - 1) := by
    rw [Units.val_mul]; noncomm_ring
  rw [e, Matrix.add_apply, Matrix.add_apply]
  have h := vN_le_one (E := E) N w
  refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ (hx i k)) (hy i k)
  exact (entry_mul_le hx hy i k).trans (mul_le_of_le_one_left' h)

private theorem cong_conj {N : ℕ} {w : Plc E} {a y : GL (Fin n) (w.adicCompletion E)}
    (ha : a ∈ KGL w n) (hy : Cong1 N w y) : Cong1 N w (a * y * a⁻¹) := fun i k => by
  have e : (a * y * a⁻¹).val - 1 = a.val * (y.val - 1) * (a⁻¹).val := by
    have h : a.val * (a⁻¹).val = 1 := by rw [← Units.val_mul]; simp
    rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, h]
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 ha
  have h1' : ∀ i j, Valued.v (a.val i j) ≤ 1 := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).1 (h1 i j)
  have h2' : ∀ i j, Valued.v ((a⁻¹).val i j) ≤ 1 := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).1 (h2 i j)
  rw [e]
  simpa using entry_mul_le (entry_mul_le h1' hy) h2' i k

private theorem cong_entry {N : ℕ} {w : Plc E} {y : GL (Fin n) (w.adicCompletion E)} (hy : Cong1 N w y) (i j : Fin n) :
    Valued.v (y.val i j) ≤ max (Valued.v (N : w.adicCompletion E)) (Valued.v ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j)) := by
  have e : y.val i j = (y.val - 1) i j + (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j := by simp
  rw [e]
  exact (Valuation.map_add _ _ _).trans (max_le_max_right _ (hy i j))

private theorem cong_int {N : ℕ} {w : Plc E} {y : GL (Fin n) (w.adicCompletion E)} (hy : Cong1 N w y) (i j : Fin n) :
    y.val i j ∈ w.adicCompletionIntegers E := by
  refine (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).2 ((cong_entry hy i j).trans (max_le (vN_le_one N w) ?_))
  by_cases h : i = j
  · subst h; simp
  · rw [Matrix.one_apply_ne h]; simp

private def congGrp (N : ℕ) (w : Plc E) : Subgroup (GL (Fin n) (w.adicCompletion E)) where
  carrier := {y | Cong1 N w y ∧ Cong1 N w y⁻¹}
  one_mem' := ⟨cong_one N w, by simpa using cong_one N w⟩
  mul_mem' := fun {x y} hx hy => ⟨cong_mul hx.1 hy.1, by rw [_root_.mul_inv_rev]; exact cong_mul hy.2 hx.2⟩
  inv_mem' := fun {x} hx => ⟨hx.2, by simpa using hx.1⟩

private theorem mem_congGrp {N : ℕ} {w : Plc E} {y : GL (Fin n) (w.adicCompletion E)} :
    y ∈ congGrp N w ↔ Cong1 N w y ∧ Cong1 N w y⁻¹ := Iff.rfl

private theorem isOpen_ball {w : Plc E} {c : w.adicCompletion E} (hc : c ≠ 0) :
    IsOpen {x : w.adicCompletion E | Valued.v x ≤ Valued.v c} := by
  have h0 : IsOpen ((w.adicCompletionIntegers E : Set (w.adicCompletion E))) :=
    Valued.isOpen_valuationSubring _
  have h1 : {x : w.adicCompletion E | Valued.v x ≤ Valued.v c} =
      (fun x => c⁻¹ * x) ⁻¹' (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
    ext x
    have hv : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).2 hc
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w,
      map_mul, map_inv₀]
    rw [inv_mul_le_iff₀ (zero_lt_iff.2 hv), mul_one]
  rw [h1]
  exact h0.preimage (continuous_const.mul continuous_id)

private theorem isOpen_cong {N : ℕ} (hN : 0 < N) (w : Plc E) :
    IsOpen {y : GL (Fin n) (w.adicCompletion E) | Cong1 N w y} := by
  have hc : (N : w.adicCompletion E) ≠ 0 := fun h => vN_ne_zero hN w (by rw [h, map_zero])
  have e : {y : GL (Fin n) (w.adicCompletion E) | Cong1 N w y} =
      ⋂ i, ⋂ k, (fun y : GL (Fin n) (w.adicCompletion E) => (y.val - 1) i k) ⁻¹'
        {x | Valued.v x ≤ Valued.v (N : w.adicCompletion E)} := by
    ext y
    simp [Cong1]
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => (isOpen_ball hc).preimage ?_
  exact ((Units.continuous_val.sub continuous_const).matrix_elem i k)

private theorem isOpen_congGrp {N : ℕ} (hN : 0 < N) (w : Plc E) :
    IsOpen (congGrp (n := n) N w : Set (GL (Fin n) (w.adicCompletion E))) :=
  (isOpen_cong hN w).inter ((isOpen_cong hN w).preimage continuous_inv)

private theorem congGrp_le (N : ℕ) (w : Plc E) : congGrp (n := n) N w ≤ KGL w n := fun _ hy =>
  GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨cong_int hy.1, cong_int hy.2⟩

private theorem congGrp_le_iw {N : ℕ} (w : Plc E) (hN : (N : 𝓞 E) ∈ w.asIdeal) : congGrp (n := n) N w ≤ Iw n w := by
  intro y hy
  have hK : y ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) := by
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion]
    exact congGrp_le N w hy
  refine GlobalTheory.SmGL.mem_iwahori.2 ⟨hK, fun i j hij => ?_⟩
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [he.lt_one_iff_lt_one]
  have h0 : (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j = 0 := Matrix.one_apply_ne hij.ne'
  refine (cong_entry hy.1 i j).trans_lt (max_lt (vN_lt_one w hN) ?_)
  simp [h0]

theorem pCongGrpEx : CongGrpEx := by
  intro E _ _ _ n N hN w
  refine ⟨congGrp N w, fun y => Iff.rfl, isOpen_congGrp hN w, ?_, congGrp_le N w, ?_, fun h => congGrp_le_iw w h,
    fun y hy => ?_⟩
  · exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2.of_isClosed_subset
      (Subgroup.isClosed_of_isOpen _ (isOpen_congGrp hN w)) (congGrp_le N w)
  · intro a ha y
    have key : ∀ a ∈ KGL w n, ∀ y, y ∈ congGrp N w → a * y * a⁻¹ ∈ congGrp N w := fun a ha y hy =>
      ⟨cong_conj ha hy.1, by
        have : (a * y * a⁻¹)⁻¹ = a * y⁻¹ * a⁻¹ := by group
        rw [this]; exact cong_conj ha hy.2⟩
    refine ⟨fun h => ?_, key a ha y⟩
    have := key a⁻¹ (inv_mem ha) _ h
    simpa [mul_assoc] using this
  · have := GlobalTheory.SmGL.iwahori_le_KO _ _ hy
    rwa [GlobalTheory.SmGL.SphCompletion.KO_completion] at this

end UpperTheory.Gal.W2.Seed
