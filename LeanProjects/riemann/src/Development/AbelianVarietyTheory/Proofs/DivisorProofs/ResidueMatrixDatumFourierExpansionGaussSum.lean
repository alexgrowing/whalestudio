import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixGaussSumSingularAndInvertible
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.ResidueFourier

section Local

variable {k : Type} [Field k] [Fintype k]

theorem sum_char_trace {n r : ℕ} {ψ : AddChar k ℂ} (hψ : ψ.IsPrimitive) (w : Matrix (Fin n) (Fin r) k) :
    ∑ x : Matrix (Fin r) (Fin n) k, ψ (Matrix.trace (x * w)) =
      if w = 0 then ((Nat.card k : ℂ) ^ (n * r)) else 0 := by
  let L : Matrix (Fin r) (Fin n) k →+ k :=
    AddMonoidHom.mk' (fun x => Matrix.trace (x * w)) (fun a b => by rw [Matrix.add_mul, Matrix.trace_add])
  have h := AddChar.sum_eq_ite (ψ.compAddMonoidHom L)
  have h2 : ψ.compAddMonoidHom L = 0 ↔ w = 0 := by
    constructor
    · intro h0
      ext i j
      by_contra hne
      refine hψ hne ?_
      ext t
      have := DFunLike.congr_fun h0 (Matrix.single j i t)
      change ψ (Matrix.trace (Matrix.single j i t * w)) = 1 at this
      rw [Matrix.trace_single_mul, smul_eq_mul] at this
      rw [AddChar.mulShift_apply, mul_comm]
      exact this
    · rintro rfl
      ext x
      change ψ (Matrix.trace (x * (0 : Matrix (Fin n) (Fin r) k))) = 1
      simp
  refine Eq.trans h ?_
  by_cases hw : w = 0
  · rw [if_pos (h2.2 hw), if_pos hw, Nat.card_eq_fintype_card]
    have : Fintype.card (Matrix (Fin r) (Fin n) k) = Fintype.card k ^ (n * r) := by
      change Fintype.card (Fin r → Fin n → k) = _
      simp [pow_mul]
    rw [this]; push_cast; rfl
  · rw [if_neg (fun h => hw (h2.1 h)), if_neg hw]

theorem inversion {n r : ℕ} {ψ : AddChar k ℂ} (hψ : ψ.IsPrimitive) (f : Matrix (Fin n) (Fin r) k → ℂ)
    (u : Matrix (Fin n) (Fin r) k) :
    f u = ∑ x : Matrix (Fin r) (Fin n) k,
      (((Nat.card k : ℂ) ^ (n * r))⁻¹ * ∑ v, f v * ψ (Matrix.trace (-x * v))) * ψ (Matrix.trace (x * u)) := by
  have hc : ((Nat.card k : ℂ) ^ (n * r)) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  have h1 : ∀ x : Matrix (Fin r) (Fin n) k,
      (((Nat.card k : ℂ) ^ (n * r))⁻¹ * ∑ v, f v * ψ (Matrix.trace (-x * v))) * ψ (Matrix.trace (x * u)) =
      ∑ v, ((Nat.card k : ℂ) ^ (n * r))⁻¹ * f v * ψ (Matrix.trace (x * (u - v))) := fun x => by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [mul_assoc, mul_assoc, mul_assoc, ← AddChar.map_add_eq_mul, ← Matrix.trace_add, Matrix.mul_sub, Matrix.neg_mul,
      neg_add_eq_sub]
  simp only [h1]
  rw [Finset.sum_comm, Finset.sum_eq_single u]
  · rw [← Finset.mul_sum, sum_char_trace hψ, if_pos (sub_self u)]
    field_simp
  · intro v _ hv
    rw [← Finset.mul_sum, sum_char_trace hψ, if_neg (fun h => hv (sub_eq_zero.1 h).symm), mul_zero]
  · simp

def embTop (n : ℕ) {r : ℕ} (g : Matrix (Fin r) (Fin r) k) : Matrix (Fin n) (Fin r) k :=
  fun i j => if h : i.val < r then g ⟨i.val, h⟩ j else 0

omit [Fintype k] in
theorem topL_embTop {n r : ℕ} (h : r ≤ n) (g : Matrix (Fin r) (Fin r) k) : topL r (embTop n g) = g := by
  ext i j
  have : i.val < n := lt_of_lt_of_le i.2 h
  simp [topL, embTop, this]

omit [Fintype k] in
theorem lowZero_embTop {n r : ℕ} (g : Matrix (Fin r) (Fin r) k) : LowZero r (embTop n g) := by
  intro i j hi _
  simp [embTop, not_lt.2 hi]

omit [Fintype k] in
theorem embTop_topL {n r : ℕ} {u : Matrix (Fin n) (Fin r) k} (hu : LowZero r u) : embTop n (topL r u) = u := by
  ext i j
  by_cases hi : i.val < r
  · simp [topL, embTop, hi]
  · simp [embTop, hi, hu i j (not_lt.1 hi) j.2]

omit [Fintype k] in
theorem trace_embTop {n r : ℕ} (h : r ≤ n) (x : Matrix (Fin r) (Fin n) k) (g : Matrix (Fin r) (Fin r) k) :
    Matrix.trace (x * embTop n g) = Matrix.trace (topL r x * g) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.sum_univ_add]
  have h2 : ∀ i : Fin r, i.val < r + t := fun i => lt_of_lt_of_le i.2 h
  simp [embTop, topL, h2]
  rfl

theorem transform {n r : ℕ} (h : r ≤ n) {ψ : AddChar k ℂ} (hψ : ψ.IsPrimitive) {ξ : kˣ →* ℂˣ} (hξ : ξ ≠ 1)
    (x : Matrix (Fin r) (Fin n) k) :
    ∑ v : Matrix (Fin n) (Fin r) k,
      (if h : LowZero r v ∧ IsUnit (topL r v).det then ((ξ h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0) * ψ (Matrix.trace (x * v)) =
      (∑ g : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) *
        ψ (Matrix.trace (g : Matrix (Fin r) (Fin r) k))) *
      (if h : IsUnit (topL r x).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) := by
  obtain ⟨h0, h1⟩ := GlobalTheory.matrixGaussSum_singular_and_invertible k ℂ ψ ξ r hψ hξ
  have step : ∑ v : Matrix (Fin n) (Fin r) k,
      (if h : LowZero r v ∧ IsUnit (topL r v).det then ((ξ h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0) * ψ (Matrix.trace (x * v)) =
      ∑ g : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) *
        ψ (Matrix.trace (topL r x * (g : Matrix (Fin r) (Fin r) k))) := by
    symm
    apply Finset.sum_of_injOn (fun g : GL (Fin r) k => embTop n (g : Matrix (Fin r) (Fin r) k))
    · intro a _ b _ hab
      have := congrArg (topL r) hab
      simp only [topL_embTop h] at this
      exact Units.ext this
    · intro a _
      simp
    · intro u _ hu
      rw [dif_neg, zero_mul]
      rintro ⟨hl, hd⟩
      exact hu ⟨((Matrix.isUnit_iff_isUnit_det _).2 hd).unit, by simp, embTop_topL hl⟩
    · intro g _
      have hx : IsUnit (topL r (embTop n (g : Matrix (Fin r) (Fin r) k))).det := by
        rw [topL_embTop h]; exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
      have hdet : hx.unit = Matrix.GeneralLinearGroup.det g := Units.ext (by simp [topL_embTop h])
      rw [dif_pos ⟨lowZero_embTop _, hx⟩, trace_embTop h, hdet, zpow_neg_one, Units.val_inv_eq_inv_val]
  rw [step]
  by_cases hy : IsUnit (topL r x).det
  · have hm := (Matrix.isUnit_iff_isUnit_det _).2 hy
    have hdet : Matrix.GeneralLinearGroup.det (hm.unit : GL (Fin r) k) = hy.unit :=
      Units.ext (by simp [Matrix.GeneralLinearGroup.det])
    have key := h1 hm.unit
    rw [hdet] at key
    simp only [IsUnit.unit_spec, one_mul] at key
    rw [key, dif_pos hy, mul_comm]
  · have hz : (topL r x).det = 0 := by simpa using hy
    rw [h0 _ hz, dif_neg hy, mul_zero]

end Local

theorem dite_prod {ι : Type} (Q : Finset ι) (p : ι → Prop) (f : ∀ i, p i → ℂ) :
    (if h : ∀ i ∈ Q, p i then ∏ i ∈ Q.attach, f i.1 (h i.1 i.2) else 0) =
      ∏ i ∈ Q.attach, if h : p i.1 then f i.1 h else 0 := by
  split_ifs with h
  · exact Finset.prod_congr rfl fun i _ => (dif_pos (h i.1 i.2)).symm
  · push_neg at h
    obtain ⟨i, hi, hp⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_attach Q ⟨i, hi⟩) (dif_neg hp)).symm

theorem omegaQ_fourier : ∀ (D : D7) [∀ PP : Pl D.host.E, Fintype (kP PP)] (Q : Finset (Pl D.host.E)) (n r : ℕ), r ≤ n → ∀ (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), (∀ PP ∈ Q, (ψP PP).IsPrimitive) → (∀ PP ∈ Q, ξ PP ≠ 1) → ∃ c : (∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)) → ℂ, (∀ u : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP), omegaQ Q r ξ (-1) u = ∑ x, c x * ∏ PP ∈ Q.attach, ψP PP.1 (Matrix.trace (x PP * u PP.1))) ∧ ∀ (x : ∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)) (y : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin n) (kP PP)), (∀ PP : ↥Q, y PP.1 = x PP) → c (-x) = (∏ PP ∈ Q.attach, ((Nat.card (kP PP.1) : ℂ) ^ (n * r))⁻¹ * ∑ g : GL (Fin r) (kP PP.1), (((ξ PP.1 (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) * ψP PP.1 (Matrix.trace (g : Matrix (Fin r) (Fin r) (kP PP.1)))) * omegaFlat Q r ξ y := by
  intro D _ Q n r hrn ψP ξ hψ hξ
  let f : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP) → ℂ := fun PP v =>
    if h : LowZero r v ∧ IsUnit (topL r v).det then ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0
  let c : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin n) (kP PP) → ℂ := fun PP x =>
    ((Nat.card (kP PP) : ℂ) ^ (n * r))⁻¹ * ∑ v, f PP v * ψP PP (Matrix.trace (-x * v))
  refine ⟨fun x => ∏ PP ∈ Q.attach, c PP.1 (x PP), fun u => ?_, fun x y hxy => ?_⟩
  · have h1 : omegaQ Q r ξ (-1) u = ∏ PP ∈ Q.attach, f PP.1 (u PP.1) := by
      unfold omegaQ
      convert dite_prod Q (fun PP => LowZero r (u PP) ∧ IsUnit (topL r (u PP)).det)
        (fun PP h => ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ))
    have h2 : ∀ PP : ↥Q, f PP.1 (u PP.1) = ∑ x, c PP.1 x * ψP PP.1 (Matrix.trace (x * u PP.1)) := fun PP => by
      letI := Ideal.Quotient.field PP.1.asIdeal
      exact inversion (k := kP PP.1) (hψ PP.1 PP.2) (f PP.1) (u PP.1)
    rw [h1]
    simp only [h2, ← Finset.prod_mul_distrib, Finset.attach_eq_univ]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  · have h1 : omegaFlat Q r ξ y = ∏ PP ∈ Q.attach, if h : IsUnit (topL r (y PP.1)).det then ((ξ PP.1 h.unit : ℂˣ) : ℂ) else 0 := by
      unfold omegaFlat
      convert dite_prod Q (fun PP => IsUnit (topL r (y PP)).det) (fun PP h => ((ξ PP h.unit : ℂˣ) : ℂ))
    rw [h1, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun PP _ => ?_
    rw [hxy PP, mul_assoc]
    simp only [c, Pi.neg_apply, neg_neg]
    congr 1
    letI := Ideal.Quotient.field PP.1.asIdeal
    convert transform (k := kP PP.1) hrn (hψ PP.1 PP.2) (hξ PP.1 PP.2) (x PP)

end GlobalTheory.ResidueFourier
