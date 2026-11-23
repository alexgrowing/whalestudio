import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierFlatCharacterDatumFiniteFieldStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1600000

namespace GlobalTheory.FlatFourierQ

theorem unitOff_mul' {N : ℕ} {u v : ℂ} (hu : UnitOff N u) (hv : UnitOff N v) : UnitOff N (u * v) := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  obtain ⟨hv0, m, hm1, hm2⟩ := hv
  refine ⟨mul_ne_zero hu0 hv0, n + m, ?_, ?_⟩
  · have e : (N : ℂ) ^ (n + m) * (u * v) = ((N : ℂ) ^ n * u) * ((N : ℂ) ^ m * v) := by rw [pow_add]; ring
    rw [e]; exact hn1.mul hm1
  · have e : (N : ℂ) ^ (n + m) * (u * v)⁻¹ = ((N : ℂ) ^ n * u⁻¹) * ((N : ℂ) ^ m * v⁻¹) := by rw [pow_add, mul_inv]; ring
    rw [e]; exact hn2.mul hm2

theorem unitOff_prod' {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, UnitOff N (f i)) :
    UnitOff N (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simp, 0, by simpa using isIntegral_one, by simpa using isIntegral_one⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact unitOff_mul' (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem unitOff_of_dvd {N q m : ℕ} {C : ℂ} (hq : q ∣ N) (h0 : C ≠ 0) (hC : IsIntegral ℤ C)
    (hCq : IsIntegral ℤ ((q : ℂ) ^ m * C⁻¹)) : UnitOff N C := by
  obtain ⟨d, rfl⟩ := hq
  have hint : ∀ a : ℕ, IsIntegral ℤ (a : ℂ) := fun a => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (a : ℤ))
  refine ⟨h0, m, ((hint _).pow m).mul hC, ?_⟩
  have e : ((q * d : ℕ) : ℂ) ^ m * C⁻¹ = (d : ℂ) ^ m * ((q : ℂ) ^ m * C⁻¹) := by push_cast; ring
  rw [e]; exact ((hint d).pow m).mul hCq

theorem dite_prod' {ι : Type} (Q : Finset ι) (p : ι → Prop) (f : ∀ i, p i → ℂ) :
    (if h : ∀ i ∈ Q, p i then ∏ i ∈ Q.attach, f i.1 (h i.1 i.2) else 0) =
      ∏ i ∈ Q.attach, if h : p i.1 then f i.1 h else 0 := by
  split_ifs with h
  · exact Finset.prod_congr rfl fun i _ => (dif_pos (h i.1 i.2)).symm
  · push_neg at h
    obtain ⟨i, hi, hp⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_attach Q ⟨i, hi⟩) (dif_neg hp)).symm

theorem omegaQ_eq_unit_mul_flat_transform : ∀ (D : D7) [∀ PP : Pl D.host.E, Fintype (kP PP)] (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (r n N : ℕ), 0 < N → (∀ PP ∈ Q, (ψP PP).IsPrimitive ∧ ξ PP ≠ 1 ∧ Nat.card (kP PP) ∣ N) → ∃ Gc : ℂ, UnitOff N Gc ∧ ∀ ub : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP), omegaQ Q r ξ (-1) ub = Gc * ∑ y : (∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)), omegaFlat Q r ξ (fun PP => if h : PP ∈ Q then -(y ⟨PP, h⟩) else 0) * ∏ PP : ↥Q, ψP PP.1 (Matrix.trace (y PP * ub PP.1)) := by
  intro D _ Q ξ ψP r n N _ hQ
  let fl : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin n) (kP PP) → ℂ := fun PP y =>
    if h : IsUnit (topL r y).det then ((ξ PP h.unit : ℂˣ) : ℂ) else 0
  let fq : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP) → ℂ := fun PP u =>
    if h : LowZero r u ∧ IsUnit (topL r u).det then ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0
  have hloc : ∀ PP : ↥Q, ∃ (C : ℂ) (m : ℕ), C ≠ 0 ∧ IsIntegral ℤ C ∧
      IsIntegral ℤ ((Nat.card (kP PP.1) : ℂ) ^ m * C⁻¹) ∧
      ∀ u : Matrix (Fin n) (Fin r) (kP PP.1),
        (∑ y : Matrix (Fin r) (Fin n) (kP PP.1), fl PP.1 (-y) * ψP PP.1 (Matrix.trace (y * u))) = C * fq PP.1 u := by
    intro PP
    letI := Ideal.Quotient.field PP.1.asIdeal
    obtain ⟨C, m, h0, h1, h2, h3⟩ :=
      GlobalTheory.T.fourier_flat_character_datum_finiteField (kP PP.1) (ψP PP.1) (ξ PP.1) r n (hQ _ PP.2).1 (hQ _ PP.2).2.1
    exact ⟨C, m, h0, h1, by rw [Nat.card_eq_fintype_card]; exact h2, h3⟩
  choose C m hC0 hCi hCm hCe using hloc
  refine ⟨(∏ PP : ↥Q, C PP)⁻¹, ?_, fun ub => ?_⟩
  · have hu : UnitOff N (∏ PP : ↥Q, C PP) :=
      unitOff_prod' _ _ fun PP _ => unitOff_of_dvd (hQ _ PP.2).2.2 (hC0 PP) (hCi PP) (hCm PP)
    obtain ⟨h0, e, h1, h2⟩ := hu
    exact ⟨inv_ne_zero h0, e, h2, by rw [inv_inv]; exact h1⟩
  · have hq : omegaQ Q r ξ (-1) ub = ∏ PP : ↥Q, fq PP.1 (ub PP.1) := by
      rw [← Finset.attach_eq_univ]
      unfold omegaQ
      convert dite_prod' Q (fun PP => LowZero r (ub PP) ∧ IsUnit (topL r (ub PP)).det)
        (fun PP h => ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ))
    have hf : ∀ y : (∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)),
        omegaFlat Q r ξ (fun PP => if h : PP ∈ Q then -(y ⟨PP, h⟩) else 0) = ∏ PP : ↥Q, fl PP.1 (-(y PP)) := by
      intro y
      have e0 : ∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin n) (kP PP),
          omegaFlat Q r ξ Y = ∏ PP ∈ Q.attach, fl PP.1 (Y PP.1) := by
        intro Y
        unfold omegaFlat
        convert dite_prod' Q (fun PP => IsUnit (topL r (Y PP)).det) (fun PP h => ((ξ PP h.unit : ℂˣ) : ℂ))
      rw [e0, Finset.attach_eq_univ]
      refine Finset.prod_congr rfl fun PP _ => ?_
      simp only [dif_pos PP.2, Subtype.coe_eta]
    simp only [hf, ← Finset.prod_mul_distrib]
    have hs := Finset.prod_univ_sum (t := fun (PP : ↥Q) => (Finset.univ : Finset (Matrix (Fin r) (Fin n) (kP PP.1))))
      (f := fun (PP : ↥Q) (y : Matrix (Fin r) (Fin n) (kP PP.1)) => fl PP.1 (-y) * ψP PP.1 (Matrix.trace (y * ub PP.1)))
    rw [Fintype.piFinset_univ] at hs
    rw [← hs]
    simp only [hCe]
    rw [Finset.prod_mul_distrib, hq, ← mul_assoc, inv_mul_cancel₀ (Finset.prod_ne_zero_iff.2 fun PP _ => hC0 PP), one_mul]

end GlobalTheory.FlatFourierQ
