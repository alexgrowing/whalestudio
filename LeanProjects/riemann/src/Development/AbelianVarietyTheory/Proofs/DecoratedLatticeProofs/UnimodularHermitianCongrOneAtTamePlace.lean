import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceComapUnitarySupported
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviTransvectionMemCompactAtPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralTraceIdempotentAtTamePlace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjFixedIntegralIsUnitOrIdemSubUnitStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormOfConjFixedUnitTamePlaceStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

namespace GlobalTheory.IwaPlace.UnimodNF

section Abstract

variable {A : Type*} [CommRing A] {ε : A} (hid : IsIdempotentElem ε) (O : Set A)
  (h0 : (0 : A) ∈ O) (hadd : ∀ a ∈ O, ∀ b ∈ O, a + b ∈ O) (hneg : ∀ a ∈ O, -a ∈ O)
  (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hεO : ε ∈ O)

def sub : Subring hid.Corner where
  carrier := {x | x.1 ∈ O}
  zero_mem' := h0
  add_mem' {x y} hx hy := hadd _ hx _ hy
  neg_mem' {x} hx := hneg _ hx
  mul_mem' {x y} hx hy := hmul _ hx _ hy
  one_mem' := hεO

include hid h0 hadd hneg hmul hεO in

theorem exists_congr_one (c : A →+* A) (hc : ∀ x, c (c x) = x) (hcO : ∀ a ∈ O, c a ∈ O) (hcε : c ε = ε)
    (hεa : ∀ a ∈ O, ε * a = a)
    (hloc : ∀ x ∈ O, c x = x → (∃ y ∈ O, x * y = ε) ∨ (∃ y ∈ O, (ε - x) * y = ε))
    (hw : ∃ w ∈ O, w + c w = ε)
    (hnorm : ∀ u ∈ O, c u = u → (∃ y ∈ O, u * y = ε) → ∃ x ∈ O, x * c x = u)
    {n : ℕ} (H : Matrix (Fin n) (Fin n) A) (hH : ∀ i j, H i j ∈ O) (hherm : ∀ i j, c (H i j) = H j i)
    (hinv : ∃ H' : Matrix (Fin n) (Fin n) A, (∀ i j, H' i j ∈ O) ∧ H * H' = ε • (1 : Matrix (Fin n) (Fin n) A)) :
    ∃ P P' : Matrix (Fin n) (Fin n) A, (∀ i j, P i j ∈ O) ∧ (∀ i j, P' i j ∈ O) ∧
      P * P' = ε • (1 : Matrix (Fin n) (Fin n) A) ∧ P' * P = ε • (1 : Matrix (Fin n) (Fin n) A) ∧
      (P.map c)ᵀ * (H * P) = ε • (1 : Matrix (Fin n) (Fin n) A) := by
  classical
  let R := sub hid O h0 hadd hneg hmul hεO
  have corner_mem : ∀ a ∈ O, a ∈ Subsemigroup.corner ε := fun a ha =>
    (Subsemigroup.mem_corner_iff hid).2 ⟨hεa a ha, by rw [mul_comm]; exact hεa a ha⟩
  let mk : ∀ a, a ∈ O → R := fun a ha => ⟨⟨a, corner_mem a ha⟩, ha⟩
  let val : R →+ A := { toFun := fun x => x.1.1, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have val_mem : ∀ x : R, val x ∈ O := fun x => x.2
  have val_inj : ∀ x y : R, val x = val y → x = y := fun x y h => Subtype.ext (Subtype.ext h)
  let c' : R →+* R :=
    { toFun := fun x => mk (c (val x)) (hcO _ (val_mem x))
      map_one' := val_inj _ _ (show c ε = ε from hcε)
      map_mul' := fun x y => val_inj _ _ (show c (val x * val y) = c (val x) * c (val y) from map_mul c _ _)
      map_zero' := val_inj _ _ (show c 0 = 0 from map_zero c)
      map_add' := fun x y => val_inj _ _ (show c (val x + val y) = c (val x) + c (val y) from map_add c _ _) }
  have hc' : ∀ x, c' (c' x) = x := fun x => val_inj _ _ (show c (c (val x)) = val x from hc _)
  have map_mul_val : ∀ X Y : Matrix (Fin n) (Fin n) R, (X * Y).map val = X.map val * Y.map val := by
    intro X Y
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_apply, map_sum]
    rfl
  have map_one_val : (1 : Matrix (Fin n) (Fin n) R).map val = ε • (1 : Matrix (Fin n) (Fin n) A) := by
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · simp only [smul_eq_mul, mul_one]; rfl
    · simp only [smul_eq_mul, mul_zero, map_zero]
  have map_inj : ∀ X Y : Matrix (Fin n) (Fin n) R, X.map val = Y.map val → X = Y := fun X Y h =>
    Matrix.ext fun i j => val_inj _ _ (congrFun (congrFun h i) j)
  let G : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => mk (H i j) (hH i j)
  have hGH : G.map val = H := by ext i j; rfl
  obtain ⟨H', hH'O, hHH'⟩ := hinv
  let G' : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => mk (H' i j) (hH'O i j)
  have hG'H : G'.map val = H' := by ext i j; rfl
  have hGG' : G * G' = 1 := map_inj _ _ (by rw [map_mul_val, map_one_val, hGH, hG'H]; exact hHH')
  have hdet : IsUnit G.det := Matrix.isUnit_det_of_right_inverse hGG'
  have hG : ∀ a b, c' (G a b) = G b a := fun a b => val_inj _ _ (hherm a b)
  have hlocR : ∀ x : R, c' x = x → IsUnit x ∨ IsUnit (1 - x) := by
    intro x hx
    have hx' : c (val x) = val x := congrArg val hx
    rcases hloc (val x) (val_mem x) hx' with ⟨y, hy, hxy⟩ | ⟨y, hy, hxy⟩
    · exact Or.inl (isUnit_iff_exists_inv.2 ⟨mk y hy, val_inj _ _ hxy⟩)
    · exact Or.inr (isUnit_iff_exists_inv.2 ⟨mk y hy, val_inj _ _ hxy⟩)
  have hwR : ∃ w : R, w + c' w = 1 := by
    obtain ⟨w, hw, hw'⟩ := hw
    exact ⟨mk w hw, val_inj _ _ hw'⟩
  have hnormR : ∀ u : R, c' u = u → IsUnit u → ∃ x, x * c' x = u := by
    intro u hu hu'
    obtain ⟨y, hy⟩ := hu'.exists_right_inv
    obtain ⟨x, hx, hx'⟩ := hnorm (val u) (val_mem u) (congrArg val hu) ⟨val y, val_mem y, congrArg val hy⟩
    exact ⟨mk x hx, val_inj _ _ hx'⟩
  obtain ⟨Q, hQ, hGQ⟩ :=
    GlobalTheory.UnramifiedHermitian.exists_eq_transpose_mul_map_of_isUnit_or c' hc' hlocR hwR hnormR hG hdet
  have hmap1 : (1 : Matrix (Fin n) (Fin n) R).map c' = 1 := Matrix.map_one _ (map_zero c') (map_one c')
  refine ⟨((Q⁻¹).map c').map val, (Q.map c').map val, fun i j => val_mem _, fun i j => val_mem _, ?_, ?_, ?_⟩
  · rw [← map_mul_val, ← Matrix.map_mul, Matrix.nonsing_inv_mul Q hQ, hmap1, map_one_val]
  · rw [← map_mul_val, ← Matrix.map_mul, Matrix.mul_nonsing_inv Q hQ, hmap1, map_one_val]
  · have e1 : (((Q⁻¹).map c').map val).map c = (Q⁻¹).map val := by
      ext i j
      exact congrArg val (hc' (Q⁻¹ i j))
    rw [e1, ← Matrix.transpose_map, ← hGH, ← map_mul_val, ← map_mul_val, ← map_one_val]
    congr 1
    have h1 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQ
    rw [hGQ]
    calc (Q⁻¹)ᵀ * (Qᵀ * Q.map c' * (Q⁻¹).map c') = (Q * Q⁻¹)ᵀ * (Q * Q⁻¹).map c' := by
          rw [Matrix.transpose_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.transpose_one, hmap1, Matrix.one_mul]

end Abstract

set_option synthInstance.maxHeartbeats 400000

variable {D : D7}

theorem intAt_zero' (P : Pl D → Prop) : (0 : AE D) ∈ intAt D P := ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩

theorem intAt_neg' {P : Pl D → Prop} {a : AE D} (ha : a ∈ intAt D P) : -a ∈ intAt D P :=
  ⟨neg_mem ha.1, by rw [RingHom.map_neg]; exact neg_mem ha.2⟩

theorem cA_mem_intAt' {v : Pl D} {a : AE D} (ha : a ∈ intAt D (· = v)) : cA D a ∈ intAt D (· = v) :=
  ⟨GlobalTheory.FinPl.RootKeep.conj_mem_idAt ha.1, (GlobalTheory.FinPl.FrameLat.cA_int_iff a).2 ha.2⟩

theorem unimodular_congr_one : ∀ (D : D7) (v : Pl D) (ε : AE D) (n : ℕ) (H : Matrix (Fin n) (Fin n) (AE D)), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → (∀ i j, H i j ∈ intAt D (· = v)) → (∀ i j, cA D (H i j) = H j i) → (∃ H' : Matrix (Fin n) (Fin n) (AE D), (∀ i j, H' i j ∈ intAt D (· = v)) ∧ H * H' = ε • (1 : Matrix (Fin n) (Fin n) (AE D))) → ∃ P P' : Matrix (Fin n) (Fin n) (AE D), (∀ i j, P i j ∈ intAt D (· = v)) ∧ (∀ i j, P' i j ∈ intAt D (· = v)) ∧ P * P' = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) ∧ P' * P = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) ∧ adj P * (H * P) = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) := by
  intro D v ε n H htame hεε hεc hεI hε hHI hherm hinv
  exact exists_congr_one (hid := hεε) (O := intAt D (· = v)) (intAt_zero' _)
    (fun a ha b hb => GlobalTheory.IwaPlace.SdComap.intAt_add ha hb) (fun a ha => intAt_neg' ha)
    (fun a ha b hb => GlobalTheory.IwaPlace.SdComap.intAt_mul ha hb) hεI (cA D) (fun z => Formalism.L2.Theta.cA_cA z)
    (fun a ha => cA_mem_intAt' ha) hεc (fun a ha => (hε a).1 ha.1)
    (GlobalTheory.T.conjFixed_integral_isUnit_or_idem_sub_unit D v ε htame hεε hεc hεI hε)
    (GlobalTheory.IwaPlace.exists_trace_one_at_tame D v ε hεε hεc hεI hε htame)
    (GlobalTheory.T.exists_norm_of_conjFixed_unit_tamePlace D v ε htame hεε hεc hεI hε) H hHI hherm hinv

end GlobalTheory.IwaPlace.UnimodNF

end
