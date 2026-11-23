import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Polynomial
open Matrix
open Formalism.UG (cT cT_mul cT_one)
open scoped Classical

noncomputable section

namespace GlobalTheory.TrScale

theorem exists_scale (D : D7) (V : HSp D) (Φ : WittFrame V) (u : SV (wittIndex V)) : ∃ g : GF V, (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V g x = (2 : D.host.E) • x) ∧ (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V g x = (2 : D.host.E)⁻¹ • x) ∧ ∀ z, (∀ x ∈ Φ.sub u, V.hT x z = 0) → (∀ x ∈ Φ.sub (-u), V.hT x z = 0) → GlobalTheory.Cusp.ratAct D.sp.cm V g z = z := by
  let b : Fin (wittIndex V) × Bool → V.V := fun a => if a.2 then Φ.e a.1 else Φ.f a.1
  let σ : D.host.E →+* D.host.E := D.sp.cm.sig
  let d : Fin (wittIndex V) × Bool → D.host.E := fun a =>
    if u a.1 = 0 then 1 else if (u a.1 = 1 ↔ a.2 = true) then 2 else 2⁻¹
  have h2 : (2 : D.host.E) ≠ 0 := two_ne_zero
  have hσ2 : σ 2 = 2 := map_ofNat σ 2
  have hσd : ∀ i s, σ (d (i, s)) * d (i, !s) = 1 := fun i s => by
    simp only [d]
    split_ifs <;> cases s <;> simp_all [map_inv₀, hσ2, h2]
  let S : Matrix (Fin (wittIndex V) × Bool) (Fin (wittIndex V) × Bool) D.host.E :=
    (1 : Matrix _ _ D.host.E).submatrix id ((Equiv.refl _).prodCongr Equiv.boolNot)
  have fe : ∀ i j, V.hT (Φ.f i) (Φ.e j) = if i = j then 1 else 0 := fun i j => (Φ.ef j i).trans (by simp only [eq_comm])
  have ef : ∀ i j, V.hT (Φ.e i) (Φ.f j) = if i = j then 1 else 0 := fun i j => by
    rw [← V.herm.eq, fe]; by_cases h : i = j <;> simp [h, eq_comm]
  have ee : ∀ i j, V.hT (Φ.e i) (Φ.e j) = 0 := fun i j => Φ.ee j i
  have ff : ∀ i j, V.hT (Φ.f i) (Φ.f j) = 0 := fun i j => Φ.ff j i
  have hB : cT σ (cols V b) * V.gram * cols V b = S := by
    rw [gram_cols]
    ext ⟨i, _ | _⟩ ⟨j, _ | _⟩ <;> simp [b, S, ee, ff, ef, fe, Matrix.one_apply]
  have hSS : S * S = 1 := by
    refine (Matrix.mul_submatrix_one (Equiv.refl _) _ S).trans ?_
    ext ⟨i, s⟩ ⟨j, t⟩
    simp [S, Matrix.one_apply]
  have hS : cT σ S = S := by
    ext ⟨i, _ | _⟩ ⟨j, _ | _⟩ <;> simp [cT, S, Matrix.one_apply, eq_comm, apply_ite σ]
  let P : Matrix (Fin (wittIndex V) × Bool) (Fin (wittIndex V) × Bool) D.host.E := diagonal d
  have hP : cT σ P * S * P = S := by
    have hc : cT σ P = diagonal fun a => σ (d a) := by
      ext a c; by_cases h : a = c <;> simp [cT, P, diagonal_apply, h, eq_comm]
    rw [hc]
    ext ⟨i, s⟩ ⟨j, t⟩
    simp only [P, Matrix.mul_diagonal, Matrix.diagonal_mul, S, submatrix_apply, Matrix.one_apply, id, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, Prod.mk.injEq, Equiv.boolNot_apply]
    by_cases hij : i = j
    · subst hij
      cases s <;> cases t <;> simp only [true_and, and_true, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, and_self, mul_one, mul_zero, zero_mul, and_false, ite_true, ite_false, Prod.mk.injEq]
      all_goals first | exact hσd i _ | exact congrArg _ (hσd i _) | skip
    · simp [hij]
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = S * (cT σ (cols V b) * V.gram) := ⟨_, rfl⟩
  have hQB : Q * cols V b = 1 := by rw [hQ, Matrix.mul_assoc, hB, hSS]
  have h1 : cT σ (cols V b) * V.gram = S * Q := by rw [hQ, ← Matrix.mul_assoc S S, hSS, Matrix.one_mul]
  have h2' : V.gram * cols V b = cT σ Q * S := by
    have := congrArg (cT σ) h1
    rwa [cT_mul, cT_mul, AutFunCompare.cT_cT', IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_gram, hS] at this
  have hw := unitary_extension σ h1 h2' hQB hP
  have hi : V.gram⁻¹ * (cT σ (1 + cols V b * (P - 1) * Q) * V.gram) * (1 + cols V b * (P - 1) * Q) = 1 := by
    rw [Matrix.mul_assoc, hw, Matrix.nonsing_inv_mul _ (IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V)]
  let w : GF V := ⟨⟨_, _, mul_eq_one_comm.1 hi, hi⟩, hw⟩
  have act : ∀ {p : Type} (x y : p → V.V), (1 + cols V b * (P - 1) * Q) * cols V x = cols V y →
      ∀ a, GlobalTheory.Cusp.ratAct D.sp.cm V w (x a) = y a := fun x y h a => by
    refine V.frame.repr.injective (DFunLike.coe_injective ?_)
    rw [GlobalTheory.Cusp.ratAct, Matrix.repr_toLin]
    exact funext fun i => congrFun (congrFun h i) a
  have hwb : ∀ a, GlobalTheory.Cusp.ratAct D.sp.cm V w (b a) = d a • b a := act b (fun a => d a • b a) (by
    rw [Matrix.add_mul, Matrix.mul_assoc, hQB, Matrix.mul_one, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
      add_sub_cancel]
    ext r a; simp [cols, P, Matrix.mul_diagonal, mul_comm])
  refine ⟨w, fun x hx => ?_, fun x hx => ?_, fun z hz1 hz2 => ?_⟩
  · refine (Submodule.span_le (p := LinearMap.eqLocus (GlobalTheory.Cusp.ratAct D.sp.cm V w) ((2 : D.host.E) • LinearMap.id))).2 ?_ hx
    rintro _ (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) <;> simp only [Set.mem_setOf_eq] at hi
    · have := hwb (i, true); simp only [b, d, hi] at this; simpa [LinearMap.mem_eqLocus] using this
    · have := hwb (i, false); simp only [b, d, hi] at this; simpa [LinearMap.mem_eqLocus] using this
  · refine (Submodule.span_le (p := LinearMap.eqLocus (GlobalTheory.Cusp.ratAct D.sp.cm V w) ((2 : D.host.E)⁻¹ • LinearMap.id))).2 ?_ hx
    rintro _ (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) <;> simp only [Set.mem_setOf_eq, Pi.neg_apply, neg_eq_iff_eq_neg] at hi
    · have := hwb (i, true); simp only [b, d, hi] at this; simpa [LinearMap.mem_eqLocus] using this
    · have := hwb (i, false); simp only [b, d, hi] at this; simpa [LinearMap.mem_eqLocus] using this
  · have hz : ∀ a, u a.1 ≠ 0 → V.hT (b a) z = 0 := by
      rintro ⟨i, s⟩ h
      have hm1 : ∀ x, x ∈ Φ.sub u ∨ x ∈ Φ.sub (-u) → V.hT x z = 0 := fun x hx => hx.elim (hz1 x) (hz2 x)
      apply hm1
      rcases (show u i = 1 ∨ u i = -1 by generalize u i = t at h; revert t; decide) with h' | h' <;> cases s <;>
        simp only [b, if_true, if_false, Bool.false_eq_true]
      · exact .inr (by rw [WittFrame.sub]; exact Submodule.subset_span (.inr ⟨i, by simp [h'], rfl⟩))
      · exact .inl (by rw [WittFrame.sub]; exact Submodule.subset_span (.inl ⟨i, h', rfl⟩))
      · exact .inl (by rw [WittFrame.sub]; exact Submodule.subset_span (.inr ⟨i, h', rfl⟩))
      · exact .inr (by rw [WittFrame.sub]; exact Submodule.subset_span (.inl ⟨i, by simp [h'], rfl⟩))
    have hY : Q * cols V (fun _ : Unit => z) = S * of fun a (_ : Unit) => V.hT (b a) z := by
      rw [hQ, Matrix.mul_assoc, gram_cols]
    have hSY : S * of (fun a (_ : Unit) => V.hT (b a) z) = of fun (a : Fin (wittIndex V) × Bool) (_ : Unit) => V.hT (b (a.1, !a.2)) z := by
      simp only [S]; rw [Matrix.one_submatrix_mul]
      ext ⟨i, s⟩ c; rfl
    have hZ : (P - 1) * of (fun (a : Fin (wittIndex V) × Bool) (_ : Unit) => V.hT (b (a.1, !a.2)) z) = 0 := by
      ext ⟨i, s⟩ c
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, show P = diagonal d from rfl, Matrix.diagonal_mul, of_apply,
        Matrix.zero_apply]
      by_cases hu : u i = 0
      · simp [d, hu]
      · rw [hz (i, !s) hu]; simp
    have key : (1 + cols V b * (P - 1) * Q) * cols V (fun _ : Unit => z) = cols V (fun _ : Unit => z) := by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, hY, hSY, hZ, Matrix.mul_zero, add_zero]
    exact act (fun _ : Unit => z) (fun _ => z) key ()

end GlobalTheory.TrScale
