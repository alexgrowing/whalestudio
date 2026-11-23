import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DarbouxModelAlgebraicVectorsLeAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.PlaceCut

section Alg

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in

theorem glue_mul {e : R} (he : e * e = e) (a b c d : Matrix ι ι A) :
    (e • a + (1 - e) • b) * (e • c + (1 - e) • d) = e • (a * c) + (1 - e) • (b * d) := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [mul_sub, h2, mul_one, sub_zero]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, he, h1, h2, h3,
    zero_smul, add_zero, zero_add]

omit [Fintype ι] [DecidableEq ι] in
theorem glue_self (e : R) (a : Matrix ι ι A) : e • a + (1 - e) • a = a := by
  rw [← add_smul, add_sub_cancel, one_smul]

theorem exists_glue (c : A →ₐ[R] A) (J : Matrix ι ι A) {e : R} (he : e * e = e) (g h : GlobalTheory.WeilM.UG c J) :
    ∃ p : GlobalTheory.WeilM.UG c J, (p.1.1 : Matrix ι ι A) = e • g.1.1 + (1 - e) • h.1.1 ∧
      ((p⁻¹).1.1 : Matrix ι ι A) = e • (g⁻¹).1.1 + (1 - e) • (h⁻¹).1.1 := by
  let q : GL ι A :=
    { val := e • g.1.1 + (1 - e) • h.1.1
      inv := e • g.1.2 + (1 - e) • h.1.2
      val_inv := by rw [glue_mul he, g.1.3, h.1.3, glue_self]
      inv_val := by rw [glue_mul he, g.1.4, h.1.4, glue_self] }
  have hq : q ∈ GlobalTheory.WeilM.UG c J := by
    have hg : (g.1.1)ᵀ * J * (g.1.1).map c = J := g.2
    have hh : (h.1.1)ᵀ * J * (h.1.1).map c = J := h.2
    show (e • g.1.1 + (1 - e) • h.1.1)ᵀ * J * (e • g.1.1 + (1 - e) • h.1.1).map c = J
    have m : (e • g.1.1 + (1 - e) • h.1.1).map c = e • (g.1.1).map c + (1 - e) • (h.1.1).map c := by
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add, map_smul]
    rw [m, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul]
    have k := glue_mul he (g.1.1)ᵀ (h.1.1)ᵀ J J
    rw [glue_self] at k
    rw [k, glue_mul he, hg, hh, glue_self]
  exact ⟨⟨q, hq⟩, rfl, rfl⟩

end Alg

theorem exists_idem {F : Type} [Field F] [NumberField F] (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) :
    ∃ e : AF F, e * e = e ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F e = 0 ∧ (∀ w ∈ S, GlobalTheory.AdelicU.evFin F w e = 1) ∧
      (∀ w ∉ S, GlobalTheory.AdelicU.evFin F w e = 0) ∧
      ∀ u : AF F, (∀ w ∈ S, GlobalTheory.AdelicU.evFin F w u = 0) → u * e = 0 := by
  classical
  let b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F := ∑ v ∈ S, GlobalTheory.AdelicU.singleFin v 1
  have hb1 : ∀ w ∈ S, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w b = 1 := by
    intro w hw
    rw [map_sum, Finset.sum_eq_single_of_mem w hw, GlobalTheory.AdelicU.evalV_singleFin_self]
    intro v _ hv
    exact GlobalTheory.AdelicU.evalV_singleFin_ne hv.symm 1
  have hb0 : ∀ w ∉ S, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w b = 0 := by
    intro w hw
    rw [map_sum]
    refine Finset.sum_eq_zero fun v hv => GlobalTheory.AdelicU.evalV_singleFin_ne ?_ 1
    rintro rfl
    exact hw hv
  refine ⟨((0 : Ainf F), b), ?_, ?_, hb1, hb0, ?_⟩
  · refine Prod.ext (by change (0 : Ainf F) * 0 = 0; exact mul_zero _) ?_
    change b * b = b
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul]
    by_cases hw : w ∈ S
    · rw [hb1 w hw, mul_one]
    · rw [hb0 w hw, mul_zero]
  · show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
    exact map_zero _
  · intro u hu
    refine Prod.ext (by change u.1 * 0 = 0; exact mul_zero _) ?_
    change u.2 * b = 0
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul, map_zero]
    by_cases hw : w ∈ S
    · have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w u.2 = 0 := hu w hw
      rw [this, zero_mul]
    · rw [hb0 w hw, mul_zero]

theorem exists_cut : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J) (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)),
    ∃ gS k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J, g = gS * k ∧
      (∀ u : AF F, (∀ w ∈ S, GlobalTheory.AdelicU.evFin F w u = 0) → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat gS - 1) = 0) ∧
      (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) ∧
      (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u →
        u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g - 1)) ∧
      (∀ w ∉ S, ∀ z ∈ GlobalTheory.InertSph.latAt X w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k *ᵥ z = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g *ᵥ z ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k⁻¹ *ᵥ z = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g⁻¹ *ᵥ z) := by
  intro F E _ _ _ _ _ σ n X g S
  obtain ⟨e, he, heI, he1, he0, heu⟩ := exists_idem S
  obtain ⟨gS, hS, -⟩ := exists_glue (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) he g 1
  obtain ⟨k, hk, hk'⟩ := exists_glue (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) he 1 g
  have hS2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat gS = e • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g + (1 - e) • 1 := hS
  have hk2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k = e • 1 + (1 - e) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g := hk
  have hk3 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k⁻¹ = e • 1 + (1 - e) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g⁻¹ := by
    rw [inv_one] at hk'
    exact hk'
  have hoff : ∀ (u : AF F) (M : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), u * e = 0 →
      u • (e • (1 : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) + (1 - e) • M) = u • M := by
    intro u M hu
    rw [smul_add, smul_smul, smul_smul, mul_sub, hu, mul_one, sub_zero, zero_smul, zero_add]
  refine ⟨gS, k, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    apply Units.ext
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat gS * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k
    rw [hS2, hk2, glue_mul he, Matrix.mul_one, Matrix.one_mul, glue_self]
  · intro u hu
    rw [hS2, smul_sub, smul_add, smul_smul, smul_smul, mul_sub, heu u hu, mul_one, sub_zero, zero_smul, zero_add,
      sub_self]
  · intro w hw u hu
    have h1 : (1 - e) * u = 0 := hu (1 - e) (by rw [map_sub, map_one, he1 w hw, sub_self])
    have h2 : u * (1 - e) = 0 := by rw [mul_comm, h1]
    have h3 : u * e = u := by rw [mul_sub, mul_one, sub_eq_zero] at h2; exact h2.symm
    rw [hk2, smul_sub, smul_add, smul_smul, smul_smul, h2, h3, zero_smul, add_zero, sub_self]
  · intro u hu
    have h1 : e * u = 0 := hu e heI
    rw [hk2, smul_sub, smul_sub, hoff u _ (by rw [mul_comm, h1])]
  · intro w hw z hz
    have key : ∀ M : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E),
        (e • (1 : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) + (1 - e) • M) *ᵥ z = M *ᵥ z := by
      intro M
      induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, -, y, -, rfl⟩ := hz
        have h1 : e * a = 0 := ha e (he0 w hw)
        rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ← Matrix.smul_mulVec, ← Matrix.smul_mulVec,
          hoff a M (by rw [mul_comm, h1])]
      | zero => rw [Matrix.mulVec_zero, Matrix.mulVec_zero]
      | add x y _ _ hx hy => rw [Matrix.mulVec_add, Matrix.mulVec_add, hx, hy]
      | neg x _ hx => rw [Matrix.mulVec_neg, Matrix.mulVec_neg, hx]
    rw [hk2, hk3]
    exact ⟨key _, key _⟩

end GlobalTheory.PlaceCut
