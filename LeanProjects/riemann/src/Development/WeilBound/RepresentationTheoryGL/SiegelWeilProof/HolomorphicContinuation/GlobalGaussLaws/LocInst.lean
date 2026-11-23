import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocInstA

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocInstH

open MvPolynomial

def toRe (m n : ℕ) : PX m n →ₐ[ℂ] PX m n :=
  aeval fun k => if k.2.2 then X (k.1, k.2.1, false) - C Complex.I * X (k.1, k.2.1, true)
    else X (k.1, k.2.1, false) + C Complex.I * X (k.1, k.2.1, true)

def ofRe (m n : ℕ) : PX m n →ₐ[ℂ] PX m n :=
  aeval fun k => if k.2.2 then C (1 / (2 * Complex.I)) * (X (k.1, k.2.1, false) - X (k.1, k.2.1, true))
    else C (1 / 2) * (X (k.1, k.2.1, false) + X (k.1, k.2.1, true))

theorem ofRe_toRe {m n : ℕ} (P : PX m n) : ofRe m n (toRe m n P) = P := by
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hC : (C Complex.I : PX m n) * C (1 / (2 * Complex.I)) = C (1 / 2) := by
    rw [← C_mul]; congr 1; field_simp
  have hC2 : (C (1 / 2) : PX m n) + C (1 / 2) = 1 := by
    rw [← C_add, ← C_1]; congr 1; norm_num
  have : (ofRe m n).comp (toRe m n) = AlgHom.id ℂ (PX m n) := by
    apply MvPolynomial.algHom_ext
    intro k
    obtain ⟨a, i, b⟩ := k
    cases b
    · simp only [AlgHom.comp_apply, AlgHom.id_apply, toRe, ofRe, aeval_X, map_add, map_mul, aeval_C, algebraMap_eq,
        Bool.false_eq_true, if_false, if_true]
      linear_combination (X (a, i, false) - X (a, i, true)) * hC + X (a, i, false) * hC2
    · simp only [AlgHom.comp_apply, AlgHom.id_apply, toRe, ofRe, aeval_X, map_sub, map_mul, aeval_C, algebraMap_eq,
        Bool.false_eq_true, if_false, if_true]
      linear_combination -(X (a, i, false) - X (a, i, true)) * hC + X (a, i, true) * hC2
  exact congrArg (fun f => f P) this

theorem evX_eq_eval_toRe {m n : ℕ} (P : PX m n) (y : Fin m × Fin n × Bool → ℝ) :
    evX P (fun a i => (y (a, i, false) : ℂ) + Complex.I * (y (a, i, true) : ℂ)) =
      eval (fun k => (y k : ℂ)) (toRe m n P) := by
  have key : (aeval fun k : Fin m × Fin n × Bool => if k.2.2 then star ((y (k.1, k.2.1, false) : ℂ) + Complex.I * (y (k.1, k.2.1, true) : ℂ))
      else (y (k.1, k.2.1, false) : ℂ) + Complex.I * (y (k.1, k.2.1, true) : ℂ)) = (aeval fun k => (y k : ℂ)).comp (toRe m n) := by
    apply MvPolynomial.algHom_ext
    intro k
    obtain ⟨a, i, b⟩ := k
    cases b
    · simp [toRe]
    · simp [toRe, Complex.conj_ofReal, sub_eq_add_neg]
  unfold evX
  rw [← coe_aeval_eq_eval, ← coe_aeval_eq_eval]
  exact congrArg (fun f => f P) key

theorem evX_injective {m n : ℕ} {P Q : PX m n} (h : ∀ u, evX P u = evX Q u) : P = Q := by
  have h0 : toRe m n (P - Q) = 0 := by
    apply eq_zero_of_eval_real
    intro y
    rw [← evX_eq_eval_toRe]
    have := h (fun a i => (y (a, i, false) : ℂ) + Complex.I * (y (a, i, true) : ℂ))
    unfold evX at this ⊢
    rw [map_sub, this, sub_self]
  rw [← sub_eq_zero, ← ofRe_toRe (P - Q), h0, map_zero]

theorem fP_injective {m n : ℕ} {c : ℝ} {P Q : PX m n} (h : fP c P = fP c Q) : P = Q := by
  apply evX_injective
  intro u
  have := congrFun h u
  simp only [fP] at this
  have hg : gs c u ≠ 0 := Complex.exp_ne_zero _
  exact mul_right_cancel₀ hg this

theorem fP_smul_add {m n : ℕ} (c : ℝ) (a : ℂ) (P Q : PX m n) : fP c (a • P + Q) = a • fP c P + fP c Q := by
  funext u
  simp only [fP, evX, map_add, smul_eq_C_mul, map_mul, eval_C, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end PositivityTheory.Rg.Sw.Glob.LocInstH

namespace PositivityTheory.Rg.Sw.Glob

open LocInstH

theorem locInst_of (hT : TensMem) (hl : LIl) (hlin : LIlin) (hlaw : LIlaw) (hcell : LIcell) (hcont : LIcont)
    (hrho : LIrho) (hk : LIkact) (hvac : LIvac) (hkv : LIkvac) : LocInst := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL
  have hl0 := hl D n V ψ χ θ μ ω H l s ν τ ε fr ι hC
  obtain ⟨hlinL, hid⟩ := hlin D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  obtain ⟨e, he⟩ := hlaw D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  obtain ⟨C0, hC0, hCc⟩ := hcell D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  obtain ⟨ρ, hρ, hfin⟩ := hrho D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  have hzero : ∀ y : GR n, L y (fP (cLoc l τ) (0 : PX V.rank n)) = 0 := by
    intro y
    have h2 := hlinL y 1 0 0
    simp only [one_smul, add_zero] at h2
    have : L y (fP (cLoc l τ) (0 : PX V.rank n)) + L y (fP (cLoc l τ) (0 : PX V.rank n)) =
        L y (fP (cLoc l τ) (0 : PX V.rank n)) + 0 := by rw [add_zero]; exact h2.symm
    exact add_left_cancel this
  let sL : PX V.rank n →ₗ[ℂ] (GR n → ℂ) :=
    { toFun := fun P => sLd L (cLoc l τ) P
      map_add' := fun P Q => by
        funext y
        have h2 := hlinL y 1 P Q
        rw [one_smul, one_smul] at h2
        simp only [sLd, Pi.add_apply, h2]
      map_smul' := fun a P => by
        funext y
        have h2 := hlinL y a P 0
        rw [add_zero, hzero y, add_zero] at h2
        simp only [sLd, Pi.smul_apply, RingHom.id_apply, h2, smul_eq_mul] }
  have hsign : ((tLoc l τ = cLoc l τ ∧ (pqOf ε l τ).1 = cnt ε true ∧ (pqOf ε l τ).2 = cnt ε false) ∨
      (tLoc l τ = -cLoc l τ ∧ (pqOf ε l τ).1 = cnt ε false ∧ (pqOf ε l τ).2 = cnt ε true)) := by
    unfold tLoc cLoc pqOf
    split_ifs with h
    · exact Or.inl ⟨by rw [abs_of_pos h], rfl, rfl⟩
    · have hneg : l τ < 0 := lt_of_le_of_ne (not_lt.mp h) hl0
      exact Or.inr ⟨by rw [abs_of_neg hneg]; ring, rfl, rfl⟩
  have hcpos : 0 < cLoc l τ := by
    unfold cLoc
    have := abs_pos.mpr hl0
    positivity
  have h11 : sLd L (cLoc l τ) 1 1 = 1 := by
    simp [sLd, hid, fP, evX, gs]
  have hvac' : ∀ g, sLd L (cLoc l τ) 1 g = F0 (pqOf ε l τ).1 (pqOf ε l τ).2 e g :=
    hvac V.rank n ε (cLoc l τ) (tLoc l τ) (pqOf ε l τ).1 (pqOf ε l τ).2 e hcpos hsign (sLd L (cLoc l τ) 1) C0
      (hcont D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL 1) h11 (fun y g hy => he 1 y g hy) (fun g b hb hg => hCc 1 g b hb hg)
  refine ⟨sL, ρ, (pqOf ε l τ).1, (pqOf ε l τ).2, e, ?_, ?_, fun P y => rfl, hρ⟩
  · have hs := hC.hsig
    unfold pqOf GoodSig at *
    split_ifs <;> omega
  · refine ⟨hcpos, hsign, fun P => hcont D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL P, hvac', fun P y g hy => he P y g hy,
      ⟨C0, hC0, fun P g b hb hg => hCc P g b hb hg⟩,
      fun P g k hk' => hk D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL ρ hρ P g k hk', ?_, hfin⟩
    intro k hkK
    have h1 := hkv D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL e hvac' k hkK
    rw [hρ k 1 hkK] at h1
    apply fP_injective (c := cLoc l τ)
    rw [h1]
    have := fP_smul_add (cLoc l τ) (F0 (pqOf ε l τ).1 (pqOf ε l τ).2 e k) (1 : PX V.rank n) 0
    simp only [add_zero] at this
    rw [this]
    funext u
    simp [fP, evX]

end PositivityTheory.Rg.Sw.Glob
