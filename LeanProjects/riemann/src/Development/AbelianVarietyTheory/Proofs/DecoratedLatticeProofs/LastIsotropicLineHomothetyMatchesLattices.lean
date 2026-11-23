import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeRationalLineTraceFractionalIdealStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionLocallyPrincipal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LastLine

variable {D : D7}

theorem cancel (v : GlobalTheory.FinPl.Pl D) (x : D.host.E) (hx : x ≠ 0) (A : AE D → Prop)
    (hA : ∀ a ∈ idAt D (· = v), A a ↔ incA D x⁻¹ * a ∈ intAt D (· = v)) (P Q : AE D → Prop)
    (hP : ∀ o ∈ intAt D (· = v), ∀ t, P t → P (o * t)) (hQ : ∀ o ∈ intAt D (· = v), ∀ t, Q t → Q (o * t))
    (h : ∀ s ∈ idAt D (· = v), (∀ a ∈ idAt D (· = v), A a → P (s * a)) ↔ (∀ a ∈ idAt D (· = v), A a → Q (s * a))) :
    ∀ t ∈ idAt D (· = v), (P t ↔ Q t) := by
  intro t ht
  obtain ⟨ε, -, hεI, hε⟩ := GlobalTheory.IwaPlace.LocSD.exists_idem (D := D) v
  have hs : incA D x⁻¹ * t ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ ht
  have ha0 : incA D x * ε ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ hεI.1
  have hA0 : A (incA D x * ε) := by
    rw [hA _ ha0, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, one_mul]
    exact hεI
  have hst : incA D x⁻¹ * t * (incA D x * ε) = t := by
    rw [show incA D x⁻¹ * t * (incA D x * ε) = (incA D x⁻¹ * incA D x) * (ε * t) by ring, ← map_mul,
      inv_mul_cancel₀ hx, map_one, one_mul, hε t ht]
  have hsa : ∀ a, incA D x⁻¹ * t * a = (incA D x⁻¹ * a) * t := fun a => by ring
  constructor
  · intro hPt
    have := (h _ hs).1 (fun a ha hAa => by
      rw [hsa]; exact hP _ ((hA a ha).1 hAa) t hPt) _ ha0 hA0
    rwa [hst] at this
  · intro hQt
    have := (h _ hs).2 (fun a ha hAa => by
      rw [hsa]; exact hQ _ ((hA a ha).1 hAa) t hQt) _ ha0 hA0
    rwa [hst] at this

theorem colMul_mul {m n : ℕ} (X : Mx D m n) (i : Fin n) (o t : AE D) :
    colMul X i (o * t) = o • colMul X i t := by
  funext k
  simp only [GlobalTheory.FinPl.colMul, Pi.smul_apply, smul_eq_mul, mul_assoc]

end GlobalTheory.Core.Mi.LastLine

end

noncomputable section

namespace GlobalTheory.Core.Mi.LastLine

variable {D : D7}

theorem lastLine_match : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) (L L' : Lat S) (M M' : Lat S₀) (v : GlobalTheory.FinPl.Pl D) (c : AE D) (γ : GA D S₀), IsSelfDualC S₀ M → z ≠ 0 → LastAt ψ d z L M v → LastAt ψ d z L' M' v → NormOneAt v c → Formalism.L2.Theta.mt S₀ γ *ᵥ ratV z = ratV z → SMoves S₀ c γ M M' v → ∀ i : Fin ρ, i.1 + 1 = ρ → ∀ a ∈ idAt D (· = v), (colMul d.jX i a ∈ latV S L (· = v) ↔ colMul d.jX i (c * a) ∈ latV S L' (· = v)) := by
  intro D ψ S S₀ ρ d z L L' M M' v c γ hM hz hL hL' hc hγ hmv i hi a ha
  obtain ⟨𝔞, h𝔞, -, hline⟩ := GlobalTheory.T.selfDualLattice_rationalLineTrace_fractionalIdeal D S₀ M z hM hz
  obtain ⟨x, hx, hgen⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔞 h𝔞
  have hA : ∀ b ∈ idAt D (· = v), b • ratV z ∈ latV S₀ M (· = v) ↔ incA D x⁻¹ * b ∈ intAt D (· = v) :=
    fun b hb => (hline v b hb).trans ((hgen b).trans ⟨fun h => h.1, fun h => ⟨h, hb⟩⟩)
  have hent : ∀ b ∈ idAt D (· = v), ∀ k, (b • ratV z) k ∈ idAt D (· = v) := fun b hb k => by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hb
  have hmove : ∀ b ∈ idAt D (· = v),
      b • ratV z ∈ latV S₀ M (· = v) ↔ (c * b) • ratV z ∈ latV S₀ M' (· = v) := by
    intro b hb
    rw [hmv _ (hent b hb), Matrix.mulVec_smul, hγ, smul_smul]
  have hcc : c * cA D c = 1 := hc.1
  have key : ∀ s ∈ idAt D (· = v),
      (∀ b ∈ idAt D (· = v), b • ratV z ∈ latV S₀ M (· = v) → colMul d.jX i (s * b) ∈ latV S L (· = v)) ↔
        (∀ b ∈ idAt D (· = v), b • ratV z ∈ latV S₀ M (· = v) →
          colMul d.jX i (c * (s * b)) ∈ latV S L' (· = v)) := by
    intro s hs
    rw [hL i hi s hs, ← hL' i hi s hs]
    constructor
    · intro h b hb hbM
      rw [show c * (s * b) = s * (c * b) by ring]
      exact h _ (Ideal.mul_mem_left _ _ hb) ((hmove b hb).1 hbM)
    · intro h b' hb' hb'M
      have hb : cA D c * b' ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ hb'
      have hcb : c * (cA D c * b') = b' := by rw [← mul_assoc, hcc, one_mul]
      have := h _ hb ((hmove _ hb).2 (by rw [hcb]; exact hb'M))
      rwa [show c * (s * (cA D c * b')) = s * (c * (cA D c * b')) by ring, hcb] at this
  exact cancel v x hx (fun b => b • ratV z ∈ latV S₀ M (· = v)) hA
    (fun t => colMul d.jX i t ∈ latV S L (· = v)) (fun t => colMul d.jX i (c * t) ∈ latV S L' (· = v))
    (fun o ho t ht => by
      show colMul d.jX i (o * t) ∈ latV S L (· = v)
      rw [colMul_mul]
      exact GlobalTheory.FinPlLoc.smul_latV v ho ht)
    (fun o ho t ht => by
      show colMul d.jX i (c * (o * t)) ∈ latV S L' (· = v)
      rw [mul_left_comm, colMul_mul]
      exact GlobalTheory.FinPlLoc.smul_latV v ho ht)
    key a ha

end GlobalTheory.Core.Mi.LastLine

end
