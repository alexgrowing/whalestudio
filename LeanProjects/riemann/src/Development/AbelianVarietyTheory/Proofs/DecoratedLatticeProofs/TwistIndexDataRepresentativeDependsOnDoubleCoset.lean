import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.TwBridge

open Classical in

theorem twNext_rep_eq_of_sameDC {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ} (mu : Tup X.F X.E X.K S₀)
    (cst : LocCst X (rowSG Pr sel mu)) {i : ℕ} (st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i)
    (hinj : ∀ d d' : (twNext Ch sel mu cst st).β, (∀ P : rowSG Pr sel mu,
      SameDC (Pr := Pr) cst.sharp (i + 1) P.1 ((twNext Ch sel mu cst st).h d P) ((twNext Ch sel mu cst st).h d' P)) → d = d')
    (d d' : (twNext Ch sel mu cst st).β) (P : rowSG Pr sel mu)
    (hs : SameDC (Pr := Pr) cst.sharp (i + 1) P.1 ((twNext Ch sel mu cst st).h d P) ((twNext Ch sel mu cst st).h d' P)) :
    (twNext Ch sel mu cst st).h d P = (twNext Ch sel mu cst st).h d' P := by
  by_cases hP : P.1 ∈ twQOff (Pr := Pr) sel mu
  · let P₀ : twQOff (Pr := Pr) sel mu := ⟨P.1, hP⟩
    let d'' : (twNext Ch sel mu cst st).β := ⟨Function.update d.1 P₀ (d'.1 P₀), d.2⟩
    have hall : ∀ Q : rowSG Pr sel mu, SameDC (Pr := Pr) cst.sharp (i + 1) Q.1
        ((twNext Ch sel mu cst st).h d Q) ((twNext Ch sel mu cst st).h d'' Q) := by
      intro Q
      by_cases hQ : Q.1 ∈ twQOff (Pr := Pr) sel mu
      · by_cases e : (⟨Q.1, hQ⟩ : twQOff (Pr := Pr) sel mu) = P₀
        · have hQP1 : Q.1 = P.1 := congrArg (fun x : twQOff (Pr := Pr) sel mu => x.1) e
          have hQP : Q = P := Subtype.ext hQP1
          rw [hQP]
          have e1 : (twNext Ch sel mu cst st).h d'' P = (twNext Ch sel mu cst st).h d' P := by
            simp only [twNext, dif_pos hP, d'']
            rw [Function.update_self]
          rw [e1]; exact hs
        · have e1 : (twNext Ch sel mu cst st).h d'' Q = (twNext Ch sel mu cst st).h d Q := by
            simp only [twNext, dif_pos hQ, d'']
            rw [Function.update_of_ne e]
          rw [e1]; exact twDC_refl _ _ _ _
      · have e1 : (twNext Ch sel mu cst st).h d'' Q = (twNext Ch sel mu cst st).h d Q := by
          simp only [twNext, dif_neg hQ]
        rw [e1]; exact twDC_refl _ _ _ _
    have hdd := hinj d d'' hall
    have hc : d.1 P₀ = d'.1 P₀ := by
      have := congrArg (fun x : (twNext Ch sel mu cst st).β => x.1 P₀) hdd
      simpa [d''] using this
    simp only [twNext, dif_pos hP]
    exact congrArg (fun D => twRep Ch sel mu cst st P₀ D.1) hc
  · simp only [twNext, dif_neg hP]

theorem idxProd_twIdx : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (m2 : ℕ) (G : ChGlob X R.m), (twIdx Ch sel mu cst m2).Ok Ch sel mu cst G m2 → IdxProd sel mu cst (twIdx Ch sel mu cst m2) := by
  intro X Pr R Ch sel S₀ mu cst m2 G hok j b b' P hs
  rcases j with _ | i
  · rfl
  · by_cases hi : i + 1 ≤ m2
    · have key : ∀ st' : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) (i + 1), st' = twNext Ch sel mu cst (twSt Ch sel mu cst m2 i) →
          ∀ b b' : st'.β, (∀ b b' : st'.β, (∀ P : rowSG Pr sel mu,
            SameDC (Pr := Pr) cst.sharp (i + 1) P.1 (st'.h b P) (st'.h b' P)) → b = b') →
          SameDC (Pr := Pr) cst.sharp (i + 1) P.1 (st'.h b P) (st'.h b' P) → st'.h b P = st'.h b' P := by
        rintro st' rfl b b' hinj hs
        exact twNext_rep_eq_of_sameDC Ch sel mu cst _ hinj b b' P hs
      exact key (twSt Ch sel mu cst m2 (i + 1)) (by rw [twSt, if_pos hi]) b b' (hok.inj i (by omega)) hs
    · by_cases hi2 : i + 1 = m2 + 1
      · have key : ∀ st' : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) (i + 1), st' = twUnitSt _ (i + 1) →
            ∀ b b' : st'.β, st'.h b P = st'.h b' P := by
          rintro st' rfl b b'; rfl
        exact key (twSt Ch sel mu cst m2 (i + 1)) (by rw [twSt, if_neg hi, if_pos hi2]) b b'
      · have key : ∀ st' : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) (i + 1), st' = twEmptySt _ (i + 1) →
            ∀ b b' : st'.β, st'.h b P = st'.h b' P := by
          rintro st' rfl b; exact b.elim
        exact key (twSt Ch sel mu cst m2 (i + 1)) (by rw [twSt, if_neg hi, if_neg hi2]) b b'

end GlobalTheory.TwBridge
