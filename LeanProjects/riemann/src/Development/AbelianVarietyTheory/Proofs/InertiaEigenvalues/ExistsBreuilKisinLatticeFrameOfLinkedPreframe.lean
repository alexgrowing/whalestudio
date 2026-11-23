import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfPrincipalIdealSaturatedClosedStatement
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
namespace GlobalTheory.BKLim

theorem frame_of_links : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val) (P : Pre bk N d fun g => (ρ g).val) (r : ℕ), (∀ n, ∃ m, n ≤ m ∧ Link bk P.T (F m).T (tw.Pi m) n r) → ∃ F₀ : Frame bk N d fun g => (ρ g).val, F₀.toPre = P := by
  intro l _ K bk d N ρ tw F P r hL
  obtain ⟨u, hu⟩ := P.unit
  obtain ⟨Ti, hT1, hT2⟩ : ∃ Ti : Matrix (Fin d) (Fin d) (WCb l), P.T * Ti = 1 ∧ Ti * P.T = 1 :=
    ⟨↑u⁻¹, by rw [← hu]; exact u.mul_inv, by rw [← hu]; exact u.inv_mul⟩
  have key : ∀ (g : ↥(GK K)) (i j : Fin d), ∃ a : Ainf l,
      (Ti * zW (ρ g).val * P.T.map (galW l (g : GQ l))) i j
        = inclW l (1 * a) := by
    intro g i j
    refine GlobalTheory.T.ainf_principal_ideal_saturated_closed l 1 (by simp) r _ ?_
    intro n
    obtain ⟨m, hnm, R, G, hc, hd⟩ := hL n
    obtain ⟨σ, hσ⟩ : ∃ σ : WCb l →+* WCb l, ∀ x, σ x = galW l (g : GQ l) x := ⟨((galW l (g : GQ l)).toRingEquiv : WCb l →+* WCb l), fun _ => rfl⟩
    have hσf : (⇑(galW l (g : GQ l)) : WCb l → WCb l) = ⇑σ := funext fun x => (hσ x).symm
    set π := Ideal.Quotient.mk (Ideal.span {((l : WCb l) ^ n)}) with hπ
    have hq : ∀ x y : WCb l, (l : WCb l) ^ n ∣ x - y → π x = π y := fun x y h =>
      Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 h)
    have hM : ∀ {a b : Type} (A B : Matrix a b (WCb l)),
        (∀ i j, (l : WCb l) ^ n ∣ (A - B) i j) → A.map π = B.map π := fun A B h => by
      ext i j; exact hq _ _ (by simpa using h i j)
    have hσd : ∀ x : WCb l, (l : WCb l) ^ n ∣ x → (l : WCb l) ^ n ∣ σ x := fun x ⟨y, hy⟩ =>
      ⟨σ y, by rw [hy, map_mul, map_pow, map_natCast]⟩
    have hσz : ∀ {a b : Type} (M : Matrix a b ℤ_[l]), (zW M).map σ = zW M := fun M => by
      ext i j; simp [zW, hσ]
    have hMM : ∀ {a b b' c : Type} [Fintype b] [Fintype b'] (A : Matrix a b (WCb l)) (B : Matrix b c (WCb l))
        (C : Matrix a b' (WCb l)) (D : Matrix b' c (WCb l)),
        (∀ i j, (l : WCb l) ^ n ∣ (A * B - C * D) i j) → A.map π * B.map π = C.map π * D.map π := by
      intro a b b' c _ _ A B C D h
      rw [← Matrix.map_mul, ← Matrix.map_mul]; exact hM _ _ h
    set T' := (F m).T
    set ε' := (F m).ε g
    set Pi := tw.Pi m
    have Ga := (F m).gal g
    rw [hσf] at Ga
    rw [hσf]
    have E1 : (zW Pi).map π * T'.map π = P.T.map π * (R.map bk.evW).map π := by
      rw [← Matrix.map_mul, ← Matrix.map_mul]; exact hM _ _ hc
    have E1σ : (zW Pi).map π * (T'.map σ).map π = (P.T.map σ).map π * ((R.map bk.evW).map σ).map π := by
      rw [← Matrix.map_mul, ← Matrix.map_mul]
      apply hM
      intro i j
      have h1 : zW Pi * T'.map σ - P.T.map σ * (R.map bk.evW).map σ = (zW Pi * T' - P.T * R.map bk.evW).map σ := by
        rw [Matrix.map_sub _ (map_sub σ), Matrix.map_mul, Matrix.map_mul, hσz]
      rw [h1, Matrix.map_apply]; exact hσd _ (hc i j)
    have E2 : (zW Pi).map π * (zW (tw.ρ' m g).val).map π = (zW (ρ g).val).map π * (zW Pi).map π := by
      apply hMM
      intro i j
      have h1 : zW Pi * zW (tw.ρ' m g).val - zW (ρ g).val * zW Pi = zW (Pi * (tw.ρ' m g).val - (ρ g).val * Pi) := by
        simp only [zW]; rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul]
      rw [h1]
      have h2 := map_dvd (algebraMap ℤ_[l] (WCb l)) ((pow_dvd_pow (l : ℤ_[l]) hnm).trans ((tw.onto m).equi g i j))
      simpa [zW] using h2
    have E3 : ((R.map bk.evW).map σ).map π * ((G.map bk.evW).map σ).map π
        = (((l : WCb l) ^ r) • (1 : Matrix (Fin d) (Fin d) (WCb l))).map π := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul]
      apply hM
      intro i j
      have h1 : (((R * G).map bk.evW).map σ - ((l : WCb l) ^ r) • (1 : Matrix (Fin d) (Fin d) (WCb l))) i j
          = σ (bk.evW ((R * G - (l : bk.S) ^ r • (1 : Matrix (Fin d) (Fin d) bk.S)) i j)) := by
        simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, map_sub]
        split_ifs <;> simp
      rw [h1]
      exact hσd _ (by simpa using map_dvd bk.evW (hd i j))
    have He : P.T.map π * ((Ti * zW (ρ g).val * P.T.map σ).map π) = (zW (ρ g).val).map π * (P.T.map σ).map π := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hT1, Matrix.one_mul]
    have GaP : (zW (tw.ρ' m g).val).map π * (T'.map σ).map π = T'.map π * (ε'.map (inclW l)).map π := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, Ga]
    have C1 : P.T.map π * ((Ti * zW (ρ g).val * P.T.map σ).map π * ((R.map bk.evW).map σ).map π)
        = P.T.map π * ((R.map bk.evW).map π * (ε'.map (inclW l)).map π) := by
      calc P.T.map π * ((Ti * zW (ρ g).val * P.T.map σ).map π * ((R.map bk.evW).map σ).map π)
          = (P.T.map π * (Ti * zW (ρ g).val * P.T.map σ).map π) * ((R.map bk.evW).map σ).map π := (Matrix.mul_assoc _ _ _).symm
        _ = (zW (ρ g).val).map π * ((P.T.map σ).map π * ((R.map bk.evW).map σ).map π) := by rw [He, Matrix.mul_assoc]
        _ = (zW (ρ g).val).map π * ((zW Pi).map π * (T'.map σ).map π) := by rw [E1σ]
        _ = ((zW Pi).map π * (zW (tw.ρ' m g).val).map π) * (T'.map σ).map π := by rw [E2, Matrix.mul_assoc]
        _ = (zW Pi).map π * (T'.map π * (ε'.map (inclW l)).map π) := by rw [Matrix.mul_assoc, GaP]
        _ = P.T.map π * ((R.map bk.evW).map π * (ε'.map (inclW l)).map π) := by rw [← Matrix.mul_assoc, E1, Matrix.mul_assoc]
    have hTi : Ti.map π * P.T.map π = 1 := by
      rw [← Matrix.map_mul, hT2, Matrix.map_one _ (map_zero _) (map_one _)]
    have C2 : (Ti * zW (ρ g).val * P.T.map σ).map π * ((R.map bk.evW).map σ).map π
        = (R.map bk.evW).map π * (ε'.map (inclW l)).map π := by
      calc _ = (Ti.map π * P.T.map π) *
            ((Ti * zW (ρ g).val * P.T.map σ).map π * ((R.map bk.evW).map σ).map π) := by rw [hTi, Matrix.one_mul]
        _ = _ := by rw [Matrix.mul_assoc, C1, ← Matrix.mul_assoc, hTi, Matrix.one_mul]
    have C3 : (Ti * zW (ρ g).val * P.T.map σ).map π * (((R.map bk.evW).map σ).map π * ((G.map bk.evW).map σ).map π)
        = (R.map bk.evW).map π * (ε'.map (inclW l)).map π * ((G.map bk.evW).map σ).map π := by
      rw [← Matrix.mul_assoc, C2]
    rw [E3] at C3
    have hR : (R.map bk.ev).map (inclW l) = R.map bk.evW := by ext; rfl
    have hG : (G.map fun x => Per.σA (g : GQ l) (bk.ev x)).map (inclW l) = (G.map bk.evW).map σ := by
      ext; simp [BK.evW, hσ, galW_inclW]
    have hY : ((R.map bk.ev * ε' * G.map fun x => Per.σA (g : GQ l) (bk.ev x)).map (inclW l)).map π
        = (R.map bk.evW).map π * (ε'.map (inclW l)).map π * ((G.map bk.evW).map σ).map π := by
      simp only [Matrix.map_mul, hR, hG]
    refine ⟨(R.map bk.ev * ε' * G.map fun x => Per.σA (g : GQ l) (bk.ev x)) i j, ?_⟩
    have C4 : (((l : WCb l) ^ r) • (Ti * zW (ρ g).val * P.T.map σ)).map π
        = ((R.map bk.ev * ε' * G.map fun x => Per.σA (g : GQ l) (bk.ev x)).map (inclW l)).map π := by
      rw [hY, ← C3, ← Matrix.map_mul, Matrix.mul_smul, mul_one]
    have C5 := congrFun (congrFun C4 i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at C5
    rw [one_mul]
    exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 C5)
  choose ε hε using key
  refine ⟨{ toPre := P, ε := fun g => Matrix.of (ε g), gal := fun g => ?_ }, rfl⟩
  have h1 : (Matrix.of (ε g)).map (inclW l) = Ti * zW (ρ g).val * P.T.map (galW l (g : GQ l)) := by
    ext i j; rw [Matrix.map_apply, Matrix.of_apply, hε g i j, one_mul]
  show zW (ρ g).val * P.T.map (galW l (g : GQ l)) = P.T * (Matrix.of (ε g)).map (inclW l)
  rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hT1, Matrix.one_mul]

end GlobalTheory.BKLim
