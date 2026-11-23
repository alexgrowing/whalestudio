import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BadPrimeNormPrimeNeLevelPrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumSupportDivLatticeFinal

namespace GlobalTheory.LvT.Built.Box

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2
open GlobalTheory.ColPeriod GlobalTheory.LvT.Built.IsTerm

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ} {u : Pr.Word}

theorem pow_dvd_cA (P : rowSG Pr sel mu) : qOf P.1 ^ cst.A ∣ cAof sel mu cst :=
  pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem (fun Q : rowSG Pr sel mu => qOf Q.1) (Finset.mem_univ P)) _

theorem intAt_of_locTop (hL : L.Ok Ch sel mu cst G m2) (P : rowSG Pr sel mu) {j : ℕ} (hj : j = R.m)
    (x : HomE X.E (R.N (m2 + 1)) (R.N j)) (y : Sp X.E (R.N (m2 + 1)))
    (h : TopStep.locTop Ch sel mu cst m2 P (castSp X.E (congrArg R.N hj) ∘ₗ x) y ≠ 0) (s : Fin (R.N (m2 + 1))) (l : Fin (R.N j)) :
    IntAt P.1 ((qOf P.1 : X.E) ^ cst.A * x (Pi.single s 1) l) := by
  subst hj
  have hm := hL.hm
  rw [castSp_comp] at h
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
  have hl2 := l.2
  by_cases hlt : l.1 < R.N R.m - 1
  · have h3 := GlobalTheory.SuppTop.intAt_of_phiTop Ch mu cst.sharp _ hm P.1 _ h1 l.1 s.1 hlt s.2
    have e1 : LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) (Loc.eN X.E (R.N (m2 + 1) + cOf R (m2 + 1)) s.1) =
        Pi.single s 1 := by
      funext t
      simp [LinearMap.funLeft_apply, Loc.eN, Pi.single_apply, Fin.ext_iff]
    simp only [LinearMap.comp_apply, e1] at h3
    have hlt' : l.1 < R.N R.m - 1 + 0 := hlt
    simp only [Loc.atN, dif_pos hlt', prXp, LinearMap.funLeft_apply] at h3
    have h4 := (GlobalTheory.SuppTop.intAt_nat P.1 (qOf P.1 ^ cst.A)).mul h3
    rwa [Nat.cast_pow] at h4
  · have h3 := GlobalTheory.SuppTop.intAt_of_ftY sel mu cst P _ _ h2 s
    have hl3 : R.N R.m - 1 < R.N R.m := by omega
    have hl4 : (⟨R.N R.m - 1, hl3⟩ : Fin (R.N R.m)) = l := Fin.ext (by simp only; omega)
    simp only [LinearMap.comp_apply, atNL, dif_pos hl3, LinearMap.proj_apply, hl4] at h3
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hL.cst_ok.M_le_A
    have h4 := (GlobalTheory.SuppTop.intAt_nat P.1 (qOf P.1 ^ k)).mul h3
    rw [Nat.cast_pow, ← mul_assoc, ← pow_add] at h4
    rwa [hk]

theorem intAt_of_xiAt (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < R.m) {b : Idx sel mu L i} {b' : Idx sel mu L (i + 1)}
    {p : PtAt R sel mu cst u i} {p' : PtAt R sel mu cst u (i + 1)} {x : HomE X.E (R.N i) (R.N (i + 1))}
    (hx : xiAt Ch sel mu cst L u i b b' p p' x ≠ 0) (P : rowSG Pr sel mu) (s : Fin (R.N i)) (l : Fin (R.N (i + 1))) :
    IntAt P.1 ((qOf P.1 : X.E) ^ cst.A * inFr (frsF sel mu p.1.1 P) (frsF sel mu p'.1.1 P) x (Pi.single s 1) l) := by
  have hm := hL.hm
  rcases lt_trichotomy (i + 2) R.m with h | h | h
  · rw [xiAt_entry Ch sel mu cst L h (b.some_get (by omega)).symm (b'.some_get (by omega)).symm] at hx
    exact hL.xiSupp i (by omega) _ _ P _
      (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) P (Finset.mem_univ _)) s l
  · obtain rfl : i = m2 := by omega
    rw [xiAt_penultimate_eq_xiCpl1 Ch sel mu cst L h (b.some_get (by omega)).symm] at hx
    exact hL.psiSuppX _ P _ _ (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) P (Finset.mem_univ _)) s l
  · obtain rfl : i = m2 + 1 := by omega
    have h1 : m2 + 1 + 1 = R.m := by omega
    rw [xiAt_last Ch sel mu cst L h1] at hx
    exact intAt_of_locTop hL P h1 _ _ (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) P (Finset.mem_univ _)) s l

theorem inBox_xiAt : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → (∀ k, Pr.g k ∈ S) → L.Ok Ch sel mu cst G m2 → i < R.m → (∃ (σ₀ : X.K →+* ℂ) (e : Fin R.m → X.Tau → ℚ) (m0 : Fin R.m → Formalism.L2.Host.HChar X.E) (eta : Formalism.L2.Host.HChar X.E), Ch.Tied σ₀ e m0 eta) → ∀ (b : Idx sel mu L i) (b' : Idx sel mu L (i + 1)) (p : PtAt R sel mu cst u i) (p' : PtAt R sel mu cst u (i + 1)), GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.InBox (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.1.1.deco.1.N p'.1.1.deco.1.N (xiAt Ch sel mu cst L u i b b' p p') := by
  classical
  rintro X Pr R Ch sel S mu cst L G m2 u i hX hPr hsel hS hg hL hi ⟨σ₀, e, m0, eta, ht⟩ b b' p p'
  refine ⟨fun x hx P hP y hy => ?_, fun x y hy => ?_⟩
  · change ((cAof sel mu cst : ℕ) : 𝓞 X.E) • x y ∈ _
    have hP' : P ∈ Pr.vT u ∨ P ∈ rowSG Pr sel mu := by
      unfold Sall at hP
      exact Finset.mem_union.1 hP
    rcases hP' with hP | hP
    · exact Submodule.smul_mem _ _ (phiT_of_xiAt_ne_zero Ch sel mu cst L hx ⟨P, hP⟩ y hy).1
    · obtain ⟨k, hk⟩ : qOf P ^ cst.A ∣ cAof sel mu cst :=
        pow_dvd_cA ⟨P, hP⟩
      have h := GlobalTheory.SuppTop.smul_mem_of_inFr P _ _ _ _ (isFrames_frsF p.1.1 ⟨P, hP⟩) (isFrames_frsF p'.1.1 ⟨P, hP⟩)
        (cAof sel mu cst) x (fun s l => by
          have h4 := (GlobalTheory.SuppTop.intAt_nat P k).mul (intAt_of_xiAt hL hi hx ⟨P, hP⟩ s l)
          rw [hk, Nat.cast_mul, Nat.cast_pow, mul_comm _ (k : X.E), mul_assoc]
          exact h4) y hy
      simpa [Nat.cast_smul_eq_nsmul] using h
  · obtain ⟨Φ, hΦ⟩ := exists_local hX hPr hsel hS hL (muqUnit_of_tied hX hPr hsel hS hg hL ht) hi b b'
    obtain ⟨w, hw⟩ := exists_place X.K (hPr.T_prime u)
    rw [(hΦ p p').1, (hΦ p p').1]
    congr 1
    · exact phiT_add _ p'.1.1.deco.2 (T := Pr.T u) (fun Q => T_mem_of_piT_mem hPr u (GlobalTheory.ColPeriod.mem_divs Q.2)) x fun Q =>
        exists_of_mem_mulLat (Dvd.intro _ rfl) hy (Finset.mem_union_left _ Q.2)
    · refine Finset.prod_congr rfl fun P _ => ?_
      have hdv : qOf P.1 ^ cst.B ∣ cBof sel mu cst u :=
        Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ P)) _) _
      obtain ⟨z, hz, rfl⟩ := exists_of_mem_mulLat hdv hy (Finset.mem_union_right _ P.2)
      rw [Nat.cast_pow]
      exact (awayAt_inFr (isFrames_frsF p.1.1 P) (isFrames_frsF p'.1.1 P) ((hΦ p p').2 P w hw)).2 x z hz

end GlobalTheory.LvT.Built.Box
