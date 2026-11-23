import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistedStartColumnReading
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelGroupNeTopNeBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlkDetEqDB
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.TopXiInv

open Formalism.L2.Col.LocE Formalism.L2.Col.Loc

theorem xiTop_invariant : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (m2 : ℕ) (u : Pr.Word), Pr.Ok → R.m = m2 + 2 → cst.Ok → (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) → ∀ (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (p' : TopPt R sel mu u), Y ∈ ybSet sel mu cst p.deco.1.N → ∀ x z, z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) → XiTop Ch sel mu cst m2 p Y p' (x + z) = XiTop Ch sel mu cst m2 p Y p' x := by
  classical
  intro X Pr R Ch sel S mu cst m2 u hPr hm hc hD p Y p' hY x y hy
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  set c : ℕ := cBof sel mu cst u with hcdef
  change XiTop Ch sel mu cst m2 p Y p' (x + (c : 𝓞 X.E) • y₀) = _
  unfold XiTop
  refine congrArg₂ (· * ·) ?_ ?_
  · refine GlobalTheory.TopInv.phiT_add _ _ p'.deco.2 x y₀ _ (fun P => ?_) fun P v hv => hy₀ P.1 (Finset.mem_union_left _ P.2) v hv
    have h1 : Pr.piT u ∈ P.1.asIdeal := by
      have h := P.2
      unfold Primes.vT divs at h
      split_ifs at h with hf
      · simpa using h
      · simp at h
    rw [hcdef, cBof, Nat.cast_mul, ← hPr.piT_norm]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h1)
  · refine Finset.prod_congr rfl fun P _ => ?_
    have hq0 := GlobalTheory.TopInv.qOf_ne P.1
    rw [GlobalTheory.TopInv.inFr_add]
    generalize inFr (frsF sel mu p P) (frsF sel mu p' P) x = x'
    have hz : ∀ v : Sp X.E (R.N (m2 + 1)), (∀ l, IntAt P.1 (v l)) → ∀ l,
        IntAt P.1 (inFr (frsF sel mu p P) (frsF sel mu p' P) ((c : 𝓞 X.E) • y₀) v l / (qOf P.1 : X.E) ^ cst.B) := by
      intro v hv l
      have h1 : frsF sel mu p P v ∈ p.deco.1.at P.1 := (frsF_mem p P v).2 ((mem_localization_standardLattice _ _).2 hv)
      have h2 := hy₀ P.1 (Finset.mem_union_right _ P.2) _ h1
      have h3 : (frsF sel mu p' P).symm (y₀ (frsF sel mu p P v)) ∈ stdAt X.E _ P.1 := by
        refine (frsF_mem p' P _).1 ?_
        rw [LinearEquiv.apply_symm_apply]
        exact h2
      have h4 := (mem_localization_standardLattice _ _).1 h3 l
      obtain ⟨c', hc'⟩ : qOf P.1 ^ cst.B ∣ c :=
        Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem (fun Q : rowSG Pr sel mu => qOf Q.1) (Finset.mem_univ P)) _) _
      have h5 : inFr (frsF sel mu p P) (frsF sel mu p' P) ((c : 𝓞 X.E) • y₀) v l =
          (c : X.E) * (frsF sel mu p' P).symm (y₀ (frsF sel mu p P v)) l := by
        change (frsF sel mu p' P).symm ((c : 𝓞 X.E) • y₀ (frsF sel mu p P v)) l = _
        rw [equiv_osmul, Nat.cast_smul_eq_nsmul, Pi.smul_apply, nsmul_eq_mul]
      rw [h5, hc']
      convert (GlobalTheory.TopInv.intAt_nat (P := P.1) c').mul h4 using 1
      push_cast
      field_simp
    generalize inFr (frsF sel mu p P) (frsF sel mu p' P) ((c : 𝓞 X.E) • y₀) = z at hz ⊢
    unfold locTop
    rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_add]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine GlobalTheory.TopInv.PhiTop_add mu Ch _ _ hm P.1 _ _ fun s l => ?_
      have h1 := hz (LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) (Pi.single s 1)) fun l' =>
        GlobalTheory.TopInv.single_int s _
      have h2 := GlobalTheory.TopInv.intAt_div_pow_le hq0 hc.B_pos (h1 (Br.iC (N_m_succ R) l))
      rw [pow_one] at h2
      exact h2
    · refine GlobalTheory.TopInv.ftY_add sel mu cst hc P (hD P) _ _ _ (fun s => ?_) ?_
      · exact GlobalTheory.TopInv.atNL_int (R.N R.m - 1) _ _ (hz (Pi.single s 1) (GlobalTheory.TopInv.single_int s))
      · have h1 := GlobalTheory.TopInv.repY_mem sel mu cst _ _ hY P
        have h2 := (frsF_mem p P ((frsF sel mu p P).symm
          (((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M)) • repY Y))).1 (by
            rw [LinearEquiv.apply_symm_apply]
            exact h1)
        intro l
        have h3 := (mem_localization_standardLattice _ _).1 h2 l
        rw [map_smul] at h3
        exact h3

end GlobalTheory.TopXiInv
