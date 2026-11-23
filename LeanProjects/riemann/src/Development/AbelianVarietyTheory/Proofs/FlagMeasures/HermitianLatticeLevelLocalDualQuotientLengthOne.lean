import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitCompletelyPlaceStructure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceDualQuotientComponentsIffStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimeSqLeLocalHermitianDualIndexStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalHermitianDualQuotientCyclicSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdLocalRelIndexDvdHermitianDualStatement

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem tidx_arith {ι : Type} (s : Finset ι) (r : ι → ℕ) (T f : ℕ) (hT : T.Prime) (hcard : s.card = f)
    (hdvd : ∏ i ∈ s, r i ∣ T ^ (2 * f)) (hlow : ∀ i ∈ s, r i ≠ 0 → T ^ 2 ≤ r i) : ∀ i ∈ s, r i = T ^ 2 := by
  have hT0 : 0 < T := hT.pos
  have hpow0 : T ^ (2 * f) ≠ 0 := pow_ne_zero _ hT.ne_zero

  have hprod0 : ∏ i ∈ s, r i ≠ 0 := by
    intro h
    rw [h] at hdvd
    exact hpow0 (zero_dvd_iff.mp hdvd)
  have hge : ∀ i ∈ s, T ^ 2 ≤ r i := fun i hi =>
    hlow i hi (fun h => hprod0 (Finset.prod_eq_zero hi h))

  have hle : ∏ i ∈ s, r i ≤ ∏ _i ∈ s, T ^ 2 := by
    rw [Finset.prod_const, hcard, ← pow_mul]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hpow0) hdvd
  intro i hi
  by_contra hne
  have hlt : ∏ _i ∈ s, T ^ 2 < ∏ i ∈ s, r i :=
    Finset.prod_lt_prod (fun j _ => pow_pos hT0 2) hge ⟨i, hi, lt_of_le_of_ne (hge i hi) (Ne.symm hne)⟩
  exact absurd hle (not_le.mpr hlt)

theorem tLat_local_index : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → (loc v L).toAddSubgroup.relIndex (loc v (dualL cm.sig J L)).toAddSubgroup = T ^ 2 ∧ ∃ d ∈ loc v (dualL cm.sig J L), ∀ x ∈ loc v (dualL cm.sig J L), ∃ a ∈ intV E v, x - a • d ∈ loc v L := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f L hT hs hdeg hL v hv
  obtain ⟨hncard, hloc⟩ := GlobalTheory.St.G.SplitPrime.split_place F E cm T hT hs

  have hF : Module.finrank ℚ F = f := by
    have h := Module.finrank_mul_finrank ℚ F E
    rw [cm.deg2, hdeg] at h
    omega
  have hfin : {w : HeightOneSpectrum (𝓞 F) | (T : 𝓞 F) ∈ w.asIdeal}.Finite :=
    Set.finite_of_ncard_pos (by rw [hncard]; exact Module.finrank_pos)
  have hcard : hfin.toFinset.card = f := by
    rw [← Set.ncard_eq_toFinset_card _ hfin, hncard, hF]

  have hlow : ∀ w ∈ hfin.toFinset,
      (loc w L).toAddSubgroup.relIndex (loc w (dualL cm.sig J L)).toAddSubgroup ≠ 0 →
      T ^ 2 ≤ (loc w L).toAddSubgroup.relIndex (loc w (dualL cm.sig J L)).toAddSubgroup := by
    intro w hw h0
    have hw' : (T : 𝓞 F) ∈ w.asIdeal := (Set.Finite.mem_toFinset hfin).mp hw
    obtain ⟨_, _, sp, hsp1, hsp2⟩ := hloc w hw'
    exact GlobalTheory.T.prime_sq_le_local_hermitian_dual_index F E cm n J hJ hdet T f L hT hs hdeg hL w hw' sp hsp1 hsp2
      (GlobalTheory.T.split_place_dual_quotient_components_iff F E cm n J hJ hdet T f L hT hs hdeg hL w hw' sp hsp1 hsp2) h0

  have hdvd := GlobalTheory.T.prod_local_relIndex_dvd_hermitian_dual F E cm n J hJ hdet T f L hT hs hdeg hL hfin.toFinset
    (fun w hw => (Set.Finite.mem_toFinset hfin).mp hw)
  rw [hL.2.2.2.1] at hdvd
  have heq := tidx_arith hfin.toFinset
    (fun w => (loc w L).toAddSubgroup.relIndex (loc w (dualL cm.sig J L)).toAddSubgroup)
    T f hT hcard hdvd hlow v ((Set.Finite.mem_toFinset hfin).mpr hv)
  refine ⟨heq, ?_⟩
  obtain ⟨_, _, sp, hsp1, hsp2⟩ := hloc v hv
  exact GlobalTheory.T.local_hermitian_dual_quotient_cyclic_split_place F E cm n J hJ hdet T f L hT hs hdeg hL v hv sp hsp1 hsp2
    (GlobalTheory.T.split_place_dual_quotient_components_iff F E cm n J hJ hdet T f L hT hs hdeg hL v hv sp hsp1 hsp2) heq

end GlobalTheory.St.G
