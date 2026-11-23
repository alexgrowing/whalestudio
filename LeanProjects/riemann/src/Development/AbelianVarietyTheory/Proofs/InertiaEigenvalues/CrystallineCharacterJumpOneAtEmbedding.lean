import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEmbOfFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantVectorExactFiltrationDegreeBcrisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysCharacterOfCrystallineVectorsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharacterJumpsOfExactDegreeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.HWL

theorem charRep_crys_jump_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (x : P.R.B), IsUnit x → (⇑P.φB)^[finrank ℚ_[l] ↥(K0 K)] x = (l : P.R.B) * x → P.ιB x ∈ (P.PD K).Fil 1 → P.ιB x ∉ (P.PD K).Fil 2 → (∀ j : ℕ, 0 < j → j < finrank ℚ_[l] ↥(K0 K) → P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil 0 ∧ P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil 1) → ∀ c : ↥(GK K) →* (↥(K0 K))ˣ, (∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x) → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → (∀ g : ↥(GK K), ((μ g : (↥LL.1)ˣ) : ↥LL.1) * τ₀ (algebraMap ↥(K0 K) ↥K.1 ((c g : (↥(K0 K))ˣ) : ↥(K0 K))) = 1) → IsCrys (P.PD K) (charRep μ) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = (if τ = τ₀ then 1 else 0) then 1 else 0 := by
  intro l _ P AI hT K LL hA τ₀ x hx _hφn hF1 hF2 hφj c hc μ hcont hμ
  let ι0 := IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1
  have hsurj : Function.Surjective ι0 := fun y =>
    ⟨⟨y.1, IntermediateField.mem_inf.2 ⟨y.2, hA.1 y.2⟩⟩, Subtype.ext rfl⟩
  obtain ⟨emb, hbij, hemb⟩ := GlobalTheory.HWL.exists_letters l P K 1 LL hA.2.2
  haveI : NeZero (finrank ℚ_[l] ↥(K0 K)) := ⟨by haveI := (P.PD K).finK₀; exact Module.finrank_pos.ne'⟩
  have hit : ∀ (j : ℕ) (i : ZMod (finrank ℚ_[l] ↥(K0 K))) (a : ↥(K0 K)),
      emb i ((⇑(P.PD K).σ)^[j] a) = emb (i - j) a := by
    intro j
    induction j with
    | zero => intro i a; simp
    | succ j ih =>
      intro i a
      rw [Function.iterate_succ_apply, ih]
      have h := DFunLike.congr_fun (hemb (i - j - 1)) a
      rw [sub_add_cancel] at h
      rw [AlgHom.comp_apply] at h
      rw [h]
      congr 1
      push_cast
      ring_nf
  obtain ⟨i₀, hi₀⟩ := hbij.2 (τ₀.comp ι0)
  have hμ' : ∀ g : ↥(GK K), ((μ g : (↥LL.1)ˣ) : ↥LL.1) * (τ₀.comp ι0) ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) = 1 :=
    fun g => hμ g
  have key : ∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ w ∈ DcrisL (P.PD K) (charRep μ) (τ.comp ι0),
      ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (if τ = τ₀ then 1 else 0) ∧
      ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) ((if τ = τ₀ then 1 else 0) + 1) := by
    intro τ
    obtain ⟨i, hi⟩ := hbij.2 (τ.comp ι0)
    have hj : ∀ a : ↥(K0 K), (τ.comp ι0) ((⇑(P.PD K).σ)^[(i - i₀).val] a) = (τ₀.comp ι0) a := by
      intro a
      rw [← hi, ← hi₀, hit, ZMod.natCast_zmod_val, sub_sub_cancel]
    by_cases hτ : τ = τ₀
    · subst hτ
      have h0 : (i - i₀).val = 0 := by
        rw [hbij.1 (hi.trans hi₀.symm), sub_self, ZMod.val_zero]
      rw [h0] at hj
      have := GlobalTheory.T.exists_invariant_vector_exact_filtrationDegree_Bcris l P AI hT K LL x hx c hc μ (τ.comp ι0) (τ.comp ι0) 0 hμ' hj 1
        (by simpa using hF1) (by simpa [show (1 : ℤ) + 1 = 2 by norm_num] using hF2)
      simpa using this
    · have hpos : 0 < (i - i₀).val := by
        rw [Nat.pos_iff_ne_zero]
        intro h0
        rw [ZMod.val_eq_zero, sub_eq_zero] at h0
        subst h0
        apply hτ
        have hc' : τ.comp ι0 = τ₀.comp ι0 := hi.symm.trans hi₀
        refine AlgHom.ext fun y => ?_
        obtain ⟨z, rfl⟩ := hsurj y
        exact DFunLike.congr_fun hc' z
      have hlt : (i - i₀).val < finrank ℚ_[l] ↥(K0 K) := ZMod.val_lt _
      obtain ⟨h1, h2⟩ := hφj _ hpos hlt
      have := GlobalTheory.T.exists_invariant_vector_exact_filtrationDegree_Bcris l P AI hT K LL x hx c hc μ (τ₀.comp ι0) (τ.comp ι0) (i - i₀).val hμ' hj 0
        h1 (by simpa using h2)
      simpa [hτ] using this
  have hcrys := GlobalTheory.T.isCrys_character_of_crystalline_vectors l P AI hT K LL hA μ hcont (fun τ => if τ = τ₀ then 1 else 0) key
  exact ⟨hcrys, GlobalTheory.T.crystalline_character_jumps_of_exact_degree l P AI hT K LL hA μ hcont (fun τ => if τ = τ₀ then 1 else 0) key hcrys⟩

end GlobalTheory.HWL
