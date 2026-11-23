import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepInclStepProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepModuleZeroOfUnitDetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepSequenceShortExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepProjectionEpiLocalTriangularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepSubmoduleRegularSectionsStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx

namespace GlobalTheory.FlagChi
open Matrix

theorem stepC_top {Z : Scheme.{0}} [IsIntegral Z] {N : ℕ} (M M' : Matrix (Fin N) (Fin N) Z.functionField) :
    stepC M N = stepC M' N := by
  funext x
  ext v
  exact ⟨fun _ k hk => absurd hk (not_le.2 k.2), fun _ k hk => absurd hk (not_le.2 k.2)⟩

theorem vsec_step_le_quot {Z : Scheme.{0}} [IsIntegral Z] {N : ℕ} {M : Matrix (Fin N) (Fin N) Z.functionField}
    {l : Fin N} {L : LB Z} {r : L.ι → Z.functionFieldˣ}
    (h : ∀ (x : Z) (v : Fin N → Z.functionField), v ∈ stepSub M ((l : ℕ) + 1) → (∀ a, RegAt x (v a)) →
      ∀ c, x ∈ L.U c → RegAt x ((M *ᵥ v) l * r c)) (V : Z.Opens) :
    vsec (stepC M ((l : ℕ) + 1)) V = vsec (quotC M l L r) V := by
  ext v
  refine ⟨fun hv hg x hx => ⟨hv hg x hx, fun c hc => h x _ (hv hg x hx) (fun a => regAt_fnOf hx hg (v a)) c hc⟩,
    fun hv hg x hx => (hv hg x hx).1⟩

theorem chiPic_isZero {Z : Scheme.{0}} (k : Type) [Field k] [Algebra k Γ(Z, ⊤)] {F : Z.Modules}
    (hF : Limits.IsZero F) (c : CechPic.Pic Z) : chiPic k F c = 0 := by
  obtain ⟨M, hM, rfl⟩ := CechPic.cls_surj c
  rw [chiPic_cls]
  exact chi_eq_zero_of_isZero k ((Twist.isZero_twist_iff hM).2 hF)

theorem chiPic_top (k : Type) [Field k] {Z : Scheme.{0}} [IsIntegral Z] [Algebra k Γ(Z, ⊤)]
    (hO : FiniteCohTwists k (structureModule Z)) {N : ℕ} (G : Fin N → LB Z) (hG : ∀ i, (G i).IsLB)
    (r : ∀ i, (G i).ι → Z.functionFieldˣ) (A : Matrix (Fin N) (Fin N) Z.functionField)
    (hr : ∀ i, IsRatSec (G i) (r i)) (hA : IsUnit A.det)
    (hB : ∀ z : Z, ∃ B : Matrix (Fin N) (Fin N) Z.functionField, B.BlockTriangular id ∧
      (∀ a b, RegAt z ((A * B) a b)) ∧ UnitAt z (A * B).det ∧
        ∀ i c, z ∈ (G i).U c → UnitAt z (B i i * r i c)) :
    FiniteCohTwists k (stepMod A⁻¹ N) ∧ ∀ c, chiPic k (stepMod A⁻¹ N) c =
      ∑ i, chiPic k (structureModule Z) (cls (G i) (hG i) + c) := by
  have key : ∀ l : ℕ, l ≤ N → FiniteCohTwists k (stepMod A⁻¹ l) ∧ ∀ c, chiPic k (stepMod A⁻¹ l) c =
      ∑ i : Fin N, if (i : ℕ) < l then chiPic k (structureModule Z) (cls (G i) (hG i) + c) else 0 := by
    intro l
    induction l with
    | zero =>
      intro _
      have hz := GlobalTheory.T.step_module_zero_of_unit_det Z N A⁻¹ (by rw [Matrix.det_nonsing_inv]; exact hA.ringInverse)
      exact ⟨FiniteCohTwists.of_isZero hz, fun c => by
        rw [chiPic_isZero k hz c]; simp⟩
    | succ l ih =>
      intro hl
      obtain ⟨h₁, e₁⟩ := ih (by omega)
      let i : Fin N := ⟨l, by omega⟩
      have hBi : ∀ z : Z, ∃ B : Matrix (Fin N) (Fin N) Z.functionField, B.BlockTriangular id ∧
          (∀ a b, RegAt z ((A * B) a b)) ∧ UnitAt z (A * B).det ∧
            ∀ c, z ∈ (G i).U c → UnitAt z (B i i * r i c) := fun z =>
        have ⟨B, h1, h2, h3, h4⟩ := hB z
        ⟨B, h1, h2, h3, h4 i⟩
      have hS := GlobalTheory.T.step_sequence_short_exact Z N A⁻¹ i (G i) (r i) (hr i) (hG i) (GlobalTheory.T.step_projection_epi_local_triangular Z N A i (G i) (r i) (hr i) (hG i) hA hBi)
      have h₃ : FiniteCohTwists k (LB.toMod (G i)) :=
        (hO.twist (hG i)).of_iso (Twist.unitTwistIso (G i))
      have h₂ : FiniteCohTwists k (quotMod A⁻¹ i (G i) (r i)) :=
        FiniteCohTwists.of_shortExact₂ hS h₁ h₃
      have hadd := chiPic_shortExact hS h₁ h₃
      have e := viso (vsec_step_le_quot (GlobalTheory.T.step_submodule_regular_sections Z N A i (G i) (r i) hA hBi))
      refine ⟨h₂.of_iso e.symm, fun c => ?_⟩
      have e₂ : chiPic k (stepMod A⁻¹ (l + 1)) c = chiPic k (quotMod A⁻¹ i (G i) (r i)) c :=
        congrFun (chiPic_congr k e) c
      have e₃ : chiPic k (LB.toMod (G i)) c = chiPic k (structureModule Z) (cls (G i) (hG i) + c) :=
        (congrFun (chiPic_congr k (Twist.unitTwistIso (G i))) c).symm.trans (chiPic_twist k _ (hG i) c)
      rw [e₂]
      have h4 := congrFun hadd c
      rw [Pi.add_apply] at h4
      refine h4.trans ?_
      change chiPic k (stepMod A⁻¹ l) c + chiPic k (LB.toMod (G i)) c = _
      rw [e₁ c, e₃]
      have hi : (i : ℕ) = l := rfl
      have hsplit : ∀ j : Fin N, (if (j : ℕ) < l + 1 then
          chiPic k (structureModule Z) (cls (G j) (hG j) + c) else 0) =
          (if (j : ℕ) < l then chiPic k (structureModule Z) (cls (G j) (hG j) + c) else 0) +
            (if j = i then chiPic k (structureModule Z) (cls (G j) (hG j) + c) else 0) := by
        intro j
        rcases lt_trichotomy (j : ℕ) l with h | h | h
        · rw [if_pos (by omega), if_pos h, if_neg (fun e => by
            have := congrArg Fin.val e; rw [hi] at this; omega), add_zero]
        · rw [if_pos (by omega), if_neg (by omega), if_pos (Fin.ext (h.trans hi.symm)), zero_add]
        · rw [if_neg (by omega), if_neg (by omega), if_neg (fun e => by
            have := congrArg Fin.val e; rw [hi] at this; omega), add_zero]
      rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib, Finset.sum_ite_eq',
        if_pos (Finset.mem_univ _)]
  obtain ⟨h, e⟩ := key N le_rfl
  exact ⟨h, fun c => (e c).trans (Finset.sum_congr rfl fun i _ => if_pos i.2)⟩

end GlobalTheory.FlagChi

open GlobalTheory.FlagChi in

theorem GlobalTheory.FlagChi.sum_chiPic_flag : ∀ (k : Type) [Field k] (Z : Scheme.{0}) [IsIntegral Z] [Algebra k Γ(Z, ⊤)], FiniteCohTwists k (structureModule Z) → ∀ (N : ℕ) (g : Fin N → Pic Z), FlagOfTriv g → ∀ c : Pic Z, ∑ i, chiPic k (structureModule Z) (g i + c) = (N : ℤ) * chiPic k (structureModule Z) c := by
  intro k _ Z _ _ hO N g hg c
  obtain ⟨G, hG, r, A, hcls, hr, hB⟩ := hg
  have hA : IsUnit A.det := by
    obtain ⟨B, -, -, h3, -⟩ := hB (genericPoint Z)
    rw [Matrix.det_mul] at h3
    exact isUnit_iff_ne_zero.2 (left_ne_zero_of_mul h3.ne_zero)
  obtain ⟨-, e⟩ := chiPic_top k hO G hG r A hr hA hB
  have hB1 : ∀ z : Z, ∃ B : Matrix (Fin N) (Fin N) Z.functionField, B.BlockTriangular id ∧
      (∀ a b, RegAt z (((1 : Matrix (Fin N) (Fin N) Z.functionField) * B) a b)) ∧
        UnitAt z ((1 : Matrix (Fin N) (Fin N) Z.functionField) * B).det ∧
        ∀ (i : Fin N) c, z ∈ (LB.triv Z).U c → UnitAt z (B i i * ((fun _ _ => 1 : ∀ _ : Fin N, (LB.triv Z).ι → Z.functionFieldˣ) i c)) :=
    fun z => ⟨1, Matrix.blockTriangular_one, fun a b => by
      rw [one_mul, Matrix.one_apply]
      split_ifs
      · exact (unitAt_one z).regAt
      · exact regAt_zero z, by simpa using unitAt_one z, fun i c _ => by simpa using unitAt_one z⟩
  obtain ⟨-, e1⟩ := chiPic_top k hO (fun _ => LB.triv Z) (fun _ => LB.isLB_triv Z) (fun _ _ => 1) 1
    (fun _ _ _ _ => ((congrArg (· * _) (map_one _)).trans (one_mul _)).symm) (by simp) hB1
  have htop : stepMod (A⁻¹) N = stepMod ((1 : Matrix (Fin N) (Fin N) Z.functionField)⁻¹) N := by
    unfold stepMod; rw [stepC_top A⁻¹ 1⁻¹]
  calc ∑ i, chiPic k (structureModule Z) (g i + c)
      = chiPic k (stepMod A⁻¹ N) c := by rw [e c]; simp only [hcls]
    _ = chiPic k (stepMod ((1 : Matrix (Fin N) (Fin N) Z.functionField)⁻¹) N) c := by rw [htop]
    _ = (N : ℤ) * chiPic k (structureModule Z) c := by
      rw [e1 c]; simp [cls_triv]

end
