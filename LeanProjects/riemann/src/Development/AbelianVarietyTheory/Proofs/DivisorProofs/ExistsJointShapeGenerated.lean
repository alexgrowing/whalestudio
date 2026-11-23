import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJointHarmonicsHighestWeightEqBotOfNotShape
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFockJointHarmonicsHighestWeightOfShape
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointShapeUniqueAndDegWEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsGradedCompactStable

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.FockAlg.MinFirst

noncomputable section
namespace GlobalTheory.RealLift.GenLift

section Objects

variable {P Q R S : ℕ}

theorem trace_Eab {p q : ℕ} (a b : Ix p q) : (Eab a b).trace = if a = b then 1 else 0 := by
  split_ifs with h
  · subst h; simp [Eab, Matrix.trace_single_eq_same]
  · simp [Eab, Matrix.trace_single_eq_of_ne _ _ _ h]

def chAct (p q : ℕ) (x : ℚ) : Mat p q →ₗ[ℂ] Module.End ℂ ℂ :=
  ((x : ℂ) • Matrix.traceLinearMap (Ix p q) ℂ ℂ).smulRight LinearMap.id

theorem chAct_apply (p q : ℕ) (x : ℚ) (X : Mat p q) (z : ℂ) :
    chAct p q x X z = ((x : ℂ) * X.trace) • z := by
  simp [chAct]

abbrev chMod (p q : ℕ) (x : ℚ) : GKMod p q where
  V := ℂ
  act := chAct p q x
  lie := by
    intro X Y
    ext
    simp [chAct_apply, Matrix.trace_sub, Matrix.trace_mul_comm X Y]
    ring
  kfin := fun _ => ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩
  wts := fun v => by
    refine Submodule.mem_iSup_of_mem (fun _ => x) ?_
    simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply]
    intro a
    rw [chAct_apply, trace_Eab, if_pos rfl, mul_one, sub_self]

abbrev shiftMod {r s : ℕ} (M : GKMod r s) (t : ℚ) : GKMod r s where
  V := M.V
  act := M.act - ((t : ℂ) • Matrix.traceLinearMap (Ix r s) ℂ ℂ).smulRight LinearMap.id
  lie := by
    intro X Y
    ext v
    have h := LinearMap.congr_fun (M.lie X Y) v
    simp only [LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.smul_apply,
      Matrix.traceLinearMap_apply, Module.End.mul_apply, LinearMap.id_apply, map_sub, map_smul,
      Matrix.trace_sub, Matrix.trace_mul_comm X Y, sub_self, smul_zero, zero_smul, sub_zero] at h ⊢
    linear_combination (norm := module) h
  kfin := fun v => by
    obtain ⟨W, fW, hv, sW⟩ := M.kfin v
    refine ⟨W, fW, hv, fun X hX w hw => ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.smul_apply,
      Matrix.traceLinearMap_apply, LinearMap.id_apply]
    exact W.sub_mem (sW X hX w hw) (W.smul_mem _ hw)
  wts := fun v => by
    refine (iSup_le fun μ => le_iSup_of_le (fun c => μ c - t) ?_ : (⨆ μ, wtSub M.act μ) ≤ _) (M.wts v)
    intro w hw
    simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      Matrix.traceLinearMap_apply] at hw ⊢
    intro a
    have := hw a
    rw [trace_Eab, if_pos rfl]
    linear_combination (norm := module) this

theorem shiftMod_act {r s : ℕ} (M : GKMod r s) (t : ℚ) (Y : Mat r s) (v : M.V) :
    (shiftMod M t).act Y v = M.act Y v - ((t : ℂ) * Y.trace) • v := by
  show ((M.act - ((t : ℂ) • Matrix.traceLinearMap (Ix r s) ℂ ℂ).smulRight LinearMap.id :
    Mat r s →ₗ[ℂ] Module.End ℂ M.V) Y) v = _
  rw [LinearMap.sub_apply, LinearMap.sub_apply]
  simp [mul_smul]

end Objects

section Main

variable {P Q R S : ℕ}

theorem tmul_one_eq_zero {V : Type} [AddCommGroup V] [Module ℂ V] {v : V}
    (h : (1 : ℂ) ⊗ₜ[ℂ] v = 0) : v = 0 := by
  have := congrArg (TensorProduct.lid ℂ V) h
  simpa using this

def fMap (x t : ℚ) {M : GKMod R S} (pr : Pol P Q R S →ₗ[ℂ] M.V) :
    Pol P Q R S →ₗ[ℂ] TensorProduct ℂ (chMod P Q x).V (shiftMod M t).V :=
  TensorProduct.mk ℂ ℂ M.V 1 ∘ₗ pr

theorem fMap_apply (x t : ℚ) {M : GKMod R S} (pr : Pol P Q R S →ₗ[ℂ] M.V) (f : Pol P Q R S) :
    fMap x t pr f = (1 : ℂ) ⊗ₜ[ℂ] pr f := rfl

theorem fMap_eq_zero {x t : ℚ} {M : GKMod R S} {pr : Pol P Q R S →ₗ[ℂ] M.V} {f : Pol P Q R S}
    (h : fMap x t pr f = 0) : pr f = 0 := tmul_one_eq_zero h

theorem intw_fMap {x t : ℚ} {M : GKMod R S} {pr : Pol P Q R S →ₗ[ℂ] M.V} (hL : IsLift x t M pr) :
    Intw (chMod P Q x) (shiftMod M t) (fMap x t pr) := by
  refine ⟨fun X => LinearMap.ext fun f => ?_, fun Y => LinearMap.ext fun f => ?_⟩
  · change (1 : ℂ) ⊗ₜ[ℂ] pr (fockAct1 P Q R S X f) =
      TensorProduct.map (chAct P Q x X) LinearMap.id ((1 : ℂ) ⊗ₜ[ℂ] pr f)
    rw [TensorProduct.map_tmul, LinearMap.id_apply, hL.2.1 X f, chAct_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  · change (1 : ℂ) ⊗ₜ[ℂ] pr (fockAct2 P Q R S Y f) =
      TensorProduct.map LinearMap.id ((shiftMod M t).act Y) ((1 : ℂ) ⊗ₜ[ℂ] pr f)
    rw [TensorProduct.map_tmul, LinearMap.id_apply, shiftMod_act, hL.2.2 Y f, add_sub_cancel_right]

theorem hw_chMod (p q : ℕ) (x : ℚ) : IsHW (chMod p q x).act (fun _ => x) (1 : ℂ) := by
  refine ⟨one_ne_zero, (mem_hwSub _ _ _).2 ⟨fun a => ?_, fun a b hab => ?_⟩⟩
  · change chAct p q x _ 1 - _ = 0
    rw [chAct_apply, trace_Eab, if_pos rfl]; simp [smul_eq_mul]
  · change chAct p q x _ 1 = 0
    have : a ≠ b := by
      rintro rfl
      cases a <;> simp [posC] at hab
    rw [chAct_apply, trace_Eab, if_neg this]; simp

theorem hw_chMod_eq {p q : ℕ} {x : ℚ} {ν : Ix p q → ℚ} {w : (chMod p q x).V}
    (h : IsHW (chMod p q x).act ν w) : ν = fun _ => x := by
  funext a
  have h1 := ((mem_hwSub _ _ _).1 h.2).1 a
  change chAct p q x _ w - _ = 0 at h1
  rw [chAct_apply, trace_Eab, if_pos rfl, mul_one, ← sub_smul, smul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact_mod_cast (sub_eq_zero.1 h1).symm
  · exact absurd h1 h.1

theorem irr_chMod (p q : ℕ) (x : ℚ) : IrrGK (chMod p q x) :=
  ⟨inferInstanceAs (Nontrivial ℂ), fun N _ => Ideal.eq_bot_or_top N⟩

theorem admissible_traceCharacterGKModule (p q : ℕ) (x : ℚ) : AdmGK (chMod p q x) := fun _ =>
  inferInstanceAs (FiniteDimensional ℂ ↥(hwSub (chAct p q x) _))

end Main

theorem genBy_of_isLift : ∀ (P Q R S : ℕ) (x t : ℚ) (M : Formalism.BasicNotions.TH.GKMod R S)
    (pr : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] M.V), GlobalTheory.RealLift.IsLift x t M pr → Nontrivial M.V →
    ∃ μ' : Formalism.BasicNotions.TH.Ix R S → ℚ, Formalism.BasicNotions.TH.JointShape P Q R S (fun _ => x) μ' ∧
      GlobalTheory.RealLift.GenBy M (fun c => μ' c + t) := by
  intro P Q R S x t M pr hL hM
  have hI := intw_fMap (P := P) (Q := Q) hL
  have hf : fMap x t pr ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : M.V)
    obtain ⟨f, rfl⟩ := hL.1 v
    intro h
    exact hv (fMap_eq_zero (LinearMap.congr_fun h f))
  have hmin : ∀ ν w, IsHW (chMod P Q x).act ν w →
      degW (cPair R S) (fun _ : Ix P Q => x) ≤ degW (cPair R S) ν := by
    intro ν w h
    rw [hw_chMod_eq h]
  obtain ⟨⟨μ', P0, hJ0, h10, h20, hf0⟩, -⟩ := GlobalTheory.FockAlg.min_first P Q R S (chMod P Q x)
    (shiftMod M t) (fMap x t pr) (irr_chMod P Q x) (admissible_traceCharacterGKModule P Q x) hI hf (fun _ => x)
    ⟨1, hw_chMod P Q x⟩ hmin
  have hpr0 : pr P0 ≠ 0 := fun h => hf0 (by rw [fMap_apply, h, TensorProduct.tmul_zero])
  have hP0mem : P0 ∈ hwSub (fockAct1 P Q R S) (fun _ => x) ⊓ hwSub (fockAct2 P Q R S) μ' ⊓
      Submodule.span ℂ (jointHarm P Q R S) := ⟨⟨h10.2, h20.2⟩, Submodule.subset_span hJ0⟩
  have hshape : JointShape P Q R S (fun _ => x) μ' := by
    by_contra h
    have := hP0mem
    rw [GlobalTheory.FockAlg.jointHarm_hw_eq_bot P Q R S _ _ h, Submodule.mem_bot] at this
    exact h10.1 this

  have hw0 : IsHW M.act (fun c => μ' c + t) (pr P0) := by
    refine ⟨hpr0, (mem_hwSub _ _ _).2 ⟨fun a => ?_, fun a b hab => ?_⟩⟩
    · have e := ((mem_hwSub _ _ _).1 h20.2).1 a
      rw [hL.2.2, trace_Eab, if_pos rfl, sub_eq_zero.1 e, map_smul]
      push_cast
      module
    · have e := ((mem_hwSub _ _ _).1 h20.2).2 a b hab
      have : a ≠ b := by
        rintro rfl
        cases a <;> simp [posC] at hab
      rw [hL.2.2, trace_Eab, if_neg this, e, map_zero]
      simp
  refine ⟨μ', hshape, pr P0, hw0, ?_⟩

  set G := genSub M.act {pr P0} with hG
  set T : Submodule ℂ (Pol P Q R S) := G.comap pr with hT
  have hT1 : ∀ X, ∀ y ∈ T, fockAct1 P Q R S X y ∈ T := by
    intro X y hy
    rw [Submodule.mem_comap, hL.2.1]
    exact G.smul_mem _ hy
  have hT2 : ∀ Z, ∀ y ∈ T, fockAct2 P Q R S Z y ∈ T := by
    intro Z y hy
    have e := hL.2.2 Z y
    rw [Submodule.mem_comap, eq_sub_of_add_eq e.symm]
    exact G.sub_mem (genSub_stable _ _ Z hy) (G.smul_mem _ hy)
  have hker : LinearMap.ker (fMap x t pr) ≤ T := by
    intro y hy
    rw [Submodule.mem_comap, fMap_eq_zero (LinearMap.mem_ker.1 hy)]
    exact G.zero_mem
  have hP0T : P0 ∈ T := subset_genSub M.act {pr P0} rfl
  have hJ : ∀ P' ∈ jointHarm P Q R S, P' ∈ hwSub (fockAct1 P Q R S) (fun _ => x) → P' ∈ T := by
    intro P' hJ' hh
    obtain ⟨U, fU, hU, sU⟩ := ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 P').1
    obtain ⟨-, -, s2, -⟩ := GlobalTheory.FockAlg.harm_graded_stable P Q R S _ (Or.inr (Or.inr rfl))
    have sH : KStable (fockAct2 P Q R S) (hwSub (fockAct1 P Q R S) (fun _ => x)) :=
      fun Z _ w hw => hw_map (fockAct2 P Q R S Z) (fun Y _ v => fockAct1_fockAct2_commute Y Z v) hw
    by_contra hPT
    obtain ⟨ν, u, hu, hhw, hN⟩ := exists_hw_notMem kLie2 wts2
      (W := U ⊓ (Submodule.span ℂ (jointHarm P Q R S) ⊓ hwSub (fockAct1 P Q R S) (fun _ => x)))
      (N := T) inferInstance (kStable_inf sU (kStable_inf s2 sH)) (fun Z _ y hy => hT2 Z y hy)
      (fun h => hPT (h ⟨hU, Submodule.subset_span hJ', hh⟩))
    have hmem : u ∈ hwSub (fockAct1 P Q R S) (fun _ => x) ⊓ hwSub (fockAct2 P Q R S) ν ⊓
        Submodule.span ℂ (jointHarm P Q R S) := ⟨⟨hu.2.2, hhw.2⟩, hu.2.1⟩
    have hsh : JointShape P Q R S (fun _ => x) ν := by
      by_contra h
      rw [GlobalTheory.FockAlg.jointHarm_hw_eq_bot P Q R S _ _ h, Submodule.mem_bot] at hmem
      exact hhw.1 hmem
    obtain rfl : ν = μ' :=
      (GlobalTheory.JointShapeUniq.jointShape_unique_deg P Q R S _ _ _ _ hsh hshape).1.1 rfl
    have hline := GlobalTheory.JointHarm.finrank_joint_highest_of_shape P Q R S _ _ hshape
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨P0, hP0mem⟩ : ↥(hwSub (fockAct1 P Q R S)
      (fun _ => x) ⊓ hwSub (fockAct2 P Q R S) ν ⊓ Submodule.span ℂ (jointHarm P Q R S)))
      (fun h => h10.1 (congrArg Subtype.val h))).1 hline ⟨u, hmem⟩
    have hu' : u = c • P0 := (congrArg Subtype.val hc).symm
    exact hN (hu' ▸ T.smul_mem c hP0T)
  have hall : ∀ P', P' ∈ T := by
    intro P'
    obtain ⟨W, fW, hW, sW⟩ := ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).1 P').1
    by_contra hPT
    obtain ⟨ν, u, hu, hhw, hN⟩ := exists_hw_notMem kLie1 wts1 fW sW (fun X _ y hy => hT1 X y hy)
      (fun h => hPT (h hW))
    have hpru : pr u ≠ 0 := fun h => hN (by rw [Submodule.mem_comap, h]; exact G.zero_mem)
    obtain rfl : ν = fun _ => x := by
      funext a
      have e := ((mem_hwSub _ _ _).1 hhw.2).1 a
      have e2 := congrArg pr e
      rw [map_sub, map_smul, hL.2.1, trace_Eab, if_pos rfl, mul_one, map_zero, ← sub_smul,
        smul_eq_zero] at e2
      rcases e2 with e2 | e2
      · exact_mod_cast (sub_eq_zero.1 e2).symm
      · exact absurd e2 hpru
    exact hN (hw_mem hI hmin T hker hT2 hJ hhw.2)
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨f, rfl⟩ := hL.1 v
  exact hall f

end GlobalTheory.RealLift.GenLift

end
