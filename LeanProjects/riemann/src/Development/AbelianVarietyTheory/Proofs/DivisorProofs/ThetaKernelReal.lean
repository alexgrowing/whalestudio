import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFormNegOfPairBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNontrivialLiftModuleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJointShapeGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicHighestWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirLtAddRootStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirLtAddRootNegStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointShapeForcedLambdaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonIrreducibleQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorIrreducibleModules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFinitePiTensorSumOfFactorOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDerivaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivatiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLawsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupGeneratorsExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLinesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLinesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieScalarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSecondOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFirstOfLieSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtAlgebraMapSgnAdSubOneStatement

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.RealLift.Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_map_piInf {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem hasExp_div (τ : ∀ w : InfinitePlace F, EmbOver E w) {χ χ' : Chr F E} {m m' : InfinitePlace F → ℤ}
    (h : HasExp τ χ m) (h' : HasExp τ χ' m') : HasExp τ (χ / χ') (fun w => m w - m' w) := by
  intro z hz
  rw [MonoidHom.div_apply, Circle.coe_div, h z hz, h' z hz, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have : piInf (τ w) (z : AE F E) / (‖piInf (τ w) (z : AE F E)‖ : ℂ) ≠ 0 := by
    have h0 : piInf (τ w) (z : AE F E) ≠ 0 := by
      intro e
      have := congrArg (piInf (τ w)) z.mul_inv
      rw [map_mul, e, zero_mul, map_one] at this
      exact zero_ne_one this
    exact div_ne_zero h0 (by exact_mod_cast norm_ne_zero_iff.2 h0)
  rw [zpow_sub₀ this]

section Tensor
variable {ι : Type} [Fintype ι] [DecidableEq ι] {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

theorem map_atPl (p : ∀ i, V i →ₗ[ℂ] W i) (w : ι) (L : Module.End ℂ (V w)) (L' : Module.End ℂ (W w))
    (h : p w ∘ₗ L = L' ∘ₗ p w) : PiTensorProduct.map p ∘ₗ atPl w L = atPl w L' ∘ₗ PiTensorProduct.map p := by
  unfold atPl
  rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
  congr 1
  funext i
  by_cases hi : i = w
  · subst hi; simp [h]
  · simp [Function.update_of_ne hi]

theorem map_sumPl (p : ∀ i, V i →ₗ[ℂ] W i) (L : ∀ i, Module.End ℂ (V i)) (L' : ∀ i, Module.End ℂ (W i))
    (h : ∀ i, p i ∘ₗ L i = L' i ∘ₗ p i) : PiTensorProduct.map p ∘ₗ sumPl L = sumPl L' ∘ₗ PiTensorProduct.map p := by
  apply LinearMap.ext; intro x
  simp only [sumPl, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => LinearMap.congr_fun (map_atPl p i (L i) (L' i) (h i)) x

end Tensor

theorem i_multone : GlobalTheory.RealLift.MultOne := GlobalTheory.T.multOne'

theorem i_formex : GlobalTheory.RealLift.FormEx := GlobalTheory.T.FormExists

theorem i_formdual : GlobalTheory.RealLift.FormEx → ∀ (P Q R S : ℕ) (x : ℚ) (k k' : ℕ), P ≤ S → Q ≤ R → 0 < k → 0 < k' → x - Formalism.BasicNotions.TH.cPair S R = k → x + Formalism.BasicNotions.TH.cPair S R = k' → GlobalTheory.RealLift.HasForm P Q R S (-x) := GlobalTheory.T.hasForm_neg_of_pair_bounds

theorem i_quot : ∀ (P Q R S : ℕ) (x t : ℚ), GlobalTheory.RealLift.HasForm P Q R S x → ∃ (M : Formalism.BasicNotions.TH.GKMod R S) (pr : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] M.V), GlobalTheory.RealLift.IsLift x t M pr ∧ Nontrivial M.V := GlobalTheory.T.exists_nontrivial_lift_module

theorem i_gen : ∀ (P Q R S : ℕ) (x t : ℚ) (M : Formalism.BasicNotions.TH.GKMod R S) (pr : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] M.V), GlobalTheory.RealLift.IsLift x t M pr → Nontrivial M.V → ∃ μ' : Formalism.BasicNotions.TH.Ix R S → ℚ, Formalism.BasicNotions.TH.JointShape P Q R S (fun _ => x) μ' ∧ GlobalTheory.RealLift.GenBy M (fun c => μ' c + t) := GlobalTheory.T.exists_joint_shape_generated

theorem i_harm : ∀ (P Q R S : ℕ) (x t : ℚ) (M : Formalism.BasicNotions.TH.GKMod R S) (pr : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] M.V), GlobalTheory.RealLift.IsLift x t M pr → ∀ (μ : Formalism.BasicNotions.TH.Ix R S → ℚ) (w : M.V), Formalism.BasicNotions.TH.IsHW M.act μ w → ∃ f : Formalism.BasicNotions.TH.Pol P Q R S, GlobalTheory.RealLift.IsHarmVec x (fun c => μ c - t) f := GlobalTheory.T.exists_harmonic_highest_weight

theorem i_steepv : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → ∀ a b : Formalism.BasicNotions.TH.Ix R S, ¬ Formalism.BasicNotions.TH.sameBlock a b → ∀ f : Formalism.BasicNotions.TH.Pol P Q R S, GlobalTheory.RealLift.IsHarmVec ((κ : ℚ) / 2) (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b) f → GlobalTheory.RealLift.casK (GlobalTheory.RealLift.lam P Q R S κ) + ((R + S : ℕ) : ℚ) < GlobalTheory.RealLift.casK (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b) := GlobalTheory.T.casimir_lt_add_root

theorem i_steepw : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → ∀ a b : Formalism.BasicNotions.TH.Ix R S, ¬ Formalism.BasicNotions.TH.sameBlock a b → ∀ f : Formalism.BasicNotions.TH.Pol P' Q' R S, GlobalTheory.RealLift.IsHarmVec (-((κ : ℚ) / 2)) (fun c => GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b c - (κ : ℚ) / 2) f → GlobalTheory.RealLift.casK (GlobalTheory.RealLift.lam P Q R S κ) + ((R + S : ℕ) : ℚ) < GlobalTheory.RealLift.casK (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b) := GlobalTheory.T.casimir_lt_add_root_neg

theorem i_shape : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → (∀ μ' : Formalism.BasicNotions.TH.Ix R S → ℚ, Formalism.BasicNotions.TH.JointShape P Q R S (fun _ => (κ : ℚ) / 2) μ' → μ' = GlobalTheory.RealLift.lam P Q R S κ) ∧ ∀ μ' : Formalism.BasicNotions.TH.Ix R S → ℚ, Formalism.BasicNotions.TH.JointShape P' Q' R S (fun _ => -((κ : ℚ) / 2)) μ' → (fun c => μ' c + (κ : ℚ) / 2) = GlobalTheory.RealLift.lam P Q R S κ := GlobalTheory.T.joint_shape_forced_lambda

theorem i_cq : GlobalTheory.RealLift.MultOne → ∀ (R S : ℕ) (M M' : Formalism.BasicNotions.TH.GKMod R S) (Λ : Formalism.BasicNotions.TH.Ix R S → ℚ), GlobalTheory.RealLift.GenBy M Λ → GlobalTheory.RealLift.GenBy M' Λ → GlobalTheory.RealLift.Steep M Λ → GlobalTheory.RealLift.Steep M' Λ → ∃ (N : Formalism.BasicNotions.TH.GKMod R S) (π : M.V →ₗ[ℂ] N.V) (π' : M'.V →ₗ[ℂ] N.V), GlobalTheory.RealLift.IsQuot M N π ∧ GlobalTheory.RealLift.IsQuot M' N π' ∧ Formalism.MainNotions.SchurIrreducible.IrrGK N ∧ GlobalTheory.RealLift.ScalarEnd N := GlobalTheory.T.exists_common_irreducible_quotient

theorem i_locfin : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] (L : ∀ i, Module.End ℂ (V i)), (∀ i, GlobalTheory.RealLift.LocFin (L i)) → GlobalTheory.RealLift.LocFin (GlobalTheory.RealLift.sumPl L) := GlobalTheory.T.isLocallyFinite_piTensorSumOfFactorOperators

theorem i_expact : ∀ (F : Type) [Field F] [NumberField F] (κ V : Type) [Fintype κ] [AddCommGroup V] [Module ℂ V] (Φ : V →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (L : Module.End ℂ V) (om : Multiplicative ℝ →* Module.End ℂ ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ)), GlobalTheory.RealLift.LocFin L → (∀ t, ∀ l ∈ (GlobalTheory.WeilM.adeleClass F).adm κ, l ∘ₗ om t ∈ (GlobalTheory.WeilM.adeleClass F).adm κ) → (∀ T, GlobalTheory.RealLift.SD (fun t => om (Multiplicative.ofAdd t)) (Φ T) (Φ (L T))) → ∃ U : Module.End ℂ V, GlobalTheory.RealLift.IsExp L U ∧ ∀ T, GlobalTheory.RealLift.SA (om (Multiplicative.ofAdd 1)) (Φ T) (Φ (U T)) := GlobalTheory.T.weakExponential_action_on_fockVectors

theorem i_actslaws : GlobalTheory.RealLift.ActsLaws := GlobalTheory.T.archActionReadings_compatible

theorem i_derex : GlobalTheory.RealLift.DerEx := GlobalTheory.T.archHeisenbergDerivatives_exist

theorem i_fockex : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.FockEx := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives

theorem i_vacline : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives

theorem i_polrange : GlobalTheory.RealLift.ActsLaws → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.PolRange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws

theorem i_genex : GlobalTheory.RealLift.GenEx := GlobalTheory.T.oneParamSubgroup_generators_exist

theorem i_lineex : GlobalTheory.RealLift.LineEx := GlobalTheory.T.unitaryLieElements_generate_oneParamLines

theorem i_kline : GlobalTheory.RealLift.LineEx → GlobalTheory.RealLift.KLine := GlobalTheory.T.maximalCompact_oneParameterLines_of_lieLines

theorem i_liescalar : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar := GlobalTheory.T.lieScalar_of_prints_derEx_vacLine

theorem i_liesecond : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.FockEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar → GlobalTheory.RealLift.LieSecond := GlobalTheory.T.lieSecond_of_prints_derEx_fockEx_vacLine_lieScalar

theorem i_liefirst : GlobalTheory.RealLift.LieSecond → GlobalTheory.RealLift.LieFirst := GlobalTheory.T.lieFirst_of_lieSecond'

theorem i_frameex : GlobalTheory.RealLift.FrameEx := GlobalTheory.T.cartanEigen_orthonormalFrame_exists

theorem i_parity : GlobalTheory.RealLift.Parity := GlobalTheory.T.realLift_parity

theorem comp_isLift {P Q R S : ℕ} {x t : ℚ} {M N : GKMod R S} {pr : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] M.V} {π : M.V →ₗ[ℂ] N.V}
    (h : IsLift x t M pr) (hπ : IsQuot M N π) : IsLift x t N (π ∘ₗ pr) := by
  refine ⟨hπ.1.comp h.1, fun X f => ?_, fun Y f => ?_⟩
  · simp [h.2.1 X f]
  · simp only [LinearMap.comp_apply]
    rw [← hπ.2, h.2.2 Y f, map_add, map_smul]

theorem onePlace (P Q P' Q' R S : ℕ) (κ : ℤ) (h : Num P Q P' Q' R S κ) :
    ∃ (N : GKMod R S) (p : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] N.V) (p' : Formalism.BasicNotions.TH.Pol P' Q' R S →ₗ[ℂ] N.V),
      IsLift ((κ : ℚ) / 2) 0 N p ∧ IsLift (-((κ : ℚ) / 2)) ((κ : ℚ) / 2) N p' ∧ Formalism.MainNotions.SchurIrreducible.IrrGK N ∧ ScalarEnd N := by
  obtain ⟨hR, hS, hSP, hSQ, ⟨m, hm⟩, ⟨k0, hk0⟩, hlt⟩ := h
  have hk : (0 : ℤ) < k0 - m + S := by omega
  have hk' : (0 : ℤ) < k0 + m - S := by omega
  have ec : cPair R S = (m : ℚ) - S := by
    unfold cPair
    have : (R : ℚ) + S = m + m := by exact_mod_cast hm
    linarith
  have ec' : cPair S R = (S : ℚ) - m := by unfold cPair at *; linarith
  have ek : ((κ : ℚ) / 2) = k0 := by rw [hk0]; push_cast; ring
  have hF : HasForm P Q R S ((κ : ℚ) / 2) :=
    i_formex P Q R S _ (k0 - m + S).toNat (k0 + m - S).toNat (by omega) (by omega) (by omega) (by omega)
      (by rw [ec, ek]; rw [show (((k0 - m + S : ℤ).toNat : ℕ) : ℚ) = ((k0 - m + S : ℤ) : ℚ) by exact_mod_cast Int.toNat_of_nonneg hk.le]; push_cast; ring)
      (by rw [ec, ek]; rw [show (((k0 + m - S : ℤ).toNat : ℕ) : ℚ) = ((k0 + m - S : ℤ) : ℚ) by exact_mod_cast Int.toNat_of_nonneg hk'.le]; push_cast; ring)
  have hF' : HasForm P' Q' R S (-((κ : ℚ) / 2)) :=
    i_formdual i_formex P' Q' R S _ (k0 + m - S).toNat (k0 - m + S).toNat (by omega) (by omega) (by omega) (by omega)
      (by rw [ec', ek]; rw [show (((k0 + m - S : ℤ).toNat : ℕ) : ℚ) = ((k0 + m - S : ℤ) : ℚ) by exact_mod_cast Int.toNat_of_nonneg hk'.le]; push_cast; ring)
      (by rw [ec', ek]; rw [show (((k0 - m + S : ℤ).toNat : ℕ) : ℚ) = ((k0 - m + S : ℤ) : ℚ) by exact_mod_cast Int.toNat_of_nonneg hk.le]; push_cast; ring)
  have hN : Num P Q P' Q' R S κ := ⟨hR, hS, hSP, hSQ, ⟨m, hm⟩, ⟨k0, hk0⟩, hlt⟩
  obtain ⟨M, pr, hM, hMn⟩ := i_quot P Q R S _ 0 hF
  obtain ⟨M', pr', hM', hMn'⟩ := i_quot P' Q' R S _ ((κ : ℚ) / 2) hF'
  obtain ⟨μ, hμ, hg⟩ := i_gen _ _ _ _ _ _ M pr hM hMn
  obtain ⟨μ', hμ', hg'⟩ := i_gen _ _ _ _ _ _ M' pr' hM' hMn'
  have e1 : (fun c => μ c + (0 : ℚ)) = lam P Q R S κ := by
    rw [← (i_shape _ _ _ _ _ _ _ hN).1 μ hμ]; funext c; simp
  have e2 := (i_shape _ _ _ _ _ _ _ hN).2 μ' hμ'
  rw [e1] at hg
  rw [e2] at hg'
  have st : Steep M (lam P Q R S κ) := fun a b hab w hw => by
    obtain ⟨f, hf⟩ := i_harm _ _ _ _ _ _ M pr hM _ w hw
    exact i_steepv _ _ _ _ _ _ _ hN a b hab f (by simpa using hf)
  have st' : Steep M' (lam P Q R S κ) := fun a b hab w hw => by
    obtain ⟨f, hf⟩ := i_harm _ _ _ _ _ _ M' pr' hM' _ w hw
    exact i_steepw _ _ _ _ _ _ _ hN a b hab f hf
  obtain ⟨N, π, π', hπ, hπ', hirr, hsc⟩ := i_cq i_multone R S M M' _ hg hg' st st'
  exact ⟨N, π ∘ₗ pr, π' ∘ₗ pr', comp_isLift hM hπ, comp_isLift hM' hπ', hirr, hsc⟩

section Helpers

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

theorem atPl_eq (w : ι) (L : Module.End ℂ (V w)) :
    atPl w L = PiTensorProduct.mapMultilinear ℂ V V (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w L) := rfl

theorem atPl_add (w : ι) (L L' : Module.End ℂ (V w)) : atPl w (L + L') = atPl w L + atPl w L' := by
  simp only [atPl_eq, MultilinearMap.map_update_add]

theorem atPl_smul (w : ι) (c : ℂ) (L : Module.End ℂ (V w)) : atPl w (c • L) = c • atPl w L := by
  simp only [atPl_eq, MultilinearMap.map_update_smul]

theorem atPl_one (w : ι) : atPl w (1 : Module.End ℂ (V w)) = 1 := by
  rw [atPl_eq, show Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w 1 = fun i => LinearMap.id by
    funext i; by_cases h : i = w
    · subst h; simp; rfl
    · simp [Function.update_of_ne h]]
  exact PiTensorProduct.map_id

theorem atPl_zero (w : ι) : atPl w (0 : Module.End ℂ (V w)) = 0 := by
  simp only [atPl_eq, MultilinearMap.map_update_zero]

end Helpers

section Exp

variable {V V' Z : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup Z] [Module ℂ Z]

theorem pow_comm {q : V →ₗ[ℂ] Z} {L : Module.End ℂ V} {L0 : Module.End ℂ Z} (h : q ∘ₗ L = L0 ∘ₗ q) (n : ℕ) (v : V) :
    q ((L ^ n) v) = (L0 ^ n) (q v) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih, ← LinearMap.comp_apply, h,
      LinearMap.comp_apply]

theorem exp_equiv {q : V →ₗ[ℂ] Z} {q' : V' →ₗ[ℂ] Z} {L U : Module.End ℂ V} {L' U' : Module.End ℂ V'} {L0 : Module.End ℂ Z}
    (hU : IsExp L U) (hU' : IsExp L' U') (h : q ∘ₗ L = L0 ∘ₗ q) (h' : q' ∘ₗ L' = L0 ∘ₗ q') {v : V} {v' : V'}
    (e : q v = q' v') : q (U v) = q' (U' v') := by
  refine sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ (q (U v) - q' (U' v'))).1 fun l => ?_)
  rw [map_sub, sub_eq_zero]
  have a := hU v (l ∘ₗ q)
  have b := hU' v' (l ∘ₗ q')
  simp only [LinearMap.comp_apply, pow_comm h, pow_comm h', e] at a b
  exact a.unique b

end Exp

theorem locFin_fock1 (P Q R S : ℕ) (X : Mat P Q) (hX : IsKC X) (c : ℂ) :
    LocFin (fockAct1 P Q R S X + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).1 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs X hX y hy) (W.smul_mem c hy)⟩

theorem locFin_fock2 (P Q R S : ℕ) (Y : Mat R S) (hY : IsKC Y) (c : ℂ) :
    LocFin (fockAct2 P Q R S Y + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs Y hY y hy) (W.smul_mem c hy)⟩

section Side

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d P Q R S : ℕ} {Y : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
  (N : InfinitePlace F → GKMod R S) (p : ∀ w, Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] (N w).V)
  (Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (Ψ : SInf F (Fin n × Fin d) →ₗ[ℂ] Tens F P Q R S)

include Φ in
theorem pol_eq (hrange : LinearMap.range Φ = M.Pol B.ψ B.emb) {f : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol B.ψ B.emb) :
    ∃ T, f = Φ T := by
  rw [← hrange] at hf
  obtain ⟨T, rfl⟩ := hf
  exact ⟨T, rfl⟩

end Side

section SideW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d P Q R S : ℕ} {Y : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
  (N : InfinitePlace F → GKMod R S) (p : ∀ w, Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] (N w).V)
  (Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (Ψ : SInf F (Fin n × Fin d) →ₗ[ℂ] Tens F P Q R S)

end SideW

theorem zero_mem_upq (R S : ℕ) : (0 : Mat R S) ∈ upq R S := by simp [upq]

end GlobalTheory.RealLift.Main
