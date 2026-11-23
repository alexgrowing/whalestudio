import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrOfNotMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsometryIntertwinesEnvelopingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RefineIsotropicFlagStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitTorusRefinedFlagStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviCommutesSplitTorusStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitTorusLeviSumVanishesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviConjugatesUnipotentRefinedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RefinedFlagHalfSumOfRootsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionInStagesRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StageFunctionContinuousStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionInStagesIntertwiningStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StageFunctionNormIntegralStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StageParameterPairingShiftStatement

noncomputable section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.Stages

theorem isKFin_map {n : ℕ} (ε : Fin n → Bool) {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (ρ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (T : H' →ₗᵢ[ℂ] H)
    (hT : ∀ (g : UJ ε) (w : H'), T (ρ' (uMat g) w) = ρ (uMat g) (T w)) {v : H'} (hv : IsKFin ε ρ' v) :
    IsKFin ε ρ (T v) := by
  obtain ⟨S, hS, hvS, hK⟩ := hv
  refine ⟨S.map T.toLinearMap, inferInstance, ⟨v, hvS, rfl⟩, ?_⟩
  rintro g hg _ ⟨w, hw, rfl⟩
  have hu : gᴴ * Jm ε * g = Jm ε := by
    rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.1 hg.1, Matrix.one_mul]
  obtain ⟨y, rfl, -⟩ := GlobalTheory.RealIwasawa.exists_uMat g hu
  exact ⟨_, hK _ hg w hw, hT y w⟩

end GlobalTheory.RealInd.Stages

namespace GlobalTheory.RealInd.Stages

theorem exists_stage {n : ℕ} {ε : Fin n → Bool} (I : IndModule ε) (h : 0 < I.a)
    (hTL : GlobalTheory.Published.Langlands.TemperedLevi) :
    ∃ (I' : IndModule ε) (h' : 0 < I'.a), I'.j ⟨0, h'⟩ = 1 ∧ (I'.s ⟨0, h'⟩).re = (I.s ⟨0, h⟩).re ∧
      ∃ T : I'.H →ₗᵢ[ℂ] I.H, ∀ (g : UJ ε) (w : I'.H), T (I'.ρ (uMat g) w) = I.ρ (uMat g) (T w) := by
  obtain ⟨b, W', β, p, hW', hp, hl, hβ, hpos⟩ := GlobalTheory.T.refine_isotropic_flag I.flag
  have h6 := GlobalTheory.T.refined_flag_half_sum_of_roots n I.j hβ hpos
  have hp0 : p 0 = 0 := Fin.ext (by rw [hpos]; simp)
  have hb : 0 < b := by
    have := (h6 ⟨0, h⟩).1
    have h1 := I.pos ⟨0, h⟩
    have h2 : #{l | β l = ⟨0, h⟩} ≤ b := (card_filter_le _ _).trans (by simp)
    omega
  have hβ0 : β ⟨0, hb⟩ = ⟨0, h⟩ := by
    refine (hβ _ _).2 ⟨?_, ?_⟩
    · rw [show (⟨0, h⟩ : Fin I.a).castSucc = 0 from rfl, hp0]; exact Fin.zero_le _
    · obtain ⟨l, hl0⟩ : (univ.filter (fun l => β l = ⟨0, h⟩)).Nonempty := by
        rw [← card_pos, (h6 ⟨0, h⟩).1]; exact I.pos _
      have := ((hβ l ⟨0, h⟩).1 (mem_filter.1 hl0).2).2
      rw [Fin.lt_iff_val_lt_val] at this ⊢
      simp only [Fin.coe_castSucc] at this ⊢
      omega
  obtain ⟨U, _, _, _, τ, y, hτ, hμ⟩ := hTL n ε I.toDatum b W' hW' (fun i => ⟨p i, hp i⟩) hl
  have hKM : IsCompact ((KG ε : Set (UJ ε)) ∩ (I.M : Set (UJ ε))) :=
    (isCompact_iff_compactSpace.2 (instCompactKG n ε)).inter_right (isClosed_leviOne I.flag I.pos)
  haveI : CompactSpace ↥(KG ε ⊓ I.M) := isCompact_iff_compactSpace.1 hKM
  let μ : Measure ↥(KG ε ⊓ I.M) := Measure.haarMeasure ⊤
  haveI : IsProbabilityMeasure μ := ⟨Measure.haarMeasure_self⟩
  obtain ⟨ι, hι⟩ := hμ μ inferInstance inferInstance
  set s' := stageS I.j β I.s y with hs'def
  obtain ⟨H', _, _, _, ρ', ι', hm'⟩ := exists_isIndModel (σ := τ) hW' (fun _ => le_rfl)
    (fun m hm => hτ.2.2.1.2.1 _ ⟨m, hm, rfl⟩) s'
  let D' : Datum ε :=
    { a := b
      j := fun _ => 1
      W := W'
      flag := hW'
      pos := fun _ => le_rfl
      V := U
      σ := τ
      temp := hτ
      s := s' }
  let I' : IndModule ε := { D' with H := H', ρ := ρ', ι := ι', model := hm' }
  have h9 := GlobalTheory.T.stage_parameter_pairing_shift n I.j β I.s y I.pos (fun i => (h6 i).1) (fun i => (h6 i).2)
  have hs : ∀ x t, IsSplit ε W' x t → t ∈ leviOne ε I.W →
      pairing (fun _ => 1) s' x = pairing (fun _ => 1) (fun l => Complex.I * y l) x :=
    fun x t ht hm => h9.2 x (GlobalTheory.T.split_torus_levi_sum_vanishes hW' hp hβ ht hm)
  have h1 : ∀ v, τ 1 v = v := fun v => by
    rw [hτ.2.2.1.1.1]; rfl
  have hmem : ∀ F ∈ I'.fns, ∀ g, restr I.M F g ∈ indFun I.M (fun _ => 1) W' τ (fun l => Complex.I * y l) := fun F hF g => GlobalTheory.T.induction_in_stages_restriction τ s' y hs hF g
  have hcont : ∀ F ∈ I'.fns, Continuous F := fun F hF => (mem_indFun_top.1 hF).1
  have hΦ : ∀ F ∈ I'.fns, stageFun I.M _ ι F ∈ I.fns := fun F hF => mem_indFun_top.2
    ⟨GlobalTheory.T.stage_function_continuous I.M _ ι μ hι.norm_sq (hcont F hF) (hmem F hF),
     GlobalTheory.T.induction_in_stages_intertwining τ I.σ I.s s' _ ι (fun m hm u hu => GlobalTheory.T.levi_conjugates_unipotent_refined I.flag hW' hp hl hβ m hm.1 u hu)
      (fun x t ht => ⟨GlobalTheory.T.split_torus_refined_flag I.flag hW' hp hl hβ ht, fun m hm => GlobalTheory.T.levi_commutes_split_torus I.flag ht m hm.1⟩) h1 h9.1 hι.transl hF
      (hmem F hF)⟩
  let Φ : I'.fns →ₗ[ℂ] I.fns :=
    { toFun := fun F => ⟨stageFun I.M _ ι F.1, hΦ F.1 F.2⟩
      map_add' := fun F G => Subtype.ext (funext fun g => by
        change stageFun I.M _ ι (F.1 + G.1) g = stageFun I.M _ ι F.1 g + stageFun I.M _ ι G.1 g
        rw [stageFun_of_mem ι (hmem _ (I'.fns.add_mem F.2 G.2) g), stageFun_of_mem ι (hmem _ F.2 g),
          stageFun_of_mem ι (hmem _ G.2 g), ← map_add]
        exact congrArg ι (Subtype.ext (funext fun m => by
          by_cases hm : m ∈ I.M <;> simp [restr, hm])))
      map_smul' := fun c F => Subtype.ext (funext fun g => by
        change stageFun I.M _ ι (c • F.1) g = c • stageFun I.M _ ι F.1 g
        rw [stageFun_of_mem ι (hmem _ (I'.fns.smul_mem c F.2) g), stageFun_of_mem ι (hmem _ F.2 g), ← map_smul]
        exact congrArg ι (Subtype.ext (funext fun m => by
          by_cases hm : m ∈ I.M <;> simp [restr, hm]))) }
  have hnorm : ∀ F : I'.fns, ‖I.ι (Φ F)‖ = ‖ι' F‖ := fun F =>
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by
      rw [I.model.norm_sq, hm'.norm_sq]
      exact GlobalTheory.T.stage_function_norm_integral I.M _ ι μ hι.norm_sq (hcont _ F.2) (hmem _ F.2))
  have hΦtr : ∀ (F : I'.fns) (g : UJ ε),
      (Φ ⟨fun g' => F.1 (g' * g), indFun_mul_right F.2 trivial⟩).1 = fun g' => (Φ F).1 (g' * g) := fun F g =>
    funext fun g' => by
      change stageFun I.M _ ι (fun g' => F.1 (g' * g)) g' = stageFun I.M _ ι F.1 (g' * g)
      have : restr I.M (fun g' => F.1 (g' * g)) g' = restr I.M F.1 (g' * g) := funext fun m => by
        simp only [restr, mul_assoc]
      unfold stageFun
      rw [this]
  have hbd : ∃ C, ∀ F, ‖(I.ι ∘ₗ Φ) F‖ ≤ C * ‖ι' F‖ := ⟨1, fun F => by rw [one_mul]; exact (hnorm F).le⟩
  let T₀ := (I.ι ∘ₗ Φ).extendOfNorm ι'
  have hT₀ : ∀ F, T₀ (ι' F) = I.ι (Φ F) := LinearMap.extendOfNorm_eq hm'.dense hbd
  have hiso : ∀ v, ‖T₀ v‖ = ‖v‖ := fun v =>
    hm'.dense.induction_on v (isClosed_eq (by fun_prop) (by fun_prop)) fun F => by rw [hT₀]; exact hnorm F
  refine ⟨I', hb, rfl, ?_, ⟨T₀.toLinearMap, hiso⟩, fun g w => ?_⟩
  · change (s' ⟨0, hb⟩).re = _
    simp [hs'def, stageS, hβ0]
  · change T₀ (ρ' (uMat g) w) = I.ρ (uMat g) (T₀ w)
    refine hm'.dense.induction_on w (isClosed_eq (by fun_prop) (by fun_prop)) fun F => ?_
    rw [hm'.transl g trivial F ⟨_, indFun_mul_right F.2 trivial⟩ (fun _ => rfl), hT₀, hT₀]
    exact (I.model.transl g trivial (Φ F) _ (fun g' => congrFun (hΦtr F g) g')).symm

end GlobalTheory.RealInd.Stages

namespace GlobalTheory.RealInd.Stages

theorem exists_first_step_one : GlobalTheory.Published.LanglandsClassification → ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε) (h : 0 < I.a) (χ : Fin n → ℂ), (∀ (k : ℕ) v, IsKFin ε I.ρ v → ∃ N : ℕ, actU ε I.ρ ((etr (Egl n) (k + 1) - algebraMap ℂ _ (gelfVal χ (k + 1))) ^ N) v = 0) → ∃ (I' : IndModule ε) (h' : 0 < I'.a), I'.j ⟨0, h'⟩ = 1 ∧ (I'.s ⟨0, h'⟩).re = (I.s ⟨0, h⟩).re ∧ (∀ (k : ℕ) v, IsKFin ε I'.ρ v → ∃ N : ℕ, actU ε I'.ρ ((etr (Egl n) (k + 1) - algebraMap ℂ _ (gelfVal χ (k + 1))) ^ N) v = 0) := by
  intro hLC n ε I h χ hI
  obtain ⟨I', h', hj, hre, T, hT⟩ := exists_stage I h hLC.2.2.2.2.2.2
  refine ⟨I', h', hj, hre, fun k v hv => ?_⟩
  obtain ⟨N, hN⟩ := hI k (T v) (isKFin_map ε _ _ T hT hv)
  exact ⟨N, T.injective (by rw [← GlobalTheory.T.isometry_intertwines_enveloping ε _ _ T hT, hN, map_zero])⟩

end GlobalTheory.RealInd.Stages

end
