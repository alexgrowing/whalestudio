import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.RightOnto
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel

noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.EmbChart

theorem std_mem_SB {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl F) :
    Set.indicator {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} (1 : (κ → Fv F v) → ℂ) ∈ SB (κ → Fv F v) := by
  set S : Set (κ → Fv F v) := {x | ∀ i, x i ∈ v.adicCompletionIntegers F} with hSdef
  have hOv : IsOpen ((v.adicCompletionIntegers F : Set (Fv F v))) := Valued.isOpen_integer _
  have hCv : IsCompact ((v.adicCompletionIntegers F : Set (Fv F v))) := by
    haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
    exact isCompact_iff_compactSpace.mpr inferInstance
  have hSeq : S = Set.pi Set.univ (fun _ : κ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext x
    simp [hSdef]
  have hO : IsOpen S := by
    rw [hSeq]
    exact isOpen_set_pi Set.finite_univ (fun _ _ => hOv)
  have hC : IsCompact S := by
    rw [hSeq]
    exact isCompact_univ_pi (fun _ => hCv)
  have hCl : IsClosed S := hC.isClosed
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ S
    · filter_upwards [hO.mem_nhds hx] with y hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
      rfl
    · filter_upwards [hCl.isOpen_compl.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · exact HasCompactSupport.intro hC (fun x hx => Set.indicator_of_notMem hx _)

theorem exists_sinf (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] : ∃ f : SInf F κ, f 0 = 1 := by
  classical
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport fun x => ((b x : ℝ) : ℂ) := b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun x => ((b x : ℝ) : ℂ) := Complex.ofRealCLM.contDiff.comp b.contDiff
  refine ⟨h1.toSchwartzMap h2, ?_⟩
  change ((b 0 : ℝ) : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
  simp

theorem pure_mem_schA {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB _)
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ schA F κ :=
  have hg : (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => evalV F v (y i)) ∈ SB _ :=
    ⟨isLocallyConstant_finprod_evalV φ hSB hstd, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hSB hstd⟩
  Submodule.subset_span ⟨f, _, hg, rfl⟩

theorem action_uniqueness : ActsUniq := by
  classical
  unfold ActsUniq
  intro F _ _ κ _ v T φ hφ φ₁ φ₂ h₁ h₂
  set std : ∀ w : Pl F, (κ → Fv F w) → ℂ :=
    fun w => Set.indicator {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 with hstd_def
  obtain ⟨f, hf⟩ := exists_sinf F κ
  set ψ : ∀ w : Pl F, (κ → Fv F w) → ℂ := Function.update std v (fun _ => 1) with hψ
  set r : (κ → AF F) → ℂ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f ψ with hr
  have hstd_ev : ∀ᶠ w in Filter.cofinite,
      std w = Set.indicator {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    Filter.Eventually.of_forall (fun w => rfl)
  have htens : tens (evFin F v) φ r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update std v φ) := by
    funext x
    simp only [tens, hr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hψ]
    rw [GlobalTheory.PureFactor.finprod_update std v φ hstd_ev x]
    ring
  have hRest : Rest (evFin F v) φ r := by
    refine ⟨?_, ?_⟩
    · intro x z hz
      let e : FiniteAdeleRing (𝓞 F) F :=
        RestrictedProduct.mk (Function.update (fun w : Pl F => (1 : Fv F w)) v 0) (by
          filter_upwards [Filter.eventually_cofinite_ne v] with w hw
          rw [Function.update_of_ne hw]
          exact (HeightOneSpectrum.adicCompletionIntegers F w).one_mem)
      let u : AF F := ((1 : InfiniteAdeleRing F), e)
      have hu : evFin F v u = 0 := by
        show Function.update (fun w : Pl F => (1 : Fv F w)) v 0 v = 0
        rw [Function.update_self]
      have huz := hz u hu
      have hz_inf : ∀ i, (z i).1 = 0 := by
        intro i
        have h := congrFun huz i
        rw [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
        have h' := congrArg Prod.fst h
        change (1 : InfiniteAdeleRing F) * (z i).1 = 0 at h'
        rwa [one_mul] at h'
      have hz_fin : ∀ w, w ≠ v → ∀ i, evFin F w (z i) = 0 := by
        intro w hw i
        have h := congrArg (evFin F w) (congrFun huz i)
        have hew : evFin F w u = 1 := by
          show Function.update (fun w : Pl F => (1 : Fv F w)) v 0 w = 1
          rw [Function.update_of_ne hw]
        rw [Pi.smul_apply, smul_eq_mul, map_mul, hew, one_mul, Pi.zero_apply, map_zero] at h
        exact h
      have hI : ∀ i, evI F ((x + z) i) = evI F (x i) := by
        intro i
        change InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + (z i).1) =
          InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1
        rw [hz_inf i, add_zero]
      have hP : ∀ w, ψ w (fun i => evFin F w ((x + z) i)) = ψ w (fun i => evFin F w (x i)) := by
        intro w
        by_cases hw : w = v
        · subst hw
          simp [hψ]
        · congr 1
          funext i
          rw [Pi.add_apply, map_add, hz_fin w hw i, add_zero]
      show f (fun i => evI F ((x + z) i)) * ∏ᶠ w, ψ w (fun i => evFin F w ((x + z) i)) =
        f (fun i => evI F (x i)) * ∏ᶠ w, ψ w (fun i => evFin F w (x i))
      rw [finprod_congr hP]
      congr 2
      funext i
      exact hI i
    · rw [htens]
      apply pure_mem_schA f
      · intro w
        by_cases hw : w = v
        · subst hw
          simpa using hφ
        · rw [Function.update_of_ne hw]
          exact std_mem_SB w
      · filter_upwards [Filter.eventually_cofinite_ne v] with w hw
        rw [Function.update_of_ne hw]
  have heq : tens (evFin F v) φ₁ r = tens (evFin F v) φ₂ r := (h₁ r hRest).symm.trans (h₂ r hRest)
  funext y
  let s : κ → AF F := fun i => ((0 : InfiniteAdeleRing F),
    RestrictedProduct.mk (Function.update (fun w : Pl F => (0 : Fv F w)) v (y i)) (by
      filter_upwards [Filter.eventually_cofinite_ne v] with w hw
      rw [Function.update_of_ne hw]
      exact (HeightOneSpectrum.adicCompletionIntegers F w).zero_mem))
  have hs : (fun i => evFin F v (s i)) = y := by
    funext i
    show Function.update (fun w : Pl F => (0 : Fv F w)) v (y i) v = y i
    rw [Function.update_self]
  have hrs : r s = 1 := by
    show f (fun i => evI F (s i)) * ∏ᶠ w, ψ w (fun i => evFin F w (s i)) = 1
    have h0 : (fun i => evI F (s i)) = 0 := by
      funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
      exact map_zero _
    have h1 : ∀ w, ψ w (fun i => evFin F w (s i)) = 1 := by
      intro w
      by_cases hw : w = v
      · subst hw
        simp [hψ]
      · rw [hψ, Function.update_of_ne hw]
        have h00 : (fun i => evFin F w (s i)) = 0 := by
          funext i
          show Function.update (fun w : Pl F => (0 : Fv F w)) v (y i) w = 0
          rw [Function.update_of_ne hw]
        rw [h00, hstd_def]
        simp
    rw [h0, hf, finprod_congr h1, finprod_one, one_mul]
  have key := congrFun heq s
  change φ₁ (fun i => evFin F v (s i)) * r s = φ₂ (fun i => evFin F v (s i)) * r s at key
  rw [hs, hrs, mul_one, mul_one] at key
  exact key

end PositivityTheory.KCo
