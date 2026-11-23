import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepPureTensorLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalPointModelEvalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorMemSchwartzAdelicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharContinuousNontrivialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSpanTranslatesOfNonzeroSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepLatticeScalarActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepScalarCharOfSignatureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPt

noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.FinComm

section Pure

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem eventually_int (x : κ → AF F) :
    ∀ᶠ u in cofinite, ∀ i, evFin F u (x i) ∈ u.adicCompletionIntegers F :=
  Filter.eventually_all.mpr fun i => (x i).2.2

theorem finite_mulSupport (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (hφ : ∀ᶠ u in cofinite, φ u = indO u)
    (x : κ → AF F) : (Function.mulSupport fun u => φ u (fun i => evFin F u (x i))).Finite := by
  have h : ∀ᶠ u in cofinite, φ u (fun i => evFin F u (x i)) = 1 := by
    filter_upwards [hφ, eventually_int x] with u hu hx
    rw [hu]
    simp [indO, Set.indicator, hx]
  exact (Filter.eventually_cofinite.mp h).subset fun u hu hp => hu hp

theorem pure_update (f : SInf F κ) (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (hφ : ∀ᶠ u in cofinite, φ u = indO u)
    (v : Pl F) (g : (κ → Fv F v) → ℂ) (x : κ → AF F) :
    pure f (Function.update φ v g) x = g (fun i => evFin F v (x i)) *
      (f (fun i => evI F (x i)) * ∏ᶠ (u) (_ : u ≠ v), φ u (fun i => evFin F u (x i))) := by
  have hφ' : ∀ᶠ u in cofinite, Function.update φ v g u = indO u := by
    filter_upwards [hφ, (Set.finite_singleton v).compl_mem_cofinite] with u hu hv
    rw [Function.update_of_ne hv, hu]
  have hfin := finite_mulSupport _ hφ' x
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  rw [← mul_finprod_cond_ne v hfin, Function.update_self]
  have : (∏ᶠ (u) (_ : u ≠ v), Function.update φ v g u (fun i => evFin F u (x i))) =
      ∏ᶠ (u) (_ : u ≠ v), φ u (fun i => evFin F u (x i)) :=
    finprod_congr fun u => finprod_congr fun hu => by rw [Function.update_of_ne hu]
  rw [this]
  ring

theorem pure_update_zero (f : SInf F κ) (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ)
    (hφ : ∀ᶠ u in cofinite, φ u = indO u) (v : Pl F) : pure f (Function.update φ v 0) = 0 := by
  funext x
  rw [pure_update f φ hφ]
  simp

theorem pure_update_add (f : SInf F κ) (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ)
    (hφ : ∀ᶠ u in cofinite, φ u = indO u) (v : Pl F) (g h : (κ → Fv F v) → ℂ) :
    pure f (Function.update φ v (g + h)) = pure f (Function.update φ v g) + pure f (Function.update φ v h) := by
  funext x
  simp only [Pi.add_apply, pure_update f φ hφ]
  ring

theorem pure_update_smul (f : SInf F κ) (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ)
    (hφ : ∀ᶠ u in cofinite, φ u = indO u) (v : Pl F) (a : ℂ) (g : (κ → Fv F v) → ℂ) :
    pure f (Function.update φ v (a • g)) = a • pure f (Function.update φ v g) := by
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, pure_update f φ hφ]
  ring

end Pure

variable {F : Type} [Field F] [NumberField F]

theorem at_of_mem_latAtV {E : Type} [Field E] [NumberField E] [Algebra F E] {n d : ℕ} {X : Spc F E n}
    {W : Spc F E d} {v : Pl F} {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v) :
    At (evFin F v) γ := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, -, x, -, y, -, rfl⟩ := hz
    intro u hu
    rw [← smul_assoc, ha u hu, zero_smul]
  | zero => intro u _; exact smul_zero u
  | add z z' _ _ hz hz' => intro u hu; rw [smul_add, hz u hu, hz' u hu, add_zero]
  | neg z _ hz => intro u hu; rw [smul_neg, hz u hu, neg_zero]

theorem commutant_pure : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ A : Module.End ℂ ((Fin n × Fin d → AF F) → ℂ), (∀ Φ ∈ schA F (Fin n × Fin d), A Φ ∈ schA F (Fin n × Fin d)) →
    (∀ (v : Pl F) (w : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) w →
      ∀ Φ ∈ schA F (Fin n × Fin d), A (M.co.rho B.ψ w Φ) = M.co.rho B.ψ w (A Φ)) →
    ∀ (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) →
      (∀ᶠ v in cofinite, φ v = M.vac v) → ∃ f₁ : SInf F (Fin n × Fin d), A (pure f φ) = pure f₁ φ := by
  intro _ F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW hM A hA hcomm f φ hφSB hφv
  have hvacO : ∀ᶠ u in cofinite, M.vac u = indO u := by
    filter_upwards [hM.std] with u hu
    rw [hu]
    rfl
  have hvacSB : ∀ u, M.vac u ∈ SB _ := fun u => (hM.vac u).1
  obtain ⟨c, hc⟩ := GlobalTheory.T.weil_rep_lattice_scalar_action M B.ψ hM
  have hpv : pure f M.vac ∈ schA F _ := GlobalTheory.T.pure_tensor_mem_schwartz_adelic f M.vac hvacSB hvacO
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.T.weil_rep_scalar_char_of_signature B X W M r s r' s' hB hX hW hM c hc (A (pure f M.vac)) (hA _ hpv)
    fun v γ hγ => by rw [← hcomm v γ (at_of_mem_latAtV hγ) _ hpv, hc v γ hγ f, map_smul]
  have key : ∀ S : Finset (Pl F), ∀ φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ, (∀ v, φ v ∈ SB _) →
      (∀ v ∉ S, φ v = M.vac v) → A (pure f φ) = pure f₁ φ := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro φ _ h
      obtain rfl : φ = M.vac := funext fun v => h v (Finset.notMem_empty v)
      exact hf₁
    | insert v S hvS ih =>
      intro φ hSB hS
      have h0SB : ∀ u, Function.update φ v (M.vac v) u ∈ SB _ := fun u => by
        by_cases h : u = v
        · subst h; rw [Function.update_self]; exact hvacSB u
        · rw [Function.update_of_ne h]; exact hSB u
      have h0S : ∀ u ∉ S, Function.update φ v (M.vac v) u = M.vac u := fun u hu => by
        by_cases h : u = v
        · subst h; rw [Function.update_self]
        · rw [Function.update_of_ne h]; exact hS u (by simp [h, hu])
      have h0O : ∀ᶠ u in cofinite, Function.update φ v (M.vac v) u = indO u := by
        filter_upwards [hvacO, S.finite_toSet.compl_mem_cofinite] with u hu huS
        rw [h0S u huS, hu]
      have hIH := ih _ h0SB h0S
      have hmem0 := GlobalTheory.T.pure_tensor_mem_schwartz_adelic f _ h0SB h0O
      obtain ⟨hc1, hne⟩ := GlobalTheory.T.standard_char_continuous_nontrivial B.ψ hB.std v
      have hφv : φ v ∈ Submodule.span ℂ (Set.range fun p => locOp B.ψ v p (M.vac v)) :=
        GlobalTheory.T.local_span_translates_of_nonzero_schwartz B.ψ v hc1 hne (M.vac v) (φ v) (hvacSB v) (hM.vac v).2.1 (hSB v)
      have hφeq : φ = Function.update (Function.update φ v (M.vac v)) v (φ v) := by
        rw [Function.update_idem, Function.update_eq_self]
      have step : ∀ g ∈ Submodule.span ℂ (Set.range fun p => locOp B.ψ v p (M.vac v)),
          A (pure f (Function.update (Function.update φ v (M.vac v)) v g)) =
            pure f₁ (Function.update (Function.update φ v (M.vac v)) v g) := by
        intro g hg
        induction hg using Submodule.span_induction with
        | mem g hg =>
          obtain ⟨p, rfl⟩ := hg
          obtain ⟨w, hw, hwp⟩ := GlobalTheory.T.exists_local_point_model_eval M v p
          have e1 := GlobalTheory.T.weil_rep_pure_tensor_local M B.ψ v w hw f _ h0O
          have e2 := GlobalTheory.T.weil_rep_pure_tensor_local M B.ψ v w hw f₁ _ h0O
          rw [hwp, Function.update_self, Function.update_idem] at e1 e2
          simp only [Function.update_idem]
          rw [← e1, hcomm v w hw _ hmem0, hIH, e2]
        | zero => rw [pure_update_zero f _ h0O, pure_update_zero f₁ _ h0O, map_zero]
        | add g h _ _ hg hh =>
          rw [pure_update_add f _ h0O, pure_update_add f₁ _ h0O, map_add, hg, hh]
        | smul a g _ hg => rw [pure_update_smul f _ h0O, pure_update_smul f₁ _ h0O, map_smul, hg]
      rw [hφeq]
      exact step _ hφv
  have hfin : {v | φ v ≠ M.vac v}.Finite := Filter.eventually_cofinite.mp hφv
  exact ⟨f₁, key hfin.toFinset φ hφSB fun v hv => by
    by_contra h
    exact hv (hfin.mem_toFinset.mpr h)⟩

end GlobalTheory.FinComm
