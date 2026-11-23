import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLatticeInvariantSchwartzGlobalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLatticeInvariantSchwartzLocalStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Classical

noncomputable section
namespace GlobalTheory.VacFactor

theorem pure_update_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (w : Pl F) (r : ℂ) (h : (κ → Fv F w) → ℂ)
    (hφ : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1) :
    pure f (Function.update φ w (r • h)) = pure (r • f) (Function.update φ w h) := by
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  rw [GlobalTheory.PureFactor.finprod_update φ w (r • h) hφ x, GlobalTheory.PureFactor.finprod_update φ w h hφ x]
  simp only [SchwartzMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem tens_smul {F : Type} [Field F] [NumberField F] {R κ : Type} (ev : AF F → R) (c : ℂ) (g : (κ → R) → ℂ)
    (r : (κ → AF F) → ℂ) : tens ev (c • g) r = c • tens ev g r := by
  funext x
  simp [tens, mul_assoc]

theorem std_of_off {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (vac φ : ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (hvac : ∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1)
    (U : Finset (Pl F)) (h : ∀ v, v ∉ U → φ v = vac v) :
    ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 := by
  filter_upwards [hvac, U.finite_toSet.compl_mem_cofinite] with v h1 h2
  rw [h v h2, h1]

theorem factor : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (S : Finset (Pl F)) (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ w, w ∉ S → φ w = G.M'.vac w) →
    ∀ Ψ ∈ schA F (Fin a' × Fin (a + a')),
    (∀ w, w ∉ S → ∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ,
      G.M'.co.rho B.ψ γ (pure f φ) = c • pure f φ → G.M'.co.rho B.ψ γ Ψ = c • Ψ) →
    ∃ (m : ℕ) (f' : Fin m → SInf F (Fin a' × Fin (a + a'))) (φ' : Fin m → ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ),
      (∀ i w, φ' i w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧ (∀ i w, w ∉ S → φ' i w = G.M'.vac w) ∧
      Ψ = ∑ i, pure (f' i) (φ' i) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT S f φ hφSB hφvac Ψ hΨ hyp
  have hvstd := hT.geo.hM'.std
  have hvSB : ∀ v, G.M'.vac v ∈ SB (Fin a' × Fin (a + a') → Fv F v) := fun v => (hT.geo.hM'.vac v).1
  have hyp' : ∀ w, w ∉ S → ∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ,
      Acts (evFin F w) (G.M'.co.rho B.ψ γ) (G.M'.vac w) (c • G.M'.vac w) → G.M'.co.rho B.ψ γ Ψ = c • Ψ := by
    intro w hw γ hγ c hc
    have hstd := std_of_off G.M'.vac φ hvstd S hφvac
    obtain ⟨r, hr1, hr2⟩ := GlobalTheory.PureFactor.exists_rest_factor w f φ hstd
    have e : pure f φ = tens (evFin F w) (G.M'.vac w) r := by
      rw [hr2, ← hφvac w hw, Function.update_eq_self]
    refine hyp w hw γ hγ c ?_
    have hR : Rest (evFin F w) (G.M'.vac w) r := ⟨hr1, e ▸ GlobalTheory.TensUniq.pure_mem_schA f φ hφSB hstd⟩
    rw [e, hc r hR, tens_smul]
  obtain ⟨T, m, f₀, φ₀, hSB₀, hstd₀, hsum₀⟩ := GlobalTheory.T.adelic_schwartz_finite_pure_tensors F _ Ψ hΨ
  have hfin : {v | ¬ G.M'.vac v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1}.Finite :=
    Filter.eventually_cofinite.1 hvstd
  have key : ∀ U : Finset (Pl F), ∀ (f : Fin m → SInf F (Fin a' × Fin (a + a')))
      (φ : Fin m → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      (∀ i v, φ i v ∈ SB (Fin a' × Fin (a + a') → Fv F v)) → (∀ i v, v ∉ S → v ∉ U → φ i v = G.M'.vac v) →
      Ψ = ∑ i, pure (f i) (φ i) →
      ∃ (f' : Fin m → SInf F (Fin a' × Fin (a + a'))) (φ' : Fin m → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        (∀ i v, φ' i v ∈ SB (Fin a' × Fin (a + a') → Fv F v)) ∧ (∀ i v, v ∉ S → φ' i v = G.M'.vac v) ∧
        Ψ = ∑ i, pure (f' i) (φ' i) := by
    intro U
    induction U using Finset.induction_on with
    | empty => exact fun f φ h1 h2 h3 => ⟨f, φ, h1, fun i v hv => h2 i v hv (Finset.notMem_empty v), h3⟩
    | insert w U hwU ih =>
      intro f φ h1 h2 h3
      by_cases hwS : w ∈ S
      · refine ih f φ h1 (fun i v hv hvU => h2 i v hv ?_) h3
        rw [Finset.mem_insert]
        rintro (rfl | h)
        exacts [hv hwS, hvU h]
      · have hstd : ∀ i, ∀ᶠ v in Filter.cofinite,
            φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 := fun i =>
          std_of_off G.M'.vac (φ i) hvstd (S ∪ insert w U) fun v hv =>
            h2 i v (fun h => hv (Finset.mem_union_left _ h)) (fun h => hv (Finset.mem_union_right _ h))
        obtain ⟨g, hgSB, hgE, hgsum⟩ := GlobalTheory.T.triple_lattice_invariant_schwartz_global hP F E σ B a a' G X om om' hT w Ψ hΨ (hyp' w hwS) m f φ h1 hstd h3
        choose r hr using fun i => GlobalTheory.T.triple_lattice_invariant_schwartz_local hP F E σ B a a' G X om om' hT w (g i) (hgSB i) (hgE i)
        refine ih (fun i => r i • f i) (fun i => Function.update (φ i) w (G.M'.vac w)) (fun i v => ?_)
          (fun i v hv hvU => ?_) ?_
        · by_cases hvw : v = w
          · subst hvw
            rw [Function.update_self]
            exact hvSB _
          · rw [Function.update_of_ne hvw]
            exact h1 i v
        · by_cases hvw : v = w
          · subst hvw
            rw [Function.update_self]
          · rw [Function.update_of_ne hvw]
            refine h2 i v hv ?_
            rw [Finset.mem_insert]
            rintro (h | h)
            exacts [hvw h, hvU h]
        · rw [hgsum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hr i, pure_update_smul _ _ _ _ _ (hstd i)]
  obtain ⟨f', φ', h1, h2, h3⟩ := key (T ∪ hfin.toFinset) f₀ φ₀ hSB₀ (fun i v _ hv => by
    rw [hstd₀ i v (fun h => hv (Finset.mem_union_left _ h))]
    by_contra hne
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 fun h => hne h.symm))) hsum₀
  exact ⟨m, f', φ', h1, h2, h3⟩

end GlobalTheory.VacFactor
