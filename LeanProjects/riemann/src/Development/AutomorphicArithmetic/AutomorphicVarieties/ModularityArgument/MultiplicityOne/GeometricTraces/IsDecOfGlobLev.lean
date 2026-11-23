import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.RCountAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SmallTendsto
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintTranslate
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.CtEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.MuConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RegCt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.LevelFn
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.ExistsUnitOrdLEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.GeneralLocalHecke
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.InertLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.UConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RChoice
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RUEval
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RFamMatch
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.EvaluationCombinedTestFunction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.ConstantTermParabolicAverage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAutFormsWeightLevelFiniteSumFixedVectorsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocCompIffEquiv
open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Mult

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem isDec_of_globLev {S : Set (Pl E)} {lam : InfinitePlace E → DomWeight n}
    {K₁ K₂ : ∀ w : Pl E, Subgroup (UL n w)} (h : globLev S K₁ = globLev S K₂) {ι : Type}
    {σ : ι → Submodule ℂ (UA E n → ℂ)} (hd : IsDec S lam K₁ σ) : IsDec S lam K₂ σ := by
  have hf : forms S lam K₁ = forms S lam K₂ := by
    unfold forms
    rw [h]
  unfold IsDec at hd ⊢
  rw [← hf, ← h]
  exact hd

private theorem isHecke_mono {G : Type} [Group G] [TopologicalSpace G] {K₁ K₂ : Subgroup G} (hle : K₁ ≤ K₂) {f : G → ℂ}
    (h : IsHecke K₂ f) : IsHecke K₁ f :=
  ⟨h.1, fun k hk x => h.2 k (hle hk) x⟩

private theorem fixed_equiv {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} (e : ρ.Equiv ρ') (φ : H →* G) (K : Subgroup H)
    (h : fixed (ρ.comp φ) K ≠ ⊥) : fixed (ρ'.comp φ) K ≠ ⊥ := by
  obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨e x, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, fun h1 => h0 ?_⟩
  · have h2 := GlobalTheory.LGrp.mem_fixed.1 hx k hk
    have h3 : e (ρ (φ k) x) = ρ' (φ k) (e x) := LinearMap.congr_fun (e.isIntertwining' (φ k)) x
    have h2' : ρ (φ k) x = x := h2
    change ρ' (φ k) (e x) = e x
    rw [← h3, h2']
  · exact e.toLinearEquiv.map_eq_zero_iff.1 h1

end UpperTheory.V.Z.Mult

theorem UpperTheory.V.Z.Mult.rMult :
    UpperTheory.V.Z.Mult.RMult := by
  intro hId hCA hLT hGT hLI hLc hCh hOS hMu E _ _ _ hU n hn hn4 lam
  obtain ⟨a, ha, hA⟩ := hId E hU n hn hn4 lam
  obtain ⟨μ, e, hμ⟩ := hMu E hU
  have key : ∀ π : CuspSub E n, (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π →
      (∀ v, π.HasInfChar v.embedding (infOfWeight (lam v))) → (∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B) →
      ∀ S : Set (Pl E), IsSection S → ∀ K' : ∀ w : Pl E, Subgroup (UL n w),
      IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → (∀ w, ¬ IsSplitAt w → K' w = KL n w) →
      (∀ w ∈ S, IsSplitAt w → ∃ τ, π.IsLocComp w τ ∧ fixed (τ.ρ.comp (UL n w).subtype) (K' w) ≠ ⊥) →
      ∀ (ι : Type) [Fintype ι] (σ : ι → Submodule ℂ (UA E n → ℂ)), IsDec S lam K' σ →
      (Nat.card {i // At π (σ i)} : ℝ) = a := by
    intro π hreg hdual hinf hunr S hS K' hK' hKn hfix ι _ σ hDec
    obtain ⟨Z, B, τ, w₀, f₀, hZ, hZK, hoff, hτ, hw₀, hf₀, htr₀, hsep⟩ := hCh E n hn π hunr μ e hμ S hS K' hK' hKn
    have hKLo : ∀ w, IsOpen (KL n w : Set (UL n w)) := fun w => (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).1
    obtain ⟨K₀, hK₀o, hK₀le, hK₀⟩ := hLc E n w₀ (hZ w₀ hw₀).2 f₀ hf₀
    obtain ⟨K₁, hK₁Z, hK₁o⟩ : ∃ K₁ : ∀ w : Pl E, Subgroup (UL n w), (∀ w ∈ Z, K₁ w = K' w) ∧ ∀ w, w ∉ Z → K₁ w = KL n w :=
      ⟨fun w => if w ∈ Z then K' w else KL n w, fun w h => if_pos h, fun w h => if_neg h⟩
    have hK₁ : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K₁ := by
      refine ⟨fun w => ?_, ?_⟩
      · by_cases h : w ∈ Z
        · rw [hK₁Z w h]
          exact hK'.1 w
        · rw [hK₁o w h]
          exact ⟨hKLo w, le_rfl, fun k hk => hk⟩
      · refine eventually_cofinite.2 (Z.finite_toSet.subset fun w hw => ?_)
        by_contra h
        exact hw (hK₁o w h)
    obtain ⟨K₂, hK₂w, hK₂⟩ : ∃ K₂ : ∀ w : Pl E, Subgroup (UL n w), K₂ w₀ = K₁ w₀ ⊓ K₀ ∧ ∀ w, w ≠ w₀ → K₂ w = K₁ w :=
      ⟨Function.update K₁ w₀ (K₁ w₀ ⊓ K₀), Function.update_self _ _ _, fun w h => Function.update_of_ne h _ _⟩
    have hle : ∀ w, K₂ w ≤ K₁ w := fun w => by
      by_cases h : w = w₀
      · subst h
        rw [hK₂w]
        exact inf_le_left
      · rw [hK₂ w h]
    have hK₂o : ∀ w, w ∉ Z → K₂ w = KL n w := fun w h => by
      rw [hK₂ w (fun e => h (e ▸ hw₀)), hK₁o w h]
    have hK₂L : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K₂ := by
      refine ⟨fun w => ?_, ?_⟩
      · by_cases h : w = w₀
        · subst h
          rw [hK₂w]
          refine ⟨?_, inf_le_left.trans (hK₁.1 w).2.1, fun k hk => hk⟩
          rw [Subgroup.coe_inf]
          exact (hK₁.1 w).1.inter hK₀o
        · rw [hK₂ w h]
          exact hK₁.1 w
      · refine eventually_cofinite.2 (Z.finite_toSet.subset fun w hw => ?_)
        by_contra h
        exact hw (hK₂o w h)
    have hg1 : globLev S K' = globLev S K₁ := hOS E n S K' K₁ fun w hw => by
      by_cases h : w ∈ Z
      · exact (hK₁Z w h).symm
      · rw [hK₁o w h]
        exact hZK w hw h
    have hDec₁ : IsDec S lam K₁ σ := isDec_of_globLev hg1 hDec
    obtain ⟨-, ι₂, _, σ₂, d1, d2, d3, -⟩ := GlobalTheory.T.unitaryAutForms_weight_level_finite_sum_fixed_vectors E hU n hn S hS lam K₂ hK₂L
    have hDec₂ : IsDec S lam K₂ σ₂ := ⟨d1, d2, d3⟩
    have hfx : ∀ w ∈ Z, fixed ((τ w).ρ.comp (UL n w).subtype) (K₁ w) ≠ ⊥ := fun w hw => by
      obtain ⟨t, ht, hne⟩ := hfix w (hZ w hw).1 (hZ w hw).2
      obtain ⟨eq⟩ := GlobalTheory.CuspRep.LocUniq.isLocComp_unique π w t (τ w) ht (hτ w hw)
      rw [hK₁Z w hw]
      exact fixed_equiv eq _ _ hne
    have hg : ∀ w : Pl E, ∃ g : GLw n w → ℂ, w ∈ Z → Lc (KGL w n) g ∧
        (∀ K ≤ K₁ w, IsHecke K fun x : UL n w => g x.1) ∧ trc (τ w).ρ (KGL w n) g ≠ 0 := fun w => by
      by_cases hw : w ∈ Z
      · obtain ⟨g, h1, h2, h3⟩ := hLI E n w (hZ w hw).2 (K₁ w) (hK₁.1 w).1 (hK₁.1 w).2.1
        exact ⟨g, fun _ => ⟨h1, h2, h3 _ (hfx w hw)⟩⟩
      · exact ⟨0, fun h => absurd h hw⟩
    choose g hg using hg
    have hc₂ : (Nat.card {i // At π (σ₂ i)} : ℝ) = a := by
      refine hA π hreg hdual hinf μ e hμ S hS Z hZ B τ (Function.update g w₀ f₀) hoff
        (fun w hw => ⟨hτ w hw, ?_⟩) ⟨w₀, hw₀, ?_⟩ K₂ hK₂L hK₂o (fun w hw => ?_) ι₂ σ₂ hDec₂
      · by_cases h : w = w₀
        · subst h
          rw [Function.update_self]
          exact ⟨hf₀, htr₀⟩
        · rw [Function.update_of_ne h]
          exact ⟨(hg w hw).1, (hg w hw).2.2⟩
      · rw [Function.update_self]
        exact hsep
      · by_cases h : w = w₀
        · subst h
          rw [Function.update_self, hK₂w]
          exact isHecke_mono inf_le_right hK₀
        · rw [Function.update_of_ne h, hK₂ w h]
          exact (hg w hw).2.1 _ le_rfl
    obtain ⟨J, _, C, hC, hF⟩ := hCA E hU n hn hn4 π hreg hdual S hS lam Z hZ B τ (fun w h => (hoff w h).1) hτ
      K₁ hK₁ hK₁o ι σ hDec₁
    obtain ⟨J', _, C', hC', hF'⟩ := hCA E hU n hn hn4 π hreg hdual S hS lam Z hZ B τ (fun w h => (hoff w h).1) hτ
      K₂ hK₂L hK₂o ι₂ σ₂ hDec₂
    obtain ⟨T, e₁, e₂, hT, hd, h1, h0⟩ := rSep places E n S hS Z (J ⊕ J') B (Sum.elim C C')
      (by rintro (j | j); exacts [hC j, hC' j])
    have hh₁ : ∀ w ∈ Z, IsHecke (K₁ w) fun x : UL n w => g w x.1 := fun w hw => (hg w hw).2.1 _ le_rfl
    have hh₂ : ∀ w ∈ Z, IsHecke (K₂ w) fun x : UL n w => g w x.1 := fun w hw => (hg w hw).2.1 _ (hle w)
    obtain ⟨t₁, r₁⟩ := hF g hh₁ T hT hd e₁ e₂ h1 (fun j => h0 (Sum.inl j)) 1
    obtain ⟨-, r₂⟩ := hF' g hh₂ T hT hd e₁ e₂ h1 (fun j => h0 (Sum.inr j)) 1
    have hlt := hLT E hU n hn S hS lam K₁ K₂ hK₁ hK₂L hle _ t₁
    have hd0 := (hGT E hU n hn S hS lam K₁ hK₁).1
    have hP : ∏ w ∈ Z, trc (τ w).ρ (KGL w n) (g w) ≠ 0 := Finset.prod_ne_zero_iff.2 fun w hw => (hg w hw).2.2
    have heq := (r₂ le_rfl).symm.trans (hlt.trans (r₁ le_rfl))
    have hcc := mul_right_cancel₀ hP (mul_left_cancel₀ hd0 heq)
    have hc : Nat.card {i // At π (σ i)} = Nat.card {i // At π (σ₂ i)} := by exact_mod_cast hcc.symm
    rw [hc]
    exact hc₂
  by_cases hN : ∃ m : ℕ, (m : ℝ) = a
  · obtain ⟨m, rfl⟩ := hN
    refine ⟨m, by exact_mod_cast ha, fun π h1 h2 h3 h4 S hS K' hK h5 h6 ι _ σ hd => ?_⟩
    exact_mod_cast key π h1 h2 h3 h4 S hS K' hK h5 h6 ι σ hd
  · exact ⟨1, one_pos, fun π h1 h2 h3 h4 S hS K' hK h5 h6 ι _ σ hd =>
      absurd ⟨_, key π h1 h2 h3 h4 S hS K' hK h5 h6 ι σ hd⟩ hN⟩
