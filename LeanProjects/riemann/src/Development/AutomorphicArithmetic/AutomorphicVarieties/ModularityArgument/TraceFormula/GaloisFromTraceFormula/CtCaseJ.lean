import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.ctCaseJ :
    StepT → SplitLim → SatComb → CDAddG → AbsInf → MToLaws → CtCaseJ := by
  intro hS hL hC hA hI hM E _ _ _ r s hr hs bad ih₁ ih₂ K W m₀ X hK hW
  obtain ⟨K₁, W₁, K₂, W₂, l₁, f₁, l₂, f₂, hS⟩ := hS E r s bad K W hK hW
  obtain ⟨T, hT⟩ := hL E m₀ ((-((s : ℝ) / 2) : ℝ) : ℂ) (((r : ℝ) / 2 : ℝ) : ℂ)
  choose J₁ i₁ D₁ C₁ a₁ b₁ using fun p : T => ih₁ K₁ W₁ p.1.1 l₁ f₁
  choose J₂ i₂ D₂ C₂ a₂ b₂ using fun p : T => ih₂ K₂ W₂ p.1.2 l₂ f₂
  have hν := fun x : ℝ => GlobalTheory.Mem.Chr.CharModel.absChar_isAbsPow (F := E) x
  choose D d₁ d₂ d₃ using fun j : Σ p : T, J₁ p × J₂ p => hA E r s (D₁ j.1 j.2.1) (D₂ j.1 j.2.2)
    (GlobalTheory.Mem.Chr.CharModel.absChar E ((-((s : ℝ) / 2) : ℝ) : ℂ)) (GlobalTheory.Mem.Chr.CharModel.absChar E (((r : ℝ) / 2 : ℝ) : ℂ)) hr hs
  refine ⟨Σ p : T, J₁ p × J₂ p, inferInstance, D, _, fun j => ⟨fun π _ => d₁ j π, fun w hw =>
    d₂ j w _ _ ((hν _).1 w) ((hν _).1 w) ((a₁ j.1 j.2.1).2 w hw) ((a₂ j.1 j.2.2).2 w hw)⟩, fun φ m B h hm => ?_⟩
  choose φ₁ φ₂ m₁ m₂ B₁ B₂ e₁ e₂ e₃ e₄ using fun k => hS (φ k) (m k) (B k) (h k).1 (h k).2
  obtain ⟨p, hp, σ, hσ, t₁, t₂⟩ := hT m m₁ m₂ e₃ hm
  obtain ⟨j₁, σ₁, hσ₁, v₁, u₁⟩ := b₁ ⟨p, hp⟩ (fun k => φ₁ (σ k)) _ (fun k => B₁ (σ k)) (fun k => ⟨e₁ _, trivial⟩) t₁
  obtain ⟨j₂, σ₂, hσ₂, v₂, u₂⟩ := b₂ ⟨p, hp⟩ (fun k => φ₂ (σ (σ₁ k))) (fun k => m₂ (σ (σ₁ k))) (fun k => B₂ (σ (σ₁ k)))
    (fun k => ⟨e₂ _, trivial⟩) fun τ ε hε => hσ₁.tendsto_atTop.eventually (t₂ τ ε hε)
  have h₀ : m₀ = fun t => (p.1 t).map (· + ((-((s : ℝ) / 2) : ℝ) : ℂ)) + (p.2 t).map (· + (((r : ℝ) / 2 : ℝ) : ℂ)) := by
    obtain ⟨hu, hsh, hadd⟩ := hM E
    have c₁ := hsh _ _ (fun _ => ((-((s : ℝ) / 2) : ℝ) : ℂ)) _ t₁ tendsto_const_nhds
    have c₂ := hsh _ _ (fun _ => (((r : ℝ) / 2 : ℝ) : ℂ)) _ t₂ tendsto_const_nhds
    have c₃ := hadd _ _ _ _ c₁ c₂
    refine hu (fun k => m (σ k)) _ _ (fun τ ε hε => hσ.tendsto_atTop.eventually (hm τ ε hε)) ?_
    have : (fun k => m (σ k)) = fun k t => (m₁ (σ k) t).map (· + ((-((s : ℝ) / 2) : ℝ) : ℂ)) +
        (m₂ (σ k) t).map (· + (((r : ℝ) / 2 : ℝ) : ℂ)) := by
      funext k t
      exact e₃ _ t
    rw [this]
    exact c₃
  refine ⟨⟨⟨p, hp⟩, j₁, j₂⟩, fun k => σ (σ₁ (σ₂ k)), hσ.comp (hσ₁.comp hσ₂), fun τ => ?_, fun w hw => ?_⟩
  · rw [d₃ ⟨⟨p, hp⟩, j₁, j₂⟩ τ, h₀]
    have key : ∀ (n : ℕ) (D' : CD E n) (z : ℝ) (x : (E →+* ℂ) → Multiset ℂ), D'.Inf x →
        ∑ i, ((D'.P i).twist (GlobalTheory.Mem.Chr.CharModel.absChar E (z : ℂ))).infChar τ = (x τ).map (· + (z : ℂ)) := by
      intro n D' z x hx
      rw [← hx τ]
      simp only [fun i => ((hI E _ (D'.P i) (z : ℂ) τ).2)]
      exact (map_sum (Multiset.mapAddMonoidHom (· + (z : ℂ))) _ _).symm
    exact congrArg₂ (· + ·) (key _ _ _ _ v₁) (key _ _ _ _ v₂)
  have := hC.2 (qV E w) r s _ _ _ _ ((GlobalTheory.Mem.Chr.CharModel.absChar E ((-((s : ℝ) / 2) : ℝ) : ℂ)).val w)
    ((GlobalTheory.Mem.Chr.CharModel.absChar E (((r : ℝ) / 2 : ℝ) : ℂ)).val w) (qV_ne_zero w)
    (fun i => (u₁ w hw i).comp hσ₂.tendsto_atTop) (u₂ w hw)
  intro i
  refine (this i).congr fun k => ?_
  exact congrArg (fun M => satEig (qV E w) (r + s) M i) (e₄ _ _ _ (hν _) (hν _) w hw).symm
