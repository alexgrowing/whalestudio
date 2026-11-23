import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.IsCompactMaximalPairPlace

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

private theorem cv_eq_conv {G : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) {f g : G → ℂ}
    (hf : GlobalTheory.BCT.IsHecke K f) (hg : GlobalTheory.BCT.IsHecke K g) :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv K f g = Formalism.UG.conv K f g := by
  funext y
  have hst : K ≤ GlobalTheory.BCT.rStab (fun z => f z * g (z⁻¹ * y)) := by
    intro k hk z
    show f (z * k) * g ((z * k)⁻¹ * y) = f z * g (z⁻¹ * y)
    rw [(hf.2 k hk z).2, mul_inv_rev, mul_assoc, (hg.2 k⁻¹ (K.inv_mem hk) _).1]
  unfold UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ K K _ le_rfl hst (by simp [Subgroup.relIndex_self]),
    Subgroup.relIndex_self, Nat.cast_one, inv_one, one_mul]
  rfl

private theorem biInv_of_hecke {G : Type} [Group G] [TopologicalSpace G] {K : Subgroup G} {f : G → ℂ}
    (hf : GlobalTheory.BCT.IsHecke K f) : Formalism.UG.IsBiInv K f := by
  intro a b x
  rw [(hf.2 b b.2 _).2, (hf.2 a a.2 x).1]

private theorem cv_comm {E : Type} [Field E] [NumberField E] (n : ℕ) (w : GlobalTheory.BCT.Pl E)
    {f g : GlobalTheory.BCT.GLw n w → ℂ} (hf : GlobalTheory.BCT.IsHecke (GlobalTheory.LFun.KGL w n) f)
    (hg : GlobalTheory.BCT.IsHecke (GlobalTheory.LFun.KGL w n) g) :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv (GlobalTheory.LFun.KGL w n) f g = UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv (GlobalTheory.LFun.KGL w n) g f := by
  rw [cv_eq_conv _ hf hg, cv_eq_conv _ hg hf]
  exact Formalism.UG.P.heckecomm_gelfand (GlobalTheory.LFun.KGL w n) Formalism.UG.P.heckecomm_tr Formalism.UG.P.heckecomm_tr_mul
    Formalism.UG.P.heckecomm_tr_tr (fun x hx => Formalism.UG.P.heckecomm_tr_mem _ x hx)
    (Formalism.UG.P.heckecomm_tr_dc Formalism.UG.P.cartan_decomposition_holds E w n) f g (biInv_of_hecke hf) (biInv_of_hecke hg)

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.sphOp_pf :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.CvOp → SphOp := by
  intro hCv E _ _ _ n w V _ _ ρ f g hf hg x hx
  obtain ⟨hKo, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
  have h₁ := (hCv _ _ hKo hKc V ρ f g hf hg x hx).1
  have h₂ := (hCv _ _ hKo hKc V ρ g f hg hf x hx).1
  rw [cv_comm n w hf hg] at h₁
  exact h₁.symm.trans h₂
