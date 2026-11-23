import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Ga.badClosed :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (r : G L Ω →* GL (Fin 2) (Qbar l)), Continuous r → (Continuous fun g => Ga.uf (r g)) ∧ (Continuous fun g : G L Ω => Ga.ep l g) ∧ IsClosed (Ga.Bad r) := by
  intro L Ω _ _ _ _ _ l _ r hr
  have hm : Continuous fun g => ((r g : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) :=
    Units.continuous_val.comp hr
  have hU : Continuous fun g => Ga.uf (r g) := by
    unfold Ga.uf Ga.tr
    refine ((hm.matrix_trace.pow 2).div hm.matrix_det fun g => ?_).sub continuous_const
    exact (Matrix.isUnits_det_units (r g)).ne_zero
  have hE : Continuous fun g : G L Ω => Ga.ep l g := by
    have hu : Continuous fun g : G L Ω => ((cycZ L Ω l g : ℤ_[l]ˣ) : ℤ_[l]) :=
      (Units.continuous_val (M := ℤ_[l])).comp (continuous_cycZ L Ω l)
    have hz : Continuous fun g : G L Ω => (((cycZ L Ω l g : ℤ_[l]) : ℚ_[l])) :=
      continuous_subtype_val.comp hu
    have h := (continuous_algebraMap ℚ_[l] (Qbar l)).comp hz
    convert h using 1
    funext g
    rfl
  have hne : ∀ g : G L Ω, Ga.ep l g ≠ 0 := fun g => (cycBar L Ω l g).ne_zero
  refine ⟨hU, hE, ?_⟩
  have hset : Ga.Bad r = ⋃ m ∈ Finset.Icc (-2 : ℤ) 2,
      {g | Ga.uf (r g) ^ 2 - 2 = Ga.ep l g ^ m + Ga.ep l g ^ (-m)} := by
    ext g
    simp only [Ga.Bad, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_Icc, exists_prop, abs_le]
  rw [hset]
  refine isClosed_biUnion_finset fun m _ => isClosed_eq ((hU.pow 2).sub continuous_const) ?_
  exact (hE.zpow₀ m fun g => Or.inl (hne g)).add (hE.zpow₀ (-m) fun g => Or.inl (hne g))
