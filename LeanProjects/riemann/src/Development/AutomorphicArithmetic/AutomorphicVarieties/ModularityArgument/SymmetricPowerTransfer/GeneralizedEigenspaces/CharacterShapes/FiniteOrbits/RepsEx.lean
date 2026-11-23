import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LocalLevelOutsideSigma

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem trim {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ) (y : DA Δ) (hy : D.Off y) :
    ∃ t w : DA Δ, w ∈ D.U2 ∧ t * w = y ∧ D.Off t ∧ {v | t.1 v ≠ 1}.Finite := by
  classical
  let P : Pl F → Prop := fun v => y.1 v ∈ KD ((cv v) Δ) (Ov v) ∧ v ∉ D.Sg
  have hfin : {v | y.1 v ∉ KD ((cv v) Δ) (Ov v)}.Finite := Filter.eventually_cofinite.mp y.2
  have hbad : {v | ¬ P v}.Finite := by
    refine (hfin.union D.Sg.finite_toSet).subset ?_
    intro v hv
    by_cases h1 : y.1 v ∈ KD ((cv v) Δ) (Ov v)
    · exact Or.inr (by_contra fun h2 => hv ⟨h1, h2⟩)
    · exact Or.inl h1
  refine ⟨⟨fun v => if P v then 1 else y.1 v, ?_⟩, ⟨fun v => if P v then y.1 v else 1, ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine Filter.eventually_cofinite.mpr (hbad.subset ?_)
    intro v hv h
    apply hv
    show (if P v then 1 else y.1 v) ∈ KD ((cv v) Δ) (Ov v)
    rw [if_pos h]
    exact one_mem _
  · show ∀ᶠ v in Filter.cofinite, (if P v then y.1 v else 1) ∈ KD ((cv v) Δ) (Ov v)
    refine Filter.Eventually.of_forall fun v => ?_
    by_cases h : P v
    · rw [if_pos h]
      exact h.1
    · rw [if_neg h]
      exact one_mem _
  · simp only [Dat.U2, RPG.box, Subgroup.mem_iInf, Subgroup.mem_comap]
    intro v
    show (if P v then y.1 v else 1) ∈ D.J2v v
    by_cases h : P v
    · rw [if_pos h, Dat.J2v, if_neg h.2]
      exact h.1
    · rw [if_neg h]
      exact one_mem _
  · refine Subtype.ext (funext fun v => ?_)
    show (if P v then 1 else y.1 v) * (if P v then y.1 v else 1) = y.1 v
    split_ifs <;> simp
  · intro v hv
    show (if P v then 1 else y.1 v) = 1
    split_ifs
    · rfl
    · exact hy v hv
  · refine hbad.subset ?_
    intro v hv h
    apply hv
    show (if P v then 1 else y.1 v) = 1
    rw [if_pos h]

theorem UpperTheory.V.Z.Sym.So.repsEx :
    UpperTheory.V.Z.Sym.So.RepsEx := by
  intro F _ _ Δ A hA hCR ι hι
  classical
  obtain ⟨Y, hY, hdec⟩ := hCR F Δ A.dat (datOk F Δ A hA).1 ι hι
  let f : DA Δ → DA Δ := fun y => if h : A.dat.Off y then (trim A.dat y h).choose else y
  refine ⟨Y.image f, ?_, ?_⟩
  · intro y' hy'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hy'
    obtain ⟨w, -, -, ht, hfin⟩ := (trim A.dat y (hY y hy)).choose_spec
    simp only [f, dif_pos (hY y hy)]
    exact ⟨ht, hfin⟩
  · intro g
    obtain ⟨γ, s, hs, y, hy, u, hu, rfl⟩ := hdec g
    obtain ⟨w, hw, hty, -, -⟩ := (trim A.dat y (hY y hy)).choose_spec
    refine ⟨γ, s, hs, f y, Finset.mem_image_of_mem f hy, w * u, mul_mem hw hu, ?_⟩
    simp only [f, dif_pos (hY y hy)]
    conv_lhs => rw [← hty]
    simp only [mul_assoc]

end
