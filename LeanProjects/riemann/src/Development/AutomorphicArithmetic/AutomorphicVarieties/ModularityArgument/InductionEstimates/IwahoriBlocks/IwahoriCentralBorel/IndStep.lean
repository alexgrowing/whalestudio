import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.TensSimple
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.TensIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.IndTens

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.indStep :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V] [Module ℂ V] {Y : Type} [AddCommGroup Y] [Module ℂ Y] (P : Subgroup G) (ρ : Representation ℂ P V) (y : Representation ℂ (P × Γ) Y) (f : V →ₗ[ℂ] Y), LocOk P ρ →
      y.IsIrreducible → f ≠ 0 → (∀ p v, f (ρ p v) = y (p, 1) (f v)) →
      SimpleG (IndF P.subtype (y.comp (MonoidHom.inl P Γ)) ⊤) fun c : Γ => y (1, c) := by
  intro G _ _ _ Γ _ V _ _ Y _ _ P ρ y f hL hy hf hfe
  obtain ⟨B, _, _, m, e, hm, he⟩ := tensIso ρ y f hL.irr hL.schur hy hf hfe
  obtain ⟨K, hK, hPK⟩ := hL.iwa
  obtain ⟨E, hE⟩ := indTens P K ρ m hK hPK
  have hirr := (tensSimple (smInd P ρ) m hL.indIrr hL.indSchur hm).1
  let L : GlobalTheory.PRep.smoothPart (ind P ρ) ⊗[ℂ] B →ₗ[ℂ] (G → Y) :=
    (e.toLinearMap.compLeft G).comp ((Submodule.subtype _).comp E.toLinearMap)
  have hLa : ∀ x t, L x t = e ((E x).1 t) := fun _ _ => rfl
  have hact : ∀ g c x t, L (extTensor (smInd P ρ) m (g, c) x) t = y (1, c) (L x (t * g)) := by
    intro g c x t
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have h1 : extTensor (smInd P ρ) m (g, c) (a ⊗ₜ[ℂ] b) = smInd P ρ g a ⊗ₜ[ℂ] m c b := by
        simp [extTensor]
      have h2 : extTensor ρ m (1, c) (a.1.1 (t * g) ⊗ₜ[ℂ] b) = a.1.1 (t * g) ⊗ₜ[ℂ] m c b := by
        simp [extTensor]
      rw [h1, hLa, hLa, hE, hE, ← he, h2]
      rfl
    | add x x' hx hx' => simp only [map_add, Pi.add_apply, hx, hx']
  have hsurj : ∀ z ∈ IndF P.subtype (y.comp (MonoidHom.inl P Γ)) ⊤, ∃ x, L x = z := by
    intro z hz
    have hlaw : ∀ (p : P) g, z (p * g) = y (p, 1) (z g) := hz.1.2
    have hz' : (fun g => e.symm (z g)) ∈ IndF P.subtype ((extTensor ρ m).comp (MonoidHom.inl P Γ)) ⊤ := by
      refine ⟨⟨fun _ => trivial, fun p g => ?_⟩, ?_⟩
      · apply e.injective
        show e (e.symm (z (p * g))) = e (extTensor ρ m (p, 1) (e.symm (z g)))
        rw [he, e.apply_symm_apply, e.apply_symm_apply, hlaw]
      · refine GlobalTheory.SmGL.mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds hz.2 (by simp)) fun u hu => ?_)
        funext x
        have h2 : z (x * u) = z x := congrFun hu x
        show e.symm (z (x * u)) = e.symm (z x)
        rw [h2]
    refine ⟨E.symm ⟨_, hz'⟩, funext fun t => ?_⟩
    rw [hLa, E.apply_symm_apply]
    exact e.apply_symm_apply _
  intro Q hQ hG hΓ
  let Q' : Subrepresentation (extTensor (smInd P ρ) m) :=
    ⟨Q.comap L, by
      rintro ⟨g, c⟩ x hx
      have h1 := hΓ c _ (hG g _ hx)
      have h2 : L (extTensor (smInd P ρ) m (g, c) x) = fun t => y (1, c) (L x (t * g)) := funext (hact g c x)
      show L _ ∈ Q
      rw [h2]
      exact h1⟩
  rcases hirr.eq_bot_or_eq_top Q' with h | h
  · left
    refine (Submodule.eq_bot_iff _).2 fun q hq => ?_
    obtain ⟨x, rfl⟩ := hsurj q (hQ hq)
    have hx : x ∈ Q'.toSubmodule := hq
    rw [h] at hx
    have hx0 : x = 0 := hx
    rw [hx0, map_zero]
  · right
    refine le_antisymm hQ fun z hz => ?_
    obtain ⟨x, rfl⟩ := hsurj z hz
    have hx : x ∈ Q'.toSubmodule := by rw [h]; trivial
    exact hx
