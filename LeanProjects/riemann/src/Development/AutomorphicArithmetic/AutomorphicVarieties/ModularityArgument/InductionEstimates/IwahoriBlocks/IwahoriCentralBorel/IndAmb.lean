import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.IndProdG

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem indF_stable {G H Y : Type} [Group G] [Group H] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace G]
    [IsTopologicalGroup G] (j : H →* G) (y : Representation ℂ H Y) (X : Submodule ℂ Y) (g : G) (f : G → Y)
    (hf : f ∈ IndF j y X) : rightReg ℂ G Y g f ∈ IndF j y X := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hf
  refine ⟨⟨fun x => h1 (x * g), fun h x => ?_⟩, ?_⟩
  · show f (j h * x * g) = y h (f (x * g))
    rw [mul_assoc, h2]
  · have h4 : IsOpen {a : G | rightReg ℂ G Y a f = f} := h3
    have h5 := h4.preimage (f := fun a : G => g⁻¹ * a * g) (by fun_prop)
    show IsOpen {a : G | rightReg ℂ G Y a (rightReg ℂ G Y g f) = rightReg ℂ G Y g f}
    convert h5 using 1
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · intro h
      funext x
      have := congrFun h (x * g⁻¹)
      change f (x * g⁻¹ * a * g) = f (x * g⁻¹ * g) at this
      change f (x * (g⁻¹ * a * g)) = f x
      simpa [mul_assoc] using this
    · intro h
      funext x
      have := congrFun h (x * g)
      change f (x * g * (g⁻¹ * a * g)) = f (x * g) at this
      change f (x * a * g) = f (x * g)
      simpa [mul_assoc] using this

private theorem simple_of_sub {G H Y : Type} [Group G] [Group H] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace G]
    [IsTopologicalGroup G] (j : H →* G) (y : Representation ℂ H Y) (X : Submodule ℂ Y) (y' : Representation ℂ H X)
    (hy : ∀ h v, (y' h v : Y) = y h v)
    (H' : ∀ Q ≤ IndF j y' ⊤, (∀ g, ∀ f ∈ Q, rightReg ℂ G X g f ∈ Q) → Q = ⊥ ∨ Q = IndF j y' ⊤) :
    SimpleIn (rightReg ℂ G Y) (IndF j y X) := by
  refine ⟨fun g f hf => indF_stable j y X g f hf, fun Q hQ hst => ?_⟩
  let Φ : (G → X) →ₗ[ℂ] (G → Y) := X.subtype.compLeft G
  have hΦ : ∀ f x, Φ f x = (f x : Y) := fun _ _ => rfl
  have hmem : ∀ f, f ∈ IndF j y' ⊤ ↔ Φ f ∈ IndF j y X := by
    intro f
    have hs : {a : G | rightReg ℂ G X a f = f} = {a : G | rightReg ℂ G Y a (Φ f) = Φ f} := by
      ext a
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h
        funext x
        exact congrArg Subtype.val (congrFun h x)
      · intro h
        funext x
        exact Subtype.ext (congrFun h x)
    constructor
    · rintro ⟨⟨-, h2⟩, h3⟩
      refine ⟨⟨fun x => (f x).2, fun h x => ?_⟩, ?_⟩
      · rw [hΦ, hΦ, h2, hy]
      · have h4 : IsOpen {a : G | rightReg ℂ G X a f = f} := h3
        rw [hs] at h4
        exact h4
    · rintro ⟨⟨-, h2⟩, h3⟩
      refine ⟨⟨fun x => trivial, fun h x => Subtype.ext ?_⟩, ?_⟩
      · rw [hy]
        exact h2 h x
      · have h4 : IsOpen {a : G | rightReg ℂ G Y a (Φ f) = Φ f} := h3
        rw [← hs] at h4
        exact h4
  have hsurj : ∀ F ∈ IndF j y X, ∃ f, Φ f = F := fun F hF => ⟨fun x => ⟨F x, hF.1.1 x⟩, rfl⟩
  rcases H' (Q.comap Φ) (fun f hf => (hmem f).2 (hQ hf)) (fun g f hf => hst g (Φ f) hf) with h | h
  · left
    rw [eq_bot_iff]
    intro F hF
    obtain ⟨f, rfl⟩ := hsurj F (hQ hF)
    have : f ∈ Q.comap Φ := hF
    rw [h, Submodule.mem_bot] at this
    rw [this, map_zero]
    exact Submodule.zero_mem _
  · right
    refine le_antisymm hQ fun F hF => ?_
    obtain ⟨f, rfl⟩ := hsurj F hF
    have : f ∈ Q.comap Φ := by
      rw [h]
      exact (hmem f).2 hF
    exact this

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.indAmb :
    ∀ {r : ℕ} {G : Fin r → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] (P : ∀ i, Subgroup (G i)) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
      (y : Representation ℂ (∀ i, P i) Y) (X : Submodule ℂ Y), SimpleIn y X → (∀ v ∈ X, IsOpen {p : ∀ i, P i | y p v = v}) →
      (∀ i, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (P i) V) (f : V →ₗ[ℂ] Y), LocOk (P i) ρ ∧ f ≠ 0 ∧ (∀ v, f v ∈ X) ∧
        ∀ p v, f (ρ p v) = y (Pi.mulSingle i p) (f v)) →
      SimpleIn (rightReg ℂ (∀ i, G i) Y) (IndF (piIncl P) y X) := by
  intro r G _ _ _ P Y _ _ y X hX hop hloc
  by_cases h0 : X = ⊥
  · refine ⟨fun g f hf => indF_stable _ y X g f hf, fun Q hQ _ => Or.inl ?_⟩
    rw [eq_bot_iff]
    intro F hF
    rw [Submodule.mem_bot]
    funext x
    have := (hQ hF).1.1 x
    rw [h0, Submodule.mem_bot] at this
    exact this
  let y' : Representation ℂ ((∀ i, P i) × PUnit.{1}) X := (GlobalTheory.PRep.sub y X hX.1).comp (MonoidHom.fst _ _)
  have hy : ∀ a (v : X), (y' a v : Y) = y a.1 v := fun _ _ => rfl
  have hirr : y'.IsIrreducible := by
    have : Nontrivial X := Submodule.nontrivial_iff_ne_bot.2 h0
    refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
    · exact bot_ne_top (α := Submodule ℂ X) (congrArg Subrepresentation.toSubmodule h)
    · rcases hX.2 (S.toSubmodule.map X.subtype) (Submodule.map_subtype_le _ _) (by
        rintro g _ ⟨v, hv, rfl⟩
        exact ⟨y' (g, 1) v, S.apply_mem_toSubmodule _ hv, rfl⟩) with h | h
      · left
        apply Subrepresentation.toSubmodule_injective
        apply Submodule.map_injective_of_injective X.injective_subtype
        rw [h]
        exact (Submodule.map_bot _).symm
      · right
        apply Subrepresentation.toSubmodule_injective
        apply Submodule.map_injective_of_injective X.injective_subtype
        rw [h]
        exact (Submodule.map_subtype_top _).symm
  have key := indProdG r P y' hirr (fun v => by
      convert hop v v.2 using 2 with p
      exact funext fun p => propext Subtype.ext_iff) (fun i => by
      obtain ⟨V, _, _, ρ, f, h1, h2, h3, h4⟩ := hloc i
      refine ⟨V, inferInstance, inferInstance, ρ, f.codRestrict X h3, h1, fun h => h2 ?_, fun p v => Subtype.ext (h4 p v)⟩
      ext v
      exact congrArg Subtype.val (LinearMap.congr_fun h v))
  refine simple_of_sub (piIncl P) y X (y'.comp (MonoidHom.inl _ _)) (fun _ _ => rfl) fun Q hQ hst => key Q hQ hst fun c f hf => ?_
  have : (fun x => y' (1, c) (f x)) = f := by
    funext x
    apply Subtype.ext
    rw [hy]
    simp
  rw [this]
  exact hf
