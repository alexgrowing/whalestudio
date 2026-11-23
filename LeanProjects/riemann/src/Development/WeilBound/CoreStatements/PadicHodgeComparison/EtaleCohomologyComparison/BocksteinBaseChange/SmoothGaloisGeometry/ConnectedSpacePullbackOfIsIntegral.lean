import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.IsOpenConnectedComponentOfNoetherianSpace
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.RelDim
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace CrystallineSemistableComparison

theorem connectedSpace_pullback_of_isIntegral {O : Type} [CommRing O] [IsDomain O] {X T : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of O)) (j : T ⟶ Spec (CommRingCat.of O)) [IsOpenImmersion j] [Nonempty T]
    [IsIntegral X] (hp : GeneralizingMap p) : ConnectedSpace ↥(pullback p j) := by
  have hne : Nonempty ↥(pullback p j) := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have hη : genericPoint (Spec (CommRingCat.of O)) ⤳ p x := genericPoint_specializes _
    obtain ⟨x', -, hx'⟩ := hp hη
    have hmem : genericPoint (Spec (CommRingCat.of O)) ∈ Set.range j := by
      obtain ⟨t⟩ := (inferInstance : Nonempty T)
      exact ((genericPoint_spec (Spec (CommRingCat.of O))).mem_open_set_iff j.isOpenEmbedding.isOpen_range).mpr
        ⟨j t, trivial, t, rfl⟩
    obtain ⟨t, ht⟩ := hmem
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback x' t (hx'.trans ht.symm)
    exact ⟨z⟩
  have hirr : IsPreirreducible (Set.univ : Set ↥(pullback p j)) := by
    have h := (IrreducibleSpace.isIrreducible_univ X).2.preimage (pullback.fst p j).isOpenEmbedding
    simpa using h
  have : PreirreducibleSpace ↥(pullback p j) := ⟨hirr⟩
  have : IrreducibleSpace ↥(pullback p j) := ⟨hne⟩
  infer_instance

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

abbrev Model.sub (M : Model l K) (U : M.X.Opens) : Model l K := ⟨U.toScheme, U.ι ≫ M.p⟩

theorem compM_of (G : Model l K → Prop)
    (hj : IsOpenImmersion (Spec.map (CommRingCat.ofHom (OK l K).subtype)))
    (hsub : ∀ M, G M → ∀ U : M.X.Opens, IsClosed (U : Set M.X) → G (M.sub U))
    (hN : ∀ M, G M → NoetherianSpace M.X)
    (hF : ∀ M, G M → GlobalTheory.IsNormalScheme M.X ∧ IsLocallyNoetherian M.X ∧ GeneralizingMap M.p ∧ Smooth M.q) :
    CompM G := by
  intro M hM
  have := hN M hM
  obtain ⟨r, U, hU, hc⟩ := exists_isSum_components M.X
  have hcl : ∀ a, IsClosed (U a : Set M.X) := by
    intro a
    have hrange := hU.2.1

    have : (U a : Set M.X)ᶜ = ⋃ b ∈ {b | b ≠ a}, (U b : Set M.X) := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
      constructor
      · intro hx
        obtain ⟨b, hb⟩ := hU.2.1 x
        rw [Scheme.Opens.range_ι] at hb
        exact ⟨b, fun h ↦ hx (h ▸ hb), hb⟩
      · rintro ⟨b, hba, hb⟩ hx
        have := hU.2.2 b a hba
        rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι] at this
        exact Set.disjoint_left.mp this hb hx
    rw [← isOpen_compl_iff, this]
    exact isOpen_biUnion fun b _ ↦ (U b).isOpen
  have hG : ∀ a, G (M.sub (U a)) := fun a ↦ hsub M hM (U a) (hcl a)
  have hconn : ∀ a, ∃ d, (M.sub (U a)).Conn d := by
    intro a
    obtain ⟨hnorm, hnoeth, hgen, hsm⟩ := hF _ (hG a)
    have : ConnectedSpace (M.sub (U a)).X := hc a
    have : IsIntegral (M.sub (U a)).X := GlobalTheory.IsNormalScheme.isIntegral_of_connectedSpace _
    have : ConnectedSpace (M.sub (U a)).gen :=
      connectedSpace_pullback_of_isIntegral (M.sub (U a)).p _ hgen
    obtain ⟨d, hd⟩ := exists_smoothOfRelativeDimension (M.sub (U a)).q
    exact ⟨d, inferInstance, hd⟩
  choose d hd using hconn
  exact ⟨r, fun a ↦ M.sub (U a), d, fun a ↦ (U a).ι, fun a ↦ rfl, hU, fun a ↦ ⟨hG a, hd a⟩⟩

end CrystallineSemistableComparison
