import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.PowNeOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ProjAlg
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.CharacterIntegrability.ChiPin

noncomputable section

namespace UpperTheory.BaseChangeIdentities.GelfandReading

open PositivityTheory.Rg.BcB.F

theorem exists_transport {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {S T : StarSubalgebra ℂ A}
    (h : S = T) (χ : S →⋆ₐ[ℂ] ℂ) : ∃ χ' : T →⋆ₐ[ℂ] ℂ, (∀ y : T, ∃ z : S, z.1 = y.1 ∧ χ' y = χ z) ∧
      ∀ x (hx : x ∈ T) (hx' : x ∈ S), χ' ⟨x, hx⟩ = χ ⟨x, hx'⟩ := by
  subst h
  exact ⟨χ, fun y => ⟨y, rfl, rfl⟩, fun _ _ _ => rfl⟩

theorem gRead_of {ι : Type} [Fintype ι] [Nonempty ι] {H : ι → Type} [∀ s, NormedAddCommGroup (H s)]
    [∀ s, InnerProductSpace ℂ (H s)] [∀ s, CompleteSpace (H s)] {d : ℕ} {Γ : Type} (gen : Γ → Prod' H d)
    (β : ∀ s, H s →L[ℂ] H s) (m : ℕ) (v : EuclideanSpace ℂ (Fin d)) (hv : v ≠ 0) (a₀ : Γ) (c : Γ → ℂ)
    (hc : ∀ x, (gen x).2 v = c x • v) (h₀ : c a₀ = 1) (Q : Prop)
    (hQ : ∀ (s : ι) (χ : StarAlgebra.adjoin ℂ (Set.range (fun x => (gen x).1 s) ∪ {star (β s ^ m) * β s ^ m}) →⋆ₐ[ℂ] ℂ),
      ((∀ y, ‖χ y‖ ≤ ‖(y : H s →L[ℂ] H s)‖) ∧
        (∀ x, χ ⟨(gen x).1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨x, rfl⟩)⟩ = c x) ∧
        χ ⟨star (β s ^ m) * β s ^ m, StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)⟩ ≠ 0) → Q) : GRead gen β m v Q := by
  intro s χ hn heig hX
  obtain ⟨χ', h1, h2⟩ := exists_transport (Rd.projAdjoin gen s (star (β s ^ m) * β s ^ m)) χ
  have ha : (gen a₀).2 v = v := by rw [hc, h₀, one_smul]
  refine hQ s χ' ⟨fun y => ?_, fun x => ?_, fun h => hX ((h2 _ _ _).symm.trans h)⟩
  · obtain ⟨z, e1, e2⟩ := h1 y
    rw [e2, ← e1]
    exact hn z
  · exact (h2 _ _ _).trans
      (R3.chi_pin gen a₀ v hv ha s _ χ heig ⟨gen x, StarAlgebra.subset_adjoin ℂ _ ⟨x, rfl⟩⟩ (c x) (hc x))

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem chiTr : BC.ChiTr := fun _ _ _ _ _ _ _ _ _ _ G Q h1 hQ =>
  gRead_of (H := G.H) G.gen G.βop G.m G.v G.v_ne G.a₀ (fun x => G.c x G.i₀) (fun x => (G.vblk x).1) h1 Q hQ

end UpperTheory.BaseChangeIdentities.GelfandReading

end
