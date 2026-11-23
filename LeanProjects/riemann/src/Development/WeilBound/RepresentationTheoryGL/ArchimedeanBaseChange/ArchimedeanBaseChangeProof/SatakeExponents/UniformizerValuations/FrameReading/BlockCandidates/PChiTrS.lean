import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.PowNeOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ProjAlg
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PChiPin

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.BcB.F.BC

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem restr {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (S T : StarSubalgebra ℂ A) (hle : S ≤ T)
    (χ : T →⋆ₐ[ℂ] ℂ) : ∃ χ' : S →⋆ₐ[ℂ] ℂ, ∀ (y : A) (hy : y ∈ S) (hy' : y ∈ T), χ' ⟨y, hy⟩ = χ ⟨y, hy'⟩ :=
  ⟨χ.comp (StarSubalgebra.inclusion hle), fun _ _ _ => rfl⟩

section Gen

variable {ι : Type} [Fintype ι] [Nonempty ι] {H : ι → Type} [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
  [∀ s, CompleteSpace (H s)] {d : ℕ} {Γ : Type}

theorem gen_tr (gen : Γ → Prod' H d) (β : ∀ s, H s →L[ℂ] H s) (m : ℕ) (v : EuclideanSpace ℂ (Fin d)) (hv : v ≠ 0) (a₀ : Γ)
    (c : Γ → ℂ) (hc : ∀ x, (gen x).2 v = c x • v) (h₀ : c a₀ = 1) (Q : Prop)
    (h : ∀ (s : ι) (χ : StarAlgebra.adjoin ℂ (Set.range (fun x => (gen x).1 s) ∪ {star (β s ^ m) * β s ^ m}) →⋆ₐ[ℂ] ℂ),
      (∀ y, ‖χ y‖ ≤ ‖(y : H s →L[ℂ] H s)‖) →
      (∀ x, χ ⟨(gen x).1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨x, rfl⟩)⟩ = c x) →
      χ ⟨star (β s ^ m) * β s ^ m, StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)⟩ ≠ 0 → Q) : GRead gen β m v Q := by
  intro s χ h1 h2 h3
  have hle : StarAlgebra.adjoin ℂ (Set.range (fun x => (gen x).1 s) ∪ {star (β s ^ m) * β s ^ m}) ≤
      StarAlgebra.adjoin ℂ (Set.range (fun a : StarAlgebra.adjoin ℂ (Set.range gen) => (a : Prod' H d).1 s) ∪
        {star (β s ^ m) * β s ^ m}) := by
    refine StarAlgebra.adjoin_le ?_
    rintro y (⟨x, rfl⟩ | hy)
    · exact StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨⟨gen x, StarAlgebra.subset_adjoin ℂ _ ⟨x, rfl⟩⟩, rfl⟩)
    · exact StarAlgebra.subset_adjoin ℂ _ (Or.inr hy)
  obtain ⟨χ', e⟩ := restr _ _ hle χ
  refine h s χ' (fun y => ?_) (fun x => ?_) ?_
  · exact (congrArg norm (e y.1 y.2 (hle y.2))).trans_le (h1 ⟨y.1, hle y.2⟩)
  · have p := ChiPin.chi_pin gen a₀ v hv (by rw [hc, h₀, one_smul]) s _ χ h2
      ⟨gen x, StarAlgebra.subset_adjoin ℂ _ ⟨x, rfl⟩⟩ (c x) (hc x)
    exact (e _ _ _).trans p
  · exact (e _ _ _).trans_ne h3

end Gen

set_option maxHeartbeats 2000000 in
theorem chiTr' : ChiTr := fun _ _ _ _ _ _ _ _ _ _ G Q h₀ h =>
  gen_tr (H := G.H) G.gen G.βop G.m G.v G.v_ne G.a₀ (fun x => G.c x G.i₀) (fun x => (G.vblk x).1) h₀ Q
    fun s χ h1 h2 h3 => h s χ ⟨h1, h2, h3⟩

end PositivityTheory.Rg.BcB.F.BC

end
