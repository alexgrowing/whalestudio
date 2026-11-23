import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ReadHalf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FRGood
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdjKer0

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.BcB.F.BC

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def Chi {E : Type} [Field E] [NumberField E] [IsCMField E] {B : Block E} {Γ : Type} (g : Γ → BGen B) (X : B.Hb →L[ℂ] B.Hb)
    (c : Γ → ℂ) (χ : Rd.ChAlg g X →⋆ₐ[ℂ] ℂ) : Prop :=
  (∀ y, ‖χ y‖ ≤ ‖(y : B.Hb →L[ℂ] B.Hb)‖) ∧ (∀ x, χ ⟨(g x).op, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨x, rfl⟩)⟩ = c x) ∧
    χ ⟨X, StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)⟩ ≠ 0

set_option maxHeartbeats 1000000 in

def ChiTr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ))
  (S T : Finset (Pl E)) (K : ∀ w : Pl E, Subgroup (GLw n w)) (W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)) (G : GenIn π S T K W)
  (Q : Prop), G.c G.a₀ G.i₀ = 1 →
  (∀ (s : G.ι) (χ : Rd.ChAlg (fun x => G.g x s) (star ((G.β s).op ^ G.m) * (G.β s).op ^ G.m) →⋆ₐ[ℂ] ℂ),
    Chi (fun x => G.g x s) _ (fun x => G.c x G.i₀) χ → Q) →
  GRead (H := G.H) G.gen G.βop G.m G.v Q

def PowNe : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E) (t : PT B) (m : ℕ) (A : Type) [Finite A]
  (G : A × B.κ → H E B.a B.b → ℂ), IsFinM t.ψ → (∀ j, HasLev (G j)) → convF B.ν (t.sq m).ψ G ≠ 0 →
    (convF B.ν t.ψ)^[m + 1] G ≠ 0

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)}
  {S T : Finset (Pl E)} {F₀ : Frame0 hR π S} (F : RunFrame F₀ T) (i : F₀.C.ι)

abbrev X : (F.B i).Hb →L[ℂ] (F.B i).Hb := star ((F.β i).op ^ F.m) * (F.β i).op ^ F.m

abbrev BO (χ : Rd.ChAlg (fun x => F.g x i) (X F i) →⋆ₐ[ℂ] ℂ) : Type :=
  Rd.BlockOut (F.B i) (fun x => F.g x i) (.inl ()) (F.t₀ i) (X F i) ((F.β i).sq (F.m - 1)) (2 * F.m) χ
    (lev₁ F₀.Sec F.d (F₀.C.a i)) (lev₂ F₀.Sec F.d (F₀.C.a i)) (rlW₁ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb)
    (rlW₂ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb)
    (rlΘ₁ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb (lev₁ F₀.Sec F.d (F₀.C.a i)) (lev₂ F₀.Sec F.d (F₀.C.a i)))
    (rlΘ₂ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb (lev₁ F₀.Sec F.d (F₀.C.a i)) (lev₂ F₀.Sec F.d (F₀.C.a i)))
    (rlΩ₁ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb) (rlΩ₂ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb)

end

set_option maxHeartbeats 2000000 in

def LimAt : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n →
  ∀ (π : Submodule ℂ (UA E n → ℂ)) (S T : Finset (Pl E)) (F₀ : Frame0 hR π S) (F : RunFrame F₀ T), F.Struct →
  ∀ (i : F₀.C.ι) (χ : Rd.ChAlg (fun x => F.g x i) (X F i) →⋆ₐ[ℂ] ℂ),
    Chi (fun x => F.g x i) (X F i) (fun x => (F.ug x).p F.fam F.i₀) χ → Nonempty (BO F i χ)

set_option maxHeartbeats 2000000 in

def Ident : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
  (π : Submodule ℂ (UA E n → ℂ)) (S T : Finset (Pl E)) (F₀ : Frame0 hR π S) (F : RunFrame F₀ T)
  (i : F₀.C.ι) (χ : Rd.ChAlg (fun x => F.g x i) (X F i) →⋆ₐ[ℂ] ℂ),
    Chi (fun x => F.g x i) (X F i) (fun x => (F.ug x).p F.fam F.i₀) χ → ∀ O : BO F i χ,
    (∀ τ, mOf O.χa τ = mOf (F₀.A i).χa τ) ∧ ∀ τ, mOf O.χb τ = mOf (F₀.A i).χb τ

def LimAtOf : Prop := SqOk → LevIdem → gamma_zeta_nabla_cancel.GelfInj → gamma_zeta_nabla_cancel.RegDom → LimAt

def IdentOf : Prop := gamma_zeta_nabla_cancel.GelfInj → Ident

def PowNeOf : Prop := Tail.ConvMul → PowNe

end PositivityTheory.Rg.BcB.F.BC

end
