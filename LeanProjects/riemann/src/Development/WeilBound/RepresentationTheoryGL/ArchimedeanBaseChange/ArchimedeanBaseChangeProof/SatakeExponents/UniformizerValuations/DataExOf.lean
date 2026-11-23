import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupExOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.GlobalTheory
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

structure GenIn (π : Submodule ℂ (UA E n → ℂ)) (S T : Finset (HeightOneSpectrum (𝓞 E)))
    (K : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin n) (w.adicCompletion E)))
    (W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)) where
  ι : Type
  [ft : Fintype ι]
  [ne : Nonempty ι]
  B : ι → Block E
  I : Type
  [fI : Fintype I]
  d : ℕ
  blk : Fin d → I
  Γ : Type
  g : Γ → ∀ s, BGen (B s)
  c : Γ → I → ℂ
  β : ∀ s, PT (B s)
  m : ℕ
  u : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)
  v : EuclideanSpace ℂ (Fin d)
  i₀ : I
  a₀ : Γ
  ok : ∀ x s, (g x s).Ok
  βok : ∀ s, (β s).Ok
  comm : ∀ x y s, Commute (g x s).op (g y s).op
  commStar : ∀ x y s, Commute (g x s).op (star (g y s).op)
  βcomm : ∀ s x, Commute (β s).op (g x s).op ∧ Commute (β s).op (star (g x s).op)
  ucomm : ∀ x, Commute u (Eig.diagOp blk (c x)) ∧ Commute u (star (Eig.diagOp blk (c x)))
  v_ne : v ≠ 0
  uv : u v = v
  vblk : ∀ x, Eig.diagOp blk (c x) v = c x i₀ • v ∧ star (Eig.diagOp blk (c x)) v = starRingEnd ℂ (c x i₀) • v
  a₀ne : c a₀ i₀ ≠ 0

section Generic

variable {ι : Type} [Fintype ι] [Nonempty ι] {H : ι → Type} [∀ s, NormedAddCommGroup (H s)]
  [∀ s, InnerProductSpace ℂ (H s)] [∀ s, CompleteSpace (H s)] {d : ℕ} {Γ : Type}

def GBound (gen : Γ → Prod' H d) (a₀ : Γ) (β : ∀ s, H s →L[ℂ] H s) (m : ℕ)
    (u : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) : Prop :=
  ∀ a ∈ StarAlgebra.adjoin ℂ (Set.range gen), (∃ b ∈ StarAlgebra.adjoin ℂ (Set.range gen), a = b * gen a₀) →
    ∃ (C : ℝ) (N j : ℕ), ∀ᶠ k : ℕ in Filter.atTop,
      ‖LinearMap.trace ℂ _ (((u * a.2) ^ k : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) :
        EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d))‖ ≤
        C * (1 + k) ^ N * Finset.univ.sup' Finset.univ_nonempty (fun s => ‖(β s ^ m * a.1 s) ^ (k - j)‖)

def GRead (gen : Γ → Prod' H d) (β : ∀ s, H s →L[ℂ] H s) (m : ℕ) (v : EuclideanSpace ℂ (Fin d)) (Q : Prop) : Prop :=
  ∀ (s : ι) (χ : StarAlgebra.adjoin ℂ
      (Set.range (fun a : StarAlgebra.adjoin ℂ (Set.range gen) => (a : Prod' H d).1 s) ∪ {star (β s ^ m) * β s ^ m})
        →⋆ₐ[ℂ] ℂ),
    (∀ x, ‖χ x‖ ≤ ‖(x : H s →L[ℂ] H s)‖) →
    (∀ a : StarAlgebra.adjoin ℂ (Set.range gen), a.1.2 v ≠ 0 → ∃ c : ℂ, a.1.2 v = c • v ∧
      χ ⟨a.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a, rfl⟩)⟩ = c) →
    χ ⟨star (β s ^ m) * β s ^ m, StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)⟩ ≠ 0 → Q

end Generic

namespace GenIn

variable {π : Submodule ℂ (UA E n → ℂ)} {S T : Finset (HeightOneSpectrum (𝓞 E))}
  {K : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin n) (w.adicCompletion E))} {W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)}
  (G : GenIn π S T K W)

attribute [instance] GenIn.ft GenIn.ne GenIn.fI

abbrev H (s : G.ι) : Type := (G.B s).Hb

instance instNH (s : G.ι) : NormedAddCommGroup (G.H s) := inferInstanceAs (NormedAddCommGroup (G.B s).Hb)
instance instIH (s : G.ι) : InnerProductSpace ℂ (G.H s) := inferInstanceAs (InnerProductSpace ℂ (G.B s).Hb)
instance instCH (s : G.ι) : CompleteSpace (G.H s) := inferInstanceAs (CompleteSpace (G.B s).Hb)

def gen (x : G.Γ) : Prod' G.H G.d := (fun s => (G.g x s).op, Eig.diagOp G.blk (G.c x))

def βop (s : G.ι) : G.H s →L[ℂ] G.H s := (G.β s).op

def Bound : Prop := GBound (H := G.H) G.gen G.a₀ G.βop G.m G.u

def Read : Prop := GRead (H := G.H) G.gen G.βop G.m G.v (∃ D : Pre E n, TOut π S T K W D)

def DiagComm : Prop := ∀ (I : Type) (d : ℕ) (blk : Fin d → I) (c c' : I → ℂ),
  Commute (Eig.diagOp blk c) (Eig.diagOp blk c') ∧ Commute (Eig.diagOp blk c) (star (Eig.diagOp blk c'))

end GenIn

def GenToData : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ))
  (S T : Finset (HeightOneSpectrum (𝓞 E))) (K : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin n) (w.adicCompletion E)))
  (W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)) (G : GenIn π S T K W), GenIn.DiagComm → G.Bound → G.Read →
  Nonempty (RunData π S T K W)

def GenEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Finset (HeightOneSpectrum (𝓞 E)), S.card ≤ 1 →
    ∃ (K : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin n) (w.adicCompletion E)))
      (W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)), IsLevel K ∧ (∀ N, FiniteDimensional ℂ (W N)) ∧
      ∀ T : Finset (HeightOneSpectrum (𝓞 E)), ∃ G : GenIn π S T K W, G.Bound ∧ G.Read

theorem dataEx_of (h0 : GenIn.DiagComm) (h1 : GenToData) (h2 : GenEx) : DataEx := by
  intro E _ _ _ hE n hn π hπ S hS
  obtain ⟨K, W, hK, hW, hT⟩ := h2 E hE n hn π hπ S hS
  exact ⟨K, W, hK, hW, fun T => let ⟨G, hb, hr⟩ := hT T; h1 E n π S T K W G h0 hb hr⟩

end PositivityTheory.Rg.BcB.F

end
