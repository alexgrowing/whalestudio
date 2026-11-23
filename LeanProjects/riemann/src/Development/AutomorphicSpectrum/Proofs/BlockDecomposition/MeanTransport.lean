import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHermPart
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

variable {D : D7} {n ρ p : ℕ}

theorem adj_bl (hn : ρ + p = n) (a : Mx D ρ ρ) (b : Mx D ρ p) (c : Mx D p ρ) (d : Mx D p p) :
    adj (bl hn a b c d : Mx D n n) = bl hn (adj a) (adj c) (adj b) (adj d) := by
  ext i j
  simp only [adj, bl, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases h1 : (finSumFinEquiv.trans (finCongr hn)).symm i with i' | i' <;>
    rcases h2 : (finSumFinEquiv.trans (finCongr hn)).symm j with j' | j' <;> rfl

def bT (hn : ρ + p = n) (z : hermA D ρ) (x : Mx D ρ p) (y : hermA D p) : hermA D n :=
  ⟨bl hn z.1 x (adj x) y.1, by
    show adj (bl hn z.1 x (adj x) y.1 : Mx D n n) = _
    rw [adj_bl, adj_adj]
    have hz : adj z.1 = z.1 := z.2
    have hy : adj y.1 = y.1 := y.2
    rw [hz, hy]⟩

def dsum (hn : ρ + p = n) (b₀ : HermE D ρ) (β' : HermE D p) : HermE D n :=
  ⟨bl hn b₀.1 0 0 β'.1, by
    have h1 := b₀.2
    have h2 := β'.2
    refine Matrix.ext fun i j => ?_
    simp only [bl, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
    rcases h1' : (finSumFinEquiv.trans (finCongr hn)).symm i with i' | i' <;>
      rcases h2' : (finSumFinEquiv.trans (finCongr hn)).symm j with j' | j' <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply, map_zero]
    · exact congrFun (congrFun h1 i') j'
    · exact congrFun (congrFun h2 i') j'⟩

def cg (a : GL (Fin n) D.host.E) (β : HermE D n) : HermE D n :=
  ⟨(a.1.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose * β.1 * a.1, by
    have h : ∀ M : Matrix (Fin n) (Fin n) D.host.E, (M.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = Mᴴ := fun _ => rfl
    have hb : β.1ᴴ = β.1 := β.2
    rw [h, h, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hb, Matrix.mul_assoc]⟩

def IsPer (Φ : hermA D n → ℂ) : Prop := ∀ γ ∈ ratHerm D n, ∀ x, Φ (γ + x) = Φ x

def chn (ψ : AddChar (AF D.host.F) ℂ) (β : HermE D n) (b : hermA D n) : ℂ :=
  ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))

def pm (hn : ρ + p = n) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (Φ : hermA D n → ℂ) (y : hermA D p) : ℂ :=
  ∫ x in m.𝓕, ∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz ∂m.μ

end GlobalTheory.CompanionTheory.PcFc

namespace GlobalTheory.CompanionTheory.PcFc

section Transport
variable {A B : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [T2Space A] [LocallyCompactSpace A]
  [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
  [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] [T2Space B] [LocallyCompactSpace B]
  [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]

theorem mean_transport (Γ : AddSubgroup A) (Δ : AddSubgroup B) [Countable Γ] [Countable Δ] (T : A ≃ₜ+ B)
    (hT : ∀ a, T a ∈ Δ ↔ a ∈ Γ) (μ : Measure A) (ν : Measure B) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {s : Set A} {t : Set B} (hs : IsAddFundamentalDomain Γ s μ) (ht : IsAddFundamentalDomain Δ t ν) (hs1 : μ s = 1) (ht1 : ν t = 1)
    (f : B → ℂ) (hf : ∀ γ ∈ Δ, ∀ x, f (γ + x) = f x) :
    ∫ a in s, f (T a) ∂μ = ∫ b in t, f b ∂ν := by
  have hm : Measurable T := T.continuous.measurable
  have hAC : (μ.map T).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ T
  have hAC2 : (ν.map T.symm).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν T.symm
  have hsm : Measure.QuasiMeasurePreserving (T.symm.toAddEquiv.toEquiv) ν μ :=
    ⟨T.symm.continuous.measurable, Measure.absolutelyContinuous_isAddHaarMeasure _ _⟩
  let eΓ : Δ ≃ Γ :=
    { toFun := fun d => ⟨T.symm d.1, (hT _).1 (by simpa using d.2)⟩
      invFun := fun c => ⟨T c.1, (hT _).2 c.2⟩
      left_inv := fun d => Subtype.ext (by simp)
      right_inv := fun c => Subtype.ext (by simp) }
  have hFD : IsAddFundamentalDomain Δ (T.toAddEquiv.toEquiv '' s) ν :=
    hs.image_of_equiv T.toAddEquiv.toEquiv hsm eΓ (fun g x => by
      show T (T.symm g.1 + x) = g.1 + T x
      simp)
  have h1 : ν (T.toAddEquiv.toEquiv '' s) = 1 := by rw [hFD.measure_eq ht, ht1]
  have hemb : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  have h2 : μ.map T (T.toAddEquiv.toEquiv '' s) = 1 := by
    rw [hemb.map_apply, show T ⁻¹' (T.toAddEquiv.toEquiv '' s) = s from Set.preimage_image_eq _ T.injective, hs1]
  have h3 : μ.map T = ν := by
    have h4 := Measure.isAddLeftInvariant_eq_smul (μ.map T) ν
    rw [h4] at h2
    have hc : Measure.addHaarScalarFactor (μ.map T) ν = 1 := by
      rw [Measure.smul_apply, h1, ENNReal.smul_def, smul_eq_mul, mul_one] at h2
      exact_mod_cast h2
    rw [h4, hc, one_smul]
  have h5 : ∫ a in s, f (T a) ∂μ = ∫ b in T.toAddEquiv.toEquiv '' s, f b ∂ν := by
    rw [← h3, hemb.setIntegral_map, show T ⁻¹' (T.toAddEquiv.toEquiv '' s) = s from Set.preimage_image_eq _ T.injective]
  rw [h5]
  exact hFD.setIntegral_eq ht (fun g x => hf g.1 g.2 x)
end Transport
end GlobalTheory.CompanionTheory.PcFc
