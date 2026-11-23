import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Clause3Asc
import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.LeviMaps
import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.IsLocCompTwistFills

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.RSHS.LS

def RestrictAtPoint : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N c : ℕ) (n : Fin c → ℕ)
  (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (w : HeightOneSpectrum (𝓞 E)) (X : Type) [AddCommGroup X]
  [Module ℂ X] (ρ : Representation ℂ (GL (Fin N) (w.adicCompletion E)) X)
  (F : PositivityTheory.RSHS.LeviInductionForms.LocMaps (indForms h π) w ρ), F.1 ≠ 0 →
    ∃ L : X →ₗ[ℂ] ((∀ i, GA E (n i)) → ℂ), (∀ v, L v ∈ tensorForms π) ∧ L ≠ 0 ∧
      ∀ (p : parab (w.adicCompletion E) (stdBlocks n h)) (v : X),
        L (ρ p v) = fun m => L v fun i => m i * finGL E (n i)
          (locGL E (n i) w (leviProj (w.adicCompletion E) (stdBlocks n h) p i))

def ExistsProj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (c : ℕ) (n : Fin c → ℕ)
  (π : ∀ i, CuspSub E (n i)) (w : HeightOneSpectrum (𝓞 E)) (τ : ∀ i, SmIrr (GL (Fin (n i)) (w.adicCompletion E))),
  (∀ i, (π i).IsLocComp w (τ i)) → ∀ t ∈ tensorForms π, t ≠ 0 →
    ∃ p : ((∀ i, GA E (n i)) → ℂ) →ₗ[ℂ] PiTensorProduct ℂ fun i => (τ i).V, p t ≠ 0 ∧
      ∀ (g : ∀ i, GL (Fin (n i)) (w.adicCompletion E)), ∀ s ∈ tensorForms π,
        p (fun m => s fun i => m i * finGL E (n i) (locGL E (n i) w (g i))) = piTensor (fun i => (τ i).ρ) g (p s)

def FrobRecip : Prop := ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (N c : ℕ) (n : Fin c → ℕ) (h : ∑ i, n i = N) (σ' : SmIrr (GL (Fin N) k)) (W : Type) [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ (∀ i, GL (Fin (n i)) k) W) (ℓ : σ'.V →ₗ[ℂ] W), ℓ ≠ 0 →
    (∀ (p : parab k (stdBlocks n h)) (v : σ'.V), ℓ (σ'.ρ p v) = ρ (leviProj k (stdBlocks n h) p) (ℓ v)) →
      ∃ f : σ'.ρ.IntertwiningMap (parInd (stdBlocks n h) (twist ρ (deltaHalf k fun i => Fin (n i))⁻¹)),
        f.toLinearMap ≠ 0

def AscIndEquiv : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N a d : ℕ)
  (h : ∑ _ : Fin d, a = N) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
  (ν : Fin d → HChar E), (∀ i, (ν i).IsAbsPow (-spehExp d i + a * spehExp d i)) →
  ∀ hd : ∑ i : Fin d, (GlobalTheory.LocGL.spehFactor (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d i.rev).1 = N,
    Nonempty ((parInd (stdBlocks (fun _ : Fin d => a) h)
      (twist (piTensor fun i => (σ.twist (CuspSub.locDet a (ν i) w) (CuspSub.isOpen_ker_locDet (ν i) w)).ρ)
        (deltaHalf (w.adicCompletion E) fun _ : Fin d => Fin a)⁻¹)).Equiv
      (GlobalTheory.LocGL.prodIrr (fun i : Fin d => GlobalTheory.LocGL.spehFactor (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d i.rev) hd))

end PositivityTheory.RSHS.LS

end
