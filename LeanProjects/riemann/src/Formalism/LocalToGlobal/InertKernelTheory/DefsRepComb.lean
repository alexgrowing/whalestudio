import Formalism.LocalToGlobal.InertKernelTheory.DefsRep
import Formalism.LocalToGlobal.InertKernelTheory.DefsInt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.KerTh
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading

noncomputable section

namespace Formalism.L2.KerInert.RepComb

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

abbrev hK (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a b : ℕ) : Sesq (TaylorLogMetric.VC D a b) :=
  HV (ι := D.what₂.Tau) (a := a) (b := b) (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹

abbrev alK (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a b : ℕ) : TaylorLogMetric.VC D a b → ℂ :=
  alV (ι := D.what₂.Tau) (a := a) (b := b) D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹

variable (cc δ) in

abbrev lamK {a b : ℕ} (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) : AddSubgroup (TaylorLogMetric.VC D a b) :=
  LamC (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) N N'

variable (cc δ) in

abbrev halfA {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) : AddSubgroup (TaylorLogMetric.VC D a b) :=
  AC (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) SS N N' cl

variable (cc δ) in

abbrev halfB {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) : AddSubgroup (TaylorLogMetric.VC D a b) :=
  BC (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) SS N N' cl

variable (cc δ) in

abbrev ptsX {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) : Finset (TaylorLogMetric.VC D a b) :=
  repsOf (lamK cc δ N N') (halfA cc δ SS cl N N')

variable (cc δ) in

abbrev ptsA {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) : Finset (TaylorLogMetric.VC D a b) :=
  repsOf (halfB cc δ SS cl N N') (lamK cc δ N N' ⊓ halfA cc δ SS cl N N')

variable (cc δ) in

abbrev ptsB {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) : Finset (TaylorLogMetric.VC D a b) :=
  repsOf (lamK cc δ N N') (halfB cc δ SS cl N N')

variable (cc δ) in

def kerCoef {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ)
    (x y : TaylorLogMetric.VC D a b) : ℂ :=
  alK D cc δ a b x *
    (hatS (hK D cc δ a b) 1 (ptsA cc δ SS cl N N')
      (fun s => onV (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ Ξ (s - x)) y * alK D cc δ a b y) *
    Complex.exp ((Real.pi : ℂ) * (hK D cc δ a b y x - hK D cc δ a b x y) / 2)

variable (cc δ) in

def CoefInt {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ)
    {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) : Prop :=
  ∀ x ∈ ptsX cc δ SS cl N N', ∀ y ∈ ptsB cc δ SS cl N N',
    kerCoef cc δ SS cl N N' Ξ x y ∈ TaylorLogMetric.Qbar ∧ TaylorLogMetric.IsIntP (TaylorLogMetric.lamC lam (kerCoef cc δ SS cl N N' Ξ x y))

variable (cc δ) in

def PtTors {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) (p : ℕ) : Prop :=
  ∀ x ∈ ptsX cc δ SS cl N N', ∀ y ∈ ptsB cc δ SS cl N N',
    TaylorLogMetric.TorsPrime D p (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) N N') (x + y)

def AlgTr (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) {a b : ℕ}
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) (p : ℕ) : Prop :=
  ∀ t : TaylorLogMetric.VC D a b, TaylorLogMetric.TorsPrime D p (TaylorLogMetric.La D B.tor N N') t → AlgEnt D (TaylorLogMetric.U D B.tor t (B.eNat χ a b N N'))

def CombKer : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (a b : ℕ)
    (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a)) (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b))
    (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]),
    TaylorLogMetric.admitted D a b N N' → CoefInt cc δ SS cl N N' Ξ lam → PtTors cc δ SS cl N N' p → AlgTr B χ N N' p →
      TaylorLogMetric.IsComb D B.tor (B.eNat χ) lam N N' (Formalism.L2.PairingIndexBounds.F.serP lam (Formalism.L2.PairingIndexBounds.F.kerTh B χ SS cl N N' Ξ))

variable (cc δ) in

def FinIdx {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) : Prop :=
  relIdx (lamK cc δ N N') (halfA cc δ SS cl N N') ≠ 0 ∧
    relIdx (halfB cc δ SS cl N N') (lamK cc δ N N' ⊓ halfA cc δ SS cl N N') ≠ 0 ∧
    relIdx (lamK cc δ N N') (halfB cc δ SS cl N N') ≠ 0

variable (cc δ) in

def LamIn {a b : ℕ} (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) : Prop :=
  lamK cc δ N N' ≤ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) N N'

def CombKerS : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (a b : ℕ)
    (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a)) (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b))
    (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ) (S : Finset ℕ) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]),
    TaylorLogMetric.admitted D a b N N' → LatInt (hK D cc δ a b) (Real.sqrt D.host.d / 2) (lamK cc δ N N') → FinIdx cc δ SS cl N N' →
    SNum S cl → (∀ x, IntOff S (Ξ x)) → p ∉ S → LamIn cc δ N N' → AlgTr B χ N N' p →
      TaylorLogMetric.IsComb D B.tor (B.eNat χ) lam N N' (Formalism.L2.PairingIndexBounds.F.serP lam (Formalism.L2.PairingIndexBounds.F.kerTh B χ SS cl N N' Ξ))

def CombKerT : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (a b : ℕ)
    (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a)) (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b))
    (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ) (S : Finset ℕ) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]),
    TaylorLogMetric.admitted D a b N N' → N'.FG → Submodule.span D.host.E (N : Set (Formalism.L2.Col.Sp D.host.E a)) = ⊤ →
    (Formalism.L2.PairingIndexBounds.F.aaOf D cc).FG →
    LaFacts (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) N N' →
    0 < cl → SNum S cl → (∀ x, IntOff S (Ξ x)) → p ∉ S → LamIn cc δ N N' → TransAlg D B.tor (B.eNat χ) →
      TaylorLogMetric.IsComb D B.tor (B.eNat χ) lam N N' (Formalism.L2.PairingIndexBounds.F.serP lam (Formalism.L2.PairingIndexBounds.F.kerTh B χ SS cl N N' Ξ))

end Formalism.L2.KerInert.RepComb
