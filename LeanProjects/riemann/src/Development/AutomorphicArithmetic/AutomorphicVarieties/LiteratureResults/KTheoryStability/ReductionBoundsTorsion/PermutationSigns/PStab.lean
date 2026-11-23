import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.PadMHerm
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.MatDefs

noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.BlockInvariants

def FFT : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N q : ℕ) (β : HS L N [⋀^Fin q]→L[ℝ] ℝ), UInv β →
    ∃ c : Pat L q → ℝ, β = ∑ x, c x • AT (N := N) x

def AGood : Prop :=
  SStokes → ∀ (L : Type) [Field L] [NumberField L] (N q : ℕ) (ω : Form (HS L N) q),
    (∀ g, FInv ω g) → Good ω

def WPad : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (n M q : ℕ), n ≤ M → ∀ x : Pat L q,
    (AT (N := M) x).compContinuousLinearMap (padL n M) = AT (N := n) x

def WBlk : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (d n q : ℕ) (x : Pat L q),
    (AT (N := d * n) x).compContinuousLinearMap (blkL d n) = ((d : ℝ) ^ ncyc x.1) • AT (N := n) x

def WInv : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N q : ℕ) (x : Pat L q), UInv (AT (N := N) x)

def WOne : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N q : ℕ) (x : Pat L q), Even q → ncyc x.1 = 1 → AT (N := N) x = 0

def WCyc : Prop := ∀ (q : ℕ) (σ : Equiv.Perm (Fin q)), 0 < q → 1 ≤ ncyc σ ∧ ncyc σ ≤ q

def TStab : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (n N : ℕ) (h : n ≤ N) (γ : Gm L n),
    (emb L N (stab (𝓞 L) n N h γ) • one L N).1 = padL n N (emb L n γ • one L n).1 + eL n N

def TBlk : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (d n : ℕ) (γ : Gm L n),
    (emb L (d * n) (psi (𝓞 L) d n γ) • one L (d * n)).1 = blkL d n (emb L n γ • one L n).1

def PStab : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (n N q : ℕ), n ≤ N → ∀ ω : Form (HS L N) q,
    (∀ g, FInv ω g) → ∀ g, FInv (pullF ω (padL n N) (eL n N)) g

def PBlk : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (d n q : ℕ) (ω : Form (HS L (d * n)) q),
    (∀ g, FInv ω g) → ∀ g, FInv (pullF ω (blkL d n) 0) g

open Classical in

def fT {L : Type} [Field L] [NumberField L] {N q : ℕ}
    (T : Matrix (Fin q → Ix (InfinitePlace L) N) (Fin q → Ix (InfinitePlace L) N) ℂ) (Y : Fin q → HS L N) : ℂ :=
  ∑ I, ∑ J, T I J * ∏ i, blk (fun w => mat (Y i) w) (I i) (J i)

open Classical in

def Cplx : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N q : ℕ) (f : ContinuousMultilinearMap ℝ (fun _ : Fin q => HS L N) ℝ),
    (∀ u : Gp L N, actL u (one L N).1 = (one L N).1 → ∀ Y, f (fun i => actL u (Y i)) = f Y) →
    ∃ T : Matrix (Fin q → Ix (InfinitePlace L) N) (Fin q → Ix (InfinitePlace L) N) ℂ,
      (∀ Y, f Y = (fT T Y).re) ∧
      ∀ d : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ, (∀ w, d w ∈ unitaryGroup (Fin N) ℂ) →
        tp q (blk d) * T = T * tp q (blk d)

end PositivityTheory.KB.BlockInvariants

end
