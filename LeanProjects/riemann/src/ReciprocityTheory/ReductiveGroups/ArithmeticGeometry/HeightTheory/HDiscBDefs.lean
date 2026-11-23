import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HNormDefs

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def fDivE (hd : d.AxH 𝒜) (h : d.S1) : KTf K d.D d.N :=
  ∏ c, ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nP h c d.wF (hd.a4.choose c) p

noncomputable def omE (hd : d.AxH 𝒜) (h : d.S1) : KTf K d.D d.N := d.De hd h * d.fDivE hd h ^ 2

def IsPres (hd : d.AxH 𝒜) (h : d.S1) (a b : KTp K d.D d.N) : Prop :=
  b ≠ 0 ∧ algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a =
    d.De hd h * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b ∧
  ∃ m : Fin (d.D + 1) → ℕ, m 0 = 0 ∧ ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m a ∧
    ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m b

noncomputable def mSgP (sg : K →+* ℂ) (a b : KTp K d.D d.N) : ℝ :=
  ∫ z, (Real.log ‖d.evT sg 0 (d.tOf z) a‖ - Real.log ‖d.evT sg 0 (d.tOf z) b‖)
    ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))

end Data

end ReciprocityTheory.ChartRestriction.G.T0
