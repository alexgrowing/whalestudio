import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs

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

noncomputable def tOf (z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1)) : Fin d.D → Fin (d.N + 1) → ℂ :=
  fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j

noncomputable def evT (sg : K →+* ℂ) (t0 : Fin (d.N + 1) → ℂ) (t : Fin d.D → Fin (d.N + 1) → ℂ)
    (q : KTp K d.D d.N) : ℂ :=
  MvPolynomial.eval₂ sg (fun v : TVar d.D d.N => Fin.cases (t0 v.2) (fun i => t i v.2) v.1) q

end Data

end ReciprocityTheory.ChartRestriction.G.T0
