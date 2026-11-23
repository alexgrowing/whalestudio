import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscBDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AGFrameNonneg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DePres
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FprodNeZero

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

theorem om_poly (hd : d.AxH 𝒜) (h : d.S1) :
    0 ≤ d.aG h d.wF hd.a4.choose ∧ (∃ a b : KTp K d.D d.N, d.IsPres hd h a b) ∧
    ∃ Om : KTp K d.D d.N, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Om = d.omE hd h ∧ Om ≠ 0 ∧
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous
        (fun b : Fin (d.D + 1) => if b = 0 then 0 else 2 * (d.aG h d.wF hd.a4.choose).toNat) Om := by
  exact ⟨d.aG_frame_nonneg hd h, d.de_pres hd h, d.om_is_poly hd h⟩

end Data

end ReciprocityTheory.ChartRestriction.G.T0
