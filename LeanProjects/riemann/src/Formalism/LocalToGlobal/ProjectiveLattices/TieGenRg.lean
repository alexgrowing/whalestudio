import Formalism.LocalToGlobal.ProjectiveLattices.TieReadingOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfA

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem ratio_single {Z : Comp Xo c} (G : WTZ E) (r s : Om Z) (hs : s ≠ 0) :
    ratio (Ω := Om Z) (AddMonoidAlgebra.single G r : AC Z) (AddMonoidAlgebra.single G s) = r / s := by
  have hex : ∃ a : Om Z, (AddMonoidAlgebra.single G r : AC Z) = a • AddMonoidAlgebra.single G s :=
    ⟨r / s, by rw [AddMonoidAlgebra.smul_single', div_mul_cancel₀ r hs]⟩
  unfold ratio
  rw [dif_pos hex]
  have e := hex.choose_spec
  rw [AddMonoidAlgebra.smul_single'] at e
  have e2 : r = hex.choose * s := by
    simpa [AddMonoidAlgebra.coeff_single] using congrArg (fun q : AC Z => q.coeff G) e
  rw [eq_div_iff hs]
  exact e2.symm

variable {D : D7} {T : Top D} {j : ℕ}
  {d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z)}
  {Z : Comp (T.Q.Xo j) T.Q.c} {X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r}

def RatRg (R : RdData1 d Z X) (x : Frame X.Ψ D.R.r) (P : Om Z →+* ℂ) : Prop :=
  ∀ G ∈ R.WE, ∀ f (hf : f ∈ R.Rg) g (hg : g ∈ R.Rg), f ∈ AG Z G → g ∈ AG Z G → g ≠ 0 →
    R.rd ⟨f, hf⟩ x = P (ratio (Ω := Om Z) f g) * R.rd ⟨g, hg⟩ x

def genRg (R : RdData1 d Z X) : Set (Frame X.Ψ D.R.r) :=
  {x | x ∈ X.dom ∧ ∃ P ∈ PT (Ω := Om Z) T.σ₀, RatRg R x P}

open Classical in

def ptRg (R : RdData1 d Z X) (hne : Nonempty (Om Z →+* ℂ)) (x : Frame X.Ψ D.R.r) : Om Z →+* ℂ :=
  if hx : x ∈ genRg R then hx.2.choose else hne.some

end Formalism.L2.Pj
