import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.Crude

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {R : Type} [CommRing R] {d n : ℕ}

def Lin (b : Fin n) (v : Fin d → R) (f : PS R n d) : PS R n d :=
  ∑ j : Fin d, C (v j) * pderiv R (b, j) f

def LinMon {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → R) (m : ι →₀ ℕ) (f : PS R n d) :
    PS R n d :=
  (Finset.univ : Finset ι).toList.foldr (fun l g => (Lin (cp l) (u l))^[m l] g) f

def OrdGe (N : ℕ) (f : PS R n d) : Prop :=
  ∀ m : Fin n × Fin d →₀ ℕ, m.degree < N → coeff m f = 0

end Formalism.L2.Pj.Crude
