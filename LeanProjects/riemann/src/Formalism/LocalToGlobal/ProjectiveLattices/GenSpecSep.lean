import Formalism.LocalToGlobal.ProjectiveLattices.GenSpecCut

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem sepX (Xo : Moduli Dw l) : SepXSt Xo := by
  unfold SepXSt
  have hq := Xo.qproj
  unfold IsQProjOver at hq
  obtain ⟨N, i, hi, -, hcomp⟩ := hq
  rw [← hcomp]
  haveI := hi
  infer_instance

theorem spMap_isDominant {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (hφ : Function.Injective φ) :
    IsDominant (spMap φ) := by
  unfold spMap
  constructor
  have hd : DenseRange (PrimeSpectrum.comap φ) := by
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
    exact bot_le
  exact hd

theorem x_eq_of_inj (Xo : Moduli Dw l) {S T : Type} [CommRing S] [IsReduced S] [CommRing T] (φ : S →+* T)
    (hφ : Function.Injective φ) {f g : Sp S ⟶ Xo.X} (hs : f ≫ Xo.s = g ≫ Xo.s)
    (h : spMap φ ≫ f = spMap φ ≫ g) : f = g := by
  haveI : IsSeparated Xo.s := sepX Xo
  haveI : IsDominant (spMap φ) := spMap_isDominant φ hφ
  first
  | exact ext_of_isDominant_of_isSeparated Xo.s hs (spMap φ) h
  | exact ext_of_isDominant_of_isSeparated Xo.s hs h
  | exact ext_of_isDominant_of_isSeparated (s := Xo.s) hs (ι := spMap φ) h

end Formalism.L2.Pj
