import Formalism.LocalRingCardinality.SpanPowerMembership.NZColF

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.MainNotions.G Classical Module

variable {D : D7}

def withNu (L : SizeData₂ D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V)
    (len : D.what₂.Word → D.what₂.places.Pl → ℚ) : SizeData₂ D :=
  { L with NuLat := N, lenMN := len }

def instNu {L : SizeData₂ D} (X : Inst D L) (N len) : Inst D (withNu L N len) :=
  { bs := X.bs, bs_orb := X.bs_orb, bs_step := X.bs_step, off := X.off, off_top := X.off_top, off_thin := X.off_thin,
    off_thick := X.off_thick, kapI := X.kapI, ep := X.ep }

variable (c : LatCmp D) {L : SizeData₂ D} (X : Inst D L) (Y : LatInst D) (K : Consts)
  (hv : c.VramDef Y) (hT : TAbs D)

def sizeDataNu : SizeData₂ D :=
  withNu L (nuLat (nuDataOf c X Y K hv hT)) (lenOf D (nuLat (nuDataOf c X Y K hv hT)))

def instOfNu : Inst D (sizeDataNu c X Y K hv hT) := instNu X _ _

end Formalism.BasicNotions.Examples₂.NZ
