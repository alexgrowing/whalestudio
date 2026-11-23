import Formalism.LocalToGlobal.ClassS
import Formalism.LocalToGlobal.UnitaryNorms.DefsDatum

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.L2

namespace Host

local instance nfOfFinHD (L : Fld) [FiniteDimensional ℚ L] : NumberField L := {}

def UnramOverE {R : Ranks} (H : Formalism.BasicNotions.Host R) (L : Fld) [hL : FiniteDimensional ℚ L] : Prop :=
  (NumberField.discr L).natAbs = (NumberField.discr H.E).natAbs ^ (Module.finrank ℚ L / Module.finrank ℚ H.E)

def IsHilbertCFE {R : Ranks} (H : Formalism.BasicNotions.Host R) (L : Fld) [hL : FiniteDimensional ℚ L] : Prop :=
  Rows.AbelOver (H.EQ) L ∧ UnramOverE H L ∧
    ∀ (L' : Fld) [FiniteDimensional ℚ L'], Rows.AbelOver (H.EQ) L' → UnramOverE H L' → L' ≤ L

end Host

section

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}

structure HostDatumC {ex : Extra D L hT Gi Gl K Y cX} (T : LinkedFamilyData ex) where

  d3b : Host.PlacesOverCommonPrime D.host

  Tu_g : ∀ u i, (D.mem u).A.T ≠ D.host.g i

  Qw_Tu : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ v ∈ ex.nch.Q w, ∀ u, ¬ Host.OverP D.host (D.mem u).A.T v

  clsK : Host.ClsRepK D.host

  clsK_Tu : ∀ c u, IsCoprime (clsK.rep c : Ideal (𝓞 D.host.K)) (Host.idK (H := D.host) (D.mem u).A.T)

  clsK_Qw : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ v ∈ ex.nch.Q w, ∀ c,
    Host.PrimeToPl (H := D.host) (clsK.rep c : Ideal (𝓞 D.host.K)) v

  LLgal : IsGalois ℚ T.host.LLQ

  HE : Fld
  HE_fd : FiniteDimensional ℚ HE
  HE_hilb : Host.IsHilbertCFE (hL := HE_fd) D.host HE

  HE_le : HE ≤ Rows.KsQ D T.host T.n.cf T.what₂.O.pieces

def HostDatumS {ex : Extra D L hT Gi Gl K Y cX} (T : LinkedFamilyData ex) : Prop := Nonempty (HostDatumC T)

end

def CMDatumFamilyClass : FamClass := fun {_} Fm =>
  LinkedFamiliesAligned Fm ∧ ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, ∃ T : LinkedFamilyData (Fm.ex x hx i), HostDatumS T

theorem CMDatumFamilyClass.c2sa {eps : ℝ} {Fm : FamP eps} (h : CMDatumFamilyClass Fm) : LinkedFamiliesAligned Fm := h.1

theorem CMDatumFamilyClass.c2s {eps : ℝ} {Fm : FamP eps} (h : CMDatumFamilyClass Fm) : LinkedFamiliesLevelClass Fm := h.1.c2s

end Formalism.L2
