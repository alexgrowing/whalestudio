import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.IntSplitOf
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.SelfDualPI

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain

namespace Formalism.L2.G

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

theorem selfDualAt_colLevel (L : ColLevel R F E sp gp C A clsLat) (v : HeightOneSpectrum (𝓞 F))
    (hT : (A.T : 𝓞 F) ∉ v.asIdeal) : SelfDualAt sp.cm.sig sp.gram0 v L.Lb :=
  self_dual_lattice_at F E R.k sp.cm.sig sp.gram0 v L.Lb A.T L.Lb_fin
    (fun x hx y hy => L.Lb_int y hy x hx) (fun y hy => L.Lb_dual y hy) hT

theorem selfDualAtP_of_not_mem (I : LocId L p nV W Qq) (hT : ∀ v : Fin nV, (A.T : 𝓞 F) ∉ (I.plc v).asIdeal) : Cmp.SelfDualAtP I :=
  fun v y => selfDualAt_colLevel L (I.plc v) (hT v) y

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem selfDualAtP_colLevel (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    {Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {nV : ℕ} {W' Qq' : Type}
    [CommRing W'] [Field Qq'] [Algebra W' Qq'] (I : LocId Lc (D.what₂.places.resChar w) nV W' Qq') : Cmp.SelfDualAtP I :=
  selfDualAtP_of_not_mem I fun v => (notBad_C D u w hg I v).2.2

theorem isHyperbolicAt_rec_of_placeIdentification (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    {Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {nV : ℕ} {W' Qq' : Type}
    [CommRing W'] [Field Qq'] [Algebra W' Qq'] (I : LocId Lc (D.what₂.places.resChar w) nV W' Qq') : Cmp.HypAtP I :=
  isHyperbolicAt_rec_of_isSelfDualAt D u w hg I (selfDualAtP_colLevel D u w hg I)

end Formalism.L2.G
