import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.Vert

namespace GlobalTheory.MixedLocalChains

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B B' : Vert.Model O}

noncomputable def Pres.pull (P : Pres B) (f : Vert.Model.Hom B' B) : Pres B' where
  r := P.r
  E := (Scheme.Modules.pullback f.f).obj P.E
  E' := (Scheme.Modules.pullback f.f).obj P.E'
  vb := P.vb.pullback f.f
  vb' := P.vb'.pullback f.f
  ψ := (Scheme.Modules.pullback f.f).map P.ψ
  iso := by
    haveI := P.iso
    rw [← Vert.Model.GenIso.pull_inv f.comp_str (φ := Vert.Model.GenIso.ofHom P.ψ) rfl]
    infer_instance

theorem Pres.ofHom_pull (P : Pres B) (f : Vert.Model.Hom B' B) :
    (haveI := (P.pull f).iso; Vert.Model.GenIso.ofHom (P.pull f).ψ) =
      (haveI := P.iso; (Vert.Model.GenIso.ofHom P.ψ).pull f.comp_str) := by
  haveI := P.iso
  haveI := (P.pull f).iso
  exact Iso.ext <| (Iso.inv_eq_inv (Vert.Model.GenIso.ofHom (P.pull f).ψ)
    ((Vert.Model.GenIso.ofHom P.ψ).pull f.comp_str)).1
    (Vert.Model.GenIso.pull_inv f.comp_str (φ := Vert.Model.GenIso.ofHom P.ψ) rfl).symm

noncomputable def Pres.pullModIso (P : Pres B) (f : Vert.Model.Hom B' B) :
    (P.pull f).mod ≅ (Scheme.Modules.pullback f.f).obj P.mod :=
  (PreservesCokernel.iso (Scheme.Modules.pullback f.f) P.ψ).symm

end GlobalTheory.MixedLocalChains

end
