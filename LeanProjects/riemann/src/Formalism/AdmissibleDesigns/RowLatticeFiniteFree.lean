import Formalism.AdmissibleDesigns.IdempotentPartRepresentationAt
import Formalism.AdmissibleDesigns.IdempotentPartFiniteAndFree
import Formalism.AdmissibleDesigns.PiEquiv2

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

set_option linter.style.haveILetI false

open Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.KRowA

open Formalism.MainNotions.N.KHf Module Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.RepresentationBoundsCohomology.FIN Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Ms

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

theorem rDuO_cont (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (x : D.nd.X i) : Continuous (rDuO D.nd i r x) := by
  have hce : Continuous fun g : GE D.nd => ((((chiU D.nd i 1 * epsU D.nd i) g : (D.nd.O i)ˣ)) : D.nd.O i) := by
    have e : (fun g : GE D.nd => ((((chiU D.nd i 1 * epsU D.nd i) g : (D.nd.O i)ˣ)) : D.nd.O i)) =
        fun g => ((chiU D.nd i 1 g : (D.nd.O i)ˣ) : D.nd.O i) * ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext g
      rw [MonoidHom.mul_apply, Units.val_mul]
    rw [e]
    exact (D.nd.chi_cont i 1).mul (K.St.hEps i)
  have hM : Continuous fun g : GE D.nd => (rO D.nd i r x g⁻¹).transpose :=
    ((hc x).comp continuous_inv).matrix_transpose
  exact hce.smul hM

theorem locC_du_cont (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) :
    Continuous ⇑(TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x)) := by
  have hinc : Continuous (TruncatedSeriesCountingIdentities.CoefExt.inc C) :=
    continuous_induced_rng.2 (by exact continuous_subtype_val)
  have h1 : Continuous fun g : Br.G D.nbr i w hw =>
      rDuO D.nd i r x ((Br.iota D.nbr i w hw g : _) : GE D.nd) :=
    (rDuO_cont i r hc x).comp (continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw))
  exact ((h1.matrix_map (D.nbr i w hw).eO_cont).matrix_map continuous_subtype_val).matrix_map hinc

end Ms

section Rec

attribute [local instance 2000] K.Topo.fracTopology K.Topo.rTopology

open Formalism.MainNotions.N.K Formalism.MainNotions.N.K.St

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)

include hD

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem rowSub_S :
    haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
    KRow.RowSub (ρ₁ := rho1 i Dd) i dc r := by
  haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  obtain ⟨hr', hsm, hχ⟩ := KLift.ringDef_lift i r Dd hD
  haveI := (idempotent_part_finite_and_free i r π g0 eB e₁ s Dd hD).1
  haveI := (idempotent_part_finite_and_free i r π g0 eB e₁ s Dd hD).2
  intro n _ hn
  exact rowSub_at i dc r Dd hr' hsm hχ hn

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem rowOrb_S (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) :
    haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
    KRow.RowOrb (ρ₁ := rho1 i Dd) i dc := by
  haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  intro n hn hw v
  exact orb_of_sub (LL := Br.LLw (D.nbr i _ hw)) (rowSub_S i r π dc g0 eB e₁ s Dd hD n hn hw)
    (fun x => by exact locC_du_cont i r hc hw (TruncatedSeriesCountingIdentities.CoefExt.self i _ hw) x) v

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem rowTop_S :
    haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
    KRow.RowTop i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (T₁ := FirstSummandSubmodule (D.nd.O i) Dd.e₁) := by
  apply KRow.rowTop_of
  · intro n _ hn
    exact KOrb.topMatch_pi (i := i) (hw := hn) _
  · exact rowTop1_S (i := i) (r := r) (π := π) (dc := dc) (g0 := g0) (eB := eB) (e₁ := e₁) (s := s)
      (Dd := Dd) (hD := hD)

variable [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem row_lattice_finite_free (n : ℕ) :
    Module.Finite (D.nd.O i) (DatS i r π dc g0 eB e₁ s Dd hD hc n).T' ∧
    Module.Free (D.nd.O i) (DatS i r π dc g0 eB e₁ s Dd hD hc n).T' ∧
    ∀ v : KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R) n, ∃ c : D.nd.O i, c ≠ 0 ∧
      ∃ t : (DatS i r π dc g0 eB e₁ s Dd hD hc n).T', (t : KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R) n) = c • v := by
  refine ⟨Module.Finite.equiv (vDS i r π dc g0 eB e₁ s Dd hD hc n),
    Module.Free.of_equiv (vDS i r π dc g0 eB e₁ s Dd hD hc n), fun v => ?_⟩
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (D.nd.O i)) Finset.univ v
  choose y hy using fun a => hb a (Finset.mem_univ a)
  refine ⟨(b : D.nd.O i), nonZeroDivisors.coe_ne_zero b, vDS i r π dc g0 eB e₁ s Dd hD hc n y, funext fun a => ?_⟩
  show algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (y a) = _
  rw [hy a]
  rfl

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem rowFin_S :
    KRow.RowFin i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R))
      (DatS i r π dc g0 eB e₁ s Dd hD hc) (T₁ := FirstSummandSubmodule (D.nd.O i) Dd.e₁) := by
  unfold KRow.RowFin
  have hT1 := idempotent_part_finite_and_free (i := i) (r := r) (π := π) (g0 := g0) (eB := eB) (e₁ := e₁) (s := s) (Dd := Dd) (hD := hD)
  exact ⟨hT1.1, hT1.2, fun n _ => row_lattice_finite_free i r π dc g0 eB e₁ s Dd hD hc n⟩

end Rec

end Formalism.MainNotions.N.KRowA

end
