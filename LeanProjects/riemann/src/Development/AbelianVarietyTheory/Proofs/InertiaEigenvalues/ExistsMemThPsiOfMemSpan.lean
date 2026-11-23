import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ser

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

open Classical in

def specXi (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) (h : GA D (Vc D j))
    (P : PolF D (Wc D j).rank (Vc D j).rank) : GA D (Wc D j) → ℂ :=
  ∑ a, ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a)) : X.Ok i k) • ρ.xi i j b Y Q M h P a

theorem exists_mem_thPsi_of_mem_span {ρ : Setup X} {hρ : ρ.Good} {Y : NExp D.R D.host D.what₂ D.LL0 N X} {i : X.Tw}
    {j : Fin D.R.m} {b : Bool} {rd : Rd ρ Y i j b} (T : CellTie hρ Y rd) (hR : RatTwist hρ rd) {k : ℕ}
    {Q : Finset (Pl D.host.E)} {ψ : G D.host.E N.Om →* (X.Ok i k)ˣ} (hψ : TwOK i k Q ψ) (hQ : ClsQ (D := D) Q)
    (d : Y.Dat i ((j : ℕ) + 1) b) {f : GA D (Wc D j) → ℂ}
    (hf : f ∈ Submodule.span (ρ.eOk i b k).range (ρ.gens i j b k Q ψ (T.cls d) (T.coef d))) :
    ∃ z ∈ Formalism.MainNotions.IntegralHeckeForms.ThPsi Y i ((j : ℕ) + 1) b k Q ψ {d}, rdK rd hρ k z = f := by
  induction hf using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨z, hz⟩ := hR k Q ψ hψ hQ _ _ _ (T.dat d) hs
    refine ⟨z, Submodule.subset_span ?_, hz⟩
    exact Set.mem_biUnion (Set.mem_singleton d) ((T.thPsi_iff k Q ψ hψ d z).2 (hz ▸ hs))
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add f g _ _ hf hg =>
    obtain ⟨z, hz, rfl⟩ := hf
    obtain ⟨z', hz', rfl⟩ := hg
    exact ⟨z + z', add_mem hz hz', map_add _ _ _⟩
  | smul c f _ hf =>
    obtain ⟨z, hz, rfl⟩ := hf
    obtain ⟨c', hc'⟩ := c.2
    refine ⟨c' • z, Submodule.smul_mem _ _ hz, ?_⟩
    rw [map_smulₛₗ]
    change ρ.eOk i b k c' • rdK rd hρ k z = (c : ℂ) • rdK rd hρ k z
    rw [hc']

end Ser

end GlobalTheory.SeriesTie

namespace GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SpecLoc

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

open Classical in

def specLoc (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) (y : Matrix (Fin (Wc D j).rank) (Fin (Vc D j).rank) (kP PP.1)) : ℂ :=
  ∑ c : ZMod (X.l i ^ M), ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) (Pi.single PP c))) : X.Ok i k) *
    ((Base.univFam (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (ρ.β j) PP.1 c y : ℚ) : ℂ)

def specSer (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) (h : GA D (Vc D j))
    (P : PolF D (Wc D j).rank (Vc D j).rank) : GA D (Wc D j) → ℂ :=
  twistBy (Wc D j) (ρ.tw i b k Q (χ.comp (Y.delU i Q M))).chi
    (series (ρ.B i j b).F (ρ.om i j b 1) ((ρ.B i j b).vecAt (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) (specLoc ρ Y i j b k Q M χ)) h P)

end SpecLoc

end GlobalTheory.SeriesTie

namespace GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ser2

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

open Classical in
theorem rdK_specU_grpSum {ρ : Setup X} (hρ : ρ.Good) {Y : NExp D.R D.host D.what₂ D.LL0 N X} {i : X.Tw}
    {j : Fin D.R.m} {b : Bool} (rd : Rd ρ Y i j b) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (x : (↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) → Y.Fm i ((j : ℕ) + 1) b) :
    rdK rd hρ k (Formalism.MainNotions.IntegralHeckeForms.specU Y i ((j : ℕ) + 1) b Q M k χ (grpSum Y (ρ.ch i) Q M x)) =
      ∑ a, ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a)) : X.Ok i k) • rd (x a) := by
  rw [grpSum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Formalism.MainNotions.IntegralHeckeForms.specU, LinearMap.coe_comp, Function.comp_apply, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, TensorProduct.comm_tmul, AlgHom.toLinearMap_apply, AddMonoidAlgebra.lift_single, one_smul,
    MonoidHom.coe_comp, Units.coeHom_apply]
  rw [rdK_tmul]

end Ser2

end GlobalTheory.SeriesTie
