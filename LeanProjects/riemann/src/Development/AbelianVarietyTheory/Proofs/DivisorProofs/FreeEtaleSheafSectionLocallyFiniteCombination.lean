import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLiftStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem etaleLocally_weaken_freeSheafSections {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U P) (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem free_sec_lin_sum {S X M : Type*} [Semiring S] [AddCommMonoid M] [Module S M]
    (φ : (X →₀ S) →ₗ[S] M) (x : X →₀ S) :
    (x.sum fun a r => r • φ (Finsupp.single a 1)) = φ x := by
  calc (x.sum fun a r => r • φ (Finsupp.single a 1))
      = x.sum fun a r => φ (Finsupp.single a r) := by
        refine Finsupp.sum_congr fun a _ => ?_
        rw [← map_smul, Finsupp.smul_single_one]
    _ = φ x := by rw [← map_finsuppSum, Finsupp.sum_single]

theorem free_sec_sum_eq (R : Type) [CommRing R] (P : PSh) (V : Scheme.{0})
    (x : ULift.{1} (P.obj (op V)) →₀ ULift.{1} R) :
    ((Finsupp.mapDomain ULift.down x).sum fun a r => r • freeGen R P V a) =
      ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom x := by
  rw [Finsupp.sum_mapDomain_index_inj ULift.down_injective]
  exact free_sec_lin_sum ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom x

theorem free_sec_loc : ∀ (R : Type) [CommRing R] (P : PSh) (U : Scheme.{0}), (∀ y : Sec ((free R).obj P) U, Loc U fun V g => ∃ c : P.obj (op V) →₀ ULift.{1} R, Sec.res g y = c.sum fun x r => r • freeGen R P V x) ∧ ∀ c : P.obj (op U) →₀ ULift.{1} R, (c.sum fun x r => r • freeGen R P U x) = 0 → Loc U fun _ g => Finsupp.mapDomain (P.map g.op) c = 0 := by
  intro R _ P U
  have base := GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift R ((freeP R).obj P)
  refine ⟨fun y => ?_, fun c hc => ?_⟩
  · refine etaleLocally_weaken_freeSheafSections (base.1 U y) ?_
    rintro V g ⟨x, hx⟩
    exact ⟨_, ((free_sec_sum_eq R P V x).trans hx).symm⟩
  · have hdu : Finsupp.mapDomain ULift.down (Finsupp.mapDomain ULift.up c) = c := by
      rw [← Finsupp.mapDomain_comp]
      exact Finsupp.mapDomain_id
    have h2 : ((Finsupp.mapDomain ULift.down (Finsupp.mapDomain ULift.up c)).sum
        fun a r => r • freeGen R P U a) = 0 := by
      rw [hdu]
      exact hc
    have hx := (free_sec_sum_eq R P U _).symm.trans h2
    refine etaleLocally_weaken_freeSheafSections (base.2.1 U _ hx) ?_
    intro V g hg
    have key : Finsupp.mapDomain ULift.down ((((freeP R).obj P).map g.op).hom
        (Finsupp.mapDomain ULift.up c)) = Finsupp.mapDomain (P.map g.op) c := by
      have e1 : (((freeP R).obj P).map g.op).hom (Finsupp.mapDomain ULift.up c) =
          Finsupp.mapDomain (fun a : ULift.{1} (P.obj (op U)) =>
            (ULift.up (P.map g.op a.down) : ULift.{1} (P.obj (op V)))) (Finsupp.mapDomain ULift.up c) := rfl
      rw [e1, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
      rfl
    rw [← key]
    exact (congrArg (Finsupp.mapDomain ULift.down) hg).trans Finsupp.mapDomain_zero

end GlobalTheory.EtC
