import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPrechartPointsSeparateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTorsionPrechartCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderHopfComultiplicationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionOrderFiniteProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionOrderComultiplicationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionOrderHopfIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfHopfOrderStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

theorem finite_tors_generic (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K]
    [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (hG : IsSemiAbelian G) (N : ℕ) (hN : N ≠ 0) : Finite (Tors G N K) := by
  obtain ⟨Idx, hI, q, c, hc⟩ := GlobalTheory.T.exists_finite_torsion_prechart_cover R K G hG N hN
  have hfin : ∀ i, Finite ((c i).C →ₐ[R] K) := fun i => (GlobalTheory.T.torsion_prechart_points_separate R K G hG N hN (q i) (c i)).1
  refine Finite.of_surjective (fun x : Σ i, ((c i).C →ₐ[R] K) => torsMap x.2 (c x.1).j) fun z => ?_
  obtain ⟨i, hi⟩ := hc K z
  obtain ⟨ψ, -, hψ⟩ := ((c i).bij K).surjOn hi
  exact ⟨⟨i, ψ⟩, hψ⟩

theorem exists_level : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra R A) (_ : IsCocomm R A) (_ : Module.Finite R A) (_ : Module.Projective R A) (θ : TorsPt G N A), IsLevel K θ := by
  intro R K _ _ _ _ _ _ _ _ G _ _ hG N hN
  haveI := finite_tors_generic R K G hG N hN
  obtain ⟨hf, hp, hs⟩ := GlobalTheory.T.torsion_order_finite_projective R K G hG N hN
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.torsion_order_comultiplication R K G hG N hN
  obtain ⟨A, iA, hA, cA, io, hio⟩ := GlobalTheory.T.order_hopf_comultiplication R K (Tors G N K) (ord G N K) hf hp hs h1 h2 h3
  haveI fA : Module.Finite R A := Module.Finite.equiv io.symm.toLinearEquiv
  haveI pA : Module.Projective R A := Module.Projective.of_equiv io.symm.toLinearEquiv
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.torsion_order_hopf_iso R K G hG N hN A io hio
  exact ⟨A, iA, hA, cA, fA, pA, θ, GlobalTheory.T.torsion_point_of_hopf_order R K G hG N hN A io θ hθ⟩

end GlobalTheory.GroupBplus.Aff
