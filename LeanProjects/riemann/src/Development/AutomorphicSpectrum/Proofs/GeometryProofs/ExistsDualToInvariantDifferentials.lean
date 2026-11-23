import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NonemptyEquivOfCardHom
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RelOfTorsion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderValueEval
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueBtOrderEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderIsHopfOrderNoetherianStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderContainsCharacters
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueTangentDualNumber

namespace GlobalTheory.CompanionTheory.Ar.BT

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

theorem valAt_sub_one {B : Type} [CommRing B] {X : Scheme.{0}} (y : Spec (CommRingCat.of B) ⟶ X) (a : Γ(X, ⊤)) :
    valAt y ⊤ le_top (a - 1) = valAt y ⊤ le_top a - 1 := by
  simp [valAt]

theorem omega_isDerAtOne : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L), ∃ θ : Module.Dual R L →ₗ[R] omega (Γ.btOrder ⊤), (Function.Surjective θ ∧ ∀ (f : augIdeal (Γ.btOrder ⊤)) (w : Module.Dual R L), θ w = (augIdeal (Γ.btOrder ⊤)).toCotangent f ↔ Γ.IsDerAtOne i M N (f.1.1 : T → R) w) ∧ (∀ w, θ w = 0 ↔ ∃ u, w = N • u) ∧ ∀ (χ : T →* Rˣ) (w : Module.Dual R L), Γ.IsHT i M N χ w → θ w = dlogChar (Γ.btOrder ⊤) χ := by
  intro R _ _ _ _ T _ _ Γ S G _ _ x N i ht hsm L _ _ M
  obtain ⟨θ, hsurj, hker, hpin⟩ := Tan.omega_canon R T Γ S G x N i ht hsm L M
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.existsUnique_btOrder_embedding R T Γ
  have hex := fun e : L => (TanLift.tangent_mod_torsion R T Γ S G x N i ht L M e).exists
  have hsec : ∀ f : Γ.btOrder ⊤, ∃ s, Γ.HasValues s (f : T → R) := fun f =>
    ⟨j.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Γ.btOrder ⊤))).inv.hom f), fun t =>
      ValEmb.valAt_pull j (Γ.pt t).left _ (hj.pt t) f⟩
  have pin : ∀ (f : augIdeal (Γ.btOrder ⊤)) (w : Module.Dual R L),
      θ w = (augIdeal (Γ.btOrder ⊤)).toCotangent f ↔ Γ.IsDerAtOne i M N (f.1.1 : T → R) w := by
    intro f w
    have h0 : (f.1.1 : T → R) 1 = 0 := f.2
    constructor
    · intro h
      obtain ⟨s, hs⟩ := hsec f.1
      refine ⟨s, hs, fun e => ?_⟩
      obtain ⟨v, a, b⟩ := hex e
      refine ⟨v, a, b, ?_⟩
      rw [(hpin f w s hs).1 h e v a b, h0]
      simp
    · rintro ⟨s, hs, hv⟩
      refine (hpin f w s hs).2 fun e v a b => ?_
      obtain ⟨v', a', b', c'⟩ := hv e
      obtain rfl := (TanLift.tangent_mod_torsion R T Γ S G x N i ht L M e).unique ⟨a, b⟩ ⟨a', b'⟩
      rw [c', h0]
      simp
  refine ⟨θ, ⟨hsurj, pin⟩, hker, ?_⟩
  rintro χ w ⟨s, hs, hv⟩
  have hχ : (fun t => ((χ t : Rˣ) : R)) ∈ Γ.btOrder ⊤ :=
    char_mem_hopfOrder R T _ (GlobalTheory.T.btOrder_isHopfOrder_noetherian R T Γ) χ
  rw [OrderApi.dlogChar_of_mem _ χ hχ]
  refine (pin _ w).2 ⟨s - 1, fun t => ?_, fun e => ?_⟩
  · rw [valAt_sub_one, hs t]
    simp
  · obtain ⟨v, a, b, c⟩ := hv e
    refine ⟨v, a, b, ?_⟩
    rw [valAt_sub_one, c]
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp

end GlobalTheory.CompanionTheory.Ar.BT
