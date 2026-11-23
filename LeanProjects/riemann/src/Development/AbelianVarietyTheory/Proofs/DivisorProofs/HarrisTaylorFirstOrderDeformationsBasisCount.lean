import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumProjSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsDeRhamPairingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationLiftDeterminesModFilStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFirstOrderHodgeEqKodairaSpencerGraphStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRealiseKodairaSpencerDirectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorKodairaSpencerDirectionsDimStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.HTCount

theorem count : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∃ f : Fin (D.a * (D.n - 1)) → (HdR o₀.A →ₗ[k] HdR o₀.A), (∀ j, ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f j x)) ∧ ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∃! c : Fin (D.a * (D.n - 1)) → k, ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (∑ j, c j • f j x) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀
  obtain ⟨β, hβ⟩ : ∃ β : R →+* k, t = spMap β := ⟨(Spec.preimage t).hom, (Spec.map_preimage _).symm⟩
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.harrisTaylor_exists_deRham_pairing p D R b N hN hNp k t o₀
  obtain ⟨f, hfKS, huniq⟩ := GlobalTheory.T.harrisTaylor_kodairaSpencer_directions_dim p D R b N hN hNp k t o₀ β hβ φ hφ
  refine ⟨f, fun j => GlobalTheory.T.harrisTaylor_realise_kodairaSpencer_direction p D R b N hN hNp k t o₀ β hβ φ hφ (f j) (hfKS j), fun o' m' => ?_⟩
  obtain ⟨g, hgKS, hg⟩ := GlobalTheory.T.harrisTaylor_firstOrder_hodge_eq_kodairaSpencer_graph p D R b N hN hNp k t o₀ β hβ φ hφ o' m'
  obtain ⟨c, hc, hcu⟩ := huniq g hgKS
  refine ⟨c, fun x hx => ?_, fun c' hc' => hcu c' fun x hx => ?_⟩
  · refine (GlobalTheory.T.hodgeFiltration_lift_determines_mod_fil k o₀.A o'.A m'.φ m'.cart o'.ab x hx (g x) _ (hg x hx)).2 ?_
    rw [← neg_sub]; exact neg_mem (hc x hx)
  · have := (GlobalTheory.T.hodgeFiltration_lift_determines_mod_fil k o₀.A o'.A m'.φ m'.cart o'.ab x hx (g x) _ (hg x hx)).1 (hc' x hx)
    rw [← neg_sub]; exact neg_mem this

end GlobalTheory.HTCount
