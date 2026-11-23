import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLatticeSpanEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLatticeSpanEqStatement

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.GenShift
open IsDedekindDomain ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw
section General
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c}
end General
theorem span_weight_lattice_of_weights : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (la : GlobalTheory.AllWt.Weight (T.Q.Dw j)), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → (∀ k : ℕ, Y.GoodAt (wtOf _ ((k + 1) • la) 0)) → ∀ m : ℕ, Submodule.span Y.d.c₂.F (GlobalTheory.AllWt.latW Y.U (wtOf _ la m) : Set (Y.V (wtOf _ la m))) = ⊤ := by
  intro _ D T hT j hp _ _ hj Y e o hG la _ _ hgood m
  have hg0 : ∀ p : ℕ, p.Prime → T.Q.l.GoodAt p :=
    Formalism.L2.Pj.goodAt_of_two_primes hT.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
  have hg : ∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p := GlobalTheory.LawsDeep.goodAt_of_mul _ _ _ hG.lev.1.2.1 hg0
  have hs : ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, Nonempty (TwSec Y.U (xiR D) Z (wtOf (T.Q.Dw j) 0 (m : ℤ))) := fun Z => by
    obtain ⟨s⟩ := GlobalTheory.KeyTwDeep.twSec_keyRoot _ _ _ _ _ _ _ _ _ hG.unf hG.xiAbs hG.geo (le_add_right hp) hg Z
    exact exists_twPow s m
  have h0 := (hgood 0).2.2
  rw [zero_add, one_smul] at h0
  have key := span_latW_add hG.unf (wtOf (T.Q.Dw j) la 0) (wtOf (T.Q.Dw j) 0 (m : ℤ)) (even_wtOf _ _) hs h0
  have hGG : wtOf (T.Q.Dw j) la 0 + wtOf (T.Q.Dw j) 0 (m : ℤ) = wtOf (T.Q.Dw j) la (m : ℤ) := by
    rw [← wtOf_add, add_zero, zero_add]
  rw [hGG] at key
  exact key
end GlobalTheory.GenShift
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_lattice_spanned_by_weights : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (la : GlobalTheory.AllWt.Weight (T.Q.Dw j)), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → (∀ k : ℕ, Y.GoodAt (wtOf _ ((k + 1) • la) 0)) → ∀ m : ℕ, Submodule.span Y.d.c₂.F (GlobalTheory.AllWt.latW Y.U (wtOf _ la m) : Set (Y.V (wtOf _ la m))) = ⊤ := by
  first | exact @_root_.GlobalTheory.GenShift.span_weight_lattice_of_weights | exact _root_.GlobalTheory.GenShift.span_weight_lattice_of_weights | (intros; apply _root_.GlobalTheory.GenShift.span_weight_lattice_of_weights <;> assumption)
end
