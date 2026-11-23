import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelAutomorphismRepresentation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf

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
theorem _root_.GlobalTheory.T.cover_type_lattice_comparison : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → Gram → DeepGood → Covers fun Fm x _ ι p i Y _ _ => ∃ (fr : TypeFrame (dat p i) Y.d.l₂) (π : (LevelAut (dat p i) Y.d.l₂) →* G0g (Fm.D x ι).nd) (s : G0g (Fm.D x ι).nd →* (LevelAut (dat p i) Y.d.l₂)) (ρ : Representation ℂ (LevelAut (dat p i) Y.d.l₂) (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) (χ : (LevelAut (dat p i) Y.d.l₂) →* ℂˣ) (Pb : Subgroup (G0g (Fm.D x ι).nd)) (lam : Pb →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, (Fm.D x ι).nd.PlG k), AddChar (ZMod ((Fm.D x ι).host.g kv.1)) ℂ) (lamb : Pb.comap π →* ℂˣ) (H : Fin 2 → Subgroup (G0g (Fm.D x ι).nd)), IsSplit π s ∧ IsWhit (Fm.D x ι) Pb lam ψ ∧ (∀ γ : Pb.comap π, lamb γ = lam ⟨π γ, γ.2⟩) ∧ (∀ k, IsHalf (Fm.D x ι) k (H k)) ∧ Pb.comap π = grpHR fr ∧ (∀ k, (H k).comap π = grpGHR fr k) ∧ (∀ (g : (LevelAut (dat p i) Y.d.l₂)) (v w : Y.V (Gk p i)), (w : Rul Y.d.Xo₂ Y.d.c₂) = transl Y.d.Xo₂ Y.d.c₂ g v → ρ g ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] v) = ((χ g : ℂˣ) : ℂ) • ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] w)) ∧ Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb) ∧ Formalism.HN.rkK (CovTop.latBad p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp s : Representation ℂ (G0g (Fm.D x ι).nd) (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) (Fm.D x ι).ntypes.e0) : Submodule ℂ (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) := by
  intro _ _ _
  refine GlobalTheory.CovTop.CovSz.covers_of_lifts (GlobalTheory.CovTop.Sizes.hostN 0) ?_
  intro eps Fm x hx ι p i C _ hN _ Y hY
  exact GlobalTheory.CovTop.BadRep.badRep_at p i Y hY
end
