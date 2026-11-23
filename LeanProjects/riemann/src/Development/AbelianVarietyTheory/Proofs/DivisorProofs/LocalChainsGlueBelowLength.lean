import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomOfBasis

set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain mv baseOf Qt IsFrobLin)
open GlobalTheory.ChainPts.PullHT (pullA)
open GlobalTheory.PerfdLat (piMap)
open scoped TensorProduct Pointwise
open GlobalTheory.ChainPts
open GlobalTheory.ChainDesc

namespace GlobalTheory.ChainDesc

theorem kills_of_isQuot : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] (h o : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (E : ℕ → B.X.Modules) (ι : ∀ n, E n ⟶ freeModule B.X (Fin h)) (I : Type) (V : I → B.X.Opens) (D : ∀ i, ChainOn p h o Lie Om π γ (V i)), IsLoc M ι V D → ∀ n < o, ∀ (Q : AM B Λ) (t : E (n + 1) ⟶ Q.V), IsQuot M (ι (n + 1)) (baseOn h π) Q t → Kills (γ 0) Q.V := by
  intro O _ _ _ p _ B Λ _ h o Lie Om π γ M E ι I V D k n hn Q t q
  obtain ⟨hV, hc, -, -, hF, -⟩ := k
  haveI := q.1
  have hcov : TopologicalSpace.IsOpenCover V := top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 (hc x)
  refine (GlobalTheory.QCoh.hom_eq_zero_iff_affineCover V hcov hV _).2 fun i s => ?_
  obtain ⟨h1, h2, -⟩ := q.2 (V i) (hV i)
  obtain ⟨s, rfl⟩ := h1 s
  have e : t.app (V i) ((resG B.X le_top (γ 0) : Γ(B.X, V i)) • s) = 0 := by
    rw [h2, map_smul]
    refine (D i).kill n hn (Submodule.smul_mem_pointwise_smul _ _ _ ?_)
    rw [hF i (n + 1) hn]
    exact ⟨s, rfl⟩
  exact ((appLinear t (V i)).map_smul _ s).symm.trans e

end GlobalTheory.ChainDesc
