import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExactFunctorEquivariantChain
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBaseEqChain
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoRestrictPushforwardUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EAComm

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
open GlobalTheory.ChainParts

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exact_functor_equivariant_chain : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] {B : Vert.Model O} {Λ : Type} [CommRing Λ] {o : ℕ} (Q : EqChain p B Λ o) {ι : Type} (φ : ι → ι) (P : ι → (AM B Λ ⥤ B.X.Modules)) [∀ τ, (P τ).PreservesZeroMorphisms] (hlin : ∀ τ (M : AM B Λ) (g : Γ(B.X, ⊤)), IsAdd M → (P τ).map (smulA M g) = smulHom ((P τ).obj M) g) (hex : ∀ τ (S : ShortComplex (AM B Λ)), S.ShortExact → IsAdd S.X₁ → IsAdd S.X₂ → IsAdd S.X₃ → (S.map (P τ)).ShortExact) (hcok : ∀ τ {M N : AM B Λ} (f : M ⟶ N), IsAdd M → IsAdd N → Nonempty ((P τ).obj (cokernel f) ≅ cokernel ((P τ).map f))) (hvb : ∀ τ (E : EPres B Λ), ∃ r, GlobalTheory.VB.IsVB ((P τ).obj E.E) r ∧ GlobalTheory.VB.IsVB ((P τ).obj E.E') r ∧ IsIso (B.genRes.map ((P τ).map E.ψ))) (hfrob : ∀ τ (M : AM B Λ), IsAdd M → Nonempty ((P (φ τ)).obj (frobA p Q.hp M) ≅ (frobFun p Q.hp).obj ((P τ).obj M))) (hret : ∀ τ (M : AM B Λ), IsAdd M → ∃ (i : (P τ).obj M ⟶ M.V) (q : M.V ⟶ (P τ).obj M), i ≫ q = 𝟙 _) (hdiv : ∀ n < o, ∃ c : Γ(B.X, ⊤), Q.g = Q.γ n ^ p ^ n * c), ∃ Ch : Chain p B φ o, Ch.π = Q.π ∧ Ch.g = Q.g ∧ ∀ τ,
      (∃ r vb vb' iso, Ch.lw τ = ⟨r, (P τ).obj Q.lw.E, (P τ).obj Q.lw.E', vb, vb', (P τ).map Q.lw.ψ, iso⟩) ∧
      (∃ r vb vb' iso, Ch.oo τ = ⟨r, (P τ).obj Q.oo.E, (P τ).obj Q.oo.E', vb, vb', (P τ).map Q.oo.ψ, iso⟩) := by
  first | exact @GlobalTheory.ChainGlue.main | exact GlobalTheory.ChainGlue.main | (intros; apply GlobalTheory.ChainGlue.main <;> assumption)
