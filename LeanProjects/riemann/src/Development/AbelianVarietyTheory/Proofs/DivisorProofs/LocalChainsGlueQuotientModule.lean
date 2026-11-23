import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulHomEqZeroOfCover

set_option autoImplicit false
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

noncomputable section

namespace GlobalTheory.ChainQuotFree

theorem of_equiv {p : ℕ} {A : Type} [CommRing A] {h o : ℕ} {π : A} {γ : ℕ → A} {Lie Om : Type} [AddCommGroup Lie]
    [Module A Lie] [AddCommGroup Om] [Module A Om] (C : RChain p A h o π γ Lie Om) {n : ℕ} (hn : n < o) {N : Type}
    [AddCommGroup N] [Module A N] (e : Qt (C.L n) (C.L (n + 1)) ≃ₗ[A] N) :
    Module.Finite A N ∧ (∀ s : N, γ n • s = 0) ∧
      Module.Projective (A ⧸ Ideal.span {γ n}) ((A ⧸ Ideal.span {γ n}) ⊗[A] N) := by
  haveI := C.finite n
  haveI := C.lfree n hn
  refine ⟨Module.Finite.equiv e, fun s => ?_,
    .of_equiv (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) e)⟩
  obtain ⟨y, rfl⟩ := e.surjective s
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [← map_smul, ← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero _).2, map_zero]
  exact C.gam n hn (Submodule.smul_mem_pointwise_smul _ _ _ x.2)

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] (h o : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (E : ℕ → B.X.Modules) (ι : ∀ n, E n ⟶ freeModule B.X (Fin h)) (I : Type) (V : I → B.X.Opens) (D : ∀ i, ChainOn p h o Lie Om π γ (V i)), IsLoc M ι V D → ∀ n < o, ∀ (Q : AM B Λ) (t : E n ⟶ Q.V), IsQuot M (ι n) (latOf (ι (n + 1))) Q t → LocFreeMod (γ n) Q.V := by
  intro O _ _ _ p _ B Λ _ h o Lie Om π γ M E ι I V D k n hn Q t q
  obtain ⟨hV, hc, -, hE, hF, -⟩ := k
  haveI := q.1
  haveI := (hE n).2
  refine GlobalTheory.LocFreeProj.main B.X Q.V (γ n) I V hV
    (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 (hc x)) fun i => ?_
  obtain ⟨e, -⟩ := q.exists_equiv (hV i) (hF i n hn.le) (hF i (n + 1) hn)
  exact of_equiv (D i) hn e

end GlobalTheory.ChainQuotFree

end
