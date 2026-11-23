import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGoodStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.BcMor

theorem chart_mor : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I)
    {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {V : X.Opens} {d : ℕ} (cV : Coord q V d),
    letI := (strV q V).toAlgebra
    ∀ (cO : Chart (dividedPowersBot O) 0 q (Ideal.Quotient.mk ⊥) V d) (cA : Chart γ 0 q (κA O I) V d)
      (eO : O ⊗[O] Γ(X, V) ≃+* cO.D.B) (eA : A ⊗[O] Γ(X, V) ≃+* cA.D.B),
      (∀ r, eO (r ⊗ₜ 1) = cO.D.i r) → (∀ r, eA (r ⊗ₜ 1) = cA.D.i r) →
      (∀ f, ev cO.D cO.inV f = Ideal.Quotient.mk _ (eO (1 ⊗ₜ f))) →
      (∀ f, ev cA.D cA.inV f = Ideal.Quotient.mk _ (eA (1 ⊗ₜ f))) →
      ∃ e₀ : cO.D ⟶ ((nmO γ q).mor 0).obj cA.D, ∀ f, e₀.φ (eO (1 ⊗ₜ f)) = eA (1 ⊗ₜ f) := by
  intro O A _ _ _ I γ X q V d cV
  letI a0 : Algebra O Γ(X, V) := (strV q V).toAlgebra
  intro cO cA eO eA hO hA hvO hvA
  have hptT : pt (((nmO γ q).mor 0).obj cA.D) = pt cA.D := Category.comp_id _
  have hT : InU V (((nmO γ q).mor 0).obj cA.D) := by
    unfold InU
    rw [hptT]
    exact cA.inV
  obtain ⟨g, hg, -⟩ := cO.rep (CommRingCat.of ((((nmO γ q).mor 0).obj cA.D).B ⧸ (((nmO γ q).mor 0).obj cA.D).J))
    (((nmO γ q).mor 0).obj cA.D).y hT
  have hg' : (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)).Pt.map (CommRingCat.ofHom g) cO.D.y =
      (((nmO γ q).mor 0).obj cA.D).y := hg
  let ι : O ⊗[O] Γ(X, V) →+* A ⊗[O] Γ(X, V) :=
    (Algebra.TensorProduct.map (Algebra.ofId O A) (AlgHom.id O Γ(X, V))).toRingHom
  let φ : cO.D.B →+* cA.D.B := (eA.toRingHom.comp ι).comp eO.symm.toRingHom
  have hφ : ∀ f, φ (eO (1 ⊗ₜ f)) = eA (1 ⊗ₜ f) := fun f => by
    change eA (ι (eO.symm (eO (1 ⊗ₜ f)))) = _
    rw [RingEquiv.symm_apply_apply]
    change eA (Algebra.TensorProduct.map (Algebra.ofId O A) (AlgHom.id O Γ(X, V)) (1 ⊗ₜ f)) = _
    simp
  have hf : ∀ r, φ (cO.D.i r) = (((nmO γ q).mor 0).obj cA.D).i r := fun r => by
    change eA (ι (eO.symm (cO.D.i r))) = cA.D.i (algebraMap O A r)
    rw [← hO r, RingEquiv.symm_apply_apply, ← hA]
    change eA (Algebra.TensorProduct.map (Algebra.ofId O A) (AlgHom.id O Γ(X, V)) (r ⊗ₜ 1)) = _
    simp [Algebra.ofId_apply]
  have hptg : pt (((nmO γ q).mor 0).obj cA.D) = Spec.map (CommRingCat.ofHom g) ≫ pt cO.D := by
    unfold pt
    rw [← hg']
    rfl
  have hev : ∀ f, ev cA.D cA.inV f = g (ev cO.D cO.inV f) := fun f => by
    have key : ∀ (y : Spec (CommRingCat.of (cA.D.B ⧸ cA.D.J)) ⟶ X) (_ : y = Spec.map (CommRingCat.ofHom g) ≫ pt cO.D)
        (h'' : ⊤ ≤ y ⁻¹ᵁ V), GlobalTheory.Cris.evalAt y V h'' f = g (ev cO.D cO.inV f) := by
      intro y hy h''
      subst hy
      exact GlobalTheory.LogCris.evalAt_map _ (pt cO.D) cO.inV h'' f
    exact key _ (hptT.symm.trans hptg) cA.inV
  have hq : (Ideal.Quotient.mk (((nmO γ q).mor 0).obj cA.D).J).comp φ = g.comp (Ideal.Quotient.mk cO.D.J) := by
    refine RingHom.ext fun x => ?_
    obtain ⟨f, rfl⟩ : ∃ f, x = eO (1 ⊗ₜ f) := by
      refine ⟨TensorProduct.lid O Γ(X, V) (eO.symm x), ?_⟩
      have e : (1 : O) ⊗ₜ[O] (TensorProduct.lid O Γ(X, V) (eO.symm x)) = eO.symm x :=
        (TensorProduct.lid O Γ(X, V)).symm_apply_apply (eO.symm x)
      rw [e, RingEquiv.apply_symm_apply]
    change Ideal.Quotient.mk cA.D.J (φ (eO (1 ⊗ₜ f))) = g (Ideal.Quotient.mk cO.D.J (eO (1 ⊗ₜ f)))
    rw [hφ, ← hvA, ← hvO, hev]
  exact ⟨GlobalTheory.CompanionTheory.ChartMaps.homOf cO (((nmO γ q).mor 0).obj cA.D) φ hf g hq hg', hφ⟩

end GlobalTheory.CompanionTheory.BcMor
