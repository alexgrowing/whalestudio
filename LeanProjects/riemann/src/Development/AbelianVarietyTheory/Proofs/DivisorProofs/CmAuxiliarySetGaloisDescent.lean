import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmRepresentationEigenDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedDenominatorInOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderActionMatrixEigenvaluesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamBasisBaseChangeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

namespace GlobalTheory.DRLine

theorem eigK_finrank_eq_one : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (σ : E →+* FractionRing R),
      Module.finrank (FractionRing R) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) σ) = 1 := by
  intro hPC hDR hDC E _ _ _ _ I _ d φ hφ 𝔣 h𝔣 l _ Q hQ hQl y hy lam 𝔠 R _ hR X₀ X U p cm hpull hcmF hα j hj φK hφK n eH σ
  classical
  choose α hαM hαp hαU using hα
  let T : orderC (condQ 𝔣 Q) → Module.End ℂ (HdR X.A) := fun a ↦ haveI := hαM a; push (dp0 ℂ) (𝟙 _) (α a)
  obtain ⟨B, hB⟩ := GlobalTheory.T.de_rham_basis_base_change hDR E (condQ 𝔣 Q) 𝔠 R X₀ X p cm hpull n eH
  have hTB : ∀ a i, T a (B i) = ∑ k, (((eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) a (Pi.single i 1) k : R) : ℂ) • B k :=
    fun a i ↦ by haveI := hαM a; exact hB a (α a) (hαp a) i
  rw [GlobalTheory.T.order_action_matrix_eigenvalues E (condQ 𝔣 Q) R n _ j hj (HdR X.A) B T hTB σ]
  obtain ⟨ε, hε⟩ := hPC
  have hLB : (X.diag U.c).IsLB := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull (X.isLB U.c) _
  obtain ⟨P, hspan, hrank, -, hpush, -⟩ := hε X.A (Module.finrank ℚ (FR E)) X.ab X.dim (X.diag U.c) hLB U.u

  have hmem : ∀ x : E, x ∈ lattice (condQ 𝔣 Q) y ↔ algebraMap E (Af E) x * (↑y⁻¹ : Af E) ∈ hatO (condQ 𝔣 Q) := fun x ↦ Iff.rfl
  let L : AddSubgroup E :=
    { carrier := lattice (condQ 𝔣 Q) y
      add_mem' := fun {a b} ha hb ↦ by
        show a + b ∈ lattice (condQ 𝔣 Q) y
        rw [hmem, map_add, add_mul]; exact Subring.add_mem _ ((hmem a).1 ha) ((hmem b).1 hb)
      zero_mem' := by
        show (0 : E) ∈ lattice (condQ 𝔣 Q) y
        rw [hmem, map_zero, zero_mul]; exact Subring.zero_mem _
      neg_mem' := fun {a} ha ↦ by
        show -a ∈ lattice (condQ 𝔣 Q) y
        rw [hmem, map_neg, neg_mul]; exact Subring.neg_mem _ ((hmem a).1 ha) }
  have hLs : ∀ a ∈ orderC (condQ 𝔣 Q), ∀ x ∈ L, a * x ∈ L := fun a ha x hx ↦ by
    show a * x ∈ lattice (condQ 𝔣 Q) y
    rw [hmem, map_mul, _root_.mul_assoc]
    refine Subring.mul_mem _ ?_ ((hmem x).1 hx)
    exact Subring.le_topologicalClosure _ ⟨a, ha, rfl⟩
  let Φ : E → (Fin (Module.finrank ℚ (FR E)) → ℂ) := fun x j ↦ φ (U.e j) x
  have hΦ : ∀ x ∈ L, Φ x ∈ U.u.Λ := fun x hx ↦ (U.lat _).2 ⟨x, hx, by funext j; simp [Φ, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]⟩
  let P' : L →+ HdR X.A :=
    { toFun := fun x ↦ P ⟨Φ x, hΦ x x.2⟩
      map_zero' := by
        have : (⟨Φ ((0 : L) : E), hΦ _ (0 : L).2⟩ : U.u.Λ) = 0 := Subtype.ext (by funext j; simp [Φ])
        rw [this, map_zero]
      map_add' := fun x x' ↦ by
        have : (⟨Φ ((x + x' : L) : E), hΦ _ (x + x').2⟩ : U.u.Λ) = ⟨Φ x, hΦ x x.2⟩ + ⟨Φ x', hΦ x' x'.2⟩ :=
          Subtype.ext (by funext j; simp [Φ])
        rw [this, map_add] }
  have hspan' : Submodule.span ℂ (Set.range P') = ⊤ := by
    rw [← hspan]; congr 1
    ext v; constructor
    · rintro ⟨x, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨w, rfl⟩
      obtain ⟨x, hx, hw⟩ := (U.lat w).1 w.2
      refine ⟨⟨x, hx⟩, ?_⟩
      show P _ = P w
      congr 1; apply Subtype.ext; rw [hw]; funext j; simp [Φ, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]
  have hdim : Module.finrank ℂ (HdR X.A) = Module.finrank ℚ E := by
    rw [hrank, ← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]
  have hT : ∀ (a : orderC (condQ 𝔣 Q)) (x x' : L), (x' : E) = a * x → T a (P' x) = P' x' := by
    intro a x x' hx'
    haveI := hαM a
    let M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
      { toFun := fun w j ↦ φ (U.e j) (a : E) * w j
        map_add' := fun w w' ↦ by funext j; simp [mul_add]
        map_smul' := fun r w ↦ by funext j; simp; ring }
    exact hpush (α a) M (fun w ↦ hαU a w) _ _ (by funext j; simp [M, Φ, hx', map_mul])
  have hc0 : condQ 𝔣 Q ≠ ⊥ := by
    unfold condQ
    refine mul_ne_zero h𝔣.1 ?_
    rw [Finset.prod_ne_zero_iff]
    exact fun q _ ↦ q.ne_bot
  exact GlobalTheory.T.cm_representation_eigen_decomposition E (orderC (condQ 𝔣 Q)) (GlobalTheory.T.bounded_denominator_in_order E _ hc0) L hLs (HdR X.A) P' hspan' hdim T hT (j.comp σ)

end GlobalTheory.DRLine
