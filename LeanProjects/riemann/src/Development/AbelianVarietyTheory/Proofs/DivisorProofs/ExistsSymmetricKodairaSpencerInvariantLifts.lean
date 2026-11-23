import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisPullbackMatrixInvariantFieldsRaynaudStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerDescentOfTorusInvariantLiftsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRelationMatrixSymmetricLocalDomainStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.InvLiftSymm

theorem exists_symm_invLift : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι) (d : J → Fld Y.H.left), ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) → (∀ i, (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f))) → ∀ C : Matrix (Fin n) (Fin n) R, (∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d i W f - d i' W f = ∑ a, ∑ b, constFn Y.H.hom W (C a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W * dd a W f) → ∃ Θ : Matrix (Fin n) (Fin n) R, Θᵀ = Θ ∧ ∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d i W f - d i' W f = ∑ a, ∑ b, constFn Y.H.hom W (Θ a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W * dd a W f := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hinv D J V j d hcov hle hlift hwt C hrel
  obtain ⟨g, w, e, P, Qm, he, hPQ, hfac⟩ := GlobalTheory.T.exists_basis_pullback_matrix_invariantFields_raynaud R Dd O oa Y n v dd hinv
  have hKS := GlobalTheory.T.kodairaSpencer_descent_of_torus_invariant_lifts R Dd O oa Y n v dd hinv g w e P he hfac D J V j d hcov hle hlift hwt C hrel
  have hM : (P * C * Pᵀ)ᵀ = P * C * Pᵀ := GlobalTheory.T.kodairaSpencer_relation_matrix_symmetric_local_domain R Dd.toPre.P g w e he D _ hKS
  have hM' : P * (Cᵀ * Pᵀ) = P * (C * Pᵀ) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at hM
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hM, Matrix.mul_assoc]
  have hQP : Qmᵀ * Pᵀ = 1 := by rw [← Matrix.transpose_mul, hPQ, Matrix.transpose_one]
  set Θ : Matrix (Fin n) (Fin n) R := C * Pᵀ * Qmᵀ + Qm * P * Cᵀ - Qm * (P * C * Pᵀ) * Qmᵀ with hΘ
  have hΘP : Θ * Pᵀ = C * Pᵀ := by
    rw [hΘ, Matrix.sub_mul, Matrix.add_mul]
    simp only [Matrix.mul_assoc, hQP, Matrix.mul_one]
    rw [hM']
    simp only [← Matrix.mul_assoc]
    abel
  refine ⟨Θ, ?_, ?_⟩
  · rw [hΘ]
    simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose, hM]
    simp only [Matrix.mul_assoc]
    abel
  · intro i i' W hW f
    rw [hrel i i' W hW f]
    let cf : R →+* Γ(Y.H.left, W) :=
      (Y.H.hom.appLE ⊤ W (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    have hcf : ∀ r, constFn Y.H.hom W r = cf r := fun _ => rfl
    have hW' : W ≤ Y.q.left ⁻¹ᵁ (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i')) :=
      fun x hx => ⟨hle i (hW hx).1, hle i' (hW hx).2⟩
    set X : Fin g → Γ(Y.H.left, W) := fun c =>
      pbT Y.q.left (e c _ (Dd.toPre.P.L.g (j i) (j i')).val) W * pbT Y.q.left (Dd.toPre.P.L.g (j i) (j i'))⁻¹.val W
    have hdlg : ∀ b, dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W = ∑ c, cf (P c b) * X c := by
      intro b
      rw [dlg, hfac b _ W hW', Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hcf, _root_.mul_assoc]
    have key : ∀ (A : Matrix (Fin n) (Fin n) R) (a : Fin n),
        ∑ b, cf (A a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W = ∑ c, cf ((A * Pᵀ) a c) * X c := by
      intro A a
      simp only [hdlg, Finset.mul_sum, Matrix.mul_apply, Matrix.transpose_apply, map_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul, _root_.mul_assoc]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hcf, ← Finset.sum_mul]
    rw [key Θ a, key C a, hΘP]

end GlobalTheory.InvLiftSymm
