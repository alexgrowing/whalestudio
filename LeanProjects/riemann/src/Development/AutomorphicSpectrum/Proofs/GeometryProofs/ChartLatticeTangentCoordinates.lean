import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductMapIffStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsRigTransport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RiemGram

theorem hodgeForm_of_isHodgeGram {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {x : Sp ℂ ⟶ S} {n : ℕ}
    {v : Fin n → (epsAt x ⟶ G)} {Γ : Matrix (Fin n) (Fin n) ℂ} (hL : L.IsLB) (hv : ∀ i, IsTanAt G x (v i))
    (h : Fl.IsHodgeGram G L x v Γ) (i j : Fin n) : HodgeForm G L x (v i) (v j) (Γ i j) := by
  obtain ⟨Q, ψ, v', u, Hm, χ, W, hp, hiso, hAH, hvW, hΓ⟩ := h
  have hM : (L.pull ψ).IsLB := LB.isLB_pull hL ψ
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  exact ⟨hL, hv i, hv j, Q.A, inferInstance, ψ, Q.g, TorsionTauCompare.transport Q.isLB hM hw u, Hm, χ, v' i, v' j,
    W i, W j, hp, TorsionTauCompare.isAH_transport Q.isLB hM hw u hAH, (hvW i).1, (hvW j).1, (hvW i).2, (hvW j).2,
    hΓ i j⟩

theorem isTanAt_value {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {Ei : Type} [AddCommGroup Ei] [Module R Ei]
    (M : LieModel G (𝟙 (Sp R)) Ei) (f : R →+* ℂ) (e : Ei) (v : epsAt (spMap f) ⟶ G)
    (hv : v.left = spMap (dualMap f) ≫ (M.pt e).left) : IsTanAt G (spMap f) v := by
  have ht := M.tan e
  unfold IsTanAt at ht ⊢
  have hsq : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ spMap (dualMap f) =
      spMap f ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => ?_
    simp [dualMap]
  rw [hv, ← Category.assoc, hsq, Category.assoc, ht]
  let F : Over.mk (spMap f) ⟶ Over.mk (𝟙 (Sp R)) := Over.homMk (spMap f) (by simp)
  have h1 : F ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G) = 1 := MonObj.comp_one _
  exact congrArg CommaMorphism.left h1

theorem exists_value {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {Ei : Type} [AddCommGroup Ei] [Module R Ei]
    (M : LieModel G (𝟙 (Sp R)) Ei) (f : R →+* ℂ) (e : Ei) :
    ∃ v : epsAt (spMap f) ⟶ G, v.left = spMap (dualMap f) ≫ (M.pt e).left := by
  have hsq : spMap (dualMap f) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap f := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => ?_
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  refine ⟨Over.homMk (spMap (dualMap f) ≫ (M.pt e).left) ?_, rfl⟩
  have hw := Over.w (M.pt e)
  show (spMap (dualMap f) ≫ (M.pt e).left) ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap f
  rw [Category.assoc, hw, ← hsq]
  simp

theorem gramAt_of_isRiem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (X : Scheme.{0}) (t : SAB H X) (h : Sp C.R ⟶ X) (m : SABMap C.t t h) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (N : ℕ) (b : Fin N → Li) (x : Fin N → Fin C.g → C.R) (z : Fin n → ℂ) (Hm : Matrix (Fin C.g) (Fin C.g) ℂ) (w : Fin N → (epsAt (spMap (C.ψ z) ≫ h) ⟶ t.G)), C.IsRiem z Hm → (∀ k, M.ValAt _ (b k) (w k)) → (∀ k, (w k).left = spMap (dualMap (C.ψ z)) ≫ (C.M.pt (x k)).left ≫ m.φ) → M.GramAt t.PP.L (spMap (C.ψ z) ≫ h) b (Matrix.of fun i j => (Real.pi : ℂ) * ((fun e => C.ψ z (x j e)) ⬝ᵥ Hm *ᵥ star (fun e => C.ψ z (x i e)))) := by
  intro E _ _ _ H D l Xo σ n a C X t h m Ω _ ξ Li _ _ M N b x z Hm w hR hval hw
  choose v hv using fun k => exists_value C.M (C.ψ z) (x k)
  have hG := (hR N x v (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (fun e => C.ψ z (x i e))
    (fun e => C.ψ z (x j e))) hv).2 fun _ _ => rfl
  have hF := hodgeForm_of_isHodgeGram C.t.PP.isLB (fun k => isTanAt_value C.M (C.ψ z) (x k) (v k) (hv k)) hG
  have e : ∀ k, (w k).left = (v k).left ≫ m.φ := fun k => by rw [hw k, hv k, Category.assoc]
  exact ⟨w, hval, fun p q => (GlobalTheory.T.hodge_inner_product_map_iff E H X t (Sp C.R) C.t h m (spMap (C.ψ z)) (v p) (v q) (w p) (w q) _
    (e p) (e q)).1 (hodgeInnerProduct_iff_hodgeForm.2 (hF q p))⟩

end GlobalTheory.CompanionTheory.Ar.RiemGram
