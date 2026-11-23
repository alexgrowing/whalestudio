import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaObjectConstantFamilyDualNumbersIsPullbackStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsConstOfKsRelZeroStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.KerZero

def derPt {o R : Type} [CommRing o] [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ]
    (D : Derivation o R ℂ) : R →+* DualNumber ℂ where
  toFun r := TrivSqZeroExt.inl (algebraMap R ℂ r) + TrivSqZeroExt.inr (D r)
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [Algebra.smul_def, mul_comm, TrivSqZeroExt.algebraMap_eq_inl]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    spMap f' ≫ spMap f = spMap (f'.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]; rfl

theorem spMap_inj {R R' : Type} [CommRing R] [CommRing R'] {f f' : R →+* R'} (h : spMap f = spMap f') : f = f' := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

theorem derivation_eq_zero_of_ks_zero : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (R : Type) [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (t : TObj g k J b (spMap (algebraMap o R))) (s₀ : Sp ℂ ⟶ Sp o) (t₀ : TObj g k J b s₀) (m : t₀.A.left ⟶ t.A.left) (u : HolUnif t₀.pol.A t₀.pol.L t₀.pol.g) (Hm : Matrix (Fin t₀.pol.g) (Fin t₀.pol.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → (IsGrpPullback t₀.A t.A (spMap (algebraMap R ℂ)) m ∧ LBIso t₀.L (t.L.pull m) ∧ (∀ i, (t₀.pt i).left ≫ m = (spMap (algebraMap R ℂ)) ≫ (t.pt i).left) ∧ ∀ jj, (t₀.act jj).left ≫ m = m ≫ (t.act jj).left) → (∀ (x : Sp (DualNumber ℂ) ⟶ Sp R) (t' : TObj g k J b (x ≫ spMap (algebraMap o R))), x ≫ spMap (algebraMap o R) = constPt x ≫ spMap (algebraMap o R) → TMap t' t x → TMap t' t (constPt x) → x = constPt x) → ∀ (D : Derivation o R ℂ) s, KSRel u t.A.hom m (fun r => D r) 0 s → D = 0 := by
  intro h₁ h₂ h₃ o _ g k J b R _ _ _ _ _ t s₀ t₀ m u Hm χ hu hm hun D s hs
  obtain ⟨hm₁, hm₂, hm₃, hm₄⟩ := hm
  have hfst : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (derPt D) = spMap (algebraMap R ℂ) := by
    rw [spMap_comp]; congr 1; ext r; simp [derPt]
  obtain ⟨t', ht'⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g k J b _ _ _ _ (spMap (derPt D)) t rfl
  obtain ⟨φ, hφ₁, hφ₂, hφ₃, hφ₄⟩ := id ht'
  have hp := hφ₁.1
  let j : t₀.A.left ⟶ t'.A.left := hp.lift m (t₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)
    (by rw [hm₁.1.w, Category.assoc, hfst])
  have hj : j ≫ φ = m := hp.lift_fst _ _ _
  have hw : j ≫ t'.A.hom = t₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom := hp.lift_snd _ _ _
  have hj₁ : IsGrpPullback t₀.A t'.A (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j :=
    hφ₁.cancel (hm₁.congr hfst.symm hj.symm) hw
  have hj₂ : LBIso t₀.L (t'.L.pull j) :=
    LBIso.trans t₀.isLB (pull_isLB t.isLB m) (pull_isLB t'.isLB j) hm₂
      (LBIso.chartPull (chartPullPull t'.L j j rfl) (chartPullSame t.L _ _ _ j fun _ => hj.symm) hφ₂).symm
  have hj₃ : ∀ i, (t₀.pt i).left ≫ j = (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ (t'.pt i).left := by
    intro i
    apply hp.hom_ext
    · rw [Category.assoc, hj, hm₃, Category.assoc, hφ₃, ← Category.assoc, hfst]
    · have a₁ : (t₀.pt i).left ≫ t₀.A.hom = 𝟙 _ := Over.w (t₀.pt i)
      have a₂ : (t'.pt i).left ≫ t'.A.hom = 𝟙 _ := Over.w (t'.pt i)
      rw [Category.assoc, hw, ← Category.assoc, a₁, Category.assoc, a₂]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  have hj₄ : ∀ jj, (t₀.act jj).left ≫ j = j ≫ (t'.act jj).left := by
    intro a
    apply hp.hom_ext
    · rw [Category.assoc, hj, hm₄, Category.assoc, hφ₄, ← Category.assoc, hj]
    · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w, hw]
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_isConst_of_ksRel_zero' h₁ t₀.pol u Hm χ hu R (derPt D) t.A t'.A φ j s t.ab t'.ab hφ₁ hj₁ (by
    have e : (fun r => (derPt D r).snd) = fun r => D r := by funext r; simp [derPt]
    rw [e]
    exact hj ▸ hs)
  have hc := GlobalTheory.T.thetaObject_constantFamily_dualNumbers_isPullback h₁ h₂ h₃ o g k J b s₀ _ t₀ t' ρ j hρ ⟨hj₁, hj₂, hj₃, hj₄⟩
  have hcp : constPt (spMap (derPt D)) = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (algebraMap R ℂ) := by
    rw [constPt, hfst]
  have hc' : TMap t' t (constPt (spMap (derPt D))) := by
    rw [hcp]
    exact ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g k J b _ _ _ _ _ _ t t₀ t').2 _ _ ⟨m, hm₁, hm₂, hm₃, hm₄⟩).1 hc
  have hx := hun (spMap (derPt D)) t' (by
    rw [hcp, spMap_comp, spMap_comp, spMap_comp]
    congr 1
    ext r <;> simp [derPt, TrivSqZeroExt.algebraMap_eq_inl]) ht' hc'
  rw [hcp, spMap_comp] at hx
  have hx' := spMap_inj hx
  ext r
  have := congrArg (fun f : R →+* DualNumber ℂ => (f r).snd) hx'
  simpa [derPt, TrivSqZeroExt.algebraMap_eq_inl] using this

end GlobalTheory.KS.KerZero
end
