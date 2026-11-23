import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelEqOfPowEqOfHasTh
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PowLeftCompOfGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

theorem level_eq_of_gLies_of_hasTh : Out.Laws → Out.Laws2 → ∀ (g n j : ℕ) (J : Type), n.Prime → Odd n → 2 ≤ j → ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (S S₁ : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver S ⟶ A)) (c : S₁ ⟶ S) (s₁ : S₁ ⟶ Sp o) (t₁ : TObj g ((n ^ j) ^ 2) J b s₁) (ψ₁ : t₁.A.left ⟶ A.left) (K : Type) [Field K] [IsAlgClosed K] (y y' : Sp K ⟶ S₁) (w : Ix g ((n ^ j) ^ 2) → K), L.IsLB → GLies A act Q c t₁ ψ₁ → LBIso t₁.L (L.pull ψ₁) → y ≫ c = y' ≫ c → y ≫ s₁ = y' ≫ s₁ → t₁.HasTh y w → t₁.HasTh y' w → ∀ i, y ≫ (t₁.pt i).left ≫ ψ₁ = y' ≫ (t₁.pt i).left ≫ ψ₁ := by
  intro hL hL2 g n j J hn hodd hj o _ b S S₁ A _ L act Q c s₁ t₁ ψ₁ K _ _ y y' w hLB hG hI hc hs T T'
  obtain ⟨u, ψ, m, ⟨a₁, -, a₃⟩, l, p⟩ :=
    gLies_pull o g (n ^ j) J b S S₁ _ A L act Q c s₁ t₁ ψ₁ y (y ≫ s₁) hLB hG hI rfl
  obtain ⟨u', ψ', m', ⟨a₁', -, a₃'⟩, l', p'⟩ :=
    gLies_pull o g (n ^ j) J b S S₁ _ A L act Q c s₁ t₁ ψ₁ y' (y ≫ s₁) hLB hG hI hs.symm
  rw [← hc] at a₁' a₃'
  have U : u.HasTh (𝟙 _) w :=
    (GlobalTheory.hasTh_iff_of_tmap o g (n ^ j) J b _ _ t₁ _ _ u _ K _ _ m).2 (by rwa [Category.id_comp])
  have U' : u'.HasTh (𝟙 _) w :=
    (GlobalTheory.hasTh_iff_of_tmap o g (n ^ j) J b _ _ t₁ _ _ u' _ K _ _ m').2 (by rwa [Category.id_comp])
  have hp := a₁.1
  let χ : u'.A.left ⟶ u.A.left := hp.lift ψ' u'.A.hom a₁'.1.w
  have e₁ : χ ≫ ψ = ψ' := hp.lift_fst _ _ _
  have e₂ : χ ≫ u.A.hom = u'.A.hom := hp.lift_snd _ _ _
  have c₁ : IsGrpPullback u'.A u.A (𝟙 _) χ :=
    a₁.cancel (a₁'.congr (Category.id_comp _).symm e₁.symm) (by rw [e₂, Category.comp_id])
  have c₀ : LBIso (u.L.pull χ) (L.pull ψ') :=
    l.chartPull (chartPullPull u.L χ χ rfl)
      (chartPullSame L (fun _ : PUnit => ψ') (fun _ : PUnit => ψ) (fun _ => 1) χ (fun _ => e₁.symm))
  have c₂ : LBIso u'.L (u.L.pull χ) :=
    LBIso.trans u'.isLB (pull_isLB hLB _) (pull_isLB u.isLB _) l' c₀.symm
  have c₃ : ∀ i, (u'.pt i ^ n ^ j).left ≫ χ = (u.pt i ^ n ^ j).left := fun i => by
    apply hp.hom_ext
    · rw [Category.assoc, e₁, a₃', a₃]
    · rw [Category.assoc, e₂, Over.w, Over.w]
  have c₅ := GlobalTheory.level_eq_of_pow_eq_of_hasTh hL hL2 g n j J hn hodd hj o b K _ u u' χ _ c₁ c₂ c₃ U U'
  intro i
  rw [← p, ← p', ← c₅, Category.assoc, e₁]

end GlobalTheory.ZM.NearBuild
end
