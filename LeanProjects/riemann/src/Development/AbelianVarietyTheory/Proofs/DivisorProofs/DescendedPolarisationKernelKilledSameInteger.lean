import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverTargetGaloisCoverNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverOfRelAmpleOverQprojNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsGaloisCoverNoetherianBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullClsDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackDescentAlongGaloisCover
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamFieldPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTripleOfFieldExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.DescPolKer

theorem pow_eq_one_of_descent : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left) (e : ℕ), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∀ (T : Over X) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1) → ∀ (T : Over Y) (x : T ⟶ A₀), (∃ t : (P₀.pull (lift (snd A₀ T ≫ x) (fst A₀ T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  intro X Y π Ga _ ρ A _ _ A₀ _ _ φ φ₂ P P₀ e hG hA hA₀ hφ hsq hP hP₀ hw hker T x ⟨t, ht⟩
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exact pow_zero x
  let T₁ : Over X := Over.mk (pullback.snd T.hom π)
  let ε : T₁.left ⟶ T.left := pullback.fst T.hom π
  have hε : Epi ε := GlobalTheory.GaloisCartDesc.epi_pullback_fst hG T.hom
  let x₁ : T₁ ⟶ A := Over.homMk (hφ.1.lift (ε ≫ x.left) (pullback.snd T.hom π)
    (by simp [ε, pullback.condition])) (hφ.1.lift_snd _ _ _)
  have hx₁ : x₁.left ≫ φ = ε ≫ x.left := hφ.1.lift_fst _ _ _

  have p₀ : IsPullback (snd A₀ T).left (fst A₀ T).left T.hom A₀.hom :=
    (IsPullback.of_hasPullback A₀.hom T.hom).flip
  have w₀ : ((snd A T₁).left ≫ ε) ≫ T.hom = ((fst A T₁).left ≫ φ) ≫ A₀.hom := by
    have a₁ := Over.w (snd A T₁)
    have a₂ := Over.w (fst A T₁)
    simp only [T₁, Over.mk_hom] at a₁
    rw [Category.assoc, Category.assoc, hφ.1.w, ← Category.assoc (fst A T₁).left, a₂, ← a₁, Category.assoc]
    simp [ε, pullback.condition]
    rfl
  let hm : (A ⊗ T₁).left ⟶ (A₀ ⊗ T).left := p₀.lift _ _ w₀
  have hc : (lift (snd A T₁ ≫ x₁) (fst A T₁)).left ≫ φ₂ = hm ≫ (lift (snd A₀ T ≫ x) (fst A₀ T)).left := by
    have p₂ : IsPullback (snd A₀ A₀).left (fst A₀ A₀).left A₀.hom A₀.hom :=
      (IsPullback.of_hasPullback A₀.hom A₀.hom).flip
    apply p₂.hom_ext
    · rw [Category.assoc, hsq.2, ← Category.assoc, GlobalTheory.TripleDescent.lift_left_snd, Category.assoc,
        GlobalTheory.TripleDescent.lift_left_snd, p₀.lift_snd]
    · rw [Category.assoc, hsq.1, ← Category.assoc, GlobalTheory.TripleDescent.lift_left_fst, Category.assoc,
        GlobalTheory.TripleDescent.lift_left_fst, Over.comp_left, Over.comp_left, Category.assoc, hx₁,
        ← Category.assoc, ← Category.assoc, p₀.lift_fst]
  obtain ⟨w, hwg⟩ := hw
  obtain ⟨t', ht', -⟩ := GlobalTheory.FamFieldPull.exists_genPull w hwg hP₀ hP (K := PUnit)
    (fun _ => (lift (snd A T₁ ≫ x₁) (fst A T₁)).left) (fun _ => (lift (snd A₀ T ≫ x) (fst A₀ T)).left)
    (fun _ => 1) hm (fun _ => hc) t ht
  have h₁ : x₁ ^ e = 1 := hker T₁ x₁ ⟨t', ht'⟩

  let j : Over.mk (T₁.hom ≫ π) ⟶ T := Over.homMk ε (by simp [T₁, ε, pullback.condition])
  have hj : (j ≫ x).left = x₁.left ≫ φ := by simp [j, hx₁]
  have hpow : ∀ n : ℕ, ((j ≫ x) ^ (n + 1)).left = (x₁ ^ (n + 1)).left ≫ φ := by
    intro n
    induction n with
    | zero => simpa using hj
    | succ n ih =>
      rw [pow_succ, pow_succ x₁]
      exact hφ.2 T₁ (x₁ ^ (n + 1)) x₁ _ _ ih hj
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  have hy : (j ≫ x) ^ (k + 1) * (j ≫ x) ^ (k + 1) = (j ≫ x) ^ (k + 1) := by
    apply Over.OverMorphism.ext
    rw [← pow_add, show k + 1 + (k + 1) = (2 * k + 1) + 1 by ring, hpow, hpow,
      show 2 * k + 1 + 1 = (k + 1) + (k + 1) by ring, pow_add, h₁, _root_.one_mul]
  have hy1 := mul_eq_left.1 hy
  apply Over.OverMorphism.ext
  rw [← cancel_epi ε]
  have e₁ : ε ≫ (x ^ (k + 1)).left = (j ≫ x ^ (k + 1)).left := by rw [Over.comp_left]; rfl
  have e₂ : ε ≫ (1 : T ⟶ A₀).left = (j ≫ (1 : T ⟶ A₀)).left := by rw [Over.comp_left]; rfl
  rw [e₁, e₂, MonObj.comp_pow, hy1, MonObj.comp_one]

end GlobalTheory.DescPolKer
