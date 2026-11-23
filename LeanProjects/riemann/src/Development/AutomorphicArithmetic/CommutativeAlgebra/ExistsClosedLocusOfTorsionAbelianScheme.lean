import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SubRepPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem UpperTheory.exists_closed_locus_of_torsion_abelianScheme :
    ∀ {S T : Scheme.{0}} (x : T ⟶ S) (A G : Over S) [GrpObj A] (inc : G ⟶ A) (k : ℕ), (∀ (T' : Over S) (a : T' ⟶ G), (a ≫ inc) ^ k = 1) → IsUnit (k : Γ(T, ⊤)) → ∀ (A₁ : Over T) [GrpObj A₁] (φ₁ : A₁.left ⟶ A.left) (B₁ : Over T) [GrpObj B₁] (f : A₁ ⟶ B₁), IsGrpPullback A₁ A x φ₁ → IsAbelianScheme B₁ → IsMonHom f → ∃ V : (Over.mk x ⊗ G).left.Opens, IsClosed (V : Set (Over.mk x ⊗ G).left) ∧ ∀ (T' : Over S) (t : T' ⟶ Over.mk x) (a : T' ⟶ G) (g : Over.mk t.left ⟶ A₁), g.left ≫ φ₁ = a.left ≫ inc.left → (g ≫ f = 1 ↔ Set.range (lift t a).left ⊆ V) := by
  intro S T x A G _ inc k hk hu A₁ _ φ₁ B₁ _ f hP hB hf
  have hfe := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion B₁ (hG := hB) hu
  obtain ⟨hfin, het⟩ := hfe.2
  let pr : (Over.mk x ⊗ G).left ⟶ T := (fst (Over.mk x) G).left
  have hpr : pr ≫ x = (Over.mk x ⊗ G).hom := Over.w (fst (Over.mk x) G)
  obtain ⟨τ, hτ, -⟩ := UpperTheory.SubRep.pull_existsUnique hP (Over.mk x ⊗ G) pr hpr (snd (Over.mk x) G ≫ inc)
  have hτk : τ ^ k = 1 := by
    apply UpperTheory.SubRep.pull_ext hP
    rw [UpperTheory.SubRep.pull_pow hP _ pr hpr hτ k, hk _ (snd (Over.mk x) G), UpperTheory.SubRep.pull_one hP _ pr hpr]
  have hpow : ∀ n : ℕ, (τ ≫ f) ^ n = (τ ^ n) ≫ f := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
    | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]
  have hwk : (τ ≫ f) ^ k = 1 := by
    rw [hpow, hτk, MonObj.one_comp]
  obtain ⟨c, hc, -⟩ := GlobalTheory.LatticeTorsion.existsUnique_torsion B₁ k (τ ≫ f) hwk
  obtain ⟨c₀, hc₀, -⟩ := GlobalTheory.LatticeTorsion.existsUnique_torsion B₁ k (1 : Over.mk pr ⟶ B₁) (one_pow k)
  obtain ⟨V, hV, H⟩ := GlobalTheory.LevCover.clopenCond_eq c c₀
  refine ⟨V, hV, fun T' t a g hg => ?_⟩
  have hl : (lift t a).left ≫ pr = t.left := by
    change ((lift t a) ≫ fst (Over.mk x) G).left = t.left
    rw [lift_fst]
  let h : Over.mk t.left ⟶ Over.mk pr := Over.homMk (lift t a).left hl
  have hhτ : h ≫ τ = g := by
    apply UpperTheory.SubRep.pull_ext hP
    have e : (lift t a).left ≫ (snd (Over.mk x) G ≫ inc).left = a.left ≫ inc.left := by
      change (lift t a ≫ snd (Over.mk x) G ≫ inc).left = _
      rw [lift_snd_assoc]; rfl
    change (lift t a).left ≫ τ.left ≫ φ₁ = _
    rw [hτ, e, hg]
  have hgf : g ≫ f = h ≫ τ ≫ f := by rw [← hhτ, Category.assoc]
  have key : g ≫ f = 1 ↔ h ≫ c = h ≫ c₀ := by
    constructor
    · intro e
      have h1 : (h ≫ c) ≫ torsion.ι B₁ k = 1 := by
        rw [Category.assoc, hc, ← hgf, e]
      have h2 : (h ≫ c₀) ≫ torsion.ι B₁ k = 1 := by
        rw [Category.assoc, hc₀, MonObj.comp_one]
      exact (GlobalTheory.LatticeTorsion.existsUnique_torsion B₁ k (1 : Over.mk t.left ⟶ B₁) (one_pow k)).unique h1 h2
    · intro e
      rw [hgf, ← hc, ← Category.assoc, e, Category.assoc, hc₀, MonObj.comp_one]
  exact key.trans (H _ h)
