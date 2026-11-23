import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsFinExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.AllEmb

open GlobalTheory.LabTrans GlobalTheory.ArcPull GlobalTheory.TorusExt GlobalTheory.ArcExt ReciprocityTheory.ChartRestriction.G.DVR

theorem lab_indep_level {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} (hB : D.TauBimult) {A : PolAV (Sp (FractionRing R))} {lab : Labels D A}
    (hlab : ∀ (σ : Kb R →ₐ[FractionRing R] Kb R) (p p' : QkPt D (Kb R) k), QkExt σ.toRingHom p p' →
      (lab k p').left = spMap σ.toRingHom ≫ (lab k p).left)
    (τ₁ τ₂ : Kb R →ₐ[FractionRing R] F) {p q : QkPt D (Kb R) k} {r : QkPt D F k}
    (h₁ : QkExt τ₁.toRingHom p r) (h₂ : QkExt τ₂.toRingHom q r) :
    spMap τ₁.toRingHom ≫ (lab k p).left = spMap τ₂.toRingHom ≫ (lab k q).left := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Kb R →ₐ[FractionRing R] Kb R, τ₂.toRingHom.comp σ.toRingHom = τ₁.toRingHom := by
    letI : Algebra (Kb R) F := τ₂.toRingHom.toAlgebra
    haveI : IsScalarTower (FractionRing R) (Kb R) F := IsScalarTower.of_algebraMap_eq fun x => (τ₂.commutes x).symm
    exact ⟨τ₁.restrictNormal (Kb R), RingHom.ext fun x => τ₁.restrictNormal_commutes (Kb R) x⟩
  obtain ⟨q', hq'⟩ := exists_ext hB σ p
  obtain ⟨r', hr'⟩ := exists_ext hB τ₂ q'
  have h₃ := qkExt_trans hq' hr'
  rw [hσ] at h₃
  obtain rfl := ext_unique hB τ₁ h₁ h₃
  obtain rfl := qkExt_inj hB τ₂ h₂ hr'
  rw [hlab σ p q hq', ← Category.assoc, ← Geo.Tor.spMap_comp, hσ]

theorem induces_of_one_embedding : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → GalEqN n lab → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (a : A'.A.left ⟶ A.A.left), IsSemiAbelian G' → IsFib φ A A' a → ∀ (hD : IsPullDeg φ D.toPre D'.toPre) (j : ℕ), (∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing W) C) (_ : Algebra (FractionRing R) C) (em : Kb R →ₐ[FractionRing R] C), (∀ r, algebraMap (FractionRing R) C (algebraMap R _ r) = algebraMap (FractionRing W) C (algebraMap W _ (φ r))) ∧  ∀ (p : QkPt D.toPre (Kb R) (n ^ j)) (p₁ : QkPt D.toPre C (n ^ j)) (p' : QkPt D'.toPre C (n ^ j)) (x' : TFK (R := W) C ⟶ A'.A), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD C p₁.g p'.g → x'.left ≫ a = spMap em.toRingHom ≫ (lab (n ^ j) p).left → QkToAkU U'.toUnifPre C (n ^ j) p' x') → Induces lab φ U' hD a (n ^ j) := by
  intro R _ _ _ hR D A lab n hn _ _ hlab W _ _ _ hW φ iφ _ G' _ _ D' A' U' a hG ⟨ga, hga, gpa, _⟩ hD j
    ⟨C, _, _, _, _, emC, cC, HC⟩ F _ _ _ _ em cF p p₁ p' x' y₁ y₂ y₃ y₄
  have hGF := GlobalTheory.firstFiveLaws.1.globalFns
  have := hR.2
  have := hW.1
  have := hW.2.2
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  have hk : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn.pos
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  letI : Algebra (FractionRing R) (Kb W) := ((algebraMap (FractionRing W) (Kb W)).comp ga).toAlgebra
  have cK : Compat φ (Kb W) := fun r => congrArg (algebraMap (FractionRing W) (Kb W)) (hga r)
  obtain ⟨e⟩ := nonempty_lift (FractionRing R) (Kb W)

  have fac : ∀ (L : Type) [Field L] [Algebra (FractionRing W) L] [Algebra (FractionRing R) L], Compat φ L →
      algebraMap (FractionRing R) L = (algebraMap (FractionRing W) L).comp ga := fun L _ _ _ c =>
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => (c r).trans
      (congrArg (algebraMap (FractionRing W) L) (hga r).symm))
  have up : ∀ (L : Type) [Field L] [Algebra (FractionRing W) L] [Algebra (FractionRing R) L], Compat φ L →
      ∀ i : Kb W →ₐ[FractionRing W] L, ∃ i' : Kb W →ₐ[FractionRing R] L, i'.toRingHom = i.toRingHom := fun L _ _ _ c i =>
    ⟨⟨i.toRingHom, fun t => by rw [fac L c]; exact i.commutes (ga t)⟩, rfl⟩

  have key : ∀ (L : Type) [Field L] [IsAlgClosed L] [Algebra (FractionRing W) L] [Algebra (FractionRing R) L],
      Compat φ L → ∀ (i : Kb W →ₐ[FractionRing W] L) (m : Kb R →ₐ[FractionRing R] L)
      (q : QkPt D.toPre (Kb R) (n ^ j)) (q₁ : QkPt D.toPre (Kb W) (n ^ j)) (x₀ : TFK (R := W) (Kb W) ⟶ A'.A),
      QkExt e.toRingHom q q₁ → x₀.left ≫ a = spMap e.toRingHom ≫ (lab (n ^ j) q).left →
      ∀ (s : QkPt D.toPre (Kb R) (n ^ j)) (s₁ : QkPt D.toPre L (n ^ j)) (s' : QkPt D'.toPre L (n ^ j))
        (z : TFK (R := W) L ⟶ A'.A), QkExt i.toRingHom q₁ s₁ → QkExt m.toRingHom s s₁ → s'.y = hD.xe.symm s₁.y →
        IsPullGtF φ hD L s₁.g s'.g → z.left ≫ a = spMap m.toRingHom ≫ (lab (n ^ j) s).left →
        (QkToAkU U'.toUnifPre (Kb W) (n ^ j) (pullQk hD hGF cK hB hB' q₁) x₀ ↔ QkToAkU U'.toUnifPre L (n ^ j) s' z) := by
    intro L _ _ _ _ c i m q q₁ x₀ hq hx₀ s s₁ s' z w₀ w₁ w₂ w₃ w₄
    obtain ⟨i', hi'⟩ := up L c i
    obtain ⟨⟨t, ht⟩, -, hgal⟩ := GlobalTheory.UT.Cl.galois_holds W _ bW D' A' G' hG U' _ L i (n ^ j) hk
      (pullQk hD hGF cK hB hB' q₁)
    have t₁ : IsPullGtF φ hD L s₁.g t.g :=
      isPullGtF_ext hD c i.toRingHom i.comp_algebraMap (isPullGtF_pullGt hD hGF cK _) w₀ ht
    have t₂ : t.y = hD.xe.symm s₁.y := by rw [ht.1, w₀.1]; rfl
    obtain rfl : s' = t := ((eq_pullQk_iff hD hGF c hB hB' _ _).2 ⟨w₂, w₃⟩).trans
      ((eq_pullQk_iff hD hGF c hB hB' _ _).2 ⟨t₂, t₁⟩).symm
    have u : QkExt (i'.comp e).toRingHom q s₁ := by
      have := qkExt_trans hq w₀
      rw [← hi'] at this
      exact this
    have l := lab_indep_level hB (fun σ => hlab σ j) m (i'.comp e) w₁ u
    refine hgal s' x₀ z ht ?_
    apply gpa.1.hom_ext
    · rw [w₄, Category.assoc, hx₀, ← Category.assoc, ← Geo.Tor.spMap_comp, l, ← hi']
      rfl
    · rw [Category.assoc, Over.w z, Over.w x₀]
      exact ((Geo.Tor.spMap_comp _ _).symm.trans (congrArg spMap i.comp_algebraMap)).symm
  obtain ⟨i⟩ := nonempty_lift (FractionRing W) F
  obtain ⟨i₀⟩ := nonempty_lift (FractionRing W) C
  obtain ⟨i', hi'⟩ := up F cF i
  obtain ⟨i₀', hi₀'⟩ := up C cC i₀
  obtain ⟨q₁, hq₁⟩ := exists_of_ext hB i' hk p₁
  obtain ⟨q, hq⟩ := exists_of_ext hB e hk q₁
  obtain ⟨x₀, hx₀⟩ := exists_lift_pt gpa.1 e.toRingHom e.comp_algebraMap (lab (n ^ j) q)
  obtain ⟨r₁, hr₁⟩ := exists_ext hB i₀' q₁
  obtain ⟨r, hr⟩ := exists_of_ext hB emC hk r₁
  obtain ⟨z, hz⟩ := exists_lift_pt gpa.1 emC.toRingHom (emC.comp_algebraMap.trans (fac C cC)) (lab (n ^ j) r)
  have hC := HC r r₁ (pullQk hD hGF cC hB hB' r₁) z hr rfl (isPullGtF_pullGt hD hGF cC _) hz
  exact (key F cF i em q q₁ x₀ hq hx₀ p p₁ p' x' (hi' ▸ hq₁) y₁ y₂ y₃ y₄).1
    ((key C cC i₀ emC q q₁ x₀ hq hx₀ r r₁ _ z (hi₀' ▸ hr₁) hr rfl (isPullGtF_pullGt hD hGF cC _) hz).2 hC)

end GlobalTheory.Mum.AllEmb
