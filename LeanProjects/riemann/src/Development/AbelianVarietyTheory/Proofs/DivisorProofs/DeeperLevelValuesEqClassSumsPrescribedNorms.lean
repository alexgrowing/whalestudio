import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WtChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalLab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaWeightPartValueDependsTraitLabelsClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartLeastVectorNormLeExpStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartUniqueLeastVectorAttainsExpStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeClassSumsOfTermsPrescribedNormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartsOverDividingThetaConstantIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadNonnegOfInt
import Development.AbelianVarietyTheory.Definitions.Divisors.IdlAlongNeTopOfValOn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.GSumCls

theorem congMod_iff {X J : Type} [AddCommGroup X] (m : ℕ) (u v : J → X) :
    CongMod m u v ↔ ∀ i, CongMod m (u i) (v i) := by
  constructor
  · rintro ⟨w, hw⟩ i
    exact ⟨w i, by rw [hw]; rfl⟩
  · intro h
    choose w hw using h
    exact ⟨w, funext fun i => by rw [hw i]; rfl⟩

theorem norm_val_root_mul {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} (hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z)
    {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {z : M.Z} (hy : y (cPt p) = z) {u x : Ω} {k : ℕ} (hk : 0 < k)
    (hu : u ^ k = 1) (hx : x ∈ M.O z) : ‖M.val (gPt p ≫ y) (u * x)‖ = ‖M.val (gPt p ≫ y) x‖ := by
  haveI := RatModel.isIntegrallyClosed_O hM z
  have hint : IsIntegral (M.O z) u := ⟨_, Polynomial.monic_X_pow_sub_C (1 : M.O z) hk.ne', by simp [hu]⟩
  obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hmem : u ∈ M.O z := hv ▸ v.2
  have hs := RatModel.gPt_specializes hy
  have h1 : (⟨u, hmem⟩ : M.O z) ^ k = 1 := Subtype.ext hu
  have h2 : M.val (gPt p ≫ y) u ^ k = 1 := by
    have := congrArg (RatModel.valHomOf (gPt p ≫ y) z hs) h1
    rwa [map_pow, map_one] at this
  have h3 : ‖M.val (gPt p ≫ y) u‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').1 (by rw [← norm_pow, h2, norm_one])
  rw [RatModel.val_mul hs hmem hx, norm_mul, h3, one_mul]

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem onto_of_isLab {X : Setup F W i} {ε} {p : ℕ} [Fact p.Prime] {z : X.M.Z} {c : CTrait X p z} {yy}
    (h : IsLab X ε c yy) (ν : Fin 8 → c.T.D.toPre.X) : ∃ a, yy a = QuotientAddGroup.mk ν := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, -, -, y₀, -, u, l, j, -, hyy, -⟩ := h
  obtain ⟨a, ha⟩ := l.yy_onto (QuotientAddGroup.mk (j.symm ν))
  exact ⟨a, by simpa using hyy a _ ha⟩

theorem tendsto_of_isLab {X : Setup F W i} {ε} {p : ℕ} [Fact p.Prime] {z : X.M.Z} {c : CTrait X p z} {yy}
    (h : IsLab X ε c yy) :
    Filter.Tendsto (fun ν : Fin 8 → c.T.D.toPre.X => c.sc * (qW W c.T.β ν : ℤ)) Filter.cofinite Filter.atTop := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, -, -, y₀, -, u, l, j, hq, -⟩ := h
  refine (l.pos.comp j.symm.injective.tendsto_cofinite).congr fun ν => ?_
  rw [Function.comp_apply, hq, AddEquiv.apply_symm_apply]

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ U : X₁.S.HH X₁.M z₁ → D.X.Ω₁, (∀ κ, ∃ k : ℕ, 0 < k ∧ U κ ^ k = 1) ∧ ∀ (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∃ t : (Fin 8 → c.T.D.toPre.X) → X₁.S.HH X₁.M z₁ → PadicAlgCl p, (∀ μ κ, ‖t μ κ‖ ≤ Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ (∀ μ, ∃ κ, ‖t μ κ‖ = Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset (Fin 8 → c.T.D.toPre.X), ∀ S : Finset (Fin 8 → c.T.D.toPre.X), (∀ μ ∈ S, ∀ u, CongMod D.m (μ u) (ν u)) → (∀ μ ∈ S₀, (∀ u, CongMod D.m (μ u) (ν u)) → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (U κ * GSum.part D z₁ z₂ a κ) - ∑ μ ∈ S, t μ κ‖ ≤ δ := by
  intro g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D p _ z₁ z₂ hz
  obtain ⟨U, hU, hgeq⟩ := GlobalTheory.T.thetaWeightPart_value_depends_trait_labels_class g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D z₁ z₂ hz
  refine ⟨U, hU, fun c yy₁ hlab => ?_⟩
  have hs : ∀ χ : Fin 8 → c.T.D.toPre.X, ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)‖ ^ (qW W c.T.β χ).toNat =
      Real.exp (-(c.sc * (qW W c.T.β χ : ℤ))) := fun χ => by
    have h0 := qW_nonneg_of_posW W X₁.posW c.T.β c.T.symm (Basic₂.trait_nonneg c.T) χ
    rw [← c.exp_neg_sc_mul, ← Int.cast_natCast (R := ℝ), Int.toNat_of_nonneg h0]
  by_cases hex : ∃ y : Sp (OO p) ⟶ D.X.M.Z, y ≫ D.q = c.y ∧ y (cPt p) = z₂
  swap
  · refine ⟨fun μ _ => c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ) ^ (qW W c.T.β μ).toNat,
      fun μ _ => by rw [norm_pow, hs], fun μ => ⟨0, by rw [norm_pow, hs]⟩, fun y h hy => (hex ⟨y, h, hy⟩).elim⟩
  obtain ⟨y₀, h₀, hy₀⟩ := hex
  obtain ⟨yy₀, hlab₀, hcomp₀⟩ :=
    GLift.labels_lift g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D p z₁ c yy₁ hlab y₀ h₀
  choose a ha using onto_of_isLab hlab₀
  have hpart : ∀ b κ, GSum.part D z₁ z₂ b κ ∈ D.X.M.O z₂ := fun b κ => by
    rw [GSum.part, Finset.sum_div]
    refine sum_mem fun j _ => ?_
    rw [mul_div_assoc]
    exact mul_mem ((D.X.M.O z₂).algebraMap_mem _)
      (GlobalTheory.T.weightParts_over_dividing_thetaConstant_integral g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D z₁ _ j z₂ hz)
  have hnorm : ∀ b κ, ‖D.X.M.val (gPt p ≫ y₀) (U κ * GSum.part D z₁ z₂ b κ)‖ =
      ‖D.X.M.val (gPt p ≫ y₀) (GSum.part D z₁ z₂ b κ)‖ := fun b κ => by
    obtain ⟨k, hk, hu⟩ := hU κ
    exact norm_val_root_mul (haveI := D.X.normal; GlobalTheory.IsNormalScheme.pred _) hy₀ hk hu (hpart b κ)
  have hsc := c.scale_pos
  obtain ⟨t, ht1, ht2, ht3⟩ := GlobalTheory.T.lattice_class_sums_of_terms_prescribed_norms p (Fin 8 → c.T.D.toPre.X) (X₁.S.HH X₁.M z₁) D.m
    (fun ν => c.sc * (qW W c.T.β ν : ℤ)) _ _ (tendsto_of_isLab hlab) hs
    (fun ν κ => D.X.M.val (gPt p ≫ y₀) (U κ * GSum.part D z₁ z₂ (a ν) κ))
    (fun ν ν' κ h => hgeq p c yy₁ hlab y₀ h₀ hy₀ yy₀ hlab₀ hcomp₀ y₀ h₀ hy₀ yy₀ hlab₀ hcomp₀ _ _ ν ν' κ (ha ν) (ha ν') h)
    (fun ν κ h => by
      rw [hnorm]
      refine GlobalTheory.T.weightPart_least_vector_norm_le_exp g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D z₁ z₂ hz p c yy₁ hlab y₀ h₀ hy₀ yy₀
        hlab₀ hcomp₀ _ ν κ (ha ν) fun χ hχ => ?_
      exact_mod_cast le_of_mul_le_mul_left (h χ hχ) hsc)
    (fun ν h => by
      simp only [hnorm]
      refine GlobalTheory.T.weightPart_unique_least_vector_attains_exp g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D z₁ z₂ hz p c yy₁ hlab y₀ h₀ hy₀ yy₀
        hlab₀ hcomp₀ _ ν (ha ν) fun χ hχ hne => ?_
      exact_mod_cast lt_of_mul_lt_mul_left (h χ hχ hne) hsc.le)
  refine ⟨t, ht1, ht2, fun y h hy yy hl hc b ν κ hb δ hδ => ?_⟩
  obtain ⟨S₀, hS₀⟩ := ht3 ν κ δ hδ
  refine ⟨S₀, fun S h1 h2 => ?_⟩
  rw [hgeq p c yy₁ hlab y h hy yy hl hc y₀ h₀ hy₀ yy₀ hlab₀ hcomp₀ b (a ν) ν ν κ hb (ha ν) ⟨0, by simp⟩]
  exact hS₀ S (fun χ hχ => (congMod_iff _ _ _).2 (h1 χ hχ)) fun χ hχ hcg => h2 χ hχ ((congMod_iff _ _ _).1 hcg)

end GlobalTheory.Poinc.GSumCls
