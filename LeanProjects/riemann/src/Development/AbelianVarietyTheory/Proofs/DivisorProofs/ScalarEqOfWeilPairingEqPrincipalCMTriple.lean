import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PrincipalTriplePullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilEqIffHermFormEqComplex
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomFamilyOfPureTypeComplexTriple
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.TwistScalarUnique

def coordMul {E : Type} [Field E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) (s : E) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun z k := ty k s * z k
  map_add' z w := by funext k; simp [mul_add]
  map_smul' c z := by funext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem cmHost_sqrtNegDisc_re_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : H.rt0.re = 0 := by
  have h2 := congrArg Complex.re H.sqrt_neg_disc_sq
  have h3 := congrArg Complex.im H.sqrt_neg_disc_sq
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im] at h2 h3
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  by_contra hne
  have him : H.rt0.im = 0 := by
    have : H.rt0.re * H.rt0.im = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hne
  rw [him] at h2
  nlinarith [mul_self_nonneg H.rt0.re]

theorem exists_embedding {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    (∃ τ : E →+* ℂ, τ (H.rt : E) = H.rt0) ∧ ∃ τ : E →+* ℂ, τ (H.rt : E) ≠ H.rt0 := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := ⟨(IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom⟩
  have hre := cmHost_sqrtNegDisc_re_eq_zero H
  have hd : (H.d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  have hr0 : H.rt0 ≠ 0 := fun h0 => hd (by have := H.sqrt_neg_disc_sq; rw [h0] at this; linear_combination this)
  have hne : H.rt0 ≠ -H.rt0 := fun h => hr0 (by linear_combination h / 2)
  have hconj : starRingEnd ℂ H.rt0 = -H.rt0 := by apply Complex.ext <;> simp [hre]
  have h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    have := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
    rw [H.sqrt_neg_disc_sq]; simpa using this
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · refine ⟨⟨τ, h⟩, (starRingEnd ℂ).comp τ, ?_⟩
    show starRingEnd ℂ (τ (H.rt : E)) ≠ H.rt0
    rw [h, hconj]; exact fun e => hne e.symm
  · refine ⟨⟨(starRingEnd ℂ).comp τ, ?_⟩, τ, ?_⟩
    · show starRingEnd ℂ (τ (H.rt : E)) = H.rt0
      rw [h, map_neg, hconj, neg_neg]
    · rw [h]; exact fun e => hne e.symm

theorem nonempty_of_isTypeFn {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {p q g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (hty : IsTypeFn H p q ty) (hpq : p + q = 1) : Nonempty (Fin g) := by
  obtain ⟨⟨τ₁, h₁⟩, τ₂, h₂⟩ := exists_embedding H
  rcases Nat.add_eq_one_iff.1 hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h := (hty τ₂).2 h₂
    obtain ⟨⟨i, -⟩⟩ : Nonempty {i // ty i = τ₂} := (Nat.card_pos_iff.1 (by rw [h]; norm_num)).1
    exact ⟨i⟩
  · have h := (hty τ₁).1 h₁
    obtain ⟨⟨i, -⟩⟩ : Nonempty {i // ty i = τ₁} := (Nat.card_pos_iff.1 (by rw [h]; norm_num)).1
    exact ⟨i⟩

theorem eq_of_weilEq_complex {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (A : PAT H (Sp ℂ))
    {p q : ℕ} (hpq : p + q = 1)
    (hdet : ∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult A.t.act (𝟙 (Sp ℂ)) τ p) ∧
      (τ H.rt ≠ H.rt0 → LieMult A.t.act (𝟙 (Sp ℂ)) τ q)) (s s' : 𝓞 E)
    (h : WeilEq A.t.PP.L (A.t.act.act s) (𝟙 _) A.t.PP.L (A.t.act.act s') (𝟙 _) (𝟙 (Sp ℂ))) : s = s' := by
  have hT : ThetaUnifAV := thetaUnifAV_all
  have hL : Out.Laws := abelianSchemeLaws_all.1
  obtain ⟨g, ty, hty⟩ := AllClasses.exists_isTypeFn H p q
  obtain ⟨u, HA, χA, -, hA, -⟩ := PureType.exists_isThetaUnif hT A.pol
  obtain ⟨D, Pe, F, -, -, -, -, -, hact⟩ := PureTriple.exists_datum_period hT hL A hty hdet u hA
  let G : 𝓞 E → (Fin A.pol.g → ℂ) →ₗ[ℂ] (Fin A.pol.g → ℂ) := fun s =>
    F.toLinearMap ∘ₗ coordMul ty (s : E) ∘ₗ F.symm.toLinearMap
  have hG : ∀ s z, u.ex (G s z) = u.ex z ≫ A.t.act.act s := fun s z => by
    have e := hact s (F.symm z)
    rw [F.apply_symm_apply] at e
    exact e
  have key := (weilEq_iff_hermForm_eq hT hL A.pol A.pol A.pol A.pol u u u u HA HA χA χA hA hA
    (A.t.act.act s) (𝟙 _) (A.t.act.act s') (𝟙 _) (G s) LinearMap.id (G s') LinearMap.id (hG s)
    (fun _ => (Category.comp_id _).symm) (hG s') (fun _ => (Category.comp_id _).symm)).1 h
  have hGeq : ∀ z, G s z = G s' z := by
    intro z
    by_contra hne
    have hpos := hA.2.1 (G s z - G s' z) (sub_ne_zero.2 hne)
    have e := key z (G s z - G s' z)
    simp only [hermForm, LinearMap.id_apply] at e
    rw [sub_dotProduct, e, sub_self] at hpos
    simp at hpos
  obtain ⟨k⟩ := nonempty_of_isTypeFn H hty hpq
  have e1 := hGeq (F fun _ => 1)
  simp only [G, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at e1
  have e2 := congrFun (F.injective e1) k
  have e3 : ty k (s : E) = ty k (s' : E) := by simpa [coordMul] using e2
  exact RingOfIntegers.ext ((ty k).injective e3)

theorem eq_of_weilEq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (A : PAT H (Sp (𝓞 K))), ρ ^ 2 = -(H.d : 𝓞 K) →
    HasType H A.t.act ρ 1 0 → ∀ s s' : 𝓞 E,
    WeilEq A.t.PP.L (A.t.act.act s) (𝟙 _) A.t.PP.L (A.t.act.act s') (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    s = s' := by
  intro E _ _ _ H K _ _ ρ σ₁ A hρ hA s s' h
  have hβi : Function.Injective (σ₁.comp (algebraMap (𝓞 K) K)) :=
    σ₁.injective.comp (IsFractionRing.injective (𝓞 K) K)
  obtain ⟨⟨A', mA, -⟩, hA2⟩ := GlobalTheory.LamT.pat_pullback E H (𝓞 K) ℂ (σ₁.comp (algebraMap (𝓞 K) K)) A
  obtain ⟨-, -, wA, hwA⟩ := hA2 A' mA inferInstance
  have hlie : ∀ (τ : 𝓞 E →+* ℂ) (n : ℕ), LieMult A'.t.act (𝟙 (Sp ℂ)) τ n ↔
      LieMult A.t.act (spMap (σ₁.comp (algebraMap (𝓞 K) K))) τ n := fun τ n => by
    have := GlobalTheory.lieMult_iff_of_isGrpPullback mA.cart A'.t.act A.t.act mA.act (𝟙 (Sp ℂ)) τ n
    rwa [Category.id_comp] at this
  have hweil : WeilEq A'.t.PP.L (A'.t.act.act s) (𝟙 _) A'.t.PP.L (A'.t.act.act s') (𝟙 _) (𝟙 (Sp ℂ)) := by
    refine (GlobalTheory.PairingFibre.weilEq_iff (f₂ := 𝟙 _) (g₂ := 𝟙 _) (f₂' := 𝟙 _) (g₂' := 𝟙 _) mA.cart mA.cart
      mA.cart mA.cart A.t.PP.isLB A.t.PP.isLB A'.t.PP.isLB A'.t.PP.isLB ⟨wA, hwA.1⟩ ⟨wA, hwA.1⟩ (mA.act s)
      (by simp) (mA.act s') (by simp) (𝟙 (Sp ℂ))).2 ?_
    rwa [Category.id_comp]
  have hT := hA ℂ (σ₁.comp (algebraMap (𝓞 K) K)) hβi
  have hd0 : (H.d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  have hr0 : H.rt0 ≠ 0 := fun h0 => hd0 (by have := H.sqrt_neg_disc_sq; rw [h0] at this; linear_combination this)
  have hsq : ∀ x : ℂ, x ^ 2 = -(H.d : ℂ) → x = H.rt0 ∨ x = -H.rt0 := fun x hx =>
    sq_eq_sq_iff_eq_or_eq_neg.1 (hx.trans H.sqrt_neg_disc_sq.symm)
  have hβρ : (σ₁.comp (algebraMap (𝓞 K) K)) ρ ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, hρ]; simp
  have hτ : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ^ 2 = -(H.d : ℂ) := fun τ => by
    rw [← map_pow, H.rt_sq]; simp
  have hne : H.rt0 ≠ -H.rt0 := fun h => hr0 (by linear_combination h / 2)
  rcases hsq _ hβρ with hc | hc
  · refine eq_of_weilEq_complex H A' (p := 1) (q := 0) rfl (fun τ => ⟨fun ht => ?_, fun ht => ?_⟩) s s' hweil
    · exact (hlie τ 1).2 ((hT τ).1 (ht.trans hc.symm))
    · exact (hlie τ 0).2 ((hT τ).2 (fun h => ht (h.trans hc)))
  · refine eq_of_weilEq_complex H A' (p := 0) (q := 1) rfl (fun τ => ⟨fun ht => ?_, fun ht => ?_⟩) s s' hweil
    · exact (hlie τ 0).2 ((hT τ).2 (fun h => hne (ht.symm.trans (h.trans hc))))
    · rcases hsq _ (hτ τ) with h | h
      · exact absurd h ht
      · exact (hlie τ 1).2 ((hT τ).1 (h.trans hc.symm))

end GlobalTheory.TwistScalarUnique
end
