import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAlgFamilyIff
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPicardGroup
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LbIsoCubeLBMulRightOf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CMSpreadCompare

open GlobalTheory.PureType GlobalTheory.IndefiniteRowSideFullHecke.CMUniformizationSpread

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Unif

theorem exists_pointEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') {s : T.left ⟶ S} (hs : s = T.hom ≫ f) :
    ∃ p : (T ⟶ G') ≃* (Over.mk s ⟶ G), ∀ x, (p x).left = x.left ≫ φ := by
  subst hs
  exact ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun _ _ e => eq_of_comp_eq h.1 (congrArg (fun z => z.left) e), fun p =>
    ⟨Over.homMk (h.1.lift p.left T.hom (Over.w p)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩⟩, fun _ => rfl⟩

theorem isHolTo_precomp {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    {X : Scheme.{0}} {y : W → (Sp ℂ ⟶ X)} (h : IsHolTo Set.univ y) {f : V → W} (hf : Differentiable ℂ f) :
    IsHolTo Set.univ (fun v => y (f v)) := fun U s =>
  ⟨(h U s).1.preimage hf.continuous, (h U s).2.comp hf.differentiableOn fun _ hv => hv⟩

theorem isHolTo_postcomp {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X Y : Scheme.{0}} {B : Set V}
    {y : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (φ : X ⟶ Y) : IsHolTo B (fun b => y b ≫ φ) := by
  intro U s
  rw [show (fun b => valAt' (y b ≫ φ) U s) = fun b => valAt' (y b) (φ ⁻¹ᵁ U) ((φ.app U).hom s) from
    funext fun b => (valAt'_comp _ φ U s).symm]
  exact h (φ ⁻¹ᵁ U) _

theorem exists_const {g : ℕ} (hg : g = 1) {c : ℂ} (hc : c ≠ 0) (x : Fin g → ℂ) : ∃ z, x = fun _ => c * z := by
  subst hg
  exact ⟨c⁻¹ * x 0, funext fun i => by rw [mul_inv_cancel_left₀ hc, Subsingleton.elim i 0]⟩

variable {k : Type} [Field k] {κ : k →+* ℂ} {A : Over (Sp k)} [GrpObj A] {PC : Out.PolAV (Sp ℂ)}
  {ψ : PC.A.left ⟶ A.left} (hψ : IsGrpPullback PC.A A (spMap κ) ψ) (u : HolUnif PC.A PC.L PC.g)

include hψ

theorem exists_param (c : ℂ) :
    ∃ e : ℂ → (Over.mk (spMap κ) ⟶ A), ∀ z, (e z).left = (u.ex fun _ => c * z).left ≫ ψ := by
  obtain ⟨p, hp⟩ := exists_pointEquiv hψ (𝟙_ _) (s := spMap κ) (Category.id_comp _).symm
  exact ⟨fun z => p (u.ex fun _ => c * z), fun z => hp _⟩

theorem exists_scalar (hg : PC.g = 1) (hu : IsThetaUnif u) {e : ℂ → (Over.mk (spMap κ) ⟶ A)}
    (he : IsCMUnif H κ A e) : ∃ c : ℂ, c ≠ 0 ∧ ∀ z, (e z).left = (u.ex fun _ => c * z).left ≫ ψ := by
  obtain ⟨p, hp⟩ := exists_pointEquiv hψ (𝟙_ _) (s := spMap κ) (Category.id_comp _).symm
  obtain ⟨_, _, _, -, h₁, h₂, -⟩ := hu
  have hp' : ∀ z, (p.symm (e z)).left ≫ ψ = (e z).left := fun z => by rw [← hp, p.apply_symm_apply]
  obtain ⟨F, hF, -⟩ := existsUnique_linear_lift_of_isHolTo PC.A PC.isAb PC.L PC.g 1 u h₁ h₂
    (fun z => p.symm (e (z 0))) (fun z w => by rw [← map_mul, ← he.1]; rfl)
    (FibreUnif.isHolTo_of_isPullback hψ.1 (fun z => Over.w (p.symm (e (z 0)))) (by
      simp only [hp']
      exact isHolTo_precomp he.2.2.2 (f := fun z : Fin 1 → ℂ => z 0) (by fun_prop)))
  have hc : ∀ z, (e z).left = (u.ex fun _ => F (fun _ => 1) ⟨0, by omega⟩ * z).left ≫ ψ := fun z => by
    have e₁ : (fun _ => F (fun _ => 1) ⟨0, by omega⟩ * z) = F fun _ => z := by
      funext i
      rw [show (fun _ => z : Fin 1 → ℂ) = z • fun _ => 1 from funext fun _ => by simp, map_smul,
        show i = ⟨0, by omega⟩ from Fin.ext (by omega), Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [e₁, hF, hp']
  refine ⟨_, fun h0 => ?_, hc⟩
  have h1 : ∀ z, e z = 1 := fun z => by
    have : e z = e 0 := Over.OverMorphism.ext (by simp only [hc, h0, zero_mul])
    rw [this]
    exact (he.2.2.1 0).2 ⟨0, 0, by simp⟩
  refine not_countable_complex ((Set.countable_range fun x : ℤ × ℤ => (x.1 : ℂ) + x.2 * omegaC H).mono fun z _ => ?_)
  obtain ⟨m, n, h⟩ := (he.2.2.1 z).1 (h1 z)
  exact ⟨(m, n), h.symm⟩

end Unif

section Quadratic

theorem exists_sign {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ty P) (ρ : ℂ) :
    ∃ s : ℤ, ∀ a ∈ lat hP ρ, ((D.EF (H.w0 • a) a).natAbs : ℤ) = s * D.EF (H.w0 • a) a := by
  obtain ⟨Hm, -, hpos, hE⟩ := hP.2.2.2.2
  have key : ∀ a ∈ lat hP ρ, ∃ r : ℝ, 0 ≤ r ∧ (D.EF (H.w0 • a) a : ℝ) = ρ.im * r := fun a ha => by
    have h1 := hE (H.w0 • a) a
    have h2 := hE a a
    rw [D.alt, Int.cast_zero] at h2
    have h0 : 0 ≤ (hermForm Hm (P a) (P a)).re := by
      by_cases hz : P a = 0
      · simp [hz, hermForm]
      · exact (hpos _ hz).le
    have h3 : hermForm Hm (P (H.w0 • a)) (P a) = ((1 + ρ) / 2) * hermForm Hm (P a) (P a) := by
      rw [period_w0_smul hP ha, hermForm, hermForm, smul_dotProduct, smul_eq_mul]
    rw [h3, Complex.mul_im, h2] at h1
    exact ⟨(hermForm Hm (P a) (P a)).re / 2, by positivity, by rw [← h1]; simp; ring⟩
  rcases le_total 0 ρ.im with h | h
  · refine ⟨1, fun a ha => ?_⟩
    obtain ⟨r, hr, e⟩ := key a ha
    have : (0 : ℝ) ≤ D.EF (H.w0 • a) a := e ▸ mul_nonneg h hr
    rw [_root_.one_mul, Int.natAbs_of_nonneg (by exact_mod_cast this)]
  · refine ⟨-1, fun a ha => ?_⟩
    obtain ⟨r, hr, e⟩ := key a ha
    have : (D.EF (H.w0 • a) a : ℝ) ≤ 0 := e ▸ mul_nonpos_of_nonpos_of_nonneg h hr
    rw [neg_one_mul, Int.ofNat_natAbs_of_nonpos (by exact_mod_cast this)]

end Quadratic

section Transport

variable {D : Datum H} {R : Type} [CommRing R] {t : SAB H (Sp R)} {B B' : Over (Sp R)} [GrpObj B] [GrpObj B']
  {M : LB B.left} {M' : LB B'.left} {L : Submodule (𝓞 E) D.La} {ρ : R} {S S' : Set L} {φ : L → (B ⟶ t.G)}

theorem exists_generators (L : Submodule (𝓞 E) D.La) : ∃ T : Set L, T.Finite ∧ AddSubgroup.closure T = ⊤ := by
  have := D.fin
  have : IsNoetherian (𝓞 E) D.La := isNoetherian_of_isNoetherianRing_of_finite _ _
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  obtain ⟨T, h₁, h₂⟩ := (AddSubgroup.fg_iff _).1 (Module.Finite.iff_addGroup_fg.1 this).out
  exact ⟨T, h₂, h₁⟩

end Transport

section Multiplication

theorem cmHost_bar_halfIntegerGenerator (H : Host E) : H.bar H.w0 = 1 - H.w0 := by
  have h0 : H.rt ≠ 0 := fun h => by
    have e := H.rt_sq
    rw [h, zero_pow two_ne_zero, zero_eq_neg, Nat.cast_eq_zero] at e
    exact H.d_prime.pos.ne' e
  have h1 : H.bar H.rt = -H.rt := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have e : τ (H.bar H.rt : 𝓞 E) = starRingEnd ℂ (τ (H.rt : E)) := by
      rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
    have e' : starRingEnd ℂ H.rt0 = -H.rt0 := by
      have hs : H.rt0 ^ 2 = (Complex.I * Real.sqrt H.d) ^ 2 := by
        rw [H.sqrt_neg_disc_sq, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
        simp
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hs with h | h <;> rw [h] <;> simp
    refine RingOfIntegers.coe_injective (τ.injective ?_)
    refine e.trans ?_
    rw [map_neg, map_neg]
    change _ = -τ (H.rt : E)
    rcases map_rt H τ with h | h <;> rw [h] <;> simp [e']
  apply mul_left_cancel₀ (two_ne_zero : (2 : 𝓞 E) ≠ 0)
  have := congrArg H.bar H.two_weight_eq_one_add_root
  rw [map_mul, map_add, map_one, h1, map_ofNat] at this
  linear_combination this + H.two_weight_eq_one_add_root

end Multiplication

end GlobalTheory.CMSpreadCompare
