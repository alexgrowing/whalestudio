import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormBoundGoodPointsExtendsAllPoints
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupSetFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SubsingletonOfScalar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SectionIntegralEqualCharAbelianLocusStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralArcSectionEqualCharStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexEmbeddingFractionFieldFiniteOverCdvStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqCharCusp

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts GlobalTheory.GoodTransfer

theorem exists_goodAt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    ∃ p : ℕ, p.Prime ∧ l.GoodAt p := by
  obtain ⟨p, hle, hp⟩ := Nat.exists_infinite_primes (l.M + 1)
  refine ⟨p, hp, ?_⟩
  have h3 := l.three_le
  have hM : ¬ p ∣ l.M := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  unfold Level.GoodAt
  rw [Nat.factorization_eq_zero_of_not_dvd hM]
  simpa using h3

theorem exists_place (K : Type) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    ∃ la : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ la.asIdeal := by
  have hP : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.mp hp)
  obtain ⟨Q, -, hQ, hQl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K) (Ideal.span {(p : ℤ)}) ⊥
    (by rw [Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 K)).injective_int]; exact bot_le)
  have hpQ : (p : 𝓞 K) ∈ Q := by
    have : ((p : ℤ)) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := hQl ▸ Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ, fun h => ?_⟩, hpQ⟩
  rw [h, Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 K)).injective_int] at hQl
  have : ((p : ℤ)) ∈ (⊥ : Ideal ℤ) := hQl ▸ Ideal.mem_span_singleton_self _
  exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 this))

theorem integral_of_eqChar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a n → f ∈ cusp Xo c U a n → ∀ (T : CDVR), Countable (IsLocalRing.ResidueField T.V) → ∀ (io : c.F →+* T.Fr), (∀ k : c.F, io k ∈ (algebraMap T.V T.Fr).range) → ∀ y : IntFr Xo c T io, evI y f ∈ (algebraMap T.V T.Fr).range := by
  intro E _ _ _ H Dw l Xo c r U hU a n f hd hf T hcnt io hint y
  obtain ⟨p, hp, hg⟩ := exists_goodAt l
  obtain ⟨la, hpl⟩ := exists_place c.F p hp
  let _ := io.toAlgebra
  obtain ⟨b, hb⟩ := exists_factor T (io.comp (la.valuation c.F).valuationSubring.subtype) (fun x => hint _)
  let z : Sp T.Fr ⟶ Xo.XF c := pullback.lift y.1.x (spMap io) (y.1.x_over.trans (sp_comp _ _).symm)
  have hz₁ : z ≫ pullback.fst _ _ = y.1.x := pullback.lift_fst _ _ _
  have hz₂ : z ≫ pullback.snd _ _ = spMap io := pullback.lift_snd _ _ _
  have hA : ∀ Y : Model Xo c (la.valuation c.F).valuationSubring.subtype, PushInvertible Y.t.G Y.t.PP.L →
      ∀ y' : Sp T.V ⟶ Y.X, z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y' → Set.range y' ⊆ abLocus Y.t.G →
      evI y f ∈ (algebraMap T.V T.Fr).range := fun Y hP y' h3 hr =>
    GlobalTheory.T.section_integral_equalChar_abelianLocus E H Dw l Xo c a n f hf.1 la Y hP T io hint y ⟨y', z, hz₁, hz₂, h3, hr⟩
  rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with hD | hD
  · obtain ⟨Y, hP⟩ := GlobalTheory.SupFinite.exists_model_rank_zero Xo c hD (la.valuation c.F).valuationSubring.subtype
    obtain ⟨⟨y', ⟨-, hz₃⟩, -⟩, -⟩ :=
      GlobalTheory.ValuativeExtension.valuation_extension E H Dw l Xo c _ _ Y T.V T.Fr b io z hb hz₂
    refine hA Y hP y' hz₃.symm ?_
    rw [GlobalTheory.DefiniteAbelian.abLocus_eq_univ (by omega) _ Y]
    exact Set.subset_univ _
  obtain ⟨Y, hP, hop, hS, h3, h4⟩ := exists_model (by omega) Xo c la p hp hpl hg
  obtain ⟨⟨y', ⟨hy', hz₃⟩, -⟩, -⟩ :=
    GlobalTheory.ValuativeExtension.valuation_extension E H Dw l Xo c _ _ Y T.V T.Fr b io z hb hz₂
  by_cases hr : Set.range y' ⊆ abLocus Y.t.G
  · exact hA Y hP y' hz₃.symm hr
  obtain ⟨T', g, ϖ, a₀, hg₁, hg₂, hϖ, hA'⟩ := GlobalTheory.T.exists_arcData_of_badReduction_finiteExtension E H Dw l Xo c _ Y h3 hS T io b y' z hb hy' hz₂ hz₃.symm hr
  obtain ⟨i, ρ, hρ, hi, hv, -⟩ := GlobalTheory.EtaVal.finite_extension_ramification_embedding T T' g hg₁ hg₂
  obtain ⟨y₁, φ, hφ, hy₁⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange E H Dw l Xo c T T' io y i ρ hρ
    (fun x _ => hv x)
  let _ := (i.comp io).toAlgebra
  have e₁ : (algebraMap T'.V T'.Fr).comp g = i.comp (algebraMap T.V T.Fr) := RingHom.ext fun x => (hi x).symm
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_complex_embedding_fractionField_finite_over_cdvr c.F c.F.val.toRingHom T T' g hg₁ hg₂ hcnt (i.comp io)
  have hint' : ∀ k : c.F, (i.comp io) k ∈ (algebraMap T'.V T'.Fr).range := fun k => by
    obtain ⟨v, hv'⟩ := hint k
    exact ⟨g v, by rw [RingHom.comp_apply, ← hv', hi]⟩
  have key := GlobalTheory.T.cuspForm_integral_arc_section_equalChar E H Dw l Xo c r U hU la Y hP hop h4 a n f hd hf
    (fun T₁ io₁ h₁ y₂ hy₂ => GlobalTheory.T.section_integral_equalChar_abelianLocus E H Dw l Xo c a n f hf.1 la Y hP T₁ io₁ h₁ y₂ hy₂)
    T' (i.comp io) hint' ⟨κ, hκ⟩ (g.comp b)
    (by rw [← RingHom.comp_assoc, e₁, RingHom.comp_assoc, hb]; rfl) ϖ hϖ a₀ (spMap g ≫ y')
    (by rw [Category.assoc, hy', sp_comp]) hA' y₁ (spMap i ≫ z)
    (by rw [Category.assoc, hz₁, hy₁.1, hφ]) (by rw [Category.assoc, hz₂, sp_comp])
    (by rw [Category.assoc, ← hz₃, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp, e₁])
  obtain ⟨hE, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have e₂ : evI y₁ f = φ (evI y f) :=
    (GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hE a n f hf.1 T.Fr).1 _ φ _ _ hy₁
  have e₃ : φ (evI y f) = i (evI y f) := RingHom.congr_fun hφ _
  have key' : InV T' (i (evI y f)) := by rw [← e₃, ← e₂]; exact key
  rw [inV_iff, hv] at key'
  show InV T (evI y f)
  rw [inV_iff]
  exact nonneg_of_mul_nonneg_right key' (by exact_mod_cast hρ)

end GlobalTheory.EqCharCusp
