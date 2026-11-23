import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FracGen
open scoped nonZeroDivisors

theorem natCast_not_isUnit (F : Type) [Field F] [NumberField F] (l : ℕ) (hl : l.Prime) :
    ¬ IsUnit ((l : ℤ) : 𝓞 F) := by
  intro h
  have h2 := h.map (Algebra.norm ℤ (S := 𝓞 F))
  have h3 : Algebra.norm ℤ (((l : ℤ) : 𝓞 F)) = (l : ℤ) ^ Module.finrank ℤ (𝓞 F) := by
    rw [← Algebra.norm_algebraMap]; rfl
  rw [h3] at h2
  have hpos : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
  have h4 : IsUnit (l : ℤ) := (isUnit_pow_iff hpos.ne').1 h2
  rw [Int.isUnit_iff] at h4
  have := hl.two_le
  omega

theorem coprime_absNorm (F : Type) [Field F] [NumberField F] (l : ℕ) (hl : l.Prime)
    (K : Ideal (𝓞 F)) (hK : K ≠ ⊥) (hsup : Ideal.span {((l : ℕ) : 𝓞 F)} ⊔ K = ⊤) :
    (Ideal.absNorm K).Coprime l := by
  haveI : Fact l.Prime := ⟨hl⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hl]
  intro hd
  haveI : Finite (𝓞 F ⧸ K) := Ideal.finiteQuotientOfFreeOfNeBot K hK
  have hcard : Ideal.absNorm K = Nat.card (𝓞 F ⧸ K) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hcard] at hd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 F ⧸ K) l hd
  have h1 : (1 : 𝓞 F) ∈ Ideal.span {((l : ℕ) : 𝓞 F)} ⊔ K := hsup ▸ Submodule.mem_top
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  have hz0 : Ideal.Quotient.mk K z = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hz
  have hu : (l : 𝓞 F ⧸ K) * Ideal.Quotient.mk K w = 1 := by
    have := congrArg (Ideal.Quotient.mk K) hyz
    rw [map_add, hz0, add_zero, map_one, map_mul, map_natCast] at this
    rw [mul_comm]; exact this
  have hlx : l • x = 0 := hx ▸ addOrderOf_nsmul_eq_zero x
  have hx0 : x = 0 := by
    rw [nsmul_eq_mul] at hlx
    calc x = ((l : 𝓞 F ⧸ K) * Ideal.Quotient.mk K w) * x := by rw [hu, _root_.one_mul]
      _ = Ideal.Quotient.mk K w * ((l : 𝓞 F ⧸ K) * x) := by ring
      _ = 0 := by rw [hlx, mul_zero]
  rw [hx0, addOrderOf_zero] at hx
  exact hl.one_lt.ne hx

theorem exists_gen_int (F : Type) [Field F] [NumberField F] (l : ℕ) (hl : l.Prime)
    (J : Ideal (𝓞 F)) (hJ : J ≠ ⊥) :
    ∃ j₀ ∈ J, j₀ ≠ 0 ∧ ∃ n : ℕ, n.Coprime l ∧ ∀ j ∈ J, ∃ t : 𝓞 F, (n : 𝓞 F) * j = t * j₀ := by
  set L : Ideal (𝓞 F) := Ideal.span {((l : ℕ) : 𝓞 F)} with hLdef
  have hl0 : ((l : ℕ) : 𝓞 F) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hL0 : L ≠ ⊥ := by rw [hLdef, Ne, Ideal.span_singleton_eq_bot]; exact hl0
  have hLtop : L ≠ ⊤ := by
    rw [hLdef, Ne, Ideal.span_singleton_eq_top]
    have := natCast_not_isUnit F l hl
    simpa using this
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq (I := J * L) (J := J) Ideal.mul_le_left
    (mul_ne_zero hJ hL0)
  have haJ : a ∈ J := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  have hdvd : J ∣ Ideal.span {a} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem J).2 haJ)
  obtain ⟨K, hK⟩ := hdvd
  have hLK : L ⊔ K = ⊤ := by
    have : J * (L ⊔ K) = J * ⊤ := by rw [Ideal.mul_sup, ← hK, ha, Ideal.mul_top]
    exact mul_left_cancel₀ hJ this
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, Ideal.span_singleton_eq_bot.2 rfl] at hK
    have hK0 : K = ⊥ := by
      rcases mul_eq_zero.1 hK.symm with h | h
      · exact absurd h hJ
      · exact h
    rw [hK0, sup_bot_eq] at hLK
    exact hLtop hLK
  have hK0 : K ≠ ⊥ := by
    intro h; rw [h, Ideal.mul_bot] at hK
    exact ha0 (Ideal.span_singleton_eq_bot.1 hK)
  refine ⟨a, haJ, ha0, Ideal.absNorm K, coprime_absNorm F l hl K hK0 hLK, fun j hj => ?_⟩
  have hm : (Ideal.absNorm K : 𝓞 F) * j ∈ Ideal.span {a} := by
    rw [hK, mul_comm]; exact Ideal.mul_mem_mul (Ideal.absNorm_mem K) hj
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hm
  exact ⟨t, ht.symm⟩

theorem exists_gen : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (l : ℕ) [Fact l.Prime],
    ∃ c₀ : 𝔠.elt, (c₀ : F) ≠ 0 ∧ ∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 F), n.Coprime l ∧ n • c = t • c₀ := by
  intro F _ _ 𝔠 l hl
  have hlp : l.Prime := hl.out
  obtain ⟨d, hdS, hd⟩ := (𝔠 : FractionalIdeal (𝓞 F)⁰ F).isFractional
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hdS
  have hdF : (d : F) ≠ 0 := by exact_mod_cast hd0
  let J : Ideal (𝓞 F) :=
    𝔠.elt.comap ((LinearMap.mulLeft (𝓞 F) (d : F)⁻¹) ∘ₗ Algebra.linearMap (𝓞 F) F)
  have hJ : ∀ o, o ∈ J ↔ (d : F)⁻¹ * algebraMap (𝓞 F) F o ∈ 𝔠.elt := fun o => Iff.rfl
  have hint : ∀ c ∈ 𝔠.elt, ∃ o ∈ J, (c : F) = (d : F)⁻¹ * algebraMap (𝓞 F) F o := by
    intro c hc
    obtain ⟨o, ho⟩ := hd c hc
    have e : c = (d : F)⁻¹ * algebraMap (𝓞 F) F o := by
      have : algebraMap (𝓞 F) F o = (d : F) * c := by rw [ho, Algebra.smul_def]
      rw [this, inv_mul_cancel_left₀ hdF]
    exact ⟨o, (hJ o).2 (e ▸ hc), e⟩
  have hJ0 : J ≠ ⊥ := by
    have hne : (𝔠 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := 𝔠.ne_zero
    have hne' : 𝔠.elt ≠ ⊥ := by
      intro h; apply hne
      exact FractionalIdeal.coeToSubmodule_eq_bot.1 h
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne'
    obtain ⟨o, ho, e⟩ := hint c hc
    intro h
    rw [h, Ideal.mem_bot] at ho
    apply hc0
    rw [e, ho]; simp
  obtain ⟨j₀, hj₀, hj₀0, n, hn, hgen⟩ := exists_gen_int F l hlp J hJ0
  refine ⟨⟨(d : F)⁻¹ * algebraMap (𝓞 F) F j₀, (hJ j₀).1 hj₀⟩, ?_, fun c => ?_⟩
  · simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or]
    exact ⟨hdF, fun h => hj₀0 (RingOfIntegers.coe_injective (by exact h.trans (map_zero _).symm))⟩
  · obtain ⟨o, ho, e⟩ := hint c c.2
    obtain ⟨t, ht⟩ := hgen o ho
    refine ⟨n, t, hn, ?_⟩
    apply Subtype.ext
    simp only [Submodule.coe_smul, Submodule.coe_smul_of_tower]
    rw [e, nsmul_eq_mul, Algebra.smul_def]
    have := congrArg (algebraMap (𝓞 F) F) ht
    simp only [map_mul, map_natCast] at this
    linear_combination (d : F)⁻¹ * this

end GlobalTheory.FracGen
