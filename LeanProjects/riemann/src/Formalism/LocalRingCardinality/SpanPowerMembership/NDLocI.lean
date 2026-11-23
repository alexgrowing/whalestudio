import Formalism.LocalRingCardinality.SpanPowerMembership.TwCore
import Formalism.LocalRingCardinality.SpanPowerMembership.UrPkgNonempty
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocH

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc LB

theorem absNorm_mod_fifteen (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (h15 : p % 15 = 1)
    {v : HeightOneSpectrum (𝓞 E)} (hv : v ∈ placesOver E p) : Ideal.absNorm v.asIdeal % 15 = 1 := by
  haveI := v.isMaximal
  obtain ⟨q, n, -, hqP, hq, hN⟩ := Ideal.exists_prime_and_absNorm_eq_pow v.asIdeal
  have hpP : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal := hv
  have hqp : q = p := by
    by_contra hne
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr (Ne.symm hne))
    have h1 := congrArg (Int.cast : ℤ → 𝓞 E) hab
    push_cast at h1
    have hmem : (1 : 𝓞 E) ∈ v.asIdeal := by
      rw [← h1]
      exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hpP) (v.asIdeal.mul_mem_left _ hqP)
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hmem)
  rw [hN, hqp, Nat.pow_mod, h15, one_pow]
  all_goals norm_num

namespace TwB

section Settings

variable (F : Type) [Field F] [NumberField F]

abbrev TwT : Type :=
  Σ l : Nat.Primes, {w : HeightOneSpectrum (𝓞 F) // (((l : ℕ) : ℕ) : 𝓞 F) ∈ w.asIdeal}

instance (i : TwT F) : Fact ((i.1 : ℕ)).Prime := ⟨i.1.2⟩

def phi (i : TwT F) : F →+* PadicAlgCl (i.1 : ℕ) := (exists_embAt i.2.1 i.2.2).choose

theorem phi_spec (i : TwT F) (x : 𝓞 F) : x ∈ i.2.1.asIdeal ↔ ‖phi F i (x : F)‖ < 1 := by
  exact (exists_embAt i.2.1 i.2.2).choose_spec x

end Settings

section OneLL

variable {l : ℕ} [hl : Fact l.Prime] {F : Type} [Field F] (LL : FinExt l) (φ : F →+* PadicAlgCl l)
  (hφ : ∀ x, φ x ∈ LL.1)

def phiL : F →+* ↥LL.1 := φ.codRestrict LL.1.toSubfield hφ

theorem phiL_coe (x : F) : ((phiL LL φ hφ x : ↥LL.1) : PadicAlgCl l) = φ x := rfl

def embF : F →+* FractionRing ↥(OL LL) := (toFrac LL).comp (phiL LL φ hφ)

theorem embF_lt_iff (x : F) : ‖φ x‖ < 1 ↔ ∃ y ∈ maximalIdeal ↥(OL LL),
    algebraMap ↥(OL LL) (FractionRing ↥(OL LL)) y = embF LL φ hφ x := by
  have key : ∀ y : ↥(OL LL), algebraMap ↥(OL LL) (FractionRing ↥(OL LL)) y = embF LL φ hφ x ↔
      (y : ↥LL.1) = phiL LL φ hφ x := by
    intro y
    show algebraMap ↥(OL LL) (FractionRing ↥(OL LL)) y =
        (FractionRing.algEquiv ↥(OL LL) ↥LL.1).symm (phiL LL φ hφ x) ↔ _
    rw [AlgEquiv.eq_symm_apply, AlgEquiv.commutes]
    rfl
  constructor
  · intro h
    have hmem : phiL LL φ hφ x ∈ OL LL := by
      rw [mem_OL, phiL_coe]
      exact h.le
    refine ⟨⟨phiL LL φ hφ x, hmem⟩, ?_, (key _).mpr rfl⟩
    rw [mem_max]
    show ‖((phiL LL φ hφ x : ↥LL.1) : PadicAlgCl l)‖ < 1
    rw [phiL_coe]
    exact h
  · rintro ⟨y, hy, hyx⟩
    rw [mem_max] at hy
    have := (key y).mp hyx
    rw [← phiL_coe LL φ hφ, ← this]
    exact hy

def pkg : UrPkg l ↥(OL LL) :=
  (urPkg_nonempty l ↥(OL LL) (toC LL) (toC_injective LL)
    (fun x => (norm_toC LL x).le.trans (nrm_le LL x))
    (fun x hx => by rw [norm_toC]; exact (mem_max LL x).mp hx)).some

end OneLL

end TwB

end Formalism.BasicNotions.Examples₂
