import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartB
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField

namespace ReciprocityTheory.AnForm.R.JacobianCriterionAlt

open MvPolynomial IsLocalRing

noncomputable section

variable {n : ℕ}

theorem isRegularLocalRing_of_jacobian' (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (hp : ∀ h ∈ K, eval p h = 0) {c : ℕ} (F : Fin c → MvPolynomial (Fin n) ℂ) (hF : ∀ i, F i ∈ K)
    (hlin : LinearIndependent ℂ (fun i => gradP p (F i)))
    (hq : ∃ 𝔮 ∈ K.minimalPrimes, 𝔮 ≤ ptI p ∧ 𝔮.height ≤ c) :
    IsRegularLocalRing (locR K p) ∧ ringKrullDim (locR K p) = ((n - c : ℕ) : WithBot ℕ∞) := by
  obtain ⟨hloc, hnoeth⟩ := locRing_isLocalRing_isNoetherian' K p hp
  have hcot := finrank_cot_eq p K
  have hrank : c ≤ Module.finrank ℂ (jacS K p) := by
    let v : Fin c → jacS K p := fun i => ⟨gradP p (F i), Submodule.subset_span ⟨F i, hF i, rfl⟩⟩
    have hv : LinearIndependent ℂ v := LinearIndependent.of_comp (jacS K p).subtype hlin
    simpa using hv.fintype_card_le_finrank
  have hcotle : Module.finrank (ResidueField (locR K p)) (CotangentSpace (locR K p)) ≤ n - c := by
    omega
  have hdimle : ringKrullDim (locR K p) ≤ ((n - c : ℕ) : WithBot ℕ∞) := by
    refine (ringKrullDim_le_spanFinrank_maximalIdeal _).trans ?_
    rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
    exact_mod_cast hcotle
  obtain ⟨𝔮, h𝔮min, h𝔮P, h𝔮c⟩ := hq
  have h𝔮prime : 𝔮.IsPrime := h𝔮min.1.1
  have hK𝔮 : K ≤ 𝔮 := h𝔮min.1.2
  set Pb : Ideal (MvPolynomial (Fin n) ℂ ⧸ 𝔮) := (ptI p).map (Ideal.Quotient.mk 𝔮) with hPb
  have hker : RingHom.ker (Ideal.Quotient.mk 𝔮) ≤ ptI p := by rw [Ideal.mk_ker]; exact h𝔮P
  have hPbprime : Pb.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hPmax : (ptI p).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, eval_C _⟩)
  have hPbmax : Pb.IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective hPmax).resolve_left
      hPbprime.ne_top
  have hheight := ReciprocityTheory.CA.height_add_height_maximal_quotient_field ℂ n 𝔮 Pb
  have hmemPb : ∀ s, Ideal.Quotient.mk 𝔮 s ∈ Pb ↔ s ∈ ptI p := by
    intro s; rw [hPb, Ideal.mem_quotient_iff_mem_sup, sup_eq_left.mpr h𝔮P]
  let gq : MvPolynomial (Fin n) ℂ →+* Localization.AtPrime Pb :=
    (algebraMap _ (Localization.AtPrime Pb)).comp (Ideal.Quotient.mk 𝔮)
  have hunits : ∀ y : (ptI p).primeCompl, IsUnit (gq y) := fun y =>
    IsLocalization.map_units (Localization.AtPrime Pb)
      (⟨Ideal.Quotient.mk 𝔮 y, fun h => y.2 ((hmemPb y).mp h)⟩ : Pb.primeCompl)
  let φ : localization₂ p →+* Localization.AtPrime Pb :=
    IsLocalization.lift (M := (ptI p).primeCompl) hunits
  have hφ : Function.Surjective φ := by
    intro t
    obtain ⟨⟨x, y⟩, rfl⟩ := IsLocalization.mk'_surjective Pb.primeCompl t
    obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y', hy'⟩ := Ideal.Quotient.mk_surjective (y : MvPolynomial (Fin n) ℂ ⧸ 𝔮)
    have hy'P : y' ∉ ptI p := fun h => y.2 (hy' ▸ (hmemPb y').mpr h)
    refine ⟨IsLocalization.mk' (localization₂ p) x' (⟨y', hy'P⟩ : (ptI p).primeCompl), ?_⟩
    rw [IsLocalization.lift_mk'_spec]
    simp only [gq, RingHom.coe_comp, Function.comp_apply, hy']
    rw [IsLocalization.mk'_spec']
  have hφK : ∀ a ∈ Ideal.map (algebraMap _ (localization₂ p)) K, φ a = 0 := by
    intro a ha
    have : Ideal.map (algebraMap _ (localization₂ p)) K ≤ RingHom.ker φ := by
      rw [Ideal.map_le_iff_le_comap]
      intro k hk
      rw [Ideal.mem_comap, RingHom.mem_ker]
      simp only [φ, IsLocalization.lift_eq, gq, RingHom.coe_comp, Function.comp_apply,
        Ideal.Quotient.eq_zero_iff_mem.mpr (hK𝔮 hk), map_zero]
    exact this ha
  have hφB : Function.Surjective (Ideal.Quotient.lift _ φ hφK) :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ hφ
  have hle := ringKrullDim_le_of_surjective _ hφB
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height Pb (Localization.AtPrime Pb)] at hle
  have hqfin : 𝔮.height ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top c) h𝔮c
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hqfin
  have hPbfin : Pb.height ≠ ⊤ := by
    intro h; rw [h, add_top] at hheight; exact ENat.top_ne_natCast n hheight
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hPbfin
  have hkm : k + m = n := by rw [← hk, ← hm] at hheight; exact_mod_cast hheight
  have hkc : k ≤ c := by rw [← hk] at h𝔮c; exact_mod_cast h𝔮c
  rw [← hm] at hle
  have hdimge : ((n - c : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (locR K p) := by
    refine le_trans ?_ hle
    show (((n - c : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ ((m : ℕ∞) : WithBot ℕ∞)
    exact WithBot.coe_le_coe.mpr (Nat.cast_le.mpr (by omega))
  have hdim := le_antisymm hdimle hdimge
  refine ⟨?_, hdim⟩
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, hdim]
  exact_mod_cast hcotle

end

end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
