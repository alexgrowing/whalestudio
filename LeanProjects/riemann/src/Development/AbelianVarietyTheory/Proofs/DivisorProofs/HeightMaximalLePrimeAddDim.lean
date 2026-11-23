import Mathlib
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.PolyCM
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bridge
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA

namespace GlobalTheory.FinTypeIntCatenary

open ReciprocityTheory.CA

theorem isCM_atPrime_of_le {S : Type*} [CommRing S] (𝔓 𝔑 : Ideal S) [𝔓.IsPrime] [𝔑.IsPrime]
    (hle : 𝔓 ≤ 𝔑) (h : IsCM (Localization.AtPrime 𝔑)) : IsCM (Localization.AtPrime 𝔓) := by
  have hdisj : Disjoint (𝔑.primeCompl : Set S) (𝔓 : Set S) :=
    Set.disjoint_left.mpr fun x hx hxp => hx (hle hxp)
  let q : Ideal (Localization.AtPrime 𝔑) := 𝔓.map (algebraMap S (Localization.AtPrime 𝔑))
  haveI : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint 𝔑.primeCompl _ 𝔓 inferInstance hdisj
  have h2 := h.localization_atPrime q
  have hc : q.comap (algebraMap S (Localization.AtPrime 𝔑)) = 𝔓 :=
    IsLocalization.under_map_of_isPrime_disjoint 𝔑.primeCompl _ inferInstance hdisj
  haveI : IsLocalization 𝔓.primeCompl (Localization.AtPrime q) := by
    have h0 : IsLocalization (q.comap (algebraMap S (Localization.AtPrime 𝔑))).primeCompl
        (Localization.AtPrime q) :=
      IsLocalization.isLocalization_atPrime_localization_atPrime (M := 𝔑.primeCompl) q
    have hsub : (q.comap (algebraMap S (Localization.AtPrime 𝔑))).primeCompl = 𝔓.primeCompl :=
      Submonoid.ext fun x => by simp only [Ideal.mem_primeCompl_iff, hc]
    rw [hsub] at h0
    exact h0
  exact h2.of_ringEquiv (IsLocalization.algEquiv 𝔓.primeCompl (Localization.AtPrime q) (Localization.AtPrime 𝔓)).toRingEquiv

theorem height_comap_mk {S : Type*} [CommRing S] (Q : Ideal S) [Q.IsPrime] (J : Ideal (S ⧸ Q))
    [J.IsPrime] (h : IsCM (Localization.AtPrime (J.comap (Ideal.Quotient.mk Q)))) :
    (J.comap (Ideal.Quotient.mk Q)).height = Q.height + J.height := by
  have hle : Q ≤ J.comap (Ideal.Quotient.mk Q) := fun x hx => by
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx, J.zero_mem]
  have := height_eq_add_of_isCM_localization (J.comap (Ideal.Quotient.mk Q)) Q h hle
  rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at this

theorem height_le_of_equidim {S : Type*} [CommRing S] (d : ℕ)
    (hS : ∀ (𝔑 : Ideal S) [𝔑.IsMaximal], IsCM (Localization.AtPrime 𝔑) ∧ 𝔑.height = d)
    (Q : Ideal S) [Q.IsPrime] (P M : Ideal (S ⧸ Q)) [P.IsPrime] [M.IsMaximal] :
    (M.height : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) + ringKrullDim ((S ⧸ Q) ⧸ P) := by
  haveI hMt : (M.comap (Ideal.Quotient.mk Q)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨hCM1, hd1⟩ := hS (M.comap (Ideal.Quotient.mk Q))
  have e1 := height_comap_mk Q M hCM1
  obtain ⟨M', hM', hPM'⟩ := Ideal.exists_le_maximal (P.comap (Ideal.Quotient.mk Q))
    (Ideal.IsPrime.ne_top inferInstance)
  obtain ⟨hCM2, hd2⟩ := hS M'
  have e2 := height_eq_add_of_isCM_localization M' (P.comap (Ideal.Quotient.mk Q)) hCM2 hPM'
  have e3 := height_comap_mk Q P (isCM_atPrime_of_le _ M' hPM' hCM2)
  have hQM : Q ≤ M.comap (Ideal.Quotient.mk Q) := fun x hx => by
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx, M.zero_mem]
  have hQP : Q ≤ P.comap (Ideal.Quotient.mk Q) := fun x hx => by
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx, P.zero_mem]
  have hQle : Q.height ≤ d := hd1 ▸ Ideal.height_mono hQM
  have hQt : Q.height ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top d) hQle
  have key : M.height = P.height +
      (M'.map (Ideal.Quotient.mk (P.comap (Ideal.Quotient.mk Q)))).height := by
    have hsum : Q.height + M.height = Q.height + (P.height +
        (M'.map (Ideal.Quotient.mk (P.comap (Ideal.Quotient.mk Q)))).height) := by
      rw [← e1, hd1, ← hd2, e2, e3, add_assoc]
    exact WithTop.add_left_cancel hQt hsum
  haveI : (M'.map (Ideal.Quotient.mk (P.comap (Ideal.Quotient.mk Q)))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hPM')
  have hb : ((M'.map (Ideal.Quotient.mk (P.comap (Ideal.Quotient.mk Q)))).height : WithBot ℕ∞) ≤
      ringKrullDim (S ⧸ P.comap (Ideal.Quotient.mk Q)) := Ideal.height_le_ringKrullDim_of_isPrime
  have hdim : ringKrullDim ((S ⧸ Q) ⧸ (P.comap (Ideal.Quotient.mk Q)).map (Ideal.Quotient.mk Q)) =
      ringKrullDim (S ⧸ P.comap (Ideal.Quotient.mk Q)) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hQP)
  rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at hdim
  rw [key, hdim]
  push_cast
  exact add_le_add le_rfl hb

theorem isMaximal_comap_C_int (N : ℕ) (𝔑 : Ideal (MvPolynomial (Fin N) ℤ)) [𝔑.IsMaximal] :
    (𝔑.comap (MvPolynomial.C : ℤ →+* MvPolynomial (Fin N) ℤ)).IsMaximal := by
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  have hi := MvPolynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing 𝔑
  letI := Ideal.Quotient.field 𝔑
  have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ hi
    (⊥ : Ideal (MvPolynomial (Fin N) ℤ ⧸ 𝔑))
  rwa [← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at this

theorem isCM_localization_int (p : Ideal ℤ) [p.IsMaximal] :
    IsCM (Localization.AtPrime p) ∧ ringKrullDim (Localization.AtPrime p) = 1 := by
  have hp : p ≠ ⊥ := by
    intro h
    have : (⊥ : Ideal ℤ).IsMaximal := h ▸ inferInstance
    exact Int.not_isField (Ring.isField_iff_maximal_bot.mpr this)
  haveI : IsDiscreteValuationRing (Localization.AtPrime p) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ hp _
  have hd := IsDiscreteValuationRing.ringKrullDim_eq_one (Localization.AtPrime p)
  refine ⟨⟨inferInstance, 1, by rw [hd]; rfl, ?_⟩, hd⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime p)
  have hm : ϖ ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p) := hϖ.not_isUnit
  refine ⟨[ϖ], rfl, by simpa using hm, ?_⟩
  rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (by simpa using hm),
    RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  exact IsSMulRegular.of_ne_zero hϖ.ne_zero

theorem exists_maximal_mvPolynomial_localization (N : ℕ) (p : Ideal ℤ) [p.IsMaximal] (𝔑 : Ideal (MvPolynomial (Fin N) ℤ)) [𝔑.IsMaximal]
    (hc : 𝔑.comap (MvPolynomial.C : ℤ →+* MvPolynomial (Fin N) ℤ) = p) :
    ∃ (𝔑' : Ideal (MvPolynomial (Fin N) (Localization.AtPrime p))) (_ : 𝔑'.IsMaximal),
      𝔑'.comap (MvPolynomial.C : Localization.AtPrime p →+* _) =
        IsLocalRing.maximalIdeal (Localization.AtPrime p) ∧
      Nonempty (Localization.AtPrime 𝔑' ≃+* Localization.AtPrime 𝔑) ∧ 𝔑'.height = 𝔑.height := by
  classical
  letI : Algebra (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)) :=
    MvPolynomial.algebraMvPolynomial
  let W : Submonoid (MvPolynomial (Fin N) ℤ) := p.primeCompl.map (MvPolynomial.C (σ := Fin N))
  haveI hL : IsLocalization W (MvPolynomial (Fin N) (Localization.AtPrime p)) :=
    MvPolynomial.isLocalization p.primeCompl (Localization.AtPrime p)
  have hdisj : Disjoint (W : Set (MvPolynomial (Fin N) ℤ)) (𝔑 : Set _) := by
    rw [Set.disjoint_left]
    rintro x ⟨m, hm, rfl⟩ hx
    exact hm (hc ▸ (show m ∈ 𝔑.comap MvPolynomial.C from hx))
  let 𝔑' := 𝔑.map (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)))
  haveI hP : 𝔑'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint W _ 𝔑 inferInstance hdisj
  have hcm : 𝔑'.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p))) = 𝔑 :=
    IsLocalization.under_map_of_isPrime_disjoint W _ inferInstance hdisj
  haveI hM : 𝔑'.IsMaximal := by
    refine ⟨⟨hP.ne_top, fun J hJ => ?_⟩⟩
    by_contra hJt
    have h1 : 𝔑 ≤ J.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p))) :=
      hcm ▸ Ideal.comap_mono hJ.le
    have h2 : J.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p))) ≠ ⊤ := by
      intro h
      apply hJt
      rw [Ideal.eq_top_iff_one]
      have : (1 : MvPolynomial (Fin N) ℤ) ∈ J.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p))) := h ▸ Submodule.mem_top
      simpa using this
    have h3 := (‹𝔑.IsMaximal›.eq_of_le h2 h1)
    have h4 : J = 𝔑' := by
      have h5 := IsLocalization.map_comap W (MvPolynomial (Fin N) (Localization.AtPrime p)) J
      change Ideal.map _ (J.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)))) = J at h5
      rw [← h3] at h5
      exact h5.symm
    exact hJ.ne' h4
  refine ⟨𝔑', hM, ?_, ?_, IsLocalization.height_map_of_disjoint W 𝔑 hdisj⟩
  · haveI : (𝔑'.comap (MvPolynomial.C : Localization.AtPrime p →+* _)).IsPrime := Ideal.comap_isPrime _ _
    refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have e : (MvPolynomial.C (algebraMap ℤ (Localization.AtPrime p) x) : MvPolynomial (Fin N) (Localization.AtPrime p)) =
        algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)) (MvPolynomial.C x) := by
      rw [MvPolynomial.algebraMap_def, MvPolynomial.map_C]
    rw [e]
    exact Ideal.mem_map_of_mem _ (by rw [← hc] at hx; exact hx)
  · haveI h0 : IsLocalization.AtPrime (Localization.AtPrime 𝔑')
        (𝔑'.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)))) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization W _ 𝔑'
    haveI : IsLocalization 𝔑.primeCompl (Localization.AtPrime 𝔑') := by
      have hsub : (𝔑'.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)))).primeCompl = 𝔑.primeCompl :=
        Submonoid.ext fun x => by simp only [Ideal.mem_primeCompl_iff, hcm]
      have h0' : IsLocalization (𝔑'.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)))).primeCompl (Localization.AtPrime 𝔑') := h0
      rw [hsub] at h0'
      exact h0'
    exact ⟨(IsLocalization.algEquiv 𝔑.primeCompl (Localization.AtPrime 𝔑') (Localization.AtPrime 𝔑)).toRingEquiv⟩

theorem isCM_and_height_of_isMaximal (N : ℕ) (𝔑 : Ideal (MvPolynomial (Fin N) ℤ)) [𝔑.IsMaximal] :
    IsCM (Localization.AtPrime 𝔑) ∧ 𝔑.height = ((N + 1 : ℕ) : ℕ∞) := by
  haveI := isMaximal_comap_C_int N 𝔑
  obtain ⟨hCM, hdim⟩ := isCM_localization_int (𝔑.comap (MvPolynomial.C : ℤ →+* MvPolynomial (Fin N) ℤ))
  obtain ⟨𝔑', h𝔑', hc, ⟨e⟩, hh⟩ := exists_maximal_mvPolynomial_localization N _ 𝔑 rfl
  have h := isCM_localization_mvPolynomial hCM N 𝔑' hc
  refine ⟨h.1.of_ringEquiv e, ?_⟩
  have h2 := h.2
  rw [hdim, hh] at h2
  have h3 : ((𝔑.height : ℕ∞) : WithBot ℕ∞) = (((N + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rw [h2]; push_cast; ring
  exact WithBot.coe_injective h3

theorem height_maximal_le (A : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A]
    (P M : Ideal A) [P.IsPrime] [M.IsMaximal] :
    (M.height : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) + ringKrullDim (A ⧸ P) := by
  obtain ⟨N, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType ℤ A›
  haveI : (RingHom.ker (f : MvPolynomial (Fin N) ℤ →+* A)).IsPrime := RingHom.ker_isPrime _
  let e : (MvPolynomial (Fin N) ℤ ⧸ RingHom.ker (f : MvPolynomial (Fin N) ℤ →+* A)) ≃+* A :=
    RingHom.quotientKerEquivOfSurjective (f := (f : MvPolynomial (Fin N) ℤ →+* A)) hf
  haveI : (P.comap e).IsPrime := Ideal.comap_isPrime _ _
  haveI : (M.comap e).IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.surjective
  have h := height_le_of_equidim (N + 1) (isCM_and_height_of_isMaximal N) _ (P.comap e) (M.comap e)
  rw [RingEquiv.height_comap, RingEquiv.height_comap] at h
  have hdim : ringKrullDim ((MvPolynomial (Fin N) ℤ ⧸ RingHom.ker (f : MvPolynomial (Fin N) ℤ →+* A)) ⧸
      P.comap e) = ringKrullDim (A ⧸ P) :=
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ e
      (Ideal.map_comap_of_surjective _ e.surjective P).symm)
  rwa [hdim] at h

end GlobalTheory.FinTypeIntCatenary
