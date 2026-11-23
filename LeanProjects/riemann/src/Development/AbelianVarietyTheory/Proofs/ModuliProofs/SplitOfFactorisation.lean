import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.HostConjugateIdeal
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegersOfCmFieldConjStructure
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq

open NumberField
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace GlobalTheory.HostCompare

section Trace

variable {E : Type} [Field E] [NumberField E]

theorem trace_eq_sum_finrank {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : 𝓞 E →+* Module.End ℂ W) (a : 𝓞 E) :
    LinearMap.trace ℂ W (ρ a) = ∑ τ : E →+* ℂ,
      (Module.finrank ℂ (EigenSplit.eigenSub ρ (τ.comp (algebraMap (𝓞 E) E))) : ℂ) * τ (a : E) := by
  classical
  have h := EigenSplit.isSplitting_complex E
  have h1 : ρ a = ∑ τ : E →+* ℂ, τ (a : E) • EigenSplit.proj h ρ τ := by
    ext v
    conv_lhs => rw [← EigenSplit.sum_proj h ρ v]
    rw [map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun τ _ =>
      EigenSplit.mem_eigenSub.1 (EigenSplit.proj_mem h ρ τ v) a
  rw [h1, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_smul, (EigenSplit.isProj_proj h ρ τ).trace, smul_eq_mul, mul_comm]

theorem eq_of_sum_eq {m n : (E →+* ℂ) → ℂ}
    (h : ∀ a : 𝓞 E, ∑ τ, m τ * τ (a : E) = ∑ τ, n τ * τ (a : E)) : m = n := by
  let f : (E →+* ℂ) → (𝓞 E →* ℂ) := fun φ => (φ.comp (algebraMap (𝓞 E) E)).toMonoidHom
  have hf : Function.Injective f := by
    intro φ ψ hφ
    apply (EigenSplit.isSplitting_complex E).injective
    ext a
    exact DFunLike.congr_fun hφ a
  have hli := (linearIndependent_monoidHom (𝓞 E) ℂ).comp f hf
  have hc := Fintype.linearIndependent_iff.1 hli (fun φ => m φ - n φ) (by
      funext a
      have := h a
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at this
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply, sub_mul]
      exact this)
  funext φ
  exact sub_eq_zero.1 (hc φ)

theorem trace_iff_finrank {W : Type} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (J : W →ₗ[ℝ] W) (hJ : ∀ x, J (J x) = -x) (ρ : 𝓞 E →+* Module.End ℝ W)
    (h : ∀ a, J ∘ₗ ρ a = ρ a ∘ₗ J) (m : (E →+* ℂ) → ℕ) :
    (∀ a : 𝓞 E, LinearMap.trace ℝ W (ρ a) = 2 * (∑ τ, (m τ : ℂ) * τ (a : E)).re ∧
      LinearMap.trace ℝ W (J ∘ₗ ρ a) = -2 * (∑ τ, (m τ : ℂ) * τ (a : E)).im) ↔
    ∀ τ : E →+* ℂ, Module.finrank ℝ (⨅ a : 𝓞 E, LinearMap.eqLocus (ρ a : W →ₗ[ℝ] W)
      ((τ (a : E)).re • LinearMap.id + (τ (a : E)).im • J) : Submodule ℝ W) = 2 * m τ := by
  let φ : ℂ →ₐ[ℝ] Module.End ℝ W := Complex.liftAux (J : Module.End ℝ W) (by ext x; simp [hJ])
  letI : Module ℂ W := Module.compHom W (φ : ℂ →+* Module.End ℝ W)
  have hsm : ∀ (z : ℂ) (v : W), z • v = z.re • v + z.im • J v := fun z v => by
    change φ z v = _
    simp [φ, Complex.liftAux_apply]
  haveI : IsScalarTower ℝ ℂ W := ⟨fun r z v => by
    simp [hsm, smul_add, smul_smul]⟩
  haveI : FiniteDimensional ℂ W := Module.Finite.of_restrictScalars_finite ℝ ℂ W
  have hI : ∀ v : W, Complex.I • v = J v := fun v => by simp [hsm]
  let L : 𝓞 E → Module.End ℂ W := fun a =>
    { toFun := ρ a
      map_add' := map_add _
      map_smul' := fun z v => by
        have := LinearMap.congr_fun (h a) v
        simp only [LinearMap.comp_apply] at this
        simp [hsm, this] }
  let ρ' : 𝓞 E →+* Module.End ℂ W :=
    { toFun := L
      map_one' := by ext v; simp [L]
      map_mul' := fun a b => by ext v; simp [L]
      map_zero' := by ext v; simp [L]
      map_add' := fun a b => by ext v; simp [L] }
  have ht : ∀ a, LinearMap.trace ℝ W (ρ a) = 2 * (LinearMap.trace ℂ W (ρ' a)).re ∧
      LinearMap.trace ℝ W (J ∘ₗ ρ a) = -2 * (LinearMap.trace ℂ W (ρ' a)).im := fun a => by
    have h1 := PeriodNonempty.trace_real (ρ' a)
    have h2 := PeriodNonempty.trace_real (Complex.I • ρ' a)
    have e2 : (Complex.I • ρ' a).restrictScalars ℝ = J ∘ₗ ρ a := by
      ext v; exact hI _
    rw [e2, map_smul] at h2
    refine ⟨h1, ?_⟩
    rw [h2]
    simp
  have hd : ∀ τ : E →+* ℂ, Module.finrank ℝ (⨅ a : 𝓞 E, LinearMap.eqLocus (ρ a : W →ₗ[ℝ] W)
      ((τ (a : E)).re • LinearMap.id + (τ (a : E)).im • J) : Submodule ℝ W) =
      2 * Module.finrank ℂ (EigenSplit.eigenSub ρ' (τ.comp (algebraMap (𝓞 E) E))) := fun τ => by
    have : (⨅ a : 𝓞 E, LinearMap.eqLocus (ρ a : W →ₗ[ℝ] W)
      ((τ (a : E)).re • LinearMap.id + (τ (a : E)).im • J) : Submodule ℝ W) =
        (EigenSplit.eigenSub ρ' (τ.comp (algebraMap (𝓞 E) E))).restrictScalars ℝ := by
      ext v
      rw [Submodule.restrictScalars_mem, EigenSplit.mem_eigenSub, Submodule.mem_iInf]
      refine forall_congr' fun a => ?_
      rw [LinearMap.mem_eqLocus, hsm]
      rfl
    rw [this, ← Complex.finrank_real_complex, Module.finrank_mul_finrank]
    rfl
  constructor
  · intro H τ
    have := eq_of_sum_eq (m := fun τ => (m τ : ℂ)) (n := fun τ =>
      (Module.finrank ℂ (EigenSplit.eigenSub ρ' (τ.comp (algebraMap (𝓞 E) E))) : ℂ)) (fun a => by
        rw [← trace_eq_sum_finrank ρ' a]
        have h1 := H a
        have h2 := ht a
        apply Complex.ext <;> linarith [h1.1, h1.2, h2.1, h2.2])
    rw [hd]
    exact_mod_cast congrArg (fun z : ℂ => 2 * z) (congrFun this τ).symm
  · intro H a
    have : ∀ τ, m τ = Module.finrank ℂ (EigenSplit.eigenSub ρ' (τ.comp (algebraMap (𝓞 E) E))) := fun τ => by
      have := H τ
      rw [hd] at this
      omega
    simp only [this]
    rw [← trace_eq_sum_finrank ρ' a]
    exact ht a

end Trace

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem unramified_iff : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) ↔
    ∀ P : Ideal (𝓞 E), P.IsPrime → P ≠ ⊥ → P.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := by
  rw [Algebra.unramified_iff_forall]
  constructor
  · intro h P hP _
    have := h ⟨P, hP⟩
    exact Ideal.ramificationIdx_eq_one P _
  · rintro h ⟨P, hP⟩
    rcases eq_or_ne P ⊥ with rfl | h0
    · exact Algebra.isUnramifiedAt_bot
    · exact Ideal.ramificationIdx_eq_one_iff.1 (h P hP h0)

def hostTo (H : Tor.Host E) : IndefiniteRowSideFullHecke.HostConjugateIdeal.Host E where
  d := H.d
  d_prime := H.d_prime
  d_mod := H.d_mod
  s := H.rt
  s_sq := by simpa using congrArg (algebraMap (𝓞 E) E) H.rt_sq
  unramified := unramified_iff.1 H.unram
  s₀ := H.rt0
  s₀_sq := H.sqrt_neg_disc_sq

def hostFrom (H : IndefiniteRowSideFullHecke.HostConjugateIdeal.Host E) : Tor.Host E where
  d := H.d
  d_mod := H.d_mod
  d_prime := H.d_prime
  rt := 2 * H.w₀ - 1
  rt_sq := by
    apply RingOfIntegers.ext
    have : ((2 * H.w₀ - 1 : 𝓞 E) : E) = H.s := by
      change 2 * ((1 + H.s) / 2) - 1 = H.s
      ring
    have h := H.s_sq
    rw [← this] at h
    simpa using h
  w0 := H.w₀
  two_weight_eq_one_add_root := by ring
  bar := (IsCMField.ringOfIntegersComplexConj E).toRingEquiv
  bar_eq := fun _ => rfl
  unram := unramified_iff.2 H.unramified
  rt0 := H.s₀
  sqrt_neg_disc_sq := H.s₀_sq

theorem bar_eq_conjO (H : Tor.Host E) (a : 𝓞 E) : H.bar a = IndefiniteRowSideFullHecke.HostConjugateIdeal.conjO E a :=
  RingOfIntegers.ext (H.bar_eq a)

theorem hostTo_w₀ (H : Tor.Host E) : (hostTo H).w₀ = H.w0 := by
  apply RingOfIntegers.ext
  change (1 + (H.rt : E)) / 2 = (H.w0 : E)
  have : (2 : E) * H.w0 = 1 + H.rt := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
  rw [← this]; ring

theorem host_ext {H H' : Tor.Host E} (h0 : H.d = H'.d) (h1 : H.rt = H'.rt) (h2 : H.w0 = H'.w0)
    (h3 : H.bar = H'.bar) (h4 : H.rt0 = H'.rt0) : H = H' := by
  cases H; cases H'; congr

def hostEquiv : Tor.Host E ≃ IndefiniteRowSideFullHecke.HostConjugateIdeal.Host E where
  toFun := hostTo
  invFun := hostFrom
  left_inv H := by
    have h1 : (hostFrom (hostTo H)).w0 = H.w0 := hostTo_w₀ H
    have h2 : (hostFrom (hostTo H)).rt = H.rt := by
      change 2 * (hostTo H).w₀ - 1 = _
      rw [hostTo_w₀, H.two_weight_eq_one_add_root]; ring
    have h3 : (hostFrom (hostTo H)).bar = H.bar := RingEquiv.ext fun a => (bar_eq_conjO H a).symm
    exact host_ext rfl h2 h1 h3 rfl
  right_inv H := by
    have h : (hostTo (hostFrom H)).s = H.s := by
      change 2 * ((1 + H.s) / 2) - 1 = H.s
      ring
    cases H
    unfold hostTo at h ⊢
    rw [IndefiniteRowSideFullHecke.HostConjugateIdeal.Host.mk.injEq]
    exact ⟨rfl, h, rfl⟩

section Datum

theorem conj_comp_mem_iff (H : IndefiniteRowSideFullHecke.HostConjugateIdeal.Host E) (τ : E →+* ℂ) :
    (starRingEnd ℂ).comp τ ∈ H.Psi ↔ τ ∉ H.Psi := by
  refine ⟨fun h1 h2 => ?_, (H.mem_Psi_or τ).resolve_left⟩
  change (starRingEnd ℂ) (τ H.s) = H.s₀ at h1
  change τ H.s = H.s₀ at h2
  rw [← IsCMField.complexEmbedding_complexConj, H.isCMField_complexConj_s_eq_neg, map_neg, h2] at h1
  have h3 : H.s₀ = 0 := by linear_combination (-1 / 2 : ℂ) * h1
  have h4 := H.s₀_sq
  rw [h3] at h4
  exact H.d_prime.ne_zero (by simpa using h4)

theorem conj_comp_conj_comp (τ : E →+* ℂ) : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp τ) = τ := by
  ext x; simp

open Classical in

theorem sum_type_eq (H : Tor.Host E) (p q : ℕ) (a : E) :
    ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
      ((p : ℂ) * τ a + (q : ℂ) * starRingEnd ℂ (τ a)) =
    ∑ τ : E →+* ℂ, ((if τ ∈ (hostTo H).Psi then p else q : ℕ) : ℂ) * τ a := by
  rw [Finset.sum_add_distrib, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ => τ ∈ (hostTo H).Psi)]
  congr 1
  · refine Finset.sum_congr (Finset.filter_congr fun _ _ => Iff.rfl) fun τ hτ => ?_
    rw [if_pos (Finset.mem_filter.1 hτ).2]
  · refine Finset.sum_nbij' (fun τ => (starRingEnd ℂ).comp τ) (fun τ => (starRingEnd ℂ).comp τ) ?_ ?_
      (fun τ _ => conj_comp_conj_comp τ) (fun τ _ => conj_comp_conj_comp τ) ?_
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, conj_comp_mem_iff, not_not] at hτ ⊢
      exact hτ
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      exact (conj_comp_mem_iff _ τ).2 hτ
    · intro τ hτ
      rw [if_neg (by rw [conj_comp_mem_iff, not_not]; exact (Finset.mem_filter.1 hτ).2)]
      rfl

variable {La : Type} [AddCommGroup La] [Module (𝓞 E) La]

def actHom (E La : Type) [Field E] [AddCommGroup La] [Module (𝓞 E) La] :
    𝓞 E →+* Module.End ℝ (ℝ ⊗[ℤ] La) where
  toFun := IndefiniteRowSideFullHecke.HostConjugateIdeal.actR La
  map_one' := by ext; simp [IndefiniteRowSideFullHecke.HostConjugateIdeal.actR]
  map_mul' a b := by ext; simp [IndefiniteRowSideFullHecke.HostConjugateIdeal.actR, mul_smul]
  map_zero' := by ext; simp [IndefiniteRowSideFullHecke.HostConjugateIdeal.actR]
  map_add' a b := by ext; simp [IndefiniteRowSideFullHecke.HostConjugateIdeal.actR, add_smul, TensorProduct.tmul_add]

omit [NumberField E] [IsCMField E] in
theorem eq_actR_iff (a : 𝓞 E) (A : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La) :
    (∀ x : La, A (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) ↔ A = IndefiniteRowSideFullHecke.HostConjugateIdeal.actR La a := by
  constructor
  · intro h
    ext x
    simp [IndefiniteRowSideFullHecke.HostConjugateIdeal.actR, h]
  · rintro rfl x
    simp [IndefiniteRowSideFullHecke.HostConjugateIdeal.actR]

theorem mem_domain_iff [Module.Finite (𝓞 E) La] (H : Tor.Host E) (EF : LinearMap.BilinForm ℤ La) (p q : ℕ)
    (J : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La) :
    ((∀ x, J (J x) = -x) ∧
    (∀ x y, EF.baseChange ℝ (J x) (J y) = EF.baseChange ℝ x y) ∧
    (∀ x, x ≠ 0 → 0 < EF.baseChange ℝ (J x) x) ∧
    ∀ (a : 𝓞 E) (A : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La) (t : ℂ), (∀ x : La, A (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) →
      t = ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
        ((p : ℂ) * τ (a : E) + (q : ℂ) * starRingEnd ℂ (τ (a : E))) →
      J ∘ₗ A = A ∘ₗ J ∧ LinearMap.trace ℝ _ A = 2 * t.re ∧ LinearMap.trace ℝ _ (J ∘ₗ A) = -2 * t.im) ↔
    J ∈ IndefiniteRowSideFullHecke.HostConjugateIdeal.domain (hostTo H) EF p q := by
  classical
  haveI : Module.Finite ℤ La := Module.Finite.trans (𝓞 E) La
  have key : ∀ (hJ : ∀ x, J (J x) = -x)
      (h : ∀ a : 𝓞 E, J ∘ₗ IndefiniteRowSideFullHecke.HostConjugateIdeal.actR La a = IndefiniteRowSideFullHecke.HostConjugateIdeal.actR La a ∘ₗ J), _ := fun hJ h =>
    trace_iff_finrank J hJ (actHom E La) h (fun τ => if τ ∈ (hostTo H).Psi then p else q)
  simp only [← sum_type_eq] at key
  simp only [eq_actR_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have h5 := fun a => (h4 a _ _ rfl rfl).1
    have h6 := (key h1 h5).1 fun a => (h4 a _ _ rfl rfl).2
    refine ⟨h5, LinearMap.ext h1, h2, h3, fun τ hτ => ⟨?_, ?_⟩⟩
    · have := h6 τ
      rwa [if_pos hτ] at this
    · have := h6 ((starRingEnd ℂ).comp τ)
      rwa [if_neg (by rwa [conj_comp_mem_iff, not_not])] at this
  · rintro ⟨h5, h1, h2, h3, h4⟩
    have h1' : ∀ x, J (J x) = -x := LinearMap.congr_fun h1
    refine ⟨h1', h2, h3, ?_⟩
    rintro a _ _ rfl rfl
    refine ⟨h5 a, (key h1' h5).2 (fun τ => ?_) a⟩
    by_cases hτ : τ ∈ (hostTo H).Psi
    · rw [if_pos hτ]
      exact (h4 τ hτ).1
    · rw [if_neg hτ]
      have := (h4 _ ((conj_comp_mem_iff _ τ).2 hτ)).2
      rwa [conj_comp_conj_comp] at this

def datumTo {H : Tor.Host E} (D : Tor.Datum H) :
    @IndefiniteRowSideFullHecke.HostConjugateIdeal.Datum E _ _ _ (hostTo H) D.La _ _ D.fin D.proj :=
  haveI := D.fin
  haveI := D.proj
  { EF := D.EF
    alt := D.alt
    unimodular := D.unimod
    adjoint := fun a x y => by rw [D.adj, bar_eq_conjO]
    p := D.p
    q := D.q
    p_add_q := D.rank.symm
    domain_nonempty := D.dom.imp fun J => (mem_domain_iff H D.EF D.p D.q J).1 }

def datumFrom {H : Tor.Host E} [hf : Module.Finite (𝓞 E) La] [hp : Module.Projective (𝓞 E) La]
    (X : IndefiniteRowSideFullHecke.HostConjugateIdeal.Datum (hostTo H) La) : Tor.Datum H where
  La := La
  fin := hf
  proj := hp
  EF := X.EF
  alt := X.alt
  unimod := X.unimodular
  adj := fun a x y => by rw [X.adjoint, bar_eq_conjO]
  p := X.p
  q := X.q
  rank := X.p_add_q.symm
  dom := X.domain_nonempty.imp fun J => (mem_domain_iff H X.EF X.p X.q J).2

abbrev BundledDatum (H : IndefiniteRowSideFullHecke.HostConjugateIdeal.Host E) :=
  Σ' (La : Type) (_ : AddCommGroup La) (_ : Module (𝓞 E) La) (_ : Module.Finite (𝓞 E) La)
    (_ : Module.Projective (𝓞 E) La), IndefiniteRowSideFullHecke.HostConjugateIdeal.Datum H La

def datumEquiv (H : Tor.Host E) : Tor.Datum H ≃ BundledDatum (hostEquiv H) where
  toFun D := ⟨D.La, D.acg, D.mod, D.fin, D.proj, datumTo D⟩
  invFun X := @datumFrom E _ _ _ X.1 X.2.1 X.2.2.1 H X.2.2.2.1 X.2.2.2.2.1 X.2.2.2.2.2
  left_inv _ := rfl
  right_inv _ := rfl

end Datum

section Level

variable (H : Tor.Host E)

abbrev incl : 𝓞 (hostTo H).K →+* 𝓞 E := algebraMap (𝓞 (hostTo H).K) (𝓞 E)

theorem rt_isIntegral : IsIntegral ℚ (H.rt : E) := Algebra.IsIntegral.isIntegral _

theorem mem_adjoin_iff (a : 𝓞 E) : a ∈ Algebra.adjoin ℤ {H.w0} ↔ ∃ b, incl H b = a := by
  constructor
  · intro ha
    have hw : (H.w0 : E) ∈ (hostTo H).K := by
      rw [← hostTo_w₀]
      exact div_mem (add_mem (one_mem _) (IntermediateField.mem_adjoin_simple_self ℚ _)) (ofNat_mem _ 2)
    have hi : IsIntegral ℤ (⟨_, hw⟩ : (hostTo H).K) :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ (hostTo H).K E) Subtype.val_injective).1 H.w0.2
    have : Algebra.adjoin ℤ {H.w0} ≤ (incl H).toIntAlgHom.range :=
      Algebra.adjoin_le (Set.singleton_subset_iff.2 ⟨⟨_, hi⟩, rfl⟩)
    exact this ha
  · rintro ⟨b, rfl⟩
    have hb : ((incl H b : 𝓞 E) : E) ∈ Algebra.adjoin ℚ {(H.rt : E)} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (rt_isIntegral H).isAlgebraic]
      exact (b : (hostTo H).K).2
    have key : ∀ x ∈ Algebra.adjoin ℚ {(H.rt : E)}, ∃ N : ℤ, N ≠ 0 ∧ ∃ c ∈ CM.OK H, (c : E) = N * x := by
      intro x hx
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        refine ⟨1, one_ne_zero, H.rt, ?_, by simpa using hx.symm⟩
        have : H.rt = (-1 : ℤ) + (2 : ℤ) * H.w0 := by push_cast; rw [H.two_weight_eq_one_add_root]; ring
        rw [this]
        exact CM.coord_mem H _ _
      | algebraMap r =>
        refine ⟨r.den, by exact_mod_cast r.den_nz, (r.num : 𝓞 E), intCast_mem _ _, ?_⟩
        have : (r.num : ℚ) = (r.den : ℚ) * r := by rw [Rat.den_mul_eq_num]
        have h := congrArg (algebraMap ℚ E) this
        rw [map_mul, map_intCast, map_natCast] at h
        exact h.trans (by rw [Int.cast_natCast])
      | add x y _ _ hx hy =>
        obtain ⟨N, hN, c, hc, h⟩ := hx
        obtain ⟨N', hN', c', hc', h'⟩ := hy
        refine ⟨N * N', mul_ne_zero hN hN', N' * c + N * c',
          add_mem (mul_mem (intCast_mem _ _) hc) (mul_mem (intCast_mem _ _) hc'), ?_⟩
        change (N' : E) * c + N * c' = _
        rw [h, h']; push_cast; ring
      | mul x y _ _ hx hy =>
        obtain ⟨N, hN, c, hc, h⟩ := hx
        obtain ⟨N', hN', c', hc', h'⟩ := hy
        refine ⟨N * N', mul_ne_zero hN hN', c * c', mul_mem hc hc', ?_⟩
        change (c : E) * c' = _
        rw [h, h']; push_cast; ring
    obtain ⟨N, hN, c, hc, h⟩ := key _ hb
    refine CM.mem_OK_of_int_mul_mem H hN ?_
    rwa [show (N : 𝓞 E) * incl H b = c from RingOfIntegers.ext h.symm]

theorem finrank_K_le : Module.finrank ℚ (hostTo H).K ≤ 2 := by
  refine (IntermediateField.adjoin.finrank (rt_isIntegral H)).trans_le ?_
  have hm : (Polynomial.X ^ 2 + Polynomial.C (H.d : ℚ)).Monic := by monicity!
  have := minpoly.min ℚ (H.rt : E) hm (by
    have := (hostTo H).s_sq
    simp only [map_add, map_pow, Polynomial.aeval_X, map_natCast]
    exact add_eq_zero_iff_eq_neg.2 this)
  rw [Polynomial.degree_X_pow_add_C two_pos] at this
  exact Polynomial.natDegree_le_iff_degree_le.2 this

theorem map_incl_injective : Function.Injective (Ideal.map (incl H)) :=
  Ideal.map_injective_of_faithfullyFlat

theorem map_conjIdeal (I : Ideal (𝓞 (hostTo H).K)) :
    ((hostTo H).conjIdeal I).map (incl H) = (I.map (incl H)).map (H.bar : 𝓞 E →+* 𝓞 E) := by
  rw [IndefiniteRowSideFullHecke.HostConjugateIdeal.Host.conjIdeal, Ideal.map_map, Ideal.map_map]
  congr 1
  ext b
  exact (H.bar_eq (incl H b)).symm

theorem conj_conj (H : IndefiniteRowSideFullHecke.HostConjugateIdeal.Host E) (b : 𝓞 H.K) :
    RingOfIntegers.mapRingHom H.conjK (RingOfIntegers.mapRingHom H.conjK b) = b :=
  RingOfIntegers.ext (Subtype.ext (IsCMField.complexConj_apply_apply E _))

theorem conjIdeal_conjIdeal (H : IndefiniteRowSideFullHecke.HostConjugateIdeal.Host E) (I : Ideal (𝓞 H.K)) : H.conjIdeal (H.conjIdeal I) = I := by
  rw [IndefiniteRowSideFullHecke.HostConjugateIdeal.Host.conjIdeal, IndefiniteRowSideFullHecke.HostConjugateIdeal.Host.conjIdeal, Ideal.map_map,
    show RingHom.comp _ _ = RingHom.id _ from RingHom.ext (conj_conj H), Ideal.map_id]

theorem span_eq_map_comap (I : Ideal (𝓞 E)) :
    Ideal.span {a | a ∈ I ∧ a ∈ Algebra.adjoin ℤ {H.w0}} = (I.comap (incl H)).map (incl H) := by
  rw [Ideal.map]
  congr 1
  ext a
  simp only [Set.mem_setOf_eq, mem_adjoin_iff, Set.mem_image, SetLike.mem_coe, Ideal.mem_comap]
  exact ⟨fun ⟨h, b, hb⟩ => ⟨b, hb ▸ h, hb⟩, fun ⟨b, h, hb⟩ => ⟨hb ▸ h, b, hb⟩⟩

theorem split_of_factorisation {M : ℕ} {I : Ideal (𝓞 (hostTo H).K)}
    (h1 : I * (hostTo H).conjIdeal I = Ideal.span {(M : 𝓞 (hostTo H).K)})
    (h2 : I ⊔ (hostTo H).conjIdeal I = ⊤) {p : ℕ} (hp : p.Prime) (hpM : p ∣ M) : (hostTo H).SplitInK p := by
  classical
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hp'.ne_zero).mpr hp').isMaximal hp0
  have hc := Ideal.card_primesOverFinset_le_finrank (𝓞 (hostTo H).K) ℚ (hostTo H).K hp0
  rw [← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset hp0] at hc
  refine le_antisymm (hc.trans (finrank_K_le H)) ?_
  let c := RingOfIntegers.mapRingHom (hostTo H).conjK
  have hmem : ∀ P : Ideal (𝓞 (hostTo H).K), P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 (hostTo H).K) →
      P.comap c ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 (hostTo H).K) := by
    rintro P ⟨hP, ⟨hP'⟩⟩
    refine ⟨Ideal.comap_isPrime c P, ⟨?_⟩⟩
    rw [hP', Ideal.under, Ideal.under, Ideal.comap_comap]
    congr 1
    exact RingHom.ext_int _ _
  obtain ⟨⟨P, hP⟩⟩ : Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 (hostTo H).K)) := inferInstance
  have hne : P ≠ P.comap c := by
    intro he
    have hM : (M : 𝓞 (hostTo H).K) ∈ P := by
      have : (M : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.mem_span_singleton.2 (by exact_mod_cast hpM)
      rw [hP.2.over, Ideal.under, Ideal.mem_comap] at this
      simpa using this
    have hiff : ∀ J, (hostTo H).conjIdeal J ≤ P ↔ J ≤ P := fun J => by
      rw [IndefiniteRowSideFullHecke.HostConjugateIdeal.Host.conjIdeal, Ideal.map_le_iff_le_comap, ← he]
    have hI : I ≤ P := by
      have := hP.1.mul_le.1 (h1.trans_le ((Ideal.span_singleton_le_iff_mem P).2 hM))
      rwa [hiff, or_self] at this
    exact hP.1.ne_top (top_le_iff.1 (h2 ▸ sup_le hI ((hiff I).2 hI)))
  exact (Set.one_lt_ncard (IsDedekindDomain.primesOver_finite _ _)).2 ⟨P, hP, _, hmem P hP, hne⟩

variable {H}

theorem map_comap_Mb (l : Tor.Level H) : (l.Mb.comap (incl H)).map (incl H) = l.Mb :=
  (l.fromK.trans (span_eq_map_comap H _)).symm

theorem level_mul_conj (l : Tor.Level H) : (hostTo H).conjIdeal (l.Mb.comap (incl H)) *
    (hostTo H).conjIdeal ((hostTo H).conjIdeal (l.Mb.comap (incl H))) = Ideal.span {(l.M : 𝓞 (hostTo H).K)} := by
  apply map_incl_injective H
  rw [conjIdeal_conjIdeal, Ideal.map_mul, map_conjIdeal, map_comap_Mb, mul_comm, l.prod, Ideal.map_span,
    Set.image_singleton, map_natCast]

theorem level_coprime (l : Tor.Level H) : (hostTo H).conjIdeal (l.Mb.comap (incl H)) ⊔
    (hostTo H).conjIdeal ((hostTo H).conjIdeal (l.Mb.comap (incl H))) = ⊤ := by
  apply map_incl_injective H
  rw [conjIdeal_conjIdeal, Ideal.map_sup, map_conjIdeal, map_comap_Mb, sup_comm, l.coprime, Ideal.map_top]

def levelTo (l : Tor.Level H) : IndefiniteRowSideFullHecke.HostConjugateIdeal.Level (hostTo H) where
  M := l.M
  three_le := l.three_le
  odd := l.odd
  split := fun _ hp hpM => split_of_factorisation H (level_mul_conj l) (level_coprime l) hp hpM
  MM := (hostTo H).conjIdeal (l.Mb.comap (incl H))
  mul_conj := level_mul_conj l
  coprime := level_coprime l
  A := l.A
  one_le := l.A_pos

theorem MMbarO_map_bar (L : IndefiniteRowSideFullHecke.HostConjugateIdeal.Level (hostTo H)) :
    L.MMbarO.map (H.bar : 𝓞 E →+* 𝓞 E) = L.MM.map (incl H) :=
  (map_conjIdeal H L.MMbar).symm.trans (congrArg _ (conjIdeal_conjIdeal _ _))

def levelFrom (L : IndefiniteRowSideFullHecke.HostConjugateIdeal.Level (hostTo H)) : Tor.Level H where
  M := L.M
  three_le := L.three_le
  odd := L.odd
  Mb := L.MMbarO
  fromK := by
    rw [span_eq_map_comap]
    exact (Ideal.map_comap_map _ _).symm
  prod := by
    have := congrArg (Ideal.map (incl H)) L.mul_conj
    rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton, map_natCast, mul_comm] at this
    rw [MMbarO_map_bar]
    exact this
  coprime := by
    have := congrArg (Ideal.map (incl H)) L.coprime
    rw [Ideal.map_sup, Ideal.map_top, sup_comm] at this
    rw [MMbarO_map_bar]
    exact this
  A := L.A
  A_pos := L.one_le

theorem levelTo_MMbarO (l : Tor.Level H) : (levelTo l).MMbarO = l.Mb :=
  (congrArg (Ideal.map (incl H)) (conjIdeal_conjIdeal _ _)).trans (map_comap_Mb l)

theorem level_ext {H : IndefiniteRowSideFullHecke.HostConjugateIdeal.Host E} {L L' : IndefiniteRowSideFullHecke.HostConjugateIdeal.Level H} (h0 : L.M = L'.M) (h1 : L.MM = L'.MM)
    (h2 : L.A = L'.A) : L = L' := by
  cases L; cases L'; congr

def levelEquiv (H : Tor.Host E) : Tor.Level H ≃ IndefiniteRowSideFullHecke.HostConjugateIdeal.Level (hostEquiv H) where
  toFun := levelTo
  invFun := levelFrom
  left_inv l := by
    have h := levelTo_MMbarO l
    cases l
    unfold levelFrom
    rw [Tor.Level.mk.injEq]
    exact ⟨rfl, h, rfl⟩
  right_inv L := by
    have h : (levelTo (levelFrom L)).MM = L.MM := by
      have h1 : L.MMbarO.comap (incl H) = L.MMbar := map_incl_injective H (Ideal.map_comap_map _ _)
      exact (congrArg (hostTo H).conjIdeal h1).trans (conjIdeal_conjIdeal _ _)
    exact level_ext rfl h rfl

end Level

theorem f_eq (H : IndefiniteRowSideFullHecke.HostConjugateIdeal.Host E) : H.f = Module.finrank ℚ E / 2 := by
  rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E,
    Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, Nat.mul_div_cancel _ two_pos]
  rfl

end GlobalTheory.HostCompare
