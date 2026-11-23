import Mathlib
import Formalism.DistinguishedUnitIdeals.CoprimeProd
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.GroundTheory

noncomputable section

namespace Formalism.ExponentWindows

open PowerSeries

section Scalar

variable {O : Type} [CommRing O] [IsDomain O]

def IsSat (ϖ : O) (P : PowerSeries O) : Prop :=
  ∀ (N : ℕ) (z : PowerSeries O), P ∣ C (ϖ ^ N) * z → P ∣ z

theorem isSat_one (ϖ : O) : IsSat ϖ 1 := by
  intro _ _ _
  exact one_dvd _

theorem isSat_mul (ϖ : O) (P Q : PowerSeries O) (hP : IsSat ϖ P) (hQ : IsSat ϖ Q) :
    IsSat ϖ (P * Q) := by
  intro N z h
  have hPz : P ∣ z := hP N z (dvd_trans (dvd_mul_right P Q) h)
  obtain ⟨z', rfl⟩ := hPz
  by_cases hP0 : P = 0
  · subst hP0; simp
  · have hQ' : Q ∣ C (ϖ ^ N) * z' := by
      obtain ⟨w, hw⟩ := h
      refine ⟨w, ?_⟩
      have e : P * (C (ϖ ^ N) * z') = P * (Q * w) := by linear_combination hw
      exact mul_left_cancel₀ hP0 e
    exact mul_dvd_mul_left P (hQ N z' hQ')

theorem isSat_prod (ϖ : O) (S : Finset ℕ) (P : ℕ → PowerSeries O) (h : ∀ s ∈ S, IsSat ϖ (P s)) :
    IsSat ϖ (∏ s ∈ S, P s) := by
  classical
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _; simpa using isSat_one ϖ
  · intro a S ha ih h
    rw [Finset.prod_insert ha]
    exact isSat_mul ϖ _ _ (h a (Finset.mem_insert_self a S))
      (ih fun s hs => h s (Finset.mem_insert_of_mem hs))

theorem coprimeRat₂_symm (ϖ : O) (P Q : PowerSeries O) (h : CoprimeRat ϖ P Q) : CoprimeRat ϖ Q P := by
  obtain ⟨N, a, a', hN⟩ := h
  exact ⟨N, a', a, by linear_combination hN⟩

theorem coprimeRat₂_one_right (ϖ : O) (P : PowerSeries O) : CoprimeRat ϖ P 1 := ⟨0, 0, C (ϖ ^ 0), by simp⟩

theorem coprimeRat₂_mul_right (ϖ : O) (P Q Q' : PowerSeries O) (h : CoprimeRat ϖ P Q)
    (h' : CoprimeRat ϖ P Q') : CoprimeRat ϖ P (Q * Q') := by
  obtain ⟨N, a, a', hN⟩ := h
  obtain ⟨M, b, b', hM⟩ := h'
  refine ⟨N + M, a * b * P + a * b' * Q' + a' * b * Q, a' * b', ?_⟩
  rw [pow_add, map_mul, ← hN, ← hM]
  ring

theorem coprimeRat₂_prod_right (ϖ : O) (P : PowerSeries O) (S : Finset ℕ) (Q : ℕ → PowerSeries O)
    (h : ∀ s ∈ S, CoprimeRat ϖ P (Q s)) : CoprimeRat ϖ P (∏ s ∈ S, Q s) := by
  classical
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _; simpa using coprimeRat₂_one_right ϖ P
  · intro a S ha ih h
    rw [Finset.prod_insert ha]
    exact coprimeRat₂_mul_right ϖ P _ _ (h a (Finset.mem_insert_self a S))
      (ih fun s hs => h s (Finset.mem_insert_of_mem hs))

theorem coprimeRat₂_pow_right (ϖ : O) (P Q : PowerSeries O) (h : CoprimeRat ϖ P Q) (n : ℕ) :
    CoprimeRat ϖ P (Q ^ n) := by
  induction n with
  | zero => simpa using coprimeRat₂_one_right ϖ P
  | succ n ih =>
    rw [pow_succ]
    exact coprimeRat₂_mul_right ϖ P _ _ ih h

theorem coprimeRat₂_pow_pow (ϖ : O) (P Q : PowerSeries O) (h : CoprimeRat ϖ P Q) (m n : ℕ) :
    CoprimeRat ϖ (P ^ m) (Q ^ n) :=
  coprimeRat₂_symm ϖ _ _ (coprimeRat₂_pow_right ϖ _ _
    (coprimeRat₂_symm ϖ _ _ (coprimeRat₂_pow_right ϖ P Q h n)) m)

theorem dvd_of_dvd_mul_coprimeRat (ϖ : O) (P Q x : PowerSeries O) (hs : IsSat ϖ P)
    (hc : CoprimeRat ϖ P Q) (N : ℕ) (h : P ∣ Q * (C (ϖ ^ N) * x)) : P ∣ x := by
  obtain ⟨M, a, a', hM⟩ := hc
  apply hs (M + N) x
  have e : C (ϖ ^ (M + N)) * x = P * (a * (C (ϖ ^ N) * x)) + a' * (Q * (C (ϖ ^ N) * x)) := by
    rw [pow_add, map_mul, ← hM]
    ring
  rw [e]
  exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_right h _)

theorem prod_dvd_of_coprimeRat (ϖ : O) (S : Finset ℕ) (P : ℕ → PowerSeries O)
    (hs : ∀ s ∈ S, IsSat ϖ (P s)) (hc : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → CoprimeRat ϖ (P s) (P t))
    (Y : PowerSeries O) (hY : ∀ s ∈ S, P s ∣ Y) : (∏ s ∈ S, P s) ∣ Y := by
  classical
  revert hs hc hY
  refine Finset.induction_on S ?_ ?_
  · intro _ _ _; simp
  · intro a S ha ih hs hc hY
    rw [Finset.prod_insert ha]
    have hS : (∏ s ∈ S, P s) ∣ Y := ih (fun s hs' => hs s (Finset.mem_insert_of_mem hs'))
      (fun s hs' t ht' hst => hc s (Finset.mem_insert_of_mem hs') t (Finset.mem_insert_of_mem ht') hst)
      (fun s hs' => hY s (Finset.mem_insert_of_mem hs'))
    obtain ⟨w, hw⟩ := hS
    have hcop : CoprimeRat ϖ (P a) (∏ s ∈ S, P s) :=
      coprimeRat₂_prod_right ϖ (P a) S P (fun t ht => hc a (Finset.mem_insert_self a S) t
        (Finset.mem_insert_of_mem ht) (fun hat => ha (by rw [hat]; exact ht)))
    have hdiv : P a ∣ (∏ s ∈ S, P s) * (C (ϖ ^ 0) * w) := by
      have := hY a (Finset.mem_insert_self a S)
      rw [hw] at this
      simpa using this
    obtain ⟨w', hw'⟩ := dvd_of_dvd_mul_coprimeRat ϖ (P a) _ w (hs a (Finset.mem_insert_self a S)) hcop 0 hdiv
    exact ⟨w', by rw [hw, hw']; ring⟩

end Scalar

section DVR

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private lemma prime_C_lemma (ϖ : O) (hϖ : Irreducible ϖ) : Prime (C ϖ : PowerSeries O) := by
  haveI hmax : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  haveI : (Ideal.span {ϖ}).IsPrime := hmax.isPrime
  have key : ∀ f : PowerSeries O,
      C ϖ ∣ f ↔ PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) f = 0 := by
    intro f
    constructor
    · rintro ⟨g, rfl⟩
      rw [map_mul, PowerSeries.map_C,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ϖ), map_zero, zero_mul]
    · intro hf
      have hc : ∀ n, ∃ a, a * ϖ = PowerSeries.coeff (R := O) n f := fun n => by
        have h1 := congrArg (PowerSeries.coeff (R := O ⧸ Ideal.span {ϖ}) n) hf
        rw [PowerSeries.coeff_map, map_zero] at h1
        exact Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp h1)
      choose g hg using hc
      refine ⟨PowerSeries.mk g, ?_⟩
      ext n
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, ← hg n, mul_comm]
  refine ⟨?_, ?_, fun a b hab => ?_⟩
  · intro h0
    apply hϖ.ne_zero
    simpa using congrArg (PowerSeries.constantCoeff (R := O)) h0
  · intro hu
    exact hϖ.not_isUnit (by simpa using hu.map (PowerSeries.constantCoeff (R := O)))
  · rw [key, key]
    rw [key, map_mul] at hab
    exact mul_eq_zero.mp hab

theorem isSat_pow_of_unitDist (ϖ : O) (hϖ : Irreducible ϖ) (d : ℕ) (p : PowerSeries O)
    (hp : UnitDist ϖ d p) (k : ℕ) : IsSat ϖ (p ^ k) := by
  have hpr := prime_C_lemma ϖ hϖ
  obtain ⟨u, E, hu, hE, -, rfl⟩ := hp
  have hnd : ¬ (C ϖ ∣ (u * (E : PowerSeries O)) ^ k) := by
    intro h
    have h1 : C ϖ ∣ (E : PowerSeries O) := by
      rcases hpr.dvd_or_dvd (hpr.dvd_of_dvd_pow h) with h2 | h2
      · exact absurd (isUnit_of_dvd_unit h2 hu) hpr.not_unit
      · exact h2
    obtain ⟨g, hg⟩ := h1
    have h3 := congrArg (PowerSeries.coeff (R := O) E.natDegree) hg
    rw [Polynomial.coeff_coe, PowerSeries.coeff_C_mul, hE.monic.coeff_natDegree] at h3
    exact hϖ.not_isUnit (isUnit_of_dvd_one ⟨_, h3⟩)
  intro N
  induction N with
  | zero =>
    intro z h
    simpa using h
  | succ N ih =>
    intro z h
    apply ih z
    obtain ⟨t, ht⟩ := h
    have e1 : C (ϖ ^ (N + 1)) = C ϖ * C (ϖ ^ N) := by rw [pow_succ', map_mul]
    rw [e1] at ht
    have hdiv : C ϖ ∣ (u * (E : PowerSeries O)) ^ k * t := by
      rw [← ht, mul_assoc]
      exact dvd_mul_right _ _
    rcases hpr.dvd_or_dvd hdiv with h2 | ⟨t', rfl⟩
    · exact absurd h2 hnd
    · refine ⟨t', ?_⟩
      have e2 : C ϖ * (C (ϖ ^ N) * z) = C ϖ * ((u * (E : PowerSeries O)) ^ k * t') := by
        linear_combination ht
      exact mul_left_cancel₀ hpr.ne_zero e2

theorem pow_dvd_of_mul_C_mem (ϖ : O) (hϖ : Irreducible ϖ) (P₀ P₁ : PowerSeries O)
    (hs : IsSat ϖ P₀) (c K : ℕ) (δ : O)
    (hnot : P₁ ∉ Ideal.span {C (ϖ ^ (c + 1)), P₀})
    (hmem : P₁ * C δ ∈ Ideal.span {C (ϖ ^ K), P₀}) : ϖ ^ K ∣ ϖ ^ c * δ := by
  by_cases hδ : δ = 0
  · subst hδ
    simp
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hδ hϖ
  by_cases hle : K ≤ c + m
  · have e : ϖ ^ (c + m) = ϖ ^ K * ϖ ^ (c + m - K) := by
      rw [← pow_add, Nat.add_sub_cancel' hle]
    refine ⟨ϖ ^ (c + m - K) * u, ?_⟩
    rw [show ϖ ^ c * ((u : O) * ϖ ^ m) = ϖ ^ (c + m) * u by ring, e]
    ring
  · exfalso
    apply hnot
    rw [Ideal.mem_span_pair] at hmem ⊢
    obtain ⟨a, b, hab⟩ := hmem
    obtain ⟨e, rfl⟩ : ∃ e, K = c + 1 + m + e := ⟨K - (c + 1 + m), by omega⟩
    have hu1 : C ((u⁻¹ : Oˣ) : O) * C (u : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hd : P₀ ∣ C (ϖ ^ m) * (P₁ - C ((u⁻¹ : Oˣ) : O) * a * C (ϖ ^ e) * C (ϖ ^ (c + 1))) := by
      refine ⟨C ((u⁻¹ : Oˣ) : O) * b, ?_⟩
      simp only [map_mul, map_pow] at hab ⊢
      linear_combination (-(C ((u⁻¹ : Oˣ) : O))) * hab - (C ϖ ^ m * P₁) * hu1
    obtain ⟨t, ht⟩ := hs m _ hd
    exact ⟨C ((u⁻¹ : Oˣ) : O) * a * C (ϖ ^ e), t, by linear_combination -ht⟩

end DVR

section Linear

variable {O : Type} [CommRing O] [IsDomain O] {r : ℕ}

def linExt (g : (Fin r → O) →ₗ[O] O) : (Fin r → PowerSeries O) →ₗ[PowerSeries O] PowerSeries O where
  toFun u := ∑ i, u i * C (g (Pi.single i 1))
  map_add' u v := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' a u := by simp [Finset.mul_sum, mul_assoc]

theorem linExt_apply (g : (Fin r → O) →ₗ[O] O) (u : Fin r → PowerSeries O) :
    linExt g u = ∑ i, u i * C (g (Pi.single i 1)) := rfl

theorem linExt_cst (g : (Fin r → O) →ₗ[O] O) (v : Fin r → O) : linExt g (cst v) = C (g v) := by
  rw [linExt_apply]
  simp_rw [cst, ← map_mul, ← map_sum]
  congr 1
  have key : ∀ i, v i * g (Pi.single i 1) = g (v i • Pi.single i 1) := fun i => by
    rw [LinearMap.map_smul, smul_eq_mul]
  simp_rw [key, ← map_sum]
  congr 1
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem linExt_proj (u : Fin r → PowerSeries O) (j : Fin r) :
    linExt (LinearMap.proj j : (Fin r → O) →ₗ[O] O) u = u j := by
  rw [linExt_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Pi.single_apply, Ne.symm hij]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem linExt_sub (g₁ g₂ : (Fin r → O) →ₗ[O] O) (u : Fin r → PowerSeries O) :
    linExt (g₁ - g₂) u = linExt g₁ u - linExt g₂ u := by
  simp only [linExt_apply, LinearMap.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

theorem linExt_mem_of_mem_ext (g : (Fin r → O) →ₗ[O] O) (V : Submodule O (Fin r → O)) (a : O)
    (hg : ∀ v ∈ V, g v ∈ Ideal.span {a}) (u : Fin r → PowerSeries O) (hu : u ∈ ext V) :
    linExt g u ∈ Ideal.span {C a} := by
  simp only [Formalism.ExponentWindows.ext] at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    rw [linExt_cst]
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (hg v hv)
    rw [← ht, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [map_smul, smul_eq_mul]
    exact Ideal.mul_mem_left _ _ hx

def vecExt (f : (Fin r → O) →ₗ[O] (Fin r → O)) (u : Fin r → PowerSeries O) :
    Fin r → PowerSeries O :=
  fun j => linExt (LinearMap.proj j ∘ₗ f) u

theorem vecExt_eq_sum (f : (Fin r → O) →ₗ[O] (Fin r → O)) (u : Fin r → PowerSeries O) :
    vecExt f u = ∑ i, u i • cst (f (Pi.single i 1)) := by
  funext j
  simp [vecExt, linExt_apply, cst, Finset.sum_apply]

theorem vecExt_mem_ext (f : (Fin r → O) →ₗ[O] (Fin r → O)) (W : Submodule O (Fin r → O))
    (hf : ∀ v, f v ∈ W) (u : Fin r → PowerSeries O) : vecExt f u ∈ ext W := by
  rw [vecExt_eq_sum]
  refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ ?_)
  exact Submodule.subset_span ⟨f (Pi.single i 1), hf _, rfl⟩

theorem saturated_pow (ϖ : O) (V : Submodule O (Fin r → O)) (hV : Saturated ϖ V) (n : ℕ)
    (v : Fin r → O) (h : ϖ ^ n • v ∈ V) : v ∈ V := by
  induction n generalizing v with
  | zero => simpa using h
  | succ n ih =>
    exact ih v (hV _ (by rwa [smul_smul, ← pow_succ']))

end Linear

section Quot

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r : ℕ}

theorem noZeroSMulDivisors_quot (ϖ : O) (hϖ : Irreducible ϖ) (V : Submodule O (Fin r → O))
    (hV : Saturated ϖ V) : NoZeroSMulDivisors O ((Fin r → O) ⧸ V) := by
  constructor
  intro c x hcx
  by_cases hc : c = 0
  · exact Or.inl hc
  right
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective V x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hcx
  rw [Submodule.Quotient.mk_eq_zero]
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  apply saturated_pow ϖ V hV n v
  have h1 := V.smul_mem ((u⁻¹ : Oˣ) : O) hcx
  rwa [smul_smul, ← mul_assoc, Units.inv_mul, one_mul] at h1

theorem exists_proj_of_saturated (ϖ : O) (hϖ : Irreducible ϖ) (V : Submodule O (Fin r → O))
    (hV : Saturated ϖ V) :
    ∃ f : (Fin r → O) →ₗ[O] (Fin r → O), (∀ v ∈ V, f v = 0) ∧ (∀ v, v - f v ∈ V) := by
  haveI := noZeroSMulDivisors_quot ϖ hϖ V hV
  haveI : Module.Free O ((Fin r → O) ⧸ V) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property V.mkQ (LinearMap.id) (Submodule.mkQ_surjective V)
  refine ⟨s ∘ₗ V.mkQ, fun v hv => ?_, fun v => ?_⟩
  · rw [LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero V).mpr hv, map_zero]
  · rw [← Submodule.Quotient.mk_eq_zero V, Submodule.Quotient.mk_sub]
    have h1 := LinearMap.congr_fun hs (Submodule.Quotient.mk v)
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Submodule.mkQ_apply] at h1 ⊢
    rw [h1, sub_self]

end Quot

section Decomp

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r : ℕ}

theorem exists_const_decomp (ϖ : O) (hϖ : Irreducible ϖ) (F C : Submodule O (Fin r → O))
    (hF : Saturated ϖ F) (c k : ℕ) (d : Fin r → O)
    (hkey : ∀ (φ : (Fin r → O) →ₗ[O] O) (n : ℕ), (∀ v ∈ F, φ v = 0) →
      (∀ v ∈ C, φ v ∈ Ideal.span {ϖ ^ n}) → ϖ ^ (k + min n c) ∣ ϖ ^ c * φ d) :
    ∃ (lam lam' : Fin r → O), lam' ∈ C ∧ ϖ ^ c • d - ϖ ^ (k + c) • lam - ϖ ^ k • lam' ∈ F := by
  classical
  haveI := noZeroSMulDivisors_quot ϖ hϖ F hF
  haveI : Module.Free O ((Fin r → O) ⧸ F) := Module.free_of_finite_type_torsion_free'
  obtain ⟨m, snf⟩ := Submodule.smithNormalForm
    (Module.Free.chooseBasis O ((Fin r → O) ⧸ F)) (C.map F.mkQ)
  have hcoord : ∀ v ∈ C, ∀ j, ∃ t : Fin m → O,
      snf.bM.equivFun (F.mkQ v) j = ∑ l, t l * (snf.a l * (if snf.f l = j then (1 : O) else 0)) := by
    intro v hv j
    have hx : F.mkQ v ∈ C.map F.mkQ := Submodule.mem_map_of_mem hv
    obtain ⟨t, e⟩ : ∃ t : Fin m → O, F.mkQ v = ∑ l, t l • (snf.a l • snf.bM (snf.f l)) := by
      refine ⟨snf.bN.repr ⟨F.mkQ v, hx⟩, ?_⟩
      have h1 := congrArg Subtype.val (snf.bN.sum_repr ⟨F.mkQ v, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul, snf.snf] at h1
      exact h1.symm
    refine ⟨t, ?_⟩
    rw [e]
    simp only [map_sum, map_smul, Module.Basis.equivFun_self, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply]
  let Φ : _ → (Fin r → O) →ₗ[O] O := fun j =>
    LinearMap.proj j ∘ₗ snf.bM.equivFun.toLinearMap ∘ₗ F.mkQ
  have hΦ : ∀ j v, Φ j v = snf.bM.equivFun (F.mkQ v) j := fun j v => rfl
  have hΦF : ∀ j, ∀ v ∈ F, Φ j v = 0 := fun j v hv => by
    rw [hΦ, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero F).mpr hv, map_zero]
    rfl
  have hj : ∀ j, ∃ l μ : O, ϖ ^ c * snf.bM.equivFun (F.mkQ d) j = ϖ ^ (k + c) * l + ϖ ^ k * μ ∧
      μ • snf.bM j ∈ C.map F.mkQ := by
    intro j
    by_cases hjr : ∃ i, snf.f i = j
    · obtain ⟨i, rfl⟩ := hjr
      have hai : snf.a i ≠ 0 := by
        intro h0
        have h1 := snf.snf i
        rw [h0, zero_smul] at h1
        exact snf.bN.ne_zero i (Subtype.ext h1)
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hai hϖ
      have hC : ∀ v ∈ C, Φ (snf.f i) v ∈ Ideal.span {ϖ ^ n} := by
        intro v hv
        obtain ⟨t, ht⟩ := hcoord v hv (snf.f i)
        rw [hΦ, ht, Finset.sum_eq_single i]
        · rw [if_pos rfl, mul_one, hu]
          exact Ideal.mem_span_singleton'.mpr ⟨t i * u, by ring⟩
        · intro l _ hl
          rw [if_neg (fun h => hl (snf.f.injective h)), mul_zero, mul_zero]
        · intro h
          exact absurd (Finset.mem_univ i) h
      have key := hkey (Φ (snf.f i)) n (hΦF _) hC
      rw [hΦ] at key
      rcases le_or_gt c n with hcn | hnc
      · rw [min_eq_right hcn] at key
        obtain ⟨w, hw⟩ := key
        exact ⟨w, 0, by linear_combination hw, by simp⟩
      · rw [min_eq_left hnc.le] at key
        obtain ⟨w, hw⟩ := key
        refine ⟨0, ϖ ^ n * w, by rw [hw]; ring, ?_⟩
        have hs : ((u⁻¹ : Oˣ) : O) * w * ((u : O) * ϖ ^ n) = ϖ ^ n * w := by
          linear_combination (w * ϖ ^ n) * u.inv_mul
        have e : (ϖ ^ n * w) • snf.bM (snf.f i) = (((u⁻¹ : Oˣ) : O) * w) • (snf.bN i : _) := by
          rw [snf.snf i, smul_smul, hu, hs]
        rw [e]
        exact Submodule.smul_mem _ _ (snf.bN i).2
    · have hC : ∀ v ∈ C, Φ j v ∈ Ideal.span {ϖ ^ c} := by
        intro v hv
        obtain ⟨t, ht⟩ := hcoord v hv j
        have h0 : ∀ l, (if snf.f l = j then (1 : O) else 0) = 0 := fun l =>
          if_neg (fun h => hjr ⟨l, h⟩)
        rw [hΦ, ht]
        simp [h0]
      have key := hkey (Φ j) c (hΦF _) hC
      rw [hΦ, min_self] at key
      obtain ⟨w, hw⟩ := key
      exact ⟨w, 0, by linear_combination hw, by simp⟩
  choose L M hLM using hj
  have hq₂ : snf.bM.equivFun.symm M ∈ C.map F.mkQ := by
    rw [Module.Basis.equivFun_symm_apply]
    exact Submodule.sum_mem _ (fun j _ => (hLM j).2)
  obtain ⟨lam', hlam'C, hlam'⟩ := Submodule.mem_map.mp hq₂
  obtain ⟨lam, hlam⟩ := F.mkQ_surjective (snf.bM.equivFun.symm L)
  refine ⟨lam, lam', hlam'C, ?_⟩
  have hlam2 : (Submodule.Quotient.mk lam : (Fin r → O) ⧸ F) = snf.bM.equivFun.symm L := hlam
  have hlam2' : (Submodule.Quotient.mk lam' : (Fin r → O) ⧸ F) = snf.bM.equivFun.symm M := hlam'
  rw [← Submodule.Quotient.mk_eq_zero F]
  apply snf.bM.equivFun.injective
  rw [map_zero]
  funext j
  have h1 := (hLM j).1
  rw [Submodule.mkQ_apply] at h1
  simp only [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, map_sub, map_smul,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hlam2, hlam2',
    LinearEquiv.apply_symm_apply]
  linear_combination h1

end Decomp

section Main

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r : ℕ}

theorem ne_zero_of_unitDist (ϖ : O) (hϖ : Irreducible ϖ) (d : ℕ) (p : PowerSeries O)
    (hp : UnitDist ϖ d p) : p ≠ 0 := by
  obtain ⟨u, E, hu, hE, -, rfl⟩ := hp
  have hE0 : (E : PowerSeries O) ≠ 0 := by
    rw [Ne, Polynomial.coe_eq_zero_iff]
    exact hE.monic.ne_zero
  exact mul_ne_zero hu.ne_zero hE0

theorem coord_levelRel (ϖ : O) (N k : ℕ) (y : Fin r → PowerSeries O) (L : PowerSeries O)
    (d : Fin r → O) (i : Fin r) :
    (C (ϖ ^ N) • (C (ϖ ^ k) • y - L • cst d)) i = C (ϖ ^ N) * (C (ϖ ^ k) * y i - L * C (d i)) := by
  simp [cst, smul_eq_mul]

theorem dvd_of_levelRel (ϖ : O) (P L Y : PowerSeries O) (δ : O) (N k : ℕ) (hPL : P ∣ L)
    (hs : IsSat ϖ P) (h : P ∣ C (ϖ ^ N) * (C (ϖ ^ k) * Y - L * C δ)) : P ∣ Y := by
  apply hs (N + k) Y
  have e : C (ϖ ^ (N + k)) * Y = C (ϖ ^ N) * (C (ϖ ^ k) * Y - L * C δ) + C (ϖ ^ N) * C δ * L := by
    rw [pow_add, map_mul]
    ring
  rw [e]
  exact dvd_add h (dvd_mul_of_dvd_right hPL _)

theorem linExt_levelRel (g : (Fin r → O) →ₗ[O] O) (ϖ : O) (N k : ℕ) (y : Fin r → PowerSeries O)
    (L : PowerSeries O) (d : Fin r → O) :
    linExt g (C (ϖ ^ N) • (C (ϖ ^ k) • y - L • cst d)) =
      C (ϖ ^ N) * (C (ϖ ^ k) * linExt g y - L * C (g d)) := by
  rw [map_smul, map_sub, map_smul, map_smul, linExt_cst]
  simp only [smul_eq_mul]

theorem linExt_eq_zero_of_mem_ext (g : (Fin r → O) →ₗ[O] O) (V : Submodule O (Fin r → O))
    (hg : ∀ v ∈ V, g v = 0) (u : Fin r → PowerSeries O) (hu : u ∈ ext V) : linExt g u = 0 := by
  have h1 := linExt_mem_of_mem_ext g V 0 (fun v hv => by rw [hg v hv]; exact Submodule.zero_mem _) u hu
  simpa using h1

theorem key_scalar (ϖ : O) (hϖ : Irreducible ϖ) (P₀ P₁ G R₀ α β g h z₀ : PowerSeries O)
    (c k n N : ℕ) (δ : O) (hs : IsSat ϖ P₀) (hcop : CoprimeRat ϖ P₀ R₀) (hG : G ≠ 0)
    (hα : P₁ = C (ϖ ^ c) * α + P₀ * β) (hnot : P₁ ∉ Ideal.span {C (ϖ ^ (c + 1)), P₀})
    (hrel : C (ϖ ^ N) * (C (ϖ ^ k) * (G * R₀ * (C (ϖ ^ n) * g + P₁ * h)) - G * R₀ * P₁ * C δ) =
      G * P₀ * z₀) :
    ϖ ^ (k + min n c) ∣ ϖ ^ c * δ := by
  apply pow_dvd_of_mul_C_mem ϖ hϖ P₀ P₁ hs c (k + min n c) δ hnot
  have h1 : C (ϖ ^ N) * (R₀ * (C (ϖ ^ k) * (C (ϖ ^ n) * g + P₁ * h) - P₁ * C δ)) = P₀ * z₀ := by
    apply mul_left_cancel₀ hG
    linear_combination hrel
  have h2 : P₀ ∣ R₀ * (C (ϖ ^ N) * (C (ϖ ^ k) * (C (ϖ ^ n) * g + P₁ * h) - P₁ * C δ)) :=
    ⟨z₀, by linear_combination h1⟩
  obtain ⟨t, ht⟩ := dvd_of_dvd_mul_coprimeRat ϖ P₀ R₀ _ hs hcop N h2
  rw [Ideal.mem_span_pair]
  obtain ⟨e₁, he₁⟩ : ∃ e, n = min n c + e := ⟨n - min n c, by omega⟩
  obtain ⟨e₂, he₂⟩ : ∃ e, c = min n c + e := ⟨c - min n c, by omega⟩
  have hn' : C (ϖ ^ n) = C (ϖ ^ min n c) * C (ϖ ^ e₁) := by
    rw [← map_mul, ← pow_add, ← he₁]
  have hc' : C (ϖ ^ c) = C (ϖ ^ min n c) * C (ϖ ^ e₂) := by
    rw [← map_mul, ← pow_add, ← he₂]
  have hk : C (ϖ ^ (k + min n c)) = C (ϖ ^ k) * C (ϖ ^ min n c) := by
    rw [pow_add, map_mul]
  refine ⟨C (ϖ ^ e₁) * g + C (ϖ ^ e₂) * α * h, β * C (ϖ ^ k) * h - t, ?_⟩
  linear_combination (C (ϖ ^ e₁) * g + C (ϖ ^ e₂) * α * h) * hk + ht
    - (C (ϖ ^ k) * g) * hn' - (C (ϖ ^ k) * h) * hα - (C (ϖ ^ k) * h * α) * hc'

end Main

section Proof

set_option maxHeartbeats 4000000 in
theorem descent_estimate_up_down : MUD := by
  intro O _ _ _ ϖ hϖ ℓ ell r p H b kind V hℓ hPS hsat hub s₀ s₁ h01 h1ell hk1 hk0 hthin c α β
    hαβ hnot y
  have h0ell : s₀ < ell := lt_trans h01 h1ell
  have hs01 : s₀ ≠ s₁ := Nat.ne_of_lt h01
  have hUD := hPS.1
  have hCop := hPS.2
  have hb1 : b s₁ ≤ H s₁ := hub s₁ h1ell hk1
  have hSat : ∀ s < ell, ∀ k, IsSat ϖ (p s ^ k) := fun s hs k =>
    isSat_pow_of_unitDist ϖ hϖ _ (p s) (hUD s hs) k
  have hcopPow : ∀ s < ell, ∀ t < ell, s ≠ t → ∀ m n, CoprimeRat ϖ (p s ^ m) (p t ^ n) :=
    fun s hs t ht hst m n => coprimeRat₂_pow_pow ϖ _ _ (hCop s hs t ht hst) m n

  set Q1 := ∏ s ∈ (Finset.range ell).erase s₁, p s ^ H s with hQ1
  have hLam : abelian₂ p H ell = p s₁ ^ H s₁ * Q1 :=
    (Finset.mul_prod_erase _ _ (Finset.mem_range.2 h1ell)).symm
  have hLL : LamLess p H ell s₁ (b s₁) = p s₁ ^ (H s₁ - b s₁) * Q1 := rfl
  have hpow1 : p s₁ ^ H s₁ = p s₁ ^ (H s₁ - b s₁) * p s₁ ^ b s₁ := by
    rw [← pow_add, Nat.sub_add_cancel hb1]
  set P : ℕ → PowerSeries O := fun s => p s ^ (if s = s₁ then H s₁ - b s₁ else H s) with hP
  have hPne : ∀ s, s ≠ s₁ → P s = p s ^ H s := fun s hs => by simp [hP, hs]
  have hLLprod : LamLess p H ell s₁ (b s₁) = ∏ s ∈ Finset.range ell, P s := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.2 h1ell), hLL]
    congr 1
    · simp [hP]
    · exact Finset.prod_congr rfl fun s hs => (hPne s (Finset.ne_of_mem_erase hs)).symm
  set R₀ := ∏ s ∈ (Finset.range ell).erase s₀, P s with hR₀
  have hLL0 : LamLess p H ell s₁ (b s₁) = p s₀ ^ H s₀ * R₀ := by
    rw [hLLprod, ← Finset.mul_prod_erase _ _ (Finset.mem_range.2 h0ell), hPne s₀ hs01]
  have hcopR₀ : CoprimeRat ϖ (p s₀ ^ b s₀) R₀ := by
    apply coprimeRat₂_prod_right
    intro t ht
    have ht' := Finset.mem_range.1 (Finset.mem_of_mem_erase ht)
    exact hcopPow s₀ h0ell t ht' (Finset.ne_of_mem_erase ht).symm _ _
  have hcopQ1 : CoprimeRat ϖ (p s₁ ^ b s₁) Q1 := by
    apply coprimeRat₂_prod_right
    intro t ht
    have ht' := Finset.mem_range.1 (Finset.mem_of_mem_erase ht)
    exact hcopPow s₁ h1ell t ht' (Finset.ne_of_mem_erase ht).symm _ _
  have hLamE : abelian₂ p H ell = p s₀ ^ H s₀ * R₀ * p s₁ ^ b s₁ := by
    rw [← hLL0, hLam, hLL, hpow1]; ring
  have hdvdLam : ∀ s < ell, p s ^ H s ∣ abelian₂ p H ell := fun s hs =>
    Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hs)
  have hdvdLL : ∀ s < ell, s ≠ s₁ → ∃ X, LamLess p H ell s₁ (b s₁) = p s ^ H s * X := by
    intro s hs hne
    rw [hLLprod, ← hPne s hne]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hs)
  have hG : p s₀ ^ H s₀ ≠ 0 := pow_ne_zero _ (ne_zero_of_unitDist ϖ hϖ _ _ (hUD s₀ h0ell))
  constructor
  ·
    intro hII
    choose! dd kk hdk using hII

    have hdivY : ∀ s ∈ Finset.range ell, ∀ i, P s ∣ y i := by
      intro s hs i
      have hs' := Finset.mem_range.1 hs
      have h := hdk s hs'
      by_cases h1 : s = s₁
      · subst h1
        rw [hk1] at h
        obtain ⟨N, c', z, -, heq⟩ := h
        have hi := congrFun heq i
        rw [coord_levelRel] at hi
        have hPs : P s = p s ^ (H s - b s) := by simp [hP]
        rw [hPs]
        refine dvd_of_levelRel ϖ (p s ^ (H s - b s)) (abelian₂ p H ell) (y i) (dd s i) N (kk s) ?_
          (hSat _ hs' _) ⟨c' i + p s ^ b s * z i, ?_⟩
        · rw [hLam, hpow1]; exact Dvd.dvd.mul_right (dvd_mul_right _ _) _
        · rw [hi]; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; rw [hpow1]; ring
      · rw [hPne s h1]
        by_cases h0 : s = s₀
        · subst h0
          rw [hk0] at h
          obtain ⟨N, c', z, -, heq⟩ := h
          have hi := congrFun heq i
          rw [coord_levelRel] at hi
          refine dvd_of_levelRel ϖ (p s ^ H s) (abelian₂ p H ell) (y i) (dd s i) N (kk s)
            (hdvdLam s hs') (hSat _ hs' _) ⟨c' i + p s ^ b s * z i, ?_⟩
          rw [hi]; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; rw [pow_add]; ring
        · rw [hthin s hs' h0 h1] at h
          obtain ⟨N, z, heq⟩ := h
          have hi := congrFun heq i
          rw [coord_levelRel] at hi
          refine dvd_of_levelRel ϖ (p s ^ H s) (abelian₂ p H ell) (y i) (dd s i) N (kk s)
            (hdvdLam s hs') (hSat _ hs' _) ⟨z i, ?_⟩
          rw [hi]; simp only [Pi.smul_apply, smul_eq_mul]

    have hdivLL : ∀ i, LamLess p H ell s₁ (b s₁) ∣ y i := by
      intro i
      rw [hLLprod]
      refine prod_dvd_of_coprimeRat ϖ _ P (fun s hs => hSat s (Finset.mem_range.1 hs) _) ?_ _
        (fun s hs => hdivY s hs i)
      intro s hs t ht hst
      exact hcopPow s (Finset.mem_range.1 hs) t (Finset.mem_range.1 ht) hst _ _
    choose W hW using hdivLL
    have hyW : y = LamLess p H ell s₁ (b s₁) • W := funext fun i => by
      rw [hW i]; rfl

    obtain ⟨f, hfC, hfid⟩ := exists_proj_of_saturated ϖ hϖ (V s₁) (hsat s₁ h1ell)
    have hfW : ∀ j, p s₁ ^ b s₁ ∣ vecExt f W j := by
      intro j
      have h := hdk s₁ h1ell
      rw [hk1] at h
      obtain ⟨N, c', z, hc', heq⟩ := h
      have hj := congrArg (linExt (LinearMap.proj j ∘ₗ f)) heq
      rw [linExt_levelRel, map_add, map_smul, map_smul,
        linExt_eq_zero_of_mem_ext _ (V s₁) (fun v hv => by simp [hfC v hv]) c' hc', hyW,
        map_smul, hLam, hLL] at hj
      have hj' : p s₁ ^ (H s₁ - b s₁) * (Q1 * (C (ϖ ^ (N + kk s₁)) * vecExt f W j)) =
          p s₁ ^ (H s₁ - b s₁) * (p s₁ ^ b s₁ *
            (linExt (LinearMap.proj j ∘ₗ f) z + C (ϖ ^ N) * Q1 * C ((LinearMap.proj j ∘ₗ f) (dd s₁)))) := by
        simp only [smul_eq_mul] at hj
        rw [pow_add, map_mul]
        have : vecExt f W j = linExt (LinearMap.proj j ∘ₗ f) W := rfl
        rw [this]
        rw [hpow1] at hj
        linear_combination hj
      have hne : p s₁ ^ (H s₁ - b s₁) ≠ 0 :=
        pow_ne_zero _ (ne_zero_of_unitDist ϖ hϖ _ _ (hUD s₁ h1ell))
      exact dvd_of_dvd_mul_coprimeRat ϖ _ Q1 _ (hSat s₁ h1ell _) hcopQ1 (N + kk s₁)
        ⟨_, mul_left_cancel₀ hne hj'⟩
    choose zW hzW using hfW
    set u := vecExt (LinearMap.id - f) W with hu
    have huC : u ∈ ext (V s₁) := vecExt_mem_ext _ _ (fun v => by simpa using hfid v) W
    have hWu : W = u + p s₁ ^ b s₁ • zW := by
      funext j
      have : u j = W j - vecExt f W j := by
        simp only [hu, vecExt, LinearMap.comp_sub, LinearMap.comp_id, linExt_sub, linExt_proj]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, this, hzW j]
      ring

    have h0 := hdk s₀ h0ell
    rw [hk0] at h0
    obtain ⟨N₀, c₀, z₀, hc₀, heq₀⟩ := h0
    have hkey : ∀ (φ : (Fin r → O) →ₗ[O] O) (n : ℕ), (∀ v ∈ V s₀, φ v = 0) →
        (∀ v ∈ V s₁, φ v ∈ Ideal.span {ϖ ^ n}) →
        ϖ ^ (kk s₀ + min n c) ∣ ϖ ^ c * φ (dd s₀) := by
      intro φ n hφF hφC
      have hj := congrArg (linExt φ) heq₀
      rw [linExt_levelRel, map_add, map_smul, map_smul,
        linExt_eq_zero_of_mem_ext _ (V s₀) hφF c₀ hc₀, hyW, map_smul, hWu, map_add, map_smul]
        at hj
      obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp (linExt_mem_of_mem_ext φ (V s₁) _ hφC u huC)
      rw [← hg] at hj
      refine key_scalar ϖ hϖ (p s₀ ^ b s₀) (p s₁ ^ b s₁) (p s₀ ^ H s₀) R₀ α β g (linExt φ zW)
        (linExt φ z₀) c (kk s₀) n N₀ (φ (dd s₀)) (hSat s₀ h0ell _) hcopR₀ hG hαβ hnot ?_
      simp only [smul_eq_mul] at hj
      rw [hLL0, hLamE, pow_add] at hj
      linear_combination hj

    obtain ⟨lam, lam', hlam'C, hD⟩ :=
      exists_const_decomp ϖ hϖ (V s₀) (V s₁) (hsat s₀ h0ell) c (kk s₀) (dd s₀) hkey

    refine ⟨lam, lam', y - abelian₂ p H ell • cst lam - (α * LamLess p H ell s₁ (b s₁)) • cst lam',
      hlam'C, ?_, by abel⟩
    intro s hs
    by_cases h1 : s = s₁
    · subst h1
      have h := hdk s hs
      rw [hk1] at h ⊢
      obtain ⟨N, c', z, hc', heq⟩ := h
      refine ⟨N + kk s, c' - (C (ϖ ^ (N + kk s)) * α * Q1) • cst lam',
        fun i => z i + C (ϖ ^ N) * Q1 * C (dd s i) - C (ϖ ^ (N + kk s)) * Q1 * C (lam i), ?_, ?_⟩
      · exact Submodule.sub_mem _ hc' (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hlam'C, rfl⟩))
      · funext i
        have hi := congrFun heq i
        rw [coord_levelRel] at hi
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cst] at hi ⊢
        rw [hLam] at hi ⊢
        rw [hLL, pow_add, map_mul]
        linear_combination hi
    · by_cases h0 : s = s₀
      · subst h0
        have h := hdk s hs
        rw [hk0] at h ⊢
        obtain ⟨N, c', z, hc', heq⟩ := h
        refine ⟨N + kk s + c,
          C (ϖ ^ c) • c' + (C (ϖ ^ N) * R₀ * p s₁ ^ b s₁) •
            cst (ϖ ^ c • dd s - ϖ ^ (kk s + c) • lam - ϖ ^ kk s • lam'),
          fun i => C (ϖ ^ c) * z i + C (ϖ ^ (N + kk s)) * R₀ * β * C (lam' i), ?_, ?_⟩
        · exact Submodule.add_mem _ (Submodule.smul_mem _ _ hc')
            (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hD, rfl⟩))
        · funext i
          have hi := congrFun heq i
          rw [coord_levelRel] at hi
          simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cst, map_sub,
            map_mul, map_pow] at hi ⊢
          rw [hLamE] at hi ⊢
          rw [hLL0]
          simp only [pow_add, map_mul, map_pow] at hi ⊢
          have hαβ' := hαβ
          rw [map_pow] at hαβ'
          linear_combination (C ϖ ^ c) * hi +
            p s ^ H s * C ϖ ^ N * R₀ * C ϖ ^ kk s * C (lam' i) * hαβ'
      · have hs' := hthin s hs h0 h1
        have h := hdk s hs
        rw [hs'] at h ⊢
        obtain ⟨N, z, heq⟩ := h
        obtain ⟨X, hX⟩ := hdvdLL s hs h1
        obtain ⟨Y, hY⟩ := hdvdLam s hs
        refine ⟨N + kk s, fun i => z i + C (ϖ ^ N) * Y * C (dd s i) -
          C (ϖ ^ (N + kk s)) * Y * C (lam i) - C (ϖ ^ (N + kk s)) * α * X * C (lam' i), ?_⟩
        funext i
        have hi := congrFun heq i
        rw [coord_levelRel] at hi
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cst] at hi ⊢
        rw [hY] at hi ⊢
        rw [hX, pow_add, map_mul]
        linear_combination hi
  ·
    rintro ⟨lam, lam', ν, hlam'C, hν, rfl⟩
    intro s hs
    by_cases h1 : s = s₁
    · subst h1
      refine ⟨0, 0, ?_⟩
      have h := hν s hs
      rw [hk1] at h ⊢
      obtain ⟨N, c', z, hc', heq⟩ := h
      refine ⟨N, c' + (C (ϖ ^ N) * α * Q1) • cst lam', fun i => z i + C (ϖ ^ N) * Q1 * C (lam i),
        Submodule.add_mem _ hc' (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hlam'C, rfl⟩)), ?_⟩
      funext i
      have hi := congrFun heq i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cst, Pi.zero_apply, map_zero, pow_zero,
        map_one, one_mul, mul_zero, sub_zero] at hi ⊢
      rw [hLam, hLL]
      linear_combination hi
    · by_cases h0 : s = s₀
      · subst h0
        refine ⟨ϖ ^ c • lam + lam', c, ?_⟩
        have h := hν s hs
        rw [hk0] at h ⊢
        obtain ⟨N, c', z, hc', heq⟩ := h
        refine ⟨N, C (ϖ ^ c) • c', fun i => C (ϖ ^ c) * z i - C (ϖ ^ N) * β * R₀ * C (lam' i),
          Submodule.smul_mem _ _ hc', ?_⟩
        funext i
        have hi := congrFun heq i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cst, map_add, map_mul]
          at hi ⊢
        rw [hLamE, hLL0]
        rw [pow_add] at hi ⊢
        linear_combination (C (ϖ ^ c)) * hi - C (ϖ ^ N) * p s ^ H s * R₀ * C (lam' i) * hαβ
      · have hs' := hthin s hs h0 h1
        refine ⟨0, 0, ?_⟩
        have h := hν s hs
        rw [hs'] at h ⊢
        obtain ⟨N, z, heq⟩ := h
        obtain ⟨X, hX⟩ := hdvdLL s hs h1
        obtain ⟨Y, hY⟩ := hdvdLam s hs
        refine ⟨N, fun i => z i + C (ϖ ^ N) * Y * C (lam i) + C (ϖ ^ N) * α * X * C (lam' i), ?_⟩
        funext i
        have hi := congrFun heq i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cst, Pi.zero_apply, map_zero, pow_zero,
          map_one, one_mul, mul_zero, sub_zero] at hi ⊢
        rw [hY, hX]
        linear_combination hi

end Proof

end Formalism.ExponentWindows
