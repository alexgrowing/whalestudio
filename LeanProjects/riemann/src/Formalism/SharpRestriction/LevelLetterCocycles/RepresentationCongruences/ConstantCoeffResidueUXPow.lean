import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ConstantLeRpowOfThreeLe

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open PowerSeries

section ContDHelpers

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem ContD.dvd_iff_map_eq_zero {ϖ : O} (hϖ : Irreducible ϖ) (f : O⟦X⟧) :
    C ϖ ∣ f ↔ f.map (IsLocalRing.residue O) = 0 := by
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  constructor
  · rintro ⟨g, rfl⟩
    have h0 : IsLocalRing.residue O ϖ = 0 :=
      (IsLocalRing.residue_eq_zero_iff ϖ).2 (hmax ▸ Ideal.mem_span_singleton_self ϖ)
    rw [map_mul, PowerSeries.map_C, h0, map_zero, zero_mul]
  · intro h
    have hc : ∀ n, ∃ c : O, coeff n f = ϖ * c := by
      intro n
      have h1 : IsLocalRing.residue O (coeff n f) = 0 := by
        have := congrArg (coeff n) h
        simpa [PowerSeries.coeff_map] using this
      rw [IsLocalRing.residue_eq_zero_iff, hmax, Ideal.mem_span_singleton] at h1
      obtain ⟨c, hc⟩ := h1
      exact ⟨c, hc⟩
    choose c hc using hc
    refine ⟨PowerSeries.mk c, ?_⟩
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc n]

theorem ContD.C_ne_zero {ϖ : O} (hϖ : Irreducible ϖ) : (C ϖ : O⟦X⟧) ≠ 0 := by
  intro h
  apply hϖ.ne_zero
  have := congrArg constantCoeff h
  simpa using this

theorem ContD.prime_C {ϖ : O} (hϖ : Irreducible ϖ) : Prime (C ϖ : O⟦X⟧) := by
  refine ⟨ContD.C_ne_zero hϖ, fun hu => hϖ.not_isUnit ?_, fun a b hab => ?_⟩
  · simpa using hu.map (constantCoeff (R := O))
  · rw [ContD.dvd_iff_map_eq_zero hϖ, map_mul, mul_eq_zero] at hab
    rcases hab with h | h
    · exact Or.inl ((ContD.dvd_iff_map_eq_zero hϖ a).2 h)
    · exact Or.inr ((ContD.dvd_iff_map_eq_zero hϖ b).2 h)

theorem ContD.not_dvd_of_isDist {ϖ : O} (hϖ : Irreducible ϖ) {g : O⟦X⟧} (hg : IsDist g) :
    ¬ C ϖ ∣ g := fun h => hg ((ContD.dvd_iff_map_eq_zero hϖ g).1 h)

theorem ContD.eq_zero_of_forall_pow_dvd {ϖ : O} (hϖ : Irreducible ϖ) (F : O⟦X⟧)
    (h : ∀ n : ℕ, C ϖ ^ n ∣ F) : F = 0 := by
  ext m
  rw [map_zero]
  by_contra hne
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
  obtain ⟨G, hG⟩ := h (n + 1)
  have h1 : coeff m F = ϖ ^ (n + 1) * coeff m G := by
    rw [hG, ← map_pow, PowerSeries.coeff_C_mul]
  rw [hu, pow_succ] at h1
  have hϖn : ϖ ^ n ≠ 0 := pow_ne_zero _ hϖ.ne_zero
  have h2 : (u : O) = ϖ * coeff m G := by
    apply mul_right_cancel₀ hϖn
    linear_combination h1
  apply hϖ.not_isUnit
  apply isUnit_of_mul_isUnit_left (y := coeff m G)
  rw [← h2]
  exact u.isUnit

theorem ContD.descent {ϖ : O} (hϖ : Irreducible ϖ) (S : O⟦X⟧ → Prop)
    (h0 : ∀ F, S F → F.map (IsLocalRing.residue O) = 0)
    (h1 : ∀ F, S (C ϖ * F) → S F) (F : O⟦X⟧) (hF : S F) : F = 0 := by
  suffices key : ∀ n : ℕ, ∀ G, S G → C ϖ ^ n ∣ G from
    ContD.eq_zero_of_forall_pow_dvd hϖ F (fun n => key n F hF)
  intro n
  induction n with
  | zero => intro G _; simp
  | succ n ih =>
    intro G hG
    obtain ⟨G', rfl⟩ := (ContD.dvd_iff_map_eq_zero hϖ G).2 (h0 G hG)
    obtain ⟨Q, hQ⟩ := ih G' (h1 G' hG)
    exact ⟨Q, by rw [hQ, pow_succ]; ring⟩

theorem ContD.dvd_of_dvd_C_mul {ϖ : O} (hϖ : Irreducible ϖ) {g : O⟦X⟧} (hg : ¬ C ϖ ∣ g) (N : ℕ)
    (F : O⟦X⟧) (h : g ^ N ∣ C ϖ * F) : g ^ N ∣ F := by
  obtain ⟨H, hH⟩ := h
  have hp := ContD.prime_C hϖ
  have hgN : ¬ C ϖ ∣ g ^ N := fun hd => hg (hp.dvd_of_dvd_pow hd)
  obtain ⟨K, rfl⟩ := (hp.dvd_or_dvd ⟨F, hH.symm⟩).resolve_left hgN
  refine ⟨K, mul_left_cancel₀ (ContD.C_ne_zero hϖ) ?_⟩
  rw [hH]
  ring

theorem ContD.pow_dvd_of_dvd_mul {ϖ : O} (hϖ : Irreducible ϖ) {g : O⟦X⟧} (hg : ¬ C ϖ ∣ g) (s : ℕ) :
    ∀ G : O⟦X⟧, C ϖ ^ s ∣ g * G → C ϖ ^ s ∣ G := by
  induction s with
  | zero => intro G _; simp
  | succ s ih =>
    intro G hG
    have hp := ContD.prime_C hϖ
    have h1 : C ϖ ∣ G :=
      (hp.dvd_or_dvd (dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero s)) hG)).resolve_left hg
    obtain ⟨G', rfl⟩ := h1
    have h2 : C ϖ ^ s ∣ g * G' := by
      obtain ⟨Q, hQ⟩ := hG
      refine ⟨Q, mul_left_cancel₀ (ContD.C_ne_zero hϖ) ?_⟩
      rw [pow_succ] at hQ
      linear_combination hQ
    obtain ⟨R, hR⟩ := ih G' h2
    exact ⟨R, by rw [hR, pow_succ]; ring⟩

theorem ContD.eq_zero_of_forall_dvd_pow {ϖ : O} (hϖ : Irreducible ϖ) {g : O⟦X⟧} (hg : ¬ C ϖ ∣ g)
    (hg0 : constantCoeff (g.map (IsLocalRing.residue O)) = 0) (F : O⟦X⟧)
    (hF : ∀ N : ℕ, g ^ N ∣ F) : F = 0 := by
  refine ContD.descent hϖ (fun F => ∀ N : ℕ, g ^ N ∣ F) ?_ ?_ F hF
  · intro F hF'
    have hX : (X : (IsLocalRing.ResidueField O)⟦X⟧) ∣ g.map (IsLocalRing.residue O) :=
      PowerSeries.X_dvd_iff.2 hg0
    ext n
    have h1 : (X : (IsLocalRing.ResidueField O)⟦X⟧) ^ (n + 1) ∣ F.map (IsLocalRing.residue O) := by
      obtain ⟨Q, hQ⟩ := hF' (n + 1)
      refine dvd_trans (pow_dvd_pow_of_dvd hX _) ⟨Q.map (IsLocalRing.residue O), ?_⟩
      rw [hQ, map_mul, map_pow]
    rw [map_zero]
    exact PowerSeries.X_pow_dvd_iff.1 h1 n (Nat.lt_succ_self n)
  · intro F hF' N
    exact ContD.dvd_of_dvd_C_mul hϖ hg N F (hF' N)

theorem ContD.m5 {R : Type*} [CommRing R] (x x' t : R) (a s : ℕ) (hs : 1 ≤ s)
    (h : x - x' ∈ Ideal.span {t}) : x ^ (a + s - 1) ∈ Ideal.span {x' ^ a, t ^ s} := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h
  have hx : x = x' + (x - x') := by ring
  rw [hx]
  apply Ideal.add_pow_mem_of_pow_mem_of_le (m := a) (n := s)
  · exact Ideal.subset_span (by simp)
  · rw [← hy, mul_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · omega

theorem ContD.mem_iff_le (ϖ : O) (g f : O⟦X⟧) (k : ℕ) :
    f ∈ Ideal.span {C ϖ ^ k, g} ↔ (k : ℕ∞) ≤ cont ϖ g f := by
  show f ∈ Ideal.span {C ϖ ^ k, g} ↔
    (k : ℕ∞) ≤ ⨆ (j : ℕ) (_ : f ∈ Ideal.span {C ϖ ^ j, g}), (j : ℕ∞)
  constructor
  · intro h
    exact le_iSup₂ (f := fun (j : ℕ) (_ : f ∈ Ideal.span {C ϖ ^ j, g}) => (j : ℕ∞)) k h
  · intro h
    by_contra hf
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hf
      have h1 : C ϖ ^ 0 ∈ Ideal.span {C ϖ ^ 0, g} := Ideal.subset_span (by simp)
      have h2 := Ideal.mul_mem_left _ f h1
      rwa [pow_zero, mul_one] at h2
    have hle : (⨆ (j : ℕ) (_ : f ∈ Ideal.span {C ϖ ^ j, g}), (j : ℕ∞)) ≤ ((k - 1 : ℕ) : ℕ∞) := by
      apply iSup₂_le
      intro j hj
      have hjk : j < k := by
        by_contra hjk
        push_neg at hjk
        apply hf
        have hsub : Ideal.span {C ϖ ^ j, g} ≤ Ideal.span {C ϖ ^ k, g} := by
          rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
          refine ⟨?_, Ideal.subset_span (by simp)⟩
          rw [show C ϖ ^ j = C ϖ ^ (j - k) * C ϖ ^ k by rw [← pow_add, Nat.sub_add_cancel hjk]]
          exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
        exact hsub hj
      exact_mod_cast (by omega : j ≤ k - 1)
    have hlt : ((k - 1 : ℕ) : ℕ∞) < (k : ℕ∞) := by exact_mod_cast (by omega : k - 1 < k)
    exact absurd (lt_of_le_of_lt hle hlt) (not_lt.2 h)

theorem ContD.enat_le_of_forall {a b : ℕ∞} (h : ∀ k : ℕ, (k : ℕ∞) ≤ a → (k : ℕ∞) ≤ b) : a ≤ b := by
  by_contra hab
  push_neg at hab
  have hb : b ≠ ⊤ := ne_top_of_lt hab
  obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.1 hb
  have h1 : ((m + 1 : ℕ) : ℕ∞) ≤ a := by
    first
    | exact_mod_cast Order.add_one_le_of_lt hab
    | exact_mod_cast (ENat.add_one_le_iff (ENat.coe_ne_top m)).2 hab
  have h2 := h (m + 1) h1
  norm_cast at h2
  omega

theorem ContD.alg_C (ψ : O⟦X⟧ →ₐ[O] O⟦X⟧) (c : O) : ψ (C c) = C c := by
  first
  | exact ψ.commutes c
  | simpa using ψ.commutes c

end ContDHelpers

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
variable {l : ℕ} [Fact l.Prime] (P : PhiData O l)
variable {ϖ : O} (hϖ : Irreducible ϖ)
include hϖ

omit hϖ in
theorem PhiData.constantCoeff_residue_u_X_pow :
    constantCoeff ((P.u * X ^ l).map (IsLocalRing.residue O)) = 0 := by
  have hl : l ≠ 0 := Nat.Prime.ne_zero Fact.out
  simp [map_mul, map_pow, PowerSeries.map_X, hl, zero_pow]

omit hϖ in
theorem PhiData.ContD_a_ne : (P.u * X ^ l).map (IsLocalRing.residue O) ≠ 0 := by
  rw [map_mul, map_pow, PowerSeries.map_X]
  exact mul_ne_zero (P.hu.map (PowerSeries.map (IsLocalRing.residue O))).ne_zero
    (pow_ne_zero _ PowerSeries.X_ne_zero)

omit hϖ in
theorem PhiData.ContD_map_phiX :
    (P.φ X).map (IsLocalRing.residue O) = (P.u * X ^ l).map (IsLocalRing.residue O) := by
  rw [P.hred, PowerSeries.map_X, PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero P.constantCoeff_residue_u_X_pow)]

theorem PhiData.ContD_isDist_phiX : IsDist (P.φ X) := by
  show (P.φ X).map (IsLocalRing.residue O) ≠ 0
  rw [P.ContD_map_phiX]
  exact P.ContD_a_ne

omit hϖ in
theorem PhiData.ContD_wdeg_phiX : 1 ≤ wdeg (P.φ X) := by
  have hu0 : constantCoeff ((P.u).map (IsLocalRing.residue O)) ≠ 0 :=
    ((P.hu.map (PowerSeries.map (IsLocalRing.residue O))).map (constantCoeff (R := IsLocalRing.ResidueField O))).ne_zero
  have h1 : ((P.φ X).map (IsLocalRing.residue O)).order = (l : ℕ∞) := by
    rw [P.ContD_map_phiX, map_mul, map_pow, PowerSeries.map_X, PowerSeries.order_mul,
      PowerSeries.order_X_pow]
    have h2 : ((P.u).map (IsLocalRing.residue O)).order = 0 := by
      rw [show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) from rfl, PowerSeries.order_eq_nat]
      refine ⟨?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
      rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [h2, zero_add]
  show 1 ≤ ((P.φ X).map (IsLocalRing.residue O)).order.toNat
  rw [h1, ENat.toNat_coe]
  exact (Nat.Prime.one_lt Fact.out).le

theorem PhiData.ContD_eq_of_X (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (hX : h X = P.φ X) (f : O⟦X⟧) :
    h f = P.φ f := by
  have hpoly : ∀ p : Polynomial O, h (p : O⟦X⟧) = P.φ (p : O⟦X⟧) := by
    intro p
    have hc : h.comp (Polynomial.coeToPowerSeries.algHom O) =
        P.φ.comp (Polynomial.coeToPowerSeries.algHom O) := by
      apply Polynomial.algHom_ext
      simp [hX]
    have := congrArg (fun ψ : Polynomial O →ₐ[O] O⟦X⟧ => ψ p) hc
    simpa using this
  rw [← sub_eq_zero]
  refine ContD.eq_zero_of_forall_dvd_pow hϖ
    (ContD.not_dvd_of_isDist hϖ (P.ContD_isDist_phiX hϖ)) ?_ _ ?_
  · rw [P.ContD_map_phiX]
    exact P.constantCoeff_residue_u_X_pow
  · intro N
    have hdvd : (X : O⟦X⟧) ^ N ∣ f - (PowerSeries.trunc N f : O⟦X⟧) := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      simp [PowerSeries.coeff_trunc, hm]
    obtain ⟨r, hr⟩ := hdvd
    have hf : f = (PowerSeries.trunc N f : O⟦X⟧) + X ^ N * r := by rw [← hr]; ring
    rw [hf, map_add, map_add, map_mul, map_mul, map_pow, map_pow, hX, hpoly]
    exact ⟨h r - P.φ r, by ring⟩

theorem PhiData.exists_retraction :
    ∃ lam : O⟦X⟧ →ₗ[O] O⟦X⟧, (∀ a b : O⟦X⟧, lam (P.φ a * b) = a * lam b) ∧ (∀ a, lam (P.φ a) = a) := by
  have hD := P.ContD_wdeg_phiX
  obtain ⟨h, hX, -, hu⟩ := exists_weierstrass_substitution (P.φ X) (P.ContD_isDist_phiX hϖ) hD
  have hh : ∀ f, h f = P.φ f := P.ContD_eq_of_X hϖ h hX
  choose c hc using fun f => (hu f).exists
  have huniq : ∀ f d, f = ∑ i : Fin (wdeg (P.φ X)), X ^ (i : ℕ) * h (d i) → c f = d :=
    fun f d hd => (hu f).unique (hc f) hd
  let lam : O⟦X⟧ →ₗ[O] O⟦X⟧ :=
    { toFun := fun f => c f ⟨0, hD⟩
      map_add' := fun f g => by
        have := huniq (f + g) (fun i => c f i + c g i) (by
          simp only [map_add, mul_add, Finset.sum_add_distrib]
          rw [← hc f, ← hc g])
        exact congrFun this _
      map_smul' := fun r f => by
        have := huniq (r • f) (fun i => r • c f i) (by
          simp only [map_smul, mul_smul_comm]
          rw [← Finset.smul_sum, ← hc f])
        exact congrFun this _ }
  refine ⟨lam, ?_, ?_⟩
  · intro a b
    rw [← hh a]
    have := huniq (h a * b) (fun i => a * c b i) (by
      simp only [map_mul]
      conv_lhs => rw [hc b]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring)
    exact congrFun this _
  · intro a
    rw [← hh a]
    have := huniq (h a) (fun i => if (i : ℕ) = 0 then a else 0) (by
      rw [Finset.sum_eq_single ⟨0, hD⟩]
      · simp
      · intro b _ hb
        have : (b : ℕ) ≠ 0 := fun h0 => hb (Fin.ext h0)
        simp [this]
      · intro hn; exact absurd (Finset.mem_univ _) hn)
    have h2 := congrFun this ⟨0, hD⟩
    have h3 : c (h a) ⟨0, hD⟩ = a := by simpa using h2
    exact h3

theorem PhiData.DESC (f g : O⟦X⟧) (k : ℕ)
    (h : P.φ f ∈ Ideal.span {C ϖ ^ k, P.φ g}) : f ∈ Ideal.span {C ϖ ^ k, g} := by
  obtain ⟨lam, hlam1, hlam2⟩ := P.exists_retraction hϖ
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 h
  rw [Ideal.mem_span_pair]
  refine ⟨lam a, lam b, ?_⟩
  have e1 : a * C ϖ ^ k = P.φ (C ϖ ^ k) * a := by rw [map_pow, ContD.alg_C, mul_comm]
  have e2 : b * P.φ g = P.φ g * b := mul_comm _ _
  calc lam a * C ϖ ^ k + lam b * g = lam (P.φ (C ϖ ^ k) * a) + lam (P.φ g * b) := by
        rw [hlam1, hlam1]; ring
    _ = lam (a * C ϖ ^ k + b * P.φ g) := by rw [map_add, e1, e2]
    _ = lam (P.φ f) := by rw [hab]
    _ = f := hlam2 f

theorem PhiData.cont_phi_phi_eq {g : O⟦X⟧} (hg : IsDist g) (f : O⟦X⟧) :
    cont ϖ (P.φ g) (P.φ f) = cont ϖ g f := by
  apply le_antisymm
  · apply ContD.enat_le_of_forall
    intro k hk
    rw [← ContD.mem_iff_le] at hk ⊢
    exact P.DESC hϖ f g k hk
  · apply ContD.enat_le_of_forall
    intro k hk
    rw [← ContD.mem_iff_le] at hk ⊢
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 hk
    rw [Ideal.mem_span_pair]
    refine ⟨P.φ a, P.φ b, ?_⟩
    rw [← hab, map_add, map_mul, map_mul, map_pow, ContD.alg_C]

theorem PhiData.X_pow_mem_span_q_pow_l_pow (A' s : ℕ) (hs : 1 ≤ s) :
    (X : O⟦X⟧) ^ (A' + s - 1) ∈ Ideal.span {(X - C (l : O)) ^ A', C (l : O) ^ s} := ContD.m5 X (X - C (l : O)) (C (l : O)) A' s hs
    (by rw [sub_sub_cancel]; exact Ideal.mem_span_singleton_self _)

theorem PhiData.p_one_pow_mem_span_X_pow_mul_l_pow (A' s : ℕ) (hs : 1 ≤ s) :
    P.p 1 ^ (A' + s - 1) ∈ Ideal.span {(X : O⟦X⟧) ^ (l * A'), C (l : O) ^ s} := by
  have hl := (Fact.out : Nat.Prime l).one_lt
  have hp1 : P.p 1 = P.φ X := rfl
  have hφX : P.φ X = C (l : O) + P.u * (X - C (l : O)) * X ^ (l - 1) := by
    have h := P.hφ0
    rw [map_sub, P.φ_C_l] at h
    linear_combination h
  have hl1 : (X : O⟦X⟧) ^ l = X * X ^ (l - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hl.le]
  have hmem : P.p 1 - P.u * X ^ l ∈ Ideal.span {C (l : O)} := by
    rw [hp1, hφX, Ideal.mem_span_singleton']
    exact ⟨1 - P.u * X ^ (l - 1), by rw [hl1]; ring⟩
  have hm := ContD.m5 (P.p 1) (P.u * X ^ l) (C (l : O)) A' s hs hmem
  refine Ideal.span_le.2 ?_ hm
  rw [Set.insert_subset_iff, Set.singleton_subset_iff]
  refine ⟨?_, Ideal.subset_span (by simp)⟩
  rw [mul_pow, ← pow_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

theorem V2 {g : O⟦X⟧} (hg : IsDist g) (k B' s : ℕ) (hk : k ≤ B') (F : O⟦X⟧)
    (h : g ^ k * F ∈ Ideal.span {C ϖ ^ s, g ^ B'}) : F ∈ Ideal.span {C ϖ ^ s, g ^ (B' - k)} := by
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 h
  have hgk : ¬ C ϖ ∣ g ^ k := fun hd =>
    ContD.not_dvd_of_isDist hϖ hg ((ContD.prime_C hϖ).dvd_of_dvd_pow hd)
  have hsplit : g ^ B' = g ^ k * g ^ (B' - k) := by rw [← pow_add, Nat.add_sub_cancel' hk]
  rw [hsplit] at hab
  have hd : C ϖ ^ s ∣ g ^ k * (F - b * g ^ (B' - k)) := ⟨a, by linear_combination -hab⟩
  obtain ⟨c, hc⟩ := ContD.pow_dvd_of_dvd_mul hϖ hgk s _ hd
  rw [Ideal.mem_span_pair]
  exact ⟨c, b, by linear_combination -hc⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries
