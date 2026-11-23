import Formalism.LocalToGlobal.InertKernelTheory.DefsInt
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnimodGenus

noncomputable section

namespace Formalism.L2.KerInert

open NumberField

def WAPlaces : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], PI.UG.IsCMUnram E →
    ∀ (p : ℕ), p.Prime → ∀ (n : ℕ) (L : Submodule (𝓞 E) (PI.UG.Sp E n)),
      (∀ P : Ideal (𝓞 E), P.IsMaximal → (p : 𝓞 E) ∈ P →
        ∃ g ∈ PI.UG.isom (PI.UG.hStd E n),
          PI.UG.gmap g (PI.UG.loc (K := E) P (PI.UG.stdLat E n)) = PI.UG.loc (K := E) P L) →
      ∃ γ ∈ PI.UG.isom (PI.UG.hStd E n), ∀ P : Ideal (𝓞 E), P.IsMaximal → (p : 𝓞 E) ∈ P →
        PI.UG.gmap γ (PI.UG.loc (K := E) P (PI.UG.stdLat E n)) = PI.UG.loc (K := E) P L

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem wa_hStd_apply {n : ℕ} (x y : PI.UG.Sp E n) : PI.UG.hStd E n x y = Formalism.BasicNotions.stdH E n x y := rfl

theorem wa_mem_std {n : ℕ} (x : PI.UG.Sp E n) :
    x ∈ PI.UG.stdLat E n ↔ ∀ i, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = x i := by
  simp only [PI.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]

theorem wa_std_fg (n : ℕ) : (PI.UG.stdLat E n).FG := by
  have h : PI.UG.stdLat E n =
      Submodule.span (𝓞 E) (Set.range fun i : Fin n => (Pi.single i (1 : E) : PI.UG.Sp E n)) := by
    apply le_antisymm
    · intro x hx
      rw [wa_mem_std] at hx
      choose r hr using hx
      have : x = ∑ i, r i • (Pi.single i (1 : E) : PI.UG.Sp E n) := by
        funext j
        simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hr]
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, wa_mem_std]
      intro j
      by_cases hj : j = i
      · subst hj
        exact ⟨1, by simp⟩
      · exact ⟨0, by simp [hj]⟩
  rw [h]
  exact Submodule.fg_span (Set.finite_range _)

theorem wa_le_loc (P : Ideal (𝓞 E)) {n : ℕ} (N : Submodule (𝓞 E) (PI.UG.Sp E n)) : N ≤ PI.UG.loc (K := E) P N :=
  fun x hx => ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩

theorem wa_hcompl_not_mem (P : Ideal (𝓞 E)) (hP : P.IsPrime) {s : 𝓞 E}
    (hs : s ∈ PI.UG.hcompl (K := E) P) : s ∉ P := by
  induction hs using Submonoid.closure_induction with
  | mem x hx => exact hx.1
  | one => exact (Ideal.ne_top_iff_one P).1 hP.ne_top
  | mul x y _ _ hx hy => exact fun h => (hP.mem_or_mem h).elim hx hy

theorem wa_not_isUnit (p : ℕ) (hp : p.Prime) : ¬ IsUnit (p : 𝓞 E) := by
  intro hu
  have h0 : (p : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ) := (map_natCast (algebraMap ℤ (𝓞 E)) p).symm
  have h2 := hu.map (Algebra.norm ℤ (S := 𝓞 E))
  rw [h0, Algebra.norm_algebraMap] at h2
  have hd : Module.finrank ℤ (𝓞 E) ≠ 0 := Module.finrank_pos.ne'
  rw [isUnit_pow_iff hd, Int.isUnit_iff] at h2
  have := hp.two_le
  omega

theorem wa_natCast_smul_mem {n : ℕ} (N : Submodule (𝓞 E) (PI.UG.Sp E n)) (d : ℕ) {z : PI.UG.Sp E n} (hz : z ∈ N) :
    (d : E) • z ∈ N := by
  rw [Nat.cast_smul_eq_nsmul]
  exact N.nsmul_mem hz d

theorem wa_denom (p : ℕ) (hp : p.Prime) {n : ℕ} (M₁ M₂ : Submodule (𝓞 E) (PI.UG.Sp E n)) (h1 : M₁.FG)
    (h : ∀ P : Ideal (𝓞 E), P.IsMaximal → (p : 𝓞 E) ∈ P → M₁ ≤ PI.UG.loc (K := E) P M₂) :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ x ∈ M₁, (s : E) • x ∈ M₂ := by
  obtain ⟨T, hT⟩ := h1
  set I : Ideal (𝓞 E) := M₂.colon (M₁ : Set (PI.UG.Sp E n)) with hIdef
  have hI : ∀ P : Ideal (𝓞 E), P.IsMaximal → (p : 𝓞 E) ∈ P → ¬ I ≤ P := by
    intro P hPm hpP hIP
    have hloc : ∀ t ∈ T, ∃ s ∈ PI.UG.hcompl (K := E) P, s • t ∈ M₂ := by
      intro t ht
      have ht1 : t ∈ M₁ := hT ▸ Submodule.subset_span ht
      exact h P hPm hpP ht1
    choose! s hs hsM using hloc
    have hprod : (∏ t ∈ T, s t) ∈ PI.UG.hcompl (K := E) P := Submonoid.prod_mem _ (fun t ht => hs t ht)
    apply wa_hcompl_not_mem P hPm.isPrime hprod
    apply hIP
    rw [Submodule.mem_colon]
    intro m hm
    rw [SetLike.mem_coe, ← hT] at hm
    induction hm using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem s ht
      rw [hc, mul_comm, mul_smul]
      exact M₂.smul_mem _ (hsM t ht)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [smul_add]
      exact M₂.add_mem hx hy
    | smul r x _ hx =>
      rw [smul_comm]
      exact M₂.smul_mem r hx
  have hsup : Ideal.span {(p : 𝓞 E)} ⊔ I = ⊤ := by
    by_contra hne
    obtain ⟨Q, hQm, hQ⟩ := Ideal.exists_le_maximal _ hne
    exact hI Q hQm (hQ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))) (le_sup_right.trans hQ)
  have h1 : (1 : 𝓞 E) ∈ Ideal.span {(p : 𝓞 E)} ⊔ I := hsup ▸ Submodule.mem_top
  obtain ⟨c, a, haI, hca⟩ := Ideal.mem_span_singleton_sup.1 h1
  have hI0 : I ≠ ⊥ := by
    intro hbot
    rw [hbot, Submodule.mem_bot] at haI
    rw [haI, add_zero] at hca
    exact wa_not_isUnit p hp (isUnit_iff_exists_inv'.2 ⟨c, hca⟩)
  refine ⟨Ideal.absNorm I, Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 ?_), ?_⟩
  · intro hdvd
    have hne : Ideal.absNorm I ≠ 0 := fun h0 => hI0 (Ideal.absNorm_eq_zero_iff.1 h0)
    have hcard : Nat.card (𝓞 E ⧸ I) = Ideal.absNorm I := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have : Finite (𝓞 E ⧸ I) := Nat.finite_of_card_ne_zero (hcard ▸ hne)
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 E ⧸ I) p (hcard ▸ hdvd)
    have hpx : (p : 𝓞 E ⧸ I) * x = 0 := by
      rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
    have ha0 : Ideal.Quotient.mk I a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 haI
    have h1' : Ideal.Quotient.mk I c * (p : 𝓞 E ⧸ I) = 1 := by
      have := congrArg (Ideal.Quotient.mk I) hca
      rw [map_add, map_mul, ha0, add_zero, map_one, map_natCast] at this
      exact this
    have hx0 : x = 0 := by
      calc x = (Ideal.Quotient.mk I c * (p : 𝓞 E ⧸ I)) * x := by rw [h1', one_mul]
        _ = Ideal.Quotient.mk I c * ((p : 𝓞 E ⧸ I) * x) := by ring
        _ = 0 := by rw [hpx, mul_zero]
    rw [hx0, addOrderOf_zero] at hx
    exact hp.one_lt.ne hx
  · intro x hx
    have hmem : ((Ideal.absNorm I : ℕ) : 𝓞 E) ∈ I := Ideal.absNorm_mem I
    have := (Submodule.mem_colon.1 hmem) x hx
    rwa [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E] at this

theorem wa_unimod {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} (hL : Formalism.BasicNotions.IsSDLat E n L) :
    PI.UG.IsUnimodular (PI.UG.hStd E n) L := by
  unfold PI.UG.IsUnimodular PI.UG.dual
  ext y
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
  rw [hL.2.2 y]
  refine forall₂_congr fun x _ => ?_
  rw [Submodule.mem_one, RingHom.mem_range]
  exact Iff.rfl

theorem wa_unitary {n : ℕ} (g : PI.UG.Sp E n ≃ₗ[E] PI.UG.Sp E n) (hg : g ∈ PI.UG.isom (PI.UG.hStd E n)) :
    LinearMap.toMatrix' (g : PI.UG.Sp E n →ₗ[E] PI.UG.Sp E n) ∈ Matrix.unitaryGroup (Fin n) E := by
  have hg' : ∀ x y, PI.UG.hStd E n (g x) (g y) = PI.UG.hStd E n x y := hg
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  have hij := hg' (Pi.single i (1 : E)) (Pi.single j (1 : E))
  rw [wa_hStd_apply, wa_hStd_apply] at hij
  simp only [Formalism.BasicNotions.stdH] at hij
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.star_apply, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
  rw [hij]
  simp only [Pi.single_apply, apply_ite star, star_one, star_zero, mul_ite, ite_mul, one_mul, zero_mul, mul_zero,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

theorem wa_main (hWA : WAPlaces) (hCM : PI.UG.IsCMUnram E) (p : ℕ) (hp : p.Prime) (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : Formalism.BasicNotions.IsSDLat E n L) :
    ∃ (γ : Matrix.unitaryGroup (Fin n) E) (M : Submodule (𝓞 E) (Fin n → E)),
      Formalism.BasicNotions.IsSDLat E n M ∧
      (∃ s : ℕ, Nat.Coprime s p ∧ (∀ x ∈ PI.UG.stdLat E n, (s : E) • x ∈ M) ∧
        ∀ x ∈ M, (s : E) • x ∈ PI.UG.stdLat E n) ∧
      L = Formalism.BasicNotions.SDLat.smulLat (γ : Matrix (Fin n) (Fin n) E) M := by
  have hLat : Submodule.IsLattice E L := ⟨hL.1, hL.2.1⟩
  have hUni : PI.UG.IsUnimodular (PI.UG.hStd E n) L := wa_unimod hL
  have hGen := unimodular_genus_unique E n hCM L hLat hUni
  obtain ⟨γ, hγ, hγP⟩ := hWA E hCM p hp n L (fun P hP _ => hGen P hP)
  have hγ' : ∀ x y, PI.UG.hStd E n (γ x) (γ y) = PI.UG.hStd E n x y := hγ
  have e : ∀ x y, Formalism.BasicNotions.stdH E n (γ x) (γ y) = Formalism.BasicNotions.stdH E n x y := hγ'
  set M : Submodule (𝓞 E) (Fin n → E) :=
    L.comap ((γ : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) with hMdef
  have hMmem : ∀ x, x ∈ M ↔ γ x ∈ L := fun x => Iff.rfl
  have hMmap : M = L.map ((γ.symm : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) := by
    ext x
    rw [hMmem, Submodule.mem_map]
    constructor
    · intro h
      exact ⟨γ x, h, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  have hMfg : M.FG := by
    rw [hMmap]
    exact hL.1.map _
  have hγs : ∀ (s : 𝓞 E) (x : Fin n → E), γ (s • x) = s • γ x := by
    intro s x
    rw [← algebraMap_smul E s x, map_smul, algebraMap_smul]
  refine ⟨⟨LinearMap.toMatrix' (γ : (Fin n → E) →ₗ[E] (Fin n → E)), wa_unitary γ hγ⟩, M, ?_, ?_, ?_⟩
  · refine ⟨hMfg, ?_, ?_⟩
    · rw [eq_top_iff]
      intro v _
      have hv : γ v ∈ Submodule.span E (L : Set (Fin n → E)) := by
        rw [hL.2.1]
        trivial
      have h2 : γ.symm (γ v) ∈
          (Submodule.span E (L : Set (Fin n → E))).map (γ.symm : (Fin n → E) →ₗ[E] (Fin n → E)) :=
        Submodule.mem_map_of_mem hv
      rw [Submodule.map_span] at h2
      simp only [LinearEquiv.symm_apply_apply] at h2
      refine Submodule.span_mono ?_ h2
      rintro _ ⟨y, hy, rfl⟩
      show γ (γ.symm y) ∈ L
      simpa using hy
    · intro y
      rw [hMmem, hL.2.2 (γ y)]
      constructor
      · intro h x hx
        rw [← e]
        exact h _ hx
      · intro h x' hx'
        have hm : γ.symm x' ∈ M := by
          show γ (γ.symm x') ∈ L
          simpa using hx'
        have := h _ hm
        rw [← e, LinearEquiv.apply_symm_apply] at this
        exact this
  · have hstd : ∀ P : Ideal (𝓞 E), P.IsMaximal → (p : 𝓞 E) ∈ P →
        PI.UG.stdLat E n ≤ PI.UG.loc (K := E) P M := by
      intro P hP hpP x hx
      have hx1 : x ∈ PI.UG.loc (K := E) P (PI.UG.stdLat E n) := wa_le_loc P _ hx
      have hx2 : γ x ∈ PI.UG.gmap γ (PI.UG.loc (K := E) P (PI.UG.stdLat E n)) :=
        Submodule.mem_map_of_mem (f := (γ : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) hx1
      rw [hγP P hP hpP] at hx2
      obtain ⟨s, hs, hsx⟩ := hx2
      refine ⟨s, hs, ?_⟩
      show γ (s • x) ∈ L
      rw [hγs]
      exact hsx
    have hM : ∀ P : Ideal (𝓞 E), P.IsMaximal → (p : 𝓞 E) ∈ P →
        M ≤ PI.UG.loc (K := E) P (PI.UG.stdLat E n) := by
      intro P hP hpP x hx
      have hx1 : γ x ∈ PI.UG.loc (K := E) P L := wa_le_loc P L hx
      rw [← hγP P hP hpP] at hx1
      obtain ⟨y, hy, hyx⟩ := hx1
      have : y = x := γ.injective hyx
      rw [← this]
      exact hy
    obtain ⟨s1, hs1, h1⟩ := wa_denom p hp (PI.UG.stdLat E n) M (wa_std_fg n) hstd
    obtain ⟨s2, hs2, h2⟩ := wa_denom p hp M (PI.UG.stdLat E n) hMfg hM
    refine ⟨s1 * s2, Nat.Coprime.mul_left hs1 hs2, ?_, ?_⟩
    · intro x hx
      rw [Nat.cast_mul, mul_comm, mul_smul]
      exact wa_natCast_smul_mem M s2 (h1 x hx)
    · intro x hx
      rw [Nat.cast_mul, mul_smul]
      exact wa_natCast_smul_mem _ s1 (h2 x hx)
  · show L = M.map ((Matrix.toLin' (LinearMap.toMatrix' (γ : (Fin n → E) →ₗ[E] (Fin n → E)))).restrictScalars (𝓞 E))
    rw [Matrix.toLin'_toMatrix', hMdef, Submodule.map_comap_eq_of_surjective]
    exact γ.surjective

theorem waPlaces_hyp_std (p n : ℕ) :
    ∀ P : Ideal (𝓞 E), P.IsMaximal → (p : 𝓞 E) ∈ P →
      ∃ g ∈ PI.UG.isom (PI.UG.hStd E n),
        PI.UG.gmap g (PI.UG.loc (K := E) P (PI.UG.stdLat E n)) = PI.UG.loc (K := E) P (PI.UG.stdLat E n) := by
  intro P _ _
  refine ⟨1, Subgroup.one_mem _, ?_⟩
  unfold PI.UG.gmap
  ext x
  simp

end Gen

theorem weakApprox_of (hWA : WAPlaces) : WeakApprox := by
  intro D p _ _ _ N N' L L' hAdm
  let _ := D.host.cmStar
  obtain ⟨hN, hN', hL, hL'⟩ := hAdm
  have hCM : PI.UG.IsCMUnram D.host.E := D.sp.cm.cmUnram
  have hp : p.Prime := Fact.out
  obtain ⟨γ, M, hM, hEq, hLM⟩ := wa_main hWA hCM p hp N L hL
  obtain ⟨γ', M', hM', hEq', hLM'⟩ := wa_main hWA hCM p hp N' L' hL'
  exact ⟨γ, γ', M, M', ⟨hN, hN', hM, hM'⟩, hEq, hEq', hLM, hLM'⟩

end Formalism.L2.KerInert
