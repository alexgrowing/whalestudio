import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulInvolEqOfFixed

namespace GlobalTheory.NormSurjMod

variable {R : Type} [CommRing R]

def NormOnto (σ : R →+* R) (I : Ideal R) : Prop :=
  ∀ u : R, σ u = u → (∃ v, u * v - 1 ∈ I) → ∃ x, x * σ x - u ∈ I

theorem normOnto_inf (σ : R →+* R) (I J : Ideal R) (hI : ∀ a ∈ I, σ a ∈ I) (hJ : ∀ a ∈ J, σ a ∈ J)
    (hIJ : I ⊔ J = ⊤) (h1 : NormOnto σ I) (h2 : NormOnto σ J) : NormOnto σ (I ⊓ J) := by
  rintro u hu ⟨v, hv⟩
  obtain ⟨x1, hx1⟩ := h1 u hu ⟨v, (Ideal.mem_inf.1 hv).1⟩
  obtain ⟨x2, hx2⟩ := h2 u hu ⟨v, (Ideal.mem_inf.1 hv).2⟩
  have h1m : (1 : R) ∈ I ⊔ J := by rw [hIJ]; exact Submodule.mem_top
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.1 h1m
  refine ⟨f * x1 + e * x2, Ideal.mem_inf.2 ⟨?_, ?_⟩⟩
  · have hd : f * x1 + e * x2 - x1 ∈ I := by
      have : f * x1 + e * x2 - x1 = e * (x2 - x1) := by linear_combination x1 * hef
      rw [this]; exact I.mul_mem_right _ he
    have hd' : σ (f * x1 + e * x2) - σ x1 ∈ I := by rw [← map_sub]; exact hI _ hd
    have : (f * x1 + e * x2) * σ (f * x1 + e * x2) - u = (f * x1 + e * x2 - x1) * σ (f * x1 + e * x2) +
        x1 * (σ (f * x1 + e * x2) - σ x1) + (x1 * σ x1 - u) := by ring
    rw [this]; exact I.add_mem (I.add_mem (I.mul_mem_right _ hd) (I.mul_mem_left _ hd')) hx1
  · have hd : f * x1 + e * x2 - x2 ∈ J := by
      have : f * x1 + e * x2 - x2 = f * (x1 - x2) := by linear_combination x2 * hef
      rw [this]; exact J.mul_mem_right _ hf
    have hd' : σ (f * x1 + e * x2) - σ x2 ∈ J := by rw [← map_sub]; exact hJ _ hd
    have : (f * x1 + e * x2) * σ (f * x1 + e * x2) - u = (f * x1 + e * x2 - x2) * σ (f * x1 + e * x2) +
        x2 * (σ (f * x1 + e * x2) - σ x2) + (x2 * σ x2 - u) := by ring
    rw [this]; exact J.add_mem (J.add_mem (J.mul_mem_right _ hd) (J.mul_mem_left _ hd')) hx2

theorem normOnto_pow (σ : R →+* R) (w : R) (hσ : ∀ a, σ (σ a) = a) (hw : w + σ w = 1) (I : Ideal R)
    (hI : ∀ a ∈ I, σ a ∈ I) (h : NormOnto σ I) : ∀ m, 1 ≤ m → NormOnto σ (I ^ m) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simpa using h
  | succ m hm ih =>
    rintro u hu ⟨v, hv⟩
    have hle : I ^ (m + 1) ≤ I ^ m := Ideal.pow_le_pow_right (Nat.le_succ m)
    have hIm : I ^ m ≤ I := Ideal.pow_le_self (by omega)
    obtain ⟨x, hx⟩ := ih u hu ⟨v, hle hv⟩
    have hv1 : u * v - 1 ∈ I := hIm (hle hv)
    obtain ⟨c, hc⟩ : ∃ c, c = u - x * σ x := ⟨_, rfl⟩
    have hcm : c ∈ I ^ m := by rw [hc, ← neg_sub]; exact (I ^ m).neg_mem hx
    have hσc : σ c = c := by rw [hc, map_sub, map_mul, hu, hσ, mul_comm]
    have h1 : x * σ x * v - 1 ∈ I := by
      have : x * σ x * v - 1 = (u * v - 1) - c * v := by rw [hc]; ring
      rw [this]; exact I.sub_mem hv1 (I.mul_mem_right v (hIm hcm))
    have h2 : σ x * x * σ v - 1 ∈ I := by
      have := hI _ h1
      rwa [map_sub, map_mul, map_mul, map_one, hσ] at this
    refine ⟨x + x * (w * v * c), ?_⟩
    have key : (x + x * (w * v * c)) * σ (x + x * (w * v * c)) - u =
        c * (w * (x * σ x * v - 1) + σ w * (σ x * x * σ v - 1)) + c * (c * (x * σ x * w * v * σ w * σ v)) := by
      rw [map_add, map_mul, map_mul, map_mul, hσc]
      linear_combination c * hw + hc
    rw [key, pow_succ]
    exact Ideal.add_mem _ (Ideal.mul_mem_mul hcm (I.add_mem (I.mul_mem_left _ h1) (I.mul_mem_left _ h2)))
      (Ideal.mul_mem_mul hcm (I.mul_mem_right _ (hIm hcm)))

theorem normOnto_of_le_radical [IsNoetherianRing R] (σ : R →+* R) (K I : Ideal R) (hKI : K ≤ I)
    (hIK : I ≤ K.radical) (h : NormOnto σ K) : NormOnto σ I := by
  rintro u hu ⟨v, hv⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (u * v - 1) ^ n ∈ K := hIK hv
  have hunit : ∃ v', u * v' - 1 ∈ K := by
    refine ⟨v * ∑ i ∈ Finset.range n, (1 - u * v) ^ i, ?_⟩
    have e : u * (v * ∑ i ∈ Finset.range n, (1 - u * v) ^ i) - 1 = -(1 - u * v) ^ n := by
      have := mul_neg_geom_sum (1 - u * v) n
      linear_combination this
    rw [e]
    have : (1 - u * v) ^ n = (-1) ^ n * (u * v - 1) ^ n := by rw [← mul_pow]; ring
    rw [this]; exact K.neg_mem (K.mul_mem_left _ hn)
  obtain ⟨x, hx⟩ := h u hu hunit
  exact ⟨x, hKI hx⟩

theorem normOnto_split (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a) (P : Ideal R) (hP : P.IsMaximal)
    (hP' : (P.comap σ).IsMaximal) (hne : P.comap σ ≠ P) : NormOnto σ (P ⊓ P.comap σ) := by
  rintro u hu -
  have hcop : P ⊔ P.comap σ = ⊤ := Ideal.IsMaximal.coprime_of_ne hP hP' hne.symm
  have h1m : (1 : R) ∈ P ⊔ P.comap σ := by rw [hcop]; exact Submodule.mem_top
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.1 h1m
  rw [Ideal.mem_comap] at hf
  refine ⟨f * u + e, Ideal.mem_inf.2 ⟨?_, ?_⟩⟩
  · have : (f * u + e) * σ (f * u + e) - u = (f * u + e) * (σ (f * u + e) - 1) + e * (1 - u) := by
      linear_combination u * hef
    rw [this]
    refine P.add_mem (P.mul_mem_left _ ?_) (P.mul_mem_right _ he)
    have : σ (f * u + e) - 1 = σ f * u - σ f := by
      rw [map_add, map_mul, hu]
      have h' := congrArg σ hef
      rw [map_add, map_one] at h'
      linear_combination h'
    rw [this]; exact P.sub_mem (P.mul_mem_right _ hf) hf
  · rw [Ideal.mem_comap]
    have h' := congrArg σ hef
    rw [map_add, map_one] at h'
    have : σ ((f * u + e) * σ (f * u + e) - u) = (σ f * u - σ f) * (f * u + e) + e * (1 - u) := by
      rw [map_sub, map_mul, hσ, hu, map_add, map_mul, hu]
      linear_combination (f * u + e) * h' + u * hef
    rw [this]
    exact P.add_mem (P.mul_mem_right _ (P.sub_mem (P.mul_mem_right _ hf) hf)) (P.mul_mem_right _ he)

theorem normOnto_inert (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a) (P : Ideal R) (hP : P.IsMaximal)
    (hfin : Finite (R ⧸ P)) (hstab : P.comap σ = P) (hne : ∃ b, σ b - b ∉ P) : NormOnto σ P := by
  rintro u hu -
  haveI := hP
  haveI := hfin
  letI : Field (R ⧸ P) := Ideal.Quotient.field P
  have hle : P ≤ P.comap σ := by rw [hstab]
  let τ : R ⧸ P →+* R ⧸ P := Ideal.quotientMap P σ hle
  have hτ : ∀ a, τ (Ideal.Quotient.mk P a) = Ideal.Quotient.mk P (σ a) := fun a => Ideal.quotientMap_mk
  have hinv : Function.Involutive τ := by
    intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [hτ, hτ, hσ]
  have hne' : ∃ b : R ⧸ P, τ b ≠ b := by
    obtain ⟨b, hb⟩ := hne
    refine ⟨Ideal.Quotient.mk P b, ?_⟩
    rw [hτ, Ne, Ideal.Quotient.eq]
    exact hb
  obtain ⟨a, ha⟩ := GlobalTheory.exists_mul_invol_eq_of_fixed (R ⧸ P) τ hinv hne' (Ideal.Quotient.mk P u)
    (by rw [hτ, hu])
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨x, ?_⟩
  rw [← Ideal.Quotient.eq, map_mul, ← hτ]
  exact ha

theorem stable_inf_comap (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a) (P : Ideal R) :
    ∀ a ∈ P ⊓ P.comap σ, σ a ∈ P ⊓ P.comap σ := by
  intro a ha
  rw [Ideal.mem_inf, Ideal.mem_comap] at ha ⊢
  rw [hσ]
  exact ⟨ha.2, ha.1⟩

theorem comap_comap_invol (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a) (P : Ideal R) :
    (P.comap σ).comap σ = P := by
  ext a
  rw [Ideal.mem_comap, Ideal.mem_comap, hσ]

theorem normOnto_finset_inf (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a) (s : Finset (Ideal R))
    (hmax : ∀ P ∈ s, P.IsMaximal) (h : ∀ P ∈ s, NormOnto σ (P ⊓ P.comap σ)) :
    NormOnto σ (s.inf fun P => P ⊓ P.comap σ) := by
  classical
  have hsurj : Function.Surjective σ := fun a => ⟨σ a, hσ a⟩
  induction s using Finset.induction_on with
  | empty => intro u _ _; exact ⟨0, by simp⟩
  | insert a s ha ih =>
    rw [Finset.inf_insert]
    have ih' := ih (fun P hP => hmax P (Finset.mem_insert_of_mem hP))
      (fun P hP => h P (Finset.mem_insert_of_mem hP))
    by_cases hex : ∃ P ∈ s, P ⊓ P.comap σ = a ⊓ a.comap σ
    · obtain ⟨P, hP, hPa⟩ := hex
      have hle : s.inf (fun P => P ⊓ P.comap σ) ≤ a ⊓ a.comap σ := by
        exact (Finset.inf_le (f := fun P : Ideal R => P ⊓ P.comap σ) hP).trans_eq hPa
      have e : (a ⊓ a.comap σ) ⊓ s.inf (fun P => P ⊓ P.comap σ) = s.inf (fun P => P ⊓ P.comap σ) :=
        inf_eq_right.2 hle
      rw [e]
      exact ih'
    · push_neg at hex
      have hstab : ∀ x ∈ s.inf (fun P => P ⊓ P.comap σ), σ x ∈ s.inf (fun P => P ⊓ P.comap σ) := by
        intro x hx
        rw [Submodule.mem_finsetInf] at hx ⊢
        exact fun P hP => stable_inf_comap σ hσ P x (hx P hP)
      refine normOnto_inf σ _ _ (stable_inf_comap σ hσ a) hstab ?_ (h a (Finset.mem_insert_self a s)) ih'
      by_contra hcop
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hcop
      have hM1 : a ⊓ a.comap σ ≤ M := le_trans le_sup_left hle
      have hM2 : s.inf (fun P => P ⊓ P.comap σ) ≤ M := le_trans le_sup_right hle
      obtain ⟨P, hP, hPM⟩ := (Ideal.IsPrime.inf_le' hM.isPrime).1 hM2
      have hamax : a.IsMaximal := hmax a (Finset.mem_insert_self a s)
      have hPmax : P.IsMaximal := hmax P (Finset.mem_insert_of_mem hP)
      have haσ : (a.comap σ).IsMaximal := Ideal.comap_isMaximal_of_surjective σ hsurj
      have hPσ : (P.comap σ).IsMaximal := Ideal.comap_isMaximal_of_surjective σ hsurj
      have hA : M = a ∨ M = a.comap σ := by
        rcases hM.isPrime.inf_le.1 hM1 with h1 | h1
        · exact Or.inl (hamax.eq_of_le hM.ne_top h1).symm
        · exact Or.inr (haσ.eq_of_le hM.ne_top h1).symm
      have hB : M = P ∨ M = P.comap σ := by
        rcases hM.isPrime.inf_le.1 hPM with h1 | h1
        · exact Or.inl (hPmax.eq_of_le hM.ne_top h1).symm
        · exact Or.inr (hPσ.eq_of_le hM.ne_top h1).symm
      apply hex P hP
      rcases hA with hA | hA <;> rcases hB with hB | hB
      · rw [← hB, hA]
      · have : P = a.comap σ := by rw [← comap_comap_invol σ hσ P, ← hB, hA]
        rw [this, comap_comap_invol σ hσ, inf_comm]
      · have : P = a.comap σ := by rw [← hB, hA]
        rw [this, comap_comap_invol σ hσ, inf_comm]
      · have : P = a := by rw [← comap_comap_invol σ hσ P, ← hB, hA, comap_comap_invol σ hσ]
        rw [this]

end GlobalTheory.NormSurjMod
