import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.CEval

section Adic

variable {A : Type} [CommRing A] (p : ℕ)

theorem smodEq_of_dvd (m : ℕ) {y z : A} (h : (p : A) ^ m ∣ y - z) :
    y ≡ z [SMOD ((Ideal.span {(p : A)}) ^ m • ⊤ : Submodule A A)] := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton.2 h

theorem dvd_of_smodEq (m : ℕ) {y z : A}
    (h : y ≡ z [SMOD ((Ideal.span {(p : A)}) ^ m • ⊤ : Submodule A A)]) :
    (p : A) ^ m ∣ y - z := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] at h
  exact Ideal.mem_span_singleton.1 h

theorem eq_of_forall_dvd [IsHausdorff (Ideal.span {(p : A)}) A] {y z : A}
    (h : ∀ m : ℕ, (p : A) ^ m ∣ y - z) : y = z :=
  sub_eq_zero.1 (IsHausdorff.haus ‹_› _ fun m =>
    smodEq_of_dvd p m (by rw [sub_zero]; exact h m))

end Adic

section Ext

variable {σ R A : Type} [Fintype σ] [CommRing R] [CommRing A]

theorem eq_on_poly (φ ψ : MvPowerSeries σ R →+* A) (hC : ∀ c, φ (C c) = ψ (C c))
    (hX : ∀ i, φ (X i) = ψ (X i)) (P : MvPolynomial σ R) : φ P = ψ P := by
  induction P using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.coe_C, hC]
  | add P Q hP hQ => rw [MvPolynomial.coe_add, map_add, map_add, hP, hQ]
  | mul_X P i hP => rw [MvPolynomial.coe_mul, map_mul, map_mul, hP, MvPolynomial.coe_X, hX]

theorem ext_of_cont (p : ℕ) [IsHausdorff (Ideal.span {(p : A)}) A] (φ ψ : MvPowerSeries σ R →+* A)
    (hC : ∀ c, φ (C c) = ψ (C c)) (hX : ∀ i, φ (X i) = ψ (X i))
    (hφ : ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ φ f)
    (hψ : ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ ψ f)
    (f : MvPowerSeries σ R) : φ f = ψ f := by
  classical
  refine eq_of_forall_dvd p fun m => ?_
  obtain ⟨N₁, h₁⟩ := hφ m
  obtain ⟨N₂, h₂⟩ := hψ m
  have hP := eq_on_poly φ ψ hC hX (trunc' R (Finsupp.equivFunOnFinite.symm fun _ : σ => N₁ + N₂) f)
  set P : MvPowerSeries σ R := ↑(trunc' R (Finsupp.equivFunOnFinite.symm fun _ : σ => N₁ + N₂) f) with hPdef
  have hg : ∀ α : σ →₀ ℕ, α.degree < N₁ + N₂ → coeff α (f - P) = 0 := by
    intro α hα
    have hle : α ≤ Finsupp.equivFunOnFinite.symm fun _ : σ => N₁ + N₂ := Finsupp.le_def.2 fun i => by
      have := Finsupp.le_degree i α
      show α i ≤ N₁ + N₂
      omega
    rw [map_sub, hPdef, MvPolynomial.coeff_coe, coeff_trunc', if_pos hle, sub_self]
  have e : φ f - ψ f = φ (f - P) - ψ (f - P) := by
    rw [map_sub, map_sub, hP]; ring
  rw [e]
  exact dvd_sub (h₁ _ fun α hα => hg α (by omega)) (h₂ _ fun α hα => hg α (by omega))

end Ext

section Exist

variable {σ R A : Type} [Fintype σ] [CommRing R] [CommRing A] [Algebra R A]

theorem dvd_aeval_of_coeff (p : ℕ) (x : σ → A) (S : ℕ) (hS : ∀ i, (p : A) ∣ x i ^ S) (m : ℕ)
    (P : MvPolynomial σ R) (hP : ∀ α : σ →₀ ℕ, (∀ i, α i ≤ m * S) → P.coeff α = 0) :
    (p : A) ^ m ∣ MvPolynomial.aeval x P := by
  classical
  conv_rhs => rw [P.as_sum]
  rw [map_sum]
  refine Finset.dvd_sum fun α hα => ?_
  rw [MvPolynomial.aeval_monomial]
  obtain ⟨i, hi⟩ : ∃ i, m * S < α i := by
    by_contra h
    push_neg at h
    exact (MvPolynomial.mem_support_iff.1 hα) (hP α h)
  refine Dvd.dvd.mul_left ?_ _
  have hmem : i ∈ α.support := Finsupp.mem_support_iff.2 (by omega)
  refine Dvd.dvd.trans ?_ (Finset.dvd_prod_of_mem (fun j => x j ^ α j) hmem)
  calc (p : A) ^ m ∣ (x i ^ S) ^ m := pow_dvd_pow_of_dvd (hS i) m
    _ = x i ^ (m * S) := by rw [← pow_mul, mul_comm]
    _ ∣ x i ^ α i := pow_dvd_pow _ hi.le

theorem exists_isEval (p : ℕ) [IsAdicComplete (Ideal.span {(p : A)}) A] (x : σ → A)
    (hx : ∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) :
    ∃ E : MvPowerSeries σ R →ₐ[R] A, IsEval p x E := by
  classical
  choose N hN using hx
  set S := ∑ i, N i
  have hS : ∀ i, (p : A) ∣ x i ^ S := fun i => (hN i).trans (pow_dvd_pow _
    (Finset.single_le_sum (fun j _ => Nat.zero_le (N j)) (Finset.mem_univ i)))
  let bx : ℕ → σ →₀ ℕ := fun K => Finsupp.equivFunOnFinite.symm fun _ => K
  have hbx : ∀ K (α : σ →₀ ℕ), α ≤ bx K ↔ ∀ i, α i ≤ K := fun K α => Finsupp.le_def
  let s : ℕ → MvPowerSeries σ R → A := fun m f => MvPolynomial.aeval x (trunc' R (bx (m * S)) f)
  have key := dvd_aeval_of_coeff (R := R) p x S hS
  have hcau : ∀ f m n, m ≤ n → (p : A) ^ m ∣ s m f - s n f := by
    intro f m n hmn
    simp only [s, ← map_sub]
    refine key m _ fun α hα => ?_
    have h1 : α ≤ bx (m * S) := (hbx _ _).2 hα
    have h2 : α ≤ bx (n * S) := (hbx _ _).2 fun i => (hα i).trans (Nat.mul_le_mul_right _ hmn)
    rw [MvPolynomial.coeff_sub, coeff_trunc', coeff_trunc', if_pos h1, if_pos h2, sub_self]
  have hL : ∀ f, ∃ L : A, ∀ m, (p : A) ^ m ∣ s m f - L := by
    intro f
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {(p : A)}) A)
      (f := fun m => s m f) (fun {m n} hmn => smodEq_of_dvd p m (hcau f m n hmn))
    exact ⟨L, fun m => dvd_of_smodEq p m (hL m)⟩
  choose L hL using hL
  have huniq : ∀ f y, (∀ m, (p : A) ^ m ∣ s m f - y) → L f = y := fun f y h =>
    eq_of_forall_dvd p fun m => by
      have := dvd_sub (h m) (hL f m)
      rwa [sub_sub_sub_cancel_left] at this
  have hpoly : ∀ P : MvPolynomial σ R, L P = MvPolynomial.aeval x P := by
    intro P
    refine huniq _ _ fun m => ?_
    simp only [s, ← map_sub]
    refine key m _ fun α hα => ?_
    rw [MvPolynomial.coeff_sub, coeff_trunc', if_pos ((hbx _ _).2 hα), MvPolynomial.coeff_coe,
      sub_self]
  have hadd : ∀ f g, L (f + g) = L f + L g := by
    intro f g
    refine huniq _ _ fun m => ?_
    have e : s m (f + g) - (L f + L g) = (s m f - L f) + (s m g - L g) := by
      simp only [s, map_add]; ring
    rw [e]
    exact dvd_add (hL f m) (hL g m)
  have hmul : ∀ f g, L (f * g) = L f * L g := by
    intro f g
    refine huniq _ _ fun m => ?_
    have e : s m (f * g) - L f * L g = (s m (f * g) - s m f * s m g) + (s m f - L f) * s m g +
        L f * (s m g - L g) := by ring
    have h1 : (p : A) ^ m ∣ s m (f * g) - s m f * s m g := by
      simp only [s, ← map_mul, ← map_sub]
      refine key m _ fun α hα => ?_
      have h1 : α ≤ bx (m * S) := (hbx _ _).2 hα
      rw [MvPolynomial.coeff_sub, coeff_trunc', if_pos h1,
        coeff_trunc'_mul_trunc'_eq_coeff_mul _ _ _ h1, sub_self]
    rw [e]
    exact dvd_add (dvd_add h1 (Dvd.dvd.mul_right (hL f m) _)) (Dvd.dvd.mul_left (hL g m) _)
  let E : MvPowerSeries σ R →ₐ[R] A :=
    { toFun := L
      map_one' := by rw [← MvPolynomial.coe_one, hpoly, map_one]
      map_mul' := hmul
      map_zero' := by rw [← MvPolynomial.coe_zero, hpoly, map_zero]
      map_add' := hadd
      commutes' := fun c => by
        rw [← c_eq_algebraMap, ← MvPolynomial.coe_C, hpoly, MvPolynomial.aeval_C] }
  refine ⟨E, fun i => ?_, fun m => ⟨Fintype.card σ * (m * S) + 1, fun f hf => ?_⟩⟩
  · show L (X i) = x i
    rw [← MvPolynomial.coe_X, hpoly, MvPolynomial.aeval_X]
  · show (p : A) ^ m ∣ L f
    have h0 : trunc' R (bx (m * S)) f = 0 := by
      ext α
      rw [coeff_trunc', MvPolynomial.coeff_zero]
      split_ifs with h
      · refine hf α ?_
        rw [Finsupp.degree_eq_sum]
        have := Finset.sum_le_sum (s := Finset.univ) fun i _ => (hbx _ _).1 h i
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at this
        omega
      · rfl
    have := hL f m
    simp only [s, h0, map_zero, zero_sub, dvd_neg] at this
    exact this

end Exist

theorem eval_unique {σ R A : Type} [Fintype σ] [CommRing R] [CommRing A] [Algebra R A] (p : ℕ)
    [IsHausdorff (Ideal.span {(p : A)}) A] (x : σ → A) (E₁ E₂ : MvPowerSeries σ R →ₐ[R] A)
    (h₁ : IsEval p x E₁) (h₂ : IsEval p x E₂) : E₁ = E₂ := by
  ext f
  exact ext_of_cont p E₁.toRingHom E₂.toRingHom
    (fun c => by
      show E₁ (C c) = E₂ (C c)
      rw [c_eq_algebraMap, AlgHom.commutes, AlgHom.commutes])
    (fun i => by
      show E₁ (X i) = E₂ (X i)
      rw [h₁.1, h₂.1])
    h₁.2 h₂.2 f

theorem continuous_eval : ∀ (p : ℕ) (R A σ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype σ] [IsAdicComplete (Ideal.span {(p : A)}) A] (x : σ → A), (∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) → (∃! E : MvPowerSeries σ R →ₐ[R] A, IsEval p x E) ∧ ∀ E : MvPowerSeries σ R →ₐ[R] A, IsEval p x E → (∀ (τ : Type) [Fintype τ] (u : τ → MvPowerSeries σ R) (E' : MvPowerSeries τ R →ₐ[R] A), (∀ j, constantCoeff (u j) = 0) → IsEval p (fun j => E (u j)) E' → ∀ f, E (subst u f) = E' f) ∧ (∀ f, constantCoeff f = 0 → ∃ N : ℕ, (p : A) ∣ E f ^ N) ∧ ∀ (R' A' : Type) [CommRing R'] [CommRing A'] [Algebra R' A'] [IsHausdorff (Ideal.span {(p : A')}) A'] (r : R →+* R') (g : A →+* A') (E' : MvPowerSeries σ R' →ₐ[R'] A'), (∀ c, g (algebraMap R A c) = algebraMap R' A' (r c)) → IsEval p (fun i => g (x i)) E' → ∀ f, g (E f) = E' (map r f) := by
  intro p R A σ _ _ _ _ _ x hx
  refine ⟨?_, fun E hE => ⟨?_, ?_, ?_⟩⟩
  · obtain ⟨E, hE⟩ := exists_isEval (R := R) p x hx
    exact ⟨E, hE, fun E' hE' => eval_unique p x E' E hE' hE⟩
  · intro τ _ u E' hu hE' f
    have hs : HasSubst u := hasSubst_of_constantCoeff_zero hu
    rw [← coe_substAlgHom hs]
    exact ext_of_cont p ((E.comp (substAlgHom hs)).toRingHom) E'.toRingHom
      (fun c => by
        show E (substAlgHom hs (C c)) = E' (C c)
        rw [c_eq_algebraMap, AlgHom.commutes, AlgHom.commutes, AlgHom.commutes])
      (fun j => by
        show E (substAlgHom hs (X j)) = E' (X j)
        rw [substAlgHom_X, hE'.1])
      (fun m => by
        obtain ⟨N, hN⟩ := hE.2 m
        refine ⟨N, fun f hf => ?_⟩
        show (p : A) ^ m ∣ E (substAlgHom hs f)
        rw [coe_substAlgHom]
        refine hN _ fun α hα => coeff_of_lt_order ?_
        have h1 : (1 : ℕ∞) ≤ ⨅ j, (u j).order :=
          le_iInf fun j => one_le_order_iff_constCoeff_eq_zero.2 (hu j)
        have h2 : (N : ℕ∞) ≤ f.order := nat_le_order hf
        calc (α.degree : ℕ∞) < N := by exact_mod_cast hα
          _ = 1 * N := (one_mul _).symm
          _ ≤ (⨅ j, (u j).order) * f.order := mul_le_mul' h1 h2
          _ ≤ (subst u f).order := le_order_subst hs f)
      hE'.2 f
  · intro f hf
    obtain ⟨N, hN⟩ := hE.2 1
    refine ⟨N, ?_⟩
    rw [← map_pow]
    have := hN (f ^ N) fun α hα => coeff_of_lt_order
      ((by exact_mod_cast hα : (α.degree : ℕ∞) < N).trans_le
        (le_order_pow_of_constantCoeff_eq_zero N hf))
    rwa [pow_one] at this
  · intro R' A' _ _ _ _ r g E' hg hE' f
    exact ext_of_cont p (g.comp E.toRingHom) (E'.toRingHom.comp (map r))
      (fun c => by
        show g (E (C c)) = E' (map r (C c))
        rw [map_C, c_eq_algebraMap, c_eq_algebraMap, AlgHom.commutes, AlgHom.commutes, hg])
      (fun i => by
        show g (E (X i)) = E' (map r (X i))
        rw [map_X, hE.1, hE'.1])
      (fun m => by
        obtain ⟨N, hN⟩ := hE.2 m
        exact ⟨N, fun f hf => by
          show (p : A') ^ m ∣ g (E f)
          have := map_dvd g (hN f hf)
          rwa [map_pow, map_natCast] at this⟩)
      (fun m => by
        obtain ⟨N, hN⟩ := hE'.2 m
        exact ⟨N, fun f hf => hN _ fun α hα => by rw [coeff_map, hf α hα, map_zero]⟩)
      f

end GlobalTheory.CEval
