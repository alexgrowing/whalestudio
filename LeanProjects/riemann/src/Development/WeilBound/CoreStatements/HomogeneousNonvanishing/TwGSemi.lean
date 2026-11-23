import Mathlib
import Formalism.HermitianLattices.HermitianLatticesProofs.UnimodUnramUnique
open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

open IsLocalRing Polynomial

theorem semi_complete {A : Type} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    IsAdicComplete (maximalIdeal A) M where
  toIsHausdorff := inferInstance
  toIsPrecomplete := by
    rw [← AdicCompletion.of_surjective_iff]
    intro y
    obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite (maximalIdeal A) M y
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul r x =>
      obtain ⟨r, rfl⟩ := AdicCompletion.of_surjective (maximalIdeal A) A r
      refine ⟨r • x, ?_⟩
      rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
      exact (algebraMap_smul (AdicCompletion (maximalIdeal A) A) r _).symm
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩

theorem semi_unit_or_nil {Q : Type} [CommRing Q] [Finite Q] (h : ∀ e : Q, e * e = e → e = 0 ∨ e = 1) (x : Q) :
    IsUnit x ∨ IsNilpotent x := by
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd x (1 : Q)
  simp only [smul_eq_mul, mul_one, Nat.succ_eq_add_one] at hy
  have h1 : ∀ k : ℕ, x ^ (n + 1) * (x * y) ^ k = x ^ (n + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => linear_combination (x * y) * ih + x * hy
  have h2 : (x * y) ^ (n + 1) * (x * y) ^ (n + 1) = (x * y) ^ (n + 1) := by
    have := h1 (n + 1)
    rw [mul_pow] at this ⊢
    linear_combination y ^ (n + 1) * this
  rcases h _ h2 with h0 | h0
  · right
    exact ⟨n + 1, by rw [← h1 (n + 1), h0, mul_zero]⟩
  · left
    exact IsUnit.of_mul_eq_one (y * (x * y) ^ n) (by rw [← h0]; ring)

theorem semi_hensel {S : Type} [CommRing S] [Nontrivial S] (I : Ideal S) [hI : HenselianRing S I] [Finite (S ⧸ I)]
    (h : ∀ e : S, e * e = e → e = 0 ∨ e = 1) :
    ∃ _ : HenselianLocalRing S, Finite (ResidueField S) := by
  have hloc : IsLocalHom (Ideal.Quotient.mk I) := isLocalHom_of_le_jacobson_bot I hI.jac
  have hQ : ∀ e : S ⧸ I, e * e = e → e = 0 ∨ e = 1 := by
    intro e he
    obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective e
    have hm : (X ^ 2 - X : S[X]).Monic := by monicity!
    obtain ⟨a, ha, hae⟩ := hI.is_henselian (X ^ 2 - X) hm e
      (by rw [← Ideal.Quotient.eq_zero_iff_mem]; simp [pow_two, he])
      (by
        refine IsUnit.of_mul_eq_one (2 * Ideal.Quotient.mk I e - 1) ?_
        have : (derivative (X ^ 2 - X : S[X])).eval e = 2 * e - 1 := by
          simp; norm_num
        rw [this, map_sub, map_mul, map_ofNat, map_one]
        linear_combination 4 * he)
    have ha' : a * a = a := by
      have : a ^ 2 - a = 0 := by simpa using ha
      linear_combination this
    have hae' : Ideal.Quotient.mk I a = Ideal.Quotient.mk I e := Ideal.Quotient.eq.2 hae
    rcases h a ha' with h0 | h0
    · left; rw [← hae', h0, map_zero]
    · right; rw [← hae', h0, map_one]
  have hun : ∀ x : S, IsUnit x ∨ IsNilpotent (Ideal.Quotient.mk I x) := fun x =>
    (semi_unit_or_nil hQ _).imp_left (IsUnit.of_map _ x)
  have hL : IsLocalRing S := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a =>
    (hun a).imp_right fun hn => IsUnit.of_map (Ideal.Quotient.mk I) _ (by
      rw [map_sub, map_one]; exact hn.isUnit_one_sub)
  have hle : I ≤ maximalIdeal S := by
    rw [← jacobson_eq_maximalIdeal ⊥ bot_ne_top]; exact hI.jac
  have hnt : Nontrivial (S ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.2 fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.1 (h ▸ hle))
  have hnil : ∀ x : S, IsNilpotent (Ideal.Quotient.mk I x) → x ∈ maximalIdeal S := fun x hx hu =>
    hx.not_isUnit (hu.map _)
  refine ⟨{ hL with is_henselian := ?_ }, Finite.of_surjective (Ideal.Quotient.factor hle)
    (Ideal.Quotient.factor_surjective hle)⟩
  intro f hf a₀ h1 h2
  have hev : ∀ (g : S[X]) (a : S), aeval (Ideal.Quotient.mk I a) g = Ideal.Quotient.mk I (g.eval a) := fun g a =>
    aeval_algebraMap_apply_eq_algebraMap_eval a g
  obtain ⟨r, ⟨hr1, hr2⟩, -⟩ := Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero
    (P := f) (x := Ideal.Quotient.mk I a₀) (by rw [hev]; exact (hun _).resolve_left h1) (by rw [hev]; exact h2.map _)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hr : a₀ - r ∈ maximalIdeal S := hnil _ (by rw [map_sub]; exact hr1)
  have hu : IsUnit (f.derivative.eval r) := by
    by_contra hn
    have hn' : f.derivative.eval r ∈ maximalIdeal S := hn
    have h3 : f.derivative.eval a₀ - f.derivative.eval r ∈ maximalIdeal S :=
      Ideal.mem_of_dvd _ (Polynomial.sub_dvd_eval_sub _ _ _) hr
    have h4 : f.derivative.eval a₀ ∈ maximalIdeal S := by simpa using add_mem h3 hn'
    exact h4 h2
  obtain ⟨a, ha, har⟩ := hI.is_henselian f hf r (by rw [← Ideal.Quotient.eq_zero_iff_mem, ← hev, hr2]) (hu.map _)
  refine ⟨a, ha, ?_⟩
  simpa using sub_mem (hle har) hr

theorem semi_hensel_padic (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [Nontrivial S] [Algebra ℤ_[p] S]
    [Module.Finite ℤ_[p] S] (h : ∀ e : S, e * e = e → e = 0 ∨ e = 1) :
    ∃ _ : HenselianLocalRing S, Finite (ResidueField S) := by
  have h1 := semi_complete (A := ℤ_[p]) S
  have h2 : IsAdicComplete ((maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] S)) S :=
    (IsAdicComplete.map_algebraMap_iff _ _).2 h1
  have h3 : Finite (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) :=
    Finite.of_equiv _ (PadicInt.residueField (p := p)).symm.toEquiv
  have h4 : Module.Finite (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) (S ⧸ (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] S)) :=
    Module.Finite.of_restrictScalars_finite ℤ_[p] _ _
  have h5 : Finite (S ⧸ (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] S)) :=
    Module.finite_of_finite (ℤ_[p] ⧸ maximalIdeal ℤ_[p])
  exact semi_hensel ((maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] S)) h

theorem semi_local (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [Nontrivial R] [Algebra ℤ_[p] R]
    [Module.Finite ℤ_[p] R] (σ : R →ₐ[ℤ_[p]] R) (hσ : ∀ r, σ (σ r) = r) (hθ : ∃ θ : R, IsUnit (θ - σ θ))
    (h : ∀ e : R, e * e = e → σ e = e → e = 0 ∨ e = 1) (n : ℕ) (A : Matrix (Fin n) (Fin n) R)
    (hA : (A.map σ).transpose = A) (hd : IsUnit A.det) :
    ∃ g : Matrix (Fin n) (Fin n) R, (g.map σ).transpose * A * g = 1 := by
  let S : Subalgebra ℤ_[p] R := AlgHom.equalizer σ (AlgHom.id _ _)
  have hfin : Module.Finite ℤ_[p] S := Module.Finite.of_injective S.val.toLinearMap Subtype.val_injective
  obtain ⟨hH, hF⟩ := semi_hensel_padic p S fun e he =>
    (h e.1 (congrArg Subtype.val he) e.2).imp Subtype.ext Subtype.ext
  let τ : R ≃+* R := RingEquiv.ofBijective σ.toRingHom (Function.Involutive.bijective hσ)
  obtain ⟨g, -, hg⟩ := @Formalism.HermitianLatticesTheory.unimodUnramUnique R _ τ hσ S.toSubring (fun _ => Iff.rfl) hH hF hθ n A hA hd
  exact ⟨g, hg⟩

theorem semi_congr {Z R : Type} [CommRing Z] [CommRing R] [Algebra Z R] (σ : R →ₐ[Z] R) (J : Ideal R)
    (hJ : ∀ x ∈ J, σ x ∈ J) {n : ℕ} (A g g' : Matrix (Fin n) (Fin n) R) (h : ∀ i j, g i j - g' i j ∈ J) (i j : Fin n) :
    ((g.map σ).transpose * A * g) i j - ((g'.map σ).transpose * A * g') i j ∈ J := by
  have h1 : ∀ i j, Ideal.Quotient.mk J (g i j) = Ideal.Quotient.mk J (g' i j) := fun i j => Ideal.Quotient.eq.2 (h i j)
  have h2 : ∀ i j, Ideal.Quotient.mk J (σ (g i j)) = Ideal.Quotient.mk J (σ (g' i j)) := fun i j =>
    Ideal.Quotient.eq.2 (by rw [← map_sub]; exact hJ _ (h i j))
  rw [← Ideal.Quotient.eq]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, h1, h2]

theorem semi_main (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [Algebra ℤ_[p] R]
    [Module.Finite ℤ_[p] R] (σ : R →ₐ[ℤ_[p]] R) (hσ : ∀ r, σ (σ r) = r) (hθ : ∃ θ : R, IsUnit (θ - σ θ))
    (n : ℕ) (A : Matrix (Fin n) (Fin n) R) (hA : (A.map σ).transpose = A) (hd : IsUnit A.det) (I : Ideal R) :
    (∀ x ∈ I, σ x ∈ I) → ∃ g : Matrix (Fin n) (Fin n) R, ∀ i j,
      ((g.map σ).transpose * A * g) i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I := by
  have hN : IsNoetherianRing R := IsNoetherianRing.of_finite ℤ_[p] R
  induction I using IsNoetherian.induction with
  | hgt I ih =>
  intro hI
  by_cases htop : I = ⊤
  · exact ⟨1, fun i j => htop ▸ Submodule.mem_top⟩
  by_cases he : ∃ e : R, e * e - e ∈ I ∧ σ e - e ∈ I ∧ e ∉ I ∧ 1 - e ∉ I
  · obtain ⟨e, he1, he2, he3, he4⟩ := he
    have hst : ∀ u : R, σ u - u ∈ I → ∀ x ∈ I ⊔ Ideal.span {u}, σ x ∈ I ⊔ Ideal.span {u} := by
      intro u hu x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hb
      have : σ (a + r * u) = (σ a + σ r * (σ u - u)) + σ r * u := by rw [map_add, map_mul]; ring
      rw [this]
      exact Submodule.add_mem_sup (add_mem (hI a ha) (Ideal.mul_mem_left I _ hu)) (Ideal.mem_span_singleton'.2 ⟨_, rfl⟩)
    have hgt : ∀ u : R, u ∉ I → I < I ⊔ Ideal.span {u} := fun u hu =>
      lt_of_le_of_ne le_sup_left fun h => hu (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self u))
    have he2' : σ (1 - e) - (1 - e) ∈ I := by
      have := neg_mem he2
      rw [map_sub, map_one]
      convert this using 1
      ring
    obtain ⟨g₁, hg₁⟩ := ih _ (hgt e he3) (hst e he2)
    obtain ⟨g₂, hg₂⟩ := ih _ (hgt (1 - e) he4) (hst _ he2')
    let g : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => (1 - e) * g₁ i j + e * g₂ i j
    refine ⟨g, fun i j => ?_⟩
    have k₁ := add_mem (semi_congr σ _ (hst e he2) A g g₁ (fun i j =>
      Ideal.mem_sup_right (Ideal.mem_span_singleton'.2 ⟨g₂ i j - g₁ i j, by simp only [g, Matrix.of_apply]; ring⟩)) i j) (hg₁ i j)
    have k₂ := add_mem (semi_congr σ _ (hst _ he2') A g g₂ (fun i j =>
      Ideal.mem_sup_right (Ideal.mem_span_singleton'.2 ⟨g₁ i j - g₂ i j, by simp only [g, Matrix.of_apply]; ring⟩)) i j) (hg₂ i j)
    rw [sub_add_sub_cancel] at k₁ k₂
    generalize ((g.map σ).transpose * A * g) i j - (1 : Matrix (Fin n) (Fin n) R) i j = x at k₁ k₂ ⊢
    obtain ⟨a, ha, b, hb, h1⟩ := Submodule.mem_sup.1 k₁
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    obtain ⟨a', ha', b', hb', h2⟩ := Submodule.mem_sup.1 k₂
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hb'
    have : x = (1 - e) * a + e * a' - (r + s) * (e * e - e) := by
      linear_combination (-(1 - e)) * h1 - e * h2
    rw [this]
    exact sub_mem (add_mem (Ideal.mul_mem_left I _ ha) (Ideal.mul_mem_left I _ ha')) (Ideal.mul_mem_left I _ he1)
  · have hnt : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 htop
    let τ : (R ⧸ I) →ₐ[ℤ_[p]] (R ⧸ I) := Ideal.quotientMapₐ I σ hI
    have hτ : ∀ x, τ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (σ x) := fun x => rfl
    obtain ⟨g, hg⟩ := semi_local p (R ⧸ I) τ
      (fun r => by obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r; rw [hτ, hτ, hσ])
      (by
        obtain ⟨θ, h⟩ := hθ
        exact ⟨Ideal.Quotient.mk I θ, by rw [hτ, ← map_sub]; exact h.map _⟩)
      (fun e h1 h2 => by
        obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective e
        by_contra hc
        rw [not_or] at hc
        refine he ⟨e, Ideal.Quotient.eq.1 h1, Ideal.Quotient.eq.1 h2, fun h => hc.1 ?_, fun h => hc.2 ?_⟩
        · exact Ideal.Quotient.eq_zero_iff_mem.2 h
        · exact (Ideal.Quotient.eq.2 h).symm)
      n (A.map (Ideal.Quotient.mk I))
      (by
        ext i j
        have := congrFun (congrFun hA i) j
        simp only [Matrix.transpose_apply, Matrix.map_apply] at this ⊢
        rw [hτ, this])
      (by
        have := hd.map (Ideal.Quotient.mk I)
        rwa [RingHom.map_det] at this)
    choose G hG using fun i j => Ideal.Quotient.mk_surjective (g i j)
    refine ⟨Matrix.of G, fun i j => ?_⟩
    have := congrFun (congrFun hg i) j
    rw [← Ideal.Quotient.eq]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul,
      ← hG, hτ] at this ⊢
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem tw_g_semi : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [Algebra ℤ_[p] R] [Module.Finite ℤ_[p] R] (σ : R →ₐ[ℤ_[p]] R), (∀ r, σ (σ r) = r) → (∃ θ : R, IsUnit (θ - σ θ)) → ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) R), (A.map σ).transpose = A → IsUnit A.det → ∃ g : Matrix (Fin n) (Fin n) R, IsUnit g.det ∧ (g.map σ).transpose * A * g = 1 := by
  intro p _ R _ _ _ σ hσ hθ n A hA hd
  obtain ⟨g, hg⟩ := semi_main p R σ hσ hθ n A hA hd ⊥ (fun x hx => by rw [Ideal.mem_bot.1 hx, map_zero]; rfl)
  have h : (g.map σ).transpose * A * g = 1 := by
    ext i j
    exact sub_eq_zero.1 (Ideal.mem_bot.1 (hg i j))
  exact ⟨g, Matrix.isUnit_det_of_left_inverse h, h⟩

end PositivityTheory.UnitarySelfGeneration
