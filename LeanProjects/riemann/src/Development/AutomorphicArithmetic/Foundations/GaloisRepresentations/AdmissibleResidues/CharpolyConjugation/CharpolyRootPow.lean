import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.IsAutomorphicOverImagQuad
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unlfrob
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unlres
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unliso
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unlwd

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.GalN.V

section

variable {F Ω K : Type} [Field F] [Field Ω] [Algebra F Ω] [Field K] [Algebra F K] [Algebra K Ω]
  [IsScalarTower F K Ω]

private def resK (K : Type) [Field K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]
    (σ : G F Ω) : K →ₐ[F] Ω :=
  (σ : Ω →ₐ[F] Ω).comp (IsScalarTower.toAlgHom F K Ω)

private theorem resK_apply (σ : G F Ω) (x : K) : resK K σ x = σ (algebraMap K Ω x) := rfl

private theorem lift_of_fix (σ : G F Ω) (h : ∀ x : K, σ (algebraMap K Ω x) = algebraMap K Ω x) :
    ∃ τ : G K Ω, (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω) τ = σ := by
  exact ⟨AlgEquiv.ofRingEquiv (f := (σ : Ω ≃+* Ω)) h, by ext x; rfl⟩

private theorem lift_of_res {σ τ : G F Ω} (h : resK K σ = resK K τ) :
    ∃ u : G K Ω, (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω) u = σ⁻¹ * τ := by
  apply lift_of_fix
  intro x
  have e := congrArg (fun f => f x) h
  simp only [resK_apply] at e
  rw [AlgEquiv.mul_apply, ← e]
  simp

private theorem exists_pow_lift [Finite (K →ₐ[F] Ω)] (s : G F Ω) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ u : G K Ω,
      (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω) u = s ^ m := by
  obtain ⟨a, b, hne, hab⟩ := Finite.exists_ne_map_eq_of_infinite (fun m : ℕ => resK K (s ^ m))
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨u, hu⟩ := lift_of_res (K := K) hab
    refine ⟨b - a, by omega, u, ?_⟩
    rw [hu, inv_mul_eq_iff_eq_mul, ← pow_add, Nat.add_sub_cancel' hlt.le]
  · obtain ⟨u, hu⟩ := lift_of_res (K := K) hab.symm
    refine ⟨a - b, by omega, u, ?_⟩
    rw [hu, inv_mul_eq_iff_eq_mul, ← pow_add, Nat.add_sub_cancel' hlt.le]

end

section

variable {F Ω K : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [Field K] [NumberField K]
  [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]

private theorem isFrob_descend {A : ValuationSubring Ω} {q : ℕ} {u : G K Ω}
    (h : IsFrob A q ((AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω) u)) : IsFrob A q u :=
  ⟨h.1, h.2⟩

private theorem ine_descend {A : ValuationSubring Ω} {u : G K Ω}
    (h : (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω) u ∈ Ine (F := F) A) :
    u ∈ Ine (F := K) A :=
  ⟨h.1, h.2⟩

private theorem isFrob_pow {A : ValuationSubring Ω} {q : ℕ} {σ : G F Ω} (h : IsFrob A q σ) (k : ℕ) :
    IsFrob A (q ^ k) (σ ^ k) := by
  obtain ⟨hd, hf⟩ := h
  have hint : ∀ τ : G F Ω, τ ∈ ValuationSubring.decompositionSubgroup F A →
      ∀ y : Ω, A.valuation y ≤ 1 → A.valuation (τ y) ≤ 1 := by
    intro τ hτ y hy
    by_contra hc
    push_neg at hc
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp at hc
    have hprod : ∀ z : Ω, z ≠ 0 → A.valuation z * A.valuation z⁻¹ = 1 := fun z hz => by
      rw [← map_mul, mul_inv_cancel₀ hz, map_one]
    have h1 : A.valuation (τ y⁻¹) < 1 := by
      by_contra h'
      push_neg at h'
      have e := hprod (τ y) (by simpa using hy0)
      rw [← map_inv₀ τ] at e
      exact absurd e (ne_of_gt (one_lt_mul_of_lt_of_le hc h'))
    rw [valuation_apply_lt_one_iff (A := A) hτ] at h1
    have e := hprod y hy0
    exact absurd e (ne_of_lt (lt_of_le_of_lt (mul_le_of_le_one_left' hy) h1))
  refine ⟨pow_mem hd k, ?_⟩
  induction k with
  | zero =>
    intro x _
    simp
  | succ k ih =>
    intro x hx
    set y := (σ ^ k) x with hydef
    have hy : A.valuation y ≤ 1 := hint _ (pow_mem hd k) x hx
    have hz : A.valuation (x ^ q ^ k) ≤ 1 := by
      rw [map_pow]
      exact pow_le_one' hx _
    have e : (σ ^ (k + 1)) x - x ^ q ^ (k + 1) = (σ y - y ^ q) + (y ^ q - (x ^ q ^ k) ^ q) := by
      rw [show σ ^ (k + 1) = σ * σ ^ k from pow_succ' σ k, show q ^ (k + 1) = q ^ k * q from pow_succ q k,
        pow_mul, AlgEquiv.mul_apply]
      ring
    rw [e]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt (hf y hy) ?_)
    rw [← geom_sum₂_mul, map_mul]
    have hs : A.valuation (∑ i ∈ Finset.range q, y ^ i * (x ^ q ^ k) ^ (q - 1 - i)) ≤ 1 := by
      apply Valuation.map_sum_le
      intro i _
      rw [map_mul, map_pow, map_pow]
      exact mul_le_one' (pow_le_one' hy _) (pow_le_one' hz _)
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hs) (ih x hx)

private theorem ine_finite [Finite (K →ₐ[F] Ω)] {l : ℕ} [Fact l.Prime] {n : ℕ}
    (r : G F Ω →* GL (Fin n) (Qbar l)) (A : ValuationSubring Ω)
    (h : ((r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) ''
      (Ine (F := K) A : Set (G K Ω))).Finite) :
    (r '' (Ine (F := F) A : Set (G F Ω))).Finite := by
  classical
  let c : (K →ₐ[F] Ω) → GL (Fin n) (Qbar l) := fun φ =>
    if hφ : ∃ g ∈ Ine (F := F) A, resK K g = φ then r (Classical.choose hφ) else 1
  refine ((Set.finite_univ.prod h).image (fun p : (K →ₐ[F] Ω) × GL (Fin n) (Qbar l) => c p.1 * p.2)).subset ?_
  rintro _ ⟨σ, hσ, rfl⟩
  have hex : ∃ g ∈ Ine (F := F) A, resK K g = resK K σ := ⟨σ, hσ, rfl⟩
  obtain ⟨hg, hgres⟩ := Classical.choose_spec hex
  obtain ⟨u, hu⟩ := lift_of_res (K := K) hgres
  have huI : u ∈ Ine (F := K) A := ine_descend (by rw [hu]; exact mul_mem (inv_mem hg) hσ)
  refine ⟨(resK K σ, r (AlgEquiv.restrictScalarsHom F u)), ⟨Set.mem_univ _, u, huI, rfl⟩, ?_⟩
  show c (resK K σ) * r ((AlgEquiv.restrictScalarsHom F) u) = r σ
  simp only [c, dif_pos hex]
  rw [hu, map_mul, map_inv, mul_inv_cancel_left]

end

private theorem charpoly_root_pow {k : Type} [Field k] [IsAlgClosed k] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) k) {N : ℕ} (hN : 0 < N) {α : k}
    (h : (M ^ N).charpoly.IsRoot α) : ∃ a, M.charpoly.IsRoot a ∧ a ^ N = α := by
  rw [← Matrix.mem_spectrum_iff_isRoot_charpoly, spectrum.map_pow_of_pos M hN] at h
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a, Matrix.mem_spectrum_iff_isRoot_charpoly.1 ha, rfl⟩

private theorem noLink_pow {l : ℕ} [Fact l.Prime] {n : ℕ} {x : GL (Fin n) (Qbar l)} {Q : ℕ}
    (h : NoLink x Q) {N : ℕ} (hN : 0 < N) : NoLink (x ^ N) (Q ^ N) := by
  intro α β hα hβ k hk heq
  rw [Units.val_pow_eq_pow_val] at hα hβ
  obtain ⟨a, ha, rfl⟩ := charpoly_root_pow _ hN hα
  obtain ⟨b, hb, rfl⟩ := charpoly_root_pow _ hN hβ
  apply h a b ha hb (N * k) (Nat.mul_pos hN hk)
  rw [pow_mul, pow_mul, mul_pow]
  push_cast at heq
  exact heq

theorem UpperTheory.GalN.V.L.wup :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω], Unlinked r → Unlinked (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) := by
  intro F Ω _ _ _ _ _ l _ n r K _ _ _ _ _ hU
  intro w hl A hA hfin
  haveI : Finite (K →ₐ[F] Ω) := inferInstance
  set v := HeightOneSpectrum.under (𝓞 F) w with hvdef
  have hAv : IsPlaceOver A v := GlobalTheory.AboveL.SatBC.isPlaceOver_under hA
  have hlv : (l : 𝓞 F) ∉ v.asIdeal := by
    intro hm
    apply hl
    have hw : algebraMap (𝓞 F) (𝓞 K) (l : 𝓞 F) ∈ w.asIdeal := hm
    simpa using hw
  obtain ⟨s, j, hj, hfrob, hnl⟩ := hU v hlv A hAv (ine_finite r A hfin)
  obtain ⟨m, hm, u, hu⟩ := exists_pow_lift (K := K) s
  set f := w.asIdeal.inertiaDeg (𝓞 F) with hfdef
  have hnorm : normV w = normV v ^ f := GlobalTheory.AboveL.SatBC.normV_under_pow F K w
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hnorm
      unfold normV at hnorm
      haveI := w.isPrime
      obtain ⟨hs, _⟩ := Nat.card_eq_one_iff_unique.1 hnorm
      exact not_subsingleton _ hs
    · exact h0
  have e : normV w ^ (j * m) = (normV v ^ j) ^ (m * f) := by
    rw [hnorm, ← pow_mul, ← pow_mul]
    ring_nf
  refine ⟨u ^ f, j * m, Nat.mul_pos hj hm, ?_, ?_⟩
  · apply isFrob_descend (F := F)
    rw [map_pow, hu, ← pow_mul, e]
    exact isFrob_pow hfrob (m * f)
  · rw [MonoidHom.comp_apply, map_pow, hu, ← pow_mul, e, map_pow r]
    exact noLink_pow hnl (Nat.mul_pos hm hf)
