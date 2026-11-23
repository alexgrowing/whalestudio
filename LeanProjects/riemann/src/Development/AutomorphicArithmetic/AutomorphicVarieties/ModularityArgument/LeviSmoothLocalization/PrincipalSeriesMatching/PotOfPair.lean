import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PotOfPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PotOfFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IneConj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter UpperTheory.V.Af
open scoped Pointwise

section Mat

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ}

private def revM (k : Type) [Field k] (n : ℕ) : Matrix (Fin n) (Fin n) k := (1 : Matrix (Fin n) (Fin n) k).submatrix Fin.rev id

private theorem revM_mul (M : Matrix (Fin n) (Fin n) k) : revM k n * M = M.submatrix Fin.rev id := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [revM, Matrix.submatrix_apply, id, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

private theorem mul_revM (M : Matrix (Fin n) (Fin n) k) : M * revM k n = M.submatrix id Fin.rev := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [revM, Matrix.submatrix_apply, id, Matrix.one_apply, Fin.rev_eq_iff, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

private theorem revM_sq : revM k n * revM k n = 1 := by
  rw [revM_mul]
  ext i j
  simp [revM, Matrix.one_apply]

private theorem flag_rev (r : Γ →* GL (Fin n) k) {H H' : Subgroup Γ} (f : ↥H' →* ↥H) (μ : ↥H' →* kˣ) (P : GL (Fin n) k)
    (hp : ∀ u : ↥H', (r (f u) : Matrix (Fin n) (Fin n) k).transpose * (P : Matrix (Fin n) (Fin n) k) *
      (r u : Matrix (Fin n) (Fin n) k) = (μ u : k) • (P : Matrix (Fin n) (Fin n) k))
    {κ : Fin n → ↥H →* kˣ} (hκ : IsFlagOn r H κ) :
    IsFlagOn r H' fun i => μ * ((κ (Fin.rev i)).comp f)⁻¹ := by
  obtain ⟨h, hh⟩ := hκ
  let Dt : GL (Fin n) k := ⟨((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).transpose, (h : Matrix (Fin n) (Fin n) k).transpose,
    by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel]; simp,
    by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel]; simp⟩
  let J : GL (Fin n) k := ⟨revM k n, revM k n, revM_sq, revM_sq⟩
  have key : ∀ u : ↥H', ((Dt * P * r u * (Dt * P)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      (μ u : k) • ((h * r ((f u)⁻¹ : ↥H) * h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).transpose := by
    intro u
    have hinv : (r ((f u)⁻¹ : ↥H) : Matrix (Fin n) (Fin n) k).transpose * (r (f u) : Matrix (Fin n) (Fin n) k).transpose = 1 := by
      rw [← Matrix.transpose_mul, ← Units.val_mul, ← map_mul]
      simp
    have e1 : (P : Matrix (Fin n) (Fin n) k) * (r u : Matrix (Fin n) (Fin n) k) =
        (μ u : k) • ((r ((f u)⁻¹ : ↥H) : Matrix (Fin n) (Fin n) k).transpose * (P : Matrix (Fin n) (Fin n) k)) := by
      rw [← Matrix.mul_smul, ← hp u, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
    have e2 : ((Dt * P * r u : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
        ((μ u : k) • ((h * r ((f u)⁻¹ : ↥H) * h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).transpose) *
          ((Dt * P : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
      have e3 : (h : Matrix (Fin n) (Fin n) k).transpose * ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).transpose = 1 := by
        rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel]
        simp
      simp only [Units.val_mul, Matrix.transpose_mul, Matrix.smul_mul]
      change ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).transpose * (P : Matrix (Fin n) (Fin n) k) * (r u : Matrix (Fin n) (Fin n) k) = _
      rw [Matrix.mul_assoc, e1, Matrix.mul_smul]
      congr 1
      change _ = _ * (((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).transpose * (P : Matrix (Fin n) (Fin n) k))
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (h : Matrix (Fin n) (Fin n) k).transpose, e3, Matrix.one_mul]
    rw [Units.val_mul, e2, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel]
    simp
  refine ⟨J * (Dt * P), fun u => ?_⟩
  have e : (J * (Dt * P) * r u * (J * (Dt * P))⁻¹ : GL (Fin n) k) = J * (Dt * P * r u * (Dt * P)⁻¹) * J⁻¹ := by group
  have e' : ∀ i j, (J * (Dt * P) * r u * (J * (Dt * P))⁻¹ : GL (Fin n) k) i j =
      (μ u : k) * (h * r ((f u)⁻¹ : ↥H) * h⁻¹ : GL (Fin n) k) (Fin.rev j) (Fin.rev i) := by
    intro i j
    rw [e]
    have : ((J * (Dt * P * r u * (Dt * P)⁻¹) * J⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
        revM k n * ((Dt * P * r u * (Dt * P)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * revM k n := rfl
    rw [this, revM_mul, mul_revM, key]
    simp only [Matrix.submatrix_apply, Matrix.smul_apply, Matrix.transpose_apply, id, smul_eq_mul]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [e', (hh ((f u)⁻¹)).1 _ _ (Fin.rev_lt_rev.2 hij), mul_zero]
  · rw [e', (hh ((f u)⁻¹)).2]
    simp [div_eq_mul_inv]

end Mat

section Gal

private theorem pow_flag {U : Type} [CommGroup U] (x y : U) (m : ℤ) (k : ℕ) (h : (x * y ^ (-m)) ^ k = 1) :
    x ^ k = (y ^ m) ^ k := by
  rw [mul_pow, zpow_neg, inv_pow, mul_inv_eq_one] at h
  exact h

private theorem pow_dual {U : Type} [CommGroup U] (x y : U) (b m : ℤ) (a : ℕ) (h : x ^ a = (y ^ m) ^ a) :
    (y ^ b * x⁻¹) ^ a = (y ^ (b - m)) ^ a := by
  rw [mul_pow, inv_pow, h, zpow_sub, mul_pow, inv_pow]

private theorem char_conj {Γ U : Type} [Group Γ] [CommGroup U] (χ : Γ →* U) (g u : Γ) : χ (g⁻¹ * u * g) = χ u := by
  rw [map_mul, map_mul, map_inv, mul_comm (χ g)⁻¹, inv_mul_cancel_right]

private theorem gap {n : ℕ} {m : Fin n → ℤ} (hm : ∀ i j, i < j → m j + 2 ≤ m i) (i j : Fin n) : m i ≠ m j + 1 := by
  rcases lt_trichotomy i j with h | h | h
  · have := hm i j h
    omega
  · subst h
    omega
  · have := hm j i h
    omega

variable {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]

private theorem place_unique {F : Type} [Field F] [NumberField F] [Algebra F Ω] {A : ValuationSubring Ω}
    {w w' : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) (h' : IsPlaceOver A w') : w = w' :=
  HeightOneSpectrum.ext (Ideal.ext fun x => (h x).symm.trans (h' x))

private theorem place_smul (g : G L Ω) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A w) :
    IsPlaceOver (g • A) w := fun x => by
  have hA' : ∀ y, g.toRingEquiv y ∈ g • A ↔ y ∈ A := fun y => ValuationSubring.smul_mem_pointwise_smul_iff
  have e : g.toRingEquiv (algebraMap L Ω (x : L)) = algebraMap L Ω (x : L) := g.commutes _
  have h1 := val_lt_one hA' (algebraMap L Ω (x : L))
  rw [e] at h1
  exact h1.trans (h x)

private theorem place_under {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A w) :
    IsPlaceOver A (w.under (𝓞 (W.Lp L))) := fun x => by
  rw [IsScalarTower.algebraMap_apply (W.Lp L) L Ω]
  exact h (algebraMap (𝓞 (W.Lp L)) (𝓞 L) x)

private instance normalLp : Normal (W.Lp L) L :=
  (Algebra.IsQuadraticExtension.isGalois (W.Lp L) L).to_normal

private theorem range_iff (γ : G (W.Lp L) Ω) :
    γ ∈ (W.resP L Ω).range ↔ AlgEquiv.restrictNormalHom L γ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    refine AlgEquiv.ext fun x => (algebraMap L Ω).injective ?_
    have h := AlgEquiv.restrictNormal_commutes (W.resP L Ω u) L x
    exact h.trans (u.commutes x)
  · intro h
    refine ⟨AlgEquiv.ofRingEquiv (f := γ.toRingEquiv) fun y => ?_, AlgEquiv.ext fun _ => rfl⟩
    have h1 : γ.restrictNormal L = 1 := h
    have h2 := AlgEquiv.restrictNormal_commutes γ L y
    rw [h1] at h2
    exact h2.symm

private theorem norm_res (c : G (W.Lp L) Ω) (u : G L Ω) : ∃ u' : G L Ω, W.resP L Ω u' = c⁻¹ * W.resP L Ω u * c := by
  have h : c⁻¹ * W.resP L Ω u * c ∈ (W.resP L Ω).range := by
    rw [range_iff, map_mul, map_mul, (range_iff (W.resP L Ω u)).1 ⟨u, rfl⟩, map_inv]
    simp
  exact h

private theorem conj_not_mem {c : G (W.Lp L) Ω} (hc : ∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x)) :
    c ∉ (W.resP L Ω).range := by
  rintro ⟨u, rfl⟩
  obtain ⟨j, hj⟩ := hc
  refine IsCMField.complexConj_ne_one L (AlgEquiv.ext fun x => ?_)
  apply (j.comp (algebraMap L Ω)).injective
  have h1 := IsCMField.complexEmbedding_complexConj L (j.comp (algebraMap L Ω)) x
  have h2 := hj (algebraMap L Ω x)
  have h3 : (W.resP L Ω u) (algebraMap L Ω x) = algebraMap L Ω x := u.commutes x
  rw [h3] at h2
  rw [h1]
  exact h2.symm

private theorem exists_res_mul {c γ : G (W.Lp L) Ω} (hc : c ∉ (W.resP L Ω).range) (hγ : γ ∉ (W.resP L Ω).range) :
    ∃ g : G L Ω, W.resP L Ω g = γ * c⁻¹ := by
  have hcard : Nat.card (L ≃ₐ[W.Lp L] L) = 2 :=
    (IsGalois.card_aut_eq_finrank (W.Lp L) L).trans (Algebra.IsQuadraticExtension.finrank_eq_two (W.Lp L) L)
  obtain ⟨t, -, hu⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[W.Lp L] L)).1 hcard
  have h1 := hu _ (fun e => hc ((range_iff c).2 e))
  have h2 := hu _ (fun e => hγ ((range_iff γ).2 e))
  have h : γ * c⁻¹ ∈ (W.resP L Ω).range := by
    rw [range_iff, map_mul, map_inv, h1, h2, mul_inv_cancel]
  exact h

variable {l : ℕ} [Fact l.Prime] {n : ℕ}

private def FlagAt (ρ : G L Ω →* GL (Fin n) (Qbar l)) (A : ValuationSubring Ω) (m : Fin n → ℤ) : Prop :=
  ∃ (κ : Fin n → ↥(Dec (F := L) A) →* (Qbar l)ˣ) (a : ℕ), 0 < a ∧ IsFlagOn ρ (Dec (F := L) A) κ ∧
    ∀ i (s : ↥(Dec (F := L) A)), (s : G L Ω) ∈ Ine (F := L) A → κ i s ^ a = (cycBar L Ω l s ^ m i) ^ a

private theorem FlagAt.smul {ρ : G L Ω →* GL (Fin n) (Qbar l)} {A : ValuationSubring Ω} {m : Fin n → ℤ} (g : G L Ω)
    (h : FlagAt ρ A m) : FlagAt ρ (g • A) m := by
  obtain ⟨κ, a, ha, ⟨x, hx⟩, hp⟩ := h
  let f : ↥(Dec (F := L) (g • A)) →* ↥(Dec (F := L) A) :=
    { toFun := fun u => ⟨g⁻¹ * u * g, by
        have hu := mem_Dec.1 u.2
        rw [mem_Dec, mul_smul, mul_smul, hu, inv_smul_smul]⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  refine ⟨fun i => (κ i).comp f, a, ha, ⟨x * (ρ g)⁻¹, fun u => ?_⟩, fun i s hs => ?_⟩
  · have e1 : ((f u : ↥(Dec (F := L) A)) : G L Ω) = g⁻¹ * u * g := rfl
    have e : x * (ρ g)⁻¹ * ρ u * (x * (ρ g)⁻¹)⁻¹ = x * ρ (f u : ↥(Dec (F := L) A)) * x⁻¹ := by
      rw [e1, map_mul, map_mul, map_inv]
      group
    rw [e]
    exact hx (f u)
  · have h1 := hp i (f s) ((UpperTheory.V.Two.ineConj L Ω g).1 A s hs)
    have e1 : ((f s : ↥(Dec (F := L) A)) : G L Ω) = g⁻¹ * s * g := rfl
    have e : cycBar L Ω l (f s : ↥(Dec (F := L) A)) = cycBar L Ω l s := by rw [e1, char_conj]
    rw [e] at h1
    exact h1

private theorem FlagAt.dual {ρ : G L Ω →* GL (Fin n) (Qbar l)} {A : ValuationSubring Ω} {m : Fin n → ℤ}
    (c : G (W.Lp L) Ω) (a₀ : ℤ) (P : GL (Fin n) (Qbar l)) (hP : IsPairing c ρ (cycBar L Ω l ^ a₀) P)
    (h : FlagAt ρ A m) : FlagAt ρ (c • A) fun i => a₀ - m (Fin.rev i) := by
  choose t ht using norm_res (L := L) (Ω := Ω) c
  have hinj : Function.Injective (W.resP L Ω) := fun a b e => AlgEquiv.ext fun x => DFunLike.congr_fun e x
  let f : ↥(Dec (F := L) (c • A)) →* ↥(Dec (F := L) A) :=
    { toFun := fun u => ⟨t u, by
        have hu : W.resP L Ω u • c • A = c • A := mem_Dec.1 u.2
        refine mem_Dec.2 ?_
        show W.resP L Ω (t u) • A = A
        rw [ht, mul_smul, mul_smul, hu, inv_smul_smul]⟩
      map_one' := Subtype.ext (hinj (by
        have e1 : W.resP L Ω (1 : G L Ω) = 1 := map_one _
        change W.resP L Ω (t 1) = W.resP L Ω 1
        rw [ht, e1]
        group))
      map_mul' := fun a b => Subtype.ext (hinj (by
        simp only [Subgroup.coe_mul, map_mul, ht]
        group)) }
  obtain ⟨κ, a, ha, hf, hp⟩ := h
  let μ : ↥(Dec (F := L) (c • A)) →* (Qbar l)ˣ := ((cycBar L Ω l ^ a₀).comp (Dec (F := L) A).subtype).comp f
  refine ⟨fun i => μ * ((κ (Fin.rev i)).comp f)⁻¹, a, ha, flag_rev ρ f μ P (fun u => ?_) hf, fun i s hs => ?_⟩
  · refine hP (t u) u ?_
    have e := ht u
    change W.resP L Ω u = c * W.resP L Ω (t u) * c⁻¹
    rw [e]
    group
  · have hs' : ((f s : ↥(Dec (F := L) A)) : G L Ω) ∈ Ine (F := L) A := by
      have h1 := (UpperTheory.V.Two.ineConj (W.Lp L) Ω c).1 A (W.resP L Ω s) hs
      rw [← ht] at h1
      exact h1
    have h2 := hp (Fin.rev i) (f s) hs'
    have e : cycBar L Ω l (f s : ↥(Dec (F := L) A)) = cycBar L Ω l s := by
      change cycBar (W.Lp L) Ω l (W.resP L Ω (t s)) = cycBar (W.Lp L) Ω l (W.resP L Ω s)
      rw [ht, char_conj]
    rw [e] at h2
    change (cycBar L Ω l (f s : ↥(Dec (F := L) A)) ^ a₀ * (κ (Fin.rev i) (f s))⁻¹) ^ a = _
    rw [e]
    exact pow_dual _ _ _ _ _ h2

end Gal

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.potOfPair :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.PotOfPair := by
  intro l _ L Ω _ _ _ _ _ _ s n ρ a P hP ψ m hm hfl hk w hw
  obtain ⟨k, hk0, hk⟩ := hk
  obtain ⟨v, hvw⟩ : ∃ v : W.Vl l L, v.1 = w.under (𝓞 (W.Lp L)) :=
    ⟨⟨w.under (𝓞 (W.Lp L)), Ideal.mem_comap.2 (by simpa using hw)⟩, rfl⟩
  have hf : FlagAt ρ (s.A v.1) (m v) :=
    ⟨ψ v, k, hk0, hfl v, fun i g hg => pow_flag _ _ _ _ (hk v i g hg)⟩
  by_cases hw' : w = s.w v.1
  · refine potOfFlag L Ω l n ρ (m v) (gap (hm v)) w hw fun A hA => ?_
    obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (hw' ▸ s.hw v.1) hA
    exact hf.smul g
  · refine potOfFlag L Ω l n ρ (fun i => a - m v (Fin.rev i)) (gap fun i j hij => ?_) w hw fun A hA => ?_
    · have := hm v (Fin.rev j) (Fin.rev i) (Fin.rev_lt_rev.2 hij)
      omega
    have h1 : IsPlaceOver A v.1 := hvw ▸ place_under hA
    obtain ⟨γ, hγ⟩ := exists_smul_eq_of_isPlaceOver (s.hA v.1) h1
    have hγ' : γ ∉ (W.resP L Ω).range := by
      rintro ⟨g, rfl⟩
      exact hw' (place_unique hA (hγ ▸ place_smul g (s.hw v.1)))
    obtain ⟨g, hg⟩ := exists_res_mul (conj_not_mem s.hc) hγ'
    have e : A = g • s.c • s.A v.1 := by
      rw [← hγ]
      change γ • s.A v.1 = W.resP L Ω g • s.c • s.A v.1
      rw [hg, ← mul_smul, inv_mul_cancel_right]
    rw [e]
    exact (hf.dual s.c a P hP).smul g
