import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterPCProof

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

theorem exists_homogenised (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (I : Ideal (MvPolynomial (Σ k, ι k) ℂ))
    (hI : ∀ k, (X ⟨k, c k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ I) (g : MvPolynomial (Σ k, ι k) ℚ) :
    ∃ (d : ℤ) (H E : MRing ι), d ≠ 0 ∧
      mConeMap y H =
        MvPolynomial.C ((d : Ω) * aeval (fun q : Σ k, ι k => y q / y ⟨q.1, c q.1⟩) g) * mConeMap y E ∧
      map (Int.castRingHom ℂ) H - MvPolynomial.C (d : ℂ) * map (algebraMap ℚ ℂ) g ∈ I ∧
      map (Int.castRingHom ℂ) E - 1 ∈ I := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    refine ⟨a.den, MvPolynomial.C a.num, 1, by exact_mod_cast a.den_ne_zero, ?_, ?_, by simp⟩
    · have h1 : ((a.den : ℤ) : Ω) * algebraMap ℚ Ω a = (a.num : Ω) := by
        calc ((a.den : ℤ) : Ω) * algebraMap ℚ Ω a = algebraMap ℚ Ω ((a.den : ℚ) * a) := by
              rw [map_mul]; simp
          _ = _ := by rw [Rat.den_mul_eq_num]; simp
      simp only [aeval_C, map_one, mul_one, h1]
      simp [mConeMap]
    · have h1 : ((a.den : ℤ) : ℂ) * algebraMap ℚ ℂ a = (a.num : ℂ) := by
        calc ((a.den : ℤ) : ℂ) * algebraMap ℚ ℂ a = algebraMap ℚ ℂ ((a.den : ℚ) * a) := by
              rw [map_mul]; simp
          _ = _ := by rw [Rat.den_mul_eq_num]; simp
      have : map (Int.castRingHom ℂ) (MvPolynomial.C a.num : MRing ι) -
          MvPolynomial.C ((a.den : ℤ) : ℂ) * map (algebraMap ℚ ℂ) (MvPolynomial.C a) = 0 := by
        rw [map_C, map_C, ← map_mul, h1]
        simp
      rw [this]; exact I.zero_mem
  | add p q hp hq =>
    obtain ⟨d₁, H₁, E₁, hd₁, ha₁, hb₁, he₁⟩ := hp
    obtain ⟨d₂, H₂, E₂, hd₂, ha₂, hb₂, he₂⟩ := hq
    have hC : ∀ d : ℤ, mConeMap y (MvPolynomial.C d) = MvPolynomial.C (d : Ω) := fun d => by
      rw [mConeMap, aeval_C]; simp
    have hZ : ∀ d : ℤ, map (Int.castRingHom ℂ) (MvPolynomial.C d : MRing ι) = MvPolynomial.C (d : ℂ) :=
      fun d => by rw [map_C]; simp
    refine ⟨d₁ * d₂, MvPolynomial.C d₂ * H₁ * E₂ + MvPolynomial.C d₁ * H₂ * E₁, E₁ * E₂,
      mul_ne_zero hd₁ hd₂, ?_, ?_, ?_⟩
    · simp only [map_add, map_mul, ha₁, ha₂, hC, Int.cast_mul, mul_add]
      ring
    · have e : map (Int.castRingHom ℂ) (MvPolynomial.C d₂ * H₁ * E₂ + MvPolynomial.C d₁ * H₂ * E₁ : MRing ι) -
          MvPolynomial.C ((d₁ * d₂ : ℤ) : ℂ) * map (algebraMap ℚ ℂ) (p + q) =
          (MvPolynomial.C (d₂ : ℂ) * map (Int.castRingHom ℂ) E₂) *
              (map (Int.castRingHom ℂ) H₁ - MvPolynomial.C (d₁ : ℂ) * map (algebraMap ℚ ℂ) p) +
            (MvPolynomial.C (d₁ : ℂ) * map (Int.castRingHom ℂ) E₁) *
              (map (Int.castRingHom ℂ) H₂ - MvPolynomial.C (d₂ : ℂ) * map (algebraMap ℚ ℂ) q) +
            (MvPolynomial.C (d₁ : ℂ) * MvPolynomial.C (d₂ : ℂ) * map (algebraMap ℚ ℂ) p) *
              (map (Int.castRingHom ℂ) E₂ - 1) +
            (MvPolynomial.C (d₁ : ℂ) * MvPolynomial.C (d₂ : ℂ) * map (algebraMap ℚ ℂ) q) *
              (map (Int.castRingHom ℂ) E₁ - 1) := by
        simp only [map_add, map_mul, hZ, Int.cast_mul]
        ring
      rw [e]
      exact I.add_mem (I.add_mem (I.add_mem (I.mul_mem_left _ hb₁) (I.mul_mem_left _ hb₂))
        (I.mul_mem_left _ he₂)) (I.mul_mem_left _ he₁)
    · have e : map (Int.castRingHom ℂ) (E₁ * E₂ : MRing ι) - 1 =
          map (Int.castRingHom ℂ) E₂ * (map (Int.castRingHom ℂ) E₁ - 1) +
            (map (Int.castRingHom ℂ) E₂ - 1) := by
        rw [map_mul]; ring
      rw [e]
      exact I.add_mem (I.mul_mem_left _ he₁) he₂
  | mul_X p s hp =>
    obtain ⟨d, H, E, hd, ha, hb, he⟩ := hp
    have hX : mConeMap y (X s) = MvPolynomial.C (y s / y ⟨s.1, c s.1⟩) * mConeMap y (X ⟨s.1, c s.1⟩) := by
      simp only [mConeMap, aeval_X, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ (hc s.1)]
    refine ⟨d, H * X s, E * X ⟨s.1, c s.1⟩, hd, ?_, ?_, ?_⟩
    · simp only [map_mul, ha, hX, aeval_X]
      ring
    · have e : map (Int.castRingHom ℂ) (H * X s : MRing ι) -
          MvPolynomial.C (d : ℂ) * map (algebraMap ℚ ℂ) (p * X s) =
          X s * (map (Int.castRingHom ℂ) H - MvPolynomial.C (d : ℂ) * map (algebraMap ℚ ℂ) p) := by
        simp only [map_mul, map_X]
        ring
      rw [e]
      exact I.mul_mem_left _ hb
    · have e : map (Int.castRingHom ℂ) (E * X ⟨s.1, c s.1⟩ : MRing ι) - 1 =
          X ⟨s.1, c s.1⟩ * (map (Int.castRingHom ℂ) E - 1) + (X ⟨s.1, c s.1⟩ - 1) := by
        simp only [map_mul, map_X]
        ring
      rw [e]
      exact I.add_mem (I.mul_mem_left _ he) (hI s.1)

theorem ker_le_chart (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (g : MvPolynomial (Σ k, ι k) ℚ)
    (hg : aeval (fun q : Σ k, ι k => y q / y ⟨q.1, c q.1⟩) g = 0) :
    map (algebraMap ℚ ℂ) g ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c := by
  obtain ⟨d, H, E, hd, ha, hb, -⟩ := exists_homogenised K ι Ω y c hc
    (ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c)
    (fun k => Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)) g
  have hH : H ∈ mCoordIdeal y := by
    rw [mCoordIdeal, RingHom.mem_ker]
    rw [ha, hg]
    simp
  have hHC : map (Int.castRingHom ℂ) H ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c :=
    Ideal.mem_sup_left (Ideal.subset_span ⟨H, hH, rfl⟩)
  have h2 : MvPolynomial.C (d : ℂ) * map (algebraMap ℚ ℂ) g ∈
      ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c := by
    have := Ideal.sub_mem _ hHC hb
    simpa using this
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have h3 := Ideal.mul_mem_left _ (MvPolynomial.C (d : ℂ)⁻¹) h2
  rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hd', map_one, one_mul] at h3

theorem exists_clear {σ Ω C : Type} [Field Ω] [CharZero Ω] [CommRing C] [Algebra ℚ C] (u : σ → Ω) (t : σ → C)
    (F : MvPolynomial σ ℚ) (a : Ω) (b : C) (ha : a * aeval u F = 1) (hb : b * aeval t F = 1)
    (h : MvPolynomial (Option σ) ℚ) :
    ∃ (n : ℕ) (g : MvPolynomial σ ℚ),
      aeval u F ^ n * aeval (fun o : Option σ => o.elim a u) h = aeval u g ∧
      aeval t F ^ n * aeval (fun o : Option σ => o.elim b t) h = aeval t g := by
  induction h using MvPolynomial.induction_on with
  | C r => exact ⟨0, MvPolynomial.C r, by simp, by simp⟩
  | add p q hp hq =>
    obtain ⟨n₁, g₁, h₁, h₁'⟩ := hp
    obtain ⟨n₂, g₂, h₂, h₂'⟩ := hq
    refine ⟨n₁ + n₂, F ^ n₂ * g₁ + F ^ n₁ * g₂, ?_, ?_⟩
    · simp only [map_add, map_mul, map_pow, ← h₁, ← h₂]; ring
    · simp only [map_add, map_mul, map_pow, ← h₁', ← h₂']; ring
  | mul_X p o hp =>
    obtain ⟨n, g, h₁, h₁'⟩ := hp
    cases o with
    | none =>
      refine ⟨n + 1, g, ?_, ?_⟩
      · rw [← h₁, map_mul, aeval_X, Option.elim_none]
        calc _ = aeval u F ^ n * aeval (fun o : Option σ => o.elim a u) p * (a * aeval u F) := by ring
          _ = _ := by rw [ha, mul_one]
      · rw [← h₁', map_mul, aeval_X, Option.elim_none]
        calc _ = aeval t F ^ n * aeval (fun o : Option σ => o.elim b t) p * (b * aeval t F) := by ring
          _ = _ := by rw [hb, mul_one]
    | some q =>
      refine ⟨n, g * X q, ?_, ?_⟩
      · rw [map_mul, map_mul, aeval_X, aeval_X, Option.elim_some, ← h₁]; ring
      · rw [map_mul, map_mul, aeval_X, aeval_X, Option.elim_some, ← h₁']; ring

theorem exists_unique_lift (σ : Type) (Ω : Type) [Field Ω] [CharZero Ω] (C : Type) [CommRing C] [Algebra ℚ C]
    (u : σ → Ω) (t : σ → C) (hker : ∀ g : MvPolynomial σ ℚ, aeval u g = 0 → aeval t g = 0)
    (F : MvPolynomial σ ℚ) (hF : aeval u F ≠ 0) (hunit : IsUnit (aeval t F : C))
    (S : Subalgebra ℚ Ω) (hS : S = Algebra.adjoin ℚ (insert (aeval u F)⁻¹ (Set.range u))) (hu : ∀ q, u q ∈ S) :
    ∃ Φ : S →ₐ[ℚ] C, (∀ q, Φ ⟨u q, hu q⟩ = t q) ∧
      ∀ Φ' : S →ₐ[ℚ] C, (∀ q, Φ' ⟨u q, hu q⟩ = t q) → Φ' = Φ := by
  classical
  obtain ⟨b, hb⟩ : ∃ b, b * aeval t F = 1 := hunit.exists_left_inv
  have ha : (aeval u F)⁻¹ * aeval u F = 1 := inv_mul_cancel₀ hF
  let π₀ : Option σ → Ω := fun o => o.elim (aeval u F)⁻¹ u
  let τ : Option σ → C := fun o => o.elim b t
  have hrange : Set.range π₀ = insert (aeval u F)⁻¹ (Set.range u) := by
    ext x
    constructor
    · rintro ⟨o, rfl⟩
      cases o with
      | none => exact Set.mem_insert _ _
      | some q => exact Set.mem_insert_of_mem _ ⟨q, rfl⟩
    · rintro (rfl | ⟨q, rfl⟩)
      · exact ⟨none, rfl⟩
      · exact ⟨some q, rfl⟩
  have hS' : S = (aeval π₀ : MvPolynomial (Option σ) ℚ →ₐ[ℚ] Ω).range := by
    rw [hS, ← hrange, Algebra.adjoin_range_eq_range_aeval]
  clear hS
  subst hS'
  have hkle : ∀ h : MvPolynomial (Option σ) ℚ, aeval π₀ h = 0 → aeval τ h = 0 := by
    intro h hh
    obtain ⟨n, g, h₁, h₂⟩ := exists_clear u t F _ b ha hb h
    have hg : aeval u g = 0 := by
      rw [← h₁]
      have : aeval (fun o : Option σ => o.elim (aeval u F)⁻¹ u) h = 0 := hh
      rw [this, mul_zero]
    have h₃ : aeval t F ^ n * aeval τ h = 0 := by
      have : aeval t F ^ n * aeval (fun o : Option σ => o.elim b t) h = 0 := by rw [h₂, hker g hg]
      exact this
    exact (hunit.pow n).mul_right_eq_zero.1 h₃
  let π : MvPolynomial (Option σ) ℚ →ₐ[ℚ] (aeval π₀ : MvPolynomial (Option σ) ℚ →ₐ[ℚ] Ω).range :=
    (aeval π₀).rangeRestrict
  have hs : Function.Surjective π := AlgHom.rangeRestrict_surjective _
  have hle : RingHom.ker π.toRingHom ≤ RingHom.ker (aeval τ : MvPolynomial (Option σ) ℚ →ₐ[ℚ] C).toRingHom := by
    intro h hh
    refine RingHom.mem_ker.2 (hkle h ?_)
    have : π h = 0 := RingHom.mem_ker.1 hh
    exact congrArg Subtype.val this
  let Φ₀ := RingHom.liftOfSurjective π.toRingHom hs ⟨(aeval τ).toRingHom, hle⟩
  have hΦ₀ : ∀ x, Φ₀ (π x) = aeval τ x := fun x =>
    RingHom.liftOfRightInverse_comp_apply π.toRingHom _ _ ⟨(aeval τ).toRingHom, hle⟩ x
  have huπ : ∀ q, (⟨u q, hu q⟩ : (aeval π₀ : MvPolynomial (Option σ) ℚ →ₐ[ℚ] Ω).range) = π (X (some q)) :=
    fun q => Subtype.ext (by simp [π, π₀])
  refine ⟨Φ₀.toRatAlgHom, fun q => ?_, fun Φ' hΦ' => ?_⟩
  · show Φ₀ _ = _
    rw [huπ, hΦ₀, aeval_X]
    rfl
  · have h1 : Φ'.comp π = aeval τ := by
      refine MvPolynomial.algHom_ext fun o => ?_
      cases o with
      | some q =>
        show Φ' (π (X (some q))) = _
        rw [← huπ, hΦ', aeval_X]
        rfl
      | none =>
        have h2 : (Φ'.comp π).comp (rename some : MvPolynomial σ ℚ →ₐ[ℚ] _) = aeval t := by
          refine MvPolynomial.algHom_ext fun q => ?_
          show Φ' (π (rename some (X q))) = _
          rw [rename_X, ← huπ, hΦ', aeval_X]
        have h3 : π (X none) * π (rename some F) = 1 := by
          refine Subtype.ext ?_
          show aeval π₀ (X none) * aeval π₀ (rename some F) = 1
          rw [aeval_X, aeval_rename]
          exact ha
        have h4 : Φ' (π (X none)) * aeval t F = 1 := by
          have : Φ' (π (rename some F)) = aeval t F := DFunLike.congr_fun h2 F
          rw [← this, ← map_mul, h3, map_one]
        show Φ' (π (X none)) = _
        rw [aeval_X]
        exact hunit.mul_right_cancel (h4.trans hb.symm)
    refine AlgHom.ext fun s => ?_
    obtain ⟨x, rfl⟩ := hs s
    have : Φ' (π x) = aeval τ x := DFunLike.congr_fun h1 x
    rw [this]
    exact (hΦ₀ x).symm

theorem exists_span_of_derivations (S : Type) [CommRing S] [Algebra ℚ S] (σ : Type) (u : σ → S) (e : ℕ)
    (z : Fin e → S)
    (hz : Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤) (ψ : S →ₐ[ℚ] ℂ) :
    ∃ b : Fin e → σ → ℂ, ∀ Φ : S →ₐ[ℚ] TrivSqZeroExt ℂ ℂ,
      (TrivSqZeroExt.fstHom ℚ ℂ ℂ).comp Φ = ψ →
      (fun q => (Φ (u q)).snd) ∈ Submodule.span ℂ (Set.range b) := by
  classical
  have hmem : ∀ q, ∃ c : Fin e → S, ∑ i, c i • KaehlerDifferential.D ℚ S (z i) =
      KaehlerDifferential.D ℚ S (u q) := by
    intro q
    have h : KaehlerDifferential.D ℚ S (u q) ∈
        Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) := hz ▸ Submodule.mem_top
    exact (Submodule.mem_span_range_iff_exists_fun S).1 h
  choose c hc using hmem
  refine ⟨fun i q => ψ (c q i), fun Φ hΦ => ?_⟩
  have hfst : ∀ s, (Φ s).fst = ψ s := fun s => DFunLike.congr_fun hΦ s
  let _ : Module S ℂ := Module.compHom ℂ (ψ : S →+* ℂ)
  have hsm : ∀ (s : S) (x : ℂ), s • x = ψ s * x := fun _ _ => rfl
  have : IsScalarTower ℚ S ℂ := ⟨fun r s x => by
    rw [hsm, hsm, map_smul, smul_mul_assoc]⟩
  let d : Derivation ℚ S ℂ := Derivation.mk'
    (((TrivSqZeroExt.sndHom ℂ ℂ).restrictScalars ℚ).comp Φ.toLinearMap) (fun a b => by
      show (Φ (a * b)).snd = a • (Φ b).snd + b • (Φ a).snd
      rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst, hsm, hsm]
      simp [mul_comm])
  have hd : ∀ s, d s = (Φ s).snd := fun _ => rfl
  have key : ∀ q, (Φ (u q)).snd = ∑ i, ψ (c q i) * (Φ (z i)).snd := by
    intro q
    have h := congrArg d.liftKaehlerDifferential (hc q)
    rw [Derivation.liftKaehlerDifferential_comp_D, map_sum] at h
    rw [← hd, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, hsm, hd]
  have he : (fun q => (Φ (u q)).snd) = ∑ i, (Φ (z i)).snd • (fun q => ψ (c q i)) := by
    funext q
    rw [key, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  rw [he]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem aeval_dual (σ : Type) [Fintype σ] (w v : σ → ℂ) (g : MvPolynomial σ ℚ) :
    (aeval (fun q => (TrivSqZeroExt.inl (w q) + TrivSqZeroExt.inr (v q) : TrivSqZeroExt ℂ ℂ)) g).fst =
        eval w (map (algebraMap ℚ ℂ) g) ∧
    (aeval (fun q => (TrivSqZeroExt.inl (w q) + TrivSqZeroExt.inr (v q) : TrivSqZeroExt ℂ ℂ)) g).snd =
        ∑ q, eval w (pderiv q (map (algebraMap ℚ ℂ) g)) * v q := by
  classical
  induction g using MvPolynomial.induction_on with
  | C a =>
    constructor
    · rw [aeval_C, TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.fst_inl, map_C, eval_C]
    · rw [aeval_C, TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.snd_inl, map_C]
      simp
  | add p q hp hq =>
    constructor
    · simp only [map_add, TrivSqZeroExt.fst_add, hp.1, hq.1]
    · simp only [map_add, TrivSqZeroExt.snd_add, hp.2, hq.2, add_mul, Finset.sum_add_distrib]
  | mul_X p s hp =>
    constructor
    · rw [map_mul, aeval_X, TrivSqZeroExt.fst_mul, hp.1]
      simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, map_mul, map_X,
        eval_X]
    · rw [map_mul, aeval_X, TrivSqZeroExt.snd_mul, hp.2, hp.1]
      simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
        TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, smul_eq_mul,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      have h : ∀ q, eval w (pderiv q (map (algebraMap ℚ ℂ) (p * X s))) * v q =
          (if q = s then eval w (map (algebraMap ℚ ℂ) p) * v q else 0) +
            w s * (eval w (pderiv q (map (algebraMap ℚ ℂ) p)) * v q) := by
        intro q
        rw [map_mul, map_X, Derivation.leibniz]
        by_cases hq : q = s
        · subst hq
          simp
          ring
        · simp [pderiv_X_of_ne (Ne.symm hq), hq]
          ring
      simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.mul_sum]
      ring

theorem card_le_finrank_add (σ : Type) [Fintype σ] (V : Submodule ℂ (σ → ℂ)) (e : ℕ) (b : Fin e → σ → ℂ)
    (h : ∀ v : σ → ℂ, (∀ a ∈ V, ∑ q, a q * v q = 0) → v ∈ Submodule.span ℂ (Set.range b)) :
    Fintype.card σ ≤ Module.finrank ℂ V + e := by
  let B : (σ → ℂ) →ₗ[ℂ] (σ → ℂ) →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ (fun v a => ∑ q, a q * v q)
    (fun v v' a => by simp [mul_add, Finset.sum_add_distrib])
    (fun c v a => by simp [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring)
    (fun v a a' => by simp [add_mul, Finset.sum_add_distrib])
    (fun c v a => by simp [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring)
  let T : (σ → ℂ) →ₗ[ℂ] Module.Dual ℂ V := B.compl₂ V.subtype
  have hk : LinearMap.ker T ≤ Submodule.span ℂ (Set.range b) := by
    intro v hv
    refine h v fun a ha => ?_
    have := DFunLike.congr_fun (LinearMap.mem_ker.1 hv) ⟨a, ha⟩
    exact this
  have h1 := LinearMap.finrank_range_add_finrank_ker T
  have h2 : Module.finrank ℂ (LinearMap.range T) ≤ Module.finrank ℂ V := by
    calc _ ≤ Module.finrank ℂ (Module.Dual ℂ V) := Submodule.finrank_le _
      _ = _ := Subspace.dual_finrank_eq
  have h3 : Module.finrank ℂ (LinearMap.ker T) ≤ e := by
    calc _ ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range b)) := Submodule.finrank_mono hk
      _ ≤ e := by
        have := finrank_range_le_card (R := ℂ) b
        simpa [Set.finrank] using this
  simp only [Module.finrank_fintype_fun_eq_card] at h1
  omega

theorem card_le_of_kaehler (σ : Type) [Fintype σ] (Ω : Type) [Field Ω] [CharZero Ω] (u : σ → Ω)
    (V : Submodule ℂ (σ → ℂ)) (w : σ → ℂ) (F : MvPolynomial σ ℚ) (hF : aeval u F ≠ 0)
    (hFw : eval w (map (algebraMap ℚ ℂ) F) ≠ 0)
    (hker : ∀ g : MvPolynomial σ ℚ, aeval u g = 0 → eval w (map (algebraMap ℚ ℂ) g) = 0)
    (hV : ∀ g : MvPolynomial σ ℚ, aeval u g = 0 →
      (fun q => eval w (pderiv q (map (algebraMap ℚ ℂ) g))) ∈ V)
    (S : Subalgebra ℚ Ω) (hS : S = Algebra.adjoin ℚ (insert (aeval u F)⁻¹ (Set.range u)))
    (e : ℕ) (z : Fin e → S)
    (hz : Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤) :
    Fintype.card σ ≤ Module.finrank ℂ V + e := by
  have huS : ∀ q, u q ∈ S := fun q => hS ▸ Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨q, rfl⟩)
  have haw : ∀ g : MvPolynomial σ ℚ, (aeval w g : ℂ) = eval w (map (algebraMap ℚ ℂ) g) := fun g => by
    rw [eval_map, aeval_def]
  obtain ⟨ψ, hψ, hψu⟩ := exists_unique_lift σ Ω ℂ u w
    (fun g hg => by rw [haw]; exact hker g hg) F hF
    (by rw [haw]; exact isUnit_iff_ne_zero.2 hFw) S hS huS
  obtain ⟨b, hb⟩ := exists_span_of_derivations S σ (fun q => ⟨u q, huS q⟩) e z hz ψ
  refine card_le_finrank_add _ _ e b fun v hv => ?_
  let t : σ → TrivSqZeroExt ℂ ℂ := fun q => TrivSqZeroExt.inl (w q) + TrivSqZeroExt.inr (v q)
  obtain ⟨Φ, hΦ, -⟩ := exists_unique_lift σ Ω (TrivSqZeroExt ℂ ℂ) u t
    (fun g hg => by
      obtain ⟨h1, h2⟩ := aeval_dual σ w v g
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [h1, hker g hg]; rfl
      · rw [h2]
        have := hv _ (hV g hg)
        exact this)
    F hF
    (by
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, (aeval_dual σ w v F).1]
      exact isUnit_iff_ne_zero.2 hFw) S hS huS
  have hfst : (TrivSqZeroExt.fstHom ℚ ℂ ℂ).comp Φ = ψ := hψu _ fun q => by
    simp [hΦ, t]
  have := hb Φ hfst
  have hv' : (fun q => (Φ ⟨u q, huS q⟩).snd) = v := by
    funext q
    simp [hΦ, t]
  rwa [hv'] at this

theorem card_le_finrank_jacSpanAt (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)) (hsnc : IsSncModel y e J)
    (p : (k : K) → ι k) (hp : ∀ k, y ⟨k, p k⟩ ≠ 0) (w : (Σ k, ι k) → ℂ)
    (hw : ∀ h ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p, eval w h = 0) :
    Fintype.card (Σ k, ι k) ≤
      Module.finrank ℂ (ReciprocityTheory.AnForm.R.jacSpanAt (ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p) w) + e := by
  classical
  have hkerC := ker_le_chart K ι Ω y p hp
  have hkerw : ∀ g : MvPolynomial (Σ k, ι k) ℚ, aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) g = 0 →
      eval w (map (algebraMap ℚ ℂ) g) = 0 :=
    fun g hg => hw _ (hkerC g hg)
  obtain ⟨m, f, a, hf, ha, hsum, hS⟩ := hsnc p hp
  have hadj : ∀ s ∈ Algebra.adjoin ℚ (Set.range fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩),
      ∃ F : MvPolynomial (Σ k, ι k) ℚ, aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) F = s := by
    intro s hs
    rw [Algebra.adjoin_range_eq_range_aeval] at hs
    exact hs
  choose F hF using fun l => hadj (f l) (hf l)
  choose A hA using fun l => hadj (a l) (ha l)
  obtain ⟨l, hl⟩ : ∃ l, eval w (map (algebraMap ℚ ℂ) (F l)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 := hkerw (∑ l, A l * F l - 1) (by
      simp only [map_sub, map_sum, map_mul, map_one, hF, hA]
      rw [hsum, sub_self])
    simp [hcon] at h0
  have hfl : f l ≠ 0 := fun h0 => hl (hkerw _ (by rw [hF, h0]))
  obtain ⟨-, z, n, -, -, hspan, -⟩ := hS l hfl _ rfl
  refine card_le_of_kaehler (Σ k, ι k) Ω _ (ReciprocityTheory.AnForm.R.jacSpanAt _ w) w (F l) (by rw [hF]; exact hfl) hl hkerw
    (fun g hg => Submodule.subset_span ⟨_, hkerC g hg, rfl⟩) _ (by rw [hF]) e z hspan

theorem isRegularLocalRing_chart : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)), IsArithVar (mCoordIdeal y) (e + 1) → IsSncModel y e J → ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src (pC (mCoordIdeal y)) p, IsRegularLocalRing (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) ∧ ringKrullDim (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) = e := by
  intro K _ ι _ Ω _ _ y e J hP hsnc p x hx
  classical
  have hPh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) := isMultiHomogIdeal_pC hP.2.1.2.1
  have hz := rep_mem x
  have hw := (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hPh p (rep x) hx).1 hz
  have hy : ∀ k, y ⟨k, p k⟩ ≠ 0 := by
    intro k h0
    have hX : (X ⟨k, p k⟩ : MRing ι) ∈ mCoordIdeal y := by
      rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0]
      simp
    have h1 := hz.2 _ (Ideal.subset_span ⟨_, hX, rfl⟩)
    rw [map_X, eval_X] at h1
    exact hx k h1
  obtain ⟨hloc, hnoeth⟩ := ReciprocityTheory.AnForm.R.locAt_isLocalRing_isNoetherian _ _ hw
  have hd := ReciprocityTheory.AnForm.R.ringKrullDim_locAt_chart _ hPh e (pcEquidim K ι _ e hP) p _ hw
  have hcot := ReciprocityTheory.AnForm.R.finrank_cotangentSpace_locAt
    (ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p) (ReciprocityTheory.AnForm.R.affCoord p (rep x))
  have hrank := card_le_finrank_jacSpanAt K ι Ω y e J hsnc p hy _ hw
  have hreg : IsRegularLocalRing (ReciprocityTheory.AnForm.R.locAt (ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p)
      (ReciprocityTheory.AnForm.R.affCoord p (rep x))) := by
    refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
    rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, hd]
    have : Module.finrank (IsLocalRing.ResidueField (ReciprocityTheory.AnForm.R.locAt (ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p)
        (ReciprocityTheory.AnForm.R.affCoord p (rep x)))) (IsLocalRing.CotangentSpace (ReciprocityTheory.AnForm.R.locAt (ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p)
        (ReciprocityTheory.AnForm.R.affCoord p (rep x)))) ≤ e := by omega
    exact_mod_cast this
  exact ⟨IsRegularLocalRing.of_ringEquiv (ReciprocityTheory.AnForm.R.locAtEquiv _ _),
    (ringKrullDim_eq_of_ringEquiv (ReciprocityTheory.AnForm.R.locAtEquiv _ _)).symm.trans hd⟩

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
