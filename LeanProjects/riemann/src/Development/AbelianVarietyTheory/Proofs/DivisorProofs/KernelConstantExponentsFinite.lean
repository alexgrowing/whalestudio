import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder Pointwise

namespace GlobalTheory.ExponentsFinite

theorem val_le_one {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) {p s : ℕ}
    (hp : ((p : ℕ) : 𝓞 K) ∈ P.asIdeal) (hs : Nat.Coprime s p) {x : K} (hx : IsIntegral ℤ ((s : K) * x)) :
    P.valuation K x ≤ 1 := by
  have hsP : ((s : ℕ) : 𝓞 K) ∉ P.asIdeal := by
    intro h
    obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hs).map (Int.castRingHom (𝓞 K))
    simp only [eq_intCast, Int.cast_natCast] at hab
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ h) (P.asIdeal.mul_mem_left _ hp)))
  have h1 := (P.valuation_eq_one_iff_notMem (K := K)).2 hsP
  have h2 := P.valuation_le_one (K := K) (⟨_, hx⟩ : 𝓞 K)
  rw [map_natCast] at h1
  change P.valuation K ((s : K) * x) ≤ 1 at h2
  rwa [map_mul, h1, one_mul] at h2

theorem val_det_le_one {K ι Γ : Type} [Field K] [Fintype ι] [DecidableEq ι] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (f : (ι → K) →ₗ[K] (ι → K)) (hf : ∀ i j, v (f (Pi.single j 1) i) ≤ 1) :
    v (LinearMap.det f) ≤ 1 := by
  rw [← LinearMap.det_toMatrix', Matrix.det_apply']
  have : ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : K) * ∏ i, LinearMap.toMatrix' f (σ i) i ∈ v.integer := by
    refine Subring.sum_mem _ fun σ _ => Subring.mul_mem _ (intCast_mem _ _) (Subring.prod_mem _ fun i _ => ?_)
    rw [LinearMap.toMatrix'_apply]
    exact hf _ _
  exact this

theorem val_det_eq_one {K ι Γ : Type} [Field K] [Fintype ι] [DecidableEq ι] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (f : (ι → K) ≃ₗ[K] (ι → K)) (hf : ∀ i j, v (f (Pi.single j 1) i) ≤ 1)
    (hf' : ∀ i j, v (f.symm (Pi.single j 1) i) ≤ 1) :
    v (LinearMap.det (f : (ι → K) →ₗ[K] (ι → K))) = 1 := by
  have h1 := val_det_le_one v (f : (ι → K) →ₗ[K] (ι → K)) hf
  have h2 := val_det_le_one v (f.symm : (ι → K) →ₗ[K] (ι → K)) hf'
  have h3 := congrArg v (LinearEquiv.det_mul_det_symm f)
  rw [map_mul, map_one] at h3
  refine le_antisymm h1 ?_
  calc 1 = _ := h3.symm
    _ ≤ v (LinearMap.det (f : (ι → K) →ₗ[K] (ι → K))) * 1 := by gcongr
    _ = _ := mul_one _

theorem exists_den {K ι : Type} [Field K] [NumberField K] [Finite ι] (c : ι → K) :
    ∃ n : ℕ, 0 < n ∧ ∀ i, IsIntegral ℤ ((n : K) * c i) := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := K) (Finset.univ.image c)
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, fun i => ?_⟩
  have h := hy (c i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [zsmul_eq_mul] at h
  rcases Int.natAbs_eq y with h1 | h1
  · rw [h1, Int.cast_natCast] at h; exact h
  · rw [h1, Int.cast_neg, Int.cast_natCast, neg_mul] at h; simpa using h.neg

theorem exists_den_fg {K E ι κ : Type} [Field K] [NumberField K] [AddCommGroup E] [Finite ι] [Fintype κ]
    (A : Submodule ℤ E) (hA : A.FG) (g : (κ → E) →+ (ι → K)) :
    ∃ n : ℕ, 0 < n ∧ ∀ x : κ → E, (∀ a, x a ∈ A) → ∀ w, IsIntegral ℤ ((n : K) * g x w) := by
  classical
  obtain ⟨S, hS⟩ := hA
  obtain ⟨n, hn, h⟩ := exists_den (fun t : S × κ × ι => g (Pi.single t.2.1 (t.1 : E)) t.2.2)
  refine ⟨n, hn, fun x hx w => ?_⟩
  have key : ∀ a, ∀ y ∈ Submodule.span ℤ (S : Set E), IsIntegral ℤ ((n : K) * g (Pi.single a y) w) := by
    intro a y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact h (⟨y, hy⟩, a, w)
    | zero => simpa using isIntegral_zero
    | add y z _ _ hy hz => rw [Pi.single_add, map_add, Pi.add_apply, mul_add]; exact hy.add hz
    | smul c y _ hy =>
      rw [Pi.single_smul, map_zsmul, Pi.smul_apply, mul_smul_comm]; exact hy.zsmul c
  rw [← Finset.univ_sum_single x, map_sum, Finset.sum_apply, Finset.mul_sum]
  exact IsIntegral.sum _ fun a _ => key a _ (hS ▸ hx a)

theorem one_mem (D : D7) : (1 : D.host.E) ∈ D.host.AA0 := by
  have hb : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 fun h => by
      have h3 : D.host.𝔟 ⊔ D.host.conj • D.host.𝔟 = ⊤ := D.host.𝔟_spec.2
      simp [h] at h3
  refine (FractionalIdeal.mem_inv_iff hb).2 fun y hy => ?_
  rw [one_mul]; exact FractionalIdeal.coeIdeal_le_one hy

theorem yFinite : ∀ (D : D7) (γ₀ : IsoK D) (k : KapChoice γ₀), k.YFinite := by
  classical
  intro D γ₀ k
  have hfg : ((D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).restrictScalars ℤ).FG :=
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl D.host.AA0).restrictScalars
  obtain ⟨n, hn, hnx⟩ := exists_den_fg _ hfg γ₀.g.toLinearMap.toAddMonoidHom
  obtain ⟨m, hm, hmx⟩ := exists_den
    (fun t : (Fin 4 × D.what₂.Tau) × Fin 4 => γ₀.g.symm (Pi.single t.1 1) t.2)
  refine (Set.finite_le_nat (n * m)).subset ?_
  rintro p ⟨hp, hsp, hy⟩
  by_contra hlt
  have hlt' : n * m < p := not_le.1 hlt
  have hcop : Nat.Coprime (n * m) p := (Nat.coprime_of_lt_prime (by positivity) hlt' hp).symm
  have hcn : Nat.Coprime n p := Nat.Coprime.coprime_mul_right hcop
  have hcm : Nat.Coprime m p := Nat.Coprime.coprime_mul_left hcop
  obtain ⟨h1, h2⟩ := k.gaP_at p hp hsp
  have hP := k.pp_over p hp hsp
  apply hy
  unfold KapChoice.yP ordK IsoK.detRel
  rw [val_det_eq_one]
  · simp
  · intro i j
    obtain ⟨s, hs, hsx⟩ := h1 (m • γ₀.g.symm (Pi.single j 1)) (fun a => by
      have := (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem ⟨_, hmx (j, a)⟩ (one_mem D)
      change ((m : D.host.E) * γ₀.g.symm (Pi.single j 1) a) * 1 ∈ D.host.AA0 at this
      simpa using this)
    obtain ⟨r, hr⟩ := hsx i
    refine val_le_one _ hP (Nat.Coprime.mul_left hs hcm) ?_
    have hi : IsIntegral ℤ (algebraMap (𝓞 D.host.K) D.host.K r) := r.2
    rw [hr, map_nsmul, Pi.smul_apply, nsmul_eq_mul, ← mul_assoc] at hi
    simpa using hi
  · intro i j
    obtain ⟨s, hs, hsx⟩ := h2 (Pi.single j 1) (fun w => by
      by_cases hw : w = j
      · subst hw; simp
      · simp [hw])
    have hi := hnx (s • (k.gaP p).g.symm (Pi.single j 1)) (fun a => by
      have := hsx a
      simpa using this) i
    refine val_le_one _ hP (Nat.Coprime.mul_left hcn hs) ?_
    rw [map_nsmul, Pi.smul_apply, nsmul_eq_mul, ← mul_assoc] at hi
    simpa using hi

end GlobalTheory.ExponentsFinite
