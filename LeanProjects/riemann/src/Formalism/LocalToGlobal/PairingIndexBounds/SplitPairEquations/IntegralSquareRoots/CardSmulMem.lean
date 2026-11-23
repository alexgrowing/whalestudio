import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.ConstCopies
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SemiCharImg

noncomputable section
open scoped BigOperators ComplexConjugate
open Classical

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.L2.Th1.H

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem sum_reps_perm {M P : AddSubgroup V} {S : Finset V} (hS : IsReps M P S) (ℓ : V → V)
    (hP : ∀ x ∈ P, ℓ x ∈ P) (hinj : ∀ x ∈ P, ∀ y ∈ P, ℓ x - ℓ y ∈ M → x - y ∈ M)
    (f : V → ℂ) (hf : ∀ x ∈ P, ∀ y ∈ M, f (x + y) = f x) :
    ∑ x ∈ S, f (ℓ x) = ∑ x ∈ S, f x := by
  obtain ⟨h1, h2, h3⟩ := hS
  have hex : ∀ x ∈ S, ∃ s ∈ S, ℓ x - s ∈ M := fun x hx => h3 _ (hP x (h1 x hx))
  choose! r hr1 hr2 using hex
  have hfr : ∀ x ∈ S, f (ℓ x) = f (r x) := by
    intro x hx
    have := hf (r x) (h1 _ (hr1 x hx)) (ℓ x - r x) (hr2 x hx)
    rwa [add_sub_cancel] at this
  have hinjr : Set.InjOn r S := by
    intro x hx y hy hxy
    refine h2 x hx y hy (hinj x (h1 x hx) y (h1 y hy) ?_)
    have : ℓ x - ℓ y = (ℓ x - r x) - (ℓ y - r y) := by rw [hxy]; abel
    rw [this]; exact M.sub_mem (hr2 x hx) (hr2 y hy)
  have himg : S.image r = S :=
    Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr hr1) (by rw [Finset.card_image_of_injOn hinjr])
  calc ∑ x ∈ S, f (ℓ x) = ∑ x ∈ S, f (r x) := Finset.sum_congr rfl hfr
    _ = ∑ y ∈ S.image r, f y := (Finset.sum_image hinjr).symm
    _ = ∑ x ∈ S, f x := by rw [himg]

theorem card_smul_mem {M P : AddSubgroup V} {S : Finset V} (hS : IsReps M P S) {x : V} (hx : x ∈ P) : S.card • x ∈ M := by
  have hc : Nat.card (P ⧸ M.addSubgroupOf P) = S.card := by
    rw [← Nat.card_congr (Equiv.ofBijective _ (repClass_bijective hS))]
    simp
  have h : S.card • (QuotientAddGroup.mk (⟨x, hx⟩ : P) : P ⧸ M.addSubgroupOf P) = 0 := by
    rw [← hc]; exact card_nsmul_eq_zero'
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h
  simpa using h

theorem comm_symm (g : V →ₗ[ℂ] V) (φ : V ≃ₗ[ℂ] V) (h : ∀ x, g (φ x) = φ (g x)) (x : V) : g (φ.symm x) = φ.symm (g x) := by
  apply φ.injective
  rw [← h, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

structure Multipliers (H : Sesq V) (Λ : AddSubgroup V) (δ : V ≃ₗ[ℂ] V) (ℓ ℓ' σ : V →ₗ[ℂ] V) (e : ℕ) : Prop where
  lΛ : ∀ x ∈ Λ, ℓ x ∈ Λ
  l'Λ : ∀ x ∈ Λ, ℓ' x ∈ Λ
  sΛ : ∀ x ∈ Λ, σ x ∈ Λ
  lδ : ∀ x, ℓ (δ x) = δ (ℓ x)
  l'δ : ∀ x, ℓ' (δ x) = δ (ℓ' x)
  sδ : ∀ x, σ (δ x) = δ (σ x)
  adj : ∀ x y, H (ℓ x) y = H x (ℓ' y)
  sadj : ∀ x y, H (σ x) y = H x (σ y)
  rel : ∀ x, ℓ' (ℓ x) = -x + (4 * e) • σ x

variable {H : Sesq V} {Λ : AddSubgroup V} {α : V → ℂ} {δ Ae : V ≃ₗ[ℂ] V}

theorem comm_cay (hA : ∀ x, Ae x = x - δ.symm x) (g : V →ₗ[ℂ] V) (h : ∀ x, g (δ x) = δ (g x)) (x : V) :
    g (Ae x) = Ae (g x) := by
  rw [hA, hA, map_sub, comm_symm g δ h]

theorem latA_stable (hA : ∀ x, Ae x = x - δ.symm x) (g : V →ₗ[ℂ] V) (hΛ : ∀ x ∈ Λ, g x ∈ Λ)
    (h : ∀ x, g (δ x) = δ (g x)) {y : V} (hy : y ∈ latA Λ δ Ae) : g y ∈ latA Λ δ Ae := by
  unfold latA at hy ⊢
  rw [mem_imgLat_iff, AddSubgroup.mem_inf, mem_imgLat_iff] at hy ⊢
  rw [← comm_symm g Ae (comm_cay hA g h), ← comm_symm g δ h]
  exact ⟨hΛ _ hy.1, hΛ _ hy.2⟩

theorem cayC_comm (hA : ∀ x, Ae x = x - δ.symm x) (g : V →ₗ[ℂ] V) (h : ∀ x, g (δ x) = δ (g x)) (x : V) :
    cayC Ae (g x) = g (cayC Ae x) := by
  unfold cayC
  rw [map_sub, map_smul, comm_symm g Ae (comm_cay hA g h)]

variable {ℓ ℓ' σ : V →ₗ[ℂ] V} {e : ℕ}

theorem phi_conj (hU : UnitaryData H Λ α δ Ae) (hM : Multipliers H Λ δ ℓ ℓ' σ e)
    (he : ∀ x ∈ Λ, e • x ∈ latA Λ δ Ae) (hα : ∀ x ∈ Λ, α (ℓ x) = α x) {x : V} (hx : x ∈ Λ) :
    phiC H α Ae (ℓ x) = conj (phiC H α Ae x) := by
  obtain ⟨hskew, hre, -, -⟩ := phiBasic V H Λ α δ Ae hU
  have h1 : H (cayC Ae (ℓ x)) (ℓ x) = -H (cayC Ae x) x + (4 * e : ℂ) * H (cayC Ae x) (σ x) := by
    rw [cayC_comm hU.cay ℓ hM.lδ, hM.adj, hM.rel, map_add, map_neg, map_nsmul, nsmul_eq_mul]
    push_cast
    rfl
  have hXre : (H (cayC Ae x) (σ x)).re = 0 := by
    have h2 : H (cayC Ae x) (σ x) = -conj (H (cayC Ae x) (σ x)) := by
      conv_lhs => rw [hskew, cayC_comm hU.cay σ hM.sδ, ← hM.sadj, hU.herm (cayC Ae x) (σ x)]
    have h3 := congrArg Complex.re h2
    simp only [Complex.neg_re, Complex.conj_re] at h3
    linarith
  have hs0 : (H x (σ x)).im = 0 := by
    have h2 : H x (σ x) = conj (H x (σ x)) := by
      conv_lhs => rw [← hM.sadj, hU.herm x (σ x)]
    have h3 := congrArg Complex.im h2
    simp only [Complex.conj_im] at h3
    linarith
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (e : ℝ) * (H (cayC Ae x) (σ x)).im = (n : ℝ) := by
    have hw : Ae.symm (e • x) ∈ Λ := by
      have := he x hx
      unfold latA at this
      rw [mem_imgLat_iff, AddSubgroup.mem_inf] at this
      exact this.1
    rw [← hU.selfDual] at hw
    obtain ⟨n, hn⟩ := hw (σ x) (hM.sΛ x hx)
    refine ⟨n, ?_⟩
    rw [← hn]
    unfold altE cayC
    rw [map_nsmul, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, map_sub, LinearMap.sub_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    simp only [Complex.sub_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, hs0]
    norm_num
  have hX : (4 * e : ℂ) * H (cayC Ae x) (σ x) = (4 * n : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [hXre]
    · have : ((4 * e : ℂ) * H (cayC Ae x) (σ x)).im = 4 * ((e : ℝ) * (H (cayC Ae x) (σ x)).im) := by
        simp [hXre]; ring
      rw [this, hn]
      simp
  have hexp : Complex.exp (-(Real.pi : ℂ) * ((4 * n : ℂ) * Complex.I)) = 1 := by
    have := Complex.exp_int_mul_two_pi_mul_I (-2 * n)
    rw [← this]
    congr 1
    push_cast
    ring
  have hc : conj (H (cayC Ae x) x) = -H (cayC Ae x) x := by
    apply Complex.ext
    · simp [hre x]
    · simp
  have hαc : conj (α x) = α x := by
    rcases hU.semi.1 x hx with h | h <;> rw [h] <;> simp
  unfold phiC
  rw [hα x hx, h1, hX, map_mul, hαc, ← Complex.exp_conj, map_mul, map_neg, Complex.conj_ofReal, hc, mul_add,
    Complex.exp_add, hexp, mul_one]

theorem gauss_sq (hU : UnitaryData H Λ α δ Ae) (hM : Multipliers H Λ δ ℓ ℓ' σ e)
    (he : ∀ x ∈ Λ, e • x ∈ latA Λ δ Ae) (hα : ∀ x ∈ Λ, α (ℓ x) = α x) {S : Finset V}
    (hS : IsReps (latA Λ δ Ae) Λ S) : gaussC H α Ae S ^ 2 = 1 := by
  obtain ⟨-, -, -, hwd⟩ := phiBasic V H Λ α δ Ae hU
  have hinj : ∀ x ∈ Λ, ∀ y ∈ Λ, ℓ x - ℓ y ∈ latA Λ δ Ae → x - y ∈ latA Λ δ Ae := by
    intro x hx y hy h
    rw [← map_sub] at h
    have h2 := latA_stable hU.cay ℓ' hM.l'Λ hM.l'δ h
    rw [hM.rel] at h2
    have h3 : (4 * e) • σ (x - y) ∈ latA Λ δ Ae := by
      rw [mul_smul]
      exact AddSubgroup.nsmul_mem _ (he _ (hM.sΛ _ (Λ.sub_mem hx hy))) 4
    have h4 := AddSubgroup.sub_mem _ h3 h2
    have h5 : (4 * e) • σ (x - y) - (-(x - y) + (4 * e) • σ (x - y)) = x - y := by abel
    rwa [h5] at h4
  have hsum := sum_reps_perm hS ℓ hM.lΛ hinj (phiC H α Ae) hwd
  have hreal : conj (gaussC H α Ae S) = gaussC H α Ae S := by
    unfold gaussC
    rw [map_mul, map_inv₀, Complex.conj_ofReal, map_sum, ← hsum]
    congr 1
    exact Finset.sum_congr rfl fun x hx => (phi_conj hU hM he hα (hS.1 x hx)).symm
  have h8 := unitaryGauss V H Λ α δ Ae hU S hS
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp hreal
  rw [hr] at h8 ⊢
  have h8' : (r ^ 2) ^ 4 = 1 := by
    have : ((r ^ 2) ^ 4 : ℝ) = r ^ 8 := by ring
    rw [this]
    exact_mod_cast h8
  have h2 := (pow_eq_one_iff_of_nonneg (sq_nonneg r) (by norm_num)).mp h8'
  exact_mod_cast h2

end Formalism.L2.PairingIndexBounds.Eq.J
