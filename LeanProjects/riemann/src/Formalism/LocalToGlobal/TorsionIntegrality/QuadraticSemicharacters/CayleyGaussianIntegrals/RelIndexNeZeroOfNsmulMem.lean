import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CommensurableK
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.RatFourSquares
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.ScalePairMulMulEq
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.RelIndexEqAbsDetReal
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

section Index

variable {V : Type*} [AddCommGroup V]

theorem relIndex_ne_zero_of_nsmul_mem (H F : AddSubgroup V) [Module.Finite ℤ F] (N : ℕ) (hN : 0 < N)
    (h : ∀ x ∈ F, N • x ∈ H) : H.relIndex F ≠ 0 := by
  classical
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨k, φ, hφ⟩ := Module.Finite.exists_fin' ℤ F
  let ψ : (Fin k → ℤ) →+ (Fin k → ZMod N) := AddMonoidHom.compLeft (Int.castAddHom (ZMod N)) (Fin k)
  have hle : ψ.ker ≤ (H.addSubgroupOf F).comap φ.toAddMonoidHom := by
    intro x hx
    have hx' := (AddMonoidHom.mem_ker).1 hx
    have hdiv : ∀ i, (N : ℤ) ∣ x i := by
      intro i
      have hi := congrFun hx' i
      simpa [ψ, AddMonoidHom.compLeft, ZMod.intCast_zmod_eq_zero_iff_dvd] using hi
    choose y hy using hdiv
    have hxy : x = (N : ℤ) • y := by
      funext i
      simp [hy i]
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, hxy]
    have hφy : φ.toAddMonoidHom ((N : ℤ) • y) = N • φ y := by
      rw [LinearMap.toAddMonoidHom_coe, map_zsmul, natCast_zsmul]
    rw [hφy, AddSubgroup.coe_nsmul]
    exact h _ (φ y).2
  have h1 : ψ.ker.index ≠ 0 := by
    haveI : Finite ((Fin k → ℤ) ⧸ ψ.ker) :=
      Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange ψ).symm.toEquiv
    exact AddSubgroup.index_ne_zero_of_finite
  have h2 : ((H.addSubgroupOf F).comap φ.toAddMonoidHom).index ≠ 0 :=
    ne_zero_of_dvd_ne_zero h1 (AddSubgroup.index_dvd_of_le hle)
  rw [AddSubgroup.index_comap_of_surjective _ hφ] at h2
  exact h2

def nsmulHom [Module ℂ V] (N : ℕ) : V →+ V where
  toFun x := N • x
  map_zero' := smul_zero _
  map_add' _ _ := smul_add _ _ _

theorem nsmulHom_injective [Module ℂ V] (N : ℕ) (hN : 0 < N) : Function.Injective (nsmulHom (V := V) N) := by
  intro x y hxy
  have hxy' : N • x = N • y := hxy
  have h : (N : ℂ) • x = (N : ℂ) • y := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact hxy'
  exact smul_right_injective V (Nat.cast_ne_zero.mpr hN.ne') h

theorem relIndex_ne_zero_of_bound [Module ℂ V] (H K F : AddSubgroup V) [Module.Finite ℤ F] (N M : ℕ)
    (hN : 0 < N) (hM : 0 < M) (hK : ∀ x ∈ K, N • x ∈ F) (hH : ∀ x ∈ F, M • x ∈ H) : H.relIndex K ≠ 0 := by
  let g : K →+ F :=
    { toFun := fun x => ⟨N • (x : V), hK x x.2⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp [smul_add]) }
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply nsmulHom_injective (V := V) N hN
    exact congrArg Subtype.val hxy
  haveI : Module.Finite ℤ K := Module.Finite.of_injective g.toIntLinearMap hg
  refine relIndex_ne_zero_of_nsmul_mem H K (M * N) (Nat.mul_pos hM hN) ?_
  intro x hx
  rw [mul_smul]
  exact hH _ (hK x hx)

end Index

section Lattice

instance periodLattice_finite (L : PeriodPair) : Module.Finite ℤ L.lattice := ZLattice.module_finite ℝ L.lattice

def stdLatEquiv (L : PeriodPair) (m : Type*) : stdLat L m ≃+ (m → L.lattice) where
  toFun x := fun i => ⟨(x : m → ℂ) i, (mem_stdLat L m x).1 x.2 i⟩
  invFun y := ⟨fun i => (y i : ℂ), (mem_stdLat L m _).2 fun i => (y i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem stdLat_finite (L : PeriodPair) (m : Type*) [Finite m] : Module.Finite ℤ (stdLat L m) := Module.Finite.equiv (stdLatEquiv L m).symm.toIntLinearEquiv

theorem mem_stdLat_fin_four_prod_iff_mem_pow4 (L : PeriodPair) (n : Type*) (x : Fin 4 × n → ℂ) :
    x ∈ stdLat L (Fin 4 × n) ↔ x ∈ pow4 (stdLat L n) := by
  rw [mem_stdLat]
  show _ ↔ ∀ a, slice a x ∈ stdLat L n
  simp only [mem_stdLat, slice]
  exact ⟨fun h a i => h (a, i), fun h p => h p.1 p.2⟩

theorem cmPair_mul_mem (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (k : ℂ) (hk : InK d k) :
    ∃ N : ℕ, 0 < N ∧ ∀ z ∈ (Formalism.L2.Th1.F.cmPair a b d ha hd).lattice,
      (N : ℂ) * k * z ∈ (Formalism.L2.Th1.F.cmPair a b d ha hd).lattice := by
  obtain ⟨p, q, rfl⟩ := hk
  have hs : ((Real.sqrt (d : ℝ) : ℝ) : ℂ) * ((Real.sqrt (d : ℝ) : ℝ) : ℂ) = (d : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp
  have hδ2 : (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ)) * (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ))
      = -(d : ℂ) := by
    linear_combination (Complex.I * Complex.I) * hs + (d : ℂ) * Complex.I_mul_I
  have hpP : (p : ℂ) * (p.den : ℂ) = (p.num : ℂ) := by exact_mod_cast Rat.mul_den_eq_num p
  have hqQ : (q : ℂ) * (q.den : ℂ) = (q.num : ℂ) := by exact_mod_cast Rat.mul_den_eq_num q
  refine ⟨2 * a * p.den * q.den, by positivity, ?_⟩
  intro z hz
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 hz
  rw [PeriodPair.mem_lattice]
  refine ⟨m * (2 * a * q.den * p.num - 2 * a * p.den * q.num * b) + n * (-(p.den * q.num * (b ^ 2 + d))),
    m * (2 * a * (2 * a * p.den * q.num)) + n * (2 * a * q.den * p.num + 2 * a * p.den * q.num * b), ?_⟩
  simp only [Formalism.L2.Th1.F.cmPair, Formalism.L2.Th1.F.cmTheta]
  push_cast
  linear_combination
    (-((m : ℂ) * a + n * ((b + Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ)) / 2)) * (2 * a * q.den)) * hpP
    - ((m : ℂ) * a + n * ((b + Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ)) / 2))
        * (2 * a * p.den * (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ))) * hqQ
    - ((a : ℂ) * p.den * q.num * n) * hδ2

theorem cmL_mul_mem (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (k : ℂ)
    (hk : InK d k) : ∃ N : ℕ, 0 < N ∧ ∀ z ∈ (cmL a b d ha hd lam hlam).lattice,
      (N : ℂ) * k * z ∈ (cmL a b d ha hd lam hlam).lattice := by
  obtain ⟨N, hN, hmul⟩ := cmPair_mul_mem a b d ha hd k hk
  refine ⟨N, hN, fun z hz => ?_⟩
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 hz
  have h0 : ((m : ℂ) * (Formalism.L2.Th1.F.cmPair a b d ha hd).ω₁ + n * (Formalism.L2.Th1.F.cmPair a b d ha hd).ω₂)
      ∈ (Formalism.L2.Th1.F.cmPair a b d ha hd).lattice :=
    PeriodPair.mem_lattice.2 ⟨m, n, rfl⟩
  obtain ⟨m', n', hmn⟩ := PeriodPair.mem_lattice.1 (hmul _ h0)
  rw [PeriodPair.mem_lattice]
  refine ⟨m', n', ?_⟩
  simp only [cmL, Formalism.L2.Th1.F.scalePair]
  linear_combination lam * hmn

theorem entries_bound (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
    {m : Type*} [Fintype m] [DecidableEq m] (f : (m → ℂ) →ₗ[ℂ] (m → ℂ))
    (hf : ∀ w w', InK d (f (Pi.single w' 1) w)) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ stdLat (cmL a b d ha hd lam hlam) m, N • f x ∈ stdLat (cmL a b d ha hd lam hlam) m := by
  classical
  choose Nf hNf hmem using fun p : m × m => cmL_mul_mem a b d ha hd lam hlam _ (hf p.1 p.2)
  refine ⟨∏ p, Nf p, Finset.prod_pos fun p _ => hNf p, fun x hx => ?_⟩
  rw [mem_stdLat] at hx ⊢
  intro w
  have hfx : f x w = ∑ w', x w' * f (Pi.single w' 1) w := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun w' _ => ?_
    rw [show (Pi.single w' (x w') : m → ℂ) = x w' • (Pi.single w' (1 : ℂ) : m → ℂ) by
      ext j; simp [Pi.single_apply]]
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
  show (∏ p, Nf p) • f x w ∈ _
  rw [hfx, Finset.smul_sum]
  refine Submodule.sum_mem _ fun w' _ => ?_
  have h1 := hmem (w, w') (x w') (hx w')
  obtain ⟨r, hr⟩ : Nf (w, w') ∣ ∏ p, Nf p := Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
  rw [hr]
  have hre : (Nf (w, w') * r) • (x w' * f (Pi.single w' 1) w)
      = r • ((Nf (w, w') : ℂ) * f (Pi.single w' 1) w * x w') := by
    rw [nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [hre]
  exact nsmul_mem h1 r

end Lattice

private theorem exists_pos_nsmul_mem_of_relIndex_ne_zero {W : Type*} [AddCommGroup W] (H K : AddSubgroup W)
    (h : H.relIndex K ≠ 0) : ∃ N : ℕ, 0 < N ∧ ∀ x ∈ K, N • x ∈ H := by
  refine ⟨H.relIndex K, Nat.pos_of_ne_zero h, fun x hx => ?_⟩
  have hmem := AddSubgroup.nsmul_index_mem (H.addSubgroupOf K) ⟨x, hx⟩
  show (H.addSubgroupOf K).index • x ∈ H
  simpa [AddSubgroup.mem_addSubgroupOf] using hmem

theorem CommensurableK_proof : CommensurableK := by
  intro a b d ha hd lam hlam n _ _ Λ h1 h2 g hg hg'
  unfold relIdx at *
  obtain ⟨N₁, hN₁, hΛ₁⟩ := exists_pos_nsmul_mem_of_relIndex_ne_zero _ _ h1
  obtain ⟨N₂, hN₂, hΛ₂⟩ := exists_pos_nsmul_mem_of_relIndex_ne_zero _ _ h2
  obtain ⟨N₃, hN₃, hg3⟩ := entries_bound a b d ha hd lam hlam (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) hg
  obtain ⟨N₄, hN₄, hg4⟩ :=
    entries_bound a b d ha hd lam hlam (g.symm : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) hg'
  haveI := stdLat_finite (cmL a b d ha hd lam hlam) (Fin 4 × n)
  have hp1 : ∀ x ∈ pow4 Λ, N₁ • x ∈ stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n) := by
    intro x hx
    have hx' : ∀ i, slice i x ∈ Λ := hx
    rw [mem_stdLat_fin_four_prod_iff_mem_pow4]
    show ∀ i, slice i (N₁ • x) ∈ stdLat (cmL a b d ha hd lam hlam) n
    intro i
    exact hΛ₁ _ (hx' i)
  have hp2 : ∀ x ∈ stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n), N₂ • x ∈ pow4 Λ := by
    intro x hx
    rw [mem_stdLat_fin_four_prod_iff_mem_pow4] at hx
    have hx' : ∀ i, slice i x ∈ stdLat (cmL a b d ha hd lam hlam) n := hx
    show ∀ i, slice i (N₂ • x) ∈ Λ
    intro i
    exact hΛ₂ _ (hx' i)
  constructor
  · refine relIndex_ne_zero_of_bound _ _ (stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n)) (N₃ * N₁) 1
      (Nat.mul_pos hN₃ hN₁) one_pos ?_ (fun x hx => by simpa using hx)
    intro y hy
    rw [imgLat, AddSubgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [mul_smul]
    have := hg3 _ (hp1 x hx)
    rw [map_nsmul] at this
    exact this
  · refine relIndex_ne_zero_of_bound _ _ (stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n)) 1 (N₂ * N₄)
      one_pos (Nat.mul_pos hN₂ hN₄) (fun x hx => by simpa using hx) ?_
    intro z hz
    rw [imgLat, AddSubgroup.mem_map]
    refine ⟨(N₂ * N₄) • g.symm z, ?_, ?_⟩
    · rw [mul_smul]
      exact hp2 _ (hg4 z hz)
    · rw [LinearMap.toAddMonoidHom_coe, map_nsmul, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

end Formalism.L2.Th1.H
