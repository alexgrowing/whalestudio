import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnimodularLatticeLocalConjSymm

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.TwistSd

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

omit [StarRing E] in
theorem mem_twO_iff (N : Submodule (𝓞 E) (Sp E n)) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ) (y : Sp E n) :
    y ∈ twist₂ N c e ↔ ∀ Q : HeightOneSpectrum (𝓞 E), ((c : E) ^ e Q)⁻¹ • y ∈ localization₂ Q.asIdeal N := by
  simp [twist₂, Submodule.mem_iInf]

omit [StarRing E] in
theorem zpow_smul_mem (M : Submodule (𝓞 E) (Sp E n)) (c : ℕ) {k : ℤ} (hk : 0 ≤ k) {y : Sp E n} (hy : y ∈ M) :
    ((c : E) ^ k) • y ∈ M := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  have : ((c : E) ^ (m : ℤ)) • y = ((c : 𝓞 E) ^ m) • y := by
    rw [← algebraMap_smul E ((c : 𝓞 E) ^ m) y, map_pow, map_natCast, zpow_natCast]
  rw [this]
  exact M.smul_mem _ hy

omit [StarRing E] in

theorem isLattice_twO {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N) {c : ℕ} (hc : 0 < c)
    {e : HeightOneSpectrum (𝓞 E) → ℤ} (he : ∀ Q, -1 ≤ e Q ∧ e Q ≤ 1) : Submodule.IsLattice E (twist₂ N c e) := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  have h1 : ∀ x ∈ twist₂ N c e, (c : E) • x ∈ N := fun x hx => mem_of_locP fun Q => by
    have := zpow_smul_mem _ c (k := 1 + e Q) (by have := he Q; omega) ((mem_twO_iff N c e x).1 hx Q)
    rwa [smul_smul, zpow_add₀ hcE, zpow_one, mul_inv_cancel_right₀ (zpow_ne_zero _ hcE)] at this
  have h2 : ∀ x ∈ N, (c : E) • x ∈ twist₂ N c e := fun x hx => (mem_twO_iff N c e _).2 fun Q => by
    have := zpow_smul_mem _ c (k := 1 - e Q) (by have := he Q; omega) (mem_localization_of_mem Q hx)
    rwa [zpow_sub₀ hcE, zpow_one, div_eq_mul_inv, mul_comm, ← smul_smul] at this
  refine ⟨?_, ?_⟩
  · let f : Sp E n →ₗ[𝓞 E] Sp E n := ((c : E) • (LinearMap.id : Sp E n →ₗ[E] Sp E n)).restrictScalars (𝓞 E)
    have hf : Function.Injective f := fun x y h => smul_right_injective _ hcE h
    refine Submodule.fg_of_fg_map_injective f hf (Submodule.FG.of_le hN.fg ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact h1 x hx
  · rw [eq_top_iff, ← hN.span_eq_top, Submodule.span_le]
    intro x hx
    have : x = (c : E)⁻¹ • (c : E) • x := by rw [smul_smul, inv_mul_cancel₀ hcE, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (h2 x hx))

theorem hStd_zpow_left (c : ℕ) (k : ℤ) (y x : Sp E n) :
    hStd E n (((c : E) ^ k) • y) x = hStd E n y (((c : E) ^ k) • x) := by
  rw [LinearMap.map_smulₛₗ₂, LinearMap.map_smul, map_zpow₀, map_natCast]

theorem isSdLat_twO {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) {c : ℕ} (hc : 0 < c)
    {e : HeightOneSpectrum (𝓞 E) → ℤ} (he : ∀ Q, -1 ≤ e Q ∧ e Q ≤ 1) (hodd : ∀ Q, e (conjPrime₂ Q) = -e Q) :
    IsSdLat (twist₂ N c e) := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  refine ⟨isLattice_twO hN.1 hc he, ?_⟩
  change dual (hStd E n) (twist₂ N c e) = twist₂ N c e
  apply le_antisymm
  · intro x hx
    rw [mem_dual] at hx
    refine (mem_twO_iff N c e x).2 fun Q' => ?_
    obtain ⟨Q, rfl⟩ : ∃ Q, Q' = conjPrime₂ Q := ⟨conjPrime₂ Q', (GlobalTheory.GO.UniExt.conjP_involutive Q').symm⟩
    rw [GlobalTheory.GO.UniExt.mem_localization_conj_iff hN.1.fg hN.2, hodd, zpow_neg, inv_inv]
    intro y hy
    have hy' : ((c : E) ^ e Q) • y ∈ localization₂ Q.asIdeal (twist₂ N c e) := by
      rwa [mem_localization_twist N hc he, smul_smul, inv_mul_cancel₀ (zpow_ne_zero _ hcE), one_smul]
    obtain ⟨t, ht, hty⟩ := hy'
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hx _ hty)
    refine ⟨r, cO E t, fun h => ht (by rwa [mem_conjP, cO_cO] at h), ?_⟩
    rw [hr, ← hStd_zpow_left, hStd_osmul_left, ← algebraMap_smul E (cO E t) x, LinearMap.map_smul, smul_eq_mul]
  · intro x hx
    rw [mem_dual]
    intro y hy
    refine mem_of_locP fun Q' => ?_
    obtain ⟨Q, rfl⟩ : ∃ Q, Q' = conjPrime₂ Q := ⟨conjPrime₂ Q', (GlobalTheory.GO.UniExt.conjP_involutive Q').symm⟩
    have h1 := (mem_twO_iff N c e x).1 hx (conjPrime₂ Q)
    rw [GlobalTheory.GO.UniExt.mem_localization_conj_iff hN.1.fg hN.2, hodd, zpow_neg, inv_inv] at h1
    obtain ⟨r, s, hs, hrs⟩ := h1 _ ((mem_twO_iff N c e y).1 hy Q)
    rw [← hStd_zpow_left, smul_smul, mul_inv_cancel₀ (zpow_ne_zero _ hcE), one_smul] at hrs
    exact ⟨s, hs, Submodule.mem_one.2 ⟨r, by rw [← hrs, Algebra.smul_def]⟩⟩

theorem expS_conjP {S : Finset (HeightOneSpectrum (𝓞 E))} (hS : ∀ P ∈ S, conjPrime₂ P ∉ S) (Q : HeightOneSpectrum (𝓞 E)) :
    expS S (conjPrime₂ Q) = -expS S Q := by
  unfold expS
  rw [GlobalTheory.GO.UniExt.conjP_involutive]
  by_cases h : Q ∈ S
  · simp [h, hS Q h]
  · by_cases h' : conjPrime₂ Q ∈ S <;> simp [h, h']

theorem isSdLat_twO_expS : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (N : Submodule (𝓞 E) (Sp E n)) (c : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ P ∈ S, conjPrime₂ P ∉ S) → IsSdLat N → 0 < c →
    IsSdLat (twist₂ N c (expS S)) ∧ IsSdLat (twist₂ N c fun Q => -expS S Q) := by
  intro E _ _ _ n N c S hS hN hc
  refine ⟨isSdLat_twO hN hc (expS_bound S) (expS_conjP hS), isSdLat_twO hN hc (fun Q => ?_) fun Q => ?_⟩
  · have := expS_bound S Q
    omega
  · rw [expS_conjP hS]

end GlobalTheory.ThetaMove.TwistSd
