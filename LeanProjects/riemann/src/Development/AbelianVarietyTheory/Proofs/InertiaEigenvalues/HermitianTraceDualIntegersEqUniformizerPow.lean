import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStableGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedStandardAddCharConductorProperties
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.DualLattice

variable {R : Type} [CommRing R]

theorem eq_zpow_mul_unit (O : Subring R) (p : Rˣ)
    (hdich : ∀ y ∈ O, (∃ z ∈ O, y = (p : R) * z) ∨ ∃ z ∈ O, y * z = 1)
    (hsep : ∀ x : R, x ≠ 0 → ∃ n : ℕ, ∀ z ∈ O, (p : R) ^ n * z ≠ x)
    (hex : ∀ y : R, ∃ n : ℕ, (p : R) ^ n * y ∈ O) :
    ∀ y : R, y ≠ 0 → ∃ v : ℤ, ∃ u ∈ O, (∃ w ∈ O, u * w = 1) ∧ y = ((p ^ v : Rˣ) : R) * u := by
  classical
  have hO : ∀ x ∈ O, x ≠ 0 → ∃ k : ℕ, ∃ u ∈ O, (∃ w ∈ O, u * w = 1) ∧ x = (p : R) ^ k * u := by
    intro x hxO hx0
    have hex' : ∃ k : ℕ, ¬ ∃ z ∈ O, x = (p : R) ^ k * z := by
      obtain ⟨n, hn⟩ := hsep x hx0
      exact ⟨n, fun ⟨z, hz, hzx⟩ => hn z hz hzx.symm⟩
    obtain ⟨m, hm, hmin⟩ : ∃ m : ℕ, (¬ ∃ z ∈ O, x = (p : R) ^ m * z) ∧
        ∀ j < m, ∃ z ∈ O, x = (p : R) ^ j * z :=
      ⟨Nat.find hex', Nat.find_spec hex', fun j hj => by simpa using Nat.find_min hex' hj⟩
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hm ⟨x, hxO, by simp⟩
    obtain ⟨z, hz, hxz⟩ := hmin (m - 1) (by omega)
    rcases hdich z hz with ⟨w, hw, hzw⟩ | hu
    · exfalso
      apply hm
      refine ⟨w, hw, ?_⟩
      rw [hxz, hzw, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)]
    · exact ⟨_, z, hz, hu, hxz⟩
  intro y hy
  obtain ⟨n, hn⟩ := hex y
  have hne : (p : R) ^ n * y ≠ 0 := by
    intro h
    apply hy
    have := congrArg (fun t => ((p⁻¹ : Rˣ) : R) ^ n * t) h
    simpa [← mul_assoc, ← mul_pow] using this
  obtain ⟨k, u, hu, hunit, hk⟩ := hO _ hn hne
  refine ⟨(k : ℤ) - n, u, hu, hunit, ?_⟩
  have e1 : ((p ^ ((k : ℤ) - n) : Rˣ) : R) = ((p⁻¹ : Rˣ) : R) ^ n * (p : R) ^ k := by
    rw [_root_.zpow_sub, zpow_natCast, zpow_natCast, Units.val_mul, ← inv_pow, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, mul_comm]
  rw [e1, mul_assoc, ← hk, ← mul_assoc, ← mul_pow]
  simp

theorem eq_zpow_smul (O : Subring R) (p : Rˣ) (D : Set R) (hpO : (p : R) ∈ O)
    (hmul : ∀ y ∈ D, ∀ r ∈ O, r * y ∈ D)
    (hbig : ∃ n : ℕ, ∀ z ∈ O, (p : R) ^ n * z ∈ D)
    (hne : ∃ y, y ∉ D)
    (hex : ∀ y : R, ∃ n : ℕ, (p : R) ^ n * y ∈ O)
    (hunit : ∀ y : R, y ≠ 0 → ∃ v : ℤ, ∃ u ∈ O, (∃ w ∈ O, u * w = 1) ∧ y = ((p ^ v : Rˣ) : R) * u) :
    ∃ e : ℤ, D = {y | ∃ z ∈ O, y = ((p ^ e : Rˣ) : R) * z} := by
  classical
  have hup : ∀ v : ℤ, ((p ^ v : Rˣ) : R) ∈ D → ∀ k : ℕ, ((p ^ (v + k) : Rˣ) : R) ∈ D := by
    intro v hv k
    have : ((p ^ (v + k) : Rˣ) : R) = (p : R) ^ k * ((p ^ v : Rˣ) : R) := by
      rw [_root_.zpow_add, zpow_natCast, mul_comm, Units.val_mul, Units.val_pow_eq_pow_val]
    rw [this]
    exact hmul _ hv _ (pow_mem hpO k)
  obtain ⟨n, hn⟩ := hbig
  have hinh : ∃ v : ℤ, ((p ^ v : Rˣ) : R) ∈ D := ⟨n, by simpa using hn 1 (one_mem O)⟩
  have hbdd : ∃ b : ℤ, ∀ v : ℤ, ((p ^ v : Rˣ) : R) ∈ D → b ≤ v := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ v : ℤ, ((p ^ v : Rˣ) : R) ∈ D := by
      intro v
      obtain ⟨w, hw, hwv⟩ := hcon v
      have := hup w hw (v - w).toNat
      rwa [Int.toNat_of_nonneg (by omega), add_sub_cancel] at this
    obtain ⟨y, hy⟩ := hne
    obtain ⟨m, hm⟩ := hex y
    apply hy
    have h1 := hmul _ (hall (-(m : ℤ))) _ hm
    have hq : ((p ^ (-(m : ℤ)) : Rˣ) : R) * (p : R) ^ m = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← _root_.zpow_add,
        neg_add_cancel, zpow_zero, Units.val_one]
    have h2 : (p : R) ^ m * y * ((p ^ (-(m : ℤ)) : Rˣ) : R) = y := by
      linear_combination y * hq
    rwa [h2] at h1
  obtain ⟨e, he, hmin⟩ := Int.exists_least_of_bdd hbdd hinh
  refine ⟨e, Set.ext fun y => ⟨fun hy => ?_, fun ⟨z, hz, hyz⟩ => ?_⟩⟩
  · by_cases hy0 : y = 0
    · exact ⟨0, zero_mem O, by simp [hy0]⟩
    obtain ⟨v, u, hu, ⟨w, hw, huw⟩, hyv⟩ := hunit y hy0
    have hv : ((p ^ v : Rˣ) : R) ∈ D := by
      have := hmul y hy w hw
      have e2 : w * y = ((p ^ v : Rˣ) : R) := by rw [hyv, mul_comm, mul_assoc, huw, mul_one]
      rwa [e2] at this
    have hev := hmin v hv
    refine ⟨(p : R) ^ (v - e).toNat * u, O.mul_mem (pow_mem hpO _) hu, ?_⟩
    rw [hyv, ← mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← _root_.zpow_add,
      Int.toNat_of_nonneg (by omega), add_sub_cancel]
  · rw [hyz, mul_comm]
    exact hmul _ he _ hz

end GlobalTheory.JR.DualLattice

namespace GlobalTheory.JR.DualLattice

set_option maxHeartbeats 1000000 in

theorem dual_eq_zpow : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → IsField A.K → IsField A.L → ∀ (ϖ : A.Kˣ) (O : Subring A.L), IsOpen (O : Set A.L) → IsCompact (O : Set A.L) → (∀ y ∈ O, star y ∈ O) → algebraMap A.K A.L (ϖ : A.K) ∈ O → (¬ ∃ z ∈ O, algebraMap A.K A.L (ϖ : A.K) * z = 1) → (∀ y ∈ O, (∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z) ∨ ∃ z ∈ O, y * z = 1) → (∀ U ∈ 𝓝 (0 : A.L), ∃ n : ℕ, ∀ z ∈ O, algebraMap A.K A.L ((ϖ : A.K) ^ n) * z ∈ U) → (∀ y : A.L, ∃ n : ℕ, algebraMap A.K A.L ((ϖ : A.K) ^ n) * y ∈ O) → ∀ a : A.Kˣ, ∃ e : ℤ, {y : A.L | ∀ m ∈ O, A.kerL ψ (a : A.K) y m = 1} = {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L ((ϖ ^ e : A.Kˣ) : A.K) * z} := by
  intro F E _ _ _ _ U A ψ hψ hK hL ϖ O hOo hOc hOstar hpO hpnu hdich hnbhd hex a
  have := U.charZero; have := U.ultraF; have := U.lcF
  have := EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have hLnt : Nontrivial A.L := ⟨hL.exists_pair_ne⟩
  have hKnt : Nontrivial A.K := ⟨hK.exists_pair_ne⟩
  let p : A.Lˣ := Units.map (algebraMap A.K A.L).toMonoidHom ϖ
  have hp : (p : A.L) = algebraMap A.K A.L (ϖ : A.K) := rfl
  have hpz : ∀ v : ℤ, ((p ^ v : A.Lˣ) : A.L) = algebraMap A.K A.L ((ϖ ^ v : A.Kˣ) : A.K) := by
    intro v
    rw [show p ^ v = Units.map (algebraMap A.K A.L).toMonoidHom (ϖ ^ v) from (map_zpow _ ϖ v).symm]
    rfl
  have hpn : ∀ n : ℕ, (p : A.L) ^ n = algebraMap A.K A.L ((ϖ : A.K) ^ n) := by
    intro n; rw [hp, map_pow]

  have hmul : ∀ y ∈ {y : A.L | ∀ m ∈ O, A.kerL ψ (a : A.K) y m = 1}, ∀ r ∈ O,
      r * y ∈ {y : A.L | ∀ m ∈ O, A.kerL ψ (a : A.K) y m = 1} := by
    intro y hy r hr m hm
    have e1 : star (r * y) * m = star y * (star r * m) := by rw [star_mul']; ring
    simp only [Et.kerL, Set.mem_setOf_eq] at hy ⊢
    rw [e1]
    exact hy _ (O.mul_mem (hOstar r hr) hm)

  have hψl : IsLocallyConstant (fun x => ψ x) := ((GlobalTheory.StdChar.psi_conductor F E).2 ψ hψ).1
  have hg : Continuous (fun q : A.L × A.L =>
      Algebra.trace F A.K ((a : A.K) * Algebra.trace A.K A.L (star q.1 * q.2))) := by
    have hs : Continuous (star : A.L → A.L) := IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)
    have ht : Continuous (Algebra.trace A.K A.L) :=
      IsModuleTopology.continuous_of_linearMap ((Algebra.trace A.K A.L).restrictScalars F)
    have htF : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K)
    exact htF.comp (continuous_const.mul (ht.comp ((hs.comp continuous_fst).mul continuous_snd)))
  have hW : IsOpen {q : A.L × A.L | A.kerL ψ (a : A.K) q.1 q.2 = 1} :=
    (hψl.isOpen_fiber 1).preimage hg
  obtain ⟨u, v, hu, -, h0u, hOv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := (0 : A.L))) hOc hW
    (by
      rintro ⟨y, m⟩ ⟨hy, -⟩
      simp only [Set.mem_singleton_iff] at hy
      subst hy
      simp [Et.kerL, Et.psiK])
  obtain ⟨n, hn⟩ := hnbhd u (hu.mem_nhds (h0u rfl))
  have hbig : ∃ n : ℕ, ∀ z ∈ O, (p : A.L) ^ n * z ∈ {y : A.L | ∀ m ∈ O, A.kerL ψ (a : A.K) y m = 1} := by
    refine ⟨n, fun z hz m hm => ?_⟩
    have : ((p : A.L) ^ n * z, m) ∈ u ×ˢ v := ⟨by rw [hpn]; exact hn z hz, hOv hm⟩
    exact huv this

  have hinj : ∀ k₁ k₂ : A.K, algebraMap A.K A.L k₁ = algebraMap A.K A.L k₂ → k₁ = k₂ := by
    intro k₁ k₂ h
    by_contra hne
    obtain ⟨k', hk'⟩ := hK.mul_inv_cancel (sub_ne_zero.2 hne)
    have : algebraMap A.K A.L ((k₁ - k₂) * k') = 0 := by rw [map_mul, map_sub, h, sub_self, zero_mul]
    rw [hk', map_one] at this
    exact one_ne_zero this
  have hne : ∃ y, y ∉ {y : A.L | ∀ m ∈ O, A.kerL ψ (a : A.K) y m = 1} := by
    obtain ⟨-, x, hx, -⟩ := hψ
    have hd : (Module.finrank F A.K : F) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    set t : F := x / (2 * (Module.finrank F A.K : F)) with ht
    set c : A.K := ((a⁻¹ : A.Kˣ) : A.K) * algebraMap F A.K t with hc
    refine ⟨algebraMap A.K A.L c, fun h => hx ?_⟩
    have h1 := h 1 (one_mem O)
    have htr : Algebra.trace A.K A.L (star (algebraMap A.K A.L c) * 1) = 2 * c := by
      apply hinj
      rw [mul_one, A.star_K, (GlobalTheory.JR.EtFacts.main F E A).2.1, A.star_K, two_mul, map_add]
    have hac : (a : A.K) * (2 * c) = algebraMap F A.K (2 * t) := by
      rw [hc, map_mul, map_ofNat, ← mul_assoc, mul_comm (a : A.K) 2, mul_assoc 2, ← mul_assoc (a : A.K),
        Units.mul_inv, one_mul]
    simp only [Et.kerL, Et.psiK, htr, hac, Algebra.trace_algebraMap, nsmul_eq_mul] at h1
    rw [← h1, ht]
    congr 1
    field_simp

  have hsep : ∀ x : A.L, x ≠ 0 → ∃ n : ℕ, ∀ z ∈ O, (p : A.L) ^ n * z ≠ x := by
    intro x hx
    obtain ⟨n, hn⟩ := hnbhd {x}ᶜ (isOpen_compl_singleton.mem_nhds (Ne.symm hx))
    exact ⟨n, fun z hz => by rw [hpn]; exact hn z hz⟩
  have hex' : ∀ y : A.L, ∃ n : ℕ, (p : A.L) ^ n * y ∈ O := by
    intro y
    obtain ⟨n, hn⟩ := hex y
    exact ⟨n, by rw [hpn]; exact hn⟩
  have hdich' : ∀ y ∈ O, (∃ z ∈ O, y = (p : A.L) * z) ∨ ∃ z ∈ O, y * z = 1 := by
    rw [hp]; exact hdich
  have hunit := eq_zpow_mul_unit O p hdich' hsep hex'
  obtain ⟨e, he⟩ := eq_zpow_smul O p _ (by rw [hp]; exact hpO) hmul hbig hne hex' hunit
  refine ⟨e, ?_⟩
  rw [he]
  simp only [hpz]

end GlobalTheory.JR.DualLattice
