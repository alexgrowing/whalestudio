import Formalism.LagrangeIdealLifts.Statement
import Formalism.WindowSums.AnnihilatorPolynomials.ValProd
import Formalism.WindowSums.AnnihilatorPolynomials.ZpowVal

noncomputable section

namespace Formalism.LIFT

section SlopeTestRemainingChoices

variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {B : Base ℓ A} {M : ℕ}
variable {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]

lemma uc_bij (W : WD B M D) (k : ℕ) : Function.Bijective (fun x : D => B.Q ^ k • x) := by
  have h : (fun x : D => B.Q ^ k • x) = (fun x : D => B.Q • x)^[k] := by
    funext x
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply', ← ih, pow_succ', mul_smul]
  rw [h]
  exact W.Q_bij.iterate k

lemma uc_smul_comm_A (a b : A) (x : D) : a • b • x = b • a • x := by
  rw [smul_smul, mul_comm, ← smul_smul]

lemma uc_qinv_add (W : WD B M D) {x y : D} (hx : W.QInv x) (hy : W.QInv y) : W.QInv (x + y) := by
  unfold WD.QInv at *
  rw [smul_add]
  exact W.N.add_mem hx hy

lemma uc_qinv_sub (W : WD B M D) {x y : D} (hx : W.QInv x) (hy : W.QInv y) : W.QInv (x - y) := by
  unfold WD.QInv at *
  rw [smul_sub]
  exact W.N.sub_mem hx hy

lemma uc_qinv_smul (W : WD B M D) (r : ℤ_[ℓ]) {x : D} (hx : W.QInv x) : W.QInv (r • x) := by
  unfold WD.QInv at *
  rw [← algebraMap_smul A r x, uc_smul_comm_A]
  exact W.N.smul_mem _ hx

lemma uc_qinv_phi_sub (W : WD B M D) {x : D} (hx : x ∈ W.N) : W.QInv (W.φ x - x) := by
  unfold WD.QInv
  rw [smul_sub]
  exact W.N.sub_mem (W.φ_N x hx) (W.N.smul_mem _ hx)

lemma d1_sub_sub (W : WD B M D) (y z y' z' : D) :
    W.d1 (y - y') (z - z') = W.d1 y z - W.d1 y' z' := by
  unfold WD.d1
  rw [map_sub, map_sub]
  abel

lemma uc_smul (W : WD B M D) (r : ℤ_[ℓ]) (y z : D) :
    W.d1 (r • y) (r • z) = r • W.d1 y z := by
  unfold WD.d1
  rw [map_smul, map_smul, smul_sub, smul_sub, smul_sub]

lemma uc_gamma (W : WD B M D) {y : D} (hy : W.QInv y) :
    ∃ a, W.QInv a ∧ W.γ y - y = B.X • a := by
  obtain ⟨t, hu, hγQ⟩ := B.γQ
  have hn : B.Q ^ M • y ∈ W.N := hy
  obtain ⟨n', hn', he⟩ := W.γ_N _ hn
  rw [W.γ_smul, map_pow, hγQ, mul_pow] at he
  obtain ⟨w, hw⟩ := (uc_bij W M).2 n'
  have hw' : B.Q ^ M • w = n' := hw
  have h1 : (1 + B.X * t) ^ M • W.γ y - y = B.X • w := by
    apply (uc_bij W M).1
    show B.Q ^ M • ((1 + B.X * t) ^ M • W.γ y - y) = B.Q ^ M • (B.X • w)
    rw [smul_sub, smul_smul, he, ← hw', uc_smul_comm_A]
  obtain ⟨s', hs'⟩ : B.X * t ∣ (1 + B.X * t) ^ M - 1 := by
    have h2 := sub_dvd_pow_sub_pow (1 + B.X * t) 1 M
    rwa [one_pow, add_sub_cancel_left] at h2
  obtain ⟨v, hv⟩ := (hu.pow M).exists_left_inv
  refine ⟨v • w - (v * (t * s')) • y, ?_, ?_⟩
  · unfold WD.QInv
    rw [smul_sub, uc_smul_comm_A, hw', uc_smul_comm_A]
    exact W.N.sub_mem (W.N.smul_mem _ hn') (W.N.smul_mem _ hn)
  · calc W.γ y - y = (v * (1 + B.X * t) ^ M) • W.γ y - (v * (1 + B.X * t) ^ M) • y := by
          rw [hv, one_smul, one_smul]
      _ = v • ((1 + B.X * t) ^ M • W.γ y - y) - v • (((1 + B.X * t) ^ M - 1) • y) := by
          rw [smul_sub, sub_smul, one_smul, smul_sub, smul_smul, smul_smul]
          abel
      _ = v • (B.X • w) - v • ((B.X * (t * s')) • y) := by
          rw [h1, hs', mul_assoc]
      _ = B.X • (v • w - (v * (t * s')) • y) := by
          rw [smul_sub, smul_smul, smul_smul, smul_smul, smul_smul, mul_comm v B.X, mul_left_comm v B.X]

end SlopeTestRemainingChoices

section Aux2

variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {B : Base ℓ A} {M : ℕ}
variable {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]

lemma uc_phi (W : WD B M D) {n : D} (hn : n ∈ W.N) :
    W.QInv (B.Q • W.φ n - n) ∧ W.φ (B.X • n) - B.X • n = B.X • (B.Q • W.φ n - n) := by
  refine ⟨?_, ?_⟩
  · unfold WD.QInv
    rw [smul_sub, smul_smul, ← pow_succ, pow_succ', mul_smul]
    exact W.N.sub_mem (W.N.smul_mem _ (W.φ_N n hn)) (W.N.smul_mem _ hn)
  · rw [W.φ_smul, B.φX, mul_smul, smul_sub]

lemma uc_xn_sub (W : WD B M D) {x y : D} (hx : W.XN x) (hy : W.XN y) : W.XN (x - y) := by
  obtain ⟨n, hn, rfl⟩ := hx
  obtain ⟨n', hn', rfl⟩ := hy
  exact ⟨n - n', W.N.sub_mem hn hn', by rw [smul_sub]⟩

lemma uc_xn_smul (W : WD B M D) (r : ℤ_[ℓ]) {x : D} (hx : W.XN x) : W.XN (r • x) := by
  obtain ⟨n, hn, rfl⟩ := hx
  refine ⟨r • n, ?_, ?_⟩
  · rw [← algebraMap_smul A r n]
    exact W.N.smul_mem _ hn
  · rw [← algebraMap_smul A r, ← algebraMap_smul A r n, uc_smul_comm_A]

lemma uc_cocycle_smul (W : WD B M D) (r : ℤ_[ℓ]) {y z : D} (h : W.Cocycle y z) :
    W.Cocycle (r • y) (r • z) := by
  obtain ⟨⟨hq, hx⟩, hd⟩ := h
  exact ⟨⟨uc_qinv_smul W r hq, uc_xn_smul W r hx⟩, by rw [uc_smul, hd, smul_zero]⟩

end Aux2

section Aux3

variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {B : Base ℓ A} {M : ℕ}
variable {D D' : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
  [AddCommGroup D'] [Module A D'] [Module ℤ_[ℓ] D'] [IsScalarTower ℤ_[ℓ] A D']
  {W : WD B M D} {W' : WD B M D'}

lemma uc_hom_tsmul (f : Hom W W') (r : ℤ_[ℓ]) (x : D) : f.f (r • x) = r • f.f x := by
  rw [← algebraMap_smul A r x, map_smul, algebraMap_smul]

lemma uc_hom (f : Hom W W') (y z : D) : f.f (W.d1 y z) = W'.d1 (f.f y) (f.f z) := by
  unfold WD.d1
  rw [map_sub, map_sub, map_sub, f.γ_comm, f.φ_comm]

lemma uc_hom_qinv (f : Hom W W') {x : D} (hx : W.QInv x) : W'.QInv (f.f x) := by
  unfold WD.QInv at *
  rw [← map_smul]
  exact f.N_le _ hx

lemma uc_hom_xn (f : Hom W W') {x : D} (hx : W.XN x) : W'.XN (f.f x) := by
  obtain ⟨n, hn, rfl⟩ := hx
  exact ⟨f.f n, f.N_le n hn, map_smul _ _ _⟩

end Aux3

section DiagramChase₂

variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {B : Base ℓ A} {M : ℕ}
variable {D₀ D₁ D₂ : Type}
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[ℓ] D₀] [IsScalarTower ℤ_[ℓ] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
    {W₀ : WD B M D₀} {W₁ : WD B M D₁} {W₂ : WD B M D₂}

lemma uc_pi_iota (S : SES W₀ W₁ W₂) (x : D₀) : S.π.f (S.ι.f x) = 0 := (S.exact (S.ι.f x)).mpr ⟨x, rfl⟩

lemma uc_lift_qinv (S : SES W₀ W₁ W₂) {e : ℕ} (hK : CokerKilled S e) {y : D₂} (hy : W₂.QInv y) :
    ∃ y₁, W₁.QInv y₁ ∧ S.π.f y₁ = ((ℓ : ℤ_[ℓ]) ^ e) • y := by
  obtain ⟨n₁, hn₁, he⟩ := hK _ hy
  obtain ⟨y₁, hy₁⟩ := (uc_bij W₁ M).2 n₁
  refine ⟨y₁, ?_, ?_⟩
  · show B.Q ^ M • y₁ ∈ W₁.N
    rw [show B.Q ^ M • y₁ = n₁ from hy₁]
    exact hn₁
  · apply (uc_bij W₂ M).1
    show B.Q ^ M • S.π.f y₁ = B.Q ^ M • (((ℓ : ℤ_[ℓ]) ^ e) • y)
    rw [← map_smul, show B.Q ^ M • y₁ = n₁ from hy₁, he, ← algebraMap_smul A ((ℓ : ℤ_[ℓ]) ^ e) (B.Q ^ M • y),
      ← algebraMap_smul A ((ℓ : ℤ_[ℓ]) ^ e) y, uc_smul_comm_A]

lemma uc_pull_qinv (S : SES W₀ W₁ W₂) {y : D₁} (hy : W₁.QInv y) (h0 : S.π.f y = 0) :
    ∃ y₀, W₀.QInv y₀ ∧ S.ι.f y₀ = y := by
  obtain ⟨y₀, rfl⟩ := (S.exact y).mp h0
  refine ⟨y₀, ?_, rfl⟩
  unfold WD.QInv at *
  apply S.sat
  rw [map_smul]
  exact hy

lemma uc_pull_xn (S : SES W₀ W₁ W₂) {m : D₁} (hm : m ∈ W₁.N) (h0 : S.π.f (B.X • m) = 0) :
    ∃ m₀ ∈ W₀.N, S.ι.f (B.X • m₀) = B.X • m := by
  have h1 : S.π.f m = 0 := by
    apply W₂.X_inj
    rw [← map_smul]
    exact h0
  obtain ⟨m₀, rfl⟩ := (S.exact m).mp h1
  exact ⟨m₀, S.sat m₀ hm, map_smul _ _ _⟩

end DiagramChase₂

theorem uChase_proof : UChase := by
  intro ℓ _ A _ _ B M D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S e c hK hR hT y z hyz
  obtain ⟨⟨hy, n, hn, rfl⟩, hd⟩ := hyz
  set L : ℤ_[ℓ] := (ℓ : ℤ_[ℓ]) ^ e with hL
  obtain ⟨y₁, hy₁, hπy⟩ := uc_lift_qinv S hK hy
  obtain ⟨n₁, hn₁, hπn⟩ := hK n hn
  rw [← hL] at hπy hπn
  have hπz : S.π.f (B.X • n₁) = L • (B.X • n) := by rw [map_smul, hπn, smul_comm]
  obtain ⟨a, ha, hga⟩ := uc_gamma W₁ hy₁
  obtain ⟨hq, hph⟩ := uc_phi W₁ hn₁
  have hω : W₁.d1 y₁ (B.X • n₁) = B.X • (a - (B.Q • W₁.φ n₁ - n₁)) := by
    rw [WD.d1, hga, hph]; exact (smul_sub _ _ _).symm
  have hπω : S.π.f (W₁.d1 y₁ (B.X • n₁)) = 0 := by
    rw [uc_hom, hπy, hπz, uc_smul, hd, smul_zero]
  obtain ⟨y₀, hy₀, hιy₀⟩ : ∃ y₀, W₀.QInv y₀ ∧ S.ι.f y₀ = a - (B.Q • W₁.φ n₁ - n₁) := by
    apply uc_pull_qinv S (uc_qinv_sub W₁ ha hq)
    rw [hω, map_smul] at hπω
    exact W₂.X_inj _ hπω
  have hιω : S.ι.f (B.X • y₀) = W₁.d1 y₁ (B.X • n₁) := by rw [map_smul, hιy₀, hω]
  obtain ⟨k, y', z', ⟨⟨hy', nz, hnz, rfl⟩, hd'⟩, x, hx, hπy', hπz'⟩ :=
    hR y (B.X • n) ⟨⟨hy, n, hn, rfl⟩, hd⟩
  obtain ⟨x₁, hx₁, hπx⟩ := hK x hx
  rw [← hL] at hπx
  obtain ⟨x', hx', hγx⟩ := W₁.γ_N x₁ hx₁
  set K : ℤ_[ℓ] := (ℓ : ℤ_[ℓ]) ^ k with hKk
  set Y := K • y₁ - L • y' + (W₁.φ x₁ - x₁) with hY
  set m := K • n₁ - L • nz + x' with hm
  have hZ : K • (B.X • n₁) - L • (B.X • nz) + (W₁.γ x₁ - x₁) = B.X • m := by
    rw [hγx, hm, smul_add, smul_sub, smul_comm K, smul_comm L]
  have hmN : m ∈ W₁.N := W₁.N.add_mem (W₁.N.sub_mem (W₁.N.smul_of_tower_mem _ hn₁)
    (W₁.N.smul_of_tower_mem _ hnz)) hx'
  have hYq : W₁.QInv Y := uc_qinv_add W₁ (uc_qinv_sub W₁ (uc_qinv_smul W₁ _ hy₁)
    (uc_qinv_smul W₁ _ hy')) (uc_qinv_phi_sub W₁ hx₁)
  have hπY : S.π.f Y = 0 := by
    simp only [hY, map_add, map_sub, uc_hom_tsmul, S.π.φ_comm, hπy, hπy', hπx]
    rw [map_smul W₂.φ]
    module
  have hπZ : S.π.f (B.X • m) = 0 := by
    rw [← hZ]
    simp only [map_add, map_sub, uc_hom_tsmul, S.π.γ_comm, hπz, hπz', hπx]
    rw [map_smul W₂.γ]
    module
  obtain ⟨Y₀, hY₀, hιY⟩ := uc_pull_qinv S hYq hπY
  obtain ⟨m₀, hm₀, hιm⟩ := uc_pull_xn S hmN hπZ
  have hdYZ : W₁.d1 Y (B.X • m) = K • W₁.d1 y₁ (B.X • n₁) := by
    rw [← hZ, hY]
    unfold WD.d1 at hd' ⊢
    simp only [map_add, map_sub, map_smul]
    have hc := W₁.comm x₁
    linear_combination (norm := module) (-L) • hd' - hc
  have hcob : W₀.IsCob2 (K • (B.X • y₀)) := by
    refine ⟨Y₀, B.X • m₀, ⟨hY₀, m₀, hm₀, rfl⟩, ?_⟩
    apply S.ι_inj
    rw [uc_hom, hιY, hιm, hdYZ, uc_hom_tsmul, hιω]
  obtain ⟨y₀', z₀', ⟨hy₀', hz₀'⟩, hc⟩ := hT _ ⟨y₀, hy₀, rfl⟩ ⟨k, hcob⟩
  refine ⟨c • y₁ - S.ι.f y₀', c • (B.X • n₁) - S.ι.f z₀', ⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · exact uc_qinv_sub W₁ (uc_qinv_smul W₁ c hy₁) (uc_hom_qinv S.ι hy₀')
  · exact uc_xn_sub W₁ (uc_xn_smul W₁ c ⟨n₁, hn₁, rfl⟩) (uc_hom_xn S.ι hz₀')
  · rw [d1_sub_sub, uc_smul, ← uc_hom, ← hc, uc_hom_tsmul, hιω, sub_self]
  · rw [map_sub, uc_hom_tsmul, hπy, uc_pi_iota, sub_zero, mul_smul, smul_comm]
  · rw [map_sub, uc_hom_tsmul, hπz, uc_pi_iota, sub_zero, mul_smul, smul_comm]

lemma uc_val_factor (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) (M s : ℕ) (J : Finset ℤ) (hs : 1 ≤ s)
    (h2 : ℓ = 2 → 2 ≤ s) (hv : PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s) (hJ : 0 ∉ J) :
    ∃ ν : ℤ_[ℓ], (ℓ : ℤ_[ℓ]) ^ eU ℓ M s J =
      ((∏ j ∈ J, (1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))) *
        ∏ i ∈ Finset.Icc 1 M, ((u : ℤ_[ℓ]) ^ i - 1)) * ν := by
  obtain ⟨hM, hJJ⟩ := Formalism.WindowSums.valProd_of Formalism.WindowSums.valuation_zpow_sub_one ℓ u s hs h2 hv
  obtain ⟨h2ne, h2v⟩ := hM M
  obtain ⟨h1ne, h1v⟩ := hJJ J hJ
  set P1 := ∏ j ∈ J, (1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) with hP1
  set P2 := ∏ i ∈ Finset.Icc 1 M, (1 - (u : ℤ_[ℓ]) ^ i) with hP2
  have hcard : (Finset.Icc 1 M).card = M := by simp
  have hneg : ∏ i ∈ Finset.Icc 1 M, ((u : ℤ_[ℓ]) ^ i - 1) = (-1) ^ M * P2 := by
    have := Finset.prod_neg (s := Finset.Icc 1 M) (fun i => 1 - (u : ℤ_[ℓ]) ^ i)
    rw [hcard] at this
    rw [hP2, ← this]
    exact Finset.prod_congr rfl (fun i _ => by ring)
  have e1 := PadicInt.unitCoeff_spec h1ne
  have e2 := PadicInt.unitCoeff_spec h2ne
  set μ1 := PadicInt.unitCoeff h1ne
  set μ2 := PadicInt.unitCoeff h2ne
  have heU : eU ℓ M s J = P1.valuation + P2.valuation := by
    rw [h1v, h2v, eU, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]; ring
  refine ⟨((μ1⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * ((μ2⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * (-1) ^ M, ?_⟩
  rw [heU, hneg, pow_add]
  have hm1 : ((-1 : ℤ_[ℓ]) ^ M) * (-1) ^ M = 1 := by rw [← mul_pow]; simp
  calc (ℓ : ℤ_[ℓ]) ^ P1.valuation * (ℓ : ℤ_[ℓ]) ^ P2.valuation
      = (ℓ : ℤ_[ℓ]) ^ P1.valuation * (ℓ : ℤ_[ℓ]) ^ P2.valuation *
          (((μ1 : ℤ_[ℓ]) * ((μ1⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) * ((μ2 : ℤ_[ℓ]) * ((μ2⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) *
            (((-1 : ℤ_[ℓ]) ^ M) * (-1) ^ M)) := by rw [Units.mul_inv, Units.mul_inv, hm1]; ring
    _ = ((μ1 : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ P1.valuation) *
          ((-1) ^ M * ((μ2 : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ P2.valuation)) *
          (((μ1⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * ((μ2⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * (-1) ^ M) := by ring
    _ = P1 * ((-1) ^ M * P2) * (((μ1⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * ((μ2⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * (-1) ^ M) := by
          rw [← e1, ← e2]

theorem lemmaU_of (hC : UClaim) (hS : UChase) : LemmaU := by
  intro ℓ _ A _ _ B M D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S e s J hs h2 hv hJ h1 h3 h4 h5 hK hR
  have hT := hC ℓ A B M D₀ W₀ s J hs h2 hv hJ h1 h3 h4 h5
  have hL := hS ℓ A B M D₀ D₁ D₂ W₀ W₁ W₂ S e _ hK hR hT
  obtain ⟨ν, hν⟩ := uc_val_factor ℓ B.u M s J hs h2 hv hJ
  rw [pow_add, hν, ← mul_assoc]
  intro y z hyz
  obtain ⟨y₁, z₁, hc, hy, hz⟩ := hL y z hyz
  refine ⟨ν • y₁, ν • z₁, uc_cocycle_smul W₁ ν hc, ?_, ?_⟩
  · rw [uc_hom_tsmul, hy, smul_smul, mul_comm]
  · rw [uc_hom_tsmul, hz, smul_smul, mul_comm]

end Formalism.LIFT
