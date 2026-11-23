import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudDefs
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ResidueClassCountOfTensorBasisInclusion

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems Formalism.GradedWeylDivisibility

section Formal2

variable {O Kf V₁ V₂ V : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V₁] [Module Kf V₁] [Module O V₁]
  [IsScalarTower O Kf V₁] [AddCommGroup V₂] [Module Kf V₂] [Module O V₂] [IsScalarTower O Kf V₂] [AddCommGroup V]
  [Module Kf V] [Module O V] [IsScalarTower O Kf V]

theorem cc_mem_scale {c : Kf} (hc : c ≠ 0) {M : Submodule O V} {x : V} : x ∈ scale c M ↔ c⁻¹ • x ∈ M := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    show c⁻¹ • (c • y) ∈ M
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul]
  · intro h
    refine ⟨c⁻¹ • x, h, ?_⟩
    show c • (c⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem cc_one {M : Submodule O V} {x : V} (h : x ∈ M) : x ∈ scale (1 : Kf) M := ⟨x, h, one_smul Kf x⟩

theorem cc_bil (μ : V₁ →ₗ[Kf] V₂ →ₗ[Kf] V) {M₁ : Submodule O V₁} {M₂ : Submodule O V₂} {M : Submodule O V}
    (hμ : ∀ F ∈ M₁, ∀ z ∈ M₂, μ F z ∈ M) {a b : Kf} {F : V₁} {z : V₂} (hF : F ∈ scale a M₁)
    (hz : z ∈ scale b M₂) : μ F z ∈ scale (a * b) M := by
  obtain ⟨F₀, hF₀, rfl⟩ := hF
  obtain ⟨z₀, hz₀, rfl⟩ := hz
  refine ⟨μ F₀ z₀, hμ F₀ hF₀ z₀ hz₀, ?_⟩
  show (a * b) • μ F₀ z₀ = μ (a • F₀) (b • z₀)
  rw [map_smul, map_smul, LinearMap.smul_apply, smul_smul, mul_comm b a]

theorem cc_dual (T : V₁ →ₗ[Kf] V) {M₁ : Submodule O V₁} {M : Submodule O V} {a b c : Kf} (hb : b ≠ 0)
    (hT : ∀ v ∈ M₁, T v ∈ scale b M) {φ : Module.Dual Kf V} (hφ : φ ∈ scale a (dualLat O Kf M)) :
    c • (φ ∘ₗ T) ∈ scale (c * a * b) (dualLat O Kf M₁) := by
  obtain ⟨φ₀, hφ₀, rfl⟩ := hφ
  refine ⟨b⁻¹ • (φ₀ ∘ₗ T), ?_, ?_⟩
  · intro v hv
    obtain ⟨u, hu, hu'⟩ := hT v hv
    obtain ⟨r, hr⟩ := hφ₀ u hu
    refine ⟨r, ?_⟩
    have h1 : T v = b • u := hu'.symm
    rw [hr, LinearMap.smul_apply, LinearMap.comp_apply, h1, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hb, one_mul]
  · show (c * a * b) • (b⁻¹ • (φ₀ ∘ₗ T)) = c • ((a • φ₀) ∘ₗ T)
    ext v
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]
    field_simp

end Formal2

theorem cc_Ar_add {n' m : ℕ} (X Y : Fin n' → Fin (m + 1) → ℤ) : Ar 1 (X + Y) = Ar 1 X + Ar 1 Y := by
  unfold Ar
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold lamAt
  split_ifs
  · rfl
  · simp only [Pi.add_apply]
    ring

theorem cc_Ar_of {n' m : ℕ} (TT : Finset (Fin n')) (X : Fin n' → Fin (m + 1) → ℤ) (c : ℤ)
    (h : ∀ s ∈ TT, X s 0 = c ∧ X s (Fin.last m) = -c) (h0 : ∀ s, s ∉ TT → X s = 0) :
    Ar 1 X = TT.card * c ∧ Elast X = -(TT.card * c) := by
  classical
  have key : ∀ s, lamAt X s 0 = (if s ∈ TT then c else 0) ∧ lamAt X s (Fin.last m) = if s ∈ TT then -c else 0 := by
    intro s
    unfold lamAt
    by_cases hs : s ∈ TT
    · obtain ⟨h1, h2⟩ := h s hs
      simp only [hs, if_true]
      split_ifs
      · exact ⟨h1, h2⟩
      · simp only [Fin.rev_zero, Fin.rev_last]
        rw [h1, h2]
        simp
    · have := h0 s hs
      simp only [hs, if_false]
      split_ifs <;> simp [this]
  constructor
  · unfold Ar
    simp_rw [filter_lt_one, Finset.sum_singleton, (key _).1]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  · unfold Elast
    simp_rw [(key _).2]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    ring

theorem cc_flat_zero {n' : ℕ} (m : ℕ) {TT : Finset (Fin n')} (al be : TT → ℕ) (s : Fin n') (hs : s ∈ TT) :
    flatW m al be s 0 = al ⟨s, hs⟩ := by
  simp [flatW, hs]

theorem cc_flat_last {n' : ℕ} (m : ℕ) {TT : Finset (Fin n')} (al be : TT → ℕ) (s : Fin n') (hs : s ∈ TT) :
    flatW (m + 1) al be s (Fin.last (m + 1)) = -(be ⟨s, hs⟩ : ℤ) := by
  simp [flatW, hs]

theorem cc_flat_mid {n' : ℕ} (m : ℕ) {TT : Finset (Fin n')} (al be : TT → ℕ) (s : Fin n') (i : Fin (m + 1))
    (h0 : i ≠ 0) (h1 : i ≠ Fin.last m) : flatW m al be s i = 0 := by
  unfold flatW
  split_ifs <;> rfl

theorem cc_flat_off {n' : ℕ} (m : ℕ) {TT : Finset (Fin n')} (al be : TT → ℕ) (s : Fin n') (hs : s ∉ TT) :
    flatW m al be s = 0 := by
  funext i
  simp [flatW, hs]

theorem cc_flat_add {n' : ℕ} (m : ℕ) {TT : Finset (Fin n')} (al be al' be' : TT → ℕ) :
    flatW m (fun s => al s + al' s) (fun s => be s + be' s) = flatW m al be + flatW m al' be' := by
  funext s i
  simp only [Pi.add_apply]
  unfold flatW
  split_ifs
  · push_cast; ring
  · push_cast; ring
  · simp
  · simp

theorem cc_dualWt_anti {m : ℕ} (mu : Fin (m + 1) → ℤ) (h : Antitone mu) : Antitone (dualWt mu) := by
  intro i j hij
  unfold dualWt
  have : j.rev ≤ i.rev := Fin.rev_le_rev.2 hij
  have := h this
  linarith

theorem cc_lo {n' mm : ℕ} (TT : Finset (Fin n')) (ccl : ℕ) (aw bw : Fin n' → ℤ)
    (lam0 : Fin n' → Fin (mm + 1 + 1) → ℤ) (A B : TT → ℕ) (hBase : IsBaseWeight TT aw bw ccl lam0)
    (hzero : ∀ s, s ∉ TT → lam0 s = 0) (hAB : ∀ s : TT, (A s : ℤ) = aw s - ccl ∧ (B s : ℤ) = bw s - ccl) :
    (∀ s ∈ TT, (lam0 - flatW (mm + 1) A B) s 0 = ccl ∧ (lam0 - flatW (mm + 1) A B) s (Fin.last (mm + 1)) = -(ccl : ℤ)) ∧
    (∀ s, s ∉ TT → (lam0 - flatW (mm + 1) A B) s = 0) := by
  constructor
  · intro s hs
    obtain ⟨h1, h2, -⟩ := (hBase s).1 hs
    obtain ⟨h3, h4⟩ := hAB ⟨s, hs⟩
    simp only [Pi.sub_apply]
    rw [cc_flat_zero _ _ _ s hs, cc_flat_last _ _ _ s hs, h1, h2, h3, h4]
    constructor <;> ring
  · intro s hs
    show lam0 s - flatW (mm + 1) A B s = 0
    rw [hzero s hs, cc_flat_off _ _ _ s hs, sub_zero]

theorem cc_lo_dom {n' mm : ℕ} (TT : Finset (Fin n')) (ccl : ℕ) (aw bw : Fin n' → ℤ)
    (lam0 : Fin n' → Fin (mm + 1 + 1) → ℤ) (A B : TT → ℕ) (hBase : IsBaseWeight TT aw bw ccl lam0)
    (hDom : IsDominant lam0) (hzero : ∀ s, s ∉ TT → lam0 s = 0)
    (hAB : ∀ s : TT, (A s : ℤ) = aw s - ccl ∧ (B s : ℤ) = bw s - ccl) :
    IsDominant (lam0 - flatW (mm + 1) A B) := by
  obtain ⟨hl1, hl2⟩ := cc_lo TT ccl aw bw lam0 A B hBase hzero hAB
  intro s
  by_cases hs : s ∈ TT
  · obtain ⟨h0, h1⟩ := hl1 s hs
    have hmid : ∀ i : Fin (mm + 1 + 1), i ≠ 0 → i ≠ Fin.last (mm + 1) →
        (lam0 - flatW (mm + 1) A B) s i = lam0 s i ∧ |lam0 s i| ≤ ccl := by
      intro i hi0 hi1
      refine ⟨?_, ?_⟩
      · simp only [Pi.sub_apply]
        rw [cc_flat_mid _ _ _ s i hi0 hi1, sub_zero]
      · refine ((hBase s).1 hs).2.2 i (Nat.pos_of_ne_zero fun h => hi0 (Fin.ext h)) ?_
        have h2 : i.val ≠ mm + 1 := fun h => hi1 (Fin.ext h)
        have := i.isLt
        omega
    have hbd : ∀ i, -(ccl : ℤ) ≤ (lam0 - flatW (mm + 1) A B) s i ∧ (lam0 - flatW (mm + 1) A B) s i ≤ ccl := by
      intro i
      by_cases hi0 : i = 0
      · rw [hi0, h0]; constructor <;> omega
      by_cases hi1 : i = Fin.last (mm + 1)
      · rw [hi1, h1]; constructor <;> omega
      obtain ⟨e1, e2⟩ := hmid i hi0 hi1
      rw [e1]
      exact abs_le.1 e2
    intro i j hij
    by_cases hi0 : i = 0
    · rw [hi0, h0]; exact (hbd j).2
    by_cases hj1 : j = Fin.last (mm + 1)
    · rw [hj1, h1]; exact (hbd i).1
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hi0 (Fin.le_zero_iff.1 hij)
    have hi1 : i ≠ Fin.last (mm + 1) := by
      rintro rfl
      exact hj1 (le_antisymm (Fin.le_last j) hij)
    rw [(hmid i hi0 hi1).1, (hmid j hj0 hj1).1]
    exact hDom s hij
  · rw [hl2 s hs]
    exact fun _ _ _ => le_rfl

theorem cc_dualW {n' m : ℕ} (TT : Finset (Fin n')) (X : Fin n' → Fin (m + 1) → ℤ) (c : ℤ)
    (h : ∀ s ∈ TT, X s 0 = c ∧ X s (Fin.last m) = -c) (h0 : ∀ s, s ∉ TT → X s = 0) :
    (∀ s ∈ TT, dualW X s 0 = c ∧ dualW X s (Fin.last m) = -c) ∧ (∀ s, s ∉ TT → dualW X s = 0) := by
  constructor
  · intro s hs
    obtain ⟨h1, h2⟩ := h s hs
    unfold dualW dualWt
    rw [Fin.rev_zero, Fin.rev_last, h1, h2]
    simp
  · intro s hs
    funext i
    unfold dualW dualWt
    rw [h0 s hs]
    simp

theorem cc_D_one {K : Type*} [Field K] (k : ℕ) : lb_D k 1 (1 : K) = 1 := by
  unfold lb_D
  have : (fun a : Fin k => if a.val < 1 then ((1 : K))⁻¹ else 1) = fun _ => 1 := by
    funext a
    split_ifs <;> simp
  rw [this, Matrix.diagonal_one]

theorem cc_D_mul {K : Type*} [Field K] (k : ℕ) (c : K) : lb_D k 1 c * lb_D k 1 c = lb_D k 1 (c * c) := by
  unfold lb_D
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  split_ifs
  · rw [mul_inv]
  · rw [mul_one]

section RSC

variable {p n' : ℕ} (R : RS p n') {m : ℕ}

theorem cc_edge (e : Edge R.W R.Qq (m + 1)) (he : IsEdge p n' 1 e) :
    ∃ G : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf, (∀ s, IsUnit (G s).det) ∧
      (fun s : Fin n' => extO R.O R.ι R.σ s.val e.src) = famD R.O G 1 ∧
      (fun s : Fin n' => LeAt p R.ι R.σ R.w s.val e) = famD R.O G (algebraMap R.O R.Kf R.w) ∧
      (fun s : Fin n' => extO R.O R.ι R.σ s.val e.tgt) =
        famD R.O G (algebraMap R.O R.Kf R.w * algebraMap R.O R.Kf R.w) := by
  obtain ⟨gs, hg, h1, h2, h3⟩ := edgeLat_RS R e he
  refine ⟨fun s => gs s.val, fun s => hg _, ?_, ?_, ?_⟩
  · funext s
    unfold famD
    rw [cc_D_one, mul_one, h1]
  · funext s
    unfold famD
    rw [h2]
  · funext s
    unfold famD
    rw [h3, Matrix.mul_assoc, cc_D_mul]

theorem cc_famD_lat (G : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf) (hG : ∀ s, IsUnit (G s).det) (c : R.Kf)
    (hc : c ≠ 0) (s : Fin n') : IsLattice R.O (famD R.O G c s) := by
  refine ⟨_, ?_, rfl⟩
  rw [Matrix.det_mul]
  exact (hG s).mul (lb_D_det _ _ _ hc)

theorem cc_latE (e : Edge R.W R.Qq (m + 1)) (he : IsEdge p n' 1 e) :
    (∀ s : Fin n', IsLattice R.O (extO R.O R.ι R.σ s.val e.src)) ∧
    (∀ s : Fin n', IsLattice R.O (LeAt p R.ι R.σ R.w s.val e)) ∧
    (∀ s : Fin n', IsLattice R.O (extO R.O R.ι R.σ s.val e.tgt)) := by
  obtain ⟨G, hG, h1, h2, h3⟩ := cc_edge R e he
  have hw := R.w_ne
  refine ⟨fun s => ?_, fun s => ?_, fun s => ?_⟩
  · have := congrFun h1 s
    beta_reduce at this
    rw [this]
    exact cc_famD_lat R G hG 1 one_ne_zero s
  · have := congrFun h2 s
    beta_reduce at this
    rw [this]
    exact cc_famD_lat R G hG _ hw s
  · have := congrFun h3 s
    beta_reduce at this
    rw [this]
    exact cc_famD_lat R G hG _ (mul_ne_zero hw hw) s

variable {X₁ X₂ X : Fin n' → Fin (m + 1) → ℤ}

def IntB (μ : Vsp R.Kf X₁ →ₗ[R.Kf] Vsp R.Kf X₂ →ₗ[R.Kf] Vsp R.Kf X) : Prop :=
  ∀ M : Fin n' → Submodule R.O (Fin (m + 1) → R.Kf), (∀ s, IsLattice R.O (M s)) →
    ∀ F ∈ toV X₁ (Hten R.O X₁ M), ∀ z ∈ toV X₂ (Hten R.O X₂ M), μ F z ∈ toV X (Hten R.O X M)

variable {R}

theorem cc_Re {μ : Vsp R.Kf X₁ →ₗ[R.Kf] Vsp R.Kf X₂ →ₗ[R.Kf] Vsp R.Kf X} (hμ : IntB R μ)
    (hA : Ar 1 X = Ar 1 X₁ + Ar 1 X₂) (e : Edge R.W R.Qq (m + 1)) (he : IsEdge p n' 1 e) :
    ∀ F ∈ Re p R.ι R.σ R.w 1 X₁ e, ∀ z ∈ Re p R.ι R.σ R.w 1 X₂ e, μ F z ∈ Re p R.ι R.σ R.w 1 X e := by
  intro F hF z hz
  have h := cc_bil μ (hμ _ (cc_latE R e he).2.1) hF hz
  rw [← zpow_add₀ R.w_ne, show -Ar 1 X₁ + -Ar 1 X₂ = -Ar 1 X by rw [hA]; ring] at h
  exact h

theorem cc_CCL (hIncl : DualHeightInclusion) {μ : Vsp R.Kf X₁ →ₗ[R.Kf] Vsp R.Kf X₂ →ₗ[R.Kf] Vsp R.Kf X} (hμ : IntB R μ)
    (hA : Ar 1 X = Ar 1 X₁ + Ar 1 X₂) (hdom : IsDominant X₂) (e : Edge R.W R.Qq (m + 1)) (he : IsEdge p n' 1 e)
    (x : Vsp R.Kf X₂) (hx1 : x ∈ HL (O := R.O) R.ι R.σ X₂ e.src) (hx2 : x ∈ Re p R.ι R.σ R.w 1 X₂ e) (t c : ℕ) :
    ∀ F ∈ CCL R X₁ t c e, μ F x ∈ CCL R X t c e := by
  intro F hF
  obtain ⟨⟨h1, h2⟩, h3⟩ := hF
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have h := cc_bil μ (hμ _ (cc_latE R e he).1) h1 (cc_one hx1)
    rw [mul_one] at h
    exact h
  · exact cc_Re hμ hA e he F h2 x hx2
  · refine SetLike.mem_coe.2 ((Submodule.mem_iInf _).2 fun e' => (Submodule.mem_iInf _).2 fun hc => ?_)
    have h4 := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (SetLike.mem_coe.1 h3) e') hc
    have hx3 : x ∈ Re p R.ι R.σ R.w 1 X₂ e' := by
      refine (hIncl p n' R.W R.Qq R.O R.Kf R.ι R.σ R.jO R.w R.std.1 m 1 X₂ hdom e' hc.1).1 ?_
      rw [hc.2.1]
      exact hx1
    have h := cc_bil μ (cc_Re hμ hA e' hc.1) h4 (cc_one hx3)
    rw [mul_one] at h
    exact h

theorem cc_tgt_le (hdom : IsDominant X₂) (hE : Elast X₂ = -Ar 1 X₂) (e : Edge R.W R.Qq (m + 1))
    (he : IsEdge p n' 1 e) : HL (O := R.O) R.ι R.σ X₂ e.tgt ≤ Re p R.ι R.σ R.w 1 X₂ e := by
  intro y hy
  have h := (steps_rev R X₂ hdom e he).2 _ hy
  rw [hE, neg_neg] at h
  refine (cc_mem_scale (zpow_ne_zero _ R.w_ne)).2 ?_
  rw [zpow_neg, inv_inv]
  exact h

theorem cc_CCL' {abelian₂ : Vsp R.Kf X₁ →ₗ[R.Kf] Vsp R.Kf X₂ →ₗ[R.Kf] Vsp R.Kf X} (hμ : IntB R abelian₂)
    (hA : Ar 1 X = Ar 1 X₁ + Ar 1 X₂) (hdom : IsDominant X₂) (hE : Elast X₂ = -Ar 1 X₂) (d : ℕ)
    (hd : Ar 1 X₂ = d) (e : Edge R.W R.Qq (m + 1)) (he : IsEdge p n' 1 e) (y : Vsp R.Kf X₂)
    (hy1 : ((algebraMap R.O R.Kf R.w * algebraMap R.O R.Kf R.w) ^ Ar 1 X₂) • y ∈ HL (O := R.O) R.ι R.σ X₂ e.tgt)
    (hy2 : y ∈ Re p R.ι R.σ R.w 1 X₂ e) (t c₂ : ℕ) (hc : 2 * d ≤ c₂) :
    ∀ g ∈ CCL' R X t c₂ e, ((p : R.Kf) ^ (Ar 1 X - Ar 1 X₁)) • (g ∘ₗ abelian₂.flip y) ∈ CCL' R X₁ t (c₂ - 2 * d) e := by
  intro g hg
  obtain ⟨⟨h1, h2⟩, h3⟩ := hg
  set ω : R.Kf := algebraMap R.O R.Kf R.w with hω
  have hw : ω ≠ 0 := R.w_ne
  have hsub : Ar 1 X - Ar 1 X₁ = d := by rw [hA, hd]; ring
  rw [hsub, R.p_zpow, ← hω]
  have hww : (ω * ω) ^ Ar 1 X₂ = ω ^ (2 * (d : ℤ)) := by
    rw [hd, ← pow_two, ← zpow_natCast ω 2, ← zpow_mul]
    norm_num
  rw [hww] at hy1
  have hy1' : y ∈ scale (ω ^ (-(2 * (d : ℤ)))) (HL (O := R.O) R.ι R.σ X₂ e.tgt) := by
    refine (cc_mem_scale (zpow_ne_zero _ hw)).2 ?_
    rw [zpow_neg, inv_inv]
    exact hy1
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hT : ∀ v ∈ HL (O := R.O) R.ι R.σ X₁ e.tgt,
        abelian₂.flip y v ∈ scale (1 * ω ^ (-(2 * (d : ℤ)))) (HL (O := R.O) R.ι R.σ X e.tgt) := fun v hv =>
      cc_bil abelian₂ (hμ _ (cc_latE R e he).2.2) (cc_one hv) hy1'
    have h := cc_dual (c := ω ^ (2 * (d : ℤ))) (abelian₂.flip y) (mul_ne_zero one_ne_zero (zpow_ne_zero _ hw)) hT h1
    rw [one_mul, ← zpow_add₀ hw, ← zpow_add₀ hw,
      show 2 * (d : ℤ) + -(t : ℤ) + -(2 * (d : ℤ)) = -(t : ℤ) by ring] at h
    exact h
  · have hT : ∀ v ∈ HLe p R.ι R.σ R.w X₁ e,
        abelian₂.flip y v ∈ scale (1 * ω ^ (-Ar 1 X₂)) (HLe p R.ι R.σ R.w X e) := fun v hv =>
      cc_bil abelian₂ (hμ _ (cc_latE R e he).2.1) (cc_one hv) hy2
    have h := cc_dual (c := ω ^ (2 * (d : ℤ))) (abelian₂.flip y) (mul_ne_zero one_ne_zero (zpow_ne_zero _ hw)) hT h2
    rw [one_mul, ← zpow_add₀ hw, ← zpow_add₀ hw,
      show 2 * (d : ℤ) + -Ar 1 X + -Ar 1 X₂ = -Ar 1 X₁ by rw [hA, hd]; ring] at h
    exact h
  · refine SetLike.mem_coe.2 ((Submodule.mem_iInf _).2 fun e' => (Submodule.mem_iInf _).2 fun hc' => ?_)
    have h4 := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (SetLike.mem_coe.1 h3) e') hc'
    have h5 := scale_scale_mem h4
    have hy3 : y ∈ scale (ω ^ (-(2 * (d : ℤ))) * ω ^ (-Ar 1 X₂)) (HLe p R.ι R.σ R.w X₂ e') := by
      apply scale_scale_mem
      refine scale_mono _ (cc_tgt_le hdom hE e' hc'.1) ?_
      rw [hc'.2.1]
      exact hy1'
    have hT : ∀ v ∈ HLe p R.ι R.σ R.w X₁ e',
        abelian₂.flip y v ∈ scale (1 * (ω ^ (-(2 * (d : ℤ))) * ω ^ (-Ar 1 X₂))) (HLe p R.ι R.σ R.w X e') := fun v hv =>
      cc_bil abelian₂ (hμ _ (cc_latE R e' hc'.1).2.1) (cc_one hv) hy3
    have h := cc_dual (c := ω ^ (2 * (d : ℤ))) (abelian₂.flip y)
      (mul_ne_zero one_ne_zero (mul_ne_zero (zpow_ne_zero _ hw) (zpow_ne_zero _ hw))) hT h5
    apply mem_scale_scale
    rw [one_mul, ← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_add₀ hw] at h
    rw [← zpow_add₀ hw]
    have e1 : 2 * (d : ℤ) + ((c₂ : ℤ) + -Ar 1 X) + (-(2 * (d : ℤ)) + -Ar 1 X₂) =
        ((c₂ - 2 * d : ℕ) : ℤ) + -Ar 1 X₁ := by
      rw [hA, hd, Nat.cast_sub hc]
      push_cast
      ring
    rw [e1] at h
    exact h

end RSC

end Formalism.MainNotions.flipOneThree.Pf

end
