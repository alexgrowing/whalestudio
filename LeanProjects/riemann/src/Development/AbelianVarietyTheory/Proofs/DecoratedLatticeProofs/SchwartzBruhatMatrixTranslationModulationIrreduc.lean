import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNeZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixIntegersModNatFinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixIntegralOfAddCharTraceDual
open ValuativeRel GlobalTheory.SplitWeil Matrix
open scoped Topology

noncomputable section
namespace GlobalTheory.IrredSB

section Alg
variable {G : Type} [AddCommGroup G]

open Classical in

def ind (K : AddSubgroup G) (t : G) : ℂ := if t ∈ K then 1 else 0

theorem ind_add (K : AddSubgroup G) (t : G) {u : G} (hu : u ∈ K) : ind K (t + u) = ind K t := by
  unfold ind
  by_cases ht : t ∈ K
  · rw [if_pos ht, if_pos (add_mem ht hu)]
  · rw [if_neg ht, if_neg fun h => ht ((add_mem_cancel_right hu).1 h)]

theorem ind_mem {B : Type} (e : B → G → ℂ) (he : ∀ b t u, e b (t + u) = e b t * e b u)
    (W : Submodule ℂ (G → ℂ)) (hM : ∀ Φ ∈ W, ∀ b, (fun t => e b t * Φ t) ∈ W) (K : AddSubgroup G)
    (hsep : ∀ p ∉ K, ∃ b, (∀ u ∈ K, e b u = 1) ∧ e b p ≠ 1) {f : G → ℂ} (hf : f ∈ W)
    (h1 : ∀ u ∈ K, f u = 1) (P : Finset G) (hP : ∀ t, f t ≠ 0 → ∃ p ∈ P, ∃ u ∈ K, t = p + u) :
    ind K ∈ W := by
  classical
  have key : ∀ R : Finset G, ∃ Φ ∈ W, (∀ t ∈ K, Φ t = 1) ∧ (∀ t, f t = 0 → Φ t = 0) ∧
      ∀ r ∈ R, r ∉ K → ∀ u ∈ K, Φ (r + u) = 0 := by
    intro R
    induction R using Finset.induction_on with
    | empty => exact ⟨f, hf, h1, fun _ h => h, by simp⟩
    | insert r R _ ih =>
      obtain ⟨Φ, hΦ, k1, k2, k3⟩ := ih
      by_cases hr : r ∈ K
      · refine ⟨Φ, hΦ, k1, k2, fun s hs hsK u hu => ?_⟩
        rcases Finset.mem_insert.1 hs with rfl | hs
        · exact absurd hr hsK
        · exact k3 s hs hsK u hu
      · obtain ⟨b, hb1, hne⟩ := hsep r hr
        have hne' : e b r - 1 ≠ 0 := sub_ne_zero.2 hne
        refine ⟨(e b r - 1)⁻¹ • (e b r • Φ - fun t => e b t * Φ t),
          Submodule.smul_mem _ _ (sub_mem (Submodule.smul_mem _ _ hΦ) (hM Φ hΦ b)), fun t ht => ?_,
          fun t ht => ?_, fun s hs hsK u hu => ?_⟩
        · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, k1 t ht, hb1 t ht, mul_one]
          exact inv_mul_cancel₀ hne'
        · simp [k2 t ht]
        · rcases Finset.mem_insert.1 hs with rfl | hs
          · simp [he, hb1 u hu]
          · simp [k3 s hs hsK u hu]
  obtain ⟨Φ, hΦ, k1, k2, k3⟩ := key P
  convert hΦ using 1
  funext t
  by_cases ht : t ∈ K
  · simp [ind, ht, k1 t ht]
  · rw [ind, if_neg ht]
    by_cases hft : f t = 0
    · exact (k2 t hft).symm
    · obtain ⟨p, hp, u, hu, rfl⟩ := hP t hft
      exact (k3 p hp (fun hh => ht (add_mem hh hu)) u hu).symm

theorem mem_of_cosets (W : Submodule ℂ (G → ℂ)) (hT : ∀ Φ ∈ W, ∀ x, (fun t => Φ (t + x)) ∈ W)
    {K : AddSubgroup G} (hK : ind K ∈ W) (P : Finset G) :
    ∀ Φ : G → ℂ, (∀ u ∈ K, ∀ t, Φ (t + u) = Φ t) →
      (∀ t, Φ t ≠ 0 → ∃ s ∈ P, ∃ u ∈ K, t = s + u) → Φ ∈ W := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    intro Φ _ h3
    convert W.zero_mem using 1
    funext t
    by_contra ht
    simpa using h3 t ht
  | insert s P _ ih =>
    intro Φ h2 h3
    have hm := Submodule.smul_mem _ (Φ s) (hT _ hK (-s))
    have hval : ∀ t, (Φ - Φ s • fun t => ind K (t + -s)) t ≠ 0 → Φ t ≠ 0 ∧ t + -s ∉ K := by
      intro t ht
      have hn : t + -s ∉ K := fun hh => ht (by
        have := h2 _ hh s
        rw [show s + (t + -s) = t by abel] at this
        simp [ind, hh, this])
      exact ⟨by simpa [ind, hn] using ht, hn⟩
    have := ih (Φ - Φ s • fun t => ind K (t + -s)) (fun u hu t => by
      simp only [Pi.sub_apply, Pi.smul_apply, h2 u hu]
      rw [add_right_comm, ind_add K _ hu]) fun t ht => by
        obtain ⟨s', hs', u, hu, rfl⟩ := h3 t (hval t ht).1
        rcases Finset.mem_insert.1 hs' with rfl | hs'
        · exact absurd (by simpa using hu) (hval _ ht).2
        · exact ⟨s', hs', u, hu, rfl⟩
    simpa using add_mem this hm

end Alg

theorem eq_one_of_forall_pow {z : ℂ} (hz : ‖z‖ = 1) (h : ∀ k : ℕ, ‖z ^ k - 1‖ < 1) : z = 1 := by
  by_contra hne
  have hb : ∀ n : ℕ, (n : ℝ) / 2 ≤ (∑ k ∈ Finset.range n, z ^ k).re := by
    intro n
    rw [Complex.re_sum]
    have hk : ∀ k ∈ Finset.range n, (1 / 2 : ℝ) ≤ (z ^ k).re := by
      intro k _
      have h1 : ‖z ^ k‖ ^ 2 = 1 := by rw [norm_pow, hz, one_pow, one_pow]
      have h2 : ‖z ^ k - 1‖ ^ 2 < 1 := by nlinarith [h k, norm_nonneg (z ^ k - 1)]
      rw [Complex.sq_norm, Complex.normSq_apply] at h1 h2
      simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero] at h2
      nlinarith
    have := Finset.card_nsmul_le_sum _ _ _ hk
    rw [Finset.card_range, nsmul_eq_mul] at this
    linarith
  have hp : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / ‖z - 1‖)
  have h3 : (∑ k ∈ Finset.range n, z ^ k).re ≤ 1 / ‖z - 1‖ := by
    refine (Complex.re_le_norm _).trans ?_
    rw [geom_sum_eq hne, norm_div]
    exact div_le_div_of_nonneg_right (h n).le hp.le
  have h4 := hb n
  have h5 : 2 / ‖z - 1‖ = 2 * (1 / ‖z - 1‖) := by ring
  linarith

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem char_eventually_one (ψk : AddChar k Circle) (hψ : Continuous ψk) :
    ∀ᶠ x in 𝓝 (0 : k), ψk x = 1 := by
  have hc : Continuous (fun x : k => ‖(ψk x : ℂ) - 1‖) := by fun_prop
  have h1 : {x : k | ‖(ψk x : ℂ) - 1‖ < 1} ∈ 𝓝 (0 : k) :=
    (isOpen_lt hc continuous_const).mem_nhds (by simp)
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).1 h1
  have hnb : {x : k | valuation k x < γ} ∈ 𝓝 (0 : k) :=
    (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨γ, subset_rfl⟩
  filter_upwards [hnb] with x hx
  have hx' : x ∈ (valuation k).ltAddSubgroup γ := hx
  refine Circle.ext (eq_one_of_forall_pow (Circle.norm_coe _) fun m => ?_)
  have hm : valuation k (m • x) < γ := (nsmul_mem hx' m : m • x ∈ (valuation k).ltAddSubgroup γ)
  have := hγ hm
  simpa [AddChar.map_nsmul_eq_pow, -nsmul_eq_mul] using this

theorem char_isLocallyConstant (ψk : AddChar k Circle) (hψ : Continuous ψk) : IsLocallyConstant ψk := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have ht : Filter.Tendsto (fun y : k => y - x) (𝓝 x) (𝓝 0) := by
    have : Continuous (fun y : k => y - x) := by fun_prop
    simpa using this.tendsto x
  filter_upwards [ht.eventually (char_eventually_one ψk hψ)] with y hy
  have : ψk y = ψk x * ψk (y - x) := by rw [← AddChar.map_add_eq_mul, add_sub_cancel]
  rw [this, hy, mul_one]

theorem exists_sep (ψk : AddChar k Circle) (hψ : Continuous ψk) (h1 : ψk ≠ 1) {x : k} (hx : x ∉ 𝒪[k]) :
    ∃ b : k, (∀ u ∈ 𝒪[k], ψk (b * u) = 1) ∧ ψk (b * x) ≠ 1 := by
  by_contra h
  push Not at h
  exact hx (GlobalTheory.CharDualMat.mem_integer_of_dual ψk hψ h1 x h)

variable {Y Y' : Type} [Fintype Y] [Fintype Y']

def pair (b t : Matrix Y Y' k) : k := ∑ r, ∑ q, b r q * t r q

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem pair_add_right (b t u : Matrix Y Y' k) : pair b (t + u) = pair b t + pair b u := by
  simp [pair, mul_add, Finset.sum_add_distrib]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem pair_single [DecidableEq Y] [DecidableEq Y'] (r : Y) (q : Y') (c : k) (t : Matrix Y Y' k) :
    pair (Matrix.single r q c) t = c * t r q := by
  unfold pair
  rw [Finset.sum_eq_single r, Finset.sum_eq_single q]
  · simp
  · intro q' _ h
    simp [Matrix.single, h.symm]
  · simp
  · intro r' _ h
    simp [Matrix.single, h.symm]
  · simp

variable (k Y Y') in

def intMat : AddSubgroup (Matrix Y Y' k) where
  carrier := {u | ∀ r q, u r q ∈ 𝒪[k]}
  add_mem' ha hb r q := add_mem (ha r q) (hb r q)
  zero_mem' _ _ := zero_mem _
  neg_mem' ha r q := neg_mem (ha r q)

variable (k Y Y') in

def lat (n : ℕ) : AddSubgroup (Matrix Y Y' k) := (intMat k Y Y').map (nsmulAddMonoidHom n)

theorem sep [CharZero k] (ψk : AddChar k Circle) (hψ : Continuous ψk) (h1 : ψk ≠ 1) {n : ℕ} (hn : 0 < n)
    (p : Matrix Y Y' k) (hp : p ∉ lat k Y Y' n) :
    ∃ b, (∀ u ∈ lat k Y Y' n, (ψk (pair b u) : ℂ) = 1) ∧ (ψk (pair b p) : ℂ) ≠ 1 := by
  classical
  have hn' : (n : k) ≠ 0 := by exact_mod_cast hn.ne'
  have : ¬ ∀ r q, (n : k)⁻¹ * p r q ∈ 𝒪[k] := fun h => hp ⟨(n : k)⁻¹ • p, h, by
    show n • (n : k)⁻¹ • p = p
    rw [← Nat.cast_smul_eq_nsmul k, smul_smul, mul_inv_cancel₀ hn', one_smul]⟩
  push Not at this
  obtain ⟨r, q, hrq⟩ := this
  obtain ⟨b, hb, hb'⟩ := exists_sep ψk hψ h1 hrq
  refine ⟨Matrix.single r q (b * (n : k)⁻¹), ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    rw [pair_single]
    have : b * (n : k)⁻¹ * (nsmulAddMonoidHom n u : Matrix Y Y' k) r q = b * u r q := by
      show b * (n : k)⁻¹ * (n • u r q) = b * u r q
      rw [nsmul_eq_mul]
      field_simp
    rw [this, hb _ (hu r q)]
    rfl
  · rw [pair_single, mul_assoc]
    exact fun h => hb' (Circle.ext h)

theorem cover [CharZero k] {a N : ℕ} (ha : 0 < a) (hN : 0 < N) :
    ∃ P : Finset (Matrix Y Y' k), ∀ t : Matrix Y Y' k, (∀ r q, (a • t) r q ∈ 𝒪[k]) →
      ∃ p ∈ P, ∃ u ∈ lat k Y Y' N, t = p + u := by
  classical
  obtain ⟨R, hR, hRc⟩ := GlobalTheory.matrix_integers_mod_nat_finite k Y Y' (a * N) (Nat.mul_pos ha hN)
  refine ⟨(hR.image fun s => ((a : k)⁻¹) • s).toFinset, fun t ht => ?_⟩
  obtain ⟨s, hs, u, hu, he⟩ := hRc _ ht
  have ha' : (a : k) ≠ 0 := by exact_mod_cast ha.ne'
  have hinv : ∀ v : Matrix Y Y' k, (a : k)⁻¹ • (a • v) = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ ha', one_smul]
  refine ⟨(a : k)⁻¹ • s, (Set.Finite.mem_toFinset _).2 ⟨s, hs, rfl⟩, N • u, ⟨u, hu, rfl⟩, ?_⟩
  rw [← hinv t, he, smul_add, mul_smul, hinv]

omit [Fintype Y] [Fintype Y'] in
theorem trans_mem_SB {Φ : Matrix Y Y' k → ℂ} (hΦ : Φ ∈ SB (Matrix Y Y' k)) (x : Matrix Y Y' k) :
    (fun t => Φ (t + x)) ∈ SB (Matrix Y Y' k) :=
  ⟨hΦ.1.comp_continuous (f := fun t => t + x) (by fun_prop), hΦ.2.comp_homeomorph (Homeomorph.addRight x)⟩

theorem modul_mem_SB (ψk : AddChar k Circle) (hψ : Continuous ψk) {Φ : Matrix Y Y' k → ℂ}
    (hΦ : Φ ∈ SB (Matrix Y Y' k)) (b : Matrix Y Y' k) :
    (fun t => (ψk (pair b t) : ℂ) * Φ t) ∈ SB (Matrix Y Y' k) := by
  have hp : Continuous (fun t : Matrix Y Y' k => pair b t) :=
    continuous_finset_sum _ fun r _ => continuous_finset_sum _ fun q _ =>
      continuous_const.mul (continuous_id.matrix_elem r q)
  have hl : IsLocallyConstant (fun t => (ψk (pair b t) : ℂ)) :=
    ((char_isLocallyConstant ψk hψ).comp_continuous hp).comp (fun z : Circle => (z : ℂ))
  exact ⟨hl.mul hΦ.1, HasCompactSupport.mul_left (f := fun t => (ψk (pair b t) : ℂ)) hΦ.2⟩

end GlobalTheory.IrredSB

namespace GlobalTheory.IrredSB

theorem sb_irreducible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (ψk : AddChar k Circle), Continuous ψk → ψk ≠ 1 → ∀ W : Submodule ℂ (Matrix Y Y' k → ℂ), W ≤ SB (Matrix Y Y' k) → (∀ Φ ∈ W, ∀ x : Matrix Y Y' k, (fun t => Φ (t + x)) ∈ SB (Matrix Y Y' k) → (fun t => Φ (t + x)) ∈ W) → (∀ Φ ∈ W, ∀ b : Matrix Y Y' k, (fun t => (ψk (∑ r, ∑ q, b r q * t r q) : ℂ) * Φ t) ∈ SB (Matrix Y Y' k) → (fun t => (ψk (∑ r, ∑ q, b r q * t r q) : ℂ) * Φ t) ∈ W) → ∀ Φ₀ ∈ W, Φ₀ ≠ 0 → W = SB (Matrix Y Y' k) := by
  intro k _ _ _ _ _ Y Y' _ _ _ _ ψk hψ hψ1 W hW hTc hMc Φ₀ h0 hne
  have hT : ∀ Φ ∈ W, ∀ x, (fun t => Φ (t + x)) ∈ W := fun Φ h x => hTc Φ h x (trans_mem_SB (hW h) x)
  have hM : ∀ Φ ∈ W, ∀ b, (fun t => (ψk (pair b t) : ℂ) * Φ t) ∈ W :=
    fun Φ h b => hMc Φ h b (modul_mem_SB ψk hψ (hW h) b)
  have he : ∀ b t u : Matrix Y Y' k, (ψk (pair b (t + u)) : ℂ) = (ψk (pair b t) : ℂ) * ψk (pair b u) :=
    fun b t u => by rw [pair_add_right, AddChar.map_add_eq_mul, Circle.coe_mul]
  refine le_antisymm hW fun Φ hΦ => ?_
  obtain ⟨a, ha⟩ : ∃ a, Φ₀ a ≠ 0 := Function.ne_iff.1 hne
  have hf : ((Φ₀ a)⁻¹ • fun t => Φ₀ (t + a)) ∈ W := W.smul_mem _ (hT _ h0 a)
  have hf0 : ((Φ₀ a)⁻¹ • fun t => Φ₀ (t + a)) 0 = 1 := by simp [ha]
  generalize ((Φ₀ a)⁻¹ • fun t => Φ₀ (t + a)) = f at hf hf0
  obtain ⟨n, hn, hinv, hsupp⟩ := GlobalTheory.SBUnif.sb_lattice_bounds k Y Y' f (hW hf)
  obtain ⟨m, hm, hinv', hsupp'⟩ := GlobalTheory.SBUnif.sb_lattice_bounds k Y Y' Φ hΦ
  have hnm : 0 < n * m := Nat.mul_pos hn hm
  have hn1 : ind (lat k Y Y' n) ∈ W := by
    obtain ⟨P, hP⟩ := cover (k := k) (Y := Y) (Y' := Y') hn hn
    refine ind_mem (fun b t => (ψk (pair b t) : ℂ)) he W hM _ (sep ψk hψ hψ1 hn) hf ?_ P
      fun t ht => hP t (hsupp t ht)
    rintro _ ⟨u, hu, rfl⟩
    have := hinv u hu 0
    rw [zero_add, hf0] at this
    exact this
  have hn2 : ind (lat k Y Y' (n * m)) ∈ W := by
    obtain ⟨P, hP⟩ := cover (k := k) (Y := Y) (Y' := Y') one_pos hnm
    refine ind_mem (fun b t => (ψk (pair b t) : ℂ)) he W hM _ (sep ψk hψ hψ1 hnm) hn1 ?_ P
      fun t ht => hP t ?_
    · rintro _ ⟨u, hu, rfl⟩
      have : nsmulAddMonoidHom (n * m) u ∈ lat k Y Y' n :=
        ⟨m • u, nsmul_mem hu m, (mul_smul n m u).symm⟩
      rw [ind, if_pos this]
    · have : t ∈ lat k Y Y' n := by
        by_contra h
        exact ht (by rw [ind, if_neg h])
      obtain ⟨u, hu, rfl⟩ := this
      rw [one_smul]
      exact (nsmul_mem hu n : n • u ∈ intMat k Y Y')
  obtain ⟨P, hP⟩ := cover (k := k) (Y := Y) (Y' := Y') hm hnm
  refine mem_of_cosets W hT hn2 P Φ ?_ fun t ht => hP t (hsupp' t ht)
  rintro _ ⟨u, hu, rfl⟩ t
  have := hinv' (n • u) (nsmul_mem hu n : n • u ∈ intMat k Y Y') t
  rw [← mul_smul, mul_comm] at this
  exact this

end GlobalTheory.IrredSB
