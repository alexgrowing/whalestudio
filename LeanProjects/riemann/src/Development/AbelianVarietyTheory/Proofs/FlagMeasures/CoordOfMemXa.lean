import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegVol.RealMat

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {k r : ℕ} {σ : K →+* ℂ} {Φ : V → Fin (2 * r + k + 1) → ℂ}

theorem herm_eI (u : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : herm (Hpk k r) u (bvec (eI k r a)) = u (esI k r a) := by
  have ha := a.2
  have ht : WeylGroupFacts.tau k r (eI k r a) = esI k r a := by
    apply Fin.ext; exact if_pos (Or.inl ha)
  have hs : WeylGroupFacts.sgn k r (eI k r a) = 1 := by
    exact if_neg (by show ¬ a.val = r + k; omega)
  unfold herm bvec
  rw [← Pi.single_star, star_one, single_one_dotProduct]
  simp only [mulVec, dotProduct, WeylGroupFacts.hpk_row, ht, hs]
  simp

theorem herm_add_left (M : Mat k r) (u v w : Fin (2 * r + k + 1) → ℂ) : herm M (u + v) w = herm M u w + herm M v w := by
  simp [herm, mulVec_add, dotProduct_add]

theorem herm_smul_left (M : Mat k r) (c : ℂ) (u w : Fin (2 * r + k + 1) → ℂ) : herm M (c • u) w = c * herm M u w := by
  simp [herm, mulVec_smul, dotProduct_smul]

theorem herm_add_right (M : Mat k r) (u v w : Fin (2 * r + k + 1) → ℂ) : herm M u (v + w) = herm M u v + herm M u w := by
  simp [herm, add_dotProduct]

theorem herm_smul_right (M : Mat k r) (c : ℂ) (u w : Fin (2 * r + k + 1) → ℂ) :
    herm M u (c • w) = star c * herm M u w := by
  simp [herm, smul_dotProduct]

theorem herm_mulVec (M m : Mat k r) (u w : Fin (2 * r + k + 1) → ℂ) :
    herm M (m *ᵥ u) (m *ᵥ w) = herm (mᴴ * M * m) u w := by
  simp only [herm, star_mulVec, ← mulVec_mulVec, dotProduct_mulVec _ mᴴ]

theorem herm_bvec (M : Mat k r) (i j : Fin (2 * r + k + 1)) : herm M (bvec j) (bvec i) = M i j := by
  unfold herm bvec
  rw [← Pi.single_star, star_one, single_one_dotProduct, mulVec_single_one]
  rfl

theorem phi_zero (h : IsReal H k r σ Φ) : Φ 0 = 0 := by
  have := h.2.1 0 0
  simpa using this

theorem phi_sub (h : IsReal H k r σ Φ) (x y : V) : Φ (x - y) = Φ x - Φ y := by
  have := h.1 (x - y) y
  rw [sub_add_cancel] at this
  rw [this]; abel

theorem phi_sum (h : IsReal H k r σ Φ) {α : Type} (s : Finset α) (f : α → V) :
    Φ (∑ i ∈ s, f i) = ∑ i ∈ s, Φ (f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using phi_zero h
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.1, ih]

theorem phi_inj (h : IsReal H k r σ Φ) {x y : V} (e : Φ x = Φ y) : x = y := by
  rw [← sub_eq_zero]
  refine H.nondeg _ fun w => σ.injective ?_
  rw [← h.2.2.1, phi_sub h, e, sub_self]
  simp [herm]

theorem span_ind (h : IsReal H k r σ Φ) (P : (Fin (2 * r + k + 1) → ℂ) → Prop) (h0 : ∀ x, P (Φ x))
    (ha : ∀ u v, P u → P v → P (u + v)) (hs : ∀ (c : ℂ) u, P u → P (c • u)) (u : Fin (2 * r + k + 1) → ℂ) : P u := by
  have hu : u ∈ Submodule.span ℂ (Set.range Φ) := by rw [h.2.2.2]; trivial
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨y, rfl⟩ := hx; exact h0 y
  | zero => rw [← phi_zero h]; exact h0 0
  | add x y _ _ hx hy => exact ha _ _ hx hy
  | smul c x _ hx => exact hs _ _ hx

theorem mat_unique (h : IsReal H k r σ Φ) {m m' : Mat k r} (e : ∀ x, m *ᵥ Φ x = m' *ᵥ Φ x) : m = m' := by
  have : ∀ u, m *ᵥ u = m' *ᵥ u := span_ind h _ e (fun u v hu hv => by rw [mulVec_add, mulVec_add, hu, hv])
    (fun c u hu => by rw [mulVec_smul, mulVec_smul, hu])
  exact Matrix.toLin'.injective (LinearMap.ext this)

theorem mat_exists [FiniteDimensional K V] (h : IsReal H k r σ Φ) (hd : Module.finrank K V = 2 * r + k + 1)
    (s : V →ₗ[K] V) : ∃ m : Mat k r, ∀ x, m *ᵥ Φ x = Φ (s x) := by
  let b := Module.finBasisOfFinrankEq K V hd
  have hx : ∀ x, Φ x = ∑ i, σ (b.repr x i) • Φ (b i) := fun x => by
    conv_lhs => rw [← b.sum_repr x]
    rw [phi_sum h]
    exact Finset.sum_congr rfl fun i _ => h.2.1 _ _
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range fun i => Φ (b i)) := by
    rw [← h.2.2.2, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let c := basisOfTopLeSpanOfCardEqFinrank (fun i => Φ (b i)) hsp (by simp)
  have hc : ∀ i, c i = Φ (b i) := fun i => by simp [c]
  refine ⟨LinearMap.toMatrix' (c.constr ℂ fun i => Φ (s (b i))), fun x => ?_⟩
  rw [LinearMap.toMatrix'_mulVec, hx x, map_sum]
  conv_rhs => rw [← b.sum_repr x]
  rw [map_sum, phi_sum h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, h.2.1, ← hc, Module.Basis.constr_basis]

theorem mem_UH (h : IsReal H k r σ Φ) {m : Mat k r}
    (e : ∀ x y, herm (Hpk k r) (m *ᵥ Φ x) (m *ᵥ Φ y) = herm (Hpk k r) (Φ x) (Φ y)) : m ∈ UH (Hpk k r) := by
  have h1 : ∀ u w, herm (Hpk k r) (m *ᵥ u) (m *ᵥ w) = herm (Hpk k r) u w := by
    intro u
    refine span_ind h (fun u => ∀ w, herm (Hpk k r) (m *ᵥ u) (m *ᵥ w) = herm (Hpk k r) u w) (fun x => ?_)
      (fun u v hu hv w => by rw [mulVec_add, herm_add_left, herm_add_left, hu, hv])
      (fun c u hu w => by rw [mulVec_smul, herm_smul_left, herm_smul_left, hu]) u
    exact span_ind h _ (e x) (fun u v hu hv => by rw [mulVec_add, herm_add_right, herm_add_right, hu, hv])
      (fun c u hu => by rw [mulVec_smul, herm_smul_right, herm_smul_right, hu])
  ext i j
  exact (herm_bvec _ i j).symm.trans (by rw [← herm_mulVec, h1, herm_bvec])

theorem isReal_mul (h : IsReal H k r σ Φ) {g : Mat k r} (hg : g ∈ UH (Hpk k r)) (hu : IsUnit g.det) :
    IsReal H k r σ fun x => g *ᵥ Φ x := by
  refine ⟨fun x y => by simp only [h.1, mulVec_add], fun c x => by simp only [h.2.1, mulVec_smul], fun x y => ?_, ?_⟩
  · rw [herm_mulVec, show gᴴ * Hpk k r * g = Hpk k r from hg, h.2.2.1]
  · rw [eq_top_iff]
    intro u _
    have : ∀ w, g *ᵥ w ∈ Submodule.span ℂ (Set.range fun x => g *ᵥ Φ x) :=
      span_ind h _ (fun x => Submodule.subset_span ⟨x, rfl⟩)
        (fun u v hu hv => by rw [mulVec_add]; exact Submodule.add_mem _ hu hv)
        (fun c u hu => by rw [mulVec_smul]; exact Submodule.smul_mem _ _ hu)
    have h2 := this (g⁻¹ *ᵥ u)
    rwa [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec] at h2

omit [NumberField K] in
theorem exists_dual (F : FlagD H r) : ∃ f : Fin r → V, ∀ a b, H.B (f a) (F.e b.castSucc) = if a = b then 1 else 0 := by
  let L : V →ₗ[K] (Fin r → K) := LinearMap.pi fun b => H.B.flip (F.e b.castSucc)
  have hL : LinearMap.range L = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    have hφ' : ∀ v : Fin r → K, φ v = ∑ b, v b * φ (Pi.single b 1) := fun v => by
      conv_lhs => rw [pi_eq_sum_univ' v]
      simp [map_sum]
    have h0 : ∑ b, star (φ (Pi.single b 1)) • F.e b.castSucc = 0 := by
      refine H.nondeg _ fun y => ?_
      rw [← H.herm, star_eq_zero]
      have := hle (LinearMap.mem_range_self L y)
      rw [LinearMap.mem_ker, hφ'] at this
      rw [← this, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp [L, mul_comm, starRingEnd_apply]
    have := Fintype.linearIndependent_iff.1 F.indep _ h0
    apply hφ
    refine LinearMap.ext fun v => ?_
    rw [hφ']
    simp only [star_eq_zero] at this
    simp [this]
  choose f hf using fun a : Fin r => (LinearMap.range_eq_top.1 hL) (Pi.single a 1)
  refine ⟨f, fun a b => ?_⟩
  have := congrFun (hf a) b
  simp only [L, LinearMap.pi_apply, LinearMap.flip_apply] at this
  rw [this, Pi.single_apply]; simp [eq_comm]

section Flag
variable {F : FlagD H r} {t : Fin r → ℂ}

theorem coord_of_mem_Xa (h : IsReal H k r σ Φ) (he : ∀ a, Φ (F.e a.castSucc) = t a • bvec (eI k r a)) {a : ℕ} {y : V}
    (hy : y ∈ F.Xa a) (i : Fin (2 * r + k + 1)) (hi : a ≤ i.val) : Φ y i = 0 := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    have hb' : b.val < a := hb
    have : i ≠ eI k r b := fun e => by
      have := congrArg Fin.val e
      simp only [eI] at this; omega
    simp [he, bvec, this]
  | zero => rw [phi_zero h]; rfl
  | add x y _ _ hx hy => rw [h.1, Pi.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [h.2.1, Pi.smul_apply, hx, smul_zero]

theorem herm_sum_left (M : Mat k r) {α : Type} (s : Finset α) (f : α → Fin (2 * r + k + 1) → ℂ) (w) :
    herm M (∑ i ∈ s, f i) w = ∑ i ∈ s, herm M (f i) w := by
  simp [herm, mulVec_sum, dotProduct_sum]

theorem mem_Xa_of_coord (h : IsReal H k r σ Φ) (ht : ∀ a, t a ≠ 0)
    (he : ∀ a, Φ (F.e a.castSucc) = t a • bvec (eI k r a)) {a : ℕ} (har : a ≤ r) {y : V}
    (hy : ∀ i : Fin (2 * r + k + 1), a ≤ i.val → Φ y i = 0) : y ∈ F.Xa a := by
  obtain ⟨f, hf⟩ := exists_dual F
  have hf' : ∀ a b, H.B (F.e b.castSucc) (f a) = if a = b then 1 else 0 := fun a b => by
    rw [← H.herm, hf]; split_ifs <;> simp
  have h1 : Φ y = ∑ b : Fin r, (Φ y (eI k r b) / t b) • Φ (F.e b.castSucc) := by
    funext i
    simp only [he, smul_smul, div_mul_cancel₀ _ (ht _), Finset.sum_apply, Pi.smul_apply, bvec, smul_eq_mul]
    by_cases hi : i.val < r
    · have e : eI k r ⟨i.val, hi⟩ = i := Fin.ext rfl
      rw [Finset.sum_eq_single ⟨i.val, hi⟩]
      · rw [e]; simp
      · intro b _ hb
        have : i ≠ eI k r b := fun e' => hb (Fin.ext (congrArg Fin.val e').symm)
        simp [this]
      · simp
    · rw [hy i (by omega)]
      refine (Finset.sum_eq_zero fun b _ => ?_).symm
      have : i ≠ eI k r b := fun e' => hi (by rw [e']; exact b.2)
      simp [this]
  have h2 : ∀ b, σ (H.B y (f b)) = Φ y (eI k r b) / t b := fun b => by
    rw [← h.2.2.1]
    conv_lhs => rw [h1]
    rw [herm_sum_left]
    simp [herm_smul_left, h.2.2.1, hf', apply_ite σ]
  have h3 : y = ∑ b : Fin r, H.B y (f b) • F.e b.castSucc := by
    apply phi_inj h
    rw [phi_sum h, h1]
    exact Finset.sum_congr rfl fun b _ => by rw [h.2.1, h2]
  rw [h3]
  refine Submodule.sum_mem _ fun b _ => ?_
  by_cases hb : b.val < a
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
  · have : H.B y (f b) = 0 := σ.injective (by rw [h2, hy _ (by simp only [eI]; omega)]; simp)
    rw [this, zero_smul]; exact Submodule.zero_mem _

theorem nset_of_inN (h : IsReal H k r σ Φ) (ht : ∀ a, t a ≠ 0)
    (he : ∀ a, Φ (F.e a.castSucc) = t a • bvec (eI k r a)) {s : V →ₗ[K] V} {m : Mat k r}
    (hm : ∀ x, m *ᵥ Φ x = Φ (s x)) (hs : F.InN s) : m ∈ Nset k r := by
  obtain ⟨h1, -, h2, h3⟩ := hs
  refine ⟨mem_UH h fun x y => by rw [hm, hm, h.2.2.1, h.2.2.1, h1], fun a i hi => ?_, fun i j hj hj' hi => ?_⟩
  · have := coord_of_mem_Xa h he (h2 a) i hi
    rw [phi_sub h, ← hm, he, mulVec_smul, ← smul_sub, Pi.smul_apply, smul_eq_zero, or_iff_right (ht a), Pi.sub_apply,
      sub_eq_zero] at this
    simpa [bvec, Pi.single_apply] using this
  · obtain ⟨f, hf⟩ := exists_dual F
    let P : (Fin (2 * r + k + 1) → ℂ) → Fin (2 * r + k + 1) → ℂ := fun u =>
      u - ∑ a : Fin r, herm (Hpk k r) u (Φ (F.e a.castSucc)) • Φ (f a)
    have hP : ∀ u, (m *ᵥ P u - P u) i = 0 := by
      refine span_ind h _ (fun x => ?_) (fun u v hu hv => ?_) (fun c u hu => ?_)
      · have e : P (Φ x) = Φ (x - ∑ a : Fin r, H.B x (F.e a.castSucc) • f a) := by
          simp only [P, phi_sub h, phi_sum h, h.2.1, h.2.2.1]
        rw [e, hm, ← phi_sub h]
        refine coord_of_mem_Xa h he (h3 _ fun b => ?_) i hi
        rw [← H.herm, star_eq_zero]
        simp [hf]
      · have e : P (u + v) = P u + P v := by
          simp only [P, herm_add_left, add_smul, Finset.sum_add_distrib]; abel
        rw [e, mulVec_add, add_sub_add_comm, Pi.add_apply, hu, hv, add_zero]
      · have e : P (c • u) = c • P u := by
          simp only [P, herm_smul_left, smul_sub, Finset.smul_sum, smul_smul]
        rw [e, mulVec_smul, ← smul_sub, Pi.smul_apply, hu, smul_zero]
    have e : P (bvec j) = bvec j := by
      simp only [P]
      rw [Finset.sum_eq_zero, sub_zero]
      intro a _
      have : esI k r a ≠ j := fun e' => by
        have := congrArg Fin.val e'
        have := a.2
        simp only [esI] at *; omega
      rw [he, herm_smul_right, herm_eI]
      simp [bvec, this]
    have := hP (bvec j)
    rw [e, Pi.sub_apply, sub_eq_zero] at this
    simpa [bvec, Pi.single_apply] using this

theorem inN_of_nset (h : IsReal H k r σ Φ) (ht : ∀ a, t a ≠ 0)
    (he : ∀ a, Φ (F.e a.castSucc) = t a • bvec (eI k r a)) {s : V ≃ₗ[K] V} {m : Mat k r}
    (hm : ∀ x, m *ᵥ Φ x = Φ (s x)) (hN : m ∈ Nset k r) : F.InN (s : V →ₗ[K] V) := by
  have hc := ((WeylGroupFacts.nset_iff m).1 hN).2
  refine ⟨fun x y => σ.injective ?_, s.bijective, fun a => ?_, fun y hy => ?_⟩
  · rw [← h.2.2.1, ← h.2.2.1, LinearEquiv.coe_coe, ← hm, ← hm, herm_mulVec, show mᴴ * Hpk k r * m = Hpk k r from hN.1]
  · refine mem_Xa_of_coord h ht he a.2.le fun i hi => ?_
    rw [phi_sub h, LinearEquiv.coe_coe, ← hm, he, mulVec_smul, ← smul_sub, Pi.smul_apply, Pi.sub_apply]
    have := hN.2.1 a i hi
    simp [bvec, Pi.single_apply, this]
  · refine mem_Xa_of_coord h ht he le_rfl fun i hi => ?_
    have hz : ∀ j : Fin (2 * r + k + 1), r + k < j.val → Φ y j = 0 := fun j hj => by
      have hj2 := j.2
      let a : Fin r := ⟨2 * r + k - j.val, by omega⟩
      have e : esI k r a = j := Fin.ext (by simp only [esI, a]; omega)
      have h0 : H.B y (F.e a.castSucc) = 0 := by rw [← H.herm, hy, star_zero]
      have := h.2.2.1 y (F.e a.castSucc)
      rw [h0, map_zero, he, herm_smul_right, herm_eI, e, mul_eq_zero, star_eq_zero, or_iff_right (ht a)] at this
      exact this
    rw [phi_sub h, LinearEquiv.coe_coe, ← hm, Pi.sub_apply, sub_eq_zero, mulVec, dotProduct, Finset.sum_eq_single i]
    · by_cases hi2 : i.val ≤ r + k
      · rw [hc i i hi2 (Or.inr hi), if_pos rfl, one_mul]
      · rw [hz i (by omega), mul_zero]
    · intro j _ hj
      by_cases hj2 : j.val ≤ r + k
      · rw [hc i j hj2 (Or.inr hi), if_neg hj.symm, zero_mul]
      · rw [hz j (by omega), mul_zero]
    · simp

end Flag

theorem hpk_sq : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [WeylGroupFacts.hpk_mul_apply, WeylGroupFacts.hpk_row, WeylGroupFacts.tau_tau, Matrix.one_apply]
  unfold WeylGroupFacts.sgn WeylGroupFacts.tau
  simp only [Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | simp

theorem isUnit_det {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : IsUnit g.det := by
  have : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, show gᴴ * Hpk k r * g = Hpk k r from hg, hpk_sq]
  exact Matrix.isUnit_det_of_left_inverse this

theorem vInv_pos (E : Type) [Field E] [NumberField E] : 0 < Formalism.HermitianLatticesTheory.vInv E := by
  unfold Formalism.HermitianLatticesTheory.vInv
  have : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero E)
  positivity

theorem real_points : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (k : ℕ) (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)) (β : Fin r → ℕ) (Φ : ι → V → Fin (2 * r + k + 1) → ℂ) (z z' : ι → Fin (2 * r + k + 1) → ℂ) (g : ι → Mat k r), IsPlaces σ → Module.finrank K V = 2 * r + k + 1 → (∀ v, IsFrameOf N k (σ v) (2 * Formalism.HermitianLatticesTheory.vInv K) β (Φ v) (z v) (z' v) (g v)) → (∀ s : V ≃ₗ[K] V, ∃! m : ι → Mt k r, ∀ v x, Matrix.of (m v) *ᵥ Φ v x = Φ v (s x)) ∧ (∀ s t : V ≃ₗ[K] V, Nonempty ι → (∀ v x, Φ v (s x) = Φ v (t x)) → s = t) ∧ realPts Φ (N.R : Set (V ≃ₗ[K] V)) ⊆ RP k r g ∧ ∀ (s : V ≃ₗ[K] V) (m : ι → Mt k r), (∀ v x, Matrix.of (m v) *ᵥ Φ v x = Φ v (s x)) → Nonempty ι → m ∈ RP k r g → s ∈ N.R := by
  intro K V _ _ _ _ _ _ _ _ H hK r N k ι _ σ β Φ z z' g _ hd hF
  have hR : ∀ s : V ≃ₗ[K] V, s ∈ N.R ↔ N.F.InN (s : V →ₗ[K] V) ∧ N.F'.InN (s : V →ₗ[K] V) :=
    (GlobalTheory.UnipStab.common_unipotent_stabiliser K V H hK r N).1
  have hr : ∀ v, IsReal H k r (σ v) (Φ v) := fun v => (hF v).1
  have hg : ∀ v, g v ∈ UH (Hpk k r) := fun v => (hF v).2.2.2.2.1.choose_spec.1
  have hu : ∀ v, IsUnit (g v).det := fun v => isUnit_det (hg v)
  have hr' : ∀ v, IsReal H k r (σ v) fun x => g v *ᵥ Φ v x := fun v => isReal_mul (hr v) (hg v) (hu v)
  have ht : ∀ a : Fin r, ((((2 * Formalism.HermitianLatticesTheory.vInv K) ^ (r - a.val) : ℝ)) : ℂ) ≠ 0 := fun a => by
    have := vInv_pos K
    exact_mod_cast (by positivity : (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (r - a.val) ≠ 0)
  have hconj : ∀ (v) (s : V ≃ₗ[K] V) (m : Mat k r), (∀ x, m *ᵥ Φ v x = Φ v (s x)) →
      ∀ x, (g v * m * (g v)⁻¹) *ᵥ (g v *ᵥ Φ v x) = g v *ᵥ Φ v (s x) := fun v s m hm x => by
    rw [mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ (hu v), Matrix.mul_one, ← mulVec_mulVec, hm]
  refine ⟨fun s => ?_, fun s t ⟨v⟩ e => LinearEquiv.ext fun x => phi_inj (hr v) (e v x), ?_, fun s m hm ⟨v⟩ hP => ?_⟩
  · choose m hm using fun v => mat_exists (hr v) hd (s : V →ₗ[K] V)
    refine ⟨fun v => Matrix.of.symm (m v), fun v x => hm v x, fun m' hm' => funext fun v => ?_⟩
    exact mat_unique (hr v) (m := Matrix.of (m' v)) (m' := m v) fun x => (hm' v x).trans (hm v x).symm
  · rintro m ⟨s, hs, hm⟩ v
    obtain ⟨h1, h2⟩ := (hR s).1 hs
    exact ⟨nset_of_inN (hr v) ht (fun a => ((hF v).2.2.2.2.2.1 a).1) (hm v) h1,
      nset_of_inN (hr' v) ht (fun a => ((hF v).2.2.2.2.2.1 a).2) (hconj v s _ (hm v)) h2⟩
  · exact (hR s).2 ⟨inN_of_nset (hr v) ht (fun a => ((hF v).2.2.2.2.2.1 a).1) (hm v) (hP v).1,
      inN_of_nset (hr' v) ht (fun a => ((hF v).2.2.2.2.2.1 a).2) (hconj v s _ (hm v)) (hP v).2⟩

end GlobalTheory.DegVol.RealMat
