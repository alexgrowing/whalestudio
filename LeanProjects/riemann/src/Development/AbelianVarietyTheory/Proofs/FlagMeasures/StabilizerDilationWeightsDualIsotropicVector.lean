import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerSetEqRangeNormalFormStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerHaarUnimodularNormalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatGroupHaarUniqueFiniteCompactOpenPos
import Formalism.FormalDegreeBessel.FinalG

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp Filter Topology
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.StabHaar

variable {k r : ℕ}

theorem conj_cont (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) := by
  show Continuous fun x : Mt k r => a * Matrix.of x * a⁻¹
  first
  | fun_prop
  | exact (continuous_const.mul continuous_id).mul continuous_const

theorem lmul_cont (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) := by
  show Continuous fun x : Mt k r => a * Matrix.of x
  first
  | fun_prop
  | exact continuous_const.mul continuous_id

theorem conj_conj (a b : Mat k r) : (conjM a : Mt k r → Mt k r) ∘ conjM b = conjM (a * b) := by
  funext x
  change a * (b * Matrix.of x * b⁻¹) * a⁻¹ = a * b * Matrix.of x * (a * b)⁻¹
  rw [Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

theorem conj_one : (conjM (1 : Mat k r) : Mt k r → Mt k r) = id := by
  funext x
  change (1 : Mat k r) * Matrix.of x * (1 : Mat k r)⁻¹ = Matrix.of x
  rw [Matrix.inv_eq_right_inv (Matrix.mul_one (1 : Mat k r)), Matrix.one_mul, Matrix.mul_one]

theorem map_conj_conj (μ : Measure (Mt k r)) (a b : Mat k r) :
    (μ.map (conjM b)).map (conjM a) = μ.map (conjM (a * b)) := by
  rw [Measure.map_map (conj_cont a).measurable (conj_cont b).measurable, conj_conj]

noncomputable def conjE (a : Mat k r) (ha : IsUnit a.det) : Mt k r ≃ᵐ Mt k r where
  toFun := conjM a
  invFun := conjM a⁻¹
  left_inv x := by
    have := congrFun (conj_conj a⁻¹ a) x
    rw [Matrix.nonsing_inv_mul a ha, conj_one] at this
    exact this
  right_inv x := by
    have := congrFun (conj_conj a a⁻¹) x
    rw [Matrix.mul_nonsing_inv a ha, conj_one] at this
    exact this
  measurable_toFun := (conj_cont a).measurable
  measurable_invFun := (conj_cont a⁻¹).measurable

theorem haar_conj {G G' : Set (Mat k r)} {μ : Measure (Mt k r)} (a : Mat k r) (ha : IsUnit a.det)
    (h : ∀ x, x ∈ G ↔ a * x * a⁻¹ ∈ G') (hμ : IsHaarOn G μ) : IsHaarOn G' (μ.map (conjM a)) := by
  obtain ⟨hσ, h0, hnull, hinv⟩ := hμ
  have hm : Measurable (conjM a : Mt k r → Mt k r) := (conj_cont a).measurable
  have hback : (μ.map (conjM a)).map (conjM a⁻¹) = μ := by
    rw [map_conj_conj, Matrix.nonsing_inv_mul a ha, conj_one, Measure.map_id]
  refine ⟨?_, ?_, ?_, ?_⟩
  · haveI := hσ
    have hs : SigmaFinite ((μ.map (conjM a)).map (conjM a⁻¹)) := by rw [hback]; exact hσ
    exact SigmaFinite.of_map _ (conj_cont a⁻¹).measurable.aemeasurable hs
  · intro hz
    apply h0
    rw [← hback, hz, Measure.map_zero]
  · have hE : μ.map (conjM a) = μ.map (conjE a ha) := rfl
    rw [hE, MeasurableEquiv.map_apply]
    convert hnull using 2
    ext x
    exact not_congr (h (Matrix.of x)).symm
  · intro s hs
    have ht : a⁻¹ * s * a ∈ G := by
      rw [h]
      have e : a * (a⁻¹ * s * a) * a⁻¹ = s := by
        simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv a ha, Matrix.one_mul]
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv a ha, Matrix.mul_one]
      rw [e]; exact hs
    have hc : (lmulM s : Mt k r → Mt k r) ∘ conjM a = conjM a ∘ lmulM (a⁻¹ * s * a) := by
      funext x
      change s * (a * Matrix.of x * a⁻¹) = a * ((a⁻¹ * s * a) * Matrix.of x) * a⁻¹
      simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv a ha, Matrix.one_mul]
    rw [Measure.map_map (lmul_cont s).measurable hm, hc,
      ← Measure.map_map hm (lmul_cont _).measurable, hinv _ ht]

theorem unit_of_GG {g : Mat k r} (hg : g ∈ GG k r) : IsUnit g.det := by
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1
  exact ((uHGroup _ (Hpk k r) hH).2.2 g hg).1

theorem matGroup {G : Set (Mat k r)} (h : IsClosedSub k r G) : PI.IsMatGroup G := by
  obtain ⟨hsub, hcl, h1, hmul, hinv⟩ := h
  exact ⟨hcl, h1, hmul, fun a ha => ⟨hinv a ha, Matrix.mul_nonsing_inv a (unit_of_GG (hsub ha))⟩⟩

theorem N_conj {n : Mat k r} (hn : n ∈ Nset k r) (y : Mat k r) : n * y * n⁻¹ ∈ Nset k r ↔ y ∈ Nset k r := by
  obtain ⟨-, hmul, hinv⟩ := nSubgroup k r
  have hu : IsUnit n.det := unit_of_GG hn.1
  constructor
  · intro hy
    have e : y = n⁻¹ * (n * y * n⁻¹) * n := by
      simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul n hu, Matrix.one_mul]
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul n hu, Matrix.mul_one]
    rw [e]
    exact hmul _ (hmul _ (hinv n hn) _ hy) _ hn
  · intro hy
    exact hmul _ (hmul _ hn _ hy) _ (hinv n hn)

theorem Rset_conj {n₁ n₂ : Mat k r} (g : Mat k r) (h₁ : n₁ ∈ Nset k r) (h₂ : n₂ ∈ Nset k r) (x : Mat k r) :
    x ∈ Rset k r (n₁ * g * n₂) ↔ n₂ * x * n₂⁻¹ ∈ Rset k r g := by
  show (x ∈ Nset k r ∧ n₁ * g * n₂ * x * (n₁ * g * n₂)⁻¹ ∈ Nset k r) ↔
    (n₂ * x * n₂⁻¹ ∈ Nset k r ∧ g * (n₂ * x * n₂⁻¹) * g⁻¹ ∈ Nset k r)
  have e : n₁ * g * n₂ * x * (n₁ * g * n₂)⁻¹ = n₁ * (g * (n₂ * x * n₂⁻¹) * g⁻¹) * n₁⁻¹ := by
    simp only [Matrix.mul_inv_rev, Matrix.mul_assoc]
  rw [e, N_conj h₁, N_conj h₂]

theorem le_of_tendsto_conj (ν : Measure (Mt k r)) (U : Set (Mt k r)) (hU : IsOpen U) (n : ℕ → Mat k r)
    (h1 : Tendsto n atTop (𝓝 1)) (h2 : Tendsto (fun i => (n i)⁻¹) atTop (𝓝 1)) (C : ℝ≥0∞)
    (h : ∀ i, ν.map (conjM (n i)) U ≤ C) : ν U ≤ C := by
  have hm : ∀ i, Measurable (conjM (n i) : Mt k r → Mt k r) := fun i => (conj_cont _).measurable
  let V : ℕ → Set (Mt k r) := fun m => ⋂ i ≥ m, conjM (n i) ⁻¹' U
  have hVmono : Monotone V := by
    intro a b hab x hx
    simp only [V, Set.mem_iInter] at hx ⊢
    exact fun i hi => hx i (le_trans hab hi)
  have hVle : ∀ m, ν (V m) ≤ C := by
    intro m
    calc ν (V m) ≤ ν (conjM (n m) ⁻¹' U) := measure_mono (Set.biInter_subset_of_mem (le_refl m))
      _ = ν.map (conjM (n m)) U := (Measure.map_apply (hm m) hU.measurableSet).symm
      _ ≤ C := h m
  have hsub : U ⊆ ⋃ m, V m := by
    intro x hx
    have h3 : Tendsto (fun i => n i * Matrix.of x * (n i)⁻¹) atTop (𝓝 (1 * Matrix.of x * 1)) :=
      (h1.mul tendsto_const_nhds).mul h2
    rw [Matrix.one_mul, Matrix.mul_one] at h3
    have ht : Tendsto (fun i => conjM (n i) x) atTop (𝓝 x) := h3
    obtain ⟨m, hm'⟩ := Filter.eventually_atTop.1 (ht (hU.mem_nhds hx))
    exact Set.mem_iUnion.2 ⟨m, Set.mem_iInter₂.2 fun i hi => hm' i hi⟩
  have hU' : ν (⋃ m, V m) = ⨆ m, ν (V m) := by
    first
    | exact hVmono.measure_iUnion
    | exact measure_iUnion_eq_iSup hVmono.directed_le
  calc ν U ≤ ν (⋃ m, V m) := measure_mono hsub
    _ = ⨆ m, ν (V m) := hU'
    _ ≤ C := iSup_le hVle

def pw (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℤ :=
  if i.val < r then (r : ℤ) - i.val else if i.val ≤ r + k then 0 else (r : ℤ) + k - i.val

theorem pw_e (a : Fin r) : pw k r (eI k r a) = (r : ℤ) - a.val := by
  have ha := a.isLt
  unfold pw
  rw [if_pos (by simp only [eI, Fin.val_mk]; omega)]
  simp only [eI, Fin.val_mk]
theorem pw_w (a : Fin (k + 1)) : pw k r (wI k r a) = 0 := by
  have ha := a.isLt
  unfold pw
  rw [if_neg (by simp only [wI, Fin.val_mk]; omega), if_pos (by simp only [wI, Fin.val_mk]; omega)]
theorem stabilizerDilationWeights_dualIsotropicVector (a : Fin r) : pw k r (esI k r a) = -((r : ℤ) - a.val) := by
  have ha := a.isLt
  unfold pw
  rw [if_neg (by simp only [esI, Fin.val_mk]; omega), if_neg (by simp only [esI, Fin.val_mk]; omega)]
  simp only [esI, Fin.val_mk]
  omega

noncomputable def DD (k r : ℕ) (ε : ℝ) : Mat k r := Matrix.diagonal fun i => (ε : ℂ) ^ pw k r i

theorem DD_mul {ε : ℝ} (h : ε ≠ 0) : DD k r ε * DD k r ε⁻¹ = 1 := by
  have hc : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h
  unfold DD
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  simp only [Complex.ofReal_inv, _root_.inv_zpow]
  exact mul_inv_cancel₀ (zpow_ne_zero _ hc)

theorem DD_unit {ε : ℝ} (h : ε ≠ 0) : IsUnit (DD k r ε).det := Matrix.isUnit_det_of_right_inverse (DD_mul h)

theorem DD_inv {ε : ℝ} (h : ε ≠ 0) : (DD k r ε)⁻¹ = DD k r ε⁻¹ := Matrix.inv_eq_right_inv (DD_mul h)

theorem DD_conj {ε : ℝ} (h : ε ≠ 0) (x : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (DD k r ε * x * (DD k r ε)⁻¹) i j = (ε : ℂ) ^ pw k r i * x i j * ((ε : ℂ) ^ pw k r j)⁻¹ := by
  rw [DD_inv h]
  unfold DD
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Complex.ofReal_inv, _root_.inv_zpow]

private theorem inv_eq_Hpk_mul_conjTranspose_mul_Hpk_of_mem_Nset {n : Mat k r} (hn : n ∈ Nset k r) : n⁻¹ = Hpk k r * nᴴ * Hpk k r := by
  have hu : nᴴ * Hpk k r * n = Hpk k r := hn.1
  have hH : Hpk k r * Hpk k r = 1 := (Formalism.QuantumDeterminants.hpkFacts k r).2.1
  apply Matrix.inv_eq_left_inv
  calc Hpk k r * nᴴ * Hpk k r * n = Hpk k r * (nᴴ * Hpk k r * n) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hu, hH]

private theorem Hpk_eI_apply (b : Fin r) (p : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r b) p = if p = esI k r b then 1 else 0 := by
  refine Rad.cases3 (P := fun p => Hpk k r (eI k r b) p = if p = esI k r b then 1 else 0) ?_ ?_ ?_ p
  · intro a
    rw [Rad.H_ee, if_neg (Rad.eI_ne_esI a b)]
  · intro j
    rw [Rad.H_ew, if_neg (Rad.wI_ne_esI j b)]
  · intro c
    rw [Rad.H_es]
    by_cases h : b = c
    · subst h; simp
    · have h' : esI k r c ≠ esI k r b := fun e => h ((Rad.esI_inj c b).1 e).symm
      rw [if_neg h, if_neg h']

private theorem Hpk_apply_eI (a : Fin r) (q : Fin (2 * r + k + 1)) :
    Hpk k r q (eI k r a) = if q = esI k r a then 1 else 0 := by
  refine Rad.cases3 (P := fun q => Hpk k r q (eI k r a) = if q = esI k r a then 1 else 0) ?_ ?_ ?_ q
  · intro c
    rw [Rad.H_ee, if_neg (Rad.eI_ne_esI c a)]
  · intro j
    rw [Rad.H_we, if_neg (Rad.wI_ne_esI j a)]
  · intro c
    rw [Rad.H_se]
    by_cases h : c = a
    · subst h; simp
    · have h' : esI k r c ≠ esI k r a := fun e => h ((Rad.esI_inj c a).1 e)
      rw [if_neg h, if_neg h']

theorem N_ss {n : Mat k r} (hn : n ∈ Nset k r) (a b : Fin r) (hab : a ≤ b) :
    n (esI k r a) (esI k r b) = if a = b then 1 else 0 := by
  have hinv : n⁻¹ ∈ Nset k r := (Formalism.QuantumDeterminants.nSubgroup k r).2.2 n hn
  have h1 := hinv.2.1 a (eI k r b) (by show a.val ≤ b.val; exact Fin.le_iff_val_le_val.mp hab)
  have h2 : n⁻¹ (eI k r b) (eI k r a) = star (n (esI k r a) (esI k r b)) := by
    rw [inv_eq_Hpk_mul_conjTranspose_mul_Hpk_of_mem_Nset hn, Matrix.mul_apply, Finset.sum_eq_single (esI k r a)]
    · rw [Hpk_apply_eI a (esI k r a), if_pos rfl, mul_one, Matrix.mul_apply, Finset.sum_eq_single (esI k r b)]
      · rw [Hpk_eI_apply b (esI k r b), if_pos rfl, one_mul, Matrix.conjTranspose_apply]
      · intro p _ hp
        rw [Hpk_eI_apply b p, if_neg hp, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · intro q _ hq
      rw [Hpk_apply_eI a q, if_neg hq, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [h2] at h1
  have h3 : eI k r b = eI k r a ↔ a = b := by rw [Rad.eI_inj]; exact eq_comm
  have h4 := congrArg star h1
  rw [star_star] at h4
  rw [h4]
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg h, if_neg (fun e => h (h3.1 e)), star_zero]

theorem N_entry {n : Mat k r} (hn : n ∈ Nset k r) (i j : Fin (2 * r + k + 1)) (h : pw k r i ≤ pw k r j) :
    n i j = (1 : Mat k r) i j := by
  revert h
  refine Rad.cases3 (P := fun j => pw k r i ≤ pw k r j → n i j = (1 : Mat k r) i j) ?_ ?_ ?_ j
  · intro b h
    have hi : b.val ≤ i.val := by
      by_contra hc
      push_neg at hc
      have hir : i.val < r := lt_trans hc b.isLt
      have hp : pw k r i = (r : ℤ) - i.val := by unfold pw; rw [if_pos hir]
      rw [hp, pw_e] at h
      omega
    rw [hn.2.1 b i hi, Matrix.one_apply]
  · intro m h
    have hi : r ≤ i.val := by
      by_contra hc
      push_neg at hc
      have hp : pw k r i = (r : ℤ) - i.val := by unfold pw; rw [if_pos hc]
      rw [hp, pw_w] at h
      omega
    have hm := m.isLt
    rw [hn.2.2 i (wI k r m) (by show r ≤ r + m.val; omega) (by show r + m.val ≤ r + k; omega) hi, Matrix.one_apply]
  · intro c h
    revert h
    refine Rad.cases3 (P := fun i => pw k r i ≤ pw k r (esI k r c) → n i (esI k r c) = (1 : Mat k r) i (esI k r c)) ?_ ?_ ?_ i
    · intro a h
      rw [pw_e, stabilizerDilationWeights_dualIsotropicVector] at h
      have := a.isLt
      have := c.isLt
      omega
    · intro m h
      rw [pw_w, stabilizerDilationWeights_dualIsotropicVector] at h
      have := c.isLt
      omega
    · intro a h
      rw [stabilizerDilationWeights_dualIsotropicVector, stabilizerDilationWeights_dualIsotropicVector] at h
      have hac : a ≤ c := by
        rw [Fin.le_iff_val_le_val]
        omega
      rw [N_ss hn a c hac, Matrix.one_apply]
      by_cases hh : a = c
      · subst hh; simp
      · rw [if_neg hh, if_neg (fun e => hh ((Rad.esI_inj a c).1 e))]

noncomputable def ep (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)

theorem ep_ne (m : ℕ) : ep m ≠ 0 := by
  unfold ep
  positivity

theorem tendsto_DD {n : Mat k r} (hn : n ∈ Nset k r) :
    Tendsto (fun m => DD k r (ep m) * n * (DD k r (ep m))⁻¹) atTop (𝓝 1) := by
  have h0 : Tendsto (fun m : ℕ => ep m) atTop (𝓝 0) := by
    show Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hep : Tendsto (fun m : ℕ => ((ep m : ℝ) : ℂ)) atTop (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp h0
    rw [Complex.ofReal_zero] at h
    exact h
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have he : ∀ m : ℕ, (DD k r (ep m) * n * (DD k r (ep m))⁻¹) i j =
      ((ep m : ℝ) : ℂ) ^ pw k r i * n i j * (((ep m : ℝ) : ℂ) ^ pw k r j)⁻¹ := fun m => DD_conj (ep_ne m) n i j
  refine (tendsto_congr he).2 ?_
  by_cases hij : pw k r i ≤ pw k r j
  · have hn' := N_entry hn i j hij
    have hc : ∀ m : ℕ, ((ep m : ℝ) : ℂ) ^ pw k r i * n i j * (((ep m : ℝ) : ℂ) ^ pw k r j)⁻¹ = (1 : Mat k r) i j := by
      intro m
      have hne : ((ep m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ep_ne m
      rw [hn', Matrix.one_apply]
      by_cases hh : i = j
      · subst hh
        rw [if_pos rfl, mul_one, mul_inv_cancel₀ (zpow_ne_zero _ hne)]
      · rw [if_neg hh, mul_zero, zero_mul]
    exact (tendsto_congr hc).2 tendsto_const_nhds
  · push_neg at hij
    have hne : i ≠ j := fun e => by subst e; exact lt_irrefl _ hij
    rw [Matrix.one_apply, if_neg hne]
    have hpos : 0 ≤ pw k r i - pw k r j - 1 := by omega
    obtain ⟨d, hd⟩ : ∃ d : ℕ, pw k r i = pw k r j + ((d + 1 : ℕ) : ℤ) := by
      refine ⟨(pw k r i - pw k r j - 1).toNat, ?_⟩
      push_cast
      rw [Int.toNat_of_nonneg hpos]
      ring
    have hc : ∀ m : ℕ, ((ep m : ℝ) : ℂ) ^ pw k r i * n i j * (((ep m : ℝ) : ℂ) ^ pw k r j)⁻¹ =
        n i j * ((ep m : ℝ) : ℂ) ^ (d + 1) := by
      intro m
      have hne' : ((ep m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ep_ne m
      have hz : ((ep m : ℝ) : ℂ) ^ pw k r j ≠ 0 := zpow_ne_zero _ hne'
      rw [hd, zpow_add₀ hne', zpow_natCast]
      rw [show ∀ x y z : ℂ, x * y * z * x⁻¹ = (x * x⁻¹) * (z * y) from fun x y z => by ring]
      rw [mul_inv_cancel₀ hz, one_mul]
    refine (tendsto_congr hc).2 ?_
    have h5 : Tendsto (fun m : ℕ => n i j * ((ep m : ℝ) : ℂ) ^ (d + 1)) atTop (𝓝 (n i j * 0 ^ (d + 1))) :=
      tendsto_const_nhds.mul (hep.pow (d + 1))
    simpa using h5

private theorem UEmb_mI_eq_wI (m : Fin (k + 1)) : UEmb.mI k r m = wI k r m := Fin.ext rfl

private theorem uEmb_eI_wI_eq_zero (u : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) (n : Fin (k + 1)) :
    uEmb k r u (eI k r a) (wI k r n) = 0 := by
  simp only [← UEmb_mI_eq_wI]; exact UEmb.u_em (u := u) (a := a) (n := n)

private theorem uEmb_wI_eI_eq_zero (u : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) (m : Fin (k + 1)) :
    uEmb k r u (wI k r m) (eI k r a) = 0 := by
  simp only [← UEmb_mI_eq_wI]; exact UEmb.u_me (u := u) (b := a) (m := m)

private theorem uEmb_wI_wI_eq_ite (u : Matrix (Fin r) (Fin r) ℂ) (m n : Fin (k + 1)) :
    uEmb k r u (wI k r m) (wI k r n) = if m = n then 1 else 0 := by
  simp only [← UEmb_mI_eq_wI]; exact UEmb.u_mm (u := u) (m := m) (n := n)

private theorem uEmb_wI_esI_eq_zero (u : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) (m : Fin (k + 1)) :
    uEmb k r u (wI k r m) (esI k r a) = 0 := by
  simp only [← UEmb_mI_eq_wI]; exact UEmb.u_ms (u := u) (b := a) (m := m)

private theorem uEmb_esI_wI_eq_zero (u : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) (n : Fin (k + 1)) :
    uEmb k r u (esI k r a) (wI k r n) = 0 := by
  simp only [← UEmb_mI_eq_wI]; exact UEmb.u_sm (u := u) (a := a) (n := n)

private theorem star_ofReal_zpow (ε : ℝ) (n : ℤ) : star ((ε : ℂ) ^ n) = (ε : ℂ) ^ n := by
  rw [star_zpow₀, Complex.star_def, Complex.conj_ofReal]

private theorem DD_eq_uEmb_diagonal_zpow {ε : ℝ} (h : ε ≠ 0) :
    DD k r ε = uEmb k r (Matrix.diagonal fun a : Fin r => (ε : ℂ) ^ ((r : ℤ) - a.val)) := by
  have hc : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h
  set d : Fin r → ℂ := fun a => (ε : ℂ) ^ ((r : ℤ) - a.val) with hd
  have hd0 : ∀ a, d a ≠ 0 := fun a => zpow_ne_zero _ hc
  have hD : Matrix.diagonal d * Matrix.diagonal (fun a => (d a)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one
    exact mul_inv_cancel₀ (hd0 _)
  have hDi : (Matrix.diagonal d)⁻¹ = Matrix.diagonal (fun a => (d a)⁻¹) := Matrix.inv_eq_right_inv hD
  ext i j
  revert j
  refine Rad.cases3 (P := fun i => ∀ j, DD k r ε i j = uEmb k r (Matrix.diagonal d) i j) ?_ ?_ ?_ i
  · intro a j
    refine Rad.cases3 (P := fun j => DD k r ε (eI k r a) j = uEmb k r (Matrix.diagonal d) (eI k r a) j) ?_ ?_ ?_ j
    · intro b
      rw [UEmb.u_ee]
      simp only [DD, Matrix.diagonal_apply, Rad.eI_inj, pw_e, hd]
    · intro n
      rw [uEmb_eI_wI_eq_zero]
      simp only [DD, Matrix.diagonal_apply, Rad.eI_ne_wI, if_false]
    · intro b
      rw [UEmb.u_es]
      simp only [DD, Matrix.diagonal_apply, Rad.eI_ne_esI, if_false]
  · intro m j
    refine Rad.cases3 (P := fun j => DD k r ε (wI k r m) j = uEmb k r (Matrix.diagonal d) (wI k r m) j) ?_ ?_ ?_ j
    · intro b
      rw [uEmb_wI_eI_eq_zero]
      simp only [DD, Matrix.diagonal_apply, Rad.wI_ne_eI, if_false]
    · intro n
      rw [uEmb_wI_wI_eq_ite]
      simp only [DD, Matrix.diagonal_apply, Rad.wI_inj, pw_w, zpow_zero]
    · intro b
      rw [uEmb_wI_esI_eq_zero]
      simp only [DD, Matrix.diagonal_apply, Rad.wI_ne_esI, if_false]
  · intro a j
    refine Rad.cases3 (P := fun j => DD k r ε (esI k r a) j = uEmb k r (Matrix.diagonal d) (esI k r a) j) ?_ ?_ ?_ j
    · intro b
      rw [UEmb.u_se]
      simp only [DD, Matrix.diagonal_apply, Rad.esI_ne_eI, if_false]
    · intro n
      rw [uEmb_esI_wI_eq_zero]
      simp only [DD, Matrix.diagonal_apply, Rad.esI_ne_wI, if_false]
    · intro b
      rw [UEmb.u_ss, hDi]
      simp only [DD, Matrix.diagonal_apply, Rad.esI_inj, stabilizerDilationWeights_dualIsotropicVector]
      by_cases hab : a = b
      · subst hab
        simp only [if_true, hd, star_inv₀, star_ofReal_zpow, _root_.zpow_neg]
      · simp only [hab, Ne.symm hab, if_false, star_zero]

theorem DD_uEmb {ε : ℝ} (h : ε ≠ 0) (β : Fin r → ℕ) (x : UTin β → ℂ) :
    ∃ x', DD k r ε * uEmb k r (upperIn β x) * (DD k r ε)⁻¹ = uEmb k r (upperIn β x') := by
  have hc : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h
  rw [DD_eq_uEmb_diagonal_zpow h]
  set d : Fin r → ℂ := fun a => (ε : ℂ) ^ ((r : ℤ) - a.val) with hd
  have hd0 : ∀ a, d a ≠ 0 := fun a => zpow_ne_zero _ hc
  have hD : Matrix.diagonal d * Matrix.diagonal (fun a => (d a)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one
    exact mul_inv_cancel₀ (hd0 _)
  have hDu : IsUnit (Matrix.diagonal d).det := Matrix.isUnit_det_of_right_inverse hD
  have hDi : (Matrix.diagonal d)⁻¹ = Matrix.diagonal (fun a => (d a)⁻¹) := Matrix.inv_eq_right_inv hD
  refine ⟨fun p => d p.1.1.1 * x p * (d p.1.1.2)⁻¹, ?_⟩
  rw [UEmb.uEmb_inv _ hDu, ← UEmb.uEmb_mul, ← UEmb.uEmb_mul, hDi]
  congr 1
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [upperIn, upper]
  by_cases hab : a < b
  · by_cases hβ : β a = β b
    · simp [hab, hβ]
    · simp [hab, hβ]
  · by_cases he : a = b
    · subst he
      simp [hd0]
    · simp [hab, he]

theorem DD_pEl {ε : ℝ} (h : ε ≠ 0) (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) :
    DD k r ε * pEl k r B S * (DD k r ε)⁻¹ = pEl k r (fun a i => (ε : ℂ) ^ ((r : ℤ) - a.val) * B a i)
      (Matrix.of fun a b => (ε : ℂ) ^ ((r : ℤ) - a.val) * S a b * (ε : ℂ) ^ ((r : ℤ) - b.val)) := by
  have hc : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h
  have hz : ∀ n : ℤ, (ε : ℂ) ^ n ≠ 0 := fun n => zpow_ne_zero n hc
  ext i j
  rw [DD_conj h]
  revert j
  refine Rad.cases3 (P := fun i => ∀ j, (ε : ℂ) ^ pw k r i * pEl k r B S i j * ((ε : ℂ) ^ pw k r j)⁻¹ =
    pEl k r (fun a i => (ε : ℂ) ^ ((r : ℤ) - a.val) * B a i)
      (Matrix.of fun a b => (ε : ℂ) ^ ((r : ℤ) - a.val) * S a b * (ε : ℂ) ^ ((r : ℤ) - b.val)) i j) ?_ ?_ ?_ i
  · intro a j
    refine Rad.cases3 (P := fun j => (ε : ℂ) ^ pw k r (eI k r a) * pEl k r B S (eI k r a) j * ((ε : ℂ) ^ pw k r j)⁻¹ =
      pEl k r (fun a i => (ε : ℂ) ^ ((r : ℤ) - a.val) * B a i)
        (Matrix.of fun a b => (ε : ℂ) ^ ((r : ℤ) - a.val) * S a b * (ε : ℂ) ^ ((r : ℤ) - b.val)) (eI k r a) j) ?_ ?_ ?_ j
    · intro b
      rw [Rad.pEl_ee, Rad.pEl_ee, pw_e, pw_e]
      by_cases hab : a = b
      · subst hab; simp [hz]
      · simp [hab]
    · intro n
      rw [Rad.pEl_ew, Rad.pEl_ew, pw_e, pw_w, zpow_zero, inv_one, mul_one, star_mul', star_ofReal_zpow]
      ring
    · intro b
      rw [Rad.pEl_es, Rad.pEl_es, pw_e, stabilizerDilationWeights_dualIsotropicVector, _root_.zpow_neg, inv_inv, Rad.herm_Hb, Rad.herm_Hb]
      have hsum : (∑ l, star ((ε : ℂ) ^ ((r : ℤ) - a.val) * B a l) *
          (Rad.sg k l * ((ε : ℂ) ^ ((r : ℤ) - b.val) * B b l))) =
          (ε : ℂ) ^ ((r : ℤ) - a.val) * (ε : ℂ) ^ ((r : ℤ) - b.val) * ∑ l, star (B a l) * (Rad.sg k l * B b l) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [star_mul', star_ofReal_zpow]
        ring
      simp only [Matrix.of_apply]
      rw [hsum]
      ring
  · intro m j
    refine Rad.cases3 (P := fun j => (ε : ℂ) ^ pw k r (wI k r m) * pEl k r B S (wI k r m) j * ((ε : ℂ) ^ pw k r j)⁻¹ =
      pEl k r (fun a i => (ε : ℂ) ^ ((r : ℤ) - a.val) * B a i)
        (Matrix.of fun a b => (ε : ℂ) ^ ((r : ℤ) - a.val) * S a b * (ε : ℂ) ^ ((r : ℤ) - b.val)) (wI k r m) j) ?_ ?_ ?_ j
    · intro b
      rw [Rad.pEl_we, Rad.pEl_we]; simp
    · intro n
      rw [Rad.pEl_ww, Rad.pEl_ww, pw_w, pw_w]; simp
    · intro b
      rw [Rad.pEl_ws, Rad.pEl_ws, pw_w, stabilizerDilationWeights_dualIsotropicVector, _root_.zpow_neg, inv_inv, zpow_zero, one_mul]
      ring
  · intro a j
    refine Rad.cases3 (P := fun j => (ε : ℂ) ^ pw k r (esI k r a) * pEl k r B S (esI k r a) j * ((ε : ℂ) ^ pw k r j)⁻¹ =
      pEl k r (fun a i => (ε : ℂ) ^ ((r : ℤ) - a.val) * B a i)
        (Matrix.of fun a b => (ε : ℂ) ^ ((r : ℤ) - a.val) * S a b * (ε : ℂ) ^ ((r : ℤ) - b.val)) (esI k r a) j) ?_ ?_ ?_ j
    · intro b
      rw [Rad.pEl_se, Rad.pEl_se]; simp
    · intro n
      rw [Rad.pEl_sw, Rad.pEl_sw]; simp
    · intro b
      rw [Rad.pEl_ss, Rad.pEl_ss, stabilizerDilationWeights_dualIsotropicVector, stabilizerDilationWeights_dualIsotropicVector]
      by_cases hab : a = b
      · subst hab; simp [hz]
      · simp [hab]

theorem DD_pTop {ε : ℝ} (h : ε ≠ 0) (j : ℕ) (q : PTop k r j) :
    ∃ q', DD k r ε * pTop k r j q * (DD k r ε)⁻¹ = pTop k r j q' := by
  obtain ⟨B, s, t⟩ := q
  refine ⟨(fun a i => (ε : ℂ) ^ ((r : ℤ) - a.1.val) * B a i,
    fun p => (ε : ℂ) ^ ((r : ℤ) - p.1.1.1.val) * (ε : ℂ) ^ ((r : ℤ) - p.1.1.2.val) * s p,
    fun a => (ε ^ ((r : ℤ) - a.1.val)) ^ 2 * t a), ?_⟩
  simp only [pTop, pOf]
  rw [DD_pEl h]
  congr 1
  · funext a i
    by_cases ha : j ≤ a.val
    · simp only [dif_pos ha]
    · simp only [dif_neg ha, Pi.zero_apply, mul_zero]
  · funext a b
    simp only [skewM, Matrix.of_apply]
    by_cases hab : a < b
    · simp only [dif_pos hab]
      by_cases ha : j ≤ a.val
      · simp only [dif_pos ha]; ring
      · simp only [dif_neg ha]; ring
    · simp only [dif_neg hab]
      by_cases hba : b < a
      · simp only [dif_pos hba]
        by_cases hb : j ≤ b.val
        · simp only [dif_pos hb, star_mul', star_ofReal_zpow]; ring
        · simp only [dif_neg hb, star_zero, neg_zero, mul_zero, zero_mul]
      · simp only [dif_neg hba]
        have hab' : a = b := le_antisymm (not_lt.mp hba) (not_lt.mp hab)
        subst hab'
        by_cases ha : j ≤ a.val
        · simp only [dif_pos ha]; push_cast; ring
        · simp only [dif_neg ha]; push_cast; ring

theorem DD_range {ε : ℝ} (h : ε ≠ 0) (j : ℕ) (β : Fin r → ℕ) {x : Mat k r} (hx : x ∈ Set.range (rEl k r j β)) :
    DD k r ε * x * (DD k r ε)⁻¹ ∈ Set.range (rEl k r j β) := by
  obtain ⟨q, rfl⟩ := hx
  obtain ⟨x1, hx1⟩ := DD_uEmb (k := k) h β q.1
  obtain ⟨q2, hq2⟩ := DD_pTop (k := k) h j q.2
  refine ⟨(x1, q2), ?_⟩
  have hinv : (DD k r ε)⁻¹ * DD k r ε = 1 := Matrix.nonsing_inv_mul _ (DD_unit h)
  simp only [rEl]
  rw [← hx1, ← hq2]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (DD k r ε)⁻¹ (DD k r ε), hinv, Matrix.one_mul]

theorem rEl_ee (j : ℕ) (β : Fin r → ℕ) (q : (UTin β → ℂ) × PTop k r j) (a b : Fin r) :
    rEl k r j β q (eI k r a) (eI k r b) = upperIn β q.1 a b := by
  have hcol : ∀ c, pTop k r j q.2 c (eI k r b) = if c = eI k r b then 1 else 0 := by
    intro c
    refine Rad.cases3 (P := fun c => pTop k r j q.2 c (eI k r b) = if c = eI k r b then 1 else 0) ?_ ?_ ?_ c
    · intro a'
      simp only [pTop, pOf, Rad.pEl_ee, Rad.eI_inj]
    · intro m
      simp only [pTop, pOf, Rad.pEl_we, Rad.wI_ne_eI, if_false]
    · intro a'
      simp only [pTop, pOf, Rad.pEl_se, Rad.esI_ne_eI, if_false]
  simp only [rEl, Matrix.mul_apply, hcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true, UEmb.u_ee]

theorem block_of_subset (j : ℕ) {β β' : Fin r → ℕ} (h : Set.range (rEl k r j β) ⊆ Set.range (rEl k r j β'))
    (p : UT r) (hp : β p.1.1 = β p.1.2) : β' p.1.1 = β' p.1.2 := by
  classical
  obtain ⟨q', hq'⟩ := h ⟨((fun s : UTin β => if s.1.1 = p.1 then (1 : ℂ) else 0), 0), rfl⟩
  have e := congrFun (congrFun hq' (eI k r p.1.1)) (eI k r p.1.2)
  rw [rEl_ee, rEl_ee] at e
  by_contra hne
  simp [upperIn, upper, p.2, hp, hne] at e

noncomputable def lebP (k r j : ℕ) (P : UT r → Prop) [DecidablePred P] : Measure (Mt k r) :=
  (volume : Measure (({p : UT r // P p} → ℂ) × PTop k r j)).map fun q =>
    Matrix.of.symm (uEmb k r (upper fun p => if h : P p then q.1 ⟨p, h⟩ else 0) * pTop k r j q.2)

theorem lebesgueWeight_congr (j : ℕ) (P Q : UT r → Prop) [i : DecidablePred P] [i' : DecidablePred Q] (h : P = Q) :
    lebP k r j P = lebP k r j Q := by
  subst h
  congr

theorem leb_congr (j : ℕ) {β β' : Fin r → ℕ} (h : Set.range (rEl k r j β) = Set.range (rEl k r j β')) :
    lebR0 k r j β = lebR0 k r j β' := by
  have e : (fun p : UT r => β p.1.1 = β p.1.2) = (fun p : UT r => β' p.1.1 = β' p.1.2) := by
    funext p
    exact propext ⟨block_of_subset j h.le p, block_of_subset j h.ge p⟩
  show lebP k r j (fun p : UT r => β p.1.1 = β p.1.2) = lebP k r j (fun p : UT r => β' p.1.1 = β' p.1.2)
  exact lebesgueWeight_congr j _ _ e

theorem DD_iff {ε : ℝ} (h : ε ≠ 0) (j : ℕ) (β : Fin r → ℕ) (x : Mat k r) :
    x ∈ Set.range (rEl k r j β) ↔ DD k r ε * x * (DD k r ε)⁻¹ ∈ Set.range (rEl k r j β) := by
  constructor
  · exact DD_range h j β
  · intro hy
    have h' : ε⁻¹ ≠ 0 := inv_ne_zero h
    have hm : DD k r ε⁻¹ * DD k r ε = 1 := by simpa only [inv_inv] using DD_mul (k := k) (r := r) h'
    have hy2 := DD_range h' j β hy
    rw [DD_inv h', inv_inv, DD_inv h] at hy2
    have e : DD k r ε⁻¹ * (DD k r ε * x * DD k r ε⁻¹) * DD k r ε = x := by
      rw [show DD k r ε⁻¹ * (DD k r ε * x * DD k r ε⁻¹) * DD k r ε =
          (DD k r ε⁻¹ * DD k r ε) * x * (DD k r ε⁻¹ * DD k r ε) by simp only [Matrix.mul_assoc], hm,
        Matrix.one_mul, Matrix.mul_one]
    rw [e] at hy2
    exact hy2

theorem tendsto_DD_inv {n : Mat k r} (hn : n ∈ Nset k r) :
    Tendsto (fun m => (DD k r (ep m) * n * (DD k r (ep m))⁻¹)⁻¹) atTop (𝓝 1) := by
  have hinv : n⁻¹ ∈ Nset k r := (Formalism.QuantumDeterminants.nSubgroup k r).2.2 n hn
  have he : ∀ m : ℕ, (DD k r (ep m) * n * (DD k r (ep m))⁻¹)⁻¹ = DD k r (ep m) * n⁻¹ * (DD k r (ep m))⁻¹ := by
    intro m
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (DD_unit (ep_ne m)), Matrix.mul_assoc]
  exact (tendsto_congr he).2 (tendsto_DD hinv)

private theorem DD_conj_conj_mem_range_rEl_of_conj_mem (j : ℕ) {β β' : Fin r → ℕ} {n : Mat k r}
    (h : ∀ x ∈ Set.range (rEl k r j β), n * x * n⁻¹ ∈ Set.range (rEl k r j β')) {ε : ℝ} (hε : ε ≠ 0)
    {x : Mat k r} (hx : x ∈ Set.range (rEl k r j β)) :
    DD k r ε * n * (DD k r ε)⁻¹ * x * (DD k r ε * n * (DD k r ε)⁻¹)⁻¹ ∈ Set.range (rEl k r j β') := by
  have hu : IsUnit (DD k r ε).det := DD_unit hε
  have hy : (DD k r ε)⁻¹ * x * DD k r ε ∈ Set.range (rEl k r j β) := by
    rw [DD_iff hε j β]
    have e : DD k r ε * ((DD k r ε)⁻¹ * x * DD k r ε) * (DD k r ε)⁻¹ = x := by
      simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    rw [e]; exact hx
  have h2 := (DD_iff hε j β' _).mp (h _ hy)
  have e2 : DD k r ε * (n * ((DD k r ε)⁻¹ * x * DD k r ε) * n⁻¹) * (DD k r ε)⁻¹ =
      DD k r ε * n * (DD k r ε)⁻¹ * x * (DD k r ε * n * (DD k r ε)⁻¹)⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu]
    simp only [Matrix.mul_assoc]
  rw [← e2]; exact h2

theorem range_subset (j : ℕ) {β β' : Fin r → ℕ} {n : Mat k r} (hn : n ∈ Nset k r)
    (hcl : IsClosed (Set.range (rEl k r j β')))
    (h : ∀ x ∈ Set.range (rEl k r j β), n * x * n⁻¹ ∈ Set.range (rEl k r j β')) :
    Set.range (rEl k r j β) ⊆ Set.range (rEl k r j β') := by
  intro x hx
  have hmem : ∀ m, DD k r (ep m) * n * (DD k r (ep m))⁻¹ * x * (DD k r (ep m) * n * (DD k r (ep m))⁻¹)⁻¹ ∈
      Set.range (rEl k r j β') := fun m => DD_conj_conj_mem_range_rEl_of_conj_mem j h (ep_ne m) hx
  have ht : Tendsto (fun m => DD k r (ep m) * n * (DD k r (ep m))⁻¹ * x *
      (DD k r (ep m) * n * (DD k r (ep m))⁻¹)⁻¹) atTop (𝓝 (1 * x * 1)) :=
    ((tendsto_DD hn).mul tendsto_const_nhds).mul (tendsto_DD_inv hn)
  rw [Matrix.one_mul, Matrix.mul_one] at ht
  exact hcl.mem_of_tendsto ht (Filter.Eventually.of_forall hmem)

private theorem map_conjM_conj_smul_eq_of_map_conjM_smul_eq {R : Set (Mat k r)} (hGm : PI.IsMatGroup R) (ν : Measure (Mt k r))
    (hν : IsHaarOn R ν) {D n : Mat k r} (hD : IsUnit D.det) (hR : ∀ x, x ∈ R ↔ D⁻¹ * x * D⁻¹⁻¹ ∈ R)
    (s s' : ℝ≥0∞) (h : (s • ν).map (conjM n) = s' • ν) : (s • ν).map (conjM (D * n * D⁻¹)) = s' • ν := by
  obtain ⟨huniq, -, -⟩ := GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ R ν hGm hν
  obtain ⟨c, -, -, hc⟩ := huniq _ (haar_conj D⁻¹ (Matrix.isUnit_nonsing_inv_det D hD) hR hν)
  have hback : (ν.map (conjM D⁻¹)).map (conjM D) = ν := by
    rw [map_conj_conj, Matrix.mul_nonsing_inv D hD, conj_one, Measure.map_id]
  calc (s • ν).map (conjM (D * n * D⁻¹))
      = (((s • ν).map (conjM D⁻¹)).map (conjM n)).map (conjM D) := by
        rw [map_conj_conj, map_conj_conj]
    _ = ((c • (s • ν)).map (conjM n)).map (conjM D) := by
        rw [Measure.map_smul s ν (conjM D⁻¹), hc, smul_comm s c ν]
    _ = (c • (s' • ν)).map (conjM D) := by
        rw [Measure.map_smul c (s • ν) (conjM n), h]
    _ = s' • (c • ν).map (conjM D) := by
        rw [Measure.map_smul c (s' • ν), Measure.map_smul s' ν, Measure.map_smul c ν, smul_comm c s']
    _ = s' • ν := by
        rw [← hc, hback]

theorem le_of_conj (j : ℕ) {β : Fin r → ℕ} {n : Mat k r} (hn : n ∈ Nset k r) (ν : Measure (Mt k r))
    (hG : IsClosedSub k r (Set.range (rEl k r j β))) (hν : IsHaarOn (Set.range (rEl k r j β)) ν) (s s' : ℝ≥0∞)
    (h : (s • ν).map (conjM n) = s' • ν) : s ≤ s' := by
  have hGm := matGroup hG
  obtain ⟨-, hfin, hpos⟩ := GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ _ ν hGm hν
  have hnull : ν {x | Matrix.of x ∉ Set.range (rEl k r j β)} = 0 := hν.2.2.1
  let U : Set (Mt k r) := Metric.ball (fun a b => (1 : Mat k r) a b) 1
  have hUo : IsOpen U := Metric.isOpen_ball
  have hUpos : 0 < ν U := hpos U hUo ⟨fun a b => (1 : Mat k r) a b, Metric.mem_ball_self one_pos, hG.2.2.1⟩
  have hRc : IsClosed {x : Mt k r | Matrix.of x ∈ Set.range (rEl k r j β)} := hG.2.1
  have hK : IsCompact (Metric.closedBall (fun a b => (1 : Mat k r) a b) 1 ∩
      {x : Mt k r | Matrix.of x ∈ Set.range (rEl k r j β)}) :=
    (isCompact_closedBall _ _).inter_right hRc
  have hUfin : ν U < ⊤ := by
    calc ν U ≤ ν (U ∩ {x : Mt k r | Matrix.of x ∈ Set.range (rEl k r j β)}) +
          ν (U \ {x : Mt k r | Matrix.of x ∈ Set.range (rEl k r j β)}) := measure_le_inter_add_sdiff _ _ _
      _ ≤ ν (Metric.closedBall (fun a b => (1 : Mat k r) a b) 1 ∩
            {x : Mt k r | Matrix.of x ∈ Set.range (rEl k r j β)}) + 0 :=
          add_le_add (measure_mono (Set.inter_subset_inter_left _ Metric.ball_subset_closedBall))
            (le_of_eq (measure_mono_null (fun x hx => hx.2) hnull))
      _ < ⊤ := by
          rw [add_zero]
          exact hfin _ hK (fun x hx => hx.2)
  have key : ∀ m, (s • ν).map (conjM (DD k r (ep m) * n * (DD k r (ep m))⁻¹)) = s' • ν := by
    intro m
    have hε := ep_ne m
    refine map_conjM_conj_smul_eq_of_map_conjM_smul_eq hGm ν hν (DD_unit hε) ?_ s s' h
    intro x
    rw [DD_inv hε]
    exact DD_iff (inv_ne_zero hε) j β x
  have hle := le_of_tendsto_conj (s • ν) U hUo (fun m => DD k r (ep m) * n * (DD k r (ep m))⁻¹)
    (tendsto_DD hn) (tendsto_DD_inv hn) ((s' • ν) U)
    (fun i => le_of_eq (congrArg (fun μ : Measure (Mt k r) => μ U) (key i)))
  simp only [Measure.smul_apply, smul_eq_mul] at hle
  first
  | exact (ENNReal.mul_le_mul_right hUpos.ne' hUfin.ne).mp hle
  | exact (ENNReal.mul_le_mul_iff_left hUpos.ne' hUfin.ne).mp hle
  | exact le_of_mul_le_mul_right hle hUpos

private theorem conj_mem_Rset_of_two_Nset_decompositions {γ g₀ g₀' n₁ n₂ m₁ m₂ : Mat k r} (hn₁ : n₁ ∈ Nset k r)
    (hn₂ : n₂ ∈ Nset k r) (hm₁ : m₁ ∈ Nset k r) (hm₂ : m₂ ∈ Nset k r) (hγ : γ = n₁ * g₀ * n₂)
    (hγ' : γ = m₁ * g₀' * m₂) {x : Mat k r} (hx : x ∈ Rset k r g₀) :
    m₂ * n₂⁻¹ * x * (m₂ * n₂⁻¹)⁻¹ ∈ Rset k r g₀' := by
  have hu₂ : IsUnit n₂.det := unit_of_GG hn₂.1
  have h1 : n₂⁻¹ * x * n₂ ∈ Rset k r γ := by
    rw [hγ, Rset_conj g₀ hn₁ hn₂]
    have e : n₂ * (n₂⁻¹ * x * n₂) * n₂⁻¹ = x := by
      simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu₂, Matrix.one_mul]
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu₂, Matrix.mul_one]
    rw [e]; exact hx
  rw [hγ', Rset_conj g₀' hm₁ hm₂] at h1
  have e2 : m₂ * (n₂⁻¹ * x * n₂) * m₂⁻¹ = m₂ * n₂⁻¹ * x * (m₂ * n₂⁻¹)⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu₂]
    simp only [Matrix.mul_assoc]
  rw [← e2]; exact h1

theorem normalFormStabilizerMeasure_scalar_le {j : ℕ} (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) (s s' : ℝ) (μ : Measure (Mt k r))
    (h : IsNormalFormStabilizerMeasure k r hj z z' γ s μ) (h' : IsNormalFormStabilizerMeasure k r hj z z' γ s' μ) : ENNReal.ofReal s ≤ ENNReal.ofReal s' := by
  obtain ⟨hz, hz', hT, n₁, hn₁, n₂, hn₂, g₀, β, c, hg₀, hγ, hμ⟩ := h
  obtain ⟨-, -, -, m₁, hm₁, m₂, hm₂, g₀', β', c', hg₀', hγ', hμ'⟩ := h'
  obtain ⟨hR, hcl⟩ := GlobalTheory.T.commonStabilizerSet_eq_range_normalForm k r j hj z z' g₀ β c hz hz' hT hg₀
  obtain ⟨hR', hcl'⟩ := GlobalTheory.T.commonStabilizerSet_eq_range_normalForm k r j hj z z' g₀' β' c' hz hz' hT hg₀'
  obtain ⟨hH, -⟩ := GlobalTheory.T.stabilizer_haar_unimodular_normal k r j hj z z' g₀ β c hz hz' hT hg₀
  obtain ⟨-, hNmul, hNinv⟩ := nSubgroup k r
  have hv₂ : IsUnit m₂.det := unit_of_GG hm₂.1
  have hn : m₂ * n₂⁻¹ ∈ Nset k r := hNmul _ hm₂ _ (hNinv _ hn₂)
  have hn' : n₂ * m₂⁻¹ ∈ Nset k r := hNmul _ hn₂ _ (hNinv _ hm₂)
  have hsub : Set.range (rEl k r j β) ⊆ Set.range (rEl k r j β') := by
    refine range_subset j hn ?_ ?_
    · rw [← hR']; exact hcl'.2.1
    · intro x hx
      rw [← hR] at hx
      rw [← hR']
      exact conj_mem_Rset_of_two_Nset_decompositions hn₁ hn₂ hm₁ hm₂ hγ hγ' hx
  have hsup : Set.range (rEl k r j β') ⊆ Set.range (rEl k r j β) := by
    refine range_subset j hn' ?_ ?_
    · rw [← hR]; exact hcl.2.1
    · intro x hx
      rw [← hR'] at hx
      rw [← hR]
      exact conj_mem_Rset_of_two_Nset_decompositions hm₁ hm₂ hn₁ hn₂ hγ' hγ hx
  have hL : lebR0 k r j β' = lebR0 k r j β := (leb_congr j (Set.Subset.antisymm hsub hsup)).symm
  rw [hL] at hμ'
  have key : (ENNReal.ofReal s • lebR0 k r j β).map (conjM (m₂ * n₂⁻¹)) = ENNReal.ofReal s' • lebR0 k r j β := by
    have e1 : ((ENNReal.ofReal s • lebR0 k r j β).map (conjM n₂⁻¹)).map (conjM m₂) =
        ((ENNReal.ofReal s' • lebR0 k r j β).map (conjM m₂⁻¹)).map (conjM m₂) := by rw [← hμ, ← hμ']
    rw [map_conj_conj, map_conj_conj, Matrix.mul_nonsing_inv _ hv₂, conj_one, Measure.map_id] at e1
    exact e1
  have hcl0 : IsClosedSub k r (Set.range (rEl k r j β)) := by rw [← hR]; exact hcl
  rw [hR] at hH
  exact le_of_conj j hn (lebR0 k r j β) hcl0 hH _ _ key

end GlobalTheory.Amp.StabHaar
