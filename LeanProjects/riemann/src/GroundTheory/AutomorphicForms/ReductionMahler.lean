import Mathlib
import GroundTheory.AutomorphicForms.ReductionSiegel
import GroundTheory.AutomorphicForms.QuotientMeasure

open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace Reduction

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem exists_adelicNorm_vecMul_le_mul {C : Set (AdelicGLn.AdelicGL K n)} (hC : IsCompact C) :
    ∃ P : ℝ, 0 < P ∧ ∀ g ∈ C, ∀ y : Fin n → 𝔸[K], HasFiniteContent y →
      adelicNorm (y ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K])) ≤ P * adelicNorm y := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, one_pos, fun g _ y _ => ?_⟩
    rw [one_mul, Subsingleton.elim (y ᵥ* (g : Matrix (Fin 0) (Fin 0) 𝔸[K])) y]
  obtain ⟨S, hS⟩ := exists_finite_forall_mem_integralGL hC
  have hinf : ∀ w : InfinitePlace K, ∃ m : ℝ, 1 ≤ m ∧ ∀ g ∈ C, ∀ i j : Fin n,
      ‖(infAt w g : GL (Fin n) w.Completion) i j‖ ≤ m := fun w => by
    obtain ⟨m, hm1, hm⟩ := exists_one_le_bound hC (f := fun g : AdelicGLn.AdelicGL K n =>
      ∑ i, ∑ j, ‖(infAt w g : GL (Fin n) w.Completion) i j‖)
      (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        ((continuous_GL_apply i j).comp (continuous_infAt w)).norm)
    refine ⟨m, hm1, fun g hg i j => le_trans ?_ (hm g hg)⟩
    exact (Finset.single_le_sum (f := fun j => ‖(infAt w g : GL (Fin n) w.Completion) i j‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖(infAt w g : GL (Fin n) w.Completion) i j‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  have hfin : ∀ v : HeightOneSpectrum (𝓞 K), ∃ m : ℝ, 1 ≤ m ∧ ∀ g ∈ C, ∀ i j : Fin n,
      ‖(finAt v g : GL (Fin n) (v.adicCompletion K)) i j‖ ≤ m := fun v => by
    obtain ⟨m, hm1, hm⟩ := exists_one_le_bound hC (f := fun g : AdelicGLn.AdelicGL K n =>
      ∑ i, ∑ j, ‖(finAt v g : GL (Fin n) (v.adicCompletion K)) i j‖)
      (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        ((continuous_GL_apply i j).comp (continuous_finAt v)).norm)
    refine ⟨m, hm1, fun g hg i j => le_trans ?_ (hm g hg)⟩
    exact (Finset.single_le_sum (f := fun j => ‖(finAt v g : GL (Fin n) (v.adicCompletion K)) i j‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖(finAt v g : GL (Fin n) (v.adicCompletion K)) i j‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  choose a ha1 ha using hinf
  choose b hb1 hb using hfin
  set b' : HeightOneSpectrum (𝓞 K) → ℝ := fun v => if v ∈ S then b v else 1 with hb'
  set P : ℝ := (∏ w, (√n * (n * a w)) ^ w.mult) * ∏ v ∈ S, b' v with hP
  have hPpos : 0 < P := by
    refine mul_pos (Finset.prod_pos fun w _ => pow_pos ?_ _) (Finset.prod_pos fun v hv => ?_)
    · have : (0 : ℝ) < n := Nat.cast_pos.2 hn
      exact mul_pos (Real.sqrt_pos.2 this) (mul_pos this (lt_of_lt_of_le one_pos (ha1 w)))
    · rw [hb']
      dsimp only
      rw [if_pos hv]
      exact lt_of_lt_of_le one_pos (hb1 v)
  refine ⟨P, hPpos, fun g hg y hy => ?_⟩
  refine (adelicNorm_le_of_local (hy.vecMul g) hy (fun w => √n * (n * a w)) b' S (fun w => ?_)
    (fun v hv => by rw [hb']; dsimp only; rw [if_neg hv]) (fun v => ?_)).trans (le_of_eq rfl)
  · rw [infComp_vecMul_GL]
    exact euclidNorm_vecMul_le (zero_le_one.trans (ha1 w)) (ha w g hg) _
  · rw [finComp_vecMul_GL, hb']
    dsimp only
    split_ifs with hv
    · exact norm_vecMul_le_of_norm_le v (zero_le_one.trans (hb1 v)) (hb v g hg) _
    · rw [norm_vecMul_integralGL v (hS g hg v hv), one_mul]

variable (K n) in

def normOneGL : Subgroup (AdelicGLn.AdelicGL K n) :=
  (normOneSubgroup K).comap (AdelicGLn.det K n)

theorem mem_normOneGL {g : AdelicGLn.AdelicGL K n} :
    g ∈ normOneGL K n ↔ (ideleModule K (AdelicGLn.det K n g) : ℝ) = 1 :=
  mem_normOneSubgroup

theorem isClosed_normOneGL : IsClosed (normOneGL K n : Set (AdelicGLn.AdelicGL K n)) :=
  (isClosed_normOneSubgroup K).preimage (AdelicGLn.continuous_det K n)

theorem rationalGL_le_normOneGL : AdelicGLn.rationalGL K n ≤ normOneGL K n := by
  rintro _ ⟨γ, rfl⟩
  have h : AdelicGLn.det K n (AdelicGLn.diagonal K n γ) =
      IdeleGroup.diagonal K (Matrix.GeneralLinearGroup.det γ) := by
    refine Units.ext ?_
    rw [AdelicGLn.coe_det, IdeleGroup.coe_diagonal]
    exact (RingHom.map_det (algebraMap K 𝔸[K]) (γ : Matrix (Fin n) (Fin n) K)).symm
  rw [mem_normOneGL, h, ideleModule_diagonal, Positive.val_one]

theorem maxCompact_le_normOneGL : maxCompact (K := K) (n := n) ≤ normOneGL K n := by
  intro k hk
  set f : AdelicGLn.AdelicGL K n →* {r : ℝ // 0 < r} := (ideleModule K).comp (AdelicGLn.det K n)
    with hf
  have hfc : Continuous fun g => (f g : ℝ) :=
    continuous_subtype_val.comp (continuous_ideleModule.comp (AdelicGLn.continuous_det K n))
  obtain ⟨M, hM⟩ := (isCompact_maxCompact (K := K) (n := n)).exists_bound_of_continuousOn
    hfc.continuousOn
  have hbound : ∀ m : ℕ, (f k : ℝ) ^ m ≤ M ∧ ((f k : ℝ)⁻¹) ^ m ≤ M := fun m => by
    have h1 := hM (k ^ m) (pow_mem hk m)
    have h2 := hM ((k⁻¹) ^ m) (pow_mem (inv_mem hk) m)
    rw [map_pow, Positive.val_pow, Real.norm_eq_abs, abs_of_pos (pow_pos (f k).2 m)] at h1
    rw [map_pow, map_inv, Positive.val_pow, Positive.coe_inv, Real.norm_eq_abs,
      abs_of_pos (pow_pos (inv_pos.2 (f k).2) m)] at h2
    exact ⟨h1, h2⟩
  rw [mem_normOneGL]
  show (f k : ℝ) = 1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : 1 < (f k : ℝ)⁻¹ := (one_lt_inv₀ (f k).2).2 hlt
    obtain ⟨m, hm⟩ := (tendsto_pow_atTop_atTop_of_one_lt h1).eventually_gt_atTop M |>.exists
    exact absurd (hbound m).2 (not_le.2 hm)
  · obtain ⟨m, hm⟩ := (tendsto_pow_atTop_atTop_of_one_lt hgt).eventually_gt_atTop M |>.exists
    exact absurd (hbound m).1 (not_le.2 hm)

theorem exists_pos_le_height_of_subset {C : Set (AdelicGLn.AdelicGL K n)} (hC : IsCompact C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ (AdelicGLn.rationalGL K n : Set (AdelicGLn.AdelicGL K n)) * C,
      ∀ x : Fin n → K, x ≠ 0 → ε ≤ height g x := by
  obtain ⟨ε, hε, h⟩ := exists_pos_le_height hC
  refine ⟨ε, hε, ?_⟩
  rintro _ ⟨_, ⟨γ, rfl⟩, c, hc, rfl⟩ x hx
  rw [height_diagonal_mul]
  refine h c hc _ fun h0 => hx ?_
  have := congrArg (fun y => y ᵥ* ((γ⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) h0
  simpa [vecMul_vecMul, ← Units.val_mul] using this

theorem ratVec_single_one (j : Fin n) :
    ratVec (Pi.single j (1 : K)) = (Pi.single j (1 : 𝔸[K]) : Fin n → 𝔸[K]) := by
  ext l
  by_cases hl : l = j
  · subst hl; simp [ratVec]
  · simp [ratVec, Pi.single_eq_of_ne hl]

theorem pow_mul_le_of_chain {m : ℕ} {r : Fin (m + 1) → ℝ} {t s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hst : s ≤ t) (hr : ∀ i, 0 < r i) (h : ∀ i j : Fin (m + 1), (j : ℕ) = i + 1 → t * r j ≤ r i)
    (i : Fin (m + 1)) : s ^ m * r (Fin.last m) ≤ r i := by
  have key : ∀ k : ℕ, ∀ i : Fin (m + 1), (i : ℕ) + k = m → s ^ k * r (Fin.last m) ≤ r i := by
    intro k
    induction k with
    | zero =>
      intro i hi
      have : i = Fin.last m := Fin.ext (by simpa using hi)
      simp [this]
    | succ k ih =>
      intro i hi
      have hj : (i : ℕ) + 1 < m + 1 := by omega
      have h1 := ih ⟨i + 1, hj⟩ (by simp; omega)
      have h2 := h i ⟨i + 1, hj⟩ rfl
      calc s ^ (k + 1) * r (Fin.last m) = s * (s ^ k * r (Fin.last m)) := by ring
        _ ≤ s * r ⟨i + 1, hj⟩ := mul_le_mul_of_nonneg_left h1 hs0
        _ ≤ t * r ⟨i + 1, hj⟩ := mul_le_mul_of_nonneg_right hst (hr _).le
        _ ≤ r i := h2
  have := key (m - i) i (by have := i.isLt; omega)
  refine le_trans (mul_le_mul_of_nonneg_right ?_ (hr _).le) this
  exact pow_le_pow_of_le_one hs0 hs1 (by omega)

theorem continuous_posIdele_subtype :
    Continuous fun r : {r : ℝ // 0 < r} => (posIdele (K := K) r.1 r.2 : IdeleGroup K) := by
  unfold posIdele
  exact continuous_finsetProd _ fun w _ => (continuous_moduleSection w).comp
    (Continuous.subtype_mk ((continuous_subtype_val).pow _) _)

theorem isCompact_torusBox {L U : ℝ} (hL : 0 < L) :
    IsCompact ((fun r : Fin n → {r : ℝ // 0 < r} =>
      diagUnits n (fun i => posIdele (K := K) (r i).1 (r i).2)) ''
        (Set.pi univ fun _ => {r : {r : ℝ // 0 < r} | r.1 ∈ Icc L U})) := by
  refine IsCompact.image (isCompact_univ_pi fun _ => ?_) ((continuous_diagUnits n).comp
    (continuous_pi fun i => continuous_posIdele_subtype.comp (continuous_apply i)))
  rw [Subtype.isCompact_iff]
  have : Subtype.val '' {r : {r : ℝ // 0 < r} | r.1 ∈ Icc L U} = Icc L U := by
    ext x
    exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ hy, fun hx => ⟨⟨x, lt_of_lt_of_le hL hx.1⟩, hx, rfl⟩⟩
  rw [this]
  exact isCompact_Icc

theorem det_diagUnits (f : Fin n → IdeleGroup K) :
    AdelicGLn.det K n (diagUnits n f) = ∏ i, f i := by
  refine Units.ext ?_
  rw [AdelicGLn.coe_det, coe_diagUnits, det_diagonal, Units.coe_prod]

theorem coe_finset_prod_pos {ι : Type*} (s : Finset ι) (f : ι → {r : ℝ // 0 < r}) :
    ((∏ i ∈ s, f i : {r : ℝ // 0 < r}) : ℝ) = ∏ i ∈ s, (f i : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Positive.val_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Positive.val_mul, ih]

theorem exists_isCompact_forall_of_pos_le_height {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Set (AdelicGLn.AdelicGL K n), IsCompact C ∧ ∀ g ∈ normOneGL K n,
      (∀ x : Fin n → K, x ≠ 0 → ε ≤ height g x) →
        g ∈ (AdelicGLn.rationalGL K n : Set (AdelicGLn.AdelicGL K n)) * C := by
  classical
  cases n with
  | zero =>
    refine ⟨{1}, isCompact_singleton, fun g _ _ => ⟨1, one_mem _, 1, rfl, ?_⟩⟩
    exact Units.ext (Subsingleton.elim _ _)
  | succ m =>
    obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := exists_siegelSet (K := K) (m + 1)
    obtain ⟨P, hP, hPle⟩ := exists_adelicNorm_vecMul_le_mul hω
    obtain ⟨m₀, hm₀, hm₀le⟩ : ∃ m₀ : ℝ, 0 < m₀ ∧
        ∀ b ∈ ω, m₀ ≤ (ideleModule K (AdelicGLn.det K _ b) : ℝ) := by
      rcases ω.eq_empty_or_nonempty with he | hne
      · exact ⟨1, one_pos, fun b hb => by rw [he] at hb; exact hb.elim⟩
      · obtain ⟨b₀, -, hmin⟩ := hω.exists_isMinOn hne (continuous_subtype_val.comp
          (continuous_ideleModule.comp (AdelicGLn.continuous_det K _))).continuousOn
        exact ⟨_, (ideleModule K (AdelicGLn.det K _ b₀)).2, fun b hb => hmin hb⟩
    set d : ℕ := Module.finrank ℚ K with hd
    have hd0 : 0 < d := Module.finrank_pos
    set s : ℝ := min t 1 with hs
    have hs0 : 0 < s := lt_min ht one_pos
    set Lρ : ℝ := (s ^ m) ^ d * (ε / P) with hLρ
    have hLρ0 : 0 < Lρ := by positivity
    set Uρ : ℝ := m₀⁻¹ / Lρ ^ m with hUρ
    set Lb : ℝ := min 1 Lρ with hLb
    set Ub : ℝ := max 1 Uρ with hUb
    set box : Set (AdelicGLn.AdelicGL K (m + 1)) := (fun r : Fin (m + 1) → {r : ℝ // 0 < r} =>
        diagUnits (m + 1) (fun i => posIdele (K := K) (r i).1 (r i).2)) ''
        (Set.pi univ fun _ => {r : {r : ℝ // 0 < r} | r.1 ∈ Icc Lb Ub}) with hbox
    have hboxc : IsCompact box := isCompact_torusBox (lt_min one_pos hLρ0)
    have hC : IsCompact ((ω * box) * (maxCompact (K := K) (n := m + 1) :
        Set (AdelicGLn.AdelicGL K (m + 1)))) :=
      (hω.mul hboxc).mul (isCompact_maxCompact (K := K) (n := m + 1))
    refine ⟨(ω * box) * (maxCompact (K := K) (n := m + 1) : Set (AdelicGLn.AdelicGL K (m + 1))),
      hC, fun g hg hgε => ?_⟩
    obtain ⟨γ, b, hbω, a, ⟨r, hr, hratio, rfl⟩, k, hk, heq⟩ := hsieg g
    have hb : b ∈ adelicBorel := hωB hbω
    set l : Fin (m + 1) := Fin.last m with hl
    have hbl : IsUnit ((b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔸[K]) l l) :=
      isUnit_apply_self_of_mem_adelicBorel hb l
    have hrow : (Pi.single l (1 : 𝔸[K]) : Fin (m + 1) → 𝔸[K]) ᵥ*
        (b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔸[K]) =
        Pi.single l ((b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔸[K]) l l) := by
      rw [single_one_vecMul]
      ext j
      by_cases hj : j = l
      · subst hj; simp [Matrix.row]
      · have hjl : j < l := lt_of_le_of_ne (Fin.le_last j) hj
        have h0 : (b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔸[K]) l j = 0 := hb hjl
        simp [Matrix.row, Pi.single_eq_of_ne hj, h0]

    have hbP : (ideleModule K hbl.unit : ℝ) ≤ P := by
      have h1 := hPle b hbω _ (hasFiniteContent_single_one (K := K) l)
      rw [hrow, adelicNorm_single_one, mul_one, ← IsUnit.unit_spec hbl,
        adelicNorm_single_units] at h1
      exact h1

    set x₀ : Fin (m + 1) → K := Pi.single l 1 ᵥ* (γ : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
      with hx₀
    have hx₀0 : x₀ ≠ 0 := by
      intro h0
      have h1 : (Pi.single l (1 : K) : Fin (m + 1) → K) = 0 := by
        have h3 : x₀ ᵥ* ((γ⁻¹ : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
            Pi.single l 1 := by
          rw [hx₀, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
        rw [← h3, h0, zero_vecMul]
      have h2 := congrFun h1 l
      simp at h2
    have hh := hgε x₀ hx₀0
    rw [hx₀, ← height_diagonal_mul, heq, height_mul_maxCompact _ hk, height, Units.val_mul,
      ← vecMul_vecMul, ratVec_single_one, hrow, coe_diagUnits, single_vecMul_diagonal,
      ← IsUnit.unit_spec hbl, ← Units.val_mul, adelicNorm_single_units, map_mul, Positive.val_mul,
      ideleModule_posIdele] at hh
    have hrl : ε / P ≤ r l ^ d := by
      rw [div_le_iff₀ hP]
      calc ε ≤ (ideleModule K hbl.unit : ℝ) * r l ^ d := hh
        _ ≤ P * r l ^ d := mul_le_mul_of_nonneg_right hbP (pow_nonneg (hr l).le _)
        _ = r l ^ d * P := mul_comm _ _

    have hlow : ∀ i, Lρ ≤ r i ^ d := fun i => by
      have h1 := pow_mul_le_of_chain hs0.le (min_le_right _ _) (min_le_left _ _) hr hratio i
      calc Lρ = (s ^ m) ^ d * (ε / P) := rfl
        _ ≤ (s ^ m) ^ d * r l ^ d :=
          mul_le_mul_of_nonneg_left hrl (pow_nonneg (pow_nonneg hs0.le _) _)
        _ = (s ^ m * r l) ^ d := (mul_pow _ _ _).symm
        _ ≤ r i ^ d := pow_le_pow_left₀ (mul_nonneg (pow_nonneg hs0.le _) (hr l).le) h1 _

    have hba : b * diagUnits (m + 1) (fun i => posIdele (r i) (hr i)) ∈ normOneGL K (m + 1) := by
      have : b * diagUnits (m + 1) (fun i => posIdele (r i) (hr i)) =
          AdelicGLn.diagonal K _ γ * g * k⁻¹ := by rw [heq]; group
      rw [this]
      exact mul_mem (mul_mem (rationalGL_le_normOneGL ⟨γ, rfl⟩) hg)
        (inv_mem (maxCompact_le_normOneGL hk))
    rw [mem_normOneGL, map_mul, det_diagUnits, map_mul, map_prod, Positive.val_mul,
      coe_finset_prod_pos] at hba
    simp only [ideleModule_posIdele] at hba
    have hprod : ∏ i, r i ^ d ≤ m₀⁻¹ := by
      rw [← hd] at hba
      have h1 := hm₀le b hbω
      rw [le_inv_comm₀ (Finset.prod_pos fun i _ => pow_pos (hr i) _) hm₀]
      calc m₀ ≤ (ideleModule K (AdelicGLn.det K _ b) : ℝ) := h1
        _ = (∏ i, r i ^ d)⁻¹ := by
          exact eq_inv_of_mul_eq_one_left hba
    have hup : ∀ i, r i ^ d ≤ Uρ := fun i => by
      rw [hUρ, le_div_iff₀ (pow_pos hLρ0 _)]
      calc r i ^ d * Lρ ^ m ≤ r i ^ d * ∏ j ∈ Finset.univ.erase i, r j ^ d := by
            refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (hr i).le _)
            calc Lρ ^ m = ∏ _j ∈ Finset.univ.erase i, Lρ := by
                  rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
                    Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]
              _ ≤ ∏ j ∈ Finset.univ.erase i, r j ^ d :=
                  Finset.prod_le_prod (fun _ _ => hLρ0.le) fun j _ => hlow j
        _ = ∏ j, r j ^ d := Finset.mul_prod_erase _ (fun j => r j ^ d) (Finset.mem_univ i)
        _ ≤ m₀⁻¹ := hprod
    have hbox : ∀ i, r i ∈ Icc Lb Ub := fun i => by
      constructor
      · rcases le_or_gt 1 (r i) with h | h
        · exact (min_le_left _ _).trans h
        · exact (min_le_right _ _).trans ((hlow i).trans (pow_le_of_le_one (hr i).le h.le hd0.ne'))
      · rcases le_or_gt (r i) 1 with h | h
        · exact h.trans (le_max_left _ _)
        · exact (le_self_pow₀ h.le hd0.ne').trans ((hup i).trans (le_max_right _ _))
    refine ⟨(AdelicGLn.diagonal K _ γ)⁻¹, ⟨γ⁻¹, map_inv _ _⟩, _, ⟨_, ⟨b, hbω, _,
      ⟨fun i => ⟨r i, hr i⟩, fun i _ => hbox i, rfl⟩, rfl⟩, k, hk, rfl⟩, ?_⟩
    dsimp only
    rw [← heq, inv_mul_cancel_left]

theorem exists_isCompact_subset_iff {Y : Set (AdelicGLn.AdelicGL K n)}
    (hY : Y ⊆ (normOneGL K n : Set (AdelicGLn.AdelicGL K n))) :
    (∃ C : Set (AdelicGLn.AdelicGL K n), IsCompact C ∧
      Y ⊆ (AdelicGLn.rationalGL K n : Set (AdelicGLn.AdelicGL K n)) * C) ↔
    ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ Y, ∀ x : Fin n → K, x ≠ 0 → ε ≤ height g x := by
  constructor
  · rintro ⟨C, hC, hYC⟩
    obtain ⟨ε, hε, h⟩ := exists_pos_le_height_of_subset hC
    exact ⟨ε, hε, fun g hg => h g (hYC hg)⟩
  · rintro ⟨ε, hε, h⟩
    obtain ⟨C, hC, hC'⟩ := exists_isCompact_forall_of_pos_le_height (K := K) (n := n) hε
    exact ⟨C, hC, fun g hg => hC' g (hY hg) (h g hg)⟩

variable (K n) in

abbrev rationalGLOne : Subgroup (normOneGL K n) :=
  (AdelicGLn.rationalGL K n).subgroupOf (normOneGL K n)

instance locallyCompactSpace_normOneGL : LocallyCompactSpace (normOneGL K n) :=
  isClosed_normOneGL.isClosedEmbedding_subtypeVal.locallyCompactSpace

instance discreteTopology_rationalGLOne : DiscreteTopology (rationalGLOne K n) := by
  have := AdelicGLn.discreteTopology_rationalGL K n
  let f : rationalGLOne K n → AdelicGLn.rationalGL K n := fun x => ⟨(x : normOneGL K n), x.2⟩
  refine DiscreteTopology.of_continuous_injective (f := f) ?_ ?_
  · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  · intro x y hxy
    have h1 := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h1)

theorem isCompact_closure_mk_image_iff {Y : Set (normOneGL K n)} :
    IsCompact (closure (RightCosetSpace.mk (rationalGLOne K n) '' Y)) ↔
      ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ Y, ∀ x : Fin n → K, x ≠ 0 →
        ε ≤ height (g : AdelicGLn.AdelicGL K n) x := by
  constructor
  · intro hc
    obtain ⟨D, hD, hKD⟩ := RightCosetSpace.exists_isCompact_subset_mk_image _ hc
    obtain ⟨ε, hε, h⟩ := exists_pos_le_height_of_subset (hD.image continuous_subtype_val)
    refine ⟨ε, hε, fun g hg x hx => h _ ?_ x hx⟩
    obtain ⟨d, hdD, hd⟩ := hKD (subset_closure ⟨g, hg, rfl⟩)
    obtain ⟨γ, hγ⟩ := (RightCosetSpace.mk_eq_mk_iff).1 hd
    refine ⟨((γ⁻¹ : rationalGLOne K n) : normOneGL K n), (γ⁻¹ : rationalGLOne K n).2, d, ⟨d, hdD, rfl⟩, ?_⟩
    rw [← hγ]
    change (((γ : normOneGL K n) : AdelicGLn.AdelicGL K n))⁻¹ *
      ((γ : normOneGL K n) * g : AdelicGLn.AdelicGL K n) = g
    rw [inv_mul_cancel_left]
  · rintro ⟨ε, hε, h⟩
    obtain ⟨C, hC, hC'⟩ := exists_isCompact_forall_of_pos_le_height (K := K) (n := n) hε
    set D : Set (normOneGL K n) := Subtype.val ⁻¹' C with hD
    have hDc : IsCompact D := isClosed_normOneGL.isClosedEmbedding_subtypeVal.isCompact_preimage hC
    have hsub : RightCosetSpace.mk (rationalGLOne K n) '' Y ⊆
        RightCosetSpace.mk (rationalGLOne K n) '' D := by
      rintro _ ⟨g, hg, rfl⟩
      obtain ⟨_, ⟨γ, rfl⟩, c, hc, hgc⟩ := hC' g g.2 (h g hg)
      have hγ1 : AdelicGLn.diagonal K n γ ∈ normOneGL K n := rationalGL_le_normOneGL ⟨γ, rfl⟩
      have hc1 : c ∈ normOneGL K n := by
        have : c = (AdelicGLn.diagonal K n γ)⁻¹ * g := by rw [← hgc, inv_mul_cancel_left]
        rw [this]
        exact mul_mem (inv_mem hγ1) g.2
      refine ⟨⟨c, hc1⟩, hc, (RightCosetSpace.mk_eq_mk_iff).2
        ⟨⟨⟨_, inv_mem hγ1⟩, ⟨γ⁻¹, map_inv _ _⟩⟩, ?_⟩⟩
      refine Subtype.ext ?_
      change (AdelicGLn.diagonal K n γ)⁻¹ * (g : AdelicGLn.AdelicGL K n) = c
      rw [← hgc]
      exact inv_mul_cancel_left _ _
    have hT2 : T2Space (RightCosetSpace (rationalGLOne K n)) := RightCosetSpace.t2Space _
    have hcl : IsClosed (RightCosetSpace.mk (rationalGLOne K n) '' D) :=
      (hDc.image (RightCosetSpace.continuous_mk _)).isClosed
    exact (hDc.image (RightCosetSpace.continuous_mk _)).of_isClosed_subset isClosed_closure
      (closure_minimal hsub hcl)

end Reduction

end

end GroundTheory.Automorphic
