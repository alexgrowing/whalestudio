import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaStdMaxParab

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open scoped Matrix Topology

noncomputable section

namespace GlobalTheory.FullRankOnto

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

local notation "Yo" => GlobalTheory.FullRankCoinv.Y0 k n d

theorem Y0_mul_apply (hnd : n ≤ d) {β : Type*} (M : Matrix (Fin d) β k) (i : Fin n) (j : β) :
    (Yo * M) i j = M ⟨d - n + i, by omega⟩ j := by
  have e : ∀ l : Fin d, ((l : ℕ) = d - n + i) ↔ l = ⟨d - n + i, by omega⟩ := fun l => by rw [Fin.ext_iff]
  simp [GlobalTheory.FullRankCoinv.Y0, Matrix.mul_apply, e]

theorem mul_Y0_apply (hnd : n ≤ d) {β : Type*} [Fintype β] (A : Matrix β (Fin n) k) (i : β) (j : Fin n) :
    (A * Yo) i ⟨d - n + j, by omega⟩ = A i j := by
  have e : ∀ l : Fin n, (d - n + (j : ℕ) = d - n + l) ↔ l = j := fun l => by rw [Fin.ext_iff]; omega
  simp [GlobalTheory.FullRankCoinv.Y0, Matrix.mul_apply, e, Fin.val_inj]

theorem mul_Y0_apply_lt {β : Type*} [Fintype β] (A : Matrix β (Fin n) k) (i : β) (j : Fin d)
    (hj : (j : ℕ) < d - n) : (A * Yo) i j = 0 := by
  simp only [GlobalTheory.FullRankCoinv.Y0, Matrix.mul_apply, Matrix.of_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  simp only [mul_ite, mul_one, mul_zero]
  rw [if_neg (by omega)]

theorem Y0_mul_transpose (hnd : n ≤ d) : Yo * (Yo)ᵀ = 1 := by
  ext i j
  rw [Y0_mul_apply hnd, transpose_apply]
  simp only [GlobalTheory.FullRankCoinv.Y0, Matrix.of_apply, Matrix.one_apply, Fin.ext_iff]
  by_cases h : (i : ℕ) = j
  · simp [h]
  · rw [if_neg (by omega), if_neg h]

def blkEquiv (hnd : n ≤ d) : Fin (d - n) ⊕ Fin n ≃ Fin d :=
  finSumFinEquiv.trans (finCongr (Nat.sub_add_cancel hnd))

theorem blkEquiv_inl (hnd : n ≤ d) (a : Fin (d - n)) : ((blkEquiv hnd (Sum.inl a) : Fin d) : ℕ) = a := by
  simp [blkEquiv]

theorem blkEquiv_inr (hnd : n ≤ d) (b : Fin n) : blkEquiv hnd (Sum.inr b) = ⟨d - n + b, by omega⟩ := by
  ext; simp [blkEquiv]

def blkMat (hnd : n ≤ d) : Matrix (Fin n) (Fin n) k →* Matrix (Fin d) (Fin d) k where
  toFun M := reindex (blkEquiv hnd) (blkEquiv hnd) (fromBlocks 1 0 0 M)
  map_one' := by simp [fromBlocks_one]
  map_mul' A B := by
    simp only [reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]
    simp

def blkGL (hnd : n ≤ d) : GL (Fin n) k →* GL (Fin d) k := Units.map (blkMat hnd)

theorem blkGL_val (hnd : n ≤ d) (g : GL (Fin n) k) :
    (blkGL hnd g).val = reindex (blkEquiv hnd) (blkEquiv hnd) (fromBlocks 1 0 0 g.val) := rfl

theorem Y0_mul_blkGL (hnd : n ≤ d) (g : GL (Fin n) k) : Yo * (blkGL hnd g).val = g.val * Yo := by
  ext i j
  rw [Y0_mul_apply hnd, blkGL_val, ← blkEquiv_inr hnd]
  obtain ⟨x, rfl⟩ := (blkEquiv hnd).surjective j
  rcases x with a | b
  · rw [mul_Y0_apply_lt _ _ _ (by rw [blkEquiv_inl]; exact a.2)]
    simp
  · rw [blkEquiv_inr hnd b, mul_Y0_apply hnd, ← blkEquiv_inr hnd]
    simp

theorem blkGL_mem_KO (hnd : n ≤ d) {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) : blkGL hnd g ∈ KO k (Fin d) := by
  have key : ∀ h : GL (Fin n) k, (∀ i j, h.val i j ∈ 𝒪[k]) → ∀ i j, (blkGL hnd h).val i j ∈ 𝒪[k] := by
    intro h hh i j
    obtain ⟨x, rfl⟩ := (blkEquiv hnd).surjective i
    obtain ⟨y, rfl⟩ := (blkEquiv hnd).surjective j
    rw [blkGL_val, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases x with a | a <;> rcases y with b | b <;> simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply]
    · rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _
    · exact zero_mem _
    · exact zero_mem _
    · exact hh a b
  rw [mem_KO_iff] at hg ⊢
  refine ⟨key g hg.1, ?_⟩
  rw [← map_inv]
  exact key g⁻¹ hg.2

def lrMat (hnd : n ≤ d) (M : Matrix (Fin d) (Fin d) k) : Matrix (Fin n) (Fin n) k :=
  Matrix.of fun i j => M ⟨d - n + i, by omega⟩ ⟨d - n + j, by omega⟩

theorem Y0_mul_parab (hnd : n ≤ d) {p : GL (Fin d) k}
    (hp : p ∈ GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.stdMaxParab k (Nat.sub_add_cancel hnd)) : Yo * p.val = lrMat hnd p.val * Yo := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.mem_stdMaxParab] at hp
  ext i j
  rw [Y0_mul_apply hnd]
  by_cases hj : (j : ℕ) < d - n
  · rw [mul_Y0_apply_lt _ _ _ hj, hp _ _ hj (by simp)]
  · have e : j = ⟨d - n + (⟨j - (d - n), by omega⟩ : Fin n), by simp; omega⟩ := by ext; simp; omega
    rw [e, mul_Y0_apply hnd]
    rfl

theorem exists_Y0_mul_parab (hnd : n ≤ d) {p : GL (Fin d) k}
    (hp : p ∈ GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.stdMaxParab k (Nat.sub_add_cancel hnd)) :
    ∃ D : GL (Fin n) k, Yo * p.val = D.val * Yo := by
  have h1 := Y0_mul_parab hnd hp
  have h2 := Y0_mul_parab hnd (inv_mem hp)
  have key : ∀ A B : Matrix (Fin n) (Fin n) k, ∀ q r : GL (Fin d) k, q * r = 1 →
      Yo * q.val = A * Yo → Yo * r.val = B * Yo → A * B = 1 := by
    intro A B q r hqr hq hr
    have : Yo = A * B * Yo := by
      calc Yo = Yo * (q * r).val := by rw [hqr]; simp
        _ = A * B * Yo := by rw [Units.val_mul, ← Matrix.mul_assoc, hq, Matrix.mul_assoc, hr, Matrix.mul_assoc]
    have := congrArg (· * (Yo)ᵀ) this
    simpa [Matrix.mul_assoc, Y0_mul_transpose hnd] using this.symm
  exact ⟨⟨_, _, key _ _ _ _ (mul_inv_cancel p) h1 h2, key _ _ _ _ (inv_mul_cancel p) h2 h1⟩, h1⟩

section Psi
open Classical in

def psi (f : GL (Fin d) k → ℂ) (Y : Matrix (Fin n) (Fin d) k) : ℂ :=
  if h : ∃ κ ∈ KO k (Fin d), Y = GlobalTheory.FullRankCoinv.Y0 k n d * κ.val then f h.choose else 0

variable {ν : kˣ →* ℂˣ} {f : GL (Fin d) k → ℂ}

theorem psi_Y0_mul (hf : f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν) {κ : GL (Fin d) k} (hκ : κ ∈ KO k (Fin d)) :
    psi f (Yo * κ.val) = f κ := by
  have hex : ∃ κ' ∈ KO k (Fin d), Yo * κ.val = Yo * κ'.val := ⟨κ, hκ, rfl⟩
  rw [psi, dif_pos hex]
  have e := hex.choose_spec.2
  set κ' := hex.choose
  have hb : Yo * (κ' * κ⁻¹).val = (1 : GL (Fin n) k).val * Yo := by
    rw [Units.val_mul, ← Matrix.mul_assoc, ← e, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]; simp
  have := hf.2 (κ' * κ⁻¹) κ 1 hb
  rw [inv_mul_cancel_right] at this
  rw [this]
  simp

theorem psi_eq_zero {Y : Matrix (Fin n) (Fin d) k} (h : ¬ ∃ κ ∈ KO k (Fin d), Y = Yo * κ.val) : psi f Y = 0 := by
  rw [psi, dif_neg h]

theorem integral_of_mul_Y0 (hnd : n ≤ d) {A : Matrix (Fin n) (Fin n) k} {M : Matrix (Fin d) (Fin d) k}
    (h : A * Yo = Yo * M) (hM : ∀ i j, M i j ∈ 𝒪[k]) : ∀ i j, A i j ∈ 𝒪[k] := by
  intro i j
  have := congrFun (congrFun h i) ⟨d - n + j, by omega⟩
  rw [mul_Y0_apply hnd, Y0_mul_apply hnd] at this
  rw [this]; exact hM _ _

theorem mem_KO_of_mul_Y0 (hnd : n ≤ d) {g : GL (Fin n) k} {κ₀ κ : GL (Fin d) k} (h₀ : κ₀ ∈ KO k (Fin d))
    (hκ : κ ∈ KO k (Fin d)) (h : g.val * (Yo * κ₀.val) = Yo * κ.val) : g ∈ KO k (Fin n) := by
  set κ' := κ * κ₀⁻¹
  have hκ' : κ' ∈ KO k (Fin d) := mul_mem hκ (inv_mem h₀)
  have e1 : g.val * Yo = Yo * κ'.val := by
    rw [Units.val_mul, ← Matrix.mul_assoc, ← h, Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have e2 : (g⁻¹).val * Yo = Yo * (κ'⁻¹).val := by
    calc (g⁻¹).val * Yo = (g⁻¹).val * (Yo * κ'.val) * (κ'⁻¹).val := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      _ = Yo * (κ'⁻¹).val := by rw [← e1, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  rw [mem_KO_iff] at hκ' ⊢
  exact ⟨integral_of_mul_Y0 hnd e1 hκ'.1, integral_of_mul_Y0 hnd e2 hκ'.2⟩

variable [MeasurableSpace k] [BorelSpace k]

theorem smallF_psi_Y0_mul (hnd : n ≤ d) (hf : f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν) {κ₀ : GL (Fin d) k}
    (h₀ : κ₀ ∈ KO k (Fin d)) : smallF (haarVol (KO k (Fin n))) ν (psi f) (Yo * κ₀.val) = f κ₀ := by
  have key : (fun g : GL (Fin n) k => psi f (g.val * (Yo * κ₀.val)) * (ν (gdet g) : ℂ) *
      apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2)) = (KO k (Fin n) : Set (GL (Fin n) k)).indicator
      (fun _ => f κ₀) := by
    funext g
    by_cases hg : g ∈ KO k (Fin n)
    · rw [Set.indicator_of_mem hg]
      have e : g.val * (Yo * κ₀.val) = Yo * (blkGL hnd g * κ₀).val := by
        rw [Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Y0_mul_blkGL]
      rw [e, psi_Y0_mul hf (mul_mem (blkGL_mem_KO hnd hg) h₀), hf.2 _ _ g (Y0_mul_blkGL hnd g),
        apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg), apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg)]
      have : (ν (gdet g) : ℂ) ≠ 0 := Units.ne_zero _
      rw [Units.val_inv_eq_inv_val]
      field_simp
    · rw [Set.indicator_of_notMem hg, psi_eq_zero, zero_mul, zero_mul]
      rintro ⟨κ, hκ, e⟩
      exact hg (mem_KO_of_mul_Y0 hnd h₀ hκ e)
  have hK : @MeasurableSet (GL (Fin n) k) Units.instMeasurableSpace (KO k (Fin n) : Set (GL (Fin n) k)) :=
    @IsOpen.measurableSet _ _ _ Units.instMeasurableSpace
      (@BorelSpace.opensMeasurable _ _ Units.instMeasurableSpace borel_GL) isOpen_KO
  rw [smallF, key]
  refine (integral_indicator_const (μ := haarVol (KO k (Fin n))) (f κ₀) hK).trans ?_
  simp [Measure.real, haarVol_self isOpen_KO le_rfl]

end Psi

section Support
variable {ν : kˣ →* ℂˣ} {f : GL (Fin d) k → ℂ}

def rowsMat (hnd : n ≤ d) (Z : Matrix (Fin n) (Fin d) k) : Matrix (Fin d) (Fin d) k :=
  Matrix.of fun i j => if h : d - n ≤ (i : ℕ) then Z ⟨i - (d - n), by omega⟩ j else (1 : Matrix (Fin d) (Fin d) k) i j

theorem continuous_rowsMat (hnd : n ≤ d) : Continuous (rowsMat (k := k) hnd) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [rowsMat, Matrix.of_apply]
  split_ifs
  · exact (continuous_apply j).comp (continuous_apply _)
  · exact continuous_const

theorem Y0_mul_rowsMat (hnd : n ≤ d) (Z : Matrix (Fin n) (Fin d) k) : Yo * rowsMat hnd Z = Z := by
  ext i j
  rw [Y0_mul_apply hnd]
  simp only [rowsMat, Matrix.of_apply, dif_pos (show d - n ≤ d - n + (i : ℕ) by omega)]
  congr 1; ext; simp

theorem rowsMat_Y0 (hnd : n ≤ d) : rowsMat hnd (Yo) = 1 := by
  ext i j
  simp only [rowsMat, Matrix.of_apply]
  split_ifs with h
  · simp only [GlobalTheory.FullRankCoinv.Y0, Matrix.of_apply, Matrix.one_apply, Fin.ext_iff]
    congr 1
    apply propext; omega
  · rfl

theorem eventually_Y0_mul (hnd : n ≤ d) {V : Set (GL (Fin d) k)} (hV : V ∈ 𝓝 1) :
    ∀ᶠ Z in 𝓝 (Yo), ∃ u ∈ V, Z = Yo * u.val := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  rw [isEmbedding_val_GL.isInducing.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨O, hO, hOV⟩ := hV
  have hdet : {M : Matrix (Fin d) (Fin d) k | M.det ≠ 0} ∈ 𝓝 (1 : Matrix (Fin d) (Fin d) k) :=
    (isOpen_ne_fun (continuous_id.matrix_det) continuous_const).mem_nhds (by simp)
  have hc : Filter.Tendsto (rowsMat hnd) (𝓝 (Yo)) (𝓝 1) := by
    have := (continuous_rowsMat (k := k) hnd).tendsto (Yo)
    rwa [rowsMat_Y0] at this
  filter_upwards [hc (Filter.inter_mem hO hdet)] with Z hZ
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (rowsMat hnd Z) hZ.2, hOV hZ.1, ?_⟩
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Y0_mul_rowsMat]

theorem isLocallyConstant_psi (hnd : n ≤ d) (hf : f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν) :
    IsLocallyConstant (psi f : Matrix (Fin n) (Fin d) k → ℂ) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  rw [IsLocallyConstant.iff_eventually_eq]
  intro Y
  set S : Set (Matrix (Fin n) (Fin d) k) := (fun κ : GL (Fin d) k => Yo * κ.val) '' (KO k (Fin d))
  have hS : IsCompact S := isCompact_KO.image (continuous_const.matrix_mul Units.continuous_val)
  have hmem : ∀ Y, Y ∈ S ↔ ∃ κ ∈ KO k (Fin d), Y = Yo * κ.val := fun Y =>
    ⟨fun ⟨κ, hκ, e⟩ => ⟨κ, hκ, e.symm⟩, fun ⟨κ, hκ, e⟩ => ⟨κ, hκ, e.symm⟩⟩
  by_cases hY : ∃ κ ∈ KO k (Fin d), Y = Yo * κ.val
  · obtain ⟨κ, hκ, rfl⟩ := hY
    obtain ⟨U, hU, hfU⟩ := hf.1
    set V : Set (GL (Fin d) k) := {u | u ∈ KO k (Fin d) ∧ κ⁻¹ * u * κ ∈ U}
    have hV : V ∈ 𝓝 1 := by
      refine Filter.inter_mem (isOpen_KO.mem_nhds (one_mem _)) ?_
      have hc : Continuous fun u : GL (Fin d) k => κ⁻¹ * u * κ := (continuous_const.mul continuous_id).mul continuous_const
      have := hc.tendsto 1
      simp only [mul_one, inv_mul_cancel] at this
      exact this hU
    have ht : Filter.Tendsto (fun Y : Matrix (Fin n) (Fin d) k => Y * (κ⁻¹).val) (𝓝 (Yo * κ.val)) (𝓝 (Yo)) := by
      have := ((continuous_id.matrix_mul continuous_const :
        Continuous fun Y : Matrix (Fin n) (Fin d) k => Y * (κ⁻¹).val)).tendsto (Yo * κ.val)
      simpa only [id, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] using this
    filter_upwards [ht (eventually_Y0_mul hnd hV)] with Z hZ
    obtain ⟨u, ⟨hu, hu'⟩, e⟩ := hZ
    have e' : Z = Yo * (u * κ).val := by
      rw [Units.val_mul, ← Matrix.mul_assoc, ← e, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [e', psi_Y0_mul hf (mul_mem hu hκ), psi_Y0_mul hf hκ]
    have := hfU κ _ hu'
    rwa [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul] at this
  · have hO : Sᶜ ∈ 𝓝 Y := hS.isClosed.isOpen_compl.mem_nhds (fun h => hY ((hmem Y).1 h))
    filter_upwards [hO] with Z hZ
    rw [psi_eq_zero (fun h => hZ ((hmem Z).2 h)), psi_eq_zero hY]

theorem hasCompactSupport_psi : HasCompactSupport (psi f : Matrix (Fin n) (Fin d) k → ℂ) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  refine HasCompactSupport.intro (K := (fun κ : GL (Fin d) k => Yo * κ.val) '' (KO k (Fin d)))
    (isCompact_KO.image (continuous_const.matrix_mul Units.continuous_val)) ?_
  intro Y hY
  exact psi_eq_zero fun ⟨κ, hκ, e⟩ => hY ⟨κ, hκ, e.symm⟩

theorem rank_zeroth_component_eq (hnd : n ≤ d) : (Yo).rank = n := by
  refine le_antisymm (Matrix.rank_le_height _) ?_
  have := Matrix.rank_mul_le_left (Yo) (Yo)ᵀ
  rwa [Y0_mul_transpose hnd, Matrix.rank_one, Fintype.card_fin] at this

theorem psi_mem_fullRk (hnd : n ≤ d) (hf : f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν) :
    psi f ∈ GlobalTheory.FullRankCoinv.fullRk k n d := by
  refine ⟨⟨isLocallyConstant_psi hnd hf, hasCompactSupport_psi⟩, fun Y hY => psi_eq_zero ?_⟩
  rintro ⟨κ, _, rfl⟩
  exact hY (by rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 κ.isUnit), rank_zeroth_component_eq hnd])

end Support

theorem exists_fullRk_smallF_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d →
    GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν,
    ∃ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ h : GL (Fin d) k,
      smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ (GlobalTheory.FullRankCoinv.Y0 k n d * h.val) = f h := by
  intro k _ _ _ _ _ _ n d ν hnd _ f hf
  refine ⟨psi f, psi_mem_fullRk hnd hf, fun h => ?_⟩
  obtain ⟨p, hp, κ₀, h₀, rfl⟩ := (GlobalTheory.MaxParabIwasawa.iwasawa_stdMaxParab k d (d - n) n
    (Nat.sub_add_cancel hnd) h).2
  obtain ⟨D, hD⟩ := exists_Y0_mul_parab hnd hp
  have e : GlobalTheory.FullRankCoinv.Y0 k n d * (p * κ₀).val = D.val * (GlobalTheory.FullRankCoinv.Y0 k n d * κ₀.val) := by
    rw [Units.val_mul, ← Matrix.mul_assoc, hD, Matrix.mul_assoc]
  have h1 := smallF_mul_left (haarVol (KO k (Fin n))) ν (psi f) D (GlobalTheory.FullRankCoinv.Y0 k n d * κ₀.val)
  rw [smallF_psi_Y0_mul hnd hf h₀] at h1
  rw [e, hf.2 p κ₀ D hD, ← h1, Units.val_inv_eq_inv_val, Fintype.card_fin, neg_div, apow_neg]
  have h2 : (ν (gdet D) : ℂ) ≠ 0 := Units.ne_zero _
  have h3 := apow_ne_zero (gdet D) ((d : ℂ) / 2)
  field_simp

end GlobalTheory.FullRankOnto
