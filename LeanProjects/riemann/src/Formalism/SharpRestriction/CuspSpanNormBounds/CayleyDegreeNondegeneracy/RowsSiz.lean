import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsDef

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

open Classical

def sumOfSquaredModuli {κ : Type} [Fintype κ] (y : κ → ℂ) : ℝ := ∏ v, ((max 1 (‖y v‖ / 1)) ^ 3)⁻¹

theorem rows_psi_nonneg {κ : Type} [Fintype κ] (y : κ → ℂ) : 0 ≤ sumOfSquaredModuli y :=
  Finset.prod_nonneg fun _ _ => inv_nonneg.2 (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) 3)

theorem rows_finsum_le {κ : Type} [Fintype κ] (Λ : AddSubgroup (κ → ℂ))
    (hΛ : ∀ x ∈ Λ, x ≠ 0 → 1 ≤ ∏ v, ‖x v‖) (T : Finset (κ → ℂ)) (hT : ∀ y ∈ T, y ∈ Λ) :
    ∑ y ∈ T, sumOfSquaredModuli y ≤ (41 : ℝ) ^ Fintype.card κ := by
  obtain ⟨hs, hle⟩ := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.latticeSum κ Λ 1 le_rfl hΛ
  have e : ∑ y ∈ T.subtype (fun y => y ∈ Λ), sumOfSquaredModuli (y : κ → ℂ) = ∑ y ∈ T, sumOfSquaredModuli y :=
    Finset.sum_subtype_of_mem (fun y => sumOfSquaredModuli y) hT
  rw [← e]
  have h1 : ∑ y ∈ T.subtype (fun y => y ∈ Λ), sumOfSquaredModuli (y : κ → ℂ) ≤
      ∑' y : Λ, ∏ v, ((max 1 (‖(y : κ → ℂ) v‖ / 1)) ^ 3)⁻¹ :=
    Summable.sum_le_tsum (f := fun y : Λ => ∏ v, ((max 1 (‖(y : κ → ℂ) v‖ / 1)) ^ 3)⁻¹) _
      (fun y _ => rows_psi_nonneg (y : κ → ℂ)) hs
  refine h1.trans (hle.trans ?_)
  norm_num

theorem rows_sum_prod_le {α ι κ : Type} [Fintype ι] [Fintype κ] (Λ : ι → AddSubgroup (κ → ℂ))
    (hΛ : ∀ i, ∀ x ∈ Λ i, x ≠ 0 → 1 ≤ ∏ v, ‖x v‖) (S : Finset α) (x : α → ι → κ → ℂ)
    (hx : ∀ Z ∈ S, ∀ i, x Z i ∈ Λ i) (hinj : ∀ Z ∈ S, ∀ Z' ∈ S, x Z = x Z' → Z = Z') :
    ∑ Z ∈ S, ∏ i, sumOfSquaredModuli (x Z i) ≤ ((41 : ℝ) ^ Fintype.card κ) ^ Fintype.card ι := by
  set T : ι → Finset (κ → ℂ) := fun i => S.image (fun Z => x Z i) with hT
  have e1 : ∑ Z ∈ S, ∏ i, sumOfSquaredModuli (x Z i) = ∑ y ∈ S.image x, ∏ i, sumOfSquaredModuli (y i) :=
    (Finset.sum_image (f := fun y : ι → κ → ℂ => ∏ i, sumOfSquaredModuli (y i)) (fun Z hZ Z' hZ' h => hinj Z hZ Z' hZ' h)).symm
  have sub : S.image x ⊆ Fintype.piFinset T := by
    intro y hy
    obtain ⟨Z, hZ, rfl⟩ := Finset.mem_image.1 hy
    exact Fintype.mem_piFinset.2 fun i => Finset.mem_image.2 ⟨Z, hZ, rfl⟩
  have e2 : ∑ y ∈ S.image x, ∏ i, sumOfSquaredModuli (y i) ≤ ∑ y ∈ Fintype.piFinset T, ∏ i, sumOfSquaredModuli (y i) :=
    Finset.sum_le_sum_of_subset_of_nonneg sub fun y _ _ => Finset.prod_nonneg fun i _ => rows_psi_nonneg _
  have e3 : ∑ y ∈ Fintype.piFinset T, ∏ i, sumOfSquaredModuli (y i) = ∏ i, ∑ y ∈ T i, sumOfSquaredModuli y :=
    (Finset.prod_univ_sum T (fun _ y => sumOfSquaredModuli y)).symm
  rw [e1]
  refine e2.trans ?_
  rw [e3]
  calc ∏ i, ∑ y ∈ T i, sumOfSquaredModuli y ≤ ∏ _i : ι, (41 : ℝ) ^ Fintype.card κ :=
        Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun y _ => rows_psi_nonneg y) fun i _ =>
          rows_finsum_le (Λ i) (hΛ i) (T i) fun y hy => by
            obtain ⟨Z, hZ, rfl⟩ := Finset.mem_image.1 hy
            exact hx Z hZ i
    _ = ((41 : ℝ) ^ Fintype.card κ) ^ Fintype.card ι := by
        rw [Finset.prod_const, Finset.card_univ]

end Abstract

section Gram

variable {D : D7}

def gramEntryFunction (D : D7) (Z : GramM D) (i : Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) : D.what₂.Tau → ℂ :=
  fun τ => ((rhoF D i.1 * rhoF D i.2 : ℝ) : ℂ) * embS D τ (Z i.1 i.2)

theorem rows_rhoF_pos (hrd : 0 < D.host.rdE) (a : Fin (D.R.rS + 1)) : 0 < rhoF D a := by
  unfold rhoF
  exact Real.rpow_pos_of_pos hrd _

theorem rows_norm_entry (hrd : 0 < D.host.rdE) (Z : GramM D) (i : Fin (D.R.rS + 1) × Fin (D.R.rS + 1))
    (τ : D.what₂.Tau) : ‖gramEntryFunction D Z i τ‖ = ‖embS D τ (Z i.1 i.2)‖ * (rhoF D i.1 * rhoF D i.2) := by
  unfold gramEntryFunction
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (rows_rhoF_pos hrd _) (rows_rhoF_pos hrd _)), mul_comm]

def rows_one (N : ℕ) (a : Fin N) : Fin 1 ↪o Fin N :=
  OrderEmbedding.ofStrictMono (fun _ => a) (fun x y h => absurd h (by rw [Subsingleton.elim x y]; exact lt_irrefl _))

theorem rows_one_apply (N : ℕ) (a : Fin N) (x : Fin 1) : rows_one N a x = a := rfl

theorem rows_absMinor_one (Z : GramM D) (a b : Fin (D.R.rS + 1)) (τ : D.what₂.Tau) :
    UnitaryVolumeMass.absMinor D Z (rows_one _ a) (rows_one _ b) τ = ‖embS D τ (Z a b)‖ * (rhoF D a * rhoF D b) := by
  unfold UnitaryVolumeMass.absMinor
  rw [Matrix.det_fin_one]
  simp [rows_one_apply]

theorem rows_det_one (Z : GramM D) (a b : Fin (D.R.rS + 1)) :
    (Z.submatrix (rows_one _ a) (rows_one _ b)).det = Z a b := by
  rw [Matrix.det_fin_one]
  simp [rows_one_apply]

theorem rows_entry_inj (hrd : 0 < D.host.rdE) (hf : 0 < D.R.f) (Z Z' : GramM D)
    (h : gramEntryFunction D Z = gramEntryFunction D Z') : Z = Z' := by
  have hc : 0 < Fintype.card D.what₂.Tau := by rw [D.what₂.card_Tau]; exact hf
  obtain ⟨τ⟩ := Fintype.card_pos_iff.1 hc
  refine Matrix.ext fun a b => ?_
  have h1 := congrFun (congrFun h (a, b)) τ
  unfold gramEntryFunction at h1
  have hne : (((rhoF D a * rhoF D b : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos (rows_rhoF_pos hrd a) (rows_rhoF_pos hrd b)).ne'
  exact (embS D τ).injective (mul_left_cancel₀ hne h1)

theorem rows_psi_ge (hrd : 0 < D.host.rdE) (Z : GramM D) (M : ℝ) (hM : 1 ≤ M)
    (hred : ∀ (j : ℕ) (I J : Fin j ↪o Fin (D.R.rS + 1)), (Z.submatrix I J).det ≠ 0 →
      ∏ τ, max 1 (UnitaryVolumeMass.absMinor D Z I J τ) ≤ M) (i : Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) :
    (M ^ 3)⁻¹ ≤ sumOfSquaredModuli (gramEntryFunction D Z i) := by
  have hP : ∏ τ, max 1 ‖gramEntryFunction D Z i τ‖ ≤ M := by
    by_cases h0 : Z i.1 i.2 = 0
    · have : ∀ τ, max 1 ‖gramEntryFunction D Z i τ‖ = 1 := fun τ => by
        rw [rows_norm_entry hrd, h0, map_zero, norm_zero, zero_mul]; exact max_eq_left zero_le_one
      rw [Finset.prod_congr rfl fun τ _ => this τ, Finset.prod_const_one]
      exact hM
    · have h := hred 1 (rows_one _ i.1) (rows_one _ i.2) (by rw [rows_det_one]; exact h0)
      refine le_trans (le_of_eq ?_) h
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [rows_absMinor_one, rows_norm_entry hrd]
  have hP0 : 0 < ∏ τ, max 1 ‖gramEntryFunction D Z i τ‖ :=
    Finset.prod_pos fun τ _ => lt_of_lt_of_le one_pos (le_max_left _ _)
  have e : sumOfSquaredModuli (gramEntryFunction D Z i) = ((∏ τ, max 1 ‖gramEntryFunction D Z i τ‖) ^ 3)⁻¹ := by
    unfold sumOfSquaredModuli
    rw [Finset.prod_inv_distrib, Finset.prod_pow]
    simp only [div_one]
  rw [e]
  exact inv_anti₀ (pow_pos hP0 3) (pow_le_pow_left₀ hP0.le hP 3)

theorem rows_sizeSum (X : TermTie D) {u u' : D.what₂.Word} (hE : wordPairEntriesInLattice X u u') (hrd : 0 < D.host.rdE)
    (hf : 0 < D.R.f) (S : Finset (GramM D)) (sg : GramM D → ℝ) (hsg : ∀ Z ∈ S, 1 ≤ sg Z) (B : ℝ) (hB : 1 ≤ B)
    (hterm : ∀ Z ∈ S, ∃ t : D.s.Term u u', D.s.Gterm t ≠ 0 ∧ D.s.relevant t ∧ ZEquiv (termGramMatrix X t) Z)
    (hred : ∀ Z ∈ S, ∀ (j : ℕ) (I J : Fin j ↪o Fin (D.R.rS + 1)), (Z.submatrix I J).det ≠ 0 →
      ∏ τ, max 1 (UnitaryVolumeMass.absMinor D Z I J τ) ≤ B * sg Z ^ 4)
    (e : ℝ) (he : 12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤ e) :
    ∑ Z ∈ S, sg Z ^ (-e) ≤ ((41 : ℝ) ^ D.R.f * B ^ 3) ^ ((D.R.rS + 1) ^ 2) := by
  classical
  choose Λ hΛ hmem using hE
  have hcard : Fintype.card (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) = (D.R.rS + 1) ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_fin, sq]
  have key := rows_sum_prod_le (fun i : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => Λ i.1 i.2)
    (fun i => hΛ i.1 i.2) S (fun Z => gramEntryFunction D Z)
    (fun Z hZ i => by
      obtain ⟨t, hG, hr, hz⟩ := hterm Z hZ
      exact hmem i.1 i.2 t Z hG hr hz)
    (fun Z _ Z' _ h => rows_entry_inj hrd hf Z Z' h)
  rw [hcard, D.what₂.card_Tau] at key
  have each : ∀ Z ∈ S, sg Z ^ (-e) ≤
      (B ^ 3) ^ ((D.R.rS + 1) ^ 2) * ∏ i : Fin (D.R.rS + 1) × Fin (D.R.rS + 1), sumOfSquaredModuli (gramEntryFunction D Z i) := by
    intro Z hZ
    have h1 := hsg Z hZ
    have s0 : 0 < sg Z := lt_of_lt_of_le one_pos h1
    have hM : 1 ≤ B * sg Z ^ 4 := by
      have : 1 ≤ sg Z ^ 4 := one_le_pow₀ h1
      nlinarith
    have hp : ((((B * sg Z ^ 4) ^ 3)⁻¹) ^ ((D.R.rS + 1) ^ 2)) ≤
        ∏ i : Fin (D.R.rS + 1) × Fin (D.R.rS + 1), sumOfSquaredModuli (gramEntryFunction D Z i) := by
      rw [← hcard, ← Finset.card_univ, ← Finset.prod_const]
      exact Finset.prod_le_prod (fun i _ => by positivity) fun i _ => rows_psi_ge hrd Z _ hM (hred Z hZ) i
    have hB3 : 0 < (B ^ 3) ^ ((D.R.rS + 1) ^ 2) := by positivity
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hp hB3.le)
    have e1 : (B ^ 3) ^ ((D.R.rS + 1) ^ 2) * (((B * sg Z ^ 4) ^ 3)⁻¹) ^ ((D.R.rS + 1) ^ 2) =
        (sg Z ^ (12 * (D.R.rS + 1) ^ 2))⁻¹ := by
      rw [← mul_pow, mul_pow B, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul, inv_pow, ← pow_mul,
        ← pow_mul]
      congr 2
      ring
    rw [e1, ← Real.rpow_natCast, ← Real.rpow_neg s0.le]
    refine Real.rpow_le_rpow_of_exponent_le h1 ?_
    push_cast
    linarith
  calc ∑ Z ∈ S, sg Z ^ (-e)
      ≤ ∑ Z ∈ S, (B ^ 3) ^ ((D.R.rS + 1) ^ 2) *
          ∏ i : Fin (D.R.rS + 1) × Fin (D.R.rS + 1), sumOfSquaredModuli (gramEntryFunction D Z i) := Finset.sum_le_sum each
    _ = (B ^ 3) ^ ((D.R.rS + 1) ^ 2) *
          ∑ Z ∈ S, ∏ i : Fin (D.R.rS + 1) × Fin (D.R.rS + 1), sumOfSquaredModuli (gramEntryFunction D Z i) := by
        rw [Finset.mul_sum]
    _ ≤ (B ^ 3) ^ ((D.R.rS + 1) ^ 2) * ((41 : ℝ) ^ D.R.f) ^ ((D.R.rS + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = ((41 : ℝ) ^ D.R.f * B ^ 3) ^ ((D.R.rS + 1) ^ 2) := by rw [mul_pow, mul_comm]

end Gram

section Reduced

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

theorem rows_isTermF' (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0) :
    IsTermF D (X.abelian₂ t) (lf D Y.F0) (X.fl' t) := by
  refine ⟨⟨X.lift' t, ?_, ?_⟩, Y.frame_ok t⟩
  · have := X.adm t
    rwa [Y.fl_eq t] at this
  · have h := X.G_eq t
    rw [Y.fl_eq t] at h
    rw [← h]
    exact (map_ne_zero_iff _ (algebraMap D.host.F D.host.E).injective).2 hG

include Y in

theorem rows_reduced_exists {C' Cl Cg cb Cu cT CT C0 A C : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hHH : UnitaryVolumeMass.stHH D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C) (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0)
    (hrel : D.s.relevant t) :
    ∃ Z : GramM D, ZEquiv (termGramMatrix X t) Z ∧
      ∀ (j : ℕ) (I J : Fin j ↪o Fin (D.R.rS + 1)), (Z.submatrix I J).det ≠ 0 →
        ∏ τ, max 1 (UnitaryVolumeMass.absMinor D Z I J τ) ≤ HHZ D large₂.sc.b C (termGramMatrix X t) := by
  have hR : RelZ D (ZhatL (lf D Y.F0) (X.fl' t)) := by
    have h := X.pt_cell t hG hrel
    rw [Y.fl_eq t] at h
    exact ⟨_, h⟩
  obtain ⟨_, _, _, Z, hZ, hm⟩ := hHH hH Y.F0 Y.flag_e_eq_hyperbolic Y.formsAtZero (X.abelian₂ t) (Y.isRows.1 _ (Y.Lam_mem t)) (X.fl' t)
    (rows_isTermF' Y t hG) hR
  refine ⟨Z, ?_, fun j I J h => ?_⟩
  · unfold termGramMatrix; rw [Y.fl_eq t]; exact hZ
  · unfold termGramMatrix; rw [Y.fl_eq t]; exact (hm j I J h).1

end Reduced

end Formalism.MainNotions.BridgeLemma₂

end
