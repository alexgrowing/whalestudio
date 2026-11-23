import Formalism.LocalToGlobal.Columns.StdBasisFlagSubmoduleOfBlockTriangular

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Mat

variable {k : Type} [CommRing k]

theorem residue_basisVec_eq_single {N i : ℕ} (hi : i < N) : Loc.eN k N i = Pi.single (⟨i, hi⟩ : Fin N) (1 : k) := by
  funext l
  unfold Loc.eN
  by_cases h : l = ⟨i, hi⟩
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h, if_neg (fun h' => h (Fin.ext h'))]

theorem residue_linearEquiv_apply_eq_sum {N : ℕ} (φ : (Fin N → k) ≃ₗ[k] (Fin N → k)) (v : Fin N → k) (l : Fin N) :
    φ v l = ∑ l' : Fin N, φ (Pi.single l' 1) l * v l' := by
  have hv : v = ∑ l' : Fin N, v l' • (Pi.single l' (1 : k) : Fin N → k) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l' _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

def ob2rMat {N : ℕ} (φ : (Fin N → k) ≃ₗ[k] (Fin N → k)) : Matrix (Fin N) (Fin N) k := fun l s => φ (Pi.single s 1) l

theorem ob2rMat_mul {N : ℕ} (φ ψ : (Fin N → k) ≃ₗ[k] (Fin N → k)) : ob2rMat (φ * ψ) = ob2rMat φ * ob2rMat ψ := by
  ext l s
  rw [Matrix.mul_apply]
  unfold ob2rMat
  rw [show (φ * ψ) (Pi.single s 1) = φ (ψ (Pi.single s 1)) from rfl, residue_linearEquiv_apply_eq_sum φ]

theorem ob2rMat_one {N : ℕ} : ob2rMat (1 : (Fin N → k) ≃ₗ[k] (Fin N → k)) = 1 := by
  ext l s
  unfold ob2rMat
  rw [show (1 : (Fin N → k) ≃ₗ[k] (Fin N → k)) (Pi.single s 1) = Pi.single s 1 from rfl, Matrix.one_apply, Pi.single_apply]

def ob2rGam (n : ℕ) {N : ℕ} (l : Fin N) : ℕ := if l.1 < n then 0 else l.1 - n + 1

theorem single_mem_partialFlag {n c i : ℕ} (s : Fin (n + c)) (hs : s.1 < n + i) : (Pi.single s (1 : k) : Fin (n + c) → k) ∈ Loc.Ufl k n c i := by
  intro l hl
  have hl' : ¬ l.1 < n + i := hl
  rw [Pi.single_eq_of_ne (fun h => hl' (by rw [h]; exact hs))]

theorem blockTriangular_mulVec_mem_partialFlag {n c i : ℕ} (M : Matrix (Fin (n + c)) (Fin (n + c)) k) (hM : M.BlockTriangular (ob2rGam n))
    {v : Fin (n + c) → k} (hv : v ∈ Loc.Ufl k n c i) : M.mulVec v ∈ Loc.Ufl k n c i := by
  intro l hl
  have hl' : ¬ l.1 < n + i := hl
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun s _ => ?_
  by_cases hs : s.1 < n + i
  · rw [hM (show ob2rGam n s < ob2rGam n l by unfold ob2rGam; split_ifs <;> omega), zero_mul]
  · rw [hv s hs, mul_zero]

theorem residueR1_matrix_blockTriangular {n c : ℕ} {ρ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hρ : Loc.R1cond k n c ρ) :
    (ob2rMat ρ).BlockTriangular (ob2rGam n) := by
  intro l s hls
  unfold ob2rGam at hls
  have hm := hρ.1 (if s.1 < n then 0 else s.1 - n + 1) _ (single_mem_partialFlag s (by split_ifs <;> omega))
  exact hm l (by show ¬ l.1 < n + _; split_ifs at hls ⊢ <;> omega)

end Mat

section Lift

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem mulVec_mem_scaledLattice (hq0 : (q : E) ≠ 0) {N : ℕ} (A : Matrix (Fin N) (Fin N) E) (e : ℕ → ℤ)
    (he : ∀ l l' : Fin N, IntAt P (A l l' * (q : E) ^ (e l'.1 - e l.1))) {v : Sp E N} (hv : v ∈ LocE.sclLat P q N e) :
    A.mulVec v ∈ LocE.sclLat P q N e := by
  rw [ciMem_sclLat] at hv ⊢
  intro l
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  refine ciIntAt_sum _ _ fun l' _ => ?_
  have e1 : ((q : E) ^ e l.1)⁻¹ * (A l l' * v l') = (A l l' * (q : E) ^ (e l'.1 - e l.1)) * (((q : E) ^ e l'.1)⁻¹ * v l') := by
    rw [zpow_sub₀ hq0]
    field_simp
  rw [e1]
  exact (he l l').mul (hv l')

theorem mulVec_single_apply_alt {N : ℕ} (A : Matrix (Fin N) (Fin N) E) (l s : Fin N) : A.mulVec (Pi.single s 1) l = A l s := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

def ob2rConj (q n c : ℕ) (L : Matrix (Fin (n + c)) (Fin (n + c)) E) : Matrix (Fin (n + c)) (Fin (n + c)) E :=
  Matrix.diagonal (fun l : Fin (n + c) => (q : E) ^ LocE.scE n (fun i => i + 1) l.1) * L *
    Matrix.diagonal (fun l : Fin (n + c) => ((q : E) ^ LocE.scE n (fun i => i + 1) l.1)⁻¹)

theorem ob2rConj_apply {n c : ℕ} (L : Matrix (Fin (n + c)) (Fin (n + c)) E) (l s : Fin (n + c)) :
    ob2rConj q n c L l s = (q : E) ^ LocE.scE n (fun i => i + 1) l.1 * L l s * ((q : E) ^ LocE.scE n (fun i => i + 1) s.1)⁻¹ := by
  unfold ob2rConj
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem ob2rConj_ent (hq0 : (q : E) ≠ 0) {n c : ℕ} (L : Matrix (Fin (n + c)) (Fin (n + c)) E) (l s : Fin (n + c)) :
    ob2rConj q n c L l s * (q : E) ^ (LocE.scE n (fun i => i + 1) s.1 - LocE.scE n (fun i => i + 1) l.1) = L l s := by
  rw [ob2rConj_apply, zpow_sub₀ hq0]
  have h1 : (q : E) ^ LocE.scE n (fun i => i + 1) l.1 ≠ 0 := zpow_ne_zero _ hq0
  have h2 : (q : E) ^ LocE.scE n (fun i => i + 1) s.1 ≠ 0 := zpow_ne_zero _ hq0
  field_simp

theorem ob2rConj_mul {n c : ℕ} (hq0 : (q : E) ≠ 0) (L L' : Matrix (Fin (n + c)) (Fin (n + c)) E) :
    ob2rConj q n c L * ob2rConj q n c L' = ob2rConj q n c (L * L') := by
  have hd : Matrix.diagonal (fun l : Fin (n + c) => ((q : E) ^ LocE.scE n (fun i => i + 1) l.1)⁻¹) *
      Matrix.diagonal (fun l : Fin (n + c) => (q : E) ^ LocE.scE n (fun i => i + 1) l.1) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext l
    exact inv_mul_cancel₀ (zpow_ne_zero _ hq0)
  unfold ob2rConj
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _), hd, Matrix.one_mul]

theorem ob2rConj_one {n c : ℕ} (hq0 : (q : E) ≠ 0) : ob2rConj q n c (1 : Matrix (Fin (n + c)) (Fin (n + c)) E) = 1 := by
  unfold ob2rConj
  rw [Matrix.mul_one, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext l
  exact mul_inv_cancel₀ (zpow_ne_zero _ hq0)

theorem ob2rConj_zero {n c : ℕ} {L : Matrix (Fin (n + c)) (Fin (n + c)) E} {l s : Fin (n + c)} (h : L l s = 0) : ob2rConj q n c L l s = 0 := by
  rw [ob2rConj_apply, h, mul_zero, zero_mul]

theorem ob2rConj_diag {n c : ℕ} (hq0 : (q : E) ≠ 0) {L : Matrix (Fin (n + c)) (Fin (n + c)) E} {l : Fin (n + c)} (h : L l l = 1) :
    ob2rConj q n c L l l = 1 := by
  rw [ob2rConj_apply, h, mul_one, mul_inv_cancel₀ (zpow_ne_zero _ hq0)]

theorem mulVec_basisVec_of_identity_column {N : ℕ} (M : Matrix (Fin N) (Fin N) E) {i : ℕ} (hcol : ∀ (l : Fin N) (hi : i < N), M l ⟨i, hi⟩ = if l.1 = i then 1 else 0) :
    M.mulVec (Loc.eN E N i) = Loc.eN E N i := by
  by_cases hi : i < N
  · rw [basisVec_eq_single hi]
    funext l
    rw [mulVec_single_apply_alt, hcol l hi, Pi.single_apply]
    by_cases h : l.1 = i
    · rw [if_pos h, if_pos (Fin.ext h)]
    · rw [if_neg h, if_neg (fun h' => h (by rw [h']))]
  · have h0 : Loc.eN E N i = 0 := by
      funext l
      unfold Loc.eN
      rw [if_neg (by have := l.2; omega)]
      rfl
    rw [h0, Matrix.mulVec_zero]

theorem conjugate_identity_column {n c : ℕ} (hq0 : (q : E) ≠ 0) {L : Matrix (Fin (n + c)) (Fin (n + c)) E} {R : Matrix (Fin (n + c)) (Fin (n + c)) (𝓞 E ⧸ P.asIdeal)}
    (hL0 : ∀ l s, R l s = 0 → L l s = 0) (hL1 : ∀ l s, R l s = 1 → L l s = 1) {l s : Fin (n + c)}
    (h : R l s = if l.1 = s.1 then 1 else 0) : ob2rConj q n c L l s = if l.1 = s.1 then 1 else 0 := by
  by_cases he : l.1 = s.1
  · rw [if_pos he] at h ⊢
    have hls : l = s := Fin.ext he
    subst hls
    exact ob2rConj_diag hq0 (hL1 _ _ h)
  · rw [if_neg he] at h ⊢
    exact ob2rConj_zero (hL0 _ _ h)

theorem residueR1_lifts_to_stabilizer (hq0 : (q : E) ≠ 0) {n c : ℕ}
    (ρ : (Fin (n + c) → 𝓞 E ⧸ P.asIdeal) ≃ₗ[𝓞 E ⧸ P.asIdeal] (Fin (n + c) → 𝓞 E ⧸ P.asIdeal))
    (hρ : ρ ∈ Loc.R1 (𝓞 E ⧸ P.asIdeal) n c) :
    ∃ ρ' ∈ Loc.R1 E n c, ρ' ∈ stabL E (n + c) (LocE.lamY P q n c fun i => i + 1) ∧ ob2M P q ρ' = ob2rMat ρ := by
  have hRR : ob2rMat ρ * ob2rMat ρ⁻¹ = 1 := by rw [← ob2rMat_mul, mul_inv_cancel, ob2rMat_one]
  have hRR' : ob2rMat ρ⁻¹ * ob2rMat ρ = 1 := by rw [← ob2rMat_mul, inv_mul_cancel, ob2rMat_one]
  let U : GL (Fin (n + c)) (𝓞 E ⧸ P.asIdeal) := ⟨ob2rMat ρ, ob2rMat ρ⁻¹, hRR, hRR'⟩
  obtain ⟨L, hL⟩ : ∃ L, L = ciLiftM P (ob2rMat ρ) := ⟨_, rfl⟩
  have hL0 : ∀ l s, ob2rMat ρ l s = 0 → L l s = 0 := fun l s h => by rw [hL, ciLiftM_apply, h, ciLift_zero, map_zero]
  have hL1 : ∀ l s, ob2rMat ρ l s = 1 → L l s = 1 := fun l s h => by rw [hL, ciLiftM_apply, h, ciLift_one, map_one]
  have hdet : IsUnit L.det := isUnit_iff_ne_zero.2 (by rw [hL]; exact ciLiftM_det_ne U)
  have hLi : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv L hdet
  have hLi' : L⁻¹ * L = 1 := Matrix.nonsing_inv_mul L hdet
  have hG1 : ob2rConj q n c L * ob2rConj q n c L⁻¹ = 1 := by rw [ob2rConj_mul hq0, hLi, ob2rConj_one hq0]
  have hG2 : ob2rConj q n c L⁻¹ * ob2rConj q n c L = 1 := by rw [ob2rConj_mul hq0, hLi', ob2rConj_one hq0]
  have hLint : ∀ l s, IntAt P (L l s) := by rw [hL]; exact ciLiftM_int _
  have hLiint : ∀ l s, IntAt P (L⁻¹ l s) := by rw [hL]; exact ciLiftM_inv_int U
  have hLred : ∀ l s, redP P (L l s) = ob2rMat ρ l s := by rw [hL]; exact ciLiftM_red _
  have hBR : (ob2rMat ρ).BlockTriangular (ob2rGam n) := residueR1_matrix_blockTriangular hρ.1
  have hBL : L.BlockTriangular (ob2rGam n) := by rw [hL]; exact ciLiftM_blockTriangular hBR
  have : Invertible L := Matrix.invertibleOfIsUnitDet L hdet
  have hBLi : L⁻¹.BlockTriangular (ob2rGam n) := Matrix.blockTriangular_inv_of_blockTriangular hBL
  have hBG : (ob2rConj q n c L).BlockTriangular (ob2rGam n) := fun l s h => ob2rConj_zero (hBL h)
  have hBGi : (ob2rConj q n c L⁻¹).BlockTriangular (ob2rGam n) := fun l s h => ob2rConj_zero (hBLi h)
  obtain ⟨ρ', hap, hapi⟩ : ∃ ρ' : Sp E (n + c) ≃ₗ[E] Sp E (n + c),
      (∀ v, ρ' v = (ob2rConj q n c L).mulVec v) ∧ ∀ v, ρ'⁻¹ v = (ob2rConj q n c L⁻¹).mulVec v :=
    ⟨ciEquiv _ _ hG1 hG2, ciEquiv_apply _ _ hG1 hG2, ciEquiv_inv_apply _ _ hG1 hG2⟩

  have hcolR : ∀ i (l : Fin (n + c)) (hi : n + i < n + c), n + i ≤ l.1 →
      ob2rMat ρ l ⟨n + i, hi⟩ = if l.1 = (⟨n + i, hi⟩ : Fin (n + c)).1 then 1 else 0 := by
    intro i l hi hl
    have h := hρ.1.2.2 i
    rw [residue_basisVec_eq_single hi] at h
    have h3 := h l (show ¬ l.1 < n + i by omega)
    rw [Pi.sub_apply, Pi.single_apply] at h3
    show ρ (Pi.single ⟨n + i, hi⟩ 1) l = _
    by_cases he : l.1 = n + i
    · rw [if_pos (Fin.ext he), sub_eq_zero] at h3
      rw [if_pos he]
      exact h3
    · rw [if_neg (fun h' => he (by rw [h'])), sub_zero] at h3
      rw [if_neg he]
      exact h3
  have hcol0 : ∀ (l : Fin (n + c)) (hi : n < n + c), ob2rMat ρ l ⟨n, hi⟩ = if l.1 = (⟨n, hi⟩ : Fin (n + c)).1 then 1 else 0 := by
    intro l hi
    have h := congrFun hρ.1.2.1 l
    rw [residue_basisVec_eq_single hi, Pi.single_apply] at h
    show ρ (Pi.single ⟨n, hi⟩ 1) l = _
    rw [h]
    by_cases he : l.1 = n
    · rw [if_pos (Fin.ext he), if_pos he]
    · rw [if_neg (fun h' => he (by rw [h'])), if_neg he]
  have hfix0 : ρ' (Loc.eN E (n + c) n) = Loc.eN E (n + c) n := by
    rw [hap]
    exact mulVec_basisVec_of_identity_column _ fun l hi => conjugate_identity_column hq0 hL0 hL1 (hcol0 l hi)
  have hUfl : ∀ i, ∀ v ∈ Loc.Ufl E n c i, ρ' v ∈ Loc.Ufl E n c i := fun i v hv => by
    rw [hap]
    exact blockTriangular_mulVec_mem_partialFlag _ hBG hv
  have hUfli : ∀ i, ∀ v ∈ Loc.Ufl E n c i, ρ'⁻¹ v ∈ Loc.Ufl E n c i := fun i v hv => by
    rw [hapi]
    exact blockTriangular_mulVec_mem_partialFlag _ hBGi hv
  have haux : ∀ i, ρ' (Loc.eN E (n + c) (n + i)) - Loc.eN E (n + c) (n + i) ∈ Loc.Ufl E n c i := by
    intro i
    by_cases hi : n + i < n + c
    · rw [basisVec_eq_single hi, hap]
      intro l hl
      have hl' : ¬ l.1 < n + i := hl
      rw [Pi.sub_apply, mulVec_single_apply_alt, conjugate_identity_column hq0 hL0 hL1 (hcolR i l hi (by omega)), Pi.single_apply]
      by_cases he : l.1 = n + i
      · rw [if_pos he, if_pos (Fin.ext he), sub_self]
      · rw [if_neg he, if_neg (fun h' => he (by rw [h'])), sub_zero]
    · have h0 : Loc.eN E (n + c) (n + i) = 0 := by
        funext l
        unfold Loc.eN
        rw [if_neg (by have := l.2; omega)]
        rfl
      rw [h0, map_zero, sub_zero]
      exact zero_mem _
  have hR1 : Loc.R1cond E n c ρ' := ⟨hUfl, hfix0, haux⟩
  have hR1i : Loc.R1cond E n c ρ'⁻¹ := by
    refine ⟨hUfli, ?_, fun i => ?_⟩
    · conv_lhs => rw [← hfix0]
      exact ρ'.symm_apply_apply _
    · have e1 : ρ'⁻¹ (Loc.eN E (n + c) (n + i)) - Loc.eN E (n + c) (n + i) =
          -(ρ'⁻¹ (ρ' (Loc.eN E (n + c) (n + i)) - Loc.eN E (n + c) (n + i))) := by
        rw [map_sub, show ρ'⁻¹ (ρ' (Loc.eN E (n + c) (n + i))) = Loc.eN E (n + c) (n + i) from ρ'.symm_apply_apply _]
        abel
      rw [e1]
      exact neg_mem (hUfli i _ (haux i))
  have hmapG : ∀ v ∈ LocE.lamY P q n c (fun i => i + 1), (ob2rConj q n c L).mulVec v ∈ LocE.lamY P q n c (fun i => i + 1) :=
    fun v hv => mulVec_mem_scaledLattice hq0 _ _ (fun l l' => by rw [ob2rConj_ent hq0]; exact hLint l l') hv
  have hmapGi : ∀ v ∈ LocE.lamY P q n c (fun i => i + 1), (ob2rConj q n c L⁻¹).mulVec v ∈ LocE.lamY P q n c (fun i => i + 1) :=
    fun v hv => mulVec_mem_scaledLattice hq0 _ _ (fun l l' => by rw [ob2rConj_ent hq0]; exact hLiint l l') hv
  refine ⟨ρ', ⟨hR1, hR1i⟩, fun x => ⟨fun hx => ?_, fun hx => by rw [hap]; exact hmapG x hx⟩, ?_⟩
  · have h2 := hmapGi _ hx
    rwa [← hapi, show ρ'⁻¹ (ρ' x) = x from ρ'.symm_apply_apply x] at h2
  · ext l s
    unfold ob2M
    rw [hap, mulVec_single_apply_alt, ob2rConj_ent hq0, hLred]

end Lift

section B3

theorem allowed_beta_contradiction {k₀ m t rS N p p' : ℕ} (hm : m = 2 * rS + 2) (hall : ocbAllow k₀ m t N p p')
    (hlt : betaExponentOfRanks k₀ rS (k₀ + m - 1) t p' < betaExponentOfRanks k₀ rS (k₀ + m - 1) t p) : False := by
  have h1 := Nat.zero_le ((p - (k₀ + m - 1)) / t)
  have h2 := Nat.zero_le ((p' - (k₀ + m - 1)) / t)
  unfold ocbAllow at hall
  unfold betaExponentOfRanks symIdx at hlt
  split_ifs at hall hlt <;> omega

theorem reducedMatrix_eq_of_isReduction {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q n c : ℕ}
    {h₀ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    {hbar : (Fin (n + c) → 𝓞 E ⧸ P.asIdeal) ≃ₗ[𝓞 E ⧸ P.asIdeal] (Fin (n + c) → 𝓞 E ⧸ P.asIdeal)}
    (h : ocbIsRed P q n c h₀ hbar) : ob2M P q h₀ = ob2rMat hbar := by
  ext l s
  have h1 := (h l.1 s.1 l.2 s.2).2
  unfold Loc.atN at h1
  rw [dif_pos l.2, dif_pos l.2, residue_basisVec_eq_single s.2, residue_basisVec_eq_single s.2] at h1
  exact h1.symm

theorem residueFrameEntry_eq_coord {k : Type} [Field k] {k₀ n c : ℕ} (hk : k₀ ≤ n) (κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) (l l' : Fin (n + c)) :
    ocbEnt k₀ c n c n κ.toLinearMap (LocE.fPos k₀ c n l.1) (LocE.fPos k₀ c n l'.1) = κ (Pi.single l' 1) l := by
  unfold ocbEnt
  rw [frameIndex_framePos hk l.2, frameIndex_framePos hk l'.2, residue_basisVec_eq_single l'.2]
  unfold Loc.atN
  rw [dif_pos l.2]
  rfl

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem liftFromResidueParabolicProduct_holds (m2 : ℕ) : LiftFromResidueParabolicProduct Ch sel mu cst m2 := by
  intro hB i hi P hP h₀ hh₀ hbar hred hin
  obtain ⟨hk, hr, hrN, -⟩ := ranks_frame_inequalities R hB.hm (show i + 1 ≤ m2 + 1 by omega)
  have hq := ciQ_mem P.1
  have hu := ciQ_notMem_sq hB.hX hB.hPr hP
  have hq0 := ciQ_ne_zero hu
  have hmS : R.m = 2 * R.rS + 2 := by
    unfold Ranks.rS
    obtain ⟨a, ha⟩ := R.m_even
    have := R.two_le_m
    omega
  have hh₀' : h₀ ∈ stabL X.E _ (LocE.lamY P.1 (qOf P.1) (R.N (i + 1)) (cOf R (i + 1)) fun i => i + 1) := by
    have h := hh₀
    unfold lamYat at h
    rwa [if_pos hP] at h
  obtain ⟨ρ, hρ, κ, hκ, heq⟩ := hin
  obtain ⟨ρ', hρ'R, hρ'S, hρ'M⟩ := residueR1_lifts_to_stabilizer hq0 ρ hρ
  have hM0 : ob2M P.1 (qOf P.1) h₀ = ob2rMat hbar := reducedMatrix_eq_of_isReduction hred
  have hκ'S : ρ'⁻¹ * h₀ ∈ stabL X.E _ (LocE.lamY P.1 (qOf P.1) (R.N (i + 1)) (cOf R (i + 1)) fun i => i + 1) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hρ'S) hh₀'
  have hMκ : ob2M P.1 (qOf P.1) (ρ'⁻¹ * h₀) = ob2rMat κ := by
    have h1 : ob2M P.1 (qOf P.1) ρ' * ob2M P.1 (qOf P.1) (ρ'⁻¹ * h₀) = ob2rMat ρ * ob2rMat κ := by
      rw [← reducedMatrix_mul hq0 hρ'S hκ'S, mul_inv_cancel_left, hM0, heq, ob2rMat_mul]
    rw [hρ'M] at h1
    have h2 : ob2rMat ρ⁻¹ * ob2rMat ρ = 1 := by rw [← ob2rMat_mul, inv_mul_cancel, ob2rMat_one]
    calc ob2M P.1 (qOf P.1) (ρ'⁻¹ * h₀) = ob2rMat ρ⁻¹ * (ob2rMat ρ * ob2M P.1 (qOf P.1) (ρ'⁻¹ * h₀)) := by
          rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
      _ = ob2rMat κ := by rw [h1, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hJ : ρ'⁻¹ * h₀ ∈ LocE.JGsym P.1 (qOf P.1) R.k R.rS R.r R.t (R.N (i + 1)) (cOf R (i + 1)) := by
    refine mem_parahoric_of_blockTriangular hq hu hk hr (by omega) hκ'S ?_ ?_ ?_
    · intro l l' hlt
      rw [hMκ]
      by_contra hne0
      have hne : LocE.fPos R.k (cOf R (i + 1)) (R.N (i + 1)) l.1 ≠ LocE.fPos R.k (cOf R (i + 1)) (R.N (i + 1)) l'.1 := by
        intro h
        have hlt' : betaExponentOfRanks R.k R.rS R.r R.t (LocE.fPos R.k (cOf R (i + 1)) (R.N (i + 1)) l'.1) <
            betaExponentOfRanks R.k R.rS R.r R.t (LocE.fPos R.k (cOf R (i + 1)) (R.N (i + 1)) l.1) := hlt
        rw [h] at hlt'
        exact lt_irrefl _ hlt'
      have hall := hκ.2 _ _ (framePos_lt hk l.2) (framePos_lt hk l'.2) hne (by rw [@residueFrameEntry_eq_coord _ (resField P.1) _ _ _ hk]; exact hne0)
      exact allowed_beta_contradiction hmS hall hlt
    · intro l hl
      rw [hMκ]
      have h := hκ.1 _ hl
      rwa [@residueFrameEntry_eq_coord _ (resField P.1) _ _ _ hk] at h
    · intro l l' hl hl'
      rw [hMκ]
      by_contra hne0
      have hall := hκ.2 _ _ (framePos_lt hk l.2) (framePos_lt hk l'.2) (by omega) (by rw [@residueFrameEntry_eq_coord _ (resField P.1) _ _ _ hk]; exact hne0)
      rw [hl'] at hall
      unfold ocbAllow at hall
      split_ifs at hall <;> omega
  unfold SameDC
  rw [hB.sharp]
  refine ⟨ρ', hρ'R, ρ'⁻¹ * h₀, ?_, by rw [mul_one, mul_inv_cancel_left]⟩
  unfold Jat
  rw [if_pos hP, if_pos rfl]
  exact hJ

end B3

end Formalism.L2.Col
