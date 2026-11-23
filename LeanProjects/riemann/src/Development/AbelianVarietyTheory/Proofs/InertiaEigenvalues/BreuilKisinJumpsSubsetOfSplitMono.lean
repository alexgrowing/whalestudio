import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerEAddSmulMemEisensteinShiftGraded
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemAnalyticFiltrationIffLatticeFiltrationAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLOfEPowSmulMem

noncomputable section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.BK.SubJumps

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {η H : ℕ}

omit [CompleteSpace K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] in

theorem C_mem_invL (c : K) : (C c : K⟦X⟧) ∈ invL l (A O K) :=
  (mem_invL_A_iff l).2 ⟨‖c‖, fun n => by
    rw [coeff_C]
    split_ifs
    · exact le_rfl
    · simp⟩

omit [CompleteSpace K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] [Fintype ι] [DecidableEq ι] in

theorem smul_mem_of_invL {B : Subalgebra O K⟦X⟧} (hB : invL l (A O K) ≤ B)
    (W : Submodule B (Vec K a ι)) (c : K) {x : Vec K a ι} (hx : x ∈ W) : c • x ∈ W := by
  have := W.smul_mem ⟨C c, hB (C_mem_invL c)⟩ hx
  convert this using 1
  ext τ i : 2
  simp [Subalgebra.smul_def, PowerSeries.smul_eq_C_mul]

omit [CompleteSpace K] [NeZero a] [TameDescentExponentData K l e a] [Fintype ι] [DecidableEq ι] in
theorem Ezpow_zero : Ezpow K l e 0 = 1 := by
  simpa using Ezpow_natCast (K := K) l e 0

omit [CompleteSpace K] [NeZero a] [TameDescentExponentData K l e a] [Fintype ι] [DecidableEq ι] in

theorem shiftE_le {B : Subalgebra O K⟦X⟧} (hB : invL l (A O K) ≤ B)
    (W : Submodule B (Vec K a ι)) {i j : ℤ} (h : i ≤ j) : shiftE l e j W ≤ shiftE l e i W := by
  intro v hv
  rw [mem_shiftE] at hv ⊢
  have := W.smul_mem ⟨_, hB ((Ezpow_mem_invL_A_iff (O := O) (e := e)).2 (sub_nonneg.2 h))⟩ hv
  rwa [Subalgebra.smul_def, smul_smul, ← Ezpow_add, show j - i + -j = -i by ring] at this

omit [CompleteSpace K] [NeZero a] [TameDescentExponentData K l e a] [Fintype ι] [DecidableEq ι] in
theorem shiftE_zero {B : Subalgebra O K⟦X⟧} (W : Submodule B (Vec K a ι)) {v : Vec K a ι} :
    v ∈ shiftE l e 0 W ↔ v ∈ W := by
  rw [mem_shiftE, neg_zero, Ezpow_zero, one_smul]

end GlobalTheory.BK.SubJumps

namespace GlobalTheory.BK.SubJumps

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {η H : ℕ}

omit [CompleteSpace K] in

theorem EN_mem_shiftE_Man (D : BKDat O K l e a ι η H) (k : ℤ) {y : Vec K a ι}
    (hy : y ∈ shiftE l e k (D.Mext (Rpi O K l e))) : D.EN y ∈ shiftE l e k (D.Mext (Rpi O K l e)) := by
  rw [mem_shiftE] at hy ⊢
  have hym : y = Ezpow K l e k • (Ezpow K l e (-k) • y) := by
    rw [smul_smul, ← Ezpow_add, add_neg_cancel, Ezpow_zero, one_smul]
  generalize Ezpow K l e (-k) • y = m at hy hym
  subst hym
  have h0 := Ezpow_neg_mul (K := K) (l := l) (e := e) k
  have key : Ezpow K l e (-k) • D.EN (Ezpow K l e k • m) = ((k : K⟦X⟧) * N K (E K l e)) • m + D.EN m := by
    rw [PhiMod.EN_apply, PhiMod.conn_smul, smul_add, smul_smul, E_mul_N_Ezpow,
      smul_comm (E K l e) (Ezpow K l e k) (D.conn m), ← PhiMod.EN_apply, smul_add, smul_smul,
      smul_smul, h0, one_smul]
    congr 1
    congr 1
    linear_combination ((k : K⟦X⟧) * N K (E K l e)) * h0
  rw [key]
  refine add_mem ?_ (D.EN_mem_Man hy)
  exact (D.Mext (Rpi O K l e)).smul_mem ⟨_, mul_mem (intCast_mem _ k)
    (N_mem (derivative_mem_R l (E_mem l e _)))⟩ hy

end GlobalTheory.BK.SubJumps

namespace GlobalTheory.BK.SubJumps

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {η H : ℕ}

section Proj

variable (l e) in

noncomputable def cst : ℕ → K
  | 0 => 1
  | n + 1 => (((n + 1 : ℕ) : ℤ) * e * l : ℤ) * cst n

omit [IsUltrametricDist K] [CompleteSpace K] [NeZero a] [TameDescentExponentData K l e a] in
theorem cst_ne_zero (n : ℕ) : cst (K := K) l e n ≠ 0 := by
  have : CharZero K := (RingHom.charZero_iff (algebraMap ℚ_[l] K).injective).1 inferInstance
  induction n with
  | zero => exact one_ne_zero
  | succ n ih =>
    refine mul_ne_zero ?_ ih
    have hl : 0 < l := (Fact.out : l.Prime).pos
    have he : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
    exact_mod_cast (by positivity : (((n + 1 : ℕ) : ℤ) * e * l : ℤ) ≠ 0)

variable (P : PhiMod O K l e a ι)

noncomputable def proj : ℕ → Module.End K (Vec K a ι)
  | 0 => LinearMap.id
  | n + 1 => (P.EN + ((((n + 1 : ℕ) : ℤ) * e * l : ℤ) : K) • LinearMap.id) * proj n

theorem proj_zero (v : Vec K a ι) : proj P 0 v = v := rfl

theorem proj_succ (n : ℕ) (v : Vec K a ι) : proj P (n + 1) v =
    P.EN (proj P n v) + ((((n + 1 : ℕ) : ℤ) * e * l : ℤ) : K) • proj P n v := rfl

theorem app_proj {Q : PhiMod O K l e a κ} (F : Hom P Q) (n : ℕ) (v : Vec K a ι) :
    F.app (proj P n v) = proj Q n (F.app v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [proj_succ, proj_succ, map_add, Hom.app_EN, LinearMap.map_smul_of_tower, ih]

theorem proj_mem_shiftE_Lan (D : BKDat O K l e a ι η H) (n : ℕ) {x : Vec K a ι}
    (hx : x ∈ shiftE l e 1 (D.ext (Rpi O K l e))) :
    proj D.toPhiMod n x ∈ shiftE l e ((n : ℤ) + 1) (D.ext (Rpi O K l e)) := by
  induction n with
  | zero => rw [proj_zero]; simpa using hx
  | succ n ih =>
    rw [proj_succ]
    have := GlobalTheory.Proof.eulerE_add_smul_mem_eisenstein_shift_graded.EN_add_smul_mem_shiftE' D ((n : ℤ) + 1) _ ih
    push_cast at this ⊢
    exact this

theorem proj_sub_mem (D : BKDat O K l e a ι η H) (n : ℕ) {x : Vec K a ι}
    (hx : x ∈ D.ext (Rpi O K l e)) :
    proj D.toPhiMod n x - cst (K := K) l e n • x ∈ shiftE l e 1 (D.ext (Rpi O K l e)) := by
  induction n with
  | zero => rw [proj_zero]; simp [cst]
  | succ n ih =>
    have hp : proj D.toPhiMod n x ∈ D.ext (Rpi O K l e) := by
      have h1 := shiftE_le (invL_A_le_Rpi l e) (D.ext (Rpi O K l e)) (show (0 : ℤ) ≤ 1 by omega) ih
      rw [shiftE_zero] at h1
      simpa using add_mem h1 (smul_mem_of_invL (invL_A_le_Rpi l e) _ (cst (K := K) l e n) hx)
    have h2 := GlobalTheory.Proof.eulerE_add_smul_mem_eisenstein_shift_graded.EN_add_smul_mem_shiftE' D 0 _ ((shiftE_zero _).2 hp)
    simp only [zero_mul, Int.cast_zero, zero_smul, add_zero, zero_add] at h2
    have h3 := smul_mem_of_invL (invL_A_le_Rpi l e) _ ((((n + 1 : ℕ) : ℤ) * e * l : ℤ) : K) ih
    have : proj D.toPhiMod (n + 1) x - cst (K := K) l e (n + 1) • x = D.EN (proj D.toPhiMod n x) +
        ((((n + 1 : ℕ) : ℤ) * e * l : ℤ) : K) • (proj D.toPhiMod n x - cst (K := K) l e n • x) := by
      rw [proj_succ, cst, smul_sub, smul_smul]
      abel
    rw [this]
    exact add_mem h2 h3

theorem proj_mem_shiftE_Man (D : BKDat O K l e a ι η H) (n : ℕ) (k : ℤ) {y : Vec K a ι}
    (hy : y ∈ shiftE l e k (D.Mext (Rpi O K l e))) :
    proj D.toPhiMod n y ∈ shiftE l e k (D.Mext (Rpi O K l e)) := by
  induction n with
  | zero => exact hy
  | succ n ih =>
    rw [proj_succ]
    exact add_mem (EN_mem_shiftE_Man D k ih) (smul_mem_of_invL (invL_A_le_Rpi l e) _ _ ih)

end Proj

end GlobalTheory.BK.SubJumps

namespace GlobalTheory.BK.SubJumps

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {η H : ℕ}

theorem mem_of_app_mem {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q) (n : ℕ)
    (hΛ : ∀ τ : ZMod a, ∃ Λ : Matrix ι κ K⟦X⟧, (∀ i k, Λ i k ∈ A O K) ∧
      Λ * F.mat τ = (l : K) ^ n • (1 : Matrix ι ι K⟦X⟧))
    (k : ℤ) {v : Vec K a ι} (hv : F.app v ∈ shiftE l e k (Q.Mext (Rpi O K l e))) :
    v ∈ shiftE l e k (P.Mext (Rpi O K l e)) := by
  rw [mem_shiftE] at hv ⊢
  rw [← LinearMap.map_smul] at hv
  generalize Ezpow K l e (-k) • v = w at hv ⊢
  refine mem_tot.2 fun τ => mem_vecs.2 fun i => ?_
  obtain ⟨Λ, hΛA, hΛ⟩ := hΛ τ
  have h1 : Matrix.mulVec Λ (F.app w τ) = (l : K) ^ n • w τ := by
    rw [Hom.app_apply, Matrix.mulVec_mulVec, hΛ]
    first
      | rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      | (ext j; simp [Matrix.mulVec, dotProduct, Matrix.one_apply])
  have h2 : (Matrix.mulVec Λ (F.app w τ)) i ∈ Rpi O K l e := by
    simp only [Matrix.mulVec, dotProduct]
    exact Subalgebra.sum_mem _ fun j _ => mul_mem (A_le_Rpi l e (hΛA i j))
      (mem_vecs.1 (mem_tot.1 hv τ) j)
  rw [h1, Pi.smul_apply, PowerSeries.smul_eq_C_mul] at h2
  have h3 := mul_mem (invL_A_le_Rpi l e (C_mem_invL (O := O) ((l : K) ^ n)⁻¹)) h2
  have hl : ((l : K) ^ n) ≠ 0 := by
    have : CharZero K := (RingHom.charZero_iff (algebraMap ℚ_[l] K).injective).1 inferInstance
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hl, map_one, one_mul] at h3

theorem mem_shiftE_Man_of_Lan (D : BKDat O K l e a ι η H) {j k : ℤ} (h : k + η ≤ j) {z : Vec K a ι}
    (hz : z ∈ shiftE l e j (D.ext (Rpi O K l e))) : z ∈ shiftE l e k (D.Mext (Rpi O K l e)) := by
  have h1 := D.smul_mem_Mext (A_le_Rpi l e) (mem_shiftE.1 hz)
  rw [← Ezpow_natCast, smul_smul, ← Ezpow_add] at h1
  refine shiftE_le (invL_A_le_Rpi l e) _ (show k ≤ j - η by omega) (mem_shiftE.2 ?_)
  rwa [show -(j - (η : ℤ)) = (η : ℤ) + -j by ring]

theorem mem_shiftE_one_of_mem (D : BKDat O K l e a ι η H) {v : Vec K a ι}
    (hv : v ∈ D.ext (invL l (A O K))) (h : v ∈ shiftE l e 1 (D.ext (Rpi O K l e))) :
    v ∈ shiftE l e 1 (D.ext (invL l (A O K))) := by
  rw [mem_shiftE] at h ⊢
  refine FilAn.mem_extInvL_of_Ezpow_smul D.toPhiMod (i := (η : ℤ) + 1) h ?_
  rw [smul_smul, ← Ezpow_add, show (η : ℤ) + 1 + -1 = ((η : ℕ) : ℤ) by ring, Ezpow_natCast]
  exact D.smul_mem_Mext (le_away _ _) hv

theorem filL_le_ext (P : PhiMod O K l e a ι) (k : ℤ) : P.filL k ≤ P.ext (invL l (A O K)) := by
  refine sup_le inf_le_left fun v hv => ?_
  have := shiftE_le le_rfl _ (show (0 : ℤ) ≤ 1 by omega) hv
  rwa [shiftE_zero] at this

theorem filL_anti (P : PhiMod O K l e a ι) (k : ℤ) : P.filL (k + 1) ≤ P.filL k :=
  sup_le_sup_right (inf_le_inf_left _ (shiftE_le le_rfl _ (by omega))) _

theorem app_mem_shiftE {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q)
    {B : Subalgebra O K⟦X⟧} {W₀ : Submodule B (Vec K a ι)} {W₁ : Submodule B (Vec K a κ)}
    (h : ∀ v ∈ W₀, F.app v ∈ W₁) (k : ℤ) {v : Vec K a ι} (hv : v ∈ shiftE l e k W₀) :
    F.app v ∈ shiftE l e k W₁ := by
  rw [mem_shiftE] at hv ⊢
  rw [← LinearMap.map_smul]
  exact h _ hv

theorem app_mem_filL {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q) (k : ℤ)
    {v : Vec K a ι} (hv : v ∈ P.filL k) : F.app v ∈ Q.filL k := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
  rw [map_add]
  exact add_mem (Submodule.mem_sup_left (Submodule.mem_inf.2
      ⟨F.app_mem_ext (le_away _ _) hy.1,
        app_mem_shiftE F (fun v hv => F.app_mem_Mext (le_away _ _) hv) k hy.2⟩))
    (Submodule.mem_sup_right (app_mem_shiftE F (fun v hv => F.app_mem_ext (le_away _ _) hv) 1 hz))

theorem mem_filL_of_app_mem (D₀ : BKDat O K l e a ι η H) (D₁ : BKDat O K l e a κ η H)
    (F : Hom D₀.toPhiMod D₁.toPhiMod) (n : ℕ)
    (hΛ : ∀ τ : ZMod a, ∃ Λ : Matrix ι κ K⟦X⟧, (∀ i k, Λ i k ∈ A O K) ∧
      Λ * F.mat τ = (l : K) ^ n • (1 : Matrix ι ι K⟦X⟧))
    (k : ℤ) {x : Vec K a ι} (hx : x ∈ D₀.ext (invL l (A O K))) (hF : F.app x ∈ D₁.filL k) :
    x ∈ D₀.filL k := by
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hF
  obtain ⟨-, hyM⟩ := Submodule.mem_inf.1 hy
  have hxL : x ∈ D₀.ext (Rpi O K l e) := D₀.ext_mono (invL_A_le_Rpi l e) hx
  have hyM' : y ∈ shiftE l e k (D₁.Mext (Rpi O K l e)) :=
    mem_shiftE.2 (D₁.Mext_mono (invL_A_le_Rpi l e) (mem_shiftE.1 hyM))
  have hz' : z ∈ shiftE l e 1 (D₁.ext (Rpi O K l e)) :=
    mem_shiftE.2 (D₁.ext_mono (invL_A_le_Rpi l e) (mem_shiftE.1 hz))
  set N : ℕ := (k + η).toNat
  have h1 := proj_mem_shiftE_Man D₁ N k hyM'
  have h3 := mem_shiftE_Man_of_Lan D₁ (k := k) (by omega) (proj_mem_shiftE_Lan D₁ N hz')
  have hw : F.app (proj D₀.toPhiMod N x) ∈ shiftE l e k (D₁.Mext (Rpi O K l e)) := by
    rw [app_proj, ← hyz, map_add]
    exact add_mem h1 h3
  have hw' := mem_of_app_mem F n hΛ k hw
  have hs := proj_sub_mem D₀ N hxL
  have hwL : proj D₀.toPhiMod N x ∈ D₀.ext (Rpi O K l e) := by
    have h4 := shiftE_le (invL_A_le_Rpi l e) (D₀.ext (Rpi O K l e)) (show (0 : ℤ) ≤ 1 by omega) hs
    rw [shiftE_zero] at h4
    simpa using add_mem h4 (smul_mem_of_invL (invL_A_le_Rpi l e) _ (cst (K := K) l e N) hxL)
  obtain ⟨y', hy', hwy'⟩ :=
    FilAn.exists_mem_filL_of_mem_inf D₀.toPhiMod k (Submodule.mem_inf.2 ⟨hwL, hw'⟩)
  have hv : cst (K := K) l e N • x - y' ∈ shiftE l e 1 (D₀.ext (Rpi O K l e)) := by
    have := sub_mem hwy' hs
    convert this using 1
    abel
  have hvL : cst (K := K) l e N • x - y' ∈ D₀.ext (invL l (A O K)) :=
    sub_mem (smul_mem_of_invL le_rfl _ _ hx) (filL_le_ext _ _ hy')
  have hv' := mem_shiftE_one_of_mem D₀ hvL hv
  have hc : cst (K := K) l e N • x ∈ D₀.filL k := by
    have := add_mem hy' (Submodule.mem_sup_right hv' : _ ∈ D₀.filL k)
    simpa using this
  have := smul_mem_of_invL le_rfl _ (cst (K := K) l e N)⁻¹ hc
  rwa [smul_smul, inv_mul_cancel₀ (cst_ne_zero N), one_smul] at this

end GlobalTheory.BK.SubJumps

open GlobalTheory.BK in

theorem GlobalTheory.BK.jumps_subset_of_split_mono : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₀ : BKDat O K l e a ι η H) (D₁ : BKDat O K l e a κ η H) (F : GlobalTheory.BK.Hom D₀.toPhiMod D₁.toPhiMod) (n : ℕ), (∀ τ : ZMod a, ∃ Λ : Matrix ι κ K⟦X⟧, (∀ i k, Λ i k ∈ A O K) ∧ Λ * F.mat τ = (l : K) ^ n • (1 : Matrix ι ι K⟦X⟧)) → D₀.jumps ⊆ D₁.jumps := by
  intro O K _ _ _ _ _ _ l e a _ _ _ _ _ ι κ _ _ _ _ η H D₀ D₁ F n hΛ i hi h1
  apply hi
  refine le_antisymm (SubJumps.filL_anti _ i) fun x hx => ?_
  have h2 := SubJumps.app_mem_filL F i hx
  rw [← h1] at h2
  exact SubJumps.mem_filL_of_app_mem D₀ D₁ F n hΛ (i + 1) (SubJumps.filL_le_ext _ _ hx) h2
