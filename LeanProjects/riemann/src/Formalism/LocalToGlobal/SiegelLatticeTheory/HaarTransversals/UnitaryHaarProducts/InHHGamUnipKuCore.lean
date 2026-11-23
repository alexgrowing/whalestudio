import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKuDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.PoincareInHH.Cut.GU

open Formalism.L2.SG.Pf.Level

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Level

variable {D : D7} (X : HidaSetting D)

theorem zs_mL {t : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (ht : ZMod' X.B.I X.B.g t) {b : VA X.B.I}
    (hb : b ∈ X.B.I.Lf) : t • b ∈ mL X.B.I X.B.g := by
  obtain ⟨s, hs, rfl⟩ := ht
  rw [mul_comm, mul_smul]
  exact intsmul_mem X hs (unitaryCongruence.smul_mem_mL X.B.I hb)

theorem Mo_le_Qs {f : VA X.B.I} (hf : f ∈ X.B.I.Lf) (T : Set (VA X.B.I))
    (hT : ∀ s ∈ T, ZMod' X.B.I X.B.g (hA X.B.I f s)) :
    unitaryCongruence.Mo X.B.I X.B.g T ≤ unitaryCongruence.Qs X.B.I X.B.g f :=
  sup_le (Submodule.span_le.mpr fun s hs => hT s hs) (unitaryCongruence.mL_Qs X.B.I X.B.g hf)

def Gm (m : ℕ) : Submodule (IntAf X.B.I.F X.B.I.E) (VA X.B.I) :=
  unitaryCongruence.Mo X.B.I X.B.g (Set.range X.e0 ∪ X.bw '' {j | j.1 < m})

theorem flag {κ : X.B.I.Gf} (hκ : κ ∈ X.K2) :
    ∀ m, m ≤ D.R.k → ∀ w ∈ Gm X m, ((X.B.I.fmat κ - 1) ^ m) *ᵥ w ∈ Gm X 0 := by
  intro m
  induction m with
  | zero => intro _ w hw; rwa [pow_zero, one_mulVec]
  | succ m ih =>
    intro hm w hw
    rw [pow_succ, ← mulVec_mulVec]
    apply ih (Nat.le_of_succ_le hm)
    exact unitaryCongruence.b_step X.B.I X.B.g X.e0 X.z0 X.bw hκ.1 hκ.2 ⟨m, hm⟩ w hw

theorem bw_Gk (j : Fin D.R.k) : X.bw j ∈ Gm X D.R.k :=
  unitaryCongruence.sub_Mo X.B.I (Or.inr ⟨j, j.2, rfl⟩)

theorem adj1 (κ : X.B.I.Gf) (a b : VA X.B.I) :
    hA X.B.I a ((X.B.I.fmat κ - 1) *ᵥ b) = hA X.B.I ((X.B.I.fmat κ⁻¹ - 1) *ᵥ a) b := by
  have h0 : hA X.B.I a (X.B.I.fmat κ *ᵥ b) = hA X.B.I (X.B.I.fmat κ⁻¹ *ᵥ a) b := by
    have := hA_fmat X κ (X.B.I.fmat κ⁻¹ *ᵥ a) b
    rwa [mulVec_mulVec, fmat_mul_inv, one_mulVec] at this
  rw [sub_mulVec, sub_mulVec, one_mulVec, one_mulVec, unitaryCongruence.hA_sub_right, hA_sub_left, h0]

theorem adj (κ : X.B.I.Gf) : ∀ m (a b : VA X.B.I),
    hA X.B.I a (((X.B.I.fmat κ - 1) ^ m) *ᵥ b) = hA X.B.I (((X.B.I.fmat κ⁻¹ - 1) ^ m) *ᵥ a) b := by
  intro m
  induction m with
  | zero => intro a b; simp only [pow_zero, one_mulVec]
  | succ m ih =>
    intro a b
    rw [pow_succ, ← mulVec_mulVec, ih, adj1, pow_succ', ← mulVec_mulVec]

theorem pow_Lf {κ : X.B.I.Gf} (hκ : κ ∈ X.B.I.Kset) :
    ∀ m, ∀ y ∈ X.B.I.Lf, ((X.B.I.fmat κ - 1) ^ m) *ᵥ y ∈ X.B.I.Lf := by
  intro m
  induction m with
  | zero => intro y hy; rwa [pow_zero, one_mulVec]
  | succ m ih =>
    intro y hy
    rw [pow_succ, ← mulVec_mulVec]
    exact ih _ (unitaryCongruence.K_sub_mv X.B.I hκ hy)

theorem pow_Y (κ : X.B.I.Gf) (Y : Submodule (IntAf X.B.I.F X.B.I.E) (VA X.B.I))
    (hYM : ∀ v ∈ Y, X.B.I.fmat κ *ᵥ v ∈ Y) :
    ∀ m, ∀ y ∈ Y, ((X.B.I.fmat κ - 1) ^ m) *ᵥ y ∈ Y := by
  intro m
  induction m with
  | zero => intro y hy; rwa [pow_zero, one_mulVec]
  | succ m ih =>
    intro y hy
    rw [pow_succ, ← mulVec_mulVec]
    apply ih
    rw [sub_mulVec, one_mulVec]
    exact Y.sub_mem (hYM y hy) hy

theorem decomp (hP : ProjModG X) {v : VA X.B.I} (hv : v ∈ X.B.I.Lf)
    (ho : (∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) v) ∧ ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) v)) ∧
      ZMod' X.B.I X.B.g (hA X.B.I X.z0 v)) :
    v - ∑ i, hA X.B.I (X.bwd i) v • X.bw i - ∑ i, hA X.B.I (X.bw i) v • X.bwd i ∈ mL X.B.I X.B.g := by
  have hA' : ∑ a, hA X.B.I (X.f0 a) v • X.e0 a ∈ mL X.B.I X.B.g :=
    Submodule.sum_mem _ fun a _ => zs_mL X (ho.1 a).2 (X.vectorsInLattice.1 a).1
  have hB' : ∑ a, hA X.B.I (X.e0 a) v • X.f0 a ∈ mL X.B.I X.B.g :=
    Submodule.sum_mem _ fun a _ => zs_mL X (ho.1 a).1 (X.vectorsInLattice.1 a).2
  have hC' : hA X.B.I X.z0 v • X.z0 ∈ mL X.B.I X.B.g := zs_mL X ho.2 X.vectorsInLattice.2.1
  have he : v - ∑ i, hA X.B.I (X.bwd i) v • X.bw i - ∑ i, hA X.B.I (X.bw i) v • X.bwd i =
      piG X v + ∑ a, hA X.B.I (X.f0 a) v • X.e0 a + ∑ a, hA X.B.I (X.e0 a) v • X.f0 a -
        hA X.B.I X.z0 v • X.z0 := by
    unfold piG; abel
  rw [he]
  exact Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (hP v hv) hA') hB') hC'

theorem dual_zero (i : Fin D.R.k) (w : VA X.B.I) (hw : w = sigA X.B.I X.ew • w) :
    hA X.B.I (X.bwd i) w = 0 := by
  have h1 : hA X.B.I (sigA X.B.I X.ew • X.bwd i) w = X.ew * hA X.B.I (X.bwd i) w := by
    rw [unitaryCongruence.hA_smul_left, unitaryCongruence.sigA_sigA]
  rw [← X.bwd_w i] at h1
  have h2 : hA X.B.I (X.bwd i) w = sigA X.B.I X.ew * hA X.B.I (X.bwd i) w := by
    conv_lhs => rw [hw]
    rw [unitaryCongruence.hA_smul_right]
  calc hA X.B.I (X.bwd i) w = X.ew * (sigA X.B.I X.ew * hA X.B.I (X.bwd i) w) := by rw [← h2, ← h1]
    _ = (X.ew * sigA X.B.I X.ew) * hA X.B.I (X.bwd i) w := by ring
    _ = 0 := by rw [X.ew_orth, zero_mul]

theorem sigA_smul_bwd_sum_eq (c : Fin D.R.k → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :
    ∑ j, c j • X.bwd j = sigA X.B.I X.ew • ∑ j, c j • X.bwd j := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [X.bwd_w j]
  rw [smul_comm]

theorem coreOfProj {D : D7} (X : HidaSetting D) : CoreOfProj X := by
  intro hP κ hκ hκi Y hYL hYM hYo v hv
  set M := X.B.I.fmat κ with hMdef
  have hvL : v ∈ X.B.I.Lf := hYL hv
  set z := ((M - 1) ^ D.R.k) *ᵥ v with hzdef
  have hzY : z ∈ Y := pow_Y X κ Y hYM _ v hv
  have hzL : z ∈ X.B.I.Lf := hYL hzY

  have ha : ∀ i, ZMod' X.B.I X.B.g (hA X.B.I (X.bw i) z) := by
    intro i
    rw [hzdef, adj X κ]
    have hG : ((X.B.I.fmat κ⁻¹ - 1) ^ D.R.k) *ᵥ X.bw i ∈ Gm X 0 :=
      flag X hκi D.R.k le_rfl (X.bw i) (bw_Gk X i)
    have hle : Gm X 0 ≤ unitaryCongruence.Qs X.B.I X.B.g v := by
      refine Mo_le_Qs X hvL _ ?_
      rintro s (⟨a, rfl⟩ | ⟨j, hj, _⟩)
      · rw [unitaryCongruence.hA_symm X.B.I (X.e0 a) v]
        exact unitaryCongruence.Z_sig X.B.I X.B.g ((hYo v hv).1 a).1
      · exact absurd hj (Nat.not_lt_zero _)
    have hq : ZMod' X.B.I X.B.g (hA X.B.I v (((X.B.I.fmat κ⁻¹ - 1) ^ D.R.k) *ᵥ X.bw i)) := hle hG
    rw [unitaryCongruence.hA_symm X.B.I v]
    exact unitaryCongruence.Z_sig X.B.I X.B.g hq

  have hb : ∀ i, ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) z) := by
    intro i
    set v1 := ∑ j, hA X.B.I (X.bwd j) v • X.bw j with hv1
    set v2 := ∑ j, hA X.B.I (X.bw j) v • X.bwd j with hv2
    have hm : v - v1 - v2 ∈ mL X.B.I X.B.g := decomp X hP hvL (hYo v hv)
    have hsplit : z = ((M - 1) ^ D.R.k) *ᵥ v1 + ((M - 1) ^ D.R.k) *ᵥ v2 +
        ((M - 1) ^ D.R.k) *ᵥ (v - v1 - v2) := by
      rw [hzdef, ← mulVec_add, ← mulVec_add]; congr 1; abel
    rw [hsplit, unitaryCongruence.hA_add_right, unitaryCongruence.hA_add_right]
    refine unitaryCongruence.Z_add X.B.I X.B.g (unitaryCongruence.Z_add X.B.I X.B.g ?_ ?_) ?_
    · have hv1G : v1 ∈ Gm X D.R.k :=
        Submodule.sum_mem _ fun j _ =>
          intsmul_mem X (unitaryCongruence.hA_int X.B.I (X.vectorsInLattice.2.2 j).2 hvL) (bw_Gk X j)
      have hG := flag X hκ D.R.k le_rfl v1 hv1G
      have hle : Gm X 0 ≤ unitaryCongruence.Qs X.B.I X.B.g (X.bwd i) := by
        refine Mo_le_Qs X (X.vectorsInLattice.2.2 i).2 _ ?_
        rintro s (⟨a, rfl⟩ | ⟨j, hj, _⟩)
        · exact (reference_frame_congruences X).2.2.1 i a
        · exact absurd hj (Nat.not_lt_zero _)
      exact hle hG
    · rw [dual_zero X i _ (by rw [hv2, ← mulVec_smul, ← sigA_smul_bwd_sum_eq X])]
      exact unitaryCongruence.Z_zero X.B.I X.B.g
    · exact Z_right X (X.vectorsInLattice.2.2 i).2
        (mL_pres X _ (pow_Lf X hκ.1 D.R.k) _ hm)

  have hd := decomp X hP hzL (hYo z hzY)
  have h1 : ∑ i, hA X.B.I (X.bwd i) z • X.bw i ∈ mL X.B.I X.B.g :=
    Submodule.sum_mem _ fun i _ => zs_mL X (hb i) (X.vectorsInLattice.2.2 i).1
  have h2 : ∑ i, hA X.B.I (X.bw i) z • X.bwd i ∈ mL X.B.I X.B.g :=
    Submodule.sum_mem _ fun i _ => zs_mL X (ha i) (X.vectorsInLattice.2.2 i).2
  have he : z = (z - ∑ i, hA X.B.I (X.bwd i) z • X.bw i - ∑ i, hA X.B.I (X.bw i) z • X.bwd i) +
      ∑ i, hA X.B.I (X.bwd i) z • X.bw i + ∑ i, hA X.B.I (X.bw i) z • X.bwd i := by abel
  rw [he]
  exact Submodule.add_mem _ (Submodule.add_mem _ hd h1) h2

end Formalism.L2.SG.PoincareInHH.Cut.GU
