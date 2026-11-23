import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipRat
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipLatPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipStmt
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipLatStmt
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsDifferentialLattice

noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.UnipB

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

section Fin

abbrev iE : X.B.I.E →+* X.B.I.E ⊗[X.B.I.F] Af X.B.I.F := Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)

def BA : Matrix (Fin X.B.I.n) (Kap X) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := (Bm X).map (iE X)
def BA' : Matrix (Kap X) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := (Bm' X).map (iE X)

theorem BA_mul_BA' : BA X * BA' X = 1 := by
  rw [BA, BA', ← Matrix.map_mul, Bm_mul_Bm', Matrix.map_one _ (map_zero _) (map_one _)]

theorem BA'_mul_BA : BA' X * BA X = 1 := by
  rw [BA, BA', ← Matrix.map_mul, Bm'_mul_Bm, Matrix.map_one _ (map_zero _) (map_one _)]

theorem BA_col (k : Kap X) : BA X *ᵥ Pi.single k 1 = incl X.B.I (bv X k) := by
  funext i
  simp [BA, Bm, mulVec_single, incl]

theorem BA'_incl (k : Kap X) : BA' X *ᵥ incl X.B.I (bv X k) = Pi.single k 1 := by
  rw [← BA_col, Matrix.mulVec_mulVec, BA'_mul_BA, Matrix.one_mulVec]

theorem mulVec_eq_sum_colsA {m p : Type*} [Fintype p] [DecidableEq p] {A : Type*} [CommRing A]
    (M : Matrix m p A) (c : p → A) : M *ᵥ c = ∑ k, c k • (M *ᵥ Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single c]
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (Pi.single k (c k) : p → A) = c k • Pi.single k 1 by ext j; simp [Pi.single_apply],
    Matrix.mulVec_smul]

theorem BA_mulVec (c : Kap X → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :
    BA X *ᵥ c = ∑ k, c k • incl X.B.I (bv X k) := by
  rw [mulVec_eq_sum_colsA]
  simp only [BA_col]

theorem BA_mulVec_mem (S : Set (Fin D.R.rS)) (c : Kap X → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
    (hc : ∀ k, k ∉ Sum.inl '' S → c k = 0) :
    BA X *ᵥ c ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((fun b => incl X.B.I (X.eR b)) '' S) := by
  rw [BA_mulVec]
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk : k ∈ Sum.inl '' S
  · obtain ⟨b, hb, rfl⟩ := hk
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
  · rw [hc k hk, zero_smul]
    exact Submodule.zero_mem _

theorem hA_e_BA (a : Fin D.R.rS) (c : Kap X → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :
    hA X.B.I (incl X.B.I (X.eR a)) (BA X *ᵥ c) = c (Sum.inr (Sum.inr a)) := by
  rw [BA_mulVec, ← Cut.hAlin_apply, map_sum]
  simp only [map_smul, Cut.hAlin_apply, smul_eq_mul]
  have e : ∀ k, hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (bv X k)) = iE X (JB X (Sum.inl a) k) := by
    intro k
    rw [Cut.hA_incl]
    rfl
  simp only [e, JB_e_row]
  simp

theorem nfin_of_pat (x : X.B.I.Gf) (M : Matrix (Kap X) (Kap X) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))
    (hx : X.B.I.fmat x = BA X * M * BA' X) (hpat : InPat (lvk X) 1 (M - 1)) : x ∈ X.NfinU u := by
  have hg : X.B.I.fmat x - 1 = BA X * (M - 1) * BA' X := by
    rw [hx, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, BA_mul_BA']
  have hgv : ∀ y, (X.B.I.fmat x - 1) *ᵥ y = BA X *ᵥ ((M - 1) *ᵥ (BA' X *ᵥ y)) := by
    intro y
    rw [hg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hperp : ∀ y, (∀ a, hA X.B.I (incl X.B.I (X.eR a)) y = 0) →
      (X.B.I.fmat x - 1) *ᵥ y ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
        (Set.range fun b => incl X.B.I (X.eR b)) := by
    intro y hy
    set c := BA' X *ᵥ y with hc
    have hyc : y = BA X *ᵥ c := by rw [hc, Matrix.mulVec_mulVec, BA_mul_BA', Matrix.one_mulVec]
    have hcf : ∀ a, c (Sum.inr (Sum.inr a)) = 0 := by
      intro a
      have := hA_e_BA X a c
      rw [← hyc, hy a] at this
      exact this.symm
    rw [hgv, ← hc, range_eq_image_lt]
    refine BA_mulVec_mem X _ _ fun k hk => ?_
    have hk' : ∀ b, k ≠ Sum.inl b := by
      rintro b rfl
      exact hk ⟨b, b.2, rfl⟩
    have hlk := lvk_notinl X k hk'
    rw [mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases j with b | i | b
    · rw [hpat k _ (by rw [lvk_inl]; have := b.2; omega), zero_mul]
    · rw [hpat k _ (by rw [lvk_w]; omega), zero_mul]
    · rw [hcf b, mul_zero]
  have hz : ∀ a, hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (X.zR u)) = 0 := by
    intro a
    rw [Cut.hA_incl]
    have := hE_ez X u a
    simp only [hE] at this
    rw [this, map_zero]
  refine ⟨fun a => ?_, hperp _ hz, hperp⟩
  rw [hgv]
  show BA X *ᵥ ((M - 1) *ᵥ (BA' X *ᵥ incl X.B.I (bv X (Sum.inl a)))) ∈ _
  rw [BA'_incl]
  refine BA_mulVec_mem X {b | b.1 < a.1} _ fun k hk => ?_
  rw [mulVec_single_one]
  refine hpat k _ ?_
  rcases k with b | i | b
  · have : ¬ b.1 < a.1 := fun h => hk ⟨b, h, rfl⟩
    simp only [lvk, Sum.elim_inl]; omega
  · simp only [lvk, Sum.elim_inl, Sum.elim_inr]; have := a.2; omega
  · simp only [lvk, Sum.elim_inl, Sum.elim_inr]; have := a.2; have := b.2; omega

theorem fmat_gA {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : X.B.I.fmat (gA X hk hY hYs).2 = (gE X Y).map (iE X) := rfl

theorem gA_nfin {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : (gA X hk hY hYs).2 ∈ X.NfinU u := by
  refine nfin_of_pat X u _ ((cay (N0 D) Y).map (iE X)) ?_ ?_
  · rw [fmat_gA, gE, BA, BA', Matrix.map_mul, Matrix.map_mul]
  · have h := inPat_map (iE X) (cay_sub_one (N0 D) hY)
    rw [Matrix.map_sub _ (fun a b => map_sub _ a b), Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact inPat_mono hk h

end Fin

section Kg

theorem kset_apply {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (y : VA X.B.I) :
    y ∈ X.B.I.Lf ↔ X.B.I.fmat x *ᵥ y ∈ X.B.I.Lf :=
  (show ∀ y, y ∈ X.B.I.Lf ↔ X.B.I.fmat x *ᵥ y ∈ X.B.I.Lf from hx) y

theorem natsmul_mem_Lf (g : ℕ) {z : VA X.B.I} (hz : z ∈ X.B.I.Lf) :
    ((g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z) ∈ X.B.I.Lf :=
  X.B.I.Lf.smul_mem (⟨(g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F), natCast_mem _ g⟩ : IntAf X.B.I.F X.B.I.E) hz

theorem kg_mul {g : ℕ} {a b : X.B.I.Gf} (ha : a ∈ X.B.I.Kg g) (hb : b ∈ X.B.I.Kg g) : a * b ∈ X.B.I.Kg g := by
  refine ⟨kset_mul X ha.1 hb.1, fun y hy => ?_⟩
  obtain ⟨z1, hz1, e1⟩ := hb.2 y hy
  obtain ⟨z2, hz2, e2⟩ := ha.2 y hy
  refine ⟨X.B.I.fmat a *ᵥ z1 + z2, add_mem ((kset_apply X ha.1 z1).1 hz1) hz2, ?_⟩
  have e : X.B.I.fmat (a * b) - 1 = X.B.I.fmat a * (X.B.I.fmat b - 1) + (X.B.I.fmat a - 1) := by
    rw [Cut.fmat_mul, Matrix.mul_sub, Matrix.mul_one]; abel
  rw [e, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, e1, e2, Matrix.mulVec_smul, smul_add]

theorem kg_conj {g : ℕ} {a x : X.B.I.Gf} (ha : a ∈ X.B.I.Kg g) (hx : x ∈ X.B.I.Kset) :
    x⁻¹ * a * x ∈ X.B.I.Kg g := by
  refine ⟨kset_mul X (kset_mul X (kset_inv X hx) ha.1) hx, fun y hy => ?_⟩
  have hxy : X.B.I.fmat x *ᵥ y ∈ X.B.I.Lf := (kset_apply X hx y).1 hy
  obtain ⟨z, hz, e⟩ := ha.2 _ hxy
  refine ⟨X.B.I.fmat x⁻¹ *ᵥ z, (kset_apply X (kset_inv X hx) z).1 hz, ?_⟩
  have e2 : X.B.I.fmat (x⁻¹ * a * x) - 1 = X.B.I.fmat x⁻¹ * (X.B.I.fmat a - 1) * X.B.I.fmat x := by
    rw [Cut.fmat_mul, Cut.fmat_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Cut.fmat_inv_mul]
  rw [e2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_smul]

theorem principal_congruence_mem_level {a : X.B.I.Gf} (ha : a ∈ X.B.I.Kg X.B.g) : a ∈ X.K2 := by
  have hin : ∀ w ∈ X.B.I.Lf, ∀ S : Set (VA X.B.I), InMod X.B.I X.B.g S ((X.B.I.fmat a - 1) *ᵥ w) := by
    intro w hw S
    obtain ⟨z, hz, e⟩ := ha.2 w hw
    rw [e]
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨z, hz, rfl⟩)
  exact ⟨ha.1, fun b => hin _ (X.vectorsInLattice.1 b).1 _, hin _ X.vectorsInLattice.2.1 _, fun i => hin _ (X.vectorsInLattice.2.2 i).1 _⟩

theorem exists_dL : ∃ dL : ℕ, 0 < dL ∧ ∀ i, ((dL : X.B.I.E) • Pi.single i 1 : Fin X.B.I.n → X.B.I.E) ∈ X.B.I.L :=
  by apply _root_.UpperTheory.Reformulated.B.ExistsNatMultipleBasisVectorMemLattice.exists_dL <;> assumption

theorem exists_cL : ∃ cL : ℕ, 0 < cL ∧ ∀ w ∈ X.B.I.Lf, ∀ i, iE X (cL : X.B.I.E) * w i ∈ IntAf X.B.I.F X.B.I.E := by
  obtain ⟨c, hc0, hc⟩ := nt_Lf_int X.B.I
  refine ⟨c.natAbs ^ 2, pow_pos (Int.natAbs_pos.2 hc0) 2, fun w hw i => ?_⟩
  have hcast : ((c.natAbs ^ 2 : ℕ) : X.B.I.E) = (c : X.B.I.E) * (c : X.B.I.E) := by
    rw [← Int.cast_natCast, ← Int.cast_mul]
    congr 1
    push_cast
    rw [← sq, sq_abs, sq]
  rw [hcast, map_mul, mul_assoc]
  exact (IntAf X.B.I.F X.B.I.E).mul_mem (nt_inclE_mem X.B.I _ (isInt_intCast c)) (hc w hw i)

theorem kg_rat {g cL dL : ℕ} (hcL : ∀ w ∈ X.B.I.Lf, ∀ i, iE X (cL : X.B.I.E) * w i ∈ IntAf X.B.I.F X.B.I.E)
    (hdL : ∀ i, ((dL : X.B.I.E) • Pi.single i 1 : Fin X.B.I.n → X.B.I.E) ∈ X.B.I.L)
    {M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E} (hM : IntDiv (g * cL * dL) (M - 1)) :
    ∀ y ∈ X.B.I.Lf, ∃ z ∈ X.B.I.Lf, (M.map (iE X) - 1) *ᵥ y = (g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z := by
  obtain ⟨A, hA, hMA⟩ := hM
  intro y hy
  have hcol : ∀ j, (fun i => (dL : X.B.I.E) * A i j) ∈ X.B.I.L := by
    intro j
    have e : (fun i => (dL : X.B.I.E) * A i j) =
        ∑ i, A i j • ((dL : X.B.I.E) • Pi.single i 1 : Fin X.B.I.n → X.B.I.E) := by
      funext l
      simp [Finset.sum_apply, Pi.single_apply, mul_comm]
    rw [e]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact X.B.I.L.smul_mem (⟨A i j, (mem_integralClosure_iff ℤ X.B.I.E).2 (hA i j)⟩ : 𝓞 X.B.I.E) (hdL i)
  have hinc : ∀ j, incl X.B.I (fun i => (dL : X.B.I.E) * A i j) ∈ X.B.I.Lf :=
    fun j => Submodule.subset_span ⟨⟨_, hcol j⟩, rfl⟩
  refine ⟨∑ j, (⟨iE X (cL : X.B.I.E) * y j, hcL y hy j⟩ : IntAf X.B.I.F X.B.I.E) •
    incl X.B.I (fun i => (dL : X.B.I.E) * A i j), Submodule.sum_mem _ fun j _ => X.B.I.Lf.smul_mem _ (hinc j), ?_⟩
  have hMm : M.map (iE X) - 1 = (M - 1).map (iE X) := by
    rw [Matrix.map_sub _ (fun a b => map_sub _ a b), Matrix.map_one _ (map_zero _) (map_one _)]
  rw [hMm, hMA]
  funext i
  simp only [mulVec, dotProduct, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply,
    Finset.sum_apply, incl, Subring.smul_def]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul, map_natCast, Nat.cast_mul]
  ring

theorem kg_of {g cL dL : ℕ} (hcL : ∀ w ∈ X.B.I.Lf, ∀ i, iE X (cL : X.B.I.E) * w i ∈ IntAf X.B.I.F X.B.I.E)
    (hdL : ∀ i, ((dL : X.B.I.E) • Pi.single i 1 : Fin X.B.I.n → X.B.I.E) ∈ X.B.I.L)
    {x : X.B.I.Gf} {M M' : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E}
    (hx : X.B.I.fmat x = M.map (iE X)) (hx' : X.B.I.fmat x⁻¹ = M'.map (iE X))
    (hM : IntDiv (g * cL * dL) (M - 1)) (hM' : IntDiv (g * cL * dL) (M' - 1)) : x ∈ X.B.I.Kg g := by
  have h1 := kg_rat X hcL hdL hM
  have h2 := kg_rat X hcL hdL hM'
  have hmov : ∀ {N : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E},
      (∀ y ∈ X.B.I.Lf, ∃ z ∈ X.B.I.Lf, (N.map (iE X) - 1) *ᵥ y = (g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z) →
      ∀ y ∈ X.B.I.Lf, N.map (iE X) *ᵥ y ∈ X.B.I.Lf := by
    intro N hN y hy
    obtain ⟨z, hz, e⟩ := hN y hy
    have e2 : N.map (iE X) *ᵥ y = y + (N.map (iE X) - 1) *ᵥ y := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [e2, e]
    exact add_mem hy (natsmul_mem_Lf X g hz)
  refine ⟨fun y => ⟨fun hy => ?_, fun hy => ?_⟩, fun y hy => ?_⟩
  · show X.B.I.fmat x *ᵥ y ∈ X.B.I.Lf
    rw [hx]; exact hmov h1 y hy
  · have hy' : X.B.I.fmat x *ᵥ y ∈ X.B.I.Lf := hy
    have e : y = X.B.I.fmat x⁻¹ *ᵥ (X.B.I.fmat x *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Cut.fmat_inv_mul, Matrix.one_mulVec]
    rw [e, hx']
    exact hmov h2 _ hy'
  · rw [hx]; exact h1 y hy

end Kg

section Div

theorem intDiv_cancel {c t : ℕ} (hc : c ≠ 0) {M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E}
    (h : IntDiv (c * t) ((c : X.B.I.E) • M)) : IntDiv t M := by
  obtain ⟨A, hA, e⟩ := h
  refine ⟨A, hA, ?_⟩
  have hc' : (c : X.B.I.E) ≠ 0 := Nat.cast_ne_zero.2 hc
  rw [Nat.cast_mul, ← smul_smul] at e
  exact smul_right_injective _ hc' e

theorem gE_intDiv {dB dB' t : ℕ} (hdB0 : 0 < dB) (hdB'0 : 0 < dB') (hdB : IntDiv 1 ((dB : X.B.I.E) • Bm X))
    (hdB' : IntDiv 1 ((dB' : X.B.I.E) • Bm' X)) {Y : Matrix (Kap X) (Kap X) X.B.I.E}
    (hY : IntDiv (2 ^ N0 D * (dB * dB' * t)) Y) : IntDiv t (gE X Y - 1) := by
  set T := dB * dB' * t with hT

  have hhalf : IntDiv 1 ((⅟2 : X.B.I.E) • Y) := by
    obtain ⟨A, hA, e⟩ := hY
    refine ⟨((2 ^ (2 * D.R.rS + 1) * T : ℕ) : X.B.I.E) • A, fun i j => ?_, ?_⟩
    · rw [Matrix.smul_apply, smul_eq_mul]
      exact (isInt_natCast _).mul (hA i j)
    · rw [e, smul_smul, Nat.cast_one, one_smul]
      congr 1
      show (⅟2 : X.B.I.E) * ((2 ^ (2 * D.R.rS + 2) * T : ℕ) : X.B.I.E) = ((2 ^ (2 * D.R.rS + 1) * T : ℕ) : X.B.I.E)
      push_cast
      rw [pow_succ, ← mul_assoc, ← mul_assoc, mul_comm (⅟2 : X.B.I.E), mul_assoc (_ ^ _), invOf_mul_self, mul_one]
  have hgeo : IntDiv 1 (geo (N0 D) ((⅟2 : X.B.I.E) • Y)) := by
    unfold geo
    exact intDiv_sum fun j _ => by simpa using intDiv_pow hhalf j
  have hcay : IntDiv T (cay (N0 D) Y - 1) := by
    have e : cay (N0 D) Y - 1 = Y * geo (N0 D) ((⅟2 : X.B.I.E) • Y) := by unfold cay; abel
    rw [e]
    have h := intDiv_mul hY hgeo
    rw [mul_one, mul_comm] at h
    exact intDiv_dvd h
  have e2 : gE X Y - 1 = Bm X * (cay (N0 D) Y - 1) * Bm' X := by
    unfold gE
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Bm_mul_Bm']
  have h3 := intDiv_mul (intDiv_mul hdB hcay) hdB'
  have e3 : (dB : X.B.I.E) • Bm X * (cay (N0 D) Y - 1) * ((dB' : X.B.I.E) • Bm' X) =
      ((dB * dB' : ℕ) : X.B.I.E) • (gE X Y - 1) := by
    rw [e2, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Nat.cast_mul, Matrix.mul_assoc]
  rw [e3, one_mul, mul_one, hT] at h3
  exact intDiv_cancel X (Nat.mul_ne_zero hdB0.ne' hdB'0.ne') h3

end Div

section Gam

def Gam : Set X.B.I.Ginf :=
  {s | ∃ γ ∈ X.B.I.GFset, γ.1 = s ∧ γ.1 ∈ X.NinfU u ∧ γ.2 ∈ X.NfinU u ∧ γ.2 ∈ X.B.I.Kg X.B.g}

theorem gam_mul : ∀ a ∈ Gam X u, ∀ b ∈ Gam X u, a * b ∈ Gam X u := by
  rintro _ ⟨γ, hγ, rfl, h1, h2, h3⟩ _ ⟨γ', hγ', rfl, h1', h2', h3'⟩
  exact ⟨γ * γ', (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I).mul_mem hγ hγ', rfl,
    (NinfSub X.eR (X.zR u)).mul_mem h1 h1', (NfinSub X.eR (X.zR u)).mul_mem h2 h2', kg_mul X h3 h3'⟩

theorem gam_one : (1 : X.B.I.Ginf) ∈ Gam X u :=
  ⟨1, (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I).one_mem, rfl, (NinfSub X.eR (X.zR u)).one_mem,
    (NfinSub X.eR (X.zR u)).one_mem, one_mem_Kg X.B.I X.B.g⟩

theorem gam_sub : Gam X u ⊆ NOinf X u := by
  rintro _ ⟨γ, hγ, rfl, h1, h2, h3⟩
  exact ⟨γ, hγ, rfl, h1, h2, principal_congruence_mem_level X (kg_conj X h3 (X.xu_K u))⟩

end Gam

section Descent

theorem inUJ_of (v : InfinitePlace X.B.I.F) {C : Matrix (Kap X) (Kap X) ℂ} (hC : Cᴴ * JBv X v * C = JBv X v) :
    Formalism.REAL.inUJ (X.B.I.ε v) (Bv X v * C * Bv' X v) := by
  unfold Formalism.REAL.inUJ
  have hh : (Bv' X v)ᴴ * (Bv X v)ᴴ = 1 := by rw [← conjTranspose_mul, Bv_mul_Bv', conjTranspose_one]
  calc (Bv X v * C * Bv' X v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (Bv X v * C * Bv' X v)
      = (Bv' X v)ᴴ * (Cᴴ * ((Bv X v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Bv X v) * C) * Bv' X v := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (Bv' X v)ᴴ * ((Bv X v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Bv X v) * Bv' X v := by rw [Bv_gram, hC]
    _ = ((Bv' X v)ᴴ * (Bv X v)ᴴ) * Formalism.REAL.Jm (X.B.I.ε v) * (Bv X v * Bv' X v) := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (X.B.I.ε v) := by rw [hh, Bv_mul_Bv', Matrix.one_mul, Matrix.mul_one]

theorem Mv_mk (v : InfinitePlace X.B.I.F) (s : X.B.I.Ginf) (C : Matrix (Kap X) (Kap X) ℂ)
    (hs : uMat (s v) = Bv X v * C * Bv' X v) : Mv X v s = C := by
  unfold Mv
  rw [hs]
  simp only [← Matrix.mul_assoc, Bv'_mul_Bv, Matrix.one_mul]
  rw [Matrix.mul_assoc, Bv'_mul_Bv, Matrix.mul_one]

theorem Mv_continuous (v : InfinitePlace X.B.I.F) : Continuous fun s : X.B.I.Ginf => Mv X v s := by
  have hu : Continuous fun s : X.B.I.Ginf => uMat (s v) :=
    Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply v))
  exact (continuous_const.matrix_mul hu).matrix_mul continuous_const

def Sset (ρ : ℝ) : Set X.B.I.Ginf :=
  Set.univ.pi fun v => (fun g : Formalism.REAL.UJ (X.B.I.ε v) => uMat g) ⁻¹'
    ((fun Z : Matrix (Kap X) (Kap X) ℂ => Bv X v * cay (N0 D) Z * Bv' X v) ''
      (Set.univ.pi fun _ : Kap X => Set.univ.pi fun _ : Kap X => Metric.closedBall (0 : ℂ) ρ :
        Set (Matrix (Kap X) (Kap X) ℂ)))

theorem sset_compact (ρ : ℝ) : IsCompact (Sset X ρ) :=
  isCompact_univ_pi fun v => ((Formalism.REAL.uJEmb X.B.I.n (X.B.I.ε v)).1).isCompact_preimage
    ((isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall (0 : ℂ) ρ).image
      ((continuous_const.matrix_mul (cay_continuous (N0 D))).matrix_mul continuous_const))

theorem mem_sset {ρ : ℝ} {s : X.B.I.Ginf} (h : ∀ v, ∃ Z : Matrix (Kap X) (Kap X) ℂ, (∀ i j, ‖Z i j‖ ≤ ρ) ∧
    uMat (s v) = Bv X v * cay (N0 D) Z * Bv' X v) : s ∈ Sset X ρ := by
  intro v _
  obtain ⟨Z, hZ, e⟩ := h v
  refine ⟨Z, Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => ?_, e.symm⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hZ i j

end Descent

section Main

theorem step_exists (hL : LatStepP X) :
    ∃ ρ : ℝ, ∀ k, 1 ≤ k → ∀ x : X.B.I.Ginf, (∀ v, InPat (lvk X) k (Mv X v x - 1)) →
      ∃ γ ∈ Gam X u, ∃ y : X.B.I.Ginf, (∀ v, InPat (lvk X) (k + 1) (Mv X v y - 1)) ∧
        ∃ s ∈ Sset X ρ, x = γ * y * s := by
  obtain ⟨cL, hcL0, hcL⟩ := exists_cL X
  obtain ⟨dL, hdL0, hdL⟩ := exists_dL X
  obtain ⟨dB, hdB0, hdB⟩ := exists_den (nt_int_mul_of X.B.I) (Bm X)
  obtain ⟨dB', hdB'0, hdB'⟩ := exists_den (nt_int_mul_of X.B.I) (Bm' X)
  have hg0 : 0 < X.B.g := by
    rw [X.g_eq]
    exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have ht0 : 0 < X.B.g * cL * dL := Nat.mul_pos (Nat.mul_pos hg0 hcL0) hdL0
  obtain ⟨ρ, -, hρ⟩ := hL (2 ^ N0 D * (dB * dB' * (X.B.g * cL * dL)))
    (Nat.mul_pos (pow_pos two_pos _) (Nat.mul_pos (Nat.mul_pos hdB0 hdB'0) ht0))
  refine ⟨ρ, fun k hk x hx => ?_⟩
  let P : InfinitePlace X.B.I.F → Matrix (Kap X) (Kap X) ℂ :=
    fun v => proj (JBv X v) (JBv' X v) (Mv X v x - 1)
  have hPk : ∀ v, InPat (lvk X) k (P v) := fun v => inPat_proj (JBv_graded X v) (JBv'_graded X v) (hx v)
  have hPs : ∀ v, (P v)ᴴ * JBv X v = -(JBv X v * P v) := fun v =>
    proj_skew (JBv_herm X v) (JBv'_herm X v) (JBv'_mul X v) (JBv_mul X v) _
  obtain ⟨Y, hYk, hYs, hYd, hYb⟩ := hρ k hk P hPk hPs
  have hdiv : ∀ {Y' : Matrix (Kap X) (Kap X) X.B.I.E}, IntDiv (2 ^ N0 D * (dB * dB' * (X.B.g * cL * dL))) Y' →
      IntDiv (X.B.g * cL * dL) (gE X Y' - 1) := fun h => gE_intDiv X hdB0 hdB'0 hdB hdB' h
  have hinv : X.B.I.fmat (gA X hk hYk hYs).2⁻¹ = (gE X (-Y)).map (iE X) := by
    have h1 : X.B.I.fmat (gA X hk hYk hYs).2 * (gE X (-Y)).map (iE X) = 1 := by
      rw [fmat_gA, ← Matrix.map_mul, gE_mul' X hk hYk, Matrix.map_one _ (map_zero _) (map_one _)]
    calc X.B.I.fmat (gA X hk hYk hYs).2⁻¹
        = X.B.I.fmat (gA X hk hYk hYs).2⁻¹ * (X.B.I.fmat (gA X hk hYk hYs).2 * (gE X (-Y)).map (iE X)) := by
          rw [h1, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, Cut.fmat_inv_mul, Matrix.one_mul]
  have hγ : (gA X hk hYk hYs).1 ∈ Gam X u :=
    ⟨gA X hk hYk hYs, gA_GF X hk hYk hYs, rfl, gA_ninf X u hk hYk hYs, gA_nfin X u hk hYk hYs,
      kg_of X hcL hdL (fmat_gA X hk hYk hYs) hinv (hdiv hYd) (hdiv (intDiv_neg hYd))⟩
  let Z : InfinitePlace X.B.I.F → Matrix (Kap X) (Kap X) ℂ := fun v => P v - Y.map (X.B.I.φ v)
  have hZk : ∀ v, InPat (lvk X) k (Z v) := fun v => inPat_sub (hPk v) (inPat_map _ hYk)
  have hZs : ∀ v, (Z v)ᴴ * JBv X v = -(JBv X v * Z v) := by
    intro v
    show (P v - Y.map (X.B.I.φ v))ᴴ * JBv X v = -(JBv X v * (P v - Y.map (X.B.I.φ v)))
    rw [conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, hPs v, skew_map X v hYs]
    abel
  have hCu : ∀ v, (cay (N0 D) (Z v))ᴴ * JBv X v * cay (N0 D) (Z v) = JBv X v :=
    fun v => cay_unitary (hZs v) (nil_of_pat X hk (hZk v) _)
  let s : X.B.I.Ginf := fun v => mkUJ (X.B.I.ε v) _ (inUJ_of X v (hCu v))
  have hMs : ∀ v, Mv X v s = cay (N0 D) (Z v) := fun v => Mv_mk X v s _ rfl
  have hsS : s ∈ Sset X ρ := mem_sset X fun v => ⟨Z v, fun i j => hYb v i j, rfl⟩
  refine ⟨(gA X hk hYk hYs).1, hγ, (gA X hk hYk hYs).1⁻¹ * x * s⁻¹, fun v => ?_, s, hsS, by group⟩
  rw [Mv_mul, Mv_mul, Mv_inv, Mv_inv, Mv_gA, hMs]
  have h := step_mat (JBv_graded X v) (JBv'_graded X v) (JBv_herm X v) (JBv'_herm X v) (JBv'_mul X v)
    (JBv_mul X v) (2 * D.R.rS + 1) (Mv_unitary X v x) (hx v) (inPat_map (X.B.I.φ v) hYk) (skew_map X v hYs)
  exact inPat_mono (by omega) h

theorem noCocompact_of (hL : LatStepP X) : NOCocompact X u := by
  obtain ⟨ρ, hρ⟩ := step_exists X u hL
  let R : ℕ → Set X.B.I.Ginf := fun j => {x | ∀ v, InPat (lvk X) (j + 1) (Mv X v x - 1)}
  have hm : ∀ x ∈ R (2 * D.R.rS + 1), x = 1 := by
    intro x hxR
    funext v
    have h0 : Mv X v x - 1 = 0 :=
      eq_zero_of_inPat (L := 2 * D.R.rS + 1 + 1) (fun i => by have := lvk_le X i; omega) (hxR v)
    have hu : uMat (x v) = 1 := by rw [uMat_eq X v x, sub_eq_zero.1 h0, Matrix.mul_one, Bv_mul_Bv']
    exact Subtype.ext (Units.ext (by simpa using hu))
  obtain ⟨C, hC, hcov⟩ := cover_of_steps (Gam X u) (gam_mul X u) (gam_one X u) R (2 * D.R.rS + 1) hm
    (fun _ => Sset X ρ) (fun _ => sset_compact X ρ) (fun k _ x hx => hρ (k + 1) (by omega) x hx)
  refine ⟨C, hC, fun x hx => ?_⟩
  obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov x fun v => pat_of_mem X u v hx
  exact ⟨γ, gam_sub X u hγ, c, hc, rfl⟩

theorem noCocompactC_of (hL : LatStepC) : NOCocompactC := fun D X u => noCocompact_of X u (hL D X)

theorem ninf_closed : IsClosed (X.NinfU u) := by
  have e : X.NinfU u = ⋂ v, ⋂ i, ⋂ j, ⋂ (_ : lvk X j < lvk X i + 1), {s : X.B.I.Ginf | (Mv X v s - 1) i j = 0} := by
    ext s
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact ⟨fun hs v i j h => pat_of_mem X u v hs i j h, fun h v => inN_of_pat X u v _ (fun i j hij => h v i j hij)⟩
  rw [e]
  exact isClosed_iInter fun v => isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (((Mv_continuous X v).sub continuous_const).matrix_elem i j) continuous_const

end Main

end Formalism.L2.SG.Pf.UnipB
