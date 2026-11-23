import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GeneralLinearLevel.HpartUnique

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.EabGlW

open Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Ec (Z : Mx k r) (f : Mx k r → E) : Mx k r → E :=
  fun g => RdV (hpart1 (Hpk k r) Z) f g + Complex.I • RdV (hpart2 (Hpk k r) Z) f g

def Good (k r : ℕ) (i : Fin (r + 1)) (Z : Mx k r) : Prop :=
  hpart1 (Hpk k r) Z ∈ LieL k r i ∧ hpart2 (Hpk k r) Z ∈ LieL k r i

theorem ec_comm {i : Fin (r + 1)} {Z W : Mx k r} (hZ : Good k r i Z) (hW : Good k r i W)
    {f F : Mx k r → E} {U : Set (Mx k r)} (hL : LocExt (Glev k r i) f F U) {g : Mx k r}
    (hg : g ∈ U) (hgG : g ∈ Glev k r i) :
    Ec Z (Ec W f) g - Ec W (Ec Z f) g = Ec (Z * W - W * Z) f g := by
  obtain ⟨hX1, hX2⟩ := hZ
  obtain ⟨hY1, hY2⟩ := hW
  have hZW := commutator_complex_expand (hpart1 (Hpk k r) Z) (hpart2 (Hpk k r) Z) (hpart1 (Hpk k r) W)
    (hpart2 (Hpk k r) W)
  rw [← hpart_decomp Z, ← hpart_decomp W] at hZW
  have hP := lieL_sub (lieL_bracket hX1 hY1) (lieL_bracket hX2 hY2)
  have hQ := lieL_add (lieL_bracket hX1 hY2) (lieL_bracket hX2 hY1)
  obtain ⟨h1, h2⟩ := hpart_unique hP.1 hQ.1
  have eZ : Ec Z f = fun h => RdV (hpart1 (Hpk k r) Z) f h + Complex.I • RdV (hpart2 (Hpk k r) Z) f h :=
    rfl
  have eW : Ec W f = fun h => RdV (hpart1 (Hpk k r) W) f h + Complex.I • RdV (hpart2 (Hpk k r) W) f h :=
    rfl
  simp only [Ec]
  rw [eZ, eW]
  rw [loc_comb (flow_of_lieL hX1) (flow_of_lieL hY1) (flow_of_lieL hY2) hL hg hgG,
    loc_comb (flow_of_lieL hX2) (flow_of_lieL hY1) (flow_of_lieL hY2) hL hg hgG,
    loc_comb (flow_of_lieL hY1) (flow_of_lieL hX1) (flow_of_lieL hX2) hL hg hgG,
    loc_comb (flow_of_lieL hY2) (flow_of_lieL hX1) (flow_of_lieL hX2) hL hg hgG,
    hZW, h1, h2,
    loc_sub (flow_of_lieL (lieL_bracket hX1 hY1)) (flow_of_lieL (lieL_bracket hX2 hY2))
      (flow_of_lieL hP) hL hg hgG,
    loc_add (flow_of_lieL (lieL_bracket hX1 hY2)) (flow_of_lieL (lieL_bracket hX2 hY1))
      (flow_of_lieL hQ) hL hg hgG,
    ← loc_bracket (flow_of_lieL hX1) (flow_of_lieL hY1) (flow_of_lieL (lieL_bracket hX1 hY1)) hL hg hgG,
    ← loc_bracket (flow_of_lieL hX2) (flow_of_lieL hY2) (flow_of_lieL (lieL_bracket hX2 hY2)) hL hg hgG,
    ← loc_bracket (flow_of_lieL hX1) (flow_of_lieL hY2) (flow_of_lieL (lieL_bracket hX1 hY2)) hL hg hgG,
    ← loc_bracket (flow_of_lieL hX2) (flow_of_lieL hY1) (flow_of_lieL (lieL_bracket hX2 hY1)) hL hg hgG]
  simp only [smul_add, smul_sub, smul_smul, Complex.I_mul_I, neg_smul, one_smul]
  abel

lemma hpart1_sub (A B : Mx k r) :
    hpart1 (Hpk k r) (A - B) = hpart1 (Hpk k r) A - hpart1 (Hpk k r) B := by
  simp only [hpart1, Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul, smul_sub]
  abel

lemma hpart2_sub (A B : Mx k r) :
    hpart2 (Hpk k r) (A - B) = hpart2 (Hpk k r) A - hpart2 (Hpk k r) B := by
  simp only [hpart2, Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul, smul_sub, smul_add]
  abel

theorem ec_sub {i : Fin (r + 1)} {A B : Mx k r} (hA : Good k r i A) (hB : Good k r i B)
    {f F : Mx k r → E} {U : Set (Mx k r)} (hL : LocExt (Glev k r i) f F U) {g : Mx k r}
    (hg : g ∈ U) (hgG : g ∈ Glev k r i) :
    Ec (A - B) f g = Ec A f g - Ec B f g := by
  simp only [Ec]
  rw [hpart1_sub, hpart2_sub,
    loc_sub (flow_of_lieL hA.1) (flow_of_lieL hB.1) (flow_of_lieL (lieL_sub hA.1 hB.1)) hL hg hgG,
    loc_sub (flow_of_lieL hA.2) (flow_of_lieL hB.2) (flow_of_lieL (lieL_sub hA.2 hB.2)) hL hg hgG,
    smul_sub]
  abel

lemma ec_zero (f : Mx k r → E) (g : Mx k r) : Ec (0 : Mx k r) f g = 0 := by
  simp [Ec, hpart1, hpart2, RdV]

lemma inV_zero {i : Fin (r + 1)} : InV k r i (0 : Mx k r) := fun _ _ _ => rfl

lemma inV_single {i : Fin (r + 1)} (x y : Fin (mdim k r i)) :
    InV k r i (Matrix.single (posL k r i x) (posL k r i y) (1 : ℂ)) := by
  intro p q h
  rw [Matrix.single_apply]
  split_ifs with hh
  · obtain ⟨rfl, rfl⟩ := hh
    exfalso
    have hx := x.isLt
    have hy := y.isLt
    have hi := i.isLt
    unfold mdim at hx hy
    rcases h with h | h <;> (simp only [Out, posL] at h; omega)
  · rfl

end Formalism.FourierDecayAlt.Q.EabGlW
