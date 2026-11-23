import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrLink
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnWittFrameBasisBlockGramStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicColumnLatticeEqSpanPartTransportedFrameStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.Proj

section Helpers

open Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.Pf.Level Formalism.L2.SG.Pf

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def tInv : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F :=
  Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((((D.mem u).A.T : ℕ) : X.B.I.E)⁻¹)

def pc : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I :=
  prA X + (hAlin X (incl X.B.I (X.zR u))).smulRight (tInv X u • incl X.B.I (X.zR u))

theorem pc_apply (y : VA X.B.I) : pc X u y =
    prA X y + hA X.B.I (incl X.B.I (X.zR u)) y • (tInv X u • incl X.B.I (X.zR u)) := by
  simp [pc, hAlin_apply]

theorem T_mul_tInv : (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * tInv X u = 1 := by
  have h0 : (((D.mem u).A.T : ℕ) : X.B.I.E) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  have h1 : (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (((D.mem u).A.T : ℕ) : X.B.I.E) := (map_natCast _ _).symm
  rw [h1, tInv, ← map_mul, mul_inv_cancel₀ h0, map_one]

theorem T_smul_pc (y : VA X.B.I) :
    (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • pc X u y =
      (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • prA X y +
        hA X.B.I (incl X.B.I (X.zR u)) y • incl X.B.I (X.zR u) := by
  rw [pc_apply, smul_add, smul_smul, smul_smul, mul_right_comm, T_mul_tInv, one_mul]

theorem adelicHermitian_anisotropic_self_eq_neg_norm : hA X.B.I (incl X.B.I (X.zR u)) (incl X.B.I (X.zR u)) =
    -(((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
  rw [HidaSetting.zR, hA_crd, X.zu_norm]
  simp

theorem hA_z_e (a : Fin D.R.rS) : hA X.B.I (incl X.B.I (X.zR u)) (incl X.B.I (X.eR a)) = 0 := by
  have h := (VS D).herm.eq (X.eX a) (X.zu u)
  rw [(X.zu_orth u a).1, map_zero] at h
  rw [HidaSetting.zR, HidaSetting.eR, hA_crd, ← h]
  simp

theorem hA_z_f (a : Fin D.R.rS) : hA X.B.I (incl X.B.I (X.zR u)) (incl X.B.I (X.fR a)) = 0 := by
  have h := (VS D).herm.eq (X.fY a) (X.zu u)
  rw [(X.zu_orth u a).2, map_zero] at h
  rw [HidaSetting.zR, HidaSetting.fR, hA_crd, ← h]
  simp

theorem adelicHermitian_hyperbolicE_anisotropic_eq_zero (a : Fin D.R.rS) : hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (X.zR u)) = 0 := by
  rw [HidaSetting.zR, HidaSetting.eR, hA_crd, (X.zu_orth u a).1]
  simp

theorem adelicHermitian_hyperbolicF_anisotropic_eq_zero (a : Fin D.R.rS) : hA X.B.I (incl X.B.I (X.fR a)) (incl X.B.I (X.zR u)) = 0 := by
  rw [HidaSetting.zR, HidaSetting.fR, hA_crd, (X.zu_orth u a).2]
  simp

theorem pc_e (a : Fin D.R.rS) : pc X u (incl X.B.I (X.eR a)) = 0 := by
  rw [pc_apply, prA_e, hA_z_e]; simp

theorem pc_f (a : Fin D.R.rS) : pc X u (incl X.B.I (X.fR a)) = 0 := by
  rw [pc_apply, prA_f, hA_z_f]; simp

theorem orthogonalProjection_anisotropic_eq_zero : pc X u (incl X.B.I (X.zR u)) = 0 := by
  rw [pc_apply, prA_fix X _ (adelicHermitian_hyperbolicE_anisotropic_eq_zero X u) (adelicHermitian_hyperbolicF_anisotropic_eq_zero X u), adelicHermitian_anisotropic_self_eq_neg_norm, smul_smul, neg_mul, T_mul_tInv]
  simp

theorem zR_mem : X.zR u ∈ X.B.I.L := by
  refine (X.L_eq _).2 ?_
  show toV X (X.crd (X.zu u)) ∈ (VS D).L0
  rw [toV_crd]
  exact Lb_le X (X.zu_Lb u)

theorem hE_z_int {x : Fin X.B.I.n → X.B.I.E} (hx : x ∈ X.B.I.L) :
    hE X (X.zR u) x ∈ (algebraMap (𝓞 X.B.I.E) X.B.I.E).range := by
  have hv : toV X x ∈ (VS D).L0 := (X.L_eq x).1 hx
  have hz : X.zu u ∈ (VS D).L0 := Lb_le X (X.zu_Lb u)
  have hd : toV X x ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT (VS D).L0 := by
    rw [(VS D).baseLattice_isUnimodular]; exact hv
  have h2 : (VS D).hT (X.zu u) (toV X x) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) :=
    (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hd (X.zu u)) hz
  obtain ⟨b, hb⟩ := Submodule.mem_one.1 h2
  have e : hE X (X.zR u) x = X.ιE.symm ((VS D).hT (X.zu u) (toV X x)) := by
    rw [← toV_crd X (X.zu u), ← iota_hE, RingEquiv.symm_apply_apply]
    rfl
  rw [e, ← hb]
  exact ⟨⟨_, (NumberField.RingOfIntegers.isIntegral_coe b).map
      (X.ιE.symm : D.host.E →+* X.B.I.E).toIntAlgHom⟩, rfl⟩

theorem T_pc_Lf (y : VA X.B.I) (hy : y ∈ X.B.I.Lf) :
    (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • pc X u y ∈ X.B.I.Lf := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, rfl⟩ := hy
    show (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • pc X u (incl X.B.I x) ∈ X.B.I.Lf
    rw [T_smul_pc]
    refine add_mem (natsmul_mem X _ (prA_Lf X _ (incl_mem_Lf X _ x.2))) ?_
    obtain ⟨a, ha⟩ := hE_z_int X u x.2
    rw [hA_incl, show Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.zR u) (x : Fin X.B.I.n → X.B.I.E) = hE X (X.zR u) x from rfl,
      ← ha, ← incl_smul]
    refine incl_mem_Lf X _ ?_
    have := X.B.I.L.smul_mem a (zR_mem X u)
    rwa [← IsScalarTower.algebraMap_smul X.B.I.E a] at this
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, smul_add]; exact add_mem hy hz
  | smul c y _ hy =>
    rw [Subring.smul_def, map_smul, smul_comm]
    exact X.B.I.Lf.smul_mem c hy

theorem inAt_add {x y : VA X.B.I} (hx : InAt X.B.I X.B.g X.B.g x) (hy : InAt X.B.I X.B.g X.B.g y) :
    InAt X.B.I X.B.g X.B.g (x + y) := by
  obtain ⟨c, hc, hcx⟩ := hx
  obtain ⟨d, hd, hdy⟩ := hy
  refine ⟨c * d, Nat.coprime_mul_iff_left.2 ⟨hc, hd⟩, ?_⟩
  have e : (((c * d : ℕ)) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (x + y) =
      (d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x) +
      (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • y) := by
    rw [smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)]
  rw [e]
  exact add_mem (natsmul_mem X _ hcx) (natsmul_mem X _ hdy)

theorem inAt_neg {x : VA X.B.I} (hx : InAt X.B.I X.B.g X.B.g x) : InAt X.B.I X.B.g X.B.g (-x) := by
  obtain ⟨c, hc, hcx⟩ := hx
  exact ⟨c, hc, by rw [smul_neg]; exact neg_mem hcx⟩

theorem inAt_natsmul (t : ℕ) {x : VA X.B.I} (hx : InAt X.B.I X.B.g X.B.g x) :
    InAt X.B.I X.B.g X.B.g ((t : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x) := by
  obtain ⟨c, hc, hcx⟩ := hx
  exact ⟨c, hc, by rw [smul_comm]; exact natsmul_mem X _ hcx⟩

theorem inAt_of_mem {x : VA X.B.I} (hx : x ∈ mL X.B.I X.B.g) : InAt X.B.I X.B.g X.B.g x :=
  ⟨1, Nat.coprime_one_left _, by simpa using hx⟩

theorem inAt_sum {ι : Type} (s : Finset ι) (x : ι → VA X.B.I)
    (h : ∀ i ∈ s, InAt X.B.I X.B.g X.B.g (x i)) : InAt X.B.I X.B.g X.B.g (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact inAt_of_mem X (by simp)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact inAt_add X (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem T_sub_mem (hT : (D.mem u).A.T ≡ 1 [MOD X.B.g]) {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) :
    (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • y - y ∈ mL X.B.I X.B.g := by
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd.1 hT.symm)
  have hg : (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • y ∈ mL X.B.I X.B.g := unitaryCongruence.smul_mem_mL X.B.I hy
  have e : (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • y - y =
      k • ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • y) := by
    rw [natsmul_eq, natsmul_eq, ← natCast_zsmul, ← natCast_zsmul y X.B.g, smul_smul, mul_comm k, ← hk, sub_smul, Nat.cast_one, one_smul]
  rw [e]
  exact zsmul_mem hg k

theorem T_pc_sub_mem (hT : (D.mem u).A.T ≡ 1 [MOD X.B.g]) {y : VA X.B.I} (hy : y ∈ X.B.I.Lf)
    (hef : ∀ a, InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.eR a)) y • incl X.B.I (X.fR a)) ∧
      InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.fR a)) y • incl X.B.I (X.eR a)))
    (hz : InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.zR u)) y • incl X.B.I (X.zR u))) :
    (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • pc X u y - y ∈ mL X.B.I X.B.g := by
  have hW : (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • pc X u y - y ∈ X.B.I.Lf :=
    sub_mem (T_pc_Lf X u y hy) hy
  have e : (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • pc X u y - y =
      ((((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • y - y) +
      (-((((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) •
          ∑ a, hA X.B.I (incl X.B.I (X.fR a)) y • incl X.B.I (X.eR a)) +
        (-((((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) •
          ∑ a, hA X.B.I (incl X.B.I (X.eR a)) y • incl X.B.I (X.fR a)) +
        hA X.B.I (incl X.B.I (X.zR u)) y • incl X.B.I (X.zR u))) := by
    rw [T_smul_pc, prA_apply, smul_sub, smul_sub]
    abel
  have hin : InAt X.B.I X.B.g X.B.g
      ((((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • pc X u y - y) := by
    rw [e]
    exact inAt_add X (inAt_of_mem X (T_sub_mem X u hT hy))
      (inAt_add X (inAt_neg X (inAt_natsmul X _ (inAt_sum X _ _ fun a _ => (hef a).2)))
        (inAt_add X (inAt_neg X (inAt_natsmul X _ (inAt_sum X _ _ fun a _ => (hef a).1))) hz))
  obtain ⟨m, hm, hmW⟩ := hin
  exact bez_vec X (mL X.B.I X.B.g) le_rfl hW hm hmW

theorem frame_expand (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (Q : Matrix (Fin X.B.I.n) (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) X.B.I.E)
    (Qi : Matrix (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) (Fin X.B.I.n) X.B.I.E)
    (hQ : Q * Qi = 1) (hq : ∀ j i, Q i (Sum.inl j) = X.crd (qFr wt j) i)
    (he : ∀ a i, Q i (Sum.inr (Sum.inl a)) = X.eR a i)
    (hf : ∀ a i, Q i (Sum.inr (Sum.inr (Sum.inl a))) = X.fR a i)
    (hz : ∀ i, Q i (Sum.inr (Sum.inr (Sum.inr ()))) = X.zR u i) (y : VA X.B.I) :
    ∃ (w : Fin (D.R.N 0) → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (s t : Fin D.R.rS → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
      (r : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
      y = ∑ j, w j • qA X wt j + (∑ a, s a • incl X.B.I (X.eR a) + (∑ a, t a • incl X.B.I (X.fR a) +
        r • incl X.B.I (X.zR u))) := by
  let f : X.B.I.E →+* X.B.I.E ⊗[X.B.I.F] Af X.B.I.F := Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)
  set v := (Qi.map f) *ᵥ y with hv
  have h1 : (Q.map f) *ᵥ v = y := by
    rw [hv, mulVec_mulVec, ← Matrix.map_mul, hQ, Matrix.map_one _ (map_zero f) (map_one f), one_mulVec]
  refine ⟨fun j => v (Sum.inl j), fun a => v (Sum.inr (Sum.inl a)), fun a => v (Sum.inr (Sum.inr (Sum.inl a))),
    v (Sum.inr (Sum.inr (Sum.inr ()))), ?_⟩
  conv_lhs => rw [← h1]
  funext i
  simp only [mulVec, dotProduct, Fintype.sum_sum_type, Matrix.map_apply, Pi.add_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, hq, he, hf, hz, qA, incl, Fintype.sum_unique]
  simp only [mul_comm]
  rfl

end Helpers

end GlobalTheory.St.G.Proj

theorem GlobalTheory.St.G.g_proj : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∃ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), c ≡ 1 [MOD X.B.g] ∧ (∀ y, ∃ x, p y = embA X wt ιA x) ∧ (∀ x, p (embA X wt ιA x) = embA X wt ιA x) ∧ (∀ y ∈ X.B.I.Lf, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p y ∈ X.B.I.Lf) ∧ (∀ a, p (incl X.B.I (X.eR a)) = 0 ∧ p (incl X.B.I (X.fR a)) = 0) ∧ p (incl X.B.I (X.zR u)) = 0 ∧ ∀ y ∈ X.B.I.Lf, (∀ a, InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.eR a)) y • incl X.B.I (X.fR a)) ∧ InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.fR a)) y • incl X.B.I (X.eR a))) → InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.zR u)) y • incl X.B.I (X.zR u)) → (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p y - y ∈ mL X.B.I X.B.g := by
  intro D X u wt ιA hW hI
  obtain ⟨Q, Qi, G', hQ, -, hq, he, hf, hz, -, -⟩ := GlobalTheory.T.columnWittFrame_basis_blockGram D X u wt hW
  obtain ⟨-, -, -, hef, hzq, -⟩ := GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hI
  have hfix : ∀ x, Proj.pc X u (embA X wt ιA x) = embA X wt ιA x := fun x => by
    rw [Proj.pc_apply, Formalism.L2.SG.Pf.Level.prA_fix X _ (fun a => (hef x a).1) (fun a => (hef x a).2), hzq]
    simp
  have hT : (D.mem u).A.T ≡ 1 [MOD X.B.g] := by
    rw [X.g_eq]
    exact D.T_modEq_of_dvd u (dvd_trans (dvd_pow_self _ two_ne_zero) D.gg_dvd_modT)
  refine ⟨(D.mem u).A.T, Proj.pc X u, hT, ?_, hfix, Proj.T_pc_Lf X u,
    fun a => ⟨Proj.pc_e X u a, Proj.pc_f X u a⟩, Proj.orthogonalProjection_anisotropic_eq_zero X u, ?_⟩
  · intro y
    obtain ⟨w, s, t, r, rfl⟩ := Proj.frame_expand X u wt Q Qi hQ hq he hf hz y
    refine ⟨fun j => ιA (w j), ?_⟩
    have hqj : ∀ j, Proj.pc X u (qA X wt j) = qA X wt j := fun j => by
      have h := hfix (Pi.single j 1)
      have e : embA X wt ιA (Pi.single j 1) = qA X wt j := by
        simp [embA, Pi.single_apply]
      rwa [e] at h
    simp only [map_add, map_sum, map_smul, Proj.pc_e, Proj.pc_f, Proj.orthogonalProjection_anisotropic_eq_zero, hqj, smul_zero,
      Finset.sum_const_zero, add_zero]
    simp [embA]
  · intro y hy h1 h2
    exact Proj.T_pc_sub_mem X u hT hy h1 h2

end
