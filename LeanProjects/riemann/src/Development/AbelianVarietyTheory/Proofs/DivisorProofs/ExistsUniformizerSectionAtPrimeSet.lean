import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedPairLatticeIffAdjointFrameMatrixInte
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedPairLatticeIffFrameMatrixIntegralOnH
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualHalfLatticeDetectingCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinPartMulIncAMem
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.QResChar

open Formalism.IndefR.Fin.LevelGroupLemmas.Lat (liftE lift lift_add lift_zero toEAf_liftE eq_lift_of_infPart)

theorem liftE_add {D : D7} (a b : EAf D) : liftE (a + b) = liftE a + liftE b := by
  unfold liftE
  rw [map_add, lift_add]

theorem liftE_zero {D : D7} : liftE (0 : EAf D) = 0 := by
  unfold liftE
  rw [map_zero, lift_zero]

theorem liftE_toEAf {D : D7} {z : AE D} (hz : infPart D z = 0) : liftE (toEAf D z) = z := by
  conv_rhs => rw [eq_lift_of_infPart z hz]
  unfold liftE
  congr 1
  exact (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm_apply_apply (finPart D z)

def psiE {D : D7} (ψ : AddChar (AF D.host.F) ℂ) : AddChar (EAf D) ℂ where
  toFun z := ψ (-Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * liftE z))
  map_zero_eq_one' := by
    rw [liftE_zero, mul_zero, map_zero, neg_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' a b := by
    rw [liftE_add, mul_add, map_add, neg_add, AddChar.map_add_eq_mul]

theorem psi_sympl {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D))
    (βT : GL (Fin T.rank) (EAf D)) (t y : WO S T) (hy : ∀ i j, infPart D (y i j) = 0) :
    ψ (symplO S T t y) = psiE ψ (Matrix.trace (frMapAdj S T βS βT t * frMapO S T βS βT y)) := by
  have hinf : infPart D (hO S T y t) = 0 := by
    simp only [hO, map_sum, map_mul, hy, mul_zero, Finset.sum_const_zero]
  rw [GlobalTheory.OrientedHeis.symplO_skew y t, ← GlobalTheory.HalfDuality.trace_id]
  change _ = ψ (-Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * liftE (toEAf D (hO S T y t))))
  rw [liftE_toEAf hinf]
  rfl

theorem resS_surj {D : D7} (PP : Pl D.host.E) : Function.Surjective (resS D.host.F PP) := by
  intro q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨_, resS_oToS PP a⟩

theorem fac {D : D7} (Φ : AddChar (EAf D) ℂ) (Q : Finset (Pl D.host.E)) (a : Pl D.host.E → EAf D)
    (h1 : ∀ PP ∈ Q, ∀ w (hw : w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), resS D.host.F PP ⟨w, hw⟩ = 0 → Φ (a PP * w) = 1)
    (h2 : ∀ PP ∈ Q, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, Φ (a PP * w) ≠ 1) :
    ∃ ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, (∀ PP ∈ Q, (ψP PP).IsPrimitive) ∧
      ∀ PP ∈ Q, ∀ w (hw : w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), ψP PP (resS D.host.F PP ⟨w, hw⟩) = Φ (a PP * w) := by
  have hcong : ∀ PP ∈ Q, ∀ w w' : Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP w = resS D.host.F PP w' →
      Φ (a PP * w) = Φ (a PP * w') := by
    intro PP hPP w w' h
    have e : a PP * (w : EAf D) = a PP * (w' : EAf D) + a PP * ((w - w' : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
      push_cast; ring
    rw [e, AddChar.map_add_eq_mul, h1 PP hPP _ (w - w').2 (by rw [map_sub, h, sub_self]), mul_one]
  let L : ∀ PP : Pl D.host.E, kP PP → Formalism.L2.Herm.intAf D.host.F D.host.E := fun PP => Function.surjInv (resS_surj PP)
  have hL : ∀ PP x, resS D.host.F PP (L PP x) = x := fun PP => Function.surjInv_eq (resS_surj PP)
  let ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ := fun PP => if hPP : PP ∈ Q then
    { toFun := fun x => Φ (a PP * (L PP x : EAf D))
      map_zero_eq_one' := h1 PP hPP _ (L PP 0).2 (hL PP 0)
      map_add_eq_mul' := fun x y => by
        rw [← AddChar.map_add_eq_mul, ← mul_add]
        exact hcong PP hPP (L PP (x + y)) (L PP x + L PP y) (by rw [map_add, hL, hL, hL]) }
    else 1
  have hψ : ∀ PP ∈ Q, ∀ w (hw : w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
      ψP PP (resS D.host.F PP ⟨w, hw⟩) = Φ (a PP * w) := by
    intro PP hPP w hw
    simp only [ψP, dif_pos hPP]
    exact hcong PP hPP _ ⟨w, hw⟩ (hL PP _)
  refine ⟨ψP, fun PP hPP => ?_, hψ⟩
  obtain ⟨w, hw, hne⟩ := h2 PP hPP
  have hnt : ψP PP ≠ 1 := fun h => hne (by rw [← hψ PP hPP w hw, h, AddChar.one_apply])
  intro c hc
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  letI := Ideal.Quotient.field PP.asIdeal
  intro h
  apply hnt
  ext x
  have := DFunLike.congr_fun h (c⁻¹ * x)
  rw [AddChar.mulShift_apply, ← mul_assoc, mul_inv_cancel₀ hc, one_mul] at this
  simpa using this

open GlobalTheory.StdFrames (cpt) in

theorem mem_int_of_mul {D : D7} {PP : Pl D.host.E} {e : AE D} (he : Formalism.L2.NTheta.IsIdemAt e PP) {ϖ : 𝓞 D.host.E}
    (hϖ : ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) {m : EAf D} (hm : toEAf D e * m = m)
    (hr : Valued.v (cpt PP (eToEAf D (ϖ : D.host.E) * m)) < 1) :
    m ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  refine (GlobalTheory.AdIsom.mem_OA m).2 fun P => ?_
  by_cases hP : P = PP
  · subst hP
    have hv : Valued.v (cpt P (eToEAf D (ϖ : D.host.E))) = P.valuation D.host.E (ϖ : D.host.E) := by
      have : eToEAf D (ϖ : D.host.E) = GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D (ϖ : D.host.E) := rfl
      rw [this, GlobalTheory.AdIsom.cpt_inc, Formalism.UG.P.levelaf_valued_algebraMap]
    rw [RingHom.map_mul, Valuation.map_mul, hv, GlobalTheory.HeckeDetChar.val_unif hϖ.1 hϖ.2] at hr
    by_cases h0 : Valued.v (cpt P m) = 0
    · rw [h0]; exact zero_le'
    obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v (cpt P m) = WithZero.exp k := ⟨_, (WithZero.exp_log h0).symm⟩
    rw [hk] at hr ⊢
    rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hr
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  · have h0 : cpt P (toEAf D e) = 0 := (GlobalTheory.StdFrames.cpt_of_isIdemAt he).2 P hP
    have := congrArg (cpt P) hm
    rw [RingHom.map_mul, h0, zero_mul] at this
    rw [← this, Valuation.map_zero]
    exact zero_le'

theorem idemSum_single {D : D7} {PP : Pl D.host.E} {e : AE D} (he : Formalism.L2.NTheta.IsIdemAt e PP) : IsIdemSum e {PP} :=
  ⟨⟨fun _ => e, fun P hP => by rw [Finset.mem_singleton.1 hP]; exact he, by rw [Finset.sum_singleton]⟩, he.1.2.1⟩

theorem frMapAdj_one {D : D7} (S : HSp D) (β : GL (Fin S.rank) (EAf D)) : frMapAdj S S β β 1 = 1 := by
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.transpose_one, Matrix.mul_one, Matrix.mul_assoc, ← Matrix.mul_assoc ((S.gram⁻¹).map (eToEAf D)),
    mul_eq_one_comm.1 (GlobalTheory.PlaceVec.gram_map_mul_inv S), Matrix.one_mul, Units.inv_mul]

section Local

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {β : GL (Fin S.rank) (EAf D)} {PP : Pl D.host.E} {e : AE D}

theorem single_half (he : Formalism.L2.NTheta.IsIdemAt e PP) (a : Fin S.rank) {m : EAf D} (hm : toEAf D e * m = m) :
    ∃ y : WO S S, IsHalf e y ∧ (∀ i j, infPart D (y i j) = 0) ∧ frMapO S S β β y = Matrix.single a a m :=
  GlobalTheory.HalfDuality.exists_half_frMapO S S β β e he.1.1 _ fun i j => by
    rw [Matrix.single_apply]
    split_ifs
    · exact hm
    · rw [mul_zero]

theorem not_mem_conj (hP : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) :
    ∀ P ∈ ({PP} : Finset (Pl D.host.E)).image Formalism.L2.DIV.conjPl,
      ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  intro P hP' hm
  obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 hP'
  rw [Finset.mem_singleton.1 hP'] at hm
  have h2 : Formalism.L2.DIV.starOHom ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := hm
  rw [map_natCast] at h2
  exact hP h2

theorem psiE_int (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S Λ) (fS : Formalism.L2.DIV.IsFrame β Λ) (a : Fin S.rank)
    (he : Formalism.L2.NTheta.IsIdemAt e PP)
    (hP : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    {m : EAf D} (hm : toEAf D e * m = m) (hi : m ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) : psiE ψ m = 1 := by
  obtain ⟨y, hyh, hy0, hy⟩ := single_half (β := β) he a hm
  have hP1 : ∀ P ∈ ({PP} : Finset (Pl D.host.E)),
      ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun P h => by
    rw [Finset.mem_singleton.1 h]; exact hP
  have hyL := GlobalTheory.HalfLatInt.mem_of_isIntM hS hS fS fS (idemSum_single he) hP1 hyh (by
    rw [hy]
    intro i j
    rw [Matrix.single_apply]
    split_ifs
    exacts [hi, zero_mem _])
  have ht : frMapAdj S S β β (cA D e • (1 : WO S S)) = toEAf D e • (1 : Matrix (Fin S.rank) (Fin S.rank) (EAf D)) := by
    rw [GlobalTheory.AdjVecLocal.frMapAdj_smul, frMapAdj_one]
  have hN : Ideal.absNorm D.host.ccK ≠ 0 := fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have htL := GlobalTheory.DatumFourier.mem_latO_of_int hS hS fS fS (idemSum_single he) hN
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D)
    (fun P h hm => hP1 P h (GlobalTheory.HalfCompare.mem_of_dvd hm (Dvd.intro_left _ rfl)))
    (x := cA D e • (1 : WO S S)) (fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← map_mul, he.1.1]) (by
      rw [ht]
      intro i j
      rw [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
      refine mul_mem (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ he).1 ?_
      split_ifs
      exacts [one_mem _, zero_mem _])
  have h := GlobalTheory.LatVac.char_sympl_eq_one hψ hS hS htL hyL
  rwa [psi_sympl ψ S S β β _ y hy0, hy, GlobalTheory.HalfDuality.trace_mul_single, ht, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one, hm] at h

theorem psiE_ne (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S Λ) (fS : Formalism.L2.DIV.IsFrame β Λ) (a : Fin S.rank)
    (he : Formalism.L2.NTheta.IsIdemAt e PP)
    (hP : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    {ϖ : 𝓞 D.host.E} (h0 : ϖ ≠ 0) (hϖ : ϖ ∈ PP.asIdeal) :
    ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, psiE ψ (eToEAf D (ϖ : D.host.E)⁻¹ * toEAf D e * w) ≠ 1 := by
  by_contra hn
  push Not at hn
  have hee : toEAf D e * toEAf D e = toEAf D e := by rw [← map_mul, he.1.1]
  have hm : toEAf D e * (eToEAf D (ϖ : D.host.E)⁻¹ * toEAf D e) = eToEAf D (ϖ : D.host.E)⁻¹ * toEAf D e := by
    rw [mul_left_comm, hee]
  obtain ⟨y, hyh, hy0, hy⟩ := single_half (β := β) he a hm
  have hP1 : ∀ P ∈ ({PP} : Finset (Pl D.host.E)),
      ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun P h => by
    rw [Finset.mem_singleton.1 h]; exact hP
  have hyL := GlobalTheory.LatVac.mem_of_char hψ hS hS (u := y) (Matrix.ext hy0) fun u hu => by
    have hu' := GlobalTheory.PlaceModelSum.idem_smul_latO (e := cA D e) (by rw [← map_mul, he.1.1]) hu
    have hint : IsIntM (frMapAdj S S β β (cA D e • u)) :=
      GlobalTheory.HalfLatInt.isIntM_adj hS hS fS fS (GlobalTheory.HalfLatInt.isIntM_of_mem hS fS fS
        (Formalism.IndefR.Fin.LevelGroupLemmas.isIdemSum_conj (idemSum_single he)) (not_mem_conj hP) (fun i j => by
          rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← map_mul, he.1.1]) hu')
    have h1 := hn _ (hint a a)
    rw [GlobalTheory.AdjVecLocal.frMapAdj_smul, Matrix.smul_apply, smul_eq_mul] at h1
    have h3 : ∀ x p : EAf D, x * (p * toEAf D e) = p * toEAf D e * (toEAf D e * x) := fun x p => by
      linear_combination (-(x * p)) * hee
    rw [GlobalTheory.OrientedHeis.symplO_skew u y, AddChar.map_neg_eq_inv, psi_sympl ψ S S β β u y hy0, hy,
      GlobalTheory.HalfDuality.trace_mul_single, h3, h1, inv_one]
  have h2 := GlobalTheory.HalfLatInt.isIntM_of_mem hS fS fS (idemSum_single he) hP1 hyh hyL a a
  rw [hy, Matrix.single_apply_same] at h2
  refine (he.2 ϖ h0).1 hϖ (GlobalTheory.PlaceVec.finPart_mem_intAE ?_)
  rw [map_mul, mul_comm]
  exact h2

theorem psiE_max (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S Λ) (fS : Formalism.L2.DIV.IsFrame β Λ) (a : Fin S.rank)
    (he : Formalism.L2.NTheta.IsIdemAt e PP)
    (hP : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    {ϖ : 𝓞 D.host.E} (h0 : ϖ ≠ 0) (hϖ : ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2)
    (w : EAf D) (hw : w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hr : resS D.host.F PP ⟨w, hw⟩ = 0) :
    psiE ψ (eToEAf D (ϖ : D.host.E)⁻¹ * toEAf D e * w) = 1 := by
  have hϖE : (ϖ : D.host.E) ≠ 0 := by simpa using h0
  have hinv : eToEAf D (ϖ : D.host.E) * eToEAf D (ϖ : D.host.E)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hϖE, map_one]
  have hee : toEAf D e * toEAf D e = toEAf D e := by rw [← map_mul, he.1.1]
  have hm : toEAf D e * (eToEAf D (ϖ : D.host.E)⁻¹ * toEAf D e * w) = eToEAf D (ϖ : D.host.E)⁻¹ * toEAf D e * w := by
    linear_combination (eToEAf D (ϖ : D.host.E)⁻¹ * w) * hee
  have h2 : eToEAf D (ϖ : D.host.E) * (eToEAf D (ϖ : D.host.E)⁻¹ * toEAf D e * w) = toEAf D e * w := by
    linear_combination (toEAf D e * w) * hinv
  refine psiE_int hψ hS fS a he hP hm (mem_int_of_mul he hϖ hm (h2.symm ▸ ?_))
  obtain ⟨h1, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ _ he
  have h3 : toEAf D e * w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := mul_mem h1 hw
  have h4 : (⟨toEAf D e * w, h3⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨toEAf D e, h1⟩ * ⟨w, hw⟩ := Subtype.ext rfl
  have h5 : resS D.host.F PP ⟨toEAf D e * w, h3⟩ = 0 := by rw [h4, RingHom.map_mul, hr, mul_zero]
  exact (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP ⟨_, h3⟩).1 h5

end Local

theorem trace_redM {D : D7} (PP : Pl D.host.E) {a b : ℕ} {A : Matrix (Fin a) (Fin b) (EAf D)} {B : Matrix (Fin b) (Fin a) (EAf D)}
    (hA : IsIntM A) (hB : IsIntM B) :
    ∃ h : Matrix.trace (A * B) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      Matrix.trace (redM PP A * redM PP B) = resS D.host.F PP ⟨_, h⟩ := by
  have e : Matrix.trace (A * B) = ((∑ i, ∑ j, (⟨A i j, hA i j⟩ * ⟨B j i, hB j i⟩) :
      Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul]
  refine ⟨e ▸ Subtype.prop _, ?_⟩
  rw [show (⟨Matrix.trace (A * B), e ▸ Subtype.prop _⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
    ∑ i, ∑ j, (⟨A i j, hA i j⟩ * ⟨B j i, hB j i⟩) from Subtype.ext e]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [GlobalTheory.HalfDuality.redM_apply_of_mem PP A i j (hA i j), GlobalTheory.HalfDuality.redM_apply_of_mem PP B j i (hB j i)]

theorem addChar_sum {A ι : Type} [AddCommMonoid A] (Φ : AddChar A ℂ) (s : Finset ι) (f : ι → A) :
    Φ (∑ i ∈ s, f i) = ∏ i ∈ s, Φ (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

theorem sum_divisible_eq_sum_mul {A ι : Type} [CommRing A] {m n : ℕ} (s : Finset ι) (f : ι → A) {p q : A} (hpq : p * q = 1)
    (B : Matrix (Fin m) (Fin n) A) (C : Matrix (Fin n) (Fin m) A) (hB : (∑ i ∈ s, f i) • B = B) :
    Matrix.trace (B * C) = ∑ i ∈ s, q * f i * Matrix.trace (p • C * B) := by
  rw [← Finset.sum_mul, ← Finset.mul_sum, Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_mul_comm C B, smul_eq_mul]
  conv_lhs => rw [← hB, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  linear_combination (-((∑ i ∈ s, f i) * Matrix.trace (B * C))) * hpq

theorem assemble {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D))
    (βT : GL (Fin T.rank) (EAf D)) (Q : Finset (Pl D.host.E)) (es : Pl D.host.E → AE D) {ϖ : D.host.E} (h0 : ϖ ≠ 0)
    (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ)
    (hψP : ∀ PP ∈ Q, ∀ w (hw : w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
      ψP PP (resS D.host.F PP ⟨w, hw⟩) = psiE ψ (eToEAf D ϖ⁻¹ * toEAf D (es PP) * w))
    (t y : WO S T) (ht : IsHalf (cA D (∑ PP ∈ Q, es PP)) t) (hy : ∀ i j, infPart D (y i j) = 0)
    (hA : IsIntM (frMapO S T βS βT (Matrix.map y fun w => incA D ϖ * w))) (hB : IsIntM (frMapAdj S T βS βT t)) :
    ψ (symplO S T t y) = ∏ PP ∈ Q, ψP PP (Matrix.trace
      (redM PP (frMapO S T βS βT (Matrix.map y fun w => incA D ϖ * w)) * redM PP (frMapAdj S T βS βT t))) := by
  have hinv : eToEAf D ϖ * eToEAf D ϖ⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ h0, map_one]
  have hdil : frMapO S T βS βT (Matrix.map y fun w => incA D ϖ * w) = eToEAf D ϖ • frMapO S T βS βT y := by
    have h : (Matrix.map y fun w => incA D ϖ * w).map (toEAf D) = eToEAf D ϖ • y.map (toEAf D) :=
      Matrix.ext fun k l => (toEAf D).map_mul _ _
    simp only [frMapO, h, Matrix.mul_smul, Matrix.smul_mul]
  have hhalf : (∑ PP ∈ Q, toEAf D (es PP)) • frMapAdj S T βS βT t = frMapAdj S T βS βT t := by
    rw [← map_sum]
    exact Matrix.ext fun k l => GlobalTheory.AdjVecLocal.frMapAdj_half _ _ _ _ ht k l
  rw [psi_sympl ψ S T βS βT t y hy, sum_divisible_eq_sum_mul Q _ hinv _ _ hhalf, addChar_sum, ← hdil]
  refine Finset.prod_congr rfl fun PP hPP => ?_
  obtain ⟨h, e⟩ := trace_redM PP hA hB
  rw [e, hψP PP hPP]

theorem char_eq_prod : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (Q : Finset (Pl D.host.E)), (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∃ ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, (∀ PP ∈ Q, (ψP PP).IsPrimitive) ∧ ∀ t y : WO (Vc D i) (Wc D i), IsHalf (cA D eQ) t → t ∈ lattice₂ R i → IsHalf eQ y → dil i (ϖ : D.host.E) y ∈ lattice₂ R i → R.ψ (symplO (Vc D i) (Wc D i) t y) = ∏ PP ∈ Q, ψP PP (Matrix.trace (redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) y)) * redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (t)))) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hG i hV Q hQ eQ hIS ϖ hϖ0 hϖ
  have hI := GlobalTheory.HalfLatInt.isIntM_iff_mem_latP D G Pl0 T0 A Ks R F hC hG i hV Q hQ eQ hIS
  have hJ := GlobalTheory.QHalfLat.isIntM_adj_iff_mem_latP D G Pl0 T0 A Ks R F hC hG i hV Q hQ eQ hIS
  have hinf : infPart D eQ = 0 := GlobalTheory.PlaceVec.idemSum_infPart hIS
  obtain ⟨t0, hQt⟩ := hQ
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hIS
  have hψ : IsStdChar D R.ψ (-1) := (hC.thP.ωP i A.μ0).std
  have hSV := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  obtain ⟨cV, hBV⟩ := hC.lev.βV i
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have a : Fin (Vc D i).rank := ⟨0, by rw [rV]; have := D.R.t_odd.pos; omega⟩
  have hϖE : (ϖ : D.host.E) ≠ 0 := by simpa using hϖ0
  obtain ⟨ψP, hprim, hψP⟩ := fac (psiE R.ψ) Q (fun PP => eToEAf D (ϖ : D.host.E)⁻¹ * toEAf D (es PP))
    (fun PP hPP => psiE_max hψ hSV hBV.1 a (hes PP hPP) (hG.2 t0 PP (hQt hPP)) hϖ0 (hϖ PP hPP))
    fun PP hPP => psiE_ne hψ hSV hBV.1 a (hes PP hPP) (hG.2 t0 PP (hQt hPP)) hϖ0 (hϖ PP hPP).1
  refine ⟨ψP, hprim, fun t y ht htL hy hyL => ?_⟩
  have hA := (hI _ (fun k l => by simp only [dil, Matrix.map_apply]; rw [mul_left_comm, hy k l])).2 hyL
  exact assemble R.ψ _ _ (R.βV i) (R.βW i) Q es hϖE ψP hψP t y ht
    (fun k l => by rw [← hy k l, RingHom.map_mul, hinf, zero_mul]) hA ((hJ t ht).2 htL)

end GlobalTheory.QResChar
