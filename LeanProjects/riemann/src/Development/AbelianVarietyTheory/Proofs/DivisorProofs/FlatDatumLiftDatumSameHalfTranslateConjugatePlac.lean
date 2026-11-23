import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramFrMulInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatVectorThreeStepsConjugatePlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatVectorEqUnitSmulCentralTranslatePlacePart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedPairLatticeIffFrameMatrixIntegralOnH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedPairLatticeIffAdjointFrameMatrixInte
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeIffUniformiserReductionVanishes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarDilationElementSupportDetPullback
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdelicUnitarySplitPlaceComponent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisOFixOfIsThetaAt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceAt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatSelf
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap

namespace GlobalTheory.FlipTranslate

open GlobalTheory.BaseCmp GlobalTheory.OnCmp Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas GlobalTheory.PartFlat
open GlobalTheory.ExportSeries.Model (ct int_mul int_ct ct_mul)

theorem ct_ct {D : D7} {a b : ℕ} (A : Matrix (Fin a) (Fin b) (Datum.EAf D)) : ct (ct A) = A :=
  Matrix.ext fun _ _ => sigR_sigR D.sp.cm _

theorem ct_smul {D : D7} {a b : ℕ} (c : Datum.EAf D) (A : Matrix (Fin a) (Fin b) (Datum.EAf D)) :
    ct (c • A) = GlobalTheory.AdelicLatMove.cF D c • ct A :=
  Matrix.ext fun i j => map_mul (GlobalTheory.AdelicLatMove.cF D) c (A j i)

theorem ct_one {D : D7} {a : ℕ} : ct (1 : Matrix (Fin a) (Fin a) (Datum.EAf D)) = 1 := by simp [ct]

theorem smul_map_of_half {D : D7} {a b : ℕ} {e : AE D} {x : Matrix (Fin a) (Fin b) (AE D)} (hx : IsHalf e x) :
    toEAf D e • x.map (toEAf D) = x.map (toEAf D) :=
  Matrix.ext fun i j => (map_mul (toEAf D) e (x i j)).symm.trans (congrArg (toEAf D) (hx i j))

theorem smul_frMapO {D : D7} {S T : HSp D} (βS : GL (Fin S.rank) (Datum.EAf D)) (βT : GL (Fin T.rank) (Datum.EAf D)) {e : AE D}
    {x : WO S T} (hx : IsHalf e x) : toEAf D e • frMapO S T βS βT x = frMapO S T βS βT x := by
  unfold frMapO
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, smul_map_of_half hx]

theorem smul_ct_of {D : D7} {a b : ℕ} {e : AE D} {A : Matrix (Fin a) (Fin b) (Datum.EAf D)} (h : toEAf D (cA D e) • A = A) :
    toEAf D e • ct A = ct A := by
  conv_rhs => rw [← h, ct_smul, ← GlobalTheory.AdelicLatMove.toEAf_cA, Formalism.L2.Theta.cA_cA]

theorem smul_ct_frMapO {D : D7} {S T : HSp D} (βS : GL (Fin S.rank) (Datum.EAf D)) (βT : GL (Fin T.rank) (Datum.EAf D)) {e : AE D}
    {x : WO S T} (hx : IsHalf (cA D e) x) : toEAf D e • ct (frMapO S T βS βT x) = ct (frMapO S T βS βT x) :=
  smul_ct_of (smul_frMapO βS βT hx)

theorem det_int {D : D7} {n : ℕ} {A : Matrix (Fin n) (Fin n) (Datum.EAf D)} (hA : IsIntM A) :
    A.det ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => hA _ _)

theorem eq_of_parts {D : D7} {z w : AE D} (h1 : infPart D z = infPart D w) (h2 : toEAf D z = toEAf D w) : z = w := by
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hφ' : ∀ z, (φ z).1 = infPart D z ∧ (φ z).2 = finPart D z := hφ
  refine φ.injective (Prod.ext ?_ ?_)
  · rw [(hφ' _).1, (hφ' _).1, h1]
  · rw [(hφ' _).2, (hφ' _).2]
    exact (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective h2

theorem redM_map {D : D7} (PP : Pl D.host.E) {b a : ℕ} (X : Matrix (Fin b) (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E)) :
    redM PP (X.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) = X.map (resS D.host.F PP) :=
  Matrix.ext fun i j => dif_pos (X i j).2

theorem redM_mul' {D : D7} (PP : Pl D.host.E) {c b a : ℕ} {A : Matrix (Fin c) (Fin b) (Datum.EAf D)}
    {B : Matrix (Fin b) (Fin a) (Datum.EAf D)} (hA : IsIntM A) (hB : IsIntM B) :
    redM PP (A * B) = redM PP A * redM PP B := by
  obtain ⟨A', rfl⟩ : ∃ X : Matrix (Fin c) (Fin b) (Formalism.L2.Herm.intAf D.host.F D.host.E),
    X.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype = A := ⟨fun i j => ⟨A i j, hA i j⟩, rfl⟩
  obtain ⟨B', rfl⟩ : ∃ X : Matrix (Fin b) (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E),
    X.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype = B := ⟨fun i j => ⟨B i j, hB i j⟩, rfl⟩
  rw [← Matrix.map_mul, redM_map, redM_map, redM_map, Matrix.map_mul]

theorem redM_one {D : D7} (PP : Pl D.host.E) {a : ℕ} : redM PP (1 : Matrix (Fin a) (Fin a) (Datum.EAf D)) = 1 := by
  rw [← Matrix.map_one (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype (map_zero _) (map_one _), redM_map,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem redM_diagW {D : D7} (PP : Pl D.host.E) (n r : ℕ) {ϖ : 𝓞 D.host.E} (h : ϖ ∈ PP.asIdeal) :
    redM PP (diagW D n r (ϖ : D.host.E)) = Matrix.diagonal fun k => if k.val < r then 1 else 0 := by
  have e : diagW D n r (ϖ : D.host.E) = (Matrix.diagonal fun k : Fin n => if k.val < r then 1 else
      oToS D.host.F D.host.E ϖ).map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype := by
    rw [Matrix.diagonal_map (map_zero _), diagW]
    congr 1
    funext k
    split_ifs <;> rfl
  rw [e, redM_map, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext k
  split_ifs
  · exact map_one _
  · rw [resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 h]

theorem redM_conj {D : D7} (PP : Pl D.host.E) {a b : ℕ} {y : Matrix (Fin a) (Fin b) (Datum.EAf D)} (hy : IsIntM y) :
    redM (conjPl PP) y = ((redM PP (ct y)).map (conjK PP)).transpose := by
  ext i j
  rw [Matrix.transpose_apply, Matrix.map_apply]
  unfold redM
  rw [dif_pos (hy i j), dif_pos (int_ct hy j i)]
  exact resS_conj PP _ _ (sigR_sigR D.sp.cm _).symm

theorem det_topL_conj {D : D7} (PP : Pl D.host.E) {n r : ℕ} (hr : r ≤ n) {y : Matrix (Fin r) (Fin n) (Datum.EAf D)} (hy : IsIntM y) :
    (topL r (redM (conjPl PP) y)).det = conjK PP (topL r (redM PP (ct y))).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.det_transpose, redM_conj PP hy]
  congr 1
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, topL]
  rw [dif_pos ⟨j.2, by omega⟩, dif_pos ⟨by omega, j.2⟩]

theorem red_adj {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (v : Matrix (Fin n) (Fin r) κ) (g : Matrix (Fin r) (Fin r) κ) :
    LowZero r ((Matrix.diagonal fun k : Fin n => if k.val < r then (1 : κ) else 0) * v * g) ∧
      topL r ((Matrix.diagonal fun k : Fin n => if k.val < r then (1 : κ) else 0) * v * g) = topL r v * g := by
  constructor
  · intro i j hi _
    rw [Matrix.mul_assoc, Matrix.diagonal_mul, if_neg (by omega), zero_mul]
  · ext i j
    have hi : i.val < n := by omega
    rw [Matrix.mul_assoc, topL, dif_pos ⟨hi, j.2⟩, Matrix.diagonal_mul, if_pos i.2, one_mul, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [topL, dif_pos ⟨hi, k.2⟩]

theorem X_pval : ∀ (D : D7) (Q : Finset (Pl D.host.E)) (ϖ : 𝓞 D.host.E), (∀ PP ∈ Q, ϖ ∈ PP.asIdeal) → ∀ (n r : ℕ), r ≤ n → ∀ (Γ Γ' : Matrix (Fin r) (Fin r) (Datum.EAf D)), IsIntM Γ → IsIntM Γ' → Γ * Γ' = 1 → ∀ (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), (∀ PP ∈ Q, ∀ u : (kP PP)ˣ, ξ' (conjPl PP) (Units.map (conjK PP).toMonoidHom u) = (ξ PP u)⁻¹) → ∃ c₀ : ℂ, GlobalTheory.ConjTwist.IsRoot1 c₀ ∧ ∀ y : Matrix (Fin r) (Fin n) (Datum.EAf D), IsIntM y → GlobalTheory.ConjTwist.omegaFlat (Q.image conjPl) r ξ' (fun PP => redM PP y) = c₀ * omegaQ Q r ξ (-1) (fun PP => redM PP (diagW D n r (ϖ : D.host.E) * GlobalTheory.ExportSeries.Model.ct y * Γ)) := by
  intro D Q ϖ hϖ n r hr Γ Γ' iΓ iΓ' hΓ ξ ξ' hξ
  have hu : ∀ PP : Pl D.host.E, IsUnit (redM PP Γ).det := fun PP =>
    IsUnit.of_mul_eq_one (redM PP Γ').det (by rw [← Matrix.det_mul, ← redM_mul' PP iΓ iΓ', hΓ, redM_one, Matrix.det_one])
  refine ⟨∏ PP ∈ Q.attach, ((ξ PP.1 (hu PP.1).unit : ℂˣ) : ℂ), ?_, fun y hy => ?_⟩
  · refine Finset.prod_induction _ GlobalTheory.ConjTwist.IsRoot1 ?_ ⟨1, one_pos, one_pow _⟩ fun PP _ => ?_
    · rintro a b ⟨k, hk, ha⟩ ⟨l, hl, hb⟩
      exact ⟨k * l, Nat.mul_pos hk hl, by rw [mul_pow, pow_mul, ha, mul_comm k, pow_mul, hb, one_pow, one_pow, one_mul]⟩
    · haveI : Finite (kP PP.1) := Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
      exact ⟨Nat.card (kP PP.1)ˣ, Nat.card_pos, by
        rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]⟩
  · have key : ∀ PP ∈ Q, LowZero r (redM PP (diagW D n r (ϖ : D.host.E) * ct y * Γ)) ∧
        (topL r (redM PP (diagW D n r (ϖ : D.host.E) * ct y * Γ))).det = (topL r (redM PP (ct y))).det * (redM PP Γ).det := by
      intro PP hPP
      rw [redM_mul' PP (int_mul (diagW_int _ _ ϖ) (int_ct hy)) iΓ, redM_mul' PP (diagW_int _ _ ϖ) (int_ct hy),
        redM_diagW PP n r (hϖ PP hPP), (red_adj hr _ _).2, Matrix.det_mul]
      exact ⟨(red_adj hr _ _).1, rfl⟩
    have hcu : ∀ (PP : Pl D.host.E) (a : kP PP), IsUnit (conjK PP a) → IsUnit a := fun PP a h => by
      haveI := PP.isMaximal
      letI := Ideal.Quotient.field PP.asIdeal
      haveI : Nontrivial (kP (conjPl PP)) := Ideal.Quotient.nontrivial_iff.2 (conjPl PP).isPrime.ne_top
      refine Ne.isUnit ?_
      rintro rfl
      rw [map_zero] at h
      exact not_isUnit_zero h
    unfold GlobalTheory.ConjTwist.omegaFlat omegaQ
    by_cases h : ∀ PP ∈ Q, IsUnit (topL r (redM PP (ct y))).det
    · have h1 : ∀ PP ∈ Q.image conjPl, IsUnit (topL r (redM PP y)).det := fun PP hPP => by
        obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hPP
        rw [det_topL_conj P hr hy]
        exact (h P hP).map _
      have h2 : ∀ PP ∈ Q, LowZero r (redM PP (diagW D n r (ϖ : D.host.E) * ct y * Γ)) ∧
          IsUnit (topL r (redM PP (diagW D n r (ϖ : D.host.E) * ct y * Γ))).det := fun PP hPP =>
        ⟨(key PP hPP).1, by rw [(key PP hPP).2]; exact (h PP hPP).mul (hu PP)⟩
      rw [dif_pos h1, dif_pos h2, ← Finset.prod_mul_distrib]
      symm
      refine Finset.prod_bij (fun P _ => ⟨conjPl P.1, Finset.mem_image_of_mem _ P.2⟩) (fun _ _ => Finset.mem_attach _ _)
        (fun a _ b _ hab => Subtype.ext ?_) (fun b _ => ?_) fun P _ => ?_
      · rw [← conjPl_conjPl a.1, show conjPl a.1 = conjPl b.1 from congrArg Subtype.val hab, conjPl_conjPl]
      · obtain ⟨P, hP, e⟩ := Finset.mem_image.1 b.2
        exact ⟨⟨P, hP⟩, Finset.mem_attach _ _, Subtype.ext e⟩
      · have e1 : (h1 _ (Finset.mem_image_of_mem _ P.2)).unit = Units.map (conjK P.1).toMonoidHom (h P.1 P.2).unit :=
          Units.ext (det_topL_conj P.1 hr hy)
        have e2 : (h2 P.1 P.2).2.unit = (h P.1 P.2).unit * (hu P.1).unit := Units.ext (key P.1 P.2).2
        rw [e1, hξ P.1 P.2, e2, map_mul, Units.val_mul, zpow_neg_one, Units.val_inv_eq_inv_val]
        field_simp
    · rw [dif_neg, dif_neg, mul_zero]
      · intro h2
        exact h fun PP hPP => isUnit_of_mul_isUnit_left (by rw [← (key PP hPP).2]; exact (h2 PP hPP).2)
      · intro h1
        exact h fun PP hPP => hcu PP _ (by rw [← det_topL_conj PP hr hy]; exact h1 _ (Finset.mem_image_of_mem _ hPP))

theorem X_pint : ∀ (D : D7) (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ ϖ : 𝓞 D.host.E, (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ϖ ≠ 0 → ∀ (n r : ℕ) (Γ Γ' : Matrix (Fin r) (Fin r) (Datum.EAf D)), IsIntM Γ' → Γ * Γ' = 1 → ∀ v : Matrix (Fin n) (Fin r) (Datum.EAf D), toEAf D e • v = v → IsIntM (diagW D n r (ϖ : D.host.E) * v * Γ) → (∀ PP ∈ Q, LowZero r (redM PP (diagW D n r (ϖ : D.host.E) * v * Γ))) → IsIntM v := by
  intro D Q e he ϖ hϖ _ n r Γ Γ' iΓ' hΓ v hv hi hz k l
  have h1 := int_mul hi iΓ'
  have e1 : diagW D n r (ϖ : D.host.E) * v * Γ * Γ' = diagW D n r (ϖ : D.host.E) * v := by
    rw [Matrix.mul_assoc, hΓ, Matrix.mul_one]
  have e2 : (diagW D n r (ϖ : D.host.E) * v * Γ * Γ') k l = (if k.val < r then 1 else eToEAf D (ϖ : D.host.E)) * v k l := by
    rw [e1, diagW, Matrix.diagonal_mul]
  have h2 := h1 k l
  by_cases hk : k.val < r
  · rwa [e2, if_pos hk, one_mul] at h2
  · rw [if_neg hk] at e2
    refine GlobalTheory.DilKer.mem_int_of_mul he hϖ (congrFun (congrFun hv k) l) (e2 ▸ h2) fun PP hPP => ?_
    rw [← e2]
    refine (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP ⟨_, h2⟩).1 ?_
    have h3 : redM PP (diagW D n r (ϖ : D.host.E) * v * Γ * Γ') k l = 0 := by
      rw [redM_mul' PP hi iΓ', Matrix.mul_apply]
      exact Finset.sum_eq_zero fun j _ => by rw [hz PP hPP k j (by omega) j.2, zero_mul]
    exact (dif_pos h2).symm.trans h3

theorem exists_idF_of_fixed {D : D7} (V : HSp D) (y : (AE D)ˣ) (hy : cA D (y : AE D) = y) : ∃ a, y = idF D a := by
  have h1 : ∀ z : (AE D)ˣ, cA D (z : AE D) = z → IsDetRoot V 1 z := fun z hz => by
    unfold IsDetRoot
    rw [map_one, Units.val_one, Matrix.det_one, one_mul]
    exact hz.symm
  obtain ⟨a, ha⟩ := (GlobalTheory.Member.isDetRoot_laws D V).2.1 1 1 y (h1 1 (map_one _)) (h1 y hy)
  exact ⟨a, by rw [ha, one_mul]⟩

open GlobalTheory.ConjTwist in

theorem isLocUnit_conj {D : D7} {PP : Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP) {u : (kP PP)ˣ} {x : (AE D)ˣ}
    (hx : IsLocUnit PP u x) :
    IsLocUnit (conjPl PP) (Units.map (conjK PP).toMonoidHom u) (Units.map (cA D).toMonoidHom x) := by
  have hi : ∀ z : AE D, finPart D z ∈ intAE D → finPart D (cA D z) ∈ intAE D := fun z hz =>
    GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (by
      rw [GlobalTheory.AdelicLatMove.toEAf_cA]; exact GlobalTheory.PlaceVec.cF_mem_int (GlobalTheory.IdemRes.toEAf_mem_of_finPart hz))
  refine ⟨?_, ?_, hi _ hx.int, hi _ hx.int', ?_⟩
  · have := congrArg (cA D) hx.off
    rw [map_mul, map_sub, map_one] at this
    rw [GlobalTheory.FlatThreeSteps.idemAt_conj h]
    exact this
  · have h0 : infPart D ((x : AE D) - 1) = 0 := by rw [map_sub, hx.inf, map_one, sub_self]
    have h1 := GlobalTheory.PlaceVec.infPart_cA h0
    rw [map_sub, map_one, map_sub, map_one, sub_eq_zero] at h1
    exact h1
  · obtain ⟨k1, k2⟩ := hx.res
    refine ⟨GlobalTheory.IdemRes.toEAf_mem_of_finPart (hi _ hx.int), ?_⟩
    rw [resS_conj PP ⟨_, k1⟩ _ (GlobalTheory.AdelicLatMove.toEAf_cA _), k2]
    rfl

open GlobalTheory.ConjTwist in

theorem X_chr : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0) (B : Base (Vc D i) (Wc D i)) (ψ : Twist D Circle), B.Good → ψ.Good → B.admitted ψ.Q → R.xi t = B.de.chi * ψ.chi → ∀ PP ∈ R.Q t, conjPl PP ∈ B.de.Q ∪ ψ.Q → ∀ u : (kP PP)ˣ, (B.de.locC (conjPl PP) * ψ.locC (conjPl PP)) (Units.map (conjK PP).toMonoidHom u) = (R.xiR t PP u)⁻¹ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i t B ψ hB hψ hQ hxi PP hPP hm u
  obtain ⟨P, -, h2, hP⟩ := hQ.1.split
  have s1 : B.de.Q ⊆ P := fun a ha => h2 (by simp [ha])
  have s2 : ψ.Q ⊆ P := fun a ha => h2 (by simp [ha])
  have hp : conjPl PP ∈ P := h2 hm
  have hid := (GlobalTheory.PartFlat.splitSet_tuple hC i t).isIdemAt hPP
  obtain ⟨x, hx⟩ := exists_isLocUnit hid u
  have hx' := isLocUnit_conj hid hx
  obtain ⟨k1, k2⟩ := hx.res
  have key : ∀ {ν : Twist D Circle}, ν.Good → ν.Q ⊆ P → ((ν.chi (Units.map (cA D).toMonoidHom x) : Circle) : ℂ) =
      ((ν.locC (conjPl PP) (Units.map (conjK PP).toMonoidHom u) : ℂˣ) : ℂ) := by
    intro ν hν hs
    unfold Twist.locC
    split_ifs with k
    · rw [hx'.eq (hν.res _ k)]
      rfl
    · rw [hx'.eq_one hν.unram hP hs hp k]
      rfl
  obtain ⟨a, ha⟩ := exists_idF_of_fixed (Vc D i) (x * Units.map (cA D).toMonoidHom x) (by
    change cA D ((x : AE D) * cA D x) = (x : AE D) * cA D x
    rw [map_mul, Formalism.L2.Theta.cA_cA, mul_comm])
  have h1 : R.xi t x * R.xi t (Units.map (cA D).toMonoidHom x) = 1 := by
    rw [← map_mul, ha, hxi, MonoidHom.mul_apply, hB.de.real, hψ.real, mul_one]
  have h3 := eq_res_of_chrEq (hC.lev.xi t) hid (hC.lev.xi_tame t PP) (hC.lev.xiR t PP hPP) x hx.off k1 u k2
  refine eq_inv_of_mul_eq_one_right (Units.ext ?_)
  rw [Units.val_mul, ← h3, MonoidHom.mul_apply, Units.val_mul, ← key hB.de s1, ← key hψ s2, ← Circle.coe_mul,
    ← MonoidHom.mul_apply, ← hxi, ← Circle.coe_mul, h1]
  rfl

theorem X_reps : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ N : ℕ, N ≠ 0 → ∀ g : GA D S, (∀ w ∈ latAll S T ΛS ΛT, IsHalf e w → actO S T g⁻¹ 1 w ∈ latAll S T ΛS ΛT) → (∀ w, IsHalf e w → actO S T g⁻¹ 1 w ∈ latAll S T ΛS ΛT → N • w ∈ latAll S T ΛS ΛT) → ∃ Rr : Finset (WO S T), (∀ u ∈ Rr, actO S T g⁻¹ 1 u ∈ latAll S T ΛS ΛT ∧ IsHalf e u) ∧ (∀ w, actO S T g⁻¹ 1 w ∈ latAll S T ΛS ΛT → IsHalf e w → ∃! v, v ∈ Rr ∧ w - v ∈ latAll S T ΛS ΛT) ∧ UnitOff N ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) := by
  intro D ψ hψ S T ΛS ΛT hS hT Q e he N hN g l1 l2
  obtain ⟨R, hR⟩ := (((Formalism.IndefR.Fin.placeLatDual D ψ hψ S T ΛS ΛT hS hT).2.2 Q e he).2.2.1) N (Nat.pos_of_ne_zero hN) e (Or.inl rfl)
  generalize latAll S T ΛS ΛT = Λ at l1 l2 hR ⊢
  let A : AddSubgroup (WO S T) :=
    { carrier := {w | actO S T g⁻¹ 1 w ∈ Λ ∧ IsHalf e w}
      add_mem' := fun {a b} ha hb => ⟨by rw [actO_add]; exact add_mem ha.1 hb.1, fun i j => by
        rw [Matrix.add_apply, mul_add, ha.2 i j, hb.2 i j]⟩
      zero_mem' := ⟨l1 0 (zero_mem _) fun _ _ => mul_zero _, fun _ _ => mul_zero _⟩
      neg_mem' := fun {a} ha => ⟨by
        rw [actO_eq, Matrix.mul_neg, Matrix.neg_mul, ← actO_eq]; exact neg_mem ha.1, fun i j => by
        rw [Matrix.neg_apply, mul_neg, ha.2 i j]⟩ }
  have hout : ∀ q q' : A ⧸ Λ.addSubgroupOf A, (q.out : WO S T) - (q'.out : WO S T) ∈ Λ → q = q' := fun q q' h => by
    rw [← q.out_eq, ← q'.out_eq]
    exact QuotientAddGroup.eq_iff_sub_mem.2 h
  have hfin : Finite (A ⧸ Λ.addSubgroupOf A) := by
    choose r hr v hv hv' hrv using fun q : A ⧸ Λ.addSubgroupOf A =>
      hR (N • (q.out : WO S T)) (l2 _ q.out.2.2 q.out.2.1) (nsmul_mem q.out.2 N).2
    refine Finite.of_injective (fun q => (⟨r q, hr q⟩ : R)) fun q q' h => hout q q' ?_
    have h1 : r q = r q' := congrArg Subtype.val h
    have h2 : (q.out : WO S T) - (q'.out : WO S T) = v q - v q' := by
      ext i j
      have a1 := congrFun (congrFun (hrv q) i) j
      have a2 := congrFun (congrFun (hrv q') i) j
      simp only [Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul, h1] at a1 a2
      have hu : IsUnit (N : AE D) := by
        rw [← map_natCast (incA D)]
        exact (Ne.isUnit (Nat.cast_ne_zero.2 hN)).map _
      refine hu.mul_left_cancel ?_
      rw [Matrix.sub_apply, Matrix.sub_apply]
      linear_combination a1 - a2
    rw [h2]
    exact sub_mem (hv q) (hv q')
  letI := Fintype.ofFinite (A ⧸ Λ.addSubgroupOf A)
  have hinj : Function.Injective fun q : A ⧸ Λ.addSubgroupOf A => (q.out : WO S T) := fun q q' h =>
    hout q q' (by rw [show (q.out : WO S T) = q'.out from h, sub_self]; exact zero_mem _)
  refine ⟨Finset.univ.image fun q : A ⧸ Λ.addSubgroupOf A => (q.out : WO S T), fun u hu => ?_, fun w h1 h2 => ?_, ?_⟩
  · obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
    exact q.out.2
  · have h3 : w - ((QuotientAddGroup.mk (⟨w, h1, h2⟩ : A) : A ⧸ Λ.addSubgroupOf A).out : WO S T) ∈ Λ :=
      (QuotientAddGroup.eq_iff_sub_mem (N := Λ.addSubgroupOf A) (x := (⟨w, h1, h2⟩ : A))).1 (QuotientAddGroup.out_eq' (QuotientAddGroup.mk (⟨w, h1, h2⟩ : A) :
        A ⧸ Λ.addSubgroupOf A)).symm
    refine ⟨_, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), h3⟩, ?_⟩
    rintro v ⟨hv, h4⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hv
    rw [hout q _ (by simpa using sub_mem h3 h4)]
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ← Nat.card_eq_fintype_card]
    obtain ⟨c, hc⟩ := card_dvd_exponent_pow_rank' (Multiplicative (A ⧸ Λ.addSubgroupOf A)) (n := N) fun q => by
      obtain ⟨a, rfl⟩ : ∃ a : A, Multiplicative.ofAdd (QuotientAddGroup.mk a : A ⧸ Λ.addSubgroupOf A) = q :=
        ⟨(Multiplicative.toAdd q).out, congrArg _ (QuotientAddGroup.out_eq' _)⟩
      rw [← ofAdd_nsmul, ← QuotientAddGroup.mk_nsmul, (QuotientAddGroup.eq_zero_iff (N • a)).2 (l2 _ a.2.2 a.2.1)]
      rfl
    rw [show Nat.card (Multiplicative (A ⧸ Λ.addSubgroupOf A)) = Nat.card (A ⧸ Λ.addSubgroupOf A) from rfl] at hc
    refine GlobalTheory.ChiUnit.unitOff_of_pow two_pos ?_
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
    have hi : ∀ m : ℕ, IsIntegral ℤ (m : ℂ) := fun m => by simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (m : ℤ))
    exact GlobalTheory.ChiUnit.unitOff_of_mul_eq (hi _) (hi c) (by exact_mod_cast hc.symm) hN

theorem isRes_one {D : D7} {χ : Formalism.L2.Host.HChar D.host.E} {P : Pl D.host.E} (h : χ.UnrAt P) : χ.TameAt P ∧ IsRes χ P 1 := by
  refine ⟨fun x hx _ => h x hx, fun a k u hk hu => (h _ ?_).symm⟩
  have ha : a ∉ P.asIdeal := fun h0 => by
    have := P.isPrime
    exact u.ne_zero (hu.trans (Ideal.Quotient.eq_zero_iff_mem.2 h0))
  unfold Formalism.L2.Host.IsUnitAt
  rw [GlobalTheory.TypeValues.val_atFin P k a hk]
  exact (P.intValuation_eq_one_iff).2 ha

open GlobalTheory.ChiUnit GlobalTheory.DilChi in

theorem X_det : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0) (Q : Finset (Pl D.host.E)), Q ⊆ R.Q t → ∀ N : ℕ, (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ e : AE D, IsIdemSum e Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ (m : ℕ) (d d' : Datum.EAf D), d ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → d' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → d * d' = 1 → ∀ x : (AE D)ˣ, (1 - e) * (x : AE D) = 1 - e → toEAf D e * toEAf D (x : AE D) = toEAf D e * (eToEAf D (ϖ : D.host.E) ^ m * d) → UnitOff N ((((Lift.chrTh (Lift.tup R.mu0 (R.xi t)) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ))⁻¹ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i t Q hQ N hNQ e he ϖ hϖ0 hϖ m d d' hd hd' hdd x hx1 hx2
  have hK := kerDat_tuple (i := i) hC.lev hC.thP t
  show GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing.UnitOff N _
  have hlev := hC.lev
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ0
  set u : D.host.Eˣ := Units.mk0 _ hϖE with hu
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hinf := GlobalTheory.PlaceVec.idemSum_infPart he
  have hk : incA D ((u ^ m : D.host.Eˣ) : D.host.E) * incA D (((u ^ m)⁻¹ : D.host.Eˣ) : D.host.E) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  obtain ⟨y, hy, hy'⟩ : ∃ y : (AE D)ˣ, (y : AE D) = 1 + e * (incA D ((u ^ m : D.host.Eˣ) : D.host.E) - 1) ∧
      ((y⁻¹ : (AE D)ˣ) : AE D) = 1 + e * (incA D (((u ^ m)⁻¹ : D.host.Eˣ) : D.host.E) - 1) := by
    generalize incA D ((u ^ m : D.host.Eˣ) : D.host.E) = b at hk
    generalize incA D (((u ^ m)⁻¹ : D.host.Eˣ) : D.host.E) = b' at hk
    have hmul : (1 + e * (b - 1)) * (1 + e * (b' - 1)) = 1 := by
      linear_combination (b - 1) * (b' - 1) * hee + e * hk
    exact ⟨⟨_, _, hmul, by rw [mul_comm]; exact hmul⟩, rfl, rfl⟩
  obtain ⟨a, ha⟩ := GlobalTheory.AdjDatumNe.toEAf_surjective d
  have hx' : ((y⁻¹ * x : (AE D)ˣ) : AE D) = e * a + (1 - e) := by
    rw [Units.val_mul, hy']
    refine eq_of_parts ?_ ?_
    · have h1 := congrArg (infPart D) hx1
      simp only [map_mul, map_sub, map_add, map_one, hinf, sub_zero, one_mul, zero_mul, add_zero, zero_add] at h1 ⊢
      exact h1
    · have h1 := congrArg (toEAf D) hx1
      have h2 := congrArg (toEAf D) hk
      have h3 := congrArg (toEAf D) hee
      have h4 : toEAf D (incA D ((u ^ m : D.host.Eˣ) : D.host.E)) = eToEAf D (ϖ : D.host.E) ^ m := by
        rw [← map_pow, Units.val_pow_eq_pow_val]; rfl
      rw [← h4] at hx2
      simp only [map_mul, map_sub, map_add, map_one, ha] at h1 h2 h3 ⊢
      linear_combination h1 + toEAf D (incA D (((u ^ m)⁻¹ : D.host.Eˣ) : D.host.E)) * hx2 + toEAf D e * d * h2
  have hun : ∀ PP : Pl D.host.E, IsUnit (resS D.host.F PP ⟨d, hd⟩) := fun PP =>
    (IsUnit.of_mul_eq_one (⟨d', hd'⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) (Subtype.ext hdd)).map _
  have hval : ∀ (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (ρ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), ChrEq c χ →
      (∀ PP ∈ Q, χ.TameAt PP ∧ IsRes χ PP (ρ PP)) → (∀ PP ∈ Q, GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing.UnitOff N ((χ.locK PP u : ℂˣ) : ℂ)) →
      GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing.UnitOff N ((c x : Circle) : ℂ) := by
    intro c χ ρ hc h1 h2
    have e1 := GlobalTheory.T.heckeCharacter_conjHalfIdele_eq_prod_local D _ _ (isIdemSum_conj he) (u ^ m) y (by rw [Formalism.L2.Theta.cA_cA]; exact hy) c χ hc
    have e2 := GlobalTheory.TameSplitChar.char_eq_prod_res D c χ Q e ρ hc he h1 (y⁻¹ * x) a ⟨d, hd⟩ (fun PP => (hun PP).unit) hx' ha.symm
      fun _ _ => rfl
    rw [← mul_inv_cancel_left y x, map_mul, Circle.coe_mul, e1, e2]
    refine unitOff_mul (unitOff_prod _ _ fun P hP => ?_) (unitOff_prod _ _ fun P _ => ?_)
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 hP
      rw [conjPl_conjPl, map_pow, Units.val_pow_eq_pow_val]
      exact unitOff_pow (h2 P' hP') _
    · haveI : Finite (kP P) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
      refine unitOff_of_pow_eq_one N (k := Nat.card (kP P)ˣ) Nat.card_pos ?_
      rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  have e0 : ((((Lift.chrTh (Lift.tup R.mu0 (R.xi t)) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ)) =
      (((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ)) * (((R.xi t x : Circle) : ℂ)) * (((R.eta x : Circle) : ℂ))⁻¹ := by
    simp only [Lift.chrTh, Lift.tup, MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv]
  have hunr : ∀ P ∈ Q, (R.C.mu0 i).UnrAt P := fun P hP => by
    obtain ⟨⟨q, hq, hqc, -, hqg⟩, -⟩ := hK.pl P (hQ hP)
    have hqm : (q : 𝓞 D.host.E) ∈ P.asIdeal := by
      rw [← hqc]; exact natCard_mem P (by rw [hqc]; exact hq.ne_zero)
    exact (R.C.isMu0 i).unr P fun k hk =>
      not_mem_of_prime_ne P (D.host.g_prime k) hq (hqg k) hqm hk
  obtain ⟨nμ, -, hnμ⟩ := (R.C.isMu0 i).inf
  obtain ⟨n, hn, hnx⟩ := hK.fin
  rw [e0]
  refine unitOff_inv (unitOff_mul (unitOff_mul
    (hval _ _ (fun _ => 1) (hlev.mu0 i) (fun P hP => isRes_one (hunr P hP)) fun P hP => ?_)
    (hval _ _ (R.xiR t) hK.chr (fun P hP => ⟨hK.tame P, hK.res P (hQ hP)⟩) fun P hP => ?_))
    (unitOff_inv (hval _ _ (fun _ => 1) hlev.eta (fun P _ => isRes_one (R.C.isEta.unr P)) fun P hP => ?_)))
  · rw [locK_eq_val _ (hunr P hP) u ϖ rfl (hϖ P hP).1 (hϖ P hP).2]
    exact GlobalTheory.ValUnit.unitOff_val _ _ _ _ nμ P _ hnμ (finite_ramified_places_hecke_character _ (R.C.isMu0 i).unr)
      (R.C.isMu0 i).tame (hunr P hP) (hNQ P hP)
  · refine unitOff_of_pow_eq_one _ hn ?_
    rw [← Units.val_pow_eq_pow_val, LR _ n hnx P u, Units.val_one]
  · rw [locK_eq_val _ (R.C.isEta.unr P) u ϖ rfl (hϖ P hP).1 (hϖ P hP).2]
    exact GlobalTheory.ValUnit.unitOff_val _ _ _ _ _ P _ R.C.isEta.inf
      (Set.Finite.subset Set.finite_empty fun w hw => hw (R.C.isEta.unr w)) (fun w y hy _ => R.C.isEta.unr w y hy)
      (R.C.isEta.unr P) (hNQ P hP)

theorem exists_flip {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Datum.EAf D)) (r : ℕ) {e : AE D} {Q : Finset (Pl D.host.E)}
    (he : IsIdemSum e Q) {a : D.host.E} (ha : a ≠ 0) : ∃ g, IsFlipElt V β r e a g := by
  have lift : ∀ M : Matrix (Fin V.rank) (Fin V.rank) (Datum.EAf D), ∃ N : Matrix (Fin V.rank) (Fin V.rank) (AE D),
      N.map (toEAf D) = M := fun M => by
    choose N hN using fun i j => GlobalTheory.AdjDatumNe.toEAf_surjective (M i j)
    exact ⟨Matrix.of N, Matrix.ext hN⟩
  obtain ⟨N, hN⟩ := lift (β.val * (diagW D V.rank r a * gramFr V β) * (β⁻¹).val)
  obtain ⟨N', hN'⟩ := lift (β.val * (gramFrInv V β * diagW D V.rank r a⁻¹) * (β⁻¹).val)
  have hinf := GlobalTheory.PlaceVec.idemSum_infPart he
  have h1 : (N * N').map (toEAf D) = (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (toEAf D) := by
    rw [Matrix.map_mul, hN, hN', Matrix.map_one _ (map_zero _) (map_one _)]
    calc _ = β.val * (diagW D V.rank r a * (gramFr V β * ((β⁻¹).val * β.val) * gramFrInv V β) * diagW D V.rank r a⁻¹) *
          (β⁻¹).val := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [Units.inv_mul, Matrix.mul_one, gramFr_mul_inv, Matrix.mul_one, diagW_mul, mul_inv_cancel₀ ha, diagW_one,
          Matrix.mul_one, Units.mul_inv]
  have hNN : e • (N * N') = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
    refine Matrix.ext fun i j => eq_of_parts ?_ ?_
    · rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul, hinf, zero_mul, zero_mul]
    · rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul]
      exact congrArg _ (congrFun (congrFun h1 i) j)
  have hJK : JR (AF D.host.F) V.gram * (V.gram⁻¹).map (incA D) = 1 := by
    show V.gram.map (incA D) * (V.gram⁻¹).map (incA D) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (GlobalTheory.UnitaryGlue.gram_det_ne_zero V).isUnit,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hJ : Formalism.UG.cT (cA D) (JR (AF D.host.F) V.gram) = JR (AF D.host.F) V.gram := by
    refine Matrix.ext fun i j => ?_
    show cA D (incA D (V.gram j i)) = incA D (V.gram i j)
    rw [GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.gram_star]
  obtain ⟨g, hg, k1, k2⟩ := GlobalTheory.SplitLift.exists_unitary (cA D) GlobalTheory.DualPairCheck.cA_cA _ _ hJ hJK e
    (GlobalTheory.PlaceVec.idemSum_mul_self he) he.2 N N' hNN
  refine ⟨⟨g, hg⟩, fun i j => congrFun (congrFun k1 i) j, ?_⟩
  have k3 : toEAf D e • (mt V ⟨g, hg⟩).map (toEAf D) = toEAf D e • N.map (toEAf D) := Matrix.ext fun i j =>
    (map_mul (toEAf D) e _).symm.trans ((congrArg (toEAf D) (congrFun (congrFun k2 i) j)).trans (map_mul (toEAf D) e _))
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, k3, hN, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc _ = ((β⁻¹).val * β.val) * (diagW D V.rank r a * gramFr V β) * ((β⁻¹).val * β.val) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_one]

theorem map_actO {D : D7} {S T : HSp D} (g : GA D S) (t : WO S T) :
    (actO S T g⁻¹ 1 t).map (toEAf D) = HMul.hMul (t.map (toEAf D)) ((mt S g).map (toEAf D)) := by
  rw [actO_eq, inv_inv, mt_one', Matrix.one_mul, Matrix.map_mul]

theorem unitary_fin {D : D7} {V : HSp D} (g : GA D V) :
    (mt V g).map (toEAf D) * (V.gram⁻¹).map (eToEAf D) * ct ((mt V g).map (toEAf D)) = (V.gram⁻¹).map (eToEAf D) := by
  have h0 : Formalism.UG.cT (cA D) (mt V g) * V.gram.map (incA D) * mt V g = V.gram.map (incA D) := g.2
  have h1 : ct ((mt V g).map (toEAf D)) * V.gram.map (eToEAf D) * (mt V g).map (toEAf D) = V.gram.map (eToEAf D) := by
    have h2 := congrArg (fun M : Matrix (Fin V.rank) (Fin V.rank) (AE D) => M.map (toEAf D)) h0
    simp only [Matrix.map_mul] at h2
    have h3 : (Formalism.UG.cT (cA D) (mt V g)).map (toEAf D) = ct ((mt V g).map (toEAf D)) :=
      Matrix.ext fun i j => GlobalTheory.AdelicLatMove.toEAf_cA _
    rw [h3] at h2
    exact h2
  have hJK := GlobalTheory.PlaceVec.gram_map_mul_inv V
  generalize (mt V g).map (toEAf D) = M at h1 ⊢
  generalize V.gram.map (eToEAf D) = J at h1 hJK
  generalize (V.gram⁻¹).map (eToEAf D) = K at hJK ⊢
  have hKJ : K * J = 1 := mul_eq_one_comm.1 hJK
  have h4 : (K * ct M * J) * M = 1 := by rw [← hKJ]; conv_rhs => rw [← h1]
                                         simp only [Matrix.mul_assoc]
  have h5 : M * (K * ct M * J) = 1 := mul_eq_one_comm.1 h4
  calc M * K * ct M = M * (K * ct M * J) * K := by simp only [Matrix.mul_assoc, hJK, Matrix.mul_one]
    _ = K := by rw [h5, Matrix.one_mul]

theorem adj_eq {D : D7} {S T : HSp D} {βS : GL (Fin S.rank) (Datum.EAf D)} (βT : GL (Fin T.rank) (Datum.EAf D)) {r : ℕ} {e : AE D}
    {a : D.host.E} {g : GA D S} (hg : IsFlipElt S βS r e a g) {t : WO S T} (ht : IsHalf (cA D e) t) :
    frMapAdj S T βS βT t = diagW D S.rank r a * ct (frMapO S T βS βT (actO S T g⁻¹ 1 t)) * gramFr T βT := by
  have hX : toEAf D e • ct (t.map (toEAf D)) = ct (t.map (toEAf D)) := smul_ct_of (smul_map_of_half ht)
  have hu := unitary_fin g
  have h2 := hg.2
  have hJK := GlobalTheory.PlaceVec.gram_map_mul_inv S
  have hb : ct (βT⁻¹).val * ct βT.val = 1 := by rw [← ct_mul, Units.mul_inv, ct_one]
  rw [GlobalTheory.PlaceVec.frMapAdj_eq]
  change _ * ct (t.map (toEAf D)) * _ = _
  unfold frMapO
  rw [map_actO, ct_mul, ct_mul, ct_mul]
  unfold gramFr at h2 ⊢
  generalize ct (t.map (toEAf D)) = X at hX ⊢
  generalize (mt S g).map (toEAf D) = M at hu h2 ⊢
  generalize S.gram.map (eToEAf D) = J at h2 hJK
  generalize (S.gram⁻¹).map (eToEAf D) = K at hJK hu ⊢
  calc (βS⁻¹).val * K * X * (T.gram.map (eToEAf D) * βT.val)
      = (toEAf D e • ((βS⁻¹).val * M * βS.val)) * ((βS⁻¹).val * K * ct M * X * (T.gram.map (eToEAf D) * βT.val)) := by
        have hβ : ∀ Z : Matrix (Fin S.rank) (Fin T.rank) (Datum.EAf D), βS.val * ((βS⁻¹).val * Z) = Z := fun Z => by
          rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
        conv_lhs => rw [← hu, ← hX]
        simp only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, hβ]
    _ = diagW D S.rank r a * (ct βS.val * (J * (βS.val * (βS⁻¹).val) * K) * (ct M * (toEAf D e • X)) *
          (T.gram.map (eToEAf D) * βT.val)) := by
        rw [h2]
        simp only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul]
    _ = diagW D S.rank r a * (ct βS.val * (ct M * X) * (ct (βT⁻¹).val * ct βT.val) * (T.gram.map (eToEAf D) * βT.val)) := by
        rw [Units.mul_inv, Matrix.mul_one, hJK, Matrix.mul_one, hX, hb, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem fr_eq {D : D7} {S T : HSp D} {βS : GL (Fin S.rank) (Datum.EAf D)} (βT : GL (Fin T.rank) (Datum.EAf D)) {r : ℕ} {e : AE D}
    {a : D.host.E} {g : GA D S} (hg : IsFlipElt S βS r e a g) {w : WO S T} (hw : IsHalf e w) :
    frMapO S T βS βT (actO S T g⁻¹ 1 w) = frMapO S T βS βT w * (diagW D S.rank r a * gramFr S βS) := by
  have h1 := smul_frMapO βS βT hw
  calc _ = frMapO S T βS βT w * ((βS⁻¹).val * (mt S g).map (toEAf D) * βS.val) := by
        unfold frMapO
        rw [map_actO]
        simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]
    _ = _ := by
        rw [← h1, Matrix.smul_mul, Matrix.smul_mul, ← Matrix.mul_smul (frMapO S T βS βT w), hg.2, Matrix.mul_smul]

theorem det_eq {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Datum.EAf D)} {r : ℕ} {e : AE D} (he : e * e = e)
    {a : D.host.E} {g : GA D V} (hg : IsFlipElt V β r e a g) :
    ∃ m : ℕ, toEAf D e * toEAf D (mt V g).det = toEAf D e * (eToEAf D a ^ m * (gramFr V β).det) := by
  refine ⟨(Finset.univ.filter fun k : Fin V.rank => ¬ k.val < r).card, ?_⟩
  have h1 := congrArg (fun M => toEAf D e * Matrix.det M) hg.2
  have h2 : IsIdempotentElem (toEAf D e) := by rw [IsIdempotentElem, ← map_mul, he]
  have h3 : ((β⁻¹).val * (mt V g).map (toEAf D) * β.val).det = toEAf D (mt V g).det := by
    rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one, one_mul,
      RingHom.map_det, RingHom.mapMatrix_apply]
  simp only [Matrix.det_smul] at h1
  rw [← mul_assoc, ← mul_assoc, ← pow_succ', h2.pow_succ_eq, h3, Matrix.det_mul] at h1
  rw [h1, diagW, Matrix.det_diagonal, Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]

theorem frMapO_nsmul {D : D7} {S T : HSp D} (βS : GL (Fin S.rank) (Datum.EAf D)) (βT : GL (Fin T.rank) (Datum.EAf D)) (N : ℕ)
    (x : WO S T) : frMapO S T βS βT (N • x) = N • frMapO S T βS βT x := by
  unfold frMapO
  rw [← Matrix.smul_mul, ← Matrix.mul_smul]
  congr 2
  exact Matrix.ext fun i j => map_nsmul (toEAf D) N (x i j)

theorem lat_facts {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (Datum.EAf D)} {βT : GL (Fin T.rank) (Datum.EAf D)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {e : AE D} {Q : Finset (Pl D.host.E)} (he : IsIdemSum e Q)
    (hP : ∀ PP ∈ Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    {N : ℕ} (hN : ∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) {ϖ : 𝓞 D.host.E} (hϖ0 : ϖ ≠ 0)
    (hϖ : ∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) {r : ℕ} {g : GA D S} (hg : IsFlipElt S βS r e (ϖ : D.host.E) g) :
    (∀ w ∈ latAll S T ΛS ΛT, IsHalf e w → actO S T g⁻¹ 1 w ∈ latAll S T ΛS ΛT) ∧
    (∀ w, IsHalf e w → actO S T g⁻¹ 1 w ∈ latAll S T ΛS ΛT → N • w ∈ latAll S T ΛS ΛT) ∧
    (∀ t, IsHalf (cA D e) t → actO S T g⁻¹ 1 t ∈ latAll S T ΛS ΛT → t ∈ latAll S T ΛS ΛT) ∧
    (∀ t ∈ latAll S T ΛS ΛT, IsHalf (cA D e) t → N • actO S T g⁻¹ 1 t ∈ latAll S T ΛS ΛT) := by
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ0
  have he' := isIdemSum_conj he
  have hP' : ∀ PP ∈ Q.image conjPl, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hPP
    obtain ⟨P, h, rfl⟩ := Finset.mem_image.1 hPP
    rw [GlobalTheory.DilChi.natCast_mem_conjPl]
    exact hP P h
  obtain ⟨iS, iS'⟩ := gramFr_int hS fS
  obtain ⟨iT, iT'⟩ := gramFr_int hT fT
  have hns : ∀ (c : AE D) (t : WO S T), IsHalf c t → IsHalf c (N • t) := fun c t ht i j => by
    change c * (N • t i j) = N • t i j
    rw [mul_smul_comm, ht i j]
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hd : IsIntM (N • toEAf D e • diagW D S.rank r (ϖ : D.host.E)⁻¹) := by
    intro i j
    have k1 : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee]))
    have k2 := GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.DilScalar.idemSum_dil_int he hN hϖ)
    rw [Matrix.smul_apply, Matrix.smul_apply, diagW, Matrix.diagonal_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one]; exact nsmul_mem k1 N
    · convert k2 using 1
      rw [map_mul, map_mul, map_mul, map_natCast, map_natCast, nsmul_eq_mul, mul_left_comm]
      rfl
    · rw [mul_zero, smul_zero]; exact zero_mem _
  have hdd : diagW D S.rank r (ϖ : D.host.E)⁻¹ * diagW D S.rank r (ϖ : D.host.E) = 1 := by
    rw [diagW_mul, inv_mul_cancel₀ hϖE, diagW_one]
  have hdd' : diagW D S.rank r (ϖ : D.host.E) * diagW D S.rank r (ϖ : D.host.E)⁻¹ = 1 := mul_eq_one_comm.1 hdd
  refine ⟨fun w hw hh => ?_, fun w hh hw => ?_, fun t hh ht => ?_, fun t ht hh => ?_⟩
  · refine GlobalTheory.HalfLatInt.mem_of_isIntM hS hT fS fT he hP ((isHalf_actO _ _ w).2 hh) ?_
    rw [fr_eq βT hg hh]
    exact int_mul (GlobalTheory.HalfLatInt.isIntM_of_mem hS fS fT he hP hh hw) (int_mul (diagW_int _ _ ϖ) iS)
  · refine GlobalTheory.HalfLatInt.mem_of_isIntM hS hT fS fT he hP (hns _ _ hh) ?_
    have h1 := GlobalTheory.HalfLatInt.isIntM_of_mem hS fS fT he hP ((isHalf_actO _ _ w).2 hh) hw
    have h2 := int_mul (int_mul h1 iS') hd
    rw [fr_eq βT hg hh, Matrix.mul_assoc _ _ (gramFrInv S βS), Matrix.mul_assoc _ _ (gramFrInv S βS), gramFr_mul_inv,
      Matrix.mul_one, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_assoc, hdd', Matrix.mul_one, smul_frMapO βS βT hh] at h2
    rwa [frMapO_nsmul]
  · have h1 := GlobalTheory.HalfLatInt.isIntM_of_mem hS fS fT he' hP' ((isHalf_actO _ _ t).2 hh) ht
    have h2 := int_mul (int_mul (diagW_int S.rank r ϖ) (int_ct h1)) iT
    rw [← adj_eq βT hg hh] at h2
    have hid : idem Q = e := idem_eq he
    exact GlobalTheory.ConjLatAdj.mem_latO_of_adj_int hS hT fS fT (GlobalTheory.QHalfLat.placesOK_of he hP) (by rw [hid]; exact hh) h2
  · have hh' := (isHalf_actO g⁻¹ 1 t).2 hh
    refine GlobalTheory.HalfLatInt.mem_of_isIntM hS hT fS fT he' hP' (hns _ _ hh') ?_
    have h1 := GlobalTheory.HalfLatInt.isIntM_adj hS hT fS fT (GlobalTheory.HalfLatInt.isIntM_of_mem hS fS fT he' hP' hh ht)
    have h2 := int_mul (int_mul hd h1) iT'
    rw [adj_eq βT hg hh, Matrix.mul_assoc, Matrix.mul_assoc _ _ (gramFrInv T βT), gramFr_mul_inv, Matrix.mul_one,
      Matrix.smul_mul, Matrix.smul_mul, ← Matrix.mul_assoc, hdd, Matrix.one_mul, smul_ct_frMapO βS βT hh'] at h2
    rw [frMapO_nsmul]
    intro i j
    have h3 := GlobalTheory.PlaceVec.cF_mem_int (h2 j i)
    rw [Matrix.smul_apply, map_nsmul] at h3
    rw [Matrix.smul_apply]
    convert h3 using 2
    exact (congrFun (congrFun (ct_ct _) i) j).symm

theorem isSBHalf_actPull {D : D7} {S T : HSp D} {e : AE D} {Λ : AddSubgroup (WO S T)} {g : GA D S} {N : ℕ} (hN : N ≠ 0)
    (h1 : ∀ t, IsHalf e t → actO S T g⁻¹ 1 t ∈ Λ → t ∈ Λ) (h2 : ∀ t ∈ Λ, IsHalf e t → N • actO S T g⁻¹ 1 t ∈ Λ)
    (Φ : WO S T → ℂ) (hΦ : IsSBHalf e Λ Φ) : IsSBHalf e Λ (actPull (g, (1 : GA D T)) Φ) := by
  obtain ⟨hsupp, k, hk, hinv, hcpt⟩ := hΦ
  have hns : ∀ (m : ℕ) (t : WO S T), IsHalf e t → IsHalf e (m • t) := fun m t ht i j => by
    change e * (m • t i j) = m • t i j
    rw [mul_smul_comm, ht i j]
  refine ⟨fun t ht => (isHalf_actO _ _ t).1 (hsupp _ ht), k * N, Nat.mul_pos hk (Nat.pos_of_ne_zero hN),
    fun u hu hue t => ?_, fun t ht => ?_⟩
  · simp only [actPull, inv_one]
    rw [actO_add, actO_nsmul, mul_smul]
    exact hinv _ (h2 u hu hue) (hns _ _ ((isHalf_actO _ _ u).2 hue)) _
  · have hth : IsHalf e t := (isHalf_actO _ _ t).1 (hsupp _ ht)
    have h3 := hcpt _ ht
    simp only [inv_one] at h3
    rw [← actO_nsmul] at h3
    rw [mul_comm, mul_smul]
    exact nsmul_mem (h1 _ (hns _ _ hth) h3) N

theorem om_model {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {e : AE D} {Q : Finset (Pl D.host.E)} (he : IsIdemSum e Q)
    {N : ℕ} (hN : N ≠ 0) {g : GA D S} (hg : SuppAt e S g) {x : (AE D)ˣ} (hx : IsDetAt e S g x)
    (l1 : ∀ w ∈ latAll S T ΛS ΛT, IsHalf e w → actO S T g⁻¹ 1 w ∈ latAll S T ΛS ΛT)
    (l2 : ∀ w, IsHalf e w → actO S T g⁻¹ 1 w ∈ latAll S T ΛS ΛT → N • w ∈ latAll S T ΛS ΛT)
    (l3 : ∀ t, IsHalf (cA D e) t → actO S T g⁻¹ 1 t ∈ latAll S T ΛS ΛT → t ∈ latAll S T ΛS ΛT)
    (l4 : ∀ t ∈ latAll S T ΛS ΛT, IsHalf (cA D e) t → N • actO S T g⁻¹ 1 t ∈ latAll S T ΛS ΛT)
    {f : WO S T → ℂ} (hθ : IsThetaFunO ψ S T f)
    (hfix : ∀ u ∈ latAll S T ΛS ΛT, (IsHalf e u ∨ IsHalf (cA D e) u) → heisO ψ S T u f = f) :
    ∃ s : ℂ, UnitOff N s ∧ ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latAll S T ΛS ΛT) 1 f Tm →
      ∀ Φ, IsSBHalf (cA D e) (latAll S T ΛS ΛT) Φ →
        om (g, 1) (Tm Φ) = ((((χT x : Circle) : ℂ))⁻¹ * s) • Tm (actPull (g, (1 : GA D T)) Φ) := by
  obtain ⟨Rr, hR1, hR2, hRc⟩ := X_reps D ψ hW.std S T ΛS ΛT hS hT Q e he N hN g l1 l2
  have he' := isIdemSum_conj he
  have hcc : cA D (cA D e) = e := Formalism.L2.Theta.cA_cA e
  have hg' : SuppAt (cA D e) S g := fun i j => by rw [hcc, add_comm]; exact hg i j
  have hfix' : ∀ u ∈ latAll S T ΛS ΛT, (IsHalf (cA D e) u ∨ IsHalf (cA D (cA D e)) u) → heisO ψ S T u f = f :=
    fun u hu h => hfix u hu (by rw [hcc] at h; exact h.symm)
  refine ⟨_, hRc, fun Tm hTm Φ hΦ => ?_⟩
  have hom := GlobalTheory.T.weilOperator_idempotentSum_vacuum_normalised_sum D ψ S T _ _ _ hW ΛS ΛT hS hT _ _ he' g x hg' (by rw [hcc]; exact hx) Rr
    (by rw [hcc]; exact hR1) (by rw [hcc]; exact hR2) (by rw [hcc]; exact l1) f hθ hfix'
  have hsum := GlobalTheory.T.sum_heisenbergTranslates_baseVector_eq_card_smul D ψ hW.std S T ΛS ΛT hS hT _ _ he' g l3 Rr
    (by rw [hcc]; exact hR1) (by rw [hcc]; exact hR2) (by rw [hcc]; exact l1) f Tm hTm
  have hvac : om (g, 1) f = ((((χT x : Circle) : ℂ))⁻¹ * ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ)) •
      Tm (actPull (g, (1 : GA D T)) (halfInd (cA D e) (latAll S T ΛS ΛT))) := by
    rw [hom, hsum, smul_smul]
    congr 1
    have hs : ((Rr.card : ℕ) : ℂ) = ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) * ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
    rw [hs]
    simp only [splitFacO, map_one, mul_one, Circle.coe_inv]
    by_cases h0 : ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) = 0
    · rw [h0]; simp
    · field_simp
  exact GlobalTheory.T.weilRep_apply_eq_smul_of_halfIndicator_base D ψ S T _ _ _ hW ΛS ΛT hS hT _ _ he' f hθ hfix' Tm hTm (g, 1) _ (isSBHalf_actPull hN l3 l4) hvac Φ hΦ

section Real

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem isSBHalf_flatDat (hC : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) {Q : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e Q)
    (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : IsSBHalf e (lattice₂ R i) (flatDat R i Q ξ e) := by
  have sV := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have sW := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  have hinf := GlobalTheory.PlaceVec.idemSum_infPart he
  refine GlobalTheory.PlaceDatum.isSBHalf_of_red _ _ (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)) (GlobalTheory.PlaceDatum.frMapO_add _ _)
      (GlobalTheory.PlaceDatum.exists_den_frMapO sV.1.fg sW.1.fg _ _) ?_ Q _ fun y y' h => GlobalTheory.FlatVecExist.omegaFlat_congr _ _ _ h
  obtain ⟨K, hK, h'⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO sV.1 sW.1 (R.βV i) (R.βW i)
  exact ⟨K, hK, fun t ht => h' t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht)⟩

theorem base_facts (hC : GlobalTheory.Hk3.Core R F) (hG : QGuard R) {i : Fin D.R.m} {t : T0} (hV : VStd D i)
    {K L : Finset (Pl D.host.E)} (hK : K ⊆ R.Q t) (hL : L ⊆ R.Q t) (hd : Disjoint K L) {eg ea et : AE D}
    {fg b : WO (Vc D i) (Wc D i) → ℂ} (heg : IsIdemSum eg R.Pg) (hea : IsIdemSum ea K) (het : IsIdemSum et L)
    (hfg : IsTypeVec R i eg fg) (hb : ThAt R i ea fg (flatDat R i K (R.xiR t) ea) b) :
    IsThetaFunO R.ψ (Vc D i) (Wc D i) b ∧ ∀ u ∈ latAll (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i), (IsHalf et u ∨ IsHalf (cA D et) u) →
      heisO R.ψ (Vc D i) (Wc D i) u b = b := by
  have hk := kerDat_tuple (i := i) hC.lev hC.thP t
  have hsp := splitSet_tuple hC i t
  obtain ⟨hSV, hSW, hθ, hfix0⟩ := GlobalTheory.T.tameKernel_typePlaceThetaVector_latticeFixed D G Pl0 T0 A Ks R F hC hG i hV _ _ _ _ _ _ hk ⟨t, subset_rfl⟩ eg
    (idem (R.Q t)) fg heg hsp.isIdemSum hfg
  have hfix : ∀ {e : AE D} {P : Finset (Pl D.host.E)}, P ⊆ R.Q t → IsIdemSum e P →
      ∀ u ∈ latAll (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i), (IsHalf e u ∨ IsHalf (cA D e) u) →
      heisO R.ψ (Vc D i) (Wc D i) u fg = fg := fun {e P} hP he u hu h => by
    have hsub : idem (R.Q t) * e = e := by rw [← idem_eq he]; exact idem_mul_of_subset hsp hP
    have hsubc : cA D (idem (R.Q t)) * cA D e = cA D e := by rw [← map_mul, hsub]
    exact hfix0 u hu (h.imp (isHalf_mono hsub) (isHalf_mono hsubc))
  obtain ⟨Tm, hTm, -, hth, hfx⟩ := Formalism.IndefR.Fin.placeModelAt_of (Formalism.IndefR.Fin.placeLatDual D) R.ψ hk.weil.std _ _ _ _ hSV hSW
    K ea hea fg hθ (hfix hK hea) ea (Or.inl rfl)
  have hsb := isSBHalf_flatDat hC i hea (R.xiR t)
  rw [hb.2 Tm hTm]
  refine ⟨hth _ hsb, fun u hu h => hfx _ hsb u ?_ (hfix hL het u hu h)⟩
  have h1 : ea * et = 0 := by
    rw [← idem_eq hea, ← idem_eq het, show idem K = ∑ PP ∈ K, idemAt PP from rfl, Finset.sum_mul]
    exact Finset.sum_eq_zero fun j hj => GlobalTheory.FlatThreeSteps.idemAt_mul_idem hsp hL (hK hj) (Finset.disjoint_left.1 hd hj)
  have h2 : ea * cA D et = 0 := by
    rw [← idem_eq hea, ← idem_eq het, idem, idem, map_sum, Finset.sum_mul_sum]
    exact Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun c hc => hsp.mul_conj (hK ha) (hL hc)
  have h3 : cA D ea * cA D et = 0 := by rw [← map_mul, h1, map_zero]
  have h4 : cA D ea * et = 0 := by rw [← Formalism.L2.Theta.cA_cA et, ← map_mul, h2, map_zero]
  intro a c
  rcases h with h | h
  · rw [← h a c, ← mul_assoc, add_mul, h1, h4, add_zero, zero_mul]
  · rw [← h a c, ← mul_assoc, add_mul, h2, h3, add_zero, zero_mul]

theorem pull_flat (hC : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) {Q : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e Q)
    {ϖ : 𝓞 D.host.E} (hϖ0 : ϖ ≠ 0) (hϖ : ∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) {g : GA D (Vc D i)}
    (hg : IsFlipElt (Vc D i) (R.βV i) (Wc D i).rank e (ϖ : D.host.E) g) (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (hξ : ∀ PP ∈ Q, ∀ u : (kP PP)ˣ, ξ' (conjPl PP) (Units.map (conjK PP).toMonoidHom u) = (ξ PP u)⁻¹) :
    ∃ c₀ : ℂ, GlobalTheory.ConjTwist.IsRoot1 c₀ ∧ actPull (g, (1 : GA D (Wc D i))) (flatDat R i (Q.image conjPl) ξ' (cA D e)) =
      c₀ • adjDat R i Q ξ (cA D e) := by
  have sW := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  obtain ⟨cW, hBW⟩ := hC.lev.βW i
  obtain ⟨iW, iW'⟩ := gramFr_int sW hBW.1
  obtain ⟨c₀, hc₀, hval⟩ := X_pval D Q ϖ (fun PP h => (hϖ PP h).1) (Vc D i).rank (Wc D i).rank
    ((rank_Wc i).trans_le (r_le_V i)) _ _ iW iW' (gramFr_mul_inv _ _) ξ ξ' hξ
  refine ⟨c₀, hc₀, funext fun x => ?_⟩
  simp only [actPull, inv_one, flatDat, adjDat, Pi.smul_apply, smul_eq_mul]
  by_cases hx : IsHalf (cA D e) x
  swap
  · rw [if_neg fun h => hx ((isHalf_actO _ _ x).1 h.1), if_neg fun h => hx h.1, mul_zero]
  have hx' : IsHalf (cA D e) (actO (Vc D i) (Wc D i) g⁻¹ 1 x) := (isHalf_actO _ _ x).2 hx
  rw [adj_eq (R.βW i) hg hx]
  have hy : toEAf D e • ct (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (actO (Vc D i) (Wc D i) g⁻¹ 1 x)) =
      ct (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (actO (Vc D i) (Wc D i) g⁻¹ 1 x)) := smul_ct_frMapO _ _ hx'
  generalize frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (actO (Vc D i) (Wc D i) g⁻¹ 1 x) = y at hy ⊢
  by_cases hi : IsIntM y
  · rw [if_pos ⟨hx', hi⟩, if_pos ⟨hx, int_mul (int_mul (diagW_int _ _ ϖ) (int_ct hi)) iW⟩]
    exact hval y hi
  · rw [if_neg fun h => hi h.2]
    split_ifs with h
    · unfold omegaQ
      rw [dif_neg, mul_zero]
      intro h'
      have := int_ct (X_pint D Q e he ϖ hϖ hϖ0 _ _ _ _ iW' (gramFr_mul_inv _ _) _ hy h.2 fun PP hPP => (h' PP hPP).1)
      rw [ct_ct] at this
      exact hi this
    · rw [mul_zero]

end Real

theorem flat_conj_eq_unit_smul_om : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (B : Base (Vc D i) (Wc D i)) (ψ : Twist D Circle), B.Good → BaseOf R i B → ψ.Good → B.admitted ψ.Q → R.xi t = B.de.chi * ψ.chi → idem (R.Q t) + cA D (idem (R.Q t)) = idem (B.de.Q ∪ ψ.Q) + cA D (idem (B.de.Q ∪ ψ.Q)) → ∀ (eg ea et : AE D) (fg b : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum ea (keepPart (R := R) t (B.de.Q ∪ ψ.Q)) → IsIdemSum et (flipPart (R := R) t (B.de.Q ∪ ψ.Q)) → GlobalTheory.BaseCmp.IsTypeVec R i eg fg → ThAt R i ea fg (GlobalTheory.BaseCmp.flatDat R i (keepPart (R := R) t (B.de.Q ∪ ψ.Q)) (R.xiR t) ea) b → ∃ (z : GA D (Vc D i)) (c : ℂ), SuppAt et (Vc D i) z ∧ SuppAt (idem (R.Q t)) (Vc D i) z ∧ UnitOff (GlobalTheory.TwistField.tupPrime R t) c ∧ ∀ f₁ f₂, ThAt R i (cA D et) b (GlobalTheory.BaseCmp.flatDat R i ((flipPart (R := R) t (B.de.Q ∪ ψ.Q)).image conjPl) (fun PP => B.de.locC PP * ψ.locC PP) (cA D et)) f₁ → ThAt R i (cA D et) b (adjDat R i (flipPart (R := R) t (B.de.Q ∪ ψ.Q)) (R.xiR t) (cA D et)) f₂ → f₁ = c • R.ωP i t (z⁻¹, 1) f₂ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i t hV B ψ hB hBO hψ hQ hxi hid eg ea et fg b heg hea het hfg hb
  have hsp := splitSet_tuple hC i t
  have hQ' : SplitSet (B.de.Q ∪ ψ.Q) := by
    obtain ⟨P, -, s2, hP⟩ := hQ.1.split
    exact hP.mono s2
  have mk : ∀ PP, PP ∈ keepPart (R := R) t (B.de.Q ∪ ψ.Q) ↔ PP ∈ R.Q t ∧ PP ∈ B.de.Q ∪ ψ.Q := fun PP => Finset.mem_filter
  have mf : ∀ PP, PP ∈ flipPart (R := R) t (B.de.Q ∪ ψ.Q) ↔ PP ∈ R.Q t ∧ PP ∉ B.de.Q ∪ ψ.Q := fun PP => Finset.mem_filter
  generalize keepPart (R := R) t (B.de.Q ∪ ψ.Q) = K at mk hea hb ⊢
  generalize flipPart (R := R) t (B.de.Q ∪ ψ.Q) = L at mf het ⊢
  have hK : K ⊆ R.Q t := fun PP h => ((mk PP).1 h).1
  have hL : L ⊆ R.Q t := fun PP h => ((mf PP).1 h).1
  have hd : Disjoint K L := Finset.disjoint_left.2 fun PP h1 h2 => ((mf PP).1 h2).2 ((mk PP).1 h1).2
  obtain ⟨hθ, hfix⟩ := base_facts hC hQG hV hK hL hd heg hea het hfg hb
  obtain ⟨ϖ, hϖ0, hϖ⟩ := GlobalTheory.FlatLift.exists_unif D.host.E L
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ0
  have hN : GlobalTheory.TwistField.tupPrime R t ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun q hq => ?_
    obtain ⟨PP, -, rfl⟩ := Finset.mem_image.1 hq
    exact GlobalTheory.TupDil.card_ne_zero PP
  have hNQ : ∀ PP ∈ L, ((GlobalTheory.TwistField.tupPrime R t : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hPP
    obtain ⟨c, hc⟩ : Nat.card (kP PP) ∣ GlobalTheory.TwistField.tupPrime R t :=
      Finset.dvd_prod_of_mem (fun q : ℕ => q) (Finset.mem_image_of_mem (fun PP => Nat.card (kP PP)) (hL hPP))
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (GlobalTheory.TupDil.card_mem PP)
  obtain ⟨g, hg⟩ := exists_flip (Vc D i) (R.βV i) (Wc D i).rank het hϖE
  have sV := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have sW := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  obtain ⟨cV, hBV⟩ := hC.lev.βV i
  obtain ⟨cW, hBW⟩ := hC.lev.βW i
  obtain ⟨l1, l2, l3, l4⟩ := lat_facts sV sW hBV.1 hBW.1 het (fun PP h => hQG.2 t PP (hL h)) hNQ hϖ0 hϖ hg
  have hee : et * et = et := GlobalTheory.PlaceVec.idemSum_mul_self het
  obtain ⟨x, hx⟩ : ∃ x : (AE D)ˣ, IsDetAt et (Vc D i) g x := by
    have hdet : (mt (Vc D i) g).det * (mt (Vc D i) g⁻¹).det = 1 := by
      rw [← Matrix.det_mul, ← mt_mul', mul_inv_cancel, mt_one', Matrix.det_one]
    refine ⟨⟨et * (mt (Vc D i) g).det + (1 - et), et * (mt (Vc D i) g⁻¹).det + (1 - et), ?_, ?_⟩, rfl⟩
    · linear_combination (et * et) * hdet + (2 - (mt (Vc D i) g).det - (mt (Vc D i) g⁻¹).det) * hee
    · linear_combination (et * et) * hdet + (2 - (mt (Vc D i) g).det - (mt (Vc D i) g⁻¹).det) * hee
  have hW := (kerDat_tuple (i := i) hC.lev hC.thP t).weil
  obtain ⟨s, hs, hact⟩ := om_model hW sV sW het hN hg.1 hx l1 l2 l3 l4 hθ hfix
  obtain ⟨m, hm⟩ := det_eq hee hg
  obtain ⟨iV, iV'⟩ := gramFr_int sV hBV.1
  have hchi := X_det D G Pl0 T0 A Ks R F hC i t L hL _ hNQ et het ϖ hϖ0 hϖ m _ _ (det_int iV) (det_int iV')
    (by rw [← Matrix.det_mul, gramFr_mul_inv, Matrix.det_one]) x
    (by rw [hx]; linear_combination (1 - (mt (Vc D i) g).det) * hee)
    (by rw [← hm, ← map_mul, ← map_mul, hx]; congr 1; linear_combination ((mt (Vc D i) g).det - 1) * hee)
  obtain ⟨c₀, hc₀, hpull⟩ := pull_flat hC i het hϖ0 hϖ hg (R.xiR t) (fun PP => B.de.locC PP * ψ.locC PP) fun PP hPP u =>
    X_chr D G Pl0 T0 A Ks R F hC i t B ψ hB hψ hQ hxi PP (hL hPP)
      ((GlobalTheory.FlatThreeSteps.mem_or_conj_mem hsp hQ' hid (hL hPP)).resolve_left ((mf PP).1 hPP).2) u
  have hsub : idem (R.Q t) * et = et := by rw [← idem_eq het]; exact idem_mul_of_subset hsp hL
  refine ⟨g, _, hg.1, suppAt_mono hsub het.2 hsp.isIdemSum.2 hg.1,
    GlobalTheory.BigOn.Exp.TupLe.unitOff_mul (GlobalTheory.BigOn.Exp.TupLe.unitOff_mul hchi hs) (GlobalTheory.BigOn.Exp.TupLe.unitOff_root hc₀.choose_spec.1.ne' hc₀.choose_spec.2),
    fun f₁ f₂ h₁ h₂ => ?_⟩
  obtain ⟨Tm, hTm⟩ := h₁.1
  have e1 := hact Tm hTm _ (isSBHalf_flatDat hC i (isIdemSum_conj het) fun PP => B.de.locC PP * ψ.locC PP)
  rw [hpull, map_smul, ← h₁.2 Tm hTm, ← h₂.2 Tm hTm, smul_smul] at e1
  rw [← map_smul, ← e1, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, mul_one, Prod.mk_one_one, map_one,
    Module.End.one_apply]

end GlobalTheory.FlipTranslate

theorem _root_.GlobalTheory.T.flatDatum_liftDatum_same_half_translate_conjugatePlaces : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (B : Base (Vc D i) (Wc D i)) (ψ : Twist D Circle), B.Good → BaseOf R i B → ψ.Good → B.admitted ψ.Q → R.xi t = B.de.chi * ψ.chi → idem (R.Q t) + cA D (idem (R.Q t)) = idem (B.de.Q ∪ ψ.Q) + cA D (idem (B.de.Q ∪ ψ.Q)) → ∀ (eg ea et : AE D) (fg b : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum ea (keepPart (R := R) t (B.de.Q ∪ ψ.Q)) → IsIdemSum et (flipPart (R := R) t (B.de.Q ∪ ψ.Q)) → GlobalTheory.BaseCmp.IsTypeVec R i eg fg → ThAt R i ea fg (GlobalTheory.BaseCmp.flatDat R i (keepPart (R := R) t (B.de.Q ∪ ψ.Q)) (R.xiR t) ea) b → ∃ (z : GA D (Vc D i)) (c : ℂ), SuppAt et (Vc D i) z ∧ SuppAt (idem (R.Q t)) (Vc D i) z ∧ UnitOff (GlobalTheory.TwistField.tupPrime R t) c ∧ ∀ f₁ f₂, ThAt R i (cA D et) b (GlobalTheory.BaseCmp.flatDat R i ((flipPart (R := R) t (B.de.Q ∪ ψ.Q)).image conjPl) (fun PP => B.de.locC PP * ψ.locC PP) (cA D et)) f₁ → ThAt R i (cA D et) b (adjDat R i (flipPart (R := R) t (B.de.Q ∪ ψ.Q)) (R.xiR t) (cA D et)) f₂ → f₁ = c • R.ωP i t (z⁻¹, 1) f₂ :=
  GlobalTheory.FlipTranslate.flat_conj_eq_unit_smul_om
