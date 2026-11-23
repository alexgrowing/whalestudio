import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalAddCharUnramifiedOfSplitsCompletelyAbovePla
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePairingTrivialMatricesSubMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMomentSurjectiveConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsMoreFurther

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.LinCoords

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def lift2 {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (τ : E →ₐ[F] Fv F v) (p q : Fv F v) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E :=
  GlobalTheory.InertLocField.liftT E v ((GlobalTheory.AdelicU.splitAlgEquiv h τ).symm (p, q))

variable {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (τ : E →ₐ[F] Fv F v)

theorem piW_liftT (t : E →ₐ[F] Fv F v) (y : Fv F v ⊗[F] E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t (GlobalTheory.InertLocField.liftT E v y) = GlobalTheory.AdelicU.splitProj t y := by
  change GlobalTheory.AdelicU.splitProj t (GlobalTheory.InertLocField.evT E v (GlobalTheory.InertLocField.liftT E v y)) = _
  rw [GlobalTheory.InertLocField.evT_liftT]

theorem piW_lift2 (p q : Fv F v) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ (lift2 h τ p q) = p := by
  rw [lift2, piW_liftT, GlobalTheory.AdelicU.splitProj_symm]

theorem piW_comp_lift2 (p q : Fv F v) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) (lift2 h τ p q) = q := by
  rw [lift2, piW_liftT, GlobalTheory.AdelicU.splitProj_comp_symm]

theorem at_lift2 (p q : Fv F v) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (lift2 h τ p q) :=
  GlobalTheory.InertLocField.at_liftT v _

theorem lift2_add (p q p' q' : Fv F v) : lift2 h τ (p + p') (q + q') = lift2 h τ p q + lift2 h τ p' q' := by
  unfold lift2
  rw [← map_add, ← map_add, Prod.mk_add_mk]

theorem lift2_zero : lift2 h τ 0 0 = 0 := by
  unfold lift2
  rw [← Prod.zero_eq_mk, map_zero, map_zero]

theorem eq_lift2 {z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E} (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z) :
    z = lift2 h τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ z) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) z) := by
  obtain ⟨y, rfl⟩ := (GlobalTheory.InertLocField.at_iff v z).1 hz
  rw [piW_liftT, piW_liftT, lift2]
  congr 1
  exact ((GlobalTheory.AdelicU.splitAlgEquiv h τ).symm_apply_apply y).symm

include h in
theorem trace_at {z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E} (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z) :
    evFin F v (Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) z) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ z + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) z := by
  obtain ⟨y, rfl⟩ := (GlobalTheory.InertLocField.at_iff v z).1 hz
  rw [GlobalTheory.InertLocField.trace_liftT, GlobalTheory.LatVac.evFin_liftV, GlobalTheory.OppLinChar.trace_split h τ, piW_liftT, piW_liftT]

theorem at_mat_iff {m n : Type} (M : Matrix m n (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) M ↔ ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (M i j) := by
  constructor
  · intro hM i j u hu
    have := congrFun (congrFun (hM u hu) i) j
    simpa using this
  · intro hM u hu
    ext i j
    simpa using hM i j u hu

end GlobalTheory.LinCoords

namespace GlobalTheory.LinCoords

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (AE At piW cA incM)

theorem piW_cA' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (τ : E →ₐ[F] Fv F v) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ w) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem piW_inclR' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (τ : E →ₐ[F] Fv F v) (e : E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ (inclR (F := F) (AF F) e) = τ e := by
  change evFin F v 1 * τ e = τ e
  simp

theorem sum_four_swap_pairs_reverse_inner {R α β : Type} [AddCommMonoid R] [Fintype α] [Fintype β] (f : α → β → α → β → R) :
    ∑ a, ∑ b, ∑ c, ∑ e, f a b c e = ∑ c, ∑ e, ∑ b, ∑ a, f a b c e := by
  first
  | exact @_root_.GlobalTheory.TargetEquivalence.target
  | exact _root_.GlobalTheory.TargetEquivalence.target
  | (apply _root_.GlobalTheory.TargetEquivalence.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.TargetEquivalence.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TargetEquivalence.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TargetEquivalence.target ..)

theorem splitTrace' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hcm : IsCMExt F E σ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (t : E →ₐ[F] Fv F v) {n d : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (K : Matrix (Fin d) (Fin d) E) (hJ : ∀ i j, σ (J j i) = J i j) (hK : ∀ i j, σ (K j i) = -K i j)
    (x u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) (hx : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) x) :
    GlobalTheory.AdelicU.evFin F v (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F K) x u) =
      ∑ i, ∑ j, (x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t)) i j * (-(J.map t * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (t.comp σ)) * (K.map t)ᵀ)) i j -
        ∑ i, ∑ j, (-(J.map t * x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (t.comp σ)) * (K.map t)ᵀ)) i j * (u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t)) i j := by
  have hzAt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v)
      ((-1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) * GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F K) x u) := by
    intro a ha
    have h0 : ∀ i j, a • x i j = 0 := fun i j => by
      have := congrFun (congrFun (hx a ha) i) j
      simpa using this
    simp only [GlobalTheory.WeilM.hTens, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
    rw [show ∀ (p q r : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E), a • ((-1) * (x i j * p * q * r)) = -1 * ((a • x i j) * p * q * r) from
      fun p q r => by simp only [Algebra.smul_def]; ring, h0]
    simp
  show GlobalTheory.AdelicU.evFin F v (Algebra.trace (AF F) _ _) = _
  rw [trace_at hcm t hzAt]
  simp only [GlobalTheory.WeilM.hTens, map_mul, map_neg, map_one, map_sum, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, piW_cA', piW_inclR',
    GlobalTheory.AdelicU.comp_conj_conj hcm, AlgHom.comp_apply, hJ, hK]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.neg_apply, Finset.mul_sum, Finset.sum_mul]
  rw [sub_eq_add_neg]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · rw [sum_four_swap_pairs_reverse_inner]
    simp only [neg_mul, mul_neg, one_mul, Finset.sum_mul, Finset.sum_neg_distrib, neg_neg]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun k _ => ?_
    ring

theorem coBar_eq' {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (u : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E)) :
    GlobalTheory.VacShape.coBar Bs Γ u =
      -(Γ.V'.J.map Bs.τ₁ * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig)) * (Γ.W.J.map Bs.τ₁)ᵀ) := by
  unfold GlobalTheory.VacShape.coBar
  simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem coords : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∃ uT uM : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) →+ Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E),
      (∀ Y, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) (uT Y) ∧ (uT Y).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = 0 ∧
        GlobalTheory.VacShape.coBar Bs Γ (uT Y) = Y) ∧
      (∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) (uM z) ∧
        (uM z).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig)) = 0 ∧ (uM z).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = -z) ∧
      (∀ u, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) u → ∃ Y z, u = uT Y + uM z) ∧
      (∀ x u, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) x → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) u →
        evFin D.host.F Bs.v₁ (symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) x u) =
          ∑ i, ∑ j, (x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁)) i j * GlobalTheory.VacShape.coBar Bs Γ u i j -
            ∑ i, ∑ j, GlobalTheory.VacShape.coBar Bs Γ x i j * (u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁)) i j) := by
  intro D a a' Bs Γ X om om' hTr
  have hcm := hTr.base.cm
  have hV' := GlobalTheory.WeilSchrodingerHerm.det_J_ne_zero D Bs Γ.V' hTr.geo.hV'
  have hW := GlobalTheory.VacShapeBd.det_ne_zero_skew Bs Γ.W hTr.geo.hW
  set A := Γ.V'.J.map Bs.τ₁ with hAdef
  set B := (Γ.W.J.map Bs.τ₁)ᵀ with hBdef
  have hA : IsUnit A.det := by
    rw [isUnit_iff_ne_zero, hAdef]
    have hm : (Γ.V'.J.map Bs.τ₁).det = (Bs.τ₁ : D.host.E →+* Fv D.host.F Bs.v₁) Γ.V'.J.det :=
      (RingHom.map_det _ _).symm
    rw [hm]
    exact (map_ne_zero _).2 hV'
  have hB : IsUnit B.det := by
    rw [isUnit_iff_ne_zero, hBdef, Matrix.det_transpose]
    have hm : (Γ.W.J.map Bs.τ₁).det = (Bs.τ₁ : D.host.E →+* Fv D.host.F Bs.v₁) Γ.W.J.det :=
      (RingHom.map_det _ _).symm
    rw [hm]
    exact (map_ne_zero _).2 hW
  have hco : ∀ u : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E),
      GlobalTheory.VacShape.coBar Bs Γ u = -(A * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig)) * B) := fun u => coBar_eq' Bs Γ u
  let uT : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) →+
      Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E) :=
    { toFun := fun Y => (-(A⁻¹ * Y * B⁻¹)).map (fun q => lift2 hcm Bs.τ₁ 0 q)
      map_zero' := by
        ext i j
        simp only [Matrix.mul_zero, Matrix.zero_mul, neg_zero, Matrix.map_apply, Matrix.zero_apply]
        exact lift2_zero hcm Bs.τ₁
      map_add' := fun Y Y' => by
        ext i j
        simp only [Matrix.mul_add, Matrix.add_mul, neg_add, Matrix.map_apply, Matrix.add_apply]
        rw [← lift2_add, add_zero] }
  let uM : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) →+
      Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E) :=
    { toFun := fun z => (-z).map (fun p => lift2 hcm Bs.τ₁ p 0)
      map_zero' := by
        ext i j
        simp only [neg_zero, Matrix.map_apply, Matrix.zero_apply]
        exact lift2_zero hcm Bs.τ₁
      map_add' := fun z z' => by
        ext i j
        simp only [neg_add, Matrix.map_apply, Matrix.add_apply]
        rw [← lift2_add, add_zero] }
  have hTapp : ∀ Y i j, uT Y i j = lift2 hcm Bs.τ₁ 0 ((-(A⁻¹ * Y * B⁻¹)) i j) := fun _ _ _ => rfl
  have hMapp : ∀ z i j, uM z i j = lift2 hcm Bs.τ₁ ((-z) i j) 0 := fun _ _ _ => rfl
  have hinv : ∀ U : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁), -(A⁻¹ * -(A * U * B) * B⁻¹) = U := by
    intro U
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]
  refine ⟨uT, uM, ?_, ?_, ?_, ?_⟩
  · intro Y
    have hx : (uT Y).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig)) = -(A⁻¹ * Y * B⁻¹) := by
      ext i j
      rw [Matrix.map_apply, hTapp, piW_comp_lift2]
    refine ⟨(at_mat_iff _).2 fun i j => at_lift2 hcm Bs.τ₁ _ _, ?_, ?_⟩
    · ext i j
      rw [Matrix.map_apply, hTapp, piW_lift2, Matrix.zero_apply]
    · rw [hco, hx]
      simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hB, Matrix.mul_one]
  · intro z
    refine ⟨(at_mat_iff _).2 fun i j => at_lift2 hcm Bs.τ₁ _ _, ?_, ?_⟩
    · ext i j
      rw [Matrix.map_apply, hMapp, piW_comp_lift2, Matrix.zero_apply]
    · ext i j
      rw [Matrix.map_apply, hMapp, piW_lift2]
  · intro u hu
    refine ⟨GlobalTheory.VacShape.coBar Bs Γ u, -u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁), ?_⟩
    ext i j
    rw [Matrix.add_apply, hTapp, hMapp, ← lift2_add, zero_add, add_zero, neg_neg, hco, hinv]
    exact eq_lift2 hcm Bs.τ₁ ((at_mat_iff u).1 hu i j)
  · intro x u hx _
    rw [splitTrace' hcm Bs.v₁ Bs.τ₁ Γ.V'.J Γ.W.J hTr.geo.hV'.herm hTr.geo.hW.skew x u hx, hco, hco]

end GlobalTheory.LinCoords
