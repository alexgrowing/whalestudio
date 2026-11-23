import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.HypothesesAtTripleAlg
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.VaceigenDual
import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasAd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice

noncomputable section

namespace PositivityTheory.ThK.PT

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.UG (IsInertAt)
open Neutral.B1 (localIdele)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)}

theorem isField_Ev (hw : IsInertAt F E v w) : IsField (Ev E v) :=
  MulEquiv.isField (Field.toIsField _) (complEquiv hw ((under_eq_iff hw w).2 rfl)).toMulEquiv

theorem isQuad_Ev (hσ : IsCMExt F E σ) (v : Pl F) : ∃ ξ, IsQuad (cV σ v) ξ := by
  obtain ⟨δ, b, hδ, h0, h1, -⟩ := GlobalTheory.QuadNormBase.exists_basis F E σ hσ.2.2.1 (conj_conj hσ) (not_forall.1 (conj_ne hσ))
  refine ⟨inclR (F := F) (Fv F v) (b 1), (b.ne_zero 1).isUnit.map _, ?_, Algebra.TensorProduct.basis (Fv F v) b, ?_, ?_⟩
  · change inclR (F := F) (Fv F v) (σ (b 1)) = _
    rw [h1, map_neg]
  · rw [Algebra.TensorProduct.basis_apply, h0]; rfl
  · rw [Algebra.TensorProduct.basis_apply]; rfl

omit [NumberField E] in
theorem comp_cA (z : AE F E) : compFin F E v (cA σ z) = cV σ v (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [NumberField E] in
theorem comp_incl (x : E) : compFin F E v (inclR (F := F) (AF F) x) = inclR (F := F) (Fv F v) x :=
  congrArg (· ⊗ₜ[F] x) (map_one (evFin F v))

theorem toCompl_cV {h : w.under (𝓞 F) = v} {c : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c) (y : Ev E v) :
    toCompl h (cV σ v y) = c (toCompl h y) := by
  rw [hc]
  congr 1

theorem psi_good {ψ : AddChar (AF F) ℂ} (h : IsStd ψ) (hu : PsiUnr ψ v) {ψv : AddChar (Fv F v) ℂ} (e : ∀ x, ψv x = psiLoc ψ v x) :
    Continuous ψv ∧ ψv ≠ 1 := by
  refine ⟨?_, fun h1 => ?_⟩
  · rw [show (ψv : _ → ℂ) = psiLoc ψ v from funext e]
    exact h.1.comp (continuous_const.prodMk (continuous_singleFin v))
  · obtain ⟨x, hx⟩ := v.valuedAdicCompletion_surjective F (WithZero.exp (1 : ℤ))
    have := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((hu x).1 fun y _ => by rw [← e, h1]; rfl)
    rw [hx] at this
    exact absurd this (by decide)

theorem locIdele_spec (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) (y : (Ev E v)ˣ) :
    At (evFin F v) ((locIdele F w (Units.map (toCompl h).toMonoidHom y) : AE F E) - 1) ∧
      Units.map (compFin F E v).toMonoidHom (locIdele F w (Units.map (toCompl h).toMonoidHom y)) = y := by
  set x := Units.map (toCompl h).toMonoidHom y with hx
  have hf := finTens_locIdele (F := F) w x
  refine ⟨fun u hu => tens_ext ?_ ((finAdEquiv F E).injective (FiniteAdeleRing.ext _ fun P => ?_)),
    Units.ext ((toCompl_bijective hw h).1 ?_)⟩
  · rw [Algebra.smul_def, map_mul, map_sub, infTens_locIdele, map_one, sub_self, mul_zero, map_zero]
  · rw [Algebra.smul_def, map_mul, map_sub, map_one, map_mul, map_sub, hf, map_one, map_zero, map_zero]
    change (complMap rfl (u.2 (P.under (𝓞 F))) * algebraMap E _ 1) * (Neutral.B1.finiteSingle E w x.1 P - 1) = 0
    by_cases e : P = w
    · subst e
      subst h
      rw [show u.2 (P.under (𝓞 F)) = 0 from hu, map_zero, zero_mul, zero_mul]
    · rw [finSingle_ne e, sub_self, mul_zero]
  · have e1 := finAdEquiv_apply h (finTens F E (locIdele F w x))
    rw [hf] at e1
    have e2 : ∀ z : AE F E, Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) (finTens F E z) = compFin F E v z := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a x => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [e2] at e1
    exact e1.symm.trans (finSingle_self w _)

theorem locChar_eq (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) {χ : Chr F E} {χv : (Ev E v)ˣ →* Circle}
    (H : IsLocChar χ v χv) (y : (Ev E v)ˣ) : χv y = χ (locIdele F w (Units.map (toCompl h).toMonoidHom y)) := by
  rw [← H _ (locIdele_spec hw h y).1, (locIdele_spec hw h y).2]

theorem continuous_loc (hw : IsInertAt F E v w) {χ : Chr F E} (hχ : Continuous χ) {χv : (Ev E v)ˣ →* Circle}
    (H : IsLocChar χ v χv) : Continuous χv := by
  have h := (under_eq_iff hw w).2 rfl
  rw [show (χv : _ → Circle) = _ from funext (locChar_eq hw h H)]
  exact hχ.comp ((continuous_locIdele w).comp (Continuous.units_map _ (continuous_complEquiv hw h).1))

omit [NumberField E] in
theorem loc_algebraMap {χ : Chr F E} {χv : (Ev E v)ˣ →* Circle} (H : IsLocChar χ v χv) (a : (Fv F v)ˣ) :
    χv (Units.map (algebraMap (Fv F v) (Ev E v) : Fv F v →* Ev E v) a) =
      χ (Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) (localIdele F v a)) := by
  rw [← H]
  · congr 1
    exact Units.ext (congrArg (· ⊗ₜ[F] (1 : E)) (finSingle_self v _).symm)
  · intro u hu
    change u • (algebraMap (AF F) (AE F E) (localIdele F v a : (AF F)ˣ) - 1) = 0
    rw [← map_one (algebraMap (AF F) (AE F E)), ← map_sub, Algebra.smul_def, ← map_mul]
    refine (congrArg _ (Prod.ext ?_ (af_ext fun t => ?_))).trans (map_zero _)
    · change u.1 * (1 - 1) = 0
      rw [sub_self, mul_zero]
    · change u.2 t * (Neutral.B1.finiteSingle F v a.1 t - 1) = 0
      by_cases e : t = v
      · subst e
        rw [show u.2 t = 0 from hu, zero_mul]
      · rw [finSingle_ne e, sub_self, mul_zero]

theorem resEtaPow_loc (h2 : Module.finrank F E = 2) {χ : Chr F E} {m : ℕ}
    (hχ : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m) {χv : (Ev E v)ˣ →* Circle} (H : IsLocChar χ v χv) :
    ResEtaPow (R := Fv F v) ⊥ χv m := fun a => by
  classical
  have : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  have key : ∀ a : (AF F)ˣ, GlobalTheory.IdeleNormChar.normSign E a = 1 ↔
      a ∈ (Units.map (algebraMap F (AF F)).toMonoidHom).range ⊔
        (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)).range := fun a => by
    rw [GlobalTheory.IdeleNormChar.normSign_eq_one_iff, Subgroup.mem_sup]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨_, ⟨t, rfl⟩, _, ht, mul_div_cancel _ _⟩
    · rintro ⟨_, ⟨t, rfl⟩, z, hz, rfl⟩
      exact ⟨t, (mul_div_cancel_left _ z).symm ▸ hz⟩
  rw [loc_algebraMap H, hχ]
  refine if_congr ?_ rfl rfl
  rw [← key, normSign_localIdele, GlobalTheory.QuadSymbol.eta_eq_one_iff, bot_sup_eq]
  rfl

theorem loc_eq_one (hw : IsInertAt F E v w) {χ : Chr F E} (hu : UnrAt χ w)
    (h1 : ∀ a, χ (Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) a) = 1) {χv : (Ev E v)ˣ →* Circle}
    (H : IsLocChar χ v χv) : χv = 1 := MonoidHom.ext fun y => by
  have h := (under_eq_iff hw w).2 rfl
  have h0 : Valued.v (toCompl h y) ≠ 0 := (Valuation.ne_zero_iff _).2 (y.isUnit.map (toCompl h)).ne_zero
  obtain ⟨x, hx⟩ := v.valuedAdicCompletion_surjective F (Valued.v (toCompl h y))
  have hx0 : x ≠ 0 := (Valuation.ne_zero_iff _).1 (hx ▸ h0)
  set s := Units.map (algebraMap (Fv F v) (Ev E v) : Fv F v →* Ev E v) (Units.mk0 x hx0) with hs
  have e1 : χv s = 1 := (loc_algebraMap H _).trans (h1 _)
  have e2 : Valued.v (toCompl h s) = Valued.v (toCompl h y) := by
    change Valued.v (toCompl h (x ⊗ₜ[F] 1)) = _
    rw [toCompl_tmul, map_one, mul_one, valued_complMap h hx0, isUnram_iff.1 (isUnram_of_isInertAt hw) w h, pow_one, hx]
  have e3 := hu (Units.map (toCompl h).toMonoidHom (y / s)) (by
    unfold Formalism.L2.Host.IsUnitAt
    rw [map_div, Units.val_div_eq_div_val, map_div₀]
    exact (div_eq_one_iff_eq (e2 ▸ h0)).2 e2.symm)
  have e4 : χv (y / s) = 1 := by
    rw [locChar_eq hw h H]
    exact Circle.ext (congrArg Units.val e3)
  rwa [map_div, e1, div_one] at e4

theorem hasAnti_loc {B : Base F E} (hσ : IsCMExt F E σ) (hw : IsInertAt F E v w) {X : Spc F E n} {r s : ℕ}
    (hX : X.IsHerm σ B r s) : HasAnti (cV σ v) (locM X.J v) := by
  have h := (under_eq_iff hw w).2 rfl
  obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw h
  have hd : X.Jᵀ.det ≠ 0 := by rw [Matrix.det_transpose]; exact (Vac.herm_det hX).ne_zero
  have hs : IsSelfDualAt σ X.Jᵀ X.L v := (SelfDual.forall_isSelfDualAt_iff hd hX.lat).2 (fun y => by
    rw [hX.dual]
    refine forall₂_congr fun x _ => ?_
    have : hE σ X.Jᵀ x y = form σ X.J y x := by
      simp only [hE, Formalism.UG.hform, form, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.transpose_apply]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by simp only [RingHom.coe_coe]; ring
    rw [this]
    exact ⟨fun hi => ⟨⟨_, hi⟩, rfl⟩, by rintro ⟨o, ho⟩; rw [← ho]; exact o.isIntegral_coe⟩) v
  obtain ⟨a, -, ha⟩ := exists_frame_antiJ hσ ⟨fun i j => hX.herm j i, hd⟩ hX.lat.fg hX.lat.span_eq_top hw hc hs
  let e := complEquiv hw h
  have inj : ∀ M N : Matrix (Fin n) (Fin n) (Ev E v), M.map (toCompl h) = N.map (toCompl h) → M = N := fun M N H =>
    Matrix.ext fun i j => (toCompl_bijective hw h).1 (congrFun (congrFun H i) j)
  have back : ∀ M : Matrix (Fin n) (Fin n) (w.adicCompletion E), (M.map e.symm).map (toCompl h) = M := fun M =>
    Matrix.ext fun i j => e.apply_symm_apply _
  have one : (1 : Matrix (Fin n) (Fin n) (Ev E v)).map (toCompl h) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨a.1.map e.symm, (a⁻¹).1.map e.symm, inj _ _ ?_, inj _ _ ?_, inj _ _ ?_⟩
  · rw [Matrix.map_mul, back, back, one, Units.mul_inv]
  · rw [Matrix.map_mul, back, back, one, Units.inv_mul]
  · have e1 : ((a.1.map e.symm).map (cV σ v)).map (toCompl h) = a.1.map c :=
      Matrix.ext fun i j => (toCompl_cV hc _).trans (congrArg c (e.apply_symm_apply _))
    have e2 : (locM X.J v).map (toCompl h) = X.J.map (algebraMap E _) := JR_map h
    have e3 : (anti (Ev E v) n).map (toCompl h) = (Formalism.UG.antiJ (w.adicCompletion E) n)ᵀ := by
      ext i j
      simp [anti, Formalism.UG.antiJ, add_comm i.val, apply_ite (toCompl h)]
    rw [Matrix.map_mul, Matrix.map_mul, e1, e2, Matrix.transpose_map, back, e3, ← ha, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.mul_assoc]
    rfl

theorem det_loc {J : Matrix (Fin n) (Fin n) E} (h : IsUnit J.det) : IsUnit (locM (F := F) J v).det :=
  (RingHom.map_det (inclR (F := F) (Fv F v)) J) ▸ h.map _

theorem isHerm_loc {B : Base F E} {X : Spc F E n} {r s : ℕ} (hX : X.IsHerm σ B r s) : IsHerm (cV σ v) (locM X.J v) :=
  ⟨fun i j => congrArg (inclR (F := F) (Fv F v)) (hX.herm i j), det_loc (Vac.herm_det hX)⟩

theorem isSkew_loc {B : Base F E} {X : Spc F E n} {r s : ℕ} (hX : X.IsSkew σ B r s) : IsSkewM (cV σ v) (locM X.J v) :=
  ⟨fun i j => (congrArg (inclR (F := F) (Fv F v)) (hX.skew i j)).trans (map_neg _ _), det_loc (Vac.skew_det hX)⟩

theorem isLagr_loc [Invertible (2 : Fv F v)] {B : Base F E} (hσ : IsCMExt F E σ) (hw : IsInertAt F E v w) {W : Spc F E d} {r s : ℕ}
    (hW : W.IsSkew σ B r s) {m : ℕ} {Cy : Matrix (Fin d) (Fin m) (AE F E)} (hL : IsLagAt σ W v Cy) :
    IsLagr (cV σ v) (locM W.J v) (Cy.map (compFin F E v)) := by
  obtain ⟨ξ, hξ⟩ := isQuad_Ev hσ v
  refine isLagr_of_free (isField_Ev hw) hξ.invol hL.rank (isSkew_loc hW) ?_ fun t ht => ?_
  · have := congrArg (fun M => M.map (compFin F E v)) hL.iso
    simp only [Matrix.map_mul, Matrix.map_zero _ (map_zero _)] at this
    have e1 : (incM F W.J).map (compFin F E v) = locM W.J v := Matrix.ext fun i j => comp_incl (F := F) (v := v) (W.J i j)
    have e2 : (Cy.map (cA σ)).map (compFin F E v) = (Cy.map (compFin F E v)).map (cV σ v) :=
      Matrix.ext fun i j => comp_cA (σ := σ) (v := v) (Cy i j)
    rwa [e1, e2, Matrix.transpose_map] at this
  · let t' : Fin m → AE F E := fun i => ThKH.Iwas.sgE E v (t i)
    have e : compFin F E v ∘ t' = t := funext fun i => ThKH.Iwas.comp_sgE _
    have ht' : At (evFin F v) t' := fun u hu => funext fun i => ThKH.Iwas.at_sgE _ u hu
    have := hL.free t' ht' (funext fun i => ThKH.Iwas.eq_zero_of_at
      (fun u hu => congrFun (ThKH.Iwas.at_mulVec_left hL.supp t' u hu) i) (by
        rw [RingHom.map_mulVec, e, ht]; rfl))
    rw [← e, this]
    exact funext fun i => map_zero _

end PositivityTheory.ThK.PT
