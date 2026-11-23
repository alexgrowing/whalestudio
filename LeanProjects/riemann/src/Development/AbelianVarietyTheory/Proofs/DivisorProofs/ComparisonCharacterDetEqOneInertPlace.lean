import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterFinitePlaceComponentEqOfInert
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertDetChr

open GlobalTheory.LFun GlobalTheory.Doubling

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_det_sub_one {n : ℕ} (v : Pl F) (t : GL (Fin n) (AE F E))
    (ht : At (evFin F v) ((t : Matrix (Fin n) (Fin n) (AE F E)) - 1)) :
    At (evFin F v) (((Matrix.GeneralLinearGroup.det t : (AE F E)ˣ) : AE F E) - 1) := by
  intro u hu
  have h := ht u hu
  set c := algebraMap (AF F) (AE F E) u with hc
  let I : Ideal (AE F E) := (Submodule.span (AE F E) {c}).annihilator
  have hmem : ∀ x : AE F E, x ∈ I ↔ c * x = 0 := fun x => by
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul, mul_comm]
  have hent : ∀ i j, (t : Matrix (Fin n) (Fin n) (AE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AE F E)) i j ∈ I :=
    fun i j => by
      rw [hmem]
      have := congrFun (congrFun h i) j
      simpa [Matrix.sub_apply, Algebra.smul_def, hc] using this
  have hq : (Ideal.Quotient.mk I).mapMatrix (t : Matrix (Fin n) (Fin n) (AE F E)) =
      (Ideal.Quotient.mk I).mapMatrix (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    ext i j
    exact Ideal.Quotient.eq.2 (hent i j)
  have hd := congrArg Matrix.det hq
  rw [← RingHom.map_det, ← RingHom.map_det, Matrix.det_one] at hd
  have := (hmem _).1 (Ideal.Quotient.eq.1 hd)
  rw [Algebra.smul_def, Matrix.GeneralLinearGroup.val_det_apply]
  exact this

theorem compFin_algebraMap (u : Pl F) (a : AF F) :
    compFin F E u (algebraMap (AF F) (AE F E) a) = algebraMap (Fv F u) (Fv F u ⊗[F] E) (evFin F u a) := by
  simp [compFin, Algebra.TensorProduct.algebraMap_apply]

theorem compInf_algebraMap (w : InfinitePlace F) (a : AF F) :
    compInf F E w (algebraMap (AF F) (AE F E) a) = algebraMap w.Completion (w.Completion ⊗[F] E) (evInf F w a) := by
  simp [compInf, Algebra.TensorProduct.algebraMap_apply]

theorem evFin_inFin_self (v : Pl F) (x : Fv F v) : evFin F v (inFin v x) = x :=
  evalV_singleFin_self v x

theorem evFin_inFin_ne {u v : Pl F} (h : u ≠ v) (x : Fv F v) : evFin F u (inFin v x) = 0 :=
  evalV_singleFin_ne h x

theorem evInf_inFin (w : InfinitePlace F) (v : Pl F) (x : Fv F v) : evInf F w (inFin v x) = 0 := by
  show GlobalTheory.AutFunCompare.evW w 0 = 0
  exact map_zero _

theorem at_inFin_one (v : Pl F) : At (evFin F v) (inFin v (1 : Fv F v)) := by
  intro u hu
  rw [smul_eq_mul]
  refine Prod.ext (mul_zero _) (af_ext fun u' => ?_)
  show evalV F u' (u.2 * singleFin v 1) = evalV F u' 0
  rw [map_mul, map_zero]
  by_cases e : u' = v
  · subst e
    exact mul_eq_zero_of_left hu _
  · rw [evalV_singleFin_ne e, mul_zero]

theorem eq_ideleAt {v : Pl F} {z : (AE F E)ˣ} (hz : At (evFin F v) ((z : AE F E) - 1)) :
    z = ideleAt F E v (unitFin F E v z) := by
  set e : AF F := inFin v 1
  have key := hz (1 - e) (by rw [map_sub, map_one, evFin_inFin_self, sub_self])
  rw [Algebra.smul_def] at key
  refine idele_ext (fun w => ?_) (fun u => ?_)
  · rw [unitInf_ideleAt]
    refine Units.ext ?_
    have := congrArg (compInf F E w) key
    rw [map_mul, compInf_algebraMap, map_sub, map_one, evInf_inFin, sub_zero, map_one, one_mul, map_zero, map_sub,
      map_one, sub_eq_zero] at this
    exact this
  · by_cases huv : u = v
    · subst huv
      rw [unitFin_ideleAt_self]
    · rw [unitFin_ideleAt_ne huv]
      refine Units.ext ?_
      have := congrArg (compFin F E u) key
      rw [map_mul, compFin_algebraMap, map_sub, map_one, evFin_inFin_ne huv, sub_zero, map_one, one_mul, map_zero,
        map_sub, map_one, sub_eq_zero] at this
      exact this

section Lat

variable {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v)

def piW' : AE F E →+* w.adicCompletion E := (toCompl h).comp (compFin F E v)

theorem piW'_algebraMap (a : AF F) : piW' h (algebraMap (AF F) (AE F E) a) = complMap h (evFin F v a) := by
  rw [piW', RingHom.comp_apply, compFin_algebraMap, Algebra.TensorProduct.algebraMap_apply, toCompl_tmul]
  simp

theorem piW'_inclR (y : E) : piW' h (inclR (F := F) (AF F) y) = algebraMap E _ y := by
  rw [piW', RingHom.comp_apply]
  have : compFin F E v (inclR (F := F) (AF F) y) = (1 : Fv F v) ⊗ₜ[F] y := by
    show Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] y) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]; rfl
  rw [this, toCompl_tmul, map_one, one_mul]

theorem comp_mem_latAt {d : ℕ} (W : Spc F E d) {z : Fin d → AE F E} (hz : z ∈ GlobalTheory.InertSph.latAt W v) :
    piW' h ∘ z ∈ latAt w W.L := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, ha, y, hy, rfl⟩ := hz
    have e : piW' h ∘ (a • fun i => inclR (F := F) (AF F) (y i)) =
        (⟨complMap h (evFin F v a), complMap_mem h ha⟩ : Formalism.UG.Ov E w) •
          (fun i => algebraMap E (w.adicCompletion E) (y i)) := by
      funext i
      show piW' h (a • inclR (F := F) (AF F) (y i)) = _
      rw [Algebra.smul_def, map_mul, piW'_algebraMap, piW'_inclR]
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, hy, rfl⟩)
  | zero =>
    convert zero_mem (latAt w W.L) using 1
    funext i; exact map_zero _
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    funext i; exact map_add _ _ _
  | neg x _ hx =>
    convert neg_mem hx using 1
    funext i; exact map_neg _ _

theorem lift_mem_latAt {d : ℕ} (W : Spc F E d) {y : Fin d → E} (hy : y ∈ W.L) :
    (inFin v (1 : Fv F v) • fun i => inclR (F := F) (AF F) (y i)) ∈ GlobalTheory.InertSph.latAt W v ∧
      piW' h ∘ (inFin v (1 : Fv F v) • fun i => inclR (F := F) (AF F) (y i)) =
        fun i => algebraMap E (w.adicCompletion E) (y i) := by
  refine ⟨AddSubgroup.subset_closure ⟨_, at_inFin_one v, ?_, y, hy, rfl⟩, ?_⟩
  · rw [evFin_inFin_self]; exact one_mem _
  · funext i
    show piW' h (inFin v (1 : Fv F v) • inclR (F := F) (AF F) (y i)) = _
    rw [Algebra.smul_def, map_mul, piW'_algebraMap, piW'_inclR, evFin_inFin_self, map_one, one_mul]

theorem mulVec_mem_latAt {d : ℕ} (W : Spc F E d) (g : Matrix (Fin d) (Fin d) (AE F E))
    (hg : ∀ z ∈ GlobalTheory.InertSph.latAt W v, g *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    ∀ z ∈ latAt w W.L, (piW' h).mapMatrix g *ᵥ z ∈ latAt w W.L := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨h1, h2⟩ := lift_mem_latAt h W hy
    show (piW' h).mapMatrix g *ᵥ (fun i => algebraMap E (w.adicCompletion E) (y i)) ∈ _
    rw [← h2]
    have e : (piW' h).mapMatrix g *ᵥ (piW' h ∘ (inFin v (1 : Fv F v) • fun i => inclR (F := F) (AF F) (y i))) =
        piW' h ∘ (g *ᵥ (inFin v (1 : Fv F v) • fun i => inclR (F := F) (AF F) (y i))) :=
      funext fun i => (RingHom.map_mulVec (piW' h) g _ i).symm
    rw [e]
    exact comp_mem_latAt h W (hg _ h1)
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have e : (piW' h).mapMatrix g *ᵥ (c • x) = c • ((piW' h).mapMatrix g *ᵥ x) := by
      funext i
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, Subring.smul_def, mul_left_comm]
    rw [e]
    exact Submodule.smul_mem _ _ hx

theorem valued_eq_one_of_isUnit {c : Formalism.UG.Ov E w} (hc : IsUnit c) : Valued.v (c : w.adicCompletion E) = 1 := by
  obtain ⟨c', hc'⟩ := hc.exists_right_inv
  have h1 : Valued.v (c : w.adicCompletion E) ≤ 1 := c.2
  have h2 : Valued.v (c' : w.adicCompletion E) ≤ 1 := c'.2
  have h3 : Valued.v (c : w.adicCompletion E) * Valued.v (c' : w.adicCompletion E) = 1 := by
    rw [← map_mul, ← Subring.coe_mul, hc']; simp
  refine le_antisymm h1 ?_
  calc (1 : _) = _ := h3.symm
    _ ≤ Valued.v (c : w.adicCompletion E) := mul_le_of_le_one_right' h2

theorem valued_det_eq_one (hw : Formalism.UG.IsInertAt F E v w) {d : ℕ} (W : Spc F E d) (hL : W.L.IsLattice E)
    (t : GL (Fin d) (AE F E))
    (ht : ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
      ((t⁻¹ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    Valued.v (piW' h (t : Matrix (Fin d) (Fin d) (AE F E)).det) = 1 := by
  set T : GL (Fin d) (w.adicCompletion E) := Formalism.UG.bc (piW' h) t with hT
  have hT1 : (T : Matrix (Fin d) (Fin d) (w.adicCompletion E)) = (piW' h).mapMatrix (t : Matrix _ _ _) := rfl
  have hT2 : ((T⁻¹ : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)) =
      (piW' h).mapMatrix ((t⁻¹ : GL (Fin d) (AE F E)) : Matrix _ _ _) := by
    rw [hT, ← map_inv]; rfl
  have hstab : ∀ z, z ∈ latAt w W.L ↔ (T : Matrix _ _ _) *ᵥ z ∈ latAt w W.L := fun z => by
    refine ⟨fun hz => hT1 ▸ mulVec_mem_latAt h W _ (fun z hz => (ht z hz).1) z hz, fun hz => ?_⟩
    have := mulVec_mem_latAt h W _ (fun z hz => (ht z hz).2) _ hz
    rwa [← hT2, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
  obtain ⟨a, ha⟩ := InertChart.exists_isFrameAt hw hL.fg hL.span_eq_top
  obtain ⟨m, hm⟩ := ((InertChart.isFrameAt_mul ha (one_mem _)).2 T).1 hstab
  have hdet : Matrix.GeneralLinearGroup.det (a⁻¹ * T * a) = Matrix.GeneralLinearGroup.det T := by
    rw [map_mul, map_mul, map_inv, mul_comm _ (Matrix.GeneralLinearGroup.det a), ← mul_assoc, mul_inv_cancel, one_mul]
  have e2 : (piW' h (t : Matrix (Fin d) (Fin d) (AE F E)).det) =
      ((Matrix.GeneralLinearGroup.det T : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hT1, RingHom.map_det]
  rw [e2, ← hdet, ← hm, Matrix.GeneralLinearGroup.val_det_apply]
  have e3 : ((Formalism.UG.bc (Formalism.UG.Ov E w).subtype m : GL (Fin d) (w.adicCompletion E)) :
      Matrix (Fin d) (Fin d) (w.adicCompletion E)).det = ((m.val.det : Formalism.UG.Ov E w) : w.adicCompletion E) := by
    show ((Formalism.UG.Ov E w).subtype.mapMatrix m.val).det = _
    rw [← RingHom.map_det]; rfl
  rw [e3]
  exact valued_eq_one_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit m))

end Lat

end GlobalTheory.InertDetChr

theorem GlobalTheory.InertDetChr.alpha_det_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ t : GL (Fin (a + a')) (AE F E), (At (evFin F v) ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v ∧
        ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      X.α (Matrix.GeneralLinearGroup.det t) = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hw hvT t ht
  obtain ⟨ht1, ht2⟩ := ht
  have h : w.under (𝓞 F) = v := (GlobalTheory.LFun.InertChart.under_eq_iff hw w).2 rfl
  have e1 := GlobalTheory.InertDetChr.eq_ideleAt (GlobalTheory.InertDetChr.at_det_sub_one v t ht1)
  rw [e1, GlobalTheory.LFun.ideleAt_eq_locIdele_of_isInertAt h hw]
  have hunr : GlobalTheory.LFun.UnrAt X.α w := hTr.chars.unrα w (by
    show ¬ (w.under (𝓞 F) ∈ (X.T : Set (Pl F)))
    rw [h]; exact_mod_cast hvT)
  have hv1 := GlobalTheory.InertDetChr.valued_det_eq_one h hw G.W hTr.geo.hW.lat t ht2
  set y : (w.adicCompletion E)ˣ :=
    Units.map (toCompl h).toMonoidHom (GlobalTheory.Doubling.unitFin F E v (Matrix.GeneralLinearGroup.det t)) with hy
  have hyv : (y : w.adicCompletion E) =
      GlobalTheory.InertDetChr.piW' h ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)).det) := by
    rw [hy, Units.coe_map, GlobalTheory.InertDetChr.piW', RingHom.comp_apply, ← Matrix.GeneralLinearGroup.val_det_apply]
    rfl
  have hu : Formalism.L2.Host.IsUnitAt w y := by
    unfold Formalism.L2.Host.IsUnitAt
    rw [hyv]; exact hv1
  have hu2 := hunr y hu
  have hu' : ((Circle.toUnits (X.α (GlobalTheory.LFun.locIdele F w y)) : ℂˣ) : ℂ) = 1 := congrArg Units.val hu2
  rw [Circle.toUnits_apply, Units.val_mk0] at hu'
  exact Circle.ext (by simpa using hu')
