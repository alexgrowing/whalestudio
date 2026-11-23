import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.TensFockInfPhysSub
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.ProjectionCommutesDerivedAction
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CsqDdPt

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

section T

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem tensFock_map_stable {S : Submodule ℂ N} {F : Module.End ℂ N} (hF : ∀ v ∈ S, F v ∈ S)
    {y : TensorProduct ℂ N (Fock n)} (hy : y ∈ tensFock (n := n) S) :
    TensorProduct.map F LinearMap.id y ∈ tensFock S := by
  obtain ⟨x, rfl⟩ := hy
  refine ⟨TensorProduct.map (F.restrict hF) LinearMap.id x, ?_⟩
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
  rfl

theorem tensFock_lTensor_stable {S : Submodule ℂ N} (g : Module.End ℂ (Fock n))
    {y : TensorProduct ℂ N (Fock n)} (hy : y ∈ tensFock (n := n) S) :
    TensorProduct.map LinearMap.id g y ∈ tensFock S := by
  obtain ⟨x, rfl⟩ := hy
  refine ⟨TensorProduct.map LinearMap.id g x, ?_⟩
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
  rfl

theorem dD_tensFock {E : Fin n → Fin n → Module.End ℂ N} {S : Submodule ℂ N}
    (hS : ∀ a b, ∀ v ∈ S, E a b v ∈ S) {y : TensorProduct ℂ N (Fock n)} (hy : y ∈ tensFock (n := n) S) :
    (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) y ∈ tensFock S := by
  simp only [dOp, dOp', LinearMap.add_apply, LinearMap.neg_apply, LinearMap.sum_apply, Module.End.mul_apply]
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun a _ => ?_)
    (Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun a _ => ?_))
  · exact tensFock_map_stable (hS a i) (tensFock_lTensor_stable _ hy)
  · exact tensFock_map_stable (hS i a) (tensFock_lTensor_stable _ hy)

theorem dD_physSub (E : Fin n → Fin n → Module.End ℂ N) {y : TensorProduct ℂ N (Fock n)}
    (hy : y ∈ physicalSubspace (N := N) ε) : (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) y ∈ physicalSubspace ε :=
  Submodule.add_mem _ ((physSub_stable ε E).2.2.1 y hy) ((physSub_stable ε E).2.2.2.1 y hy)

theorem casimir_eT (E : Fin n → Fin n → Module.End ℂ N) :
    casimir (eT (n := n) E) = TensorProduct.map (casimir E) LinearMap.id := by
  apply TensorProduct.ext'
  intro m f
  simp [casimir, eT, LinearMap.sum_apply, TensorProduct.sum_tmul]

theorem gradT_D (E : Fin n → Fin n → Module.End ℂ N) (y : TensorProduct ℂ N (Fock n)) :
    gradT ((dOp ε (eT E) cpT + dOp' ε (eT E) cmT) y) = -(dOp ε (eT E) cpT + dOp' ε (eT E) cmT) (gradT y) := by
  have h1 := LinearMap.congr_fun (gradT_props ε E).2.1 y
  have h2 := LinearMap.congr_fun (gradT_props ε E).2.2 y
  simp only [Module.End.mul_apply, LinearMap.neg_apply] at h1 h2
  rw [LinearMap.add_apply, map_add, h1, h2, LinearMap.add_apply, neg_add]

end T

section Y

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

def Y0 (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ N) (V : Submodule ℂ N) (J : ℕ) :
    Submodule ℂ (TensorProduct ℂ N (Fock n)) :=
  tensFock (layer ε E V J) ⊓ physicalSubspace ε

def YY (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ N) (V : Submodule ℂ N) (J : ℕ) :
    Submodule ℂ (TensorProduct ℂ N (Fock n)) :=
  Y0 ε E V J ⊔ (Y0 ε E V J).map (dOp ε (eT E) cpT + dOp' ε (eT E) cmT)

variable {E : Fin n → Fin n → Module.End ℂ N} {V : Submodule ℂ N}

theorem map_eq_smul_of_tensFock {S : Submodule ℂ N} {F : Module.End ℂ N} {c : ℂ} (hF : ∀ v ∈ S, F v = c • v)
    {y : TensorProduct ℂ N (Fock n)} (hy : y ∈ tensFock (n := n) S) :
    TensorProduct.map F LinearMap.id y = c • y := by
  obtain ⟨x, rfl⟩ := hy
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m f =>
    simp only [TensorProduct.map_tmul, Submodule.coe_subtype, LinearMap.id_apply, hF m m.2,
      TensorProduct.smul_tmul']
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', smul_add]

theorem layer_le_generated_tensorFock (J : ℕ) : Y0 ε E V J ≤ tensFock (n := n) (genSub E V) ⊓ physicalSubspace ε :=
  inf_le_inf_right _ (tensorFock_mono (layer_le_genSub J))

theorem YY_le_genSub (J : ℕ) : YY ε E V J ≤ tensFock (n := n) (genSub E V) ⊓ physicalSubspace ε := by
  refine sup_le (layer_le_generated_tensorFock J) ?_
  rintro _ ⟨y, hy, rfl⟩
  have hy' := layer_le_generated_tensorFock J hy
  exact ⟨dD_tensFock (fun a b v hv => generatedSub_stable E V a b hv) hy'.1, dD_physSub E hy'.2⟩

theorem diracSquare_mem_layer (hE : IsGlRep E) (hVk : IsKStableSub ε E V) {c : ℂ} (hc : ∀ v ∈ genSub E V, casimir E v = c • v)
    (J : ℕ) {y : TensorProduct ℂ N (Fock n)} (hy : y ∈ Y0 ε E V J) :
    (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) ((dOp ε (eT E) cpT + dOp' ε (eT E) cmT) y) ∈ Y0 ε E V J := by
  have hL := layer_kStable hE hVk J
  have hA : ∀ a b, ε a = ε b → ∀ x ∈ Y0 ε E V J, diagE ε (eT E) cpT cmT a b x ∈ Y0 ε E V J :=
    fun a b hab x hx => ⟨tensorFock_diagAction_stable ε hL hab hx.1, (physSub_stable ε E).2.1 a b x hx.2⟩
  have h2 := LinearMap.congr_fun (two_D_sq (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) ε) y
  rw [LinearMap.smul_apply, Module.End.mul_apply] at h2
  have hcas : casimir (eT (n := n) E) y = c • y := by
    rw [casimir_eT]
    exact map_eq_smul_of_tensFock (fun v hv => hc v (layer_le_genSub J hv)) hy.1
  have hmem : (2 : ℂ) • (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) ((dOp ε (eT E) cpT + dOp' ε (eT E) cmT) y) ∈
      Y0 ε E V J := by
    rw [h2]
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
      LinearMap.sum_apply]
    rw [hcas]
    refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.neg_mem _ (Submodule.smul_mem _ _ hy)) ?_)
      (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hA a a rfl y hy)))
    simp only [casimirK, LinearMap.sum_apply, Module.End.mul_apply]
    exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b hb =>
      hA a b (Finset.mem_filter.1 hb).2.symm _ (hA b a (Finset.mem_filter.1 hb).2 y hy)
  have := Submodule.smul_mem _ (1 / 2 : ℂ) hmem
  rwa [smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul] at this

theorem YY_D (hE : IsGlRep E) (hVk : IsKStableSub ε E V) {c : ℂ} (hc : ∀ v ∈ genSub E V, casimir E v = c • v)
    (J : ℕ) {y : TensorProduct ℂ N (Fock n)} (hy : y ∈ YY ε E V J) :
    (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) y ∈ YY ε E V J := by
  obtain ⟨y0, hy0, y1, ⟨x, hx, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
  rw [map_add]
  exact Submodule.add_mem _ (Submodule.mem_sup_right ⟨y0, hy0, rfl⟩)
    (Submodule.mem_sup_left (diracSquare_mem_layer hE hVk hc J hx))

theorem YY_gradT (J : ℕ) {y : TensorProduct ℂ N (Fock n)} (hy : y ∈ YY ε E V J) : gradT y ∈ YY ε E V J := by
  obtain ⟨y0, hy0, y1, ⟨x, hx, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
  have hG : ∀ z ∈ Y0 ε E V J, gradT z ∈ Y0 ε E V J := fun z hz =>
    ⟨tensFock_lTensor_stable _ hz.1, (physSub_stable ε E).2.2.2.2 z hz.2⟩
  rw [map_add, gradT_D]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (hG y0 hy0))
    (Submodule.mem_sup_right ⟨-gradT x, Submodule.neg_mem _ (hG x hx), by rw [map_neg]⟩)

theorem YY_fd (hVf : FiniteDimensional ℂ V) (J : ℕ) : FiniteDimensional ℂ (YY ε E V J) := by
  have h1 : FiniteDimensional ℂ (tensFock (n := n) (layer ε E V J)) :=
    tensorFock_finiteDimensional (finiteDimensional_layer hVf J)
  have h2 : FiniteDimensional ℂ (Y0 ε E V J) := Submodule.finiteDimensional_of_le inf_le_left
  unfold YY
  infer_instance

end Y

section W

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
  {V : Submodule ℂ D}

theorem sigD_layer (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hVs : IsKStableSub ε E V)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (J : ℕ) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) {x : D} (hx : x ∈ layer ε E V J) : sigD hD hk x ∈ layer ε E V J := by
  obtain ⟨y, hy, hyx⟩ := layer_k_stable hσ hD hVs hVK J k hk x hx
  have : sigD hD hk x = y := Subtype.ext hyx.symm
  rw [this]
  exact hy

theorem wK_tensFock (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    {S : Submodule ℂ D} (hS : ∀ x ∈ S, sigD hD hk x ∈ S) {y : TensorProduct ℂ D (Fock n)}
    (hy : y ∈ tensFock (n := n) S) : wK hD hk y ∈ tensFock S := by
  obtain ⟨x, rfl⟩ := hy
  refine ⟨TensorProduct.map ((sigD hD hk).restrict hS) (ff ε k).toLinearMap x, ?_⟩
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
  show _ = (TensorProduct.map (sigD hD hk) (ff ε k).toLinearMap ∘ₗ
    TensorProduct.map S.subtype LinearMap.id) x
  rw [← TensorProduct.map_comp]
  rfl

theorem wK_D (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) (x : TensorProduct ℂ D (Fock n)) :
    wK hD hk ((dOp ε (eT E) cpT + dOp' ε (eT E) cmT) x) =
      (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) (wK hD hk x) := by
  have h1 := LinearMap.congr_fun (wK_dOp hσ hD hk) x
  have h2 := LinearMap.congr_fun (wK_dOp' hσ hD hk) x
  simp only [Module.End.mul_apply] at h1 h2
  rw [LinearMap.add_apply, map_add, h1, h2, LinearMap.add_apply]

theorem compactAction_mem_layer (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hVs : IsKStableSub ε E V)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (J : ℕ) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) {y : TensorProduct ℂ D (Fock n)} (hy : y ∈ Y0 ε E V J) : wK hD hk y ∈ Y0 ε E V J :=
  ⟨wK_tensFock hD hk (fun x hx => sigD_layer hσ hD hVs hVK J hk hx) hy.1, wK_physSub hD hk hy.2⟩

theorem YY_wK (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hVs : IsKStableSub ε E V)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (J : ℕ) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) {y : TensorProduct ℂ D (Fock n)} (hy : y ∈ YY ε E V J) : wK hD hk y ∈ YY ε E V J := by
  obtain ⟨y0, hy0, y1, ⟨x, hx, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
  rw [map_add, wK_D hσ hD hk]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (compactAction_mem_layer hσ hD hVs hVK J hk hy0))
    (Submodule.mem_sup_right ⟨_, compactAction_mem_layer hσ hD hVs hVK J hk hx, rfl⟩)

set_option maxHeartbeats 1000000 in

theorem str_YY (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hVs : IsKStableSub ε E V)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {c : ℂ}
    (hc : ∀ v ∈ genSub E V, casimir E v = c • v) (J : ℕ) [FiniteDimensional ℂ (YY ε E V J)]
    (hKK : LinearMap.ker (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) ⊓ tensFock (genSub E V) ⊓ physicalSubspace ε ≤
      Y0 ε E V J)
    (hgr : ∀ y ∈ LinearMap.ker (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) ⊓ tensFock (genSub E V) ⊓ physicalSubspace ε,
      gradT y = ((-1 : ℂ) ^ sDeg ε) • y)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    LinearMap.trace ℂ (YY ε E V J) ((gradT ∘ₗ wK hD hk).restrict
        (fun y hy => YY_gradT J (YY_wK hσ hD hVs hVK J hk hy))) =
      ((-1 : ℂ) ^ sDeg ε) * LinearMap.trace ℂ
        (LinearMap.ker (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) ⊓ tensFock (genSub E V) ⊓ physicalSubspace ε :
          Submodule ℂ (TensorProduct ℂ D (Fock n))) ((wK hD hk).restrict (wK_KK hσ hD hVK k hk)) := by
  classical
  set Y := YY ε E V J
  set Dop := dOp ε (eT E) cpT + dOp' ε (eT E) cmT
  have hU : IsInfUnitary ε E := isInfUnitary_of_isDerivedOn hσ hD
  have hE : IsGlRep E := hD.glRep
  let Dl : TSub Y →ₗ[ℂ] TSub Y := Dop.restrict (fun y hy => YY_D hE hVs hc J hy)
  let Γ : TSub Y →ₗ[ℂ] TSub Y := gradT.restrict (fun y hy => YY_gradT J hy)
  let B : TSub Y →ₗ[ℂ] TSub Y := (wK hD hk).restrict (fun y hy => YY_wK hσ hD hVs hVK J hk hy)
  obtain ⟨hker, htr⟩ := str_eq_str_ker Dl Γ B
    (fun x y => by rw [tsub_inner, tsub_inner]; exact tform_D hU _ _)
    (fun x => Subtype.ext (gradT_D E _)) (fun x => Subtype.ext (wK_D hσ hD hk _))
  have h1 : LinearMap.trace ℂ Y ((gradT ∘ₗ wK hD hk).restrict
      (fun y hy => YY_gradT J (YY_wK hσ hD hVs hVK J hk hy))) = LinearMap.trace ℂ (TSub Y) (Γ ∘ₗ B) := rfl
  rw [h1, htr]
  set KK : Submodule ℂ (TensorProduct ℂ D (Fock n)) :=
    LinearMap.ker Dop ⊓ tensFock (genSub E V) ⊓ physicalSubspace ε with hKKdef
  have hmemKK : ∀ x : LinearMap.ker Dl, tsubVal Y (x : TSub Y) ∈ KK := by
    intro x
    have hx : Dl (x : TSub Y) = 0 := x.2
    have hYle := YY_le_genSub (ε := ε) (E := E) (V := V) J (tsubVal_mem (x : TSub Y))
    refine ⟨⟨?_, hYle.1⟩, hYle.2⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact congrArg (tsubVal Y) hx
  let f : LinearMap.ker Dl →ₗ[ℂ] KK :=
    { toFun := fun x => ⟨tsubVal Y (x : TSub Y), hmemKK x⟩
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have := congrArg Subtype.val hxy
      exact Subtype.ext (tsubVal_injective this)
    · intro y
      have hyY : (y : TensorProduct ℂ D (Fock n)) ∈ Y := Submodule.mem_sup_left (hKK y.2)
      let x : TSub Y := (⟨y, hyY⟩ : Y)
      have hx : x ∈ LinearMap.ker Dl := by
        rw [LinearMap.mem_ker]
        apply tsubVal_injective
        rw [map_zero]
        exact y.2.1.1
      exact ⟨⟨x, hx⟩, rfl⟩
  let e := LinearEquiv.ofBijective f hf
  rw [← LinearMap.trace_conj' _ e]
  set h := ((-1 : ℂ) ^ sDeg ε) • (wK hD hk).restrict (wK_KK hσ hD hVK k hk) with hhdef
  have hcomm : ∀ x : LinearMap.ker Dl, h (f x) = f ((Γ ∘ₗ B).restrict hker x) := by
    intro x
    have hx1 : ((h (f x) : KK) : TensorProduct ℂ D (Fock n)) =
        ((-1 : ℂ) ^ sDeg ε) • wK hD hk (tsubVal Y (x : TSub Y)) := by
      rw [hhdef, LinearMap.smul_apply, Submodule.coe_smul, LinearMap.restrict_coe_apply]
      rfl
    have hx2 : ((f ((Γ ∘ₗ B).restrict hker x) : KK) : TensorProduct ℂ D (Fock n)) =
        gradT (wK hD hk (tsubVal Y (x : TSub Y))) := rfl
    apply Subtype.ext
    rw [hx1, hx2, hgr _ (wK_KK hσ hD hVK k hk _ (hmemKK x))]
  have hc' : e.conj ((Γ ∘ₗ B).restrict hker) = h := by
    apply LinearMap.ext
    intro y
    rw [LinearEquiv.conj_apply_apply]
    calc e ((Γ ∘ₗ B).restrict hker (e.symm y)) = h (e (e.symm y)) := (hcomm _).symm
      _ = h y := by rw [LinearEquiv.apply_symm_apply]
  rw [hc', map_smul, smul_eq_mul]

end W

end ReciprocityTheory.ChartRestriction.DS.TRGap
