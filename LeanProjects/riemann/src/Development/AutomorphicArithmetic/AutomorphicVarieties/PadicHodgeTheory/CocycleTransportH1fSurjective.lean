import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OpenField
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

noncomputable section

namespace UpperTheory.V.Loc.BlochKatoDimension

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] {K : FinExt l} (e : G ≃* ↥(GK K))
  {E : Type} [Field E] [Algebra ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] E V] (ρ : Representation E G V)

private def tr : Representation ℚ_[l] ↥(GK K) V := (resCoef ℚ_[l] ρ).comp e.symm.toMonoidHom

private theorem tr_apply (g : G) (v : V) : tr e ρ (e g) v = ρ g v := by
  simp [tr, resCoef]

private theorem actVB_tr (g : G) (x : V ⊗[ℚ_[l]] Bcr l) :
    actVB ((PP l).PD K) (tr e ρ) (e g) x = actC ((GK K).subtype.comp e.toMonoidHom) ρ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, actC, tr_apply, (PP l).PD_actB]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem actVdR_tr (g : G) (x : V ⊗[ℚ_[l]] Bdr l) :
    actVdR ((PP l).PD K) (tr e ρ) (e g) x = actD ((GK K).subtype.comp e.toMonoidHom) ρ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVdR, actD, tr_apply, (PP l).PD_actdR]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem actD_res (φ : G →* GQ l) (g : G) (x : V ⊗[ℚ_[l]] Bdr l) :
    actD φ (resCoef ℚ_[l] ρ) g x = actD φ ρ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actD, resCoef]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem Ddr_res (φ : G →* GQ l) :
    Ddr φ (resCoef ℚ_[l] ρ) = (Ddr φ ρ).restrictScalars ℚ_[l] := by
  ext x
  simp [Ddr, sub_eq_zero, actD_res]

private theorem DdR_tr :
    DdR ((PP l).PD K) (tr e ρ) = (Ddr ((GK K).subtype.comp e.toMonoidHom) ρ).restrictScalars ℚ_[l] := by
  ext x
  simp only [DdR, Ddr, Submodule.restrictScalars_mem, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply]
  rw [e.surjective.forall]
  simp only [actVdR_tr]

private theorem h0V_tr_eq_restrictScalars_h0 : H0V (tr e ρ) = (H0 ρ).restrictScalars ℚ_[l] := by
  ext x
  simp only [H0V, Submodule.restrictScalars_mem, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, H0, Representation.mem_invariants]
  rw [e.surjective.forall]
  simp only [tr_apply]

variable (K E V) in
private theorem FilV_eq (a : ℤ) :
    FilV ((PP l).PD K) (LL := ℚ_[l]) (V := V) a = (FilT (l := l) E V a).restrictScalars ℚ_[l] := by
  have hF : (((PP l).PD K).Fil a).restrictScalars ℚ_[l] =
      (((PP l).PD (botExt l)).Fil a).restrictScalars ℚ_[l] :=
    SetLike.coe_injective ((PP l).PD_Fil K (botExt l) a)
  have h : ∀ (N : Submodule ℚ_[l] (Bdr l)) y, AlgebraTensorModule.map (LinearMap.id : V →ₗ[ℚ_[l]] V)
      N.subtype y = AlgebraTensorModule.map (LinearMap.id : V →ₗ[E] V) N.subtype y := by
    intro N y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  ext x
  rw [FilV, hF]
  simp only [FilT, Submodule.restrictScalars_mem, LinearMap.mem_range, h]

variable [TopologicalSpace G] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V]
  [ContinuousConstSMul ℚ_[l] V]

private theorem mem_Z1f_transport_iff (he : Continuous e) (he' : Continuous e.symm) (c : ↥(GK K) → V) :
    c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles ((PP l).PD K) (tr e ρ) ↔
      (c ∘ e) ∈ UpperTheory.V.Loc.finiteCocycles ((GK K).subtype.comp e.toMonoidHom) ρ := by
  show ((Continuous c ∧ ∀ g h, c (g * h) = c g + tr e ρ g (c h)) ∧
      ∃ x, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bcr l) = actVB ((PP l).PD K) (tr e ρ) g x - x) ↔
    ((Continuous (c ∘ e) ∧ ∀ g h, c (e (g * h)) = c (e g) + ρ g (c (e h))) ∧
      ∃ x, ∀ g, c (e g) ⊗ₜ[ℚ_[l]] (1 : Bcr l) = actC ((GK K).subtype.comp e.toMonoidHom) ρ g x - x)
  refine and_congr (and_congr ⟨fun h => h.comp he, fun h => ?_⟩ ?_) (exists_congr fun x => ?_)
  · have := h.comp he'
    convert this using 1
    funext g
    simp
  · rw [e.surjective.forall₂]
    simp only [tr_apply, map_mul]
  · rw [e.surjective.forall]
    simp only [actVB_tr]

private def cocycleTransportToH1f (he : Continuous e) (he' : Continuous e.symm) :
    ↥(Formalism.WeaklyAdmissibleFiltrations.finiteCocycles ((PP l).PD K) (tr e ρ)) →ₗ[ℚ_[l]] ↥(finiteCohomology ((GK K).subtype.comp e.toMonoidHom) ρ) where
  toFun c := ⟨Submodule.Quotient.mk ⟨c.1 ∘ e, ((mem_Z1f_transport_iff e ρ he he' c.1).mp c.2).1⟩,
    ⟨_, (mem_Z1f_transport_iff e ρ he he' c.1).mp c.2, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem cocycle_transport_H1f_surjective (he : Continuous e) (he' : Continuous e.symm) :
    Function.Surjective (cocycleTransportToH1f e ρ he he') := by
  rintro ⟨_, c, hc, rfl⟩
  have h : (c.1 ∘ e.symm) ∘ e = c.1 := by
    funext g
    simp
  refine ⟨⟨c.1 ∘ e.symm, (mem_Z1f_transport_iff e ρ he he' _).mpr (by rw [h]; exact hc)⟩, Subtype.ext ?_⟩
  exact congrArg Submodule.Quotient.mk (Subtype.ext h)

private theorem ker_cocycle_transport_H1f (he : Continuous e) (he' : Continuous e.symm) :
    LinearMap.ker (cocycleTransportToH1f e ρ he he') =
      (Formalism.WeaklyAdmissibleFiltrations.B1 (tr e ρ)).comap (Formalism.WeaklyAdmissibleFiltrations.finiteCocycles ((PP l).PD K) (tr e ρ)).subtype := by
  ext c
  rw [LinearMap.mem_ker, Subtype.ext_iff]
  refine (Submodule.Quotient.mk_eq_zero _).trans ?_
  refine (mem_coboundaries1 ρ (c.1 ∘ e)).trans ?_
  refine exists_congr fun m => ?_
  show (∀ g, c.1 (e g) = ρ g m - m) ↔ (fun g => tr e ρ g m - m) = c.1
  rw [funext_iff, e.surjective.forall]
  simp only [tr_apply]
  exact forall_congr' fun g => eq_comm

private def h1fEquiv (he : Continuous e) (he' : Continuous e.symm) :
    FiniteCohomology ((PP l).PD K) (tr e ρ) ≃ₗ[ℚ_[l]] ↥(finiteCohomology ((GK K).subtype.comp e.toMonoidHom) ρ) :=
  (Submodule.quotEquivOfEq _ _ (ker_cocycle_transport_H1f e ρ he he').symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (cocycle_transport_H1f_surjective e ρ he he'))

end UpperTheory.V.Loc.BlochKatoDimension

open UpperTheory.V.Loc.BlochKatoDimension in
theorem UpperTheory.V.Loc.bkDim :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρ : Representation E G V), ContAction ρ → IsDr φ ρ → Module.Finite E ↥(finiteCohomology φ ρ) ∧ finrank E ↥(finiteCohomology φ ρ) + finrank E ↥(FilD φ ρ 0) = finrank E ↥(H0 ρ) + φ.range.index * finrank E V := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ V _ _ _ _ _ _ _ _ _ ρ hc hdR
  obtain ⟨K, e, he, he', hφe, -, hind, -⟩ := openField φ hφ
  obtain ⟨T⟩ := tiedP l
  rw [IsDr, hind, Ddr_res] at hdR
  rw [hind]
  clear hind hφ
  subst hφe
  have hD := (hP.bk l (PP l) (AIP l) T K).1
  have hcont : ∀ x, Continuous fun g => tr e ρ g x := fun x =>
    hc.comp (he'.prodMk continuous_const)
  have hdR' : IsDR ((PP l).PD K) (tr e ρ) := by
    rw [IsDR, DdR_tr]
    exact hdR
  obtain ⟨hfin, hdim⟩ := hD V (tr e ρ) hcont hdR'
  haveI : Module.Finite ℚ_[l] ↥(finiteCohomology ((GK K).subtype.comp e.toMonoidHom) ρ) :=
    Module.Finite.equiv (h1fEquiv e ρ he he')
  refine ⟨Module.Finite.of_restrictScalars_finite ℚ_[l] E _, ?_⟩
  have hH1 : finrank ℚ_[l] (FiniteCohomology ((PP l).PD K) (tr e ρ)) =
      finrank ℚ_[l] E * finrank E ↥(finiteCohomology ((GK K).subtype.comp e.toMonoidHom) ρ) := by
    rw [(h1fEquiv e ρ he he').finrank_eq, finrank_mul_finrank]
  have hH0 : finrank ℚ_[l] ↥(H0V (tr e ρ)) = finrank ℚ_[l] E * finrank E ↥(H0 ρ) := by
    rw [h0V_tr_eq_restrictScalars_h0, finrank_mul_finrank]
    rfl
  have hF : finrank ℚ_[l] ↥(DdR ((PP l).PD K) (tr e ρ) ⊓ FilV ((PP l).PD K) (LL := ℚ_[l]) (V := V) 0) =
      finrank ℚ_[l] E * finrank E ↥(FilD ((GK K).subtype.comp e.toMonoidHom) ρ 0) := by
    rw [DdR_tr, FilV_eq K E V, ← Submodule.restrictScalars_inf, finrank_mul_finrank]
    rfl
  rw [IsDR, ← finrank_mul_finrank ℚ_[l] E V] at hdR'
  rw [hH1, hH0, hdR', hF] at hdim
  have hd : (finrank ℚ_[l] E : ℤ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ_[l]) (M := E)).ne'
  push_cast at hdim
  have : ((finrank E ↥(finiteCohomology ((GK K).subtype.comp e.toMonoidHom) ρ) +
      finrank E ↥(FilD ((GK K).subtype.comp e.toMonoidHom) ρ 0) : ℕ) : ℤ) =
      ((finrank E ↥(H0 ρ) + finrank ℚ_[l] ↥K.1 * finrank E V : ℕ) : ℤ) := by
    push_cast
    refine mul_left_cancel₀ hd ?_
    linear_combination hdim
  exact_mod_cast this

end
