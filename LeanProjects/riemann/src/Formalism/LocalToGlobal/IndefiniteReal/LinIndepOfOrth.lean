import Formalism.LocalToGlobal.IndefiniteReal.IsotInLeOfIntw

noncomputable section

open NumberField IsDedekindDomain
open Formalism.L2.Theta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.principalLevelFrame

section ConjIso

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def cj (f : Formalism.AUTREP.GAf L n → ℂ) : Formalism.AUTREP.GAf L n → ℂ := fun g => star (f g)

theorem cj_cj (f : Formalism.AUTREP.GAf L n → ℂ) : cj (cj f) = f := by
  funext g
  simp [cj]

theorem cj_add (f f' : Formalism.AUTREP.GAf L n → ℂ) : cj (f + f') = cj f + cj f' := by
  funext g
  simp [cj]

theorem cj_smul (a : ℂ) (f : Formalism.AUTREP.GAf L n → ℂ) : cj (a • f) = star a • cj f := by
  funext g
  simp [cj, mul_comm]

def toU {U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)} (f : conjSub U) : U := ⟨cj f.1, f.2⟩

def ofU {U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)} (u : U) : conjSub U :=
  ⟨cj u.1, by
    show cj (cj u.1) ∈ U
    rw [cj_cj]
    exact u.2⟩

def conjMap {U U' : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)} (T : U →ₗ[ℂ] U') : conjSub U →ₗ[ℂ] conjSub U' where
  toFun f := ofU (T (toU f))
  map_add' f f' := by
    have : toU (f + f') = toU f + toU f' := Subtype.ext (cj_add f.1 f'.1)
    apply Subtype.ext
    show cj ((T (toU (f + f')) : U') : Formalism.AUTREP.GAf L n → ℂ) =
      cj ((T (toU f) : U') : Formalism.AUTREP.GAf L n → ℂ) + cj ((T (toU f') : U') : Formalism.AUTREP.GAf L n → ℂ)
    rw [this, map_add, Submodule.coe_add, cj_add]
  map_smul' a f := by
    have : toU (a • f) = star a • toU f := Subtype.ext (cj_smul a f.1)
    apply Subtype.ext
    show cj ((T (toU (a • f)) : U') : Formalism.AUTREP.GAf L n → ℂ) = a • cj ((T (toU f) : U') : Formalism.AUTREP.GAf L n → ℂ)
    rw [this, map_smul, Submodule.coe_smul, cj_smul, star_star]

theorem toU_ofU {U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)} (u : U) : toU (ofU u) = u :=
  Subtype.ext (cj_cj u.1)

theorem conjT_iso {π π' : Formalism.L2.NG.FinTyp L n} (h : π.Iso π') : (FinTyp.conjT π).Iso (FinTyp.conjT π') := by
  obtain ⟨T, hT⟩ := h
  let E : conjSub π.S ≃ₗ[ℂ] conjSub π'.S :=
    { conjMap T.toLinearMap with
      invFun := conjMap T.symm.toLinearMap
      left_inv := fun f => by
        apply Subtype.ext
        show cj ((T.symm (toU (ofU (T (toU f)))) : π.S) : Formalism.AUTREP.GAf L n → ℂ) = f.1
        rw [toU_ofU, LinearEquiv.symm_apply_apply]
        exact cj_cj f.1
      right_inv := fun f => by
        apply Subtype.ext
        show cj ((T (toU (ofU (T.symm (toU f)))) : π'.S) : Formalism.AUTREP.GAf L n → ℂ) = f.1
        rw [toU_ofU, LinearEquiv.apply_symm_apply]
        exact cj_cj f.1 }
  refine ⟨E, fun h f f' hf => ?_⟩
  show cj ((T (toU f') : π'.S) : Formalism.AUTREP.GAf L n → ℂ) = Formalism.L2.NG.rt L n h (cj ((T (toU f) : π'.S) : Formalism.AUTREP.GAf L n → ℂ))
  have h1 : ((toU f' : π.S) : Formalism.AUTREP.GAf L n → ℂ) = Formalism.L2.NG.rt L n h ((toU f : π.S) : Formalism.AUTREP.GAf L n → ℂ) := by
    show cj f'.1 = Formalism.L2.NG.rt L n h (cj f.1)
    rw [hf]
    rfl
  rw [hT h _ _ h1]
  rfl

theorem not_iso_conjT {π π' : Formalism.L2.NG.FinTyp L n} (h : ¬ π.Iso π') : ¬ (FinTyp.conjT π).Iso (FinTyp.conjT π') := by
  intro hc
  apply h
  have := conjT_iso hc
  unfold Formalism.L2.NG.FinTyp.Iso at this ⊢
  rwa [conjT_S, conjT_S, conjT_S, conjT_S, conjSub_conjSub, conjSub_conjSub] at this

end ConjIso

section LinIndep

variable {A : Type} [AddCommGroup A] [Module ℂ A]

theorem hp_smul_right {C : Submodule ℂ A} {ip : A → A → ℂ} (hp : PeterssonHilbertSpace.IsHermPos C ip) (x y : C) (a : ℂ) :
    ip x (a • (y : A)) = a * ip x y := by
  have h1 := hp.herm x (a • y)
  have h2 := hp.smul a y x
  have h3 := hp.herm y x
  rw [Submodule.coe_smul] at h1
  calc ip x (a • (y : A)) = starRingEnd ℂ (starRingEnd ℂ (ip x (a • (y : A)))) := by simp
    _ = starRingEnd ℂ (ip (a • (y : A)) x) := by rw [h1]
    _ = starRingEnd ℂ (starRingEnd ℂ a * ip y x) := by rw [h2]
    _ = a * starRingEnd ℂ (ip y x) := by simp
    _ = a * ip x y := by rw [h3]

theorem linIndep_of_orth {C : Submodule ℂ A} {ip : A → A → ℂ} (hp : PeterssonHilbertSpace.IsHermPos C ip) {ι : Type} (x : ι → C)
    (hx : ∀ i, x i ≠ 0) (horth : ∀ i j, i ≠ j → ip (x i) (x j) = 0) : LinearIndependent ℂ x := by
  classical
  rw [linearIndependent_iff']
  intro s g hg j hj
  have h0 := congrArg (fun z : C => ip (x j) (z : A)) hg
  simp only [Submodule.coe_zero, Submodule.coe_sum] at h0
  rw [hp_zero_right hp, hp_sum_right hp (x j) s (fun i => g i • x i)] at h0
  have hterm : ∀ i ∈ s, ip (x j) ((g i • x i : C) : A) = if i = j then g j * ip (x j) (x j) else 0 := by
    intro i _
    rw [Submodule.coe_smul, hp_smul_right hp]
    split_ifs with hij
    · rw [hij]
    · rw [horth j i (Ne.symm hij), mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' s j, if_pos hj] at h0
  have hne : ip (x j) (x j) ≠ 0 := by
    intro h
    have := hp.pos (x j) (hx j)
    rw [h, Complex.zero_re] at this
    exact lt_irrefl _ this
  exact (mul_eq_zero.1 h0).resolve_right hne

end LinIndep

section Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance instCMHostN (D : Formalism.BasicNotions.D7) : IsCMField D.host.E := D.host.isCMField_hostE

variable {D : Formalism.BasicNotions.D7} {Y : Formalism.BasicNotions.TH.HSp D} {n : ℕ} {Sp : D.what₂.Tau → SPar}
variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

theorem finite_FTR (P : RowPsi Y n) (M : Mult.DSModel Y Sp) (J : Bool → Set (GA D Y)) (χ : Bool → GA D Y → ℂ)
    (e : Bool → (GA D Y → ℂ) →ₗ[ℂ] (GA D Y → ℂ)) (μ : Bool → Measure (GA D Y)) (𝓕 : Bool → Set (GA D Y))
    (hD : ∀ b, IsotDecomp θ P M (J b) (χ b) (e b) (μ b) (𝓕 b))
    (hp : ∀ b, PeterssonHilbertSpace.IsHermPos (Mult.goodPart θ M (J b) (χ b) (e b)) (Mult.ipM M (μ b) (𝓕 b))) : Finite (FTR θ P M J χ e) := by
  classical
  have hfin : ∀ b, Finite {σ : FTR θ P M J χ e // isotE θ P M (J b) (χ b) (e b) (rowRepR θ σ) ≠ ⊥} := by
    intro b
    haveI := (hp b).fd
    let x : {σ : FTR θ P M J χ e // isotE θ P M (J b) (χ b) (e b) (rowRepR θ σ) ≠ ⊥} → Mult.goodPart θ M (J b) (χ b) (e b) :=
      fun σ => ⟨(Submodule.exists_mem_ne_zero_of_ne_bot σ.2).choose,
        ((Submodule.exists_mem_ne_zero_of_ne_bot σ.2).choose_spec.1).1⟩
    have hx0 : ∀ σ, x σ ≠ 0 := fun σ h0 =>
      (Submodule.exists_mem_ne_zero_of_ne_bot σ.2).choose_spec.2 (congrArg Subtype.val h0)
    have horth : ∀ σ σ', σ ≠ σ' → Mult.ipM M (μ b) (𝓕 b) (x σ) (x σ') = 0 := by
      intro σ σ' hne
      refine (hD b).2 _ _ (not_iso_conjT fun h => hne (Subtype.ext (rowRepR_inj θ σ.1 σ'.1 h))) _
        (Submodule.exists_mem_ne_zero_of_ne_bot σ.2).choose_spec.1 _ (Submodule.exists_mem_ne_zero_of_ne_bot σ'.2).choose_spec.1
    exact (linIndep_of_orth (hp b) x hx0 horth).finite
  have hcover : ∀ σ : FTR θ P M J χ e, ∃ b, isotE θ P M (J b) (χ b) (e b) (rowRepR θ σ) ≠ ⊥ := fun σ => rowRepR_occ θ σ
  have : Finite ((Σ b : Bool, {σ : FTR θ P M J χ e // isotE θ P M (J b) (χ b) (e b) (rowRepR θ σ) ≠ ⊥})) := by
    haveI := hfin true
    haveI := hfin false
    infer_instance
  exact Finite.of_surjective (fun p : (Σ b : Bool, {σ : FTR θ P M J χ e // isotE θ P M (J b) (χ b) (e b) (rowRepR θ σ) ≠ ⊥}) =>
    p.2.1) fun σ => by
      obtain ⟨b, hb⟩ := hcover σ
      exact ⟨⟨b, σ, hb⟩, rfl⟩

end Fin

end Formalism.IndefR.principalLevelFrame
