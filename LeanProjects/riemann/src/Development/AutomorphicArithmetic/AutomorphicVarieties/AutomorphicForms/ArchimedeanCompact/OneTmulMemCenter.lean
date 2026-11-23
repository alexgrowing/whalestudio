import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.GrpEqMemArchCompact
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.MultiCentre
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.SLApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.LieDecomp

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped TensorProduct

namespace UpperTheory.V.Cm

attribute [local instance 100] LieRing.ofAssociativeRing

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)

theorem sm_eq : Sm E a = archSmooth E a :=
  le_antisymm (fun _ h => isArchSmooth_of_mem h) fun _ h => mem_Sm_of h

def smEq : Sm E a ≃ₗ[ℂ] archSmooth E a := LinearEquiv.ofEq _ _ (sm_eq E a)

def uTC : UEnv E a →ₐ[ℝ] Module.End ℂ (Sm E a) :=
  ((smEq E a).symm.conjAlgEquiv ℝ).toAlgHom.comp uAction

abbrev UC (E : Type) [Field E] [NumberField E] (a : ℕ) : Type := ℂ ⊗[ℝ] UEnv E a

def uC : UC E a →ₐ[ℂ] Module.End ℂ (Sm E a) :=
  Algebra.TensorProduct.lift (Algebra.ofId ℂ _) (uTC E a) fun c x => Algebra.commutes c (uTC E a x)

def ιC : Lie E a →ₗ[ℝ] UC E a :=
  (Algebra.TensorProduct.includeRight : UEnv E a →ₐ[ℝ] UC E a).toLinearMap ∘ₗ
    (UniversalEnvelopingAlgebra.ι ℝ).toLinearMap ∘ₗ (lieEq E a).toLinearMap

variable {E a}

@[simp] theorem coe_smEq (φ : Sm E a) : (smEq E a φ).1 = φ.1 := rfl

@[simp] theorem coe_smEq_symm (φ : archSmooth E a) : ((smEq E a).symm φ).1 = φ.1 := rfl

theorem smEq_uTC (u : UEnv E a) (φ : Sm E a) : smEq E a (uTC E a u φ) = uAction u (smEq E a φ) := rfl

theorem uTC_ι (X : Lie E a) : uTC E a (UniversalEnvelopingAlgebra.ι ℝ (lieEq E a X)) = lie E a X := by
  refine LinearMap.ext fun φ => Subtype.ext (funext fun g => ?_)
  set h := isExpLieAlgebra E a
  set Y := h.ofLie (lieEq E a X)
  have h1 := h.hasDerivAt_rightDeriv ((smEq E a φ).2 g) Y 1
  have h3 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • (Y : ArchMatrix E a))) (Y : ArchMatrix E a) 0 := by
    simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) (Y : ArchMatrix E a) 0
  have h4 := (archEq E a).symm.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3
  have e : (archEq E a).symm Y = X := (archEq E a).symm_apply_apply X
  have h2 := hasDerivAt_curve φ g (fun t => (grpEq E a).symm (h.expG (t • Y))) X
    (by rw [zero_smul, h.expG_zero, map_one]) (h4.congr_deriv e)
  refine (uAction_ι_apply (lieEq E a X) (smEq E a φ) g).trans (h1.unique ?_)
  simp only [← infEmb_grpEq, MulEquiv.apply_symm_apply] at h2
  simp only [one_mul]
  exact h2

theorem uAction_ι_smEq (X : Lie E a) (φ : Sm E a) :
    uAction (UniversalEnvelopingAlgebra.ι ℝ (lieEq E a X)) (smEq E a φ) = smEq E a (lie E a X φ) := by
  rw [← smEq_uTC, uTC_ι]

theorem uC_tmul (c : ℂ) (x : UEnv E a) : uC E a (c ⊗ₜ x) = c • uTC E a x :=
  (Algebra.TensorProduct.lift_tmul _ _ _ c x).trans (Algebra.smul_def c (uTC E a x)).symm

theorem ιC_apply (X : Lie E a) : ιC E a X = 1 ⊗ₜ UniversalEnvelopingAlgebra.ι ℝ (lieEq E a X) := rfl

theorem uC_ιC (X : Lie E a) : uC E a (ιC E a X) = lie E a X := by rw [ιC_apply, uC_tmul, one_smul, uTC_ι]

theorem isLieHom_ιC : AlgRepEndIrreducible.IsLieHom (ιC E a) := fun X Y => by
  simp only [ιC_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [← TensorProduct.tmul_sub, lieEq_lie, LieHom.map_lie, Ring.lie_def]

def genC (τ : E →+* ℂ) (i j : Fin a) : UC E a := AlgRepEndIrreducible.eL (ιC E a) τ i j

theorem uC_genC (τ : E →+* ℂ) (i j : Fin a) : uC E a (genC τ i j) = Eop τ i j := by
  rw [genC, AlgRepEndIrreducible.eL, map_smul, map_sub, map_smul, uC_ιC, uC_ιC]
  rfl

theorem glRel_genC (τ : E →+* ℂ) : Formalism.REAL.GlRel (genC (a := a) τ) := (AlgRepEndIrreducible.eLRel E a _ _ isLieHom_ιC).1 τ

theorem commute_genC {σ τ : E →+* ℂ} (h : σ ≠ τ) (i j k l : Fin a) : Commute (genC σ i j) (genC τ k l) :=
  (AlgRepEndIrreducible.eLRel E a _ _ isLieHom_ιC).2 σ τ h i j k l

theorem ιC_eq_sum (X : Lie E a) : ιC E a X = ∑ τ : E →+* ℂ, ∑ i, ∑ j, coord τ (X i j) • genC τ i j :=
  AlgRepEndIrreducible.lieDecomp E a _ (ιC E a) (Matrix.of X)

theorem lie_eq_sum (X : Lie E a) : lie E a X = ∑ τ : E →+* ℂ, ∑ i, ∑ j, coord τ (X i j) • Eop τ i j := by
  simp only [← uC_ιC, ιC_eq_sum, map_sum, map_smul, uC_genC]

theorem adjoin_genC : Algebra.adjoin ℂ {x : UC E a | ∃ τ i j, x = genC τ i j} = ⊤ := by
  set S := Algebra.adjoin ℂ {x : UC E a | ∃ τ i j, x = genC τ i j}
  have key : ∀ u : UEnv E a, (1 : ℂ) ⊗ₜ[ℝ] u ∈ S := fun u => by
    induction u using UEnv.induction with
    | halg r =>
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul]
      exact (S.restrictScalars ℝ).smul_mem S.one_mem r
    | hι Y =>
      obtain ⟨X, rfl⟩ := (lieEq E a).surjective Y
      rw [← ιC_apply, ιC_eq_sum]
      exact sum_mem fun τ _ => sum_mem fun i _ => sum_mem fun j _ =>
        S.smul_mem (Algebra.subset_adjoin ⟨τ, i, j, rfl⟩) _
    | hmul x y hx hy => simpa only [Algebra.TensorProduct.tmul_mul_tmul, one_mul] using mul_mem hx hy
    | hadd x y hx hy => rw [TensorProduct.tmul_add]; exact add_mem hx hy
  refine eq_top_iff.2 fun w _ => ?_
  induction w using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul c x => simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using S.smul_mem (key x) c
  | add x y hx hy => exact add_mem (hx trivial) (hy trivial)

def capC (τ : E →+* ℂ) (u : ℂ) : UC E a := Formalism.REAL.qdet (genC τ) (u + ((a : ℂ) - 1) / 2)

theorem uC_capC (τ : E →+* ℂ) (u : ℂ) : uC E a (capC τ u) = cap τ u := by
  rw [capC, Fb.map_qdet]
  simp only [uC_genC]
  rfl

private theorem mem_center_of {z : UC E a} (h : ∀ τ i j, genC τ i j * z = z * genC τ i j) :
    z ∈ Subalgebra.center ℂ (UC E a) := by
  have : Algebra.adjoin ℂ {x : UC E a | ∃ τ i j, x = genC τ i j} ≤ Subalgebra.centralizer ℂ {z} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, i, j, rfl⟩ _ rfl
    exact (h τ i j).symm
  exact Subalgebra.mem_center_iff.2 fun x => (this (adjoin_genC (E := E) (a := a) ▸ Algebra.mem_top) z rfl).symm

theorem capC_mem_center (τ : E →+* ℂ) (u : ℂ) : capC τ u ∈ Subalgebra.center ℂ (UC E a) := by
  refine mem_center_of fun σ i j => ?_
  by_cases e : σ = τ
  · subst e
    exact (Formalism.REAL.qDetCentral _ a _ (glRel_genC σ) _ i j).symm
  · let S := Subalgebra.centralizer ℂ {genC σ i j}
    have hS : ∀ k l, genC τ k l ∈ S := fun k l => by
      rintro _ rfl
      exact commute_genC e i j k l
    refine (?_ : capC τ u ∈ S) _ rfl
    refine S.sum_mem fun s _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine S.add_mem ?_ (hS _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem

theorem center_UC : Subalgebra.center ℂ (UC E a) = Algebra.adjoin ℂ {z | ∃ τ u, z = capC τ u} := by
  refine le_antisymm (fun z hz => ?_) (Algebra.adjoin_le ?_)
  · refine Algebra.adjoin_mono ?_ (Fb.multiCentre (genC (E := E) (a := a)) glRel_genC (fun _ _ h => commute_genC h)
      (adjoin_genC (E := E) (a := a) ▸ Algebra.mem_top) fun τ i j => Subalgebra.mem_center_iff.1 hz _)
    rintro _ ⟨τ, u, rfl⟩
    exact ⟨τ, u - ((a : ℂ) - 1) / 2, by rw [capC, sub_add_cancel]⟩
  · rintro _ ⟨τ, u, rfl⟩
    exact capC_mem_center τ u

theorem Zalg_eq_map : Zalg E a = (Subalgebra.center ℂ (UC E a)).map (uC E a) := by
  rw [center_UC, AlgHom.map_adjoin]
  refine congrArg (Algebra.adjoin ℂ) (Set.ext fun z => ⟨?_, ?_⟩)
  · rintro ⟨τ, u, rfl⟩
    exact ⟨_, ⟨τ, u, rfl⟩, uC_capC τ u⟩
  · rintro ⟨_, ⟨τ, u, rfl⟩, rfl⟩
    exact ⟨τ, u, uC_capC τ u⟩

omit [IsTotallyComplex E] in
theorem one_tmul_mem_center {z : UEnv E a} (hz : z ∈ (isExpLieAlgebra E a).centerU) :
    (1 : ℂ) ⊗ₜ[ℝ] z ∈ Subalgebra.center ℂ (UC E a) := by
  refine Subalgebra.mem_center_iff.2 fun w => ?_
  induction w with
  | zero => rw [zero_mul, mul_zero]
  | tmul c x => simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, Subalgebra.mem_center_iff.1 hz x]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]

omit [IsTotallyComplex E] in

theorem exists_re_im_center {w : UC E a} (hw : w ∈ Subalgebra.center ℂ (UC E a)) :
    ∃ p ∈ (isExpLieAlgebra E a).centerU, ∃ q ∈ (isExpLieAlgebra E a).centerU, w = (1 : ℂ) ⊗ₜ p + Complex.I ⊗ₜ q :=
  Fb.exists_re_im w fun _ => Subalgebra.mem_center_iff.1 hw _

theorem uTC_mem_Zalg {z : UEnv E a} (hz : z ∈ (isExpLieAlgebra E a).centerU) : uTC E a z ∈ Zalg E a := by
  rw [Zalg_eq_map]
  exact ⟨_, one_tmul_mem_center hz, (uC_tmul 1 z).trans (one_smul _ _)⟩

theorem mem_Zalg_iff {z : Module.End ℂ (Sm E a)} : z ∈ Zalg E a ↔
    ∃ p ∈ (isExpLieAlgebra E a).centerU, ∃ q ∈ (isExpLieAlgebra E a).centerU,
      z = uTC E a p + Complex.I • uTC E a q := by
  constructor
  · rw [Zalg_eq_map]
    rintro ⟨w, hw, rfl⟩
    obtain ⟨p, hp, q, hq, rfl⟩ := exists_re_im_center hw
    exact ⟨p, hp, q, hq, (map_add (uC E a) _ _).trans (by rw [uC_tmul, uC_tmul, one_smul])⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact add_mem (uTC_mem_Zalg hp) (Subalgebra.smul_mem _ (uTC_mem_Zalg hq) _)

theorem cap_mem_Zalg (τ : E →+* ℂ) (u : ℂ) : cap τ u ∈ Zalg E a := Algebra.subset_adjoin ⟨τ, u, rfl⟩

theorem Zalg_eq_span : Subalgebra.toSubmodule (Zalg E a) =
    Submodule.span ℂ (uTC E a '' ((isExpLieAlgebra E a).centerU : Set (UEnv E a))) := by
  refine le_antisymm (fun z hz => ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨p, hp, q, hq, rfl⟩ := mem_Zalg_iff.1 hz
    exact add_mem (Submodule.subset_span ⟨p, hp, rfl⟩) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, hq, rfl⟩))
  · rintro _ ⟨z, hz, rfl⟩
    exact uTC_mem_Zalg hz

theorem zfin_iff (φ : Sm E a) :
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)) ↔
      IsZFinite (smEq E a φ) := by
  have e : (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)).map (smEq E a).toLinearMap =
      Submodule.span ℂ ((fun z => uAction z (smEq E a φ)) '' ((isExpLieAlgebra E a).centerU : Set (UEnv E a))) := by
    have h1 : (fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a =
        (Subalgebra.toSubmodule (Zalg E a)).map (LinearMap.applyₗ φ) := rfl
    rw [h1, Submodule.span_eq, Zalg_eq_span, Submodule.map_span, Submodule.map_span, Set.image_image, Set.image_image]
    rfl
  rw [IsZFinite, ← e]
  exact ⟨fun _ => inferInstance, fun h => Module.Finite.equiv ((smEq E a).submoduleMap _).symm⟩

end UpperTheory.V.Cm
