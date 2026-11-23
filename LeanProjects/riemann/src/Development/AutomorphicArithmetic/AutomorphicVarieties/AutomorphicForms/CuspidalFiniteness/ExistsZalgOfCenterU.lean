import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelHeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsArchSmoothOfContDiffChart
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ConstantTermEqZeroOfIsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsKFiniteTotallyRealModelOfIsKFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ModerateGrowthTotallyRealModelOfModerateGrowth
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MapCenterEnvelopingProductGLMemCapelliAlgebra
import GroundTheory.AutomorphicForms.UnitaryAdmissible.CuspFinite

noncomputable section

open NumberField GlobalTheory.CuspRep UpperTheory.V GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

attribute [local instance 100] LieRing.ofAssociativeRing

namespace UpperTheory.V.Af.CuspFin

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ}

def toArch (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) : TR.Sm F a →ₗ[ℂ] archSmooth F a :=
  Submodule.inclusion fun φ h => UpperTheory.isArchSmooth_of_contDiff_chart F a φ h

theorem uAction_lieEq (X : TR.Lie F a) (φ : TR.Sm F a) :
    uAction (UniversalEnvelopingAlgebra.ι ℝ (Fb.lieEq F a X)) (toArch F a φ) = toArch F a (TR.lie F a X φ) := by
  refine Subtype.ext (funext fun g => ?_)
  rw [uAction_ι_apply]
  set Y := (isExpLieAlgebra F a).ofLie (Fb.lieEq F a X)
  have h1 := (isExpLieAlgebra F a).hasDerivAt_rightDeriv ((toArch F a φ).2 g) Y 1
  let T : ArchMatrix F a →ₗ[ℝ] TR.Lie F a :=
    { toFun := fun Z => TR.toL ((Fb.matEq F a).symm Z)
      map_add' := fun _ _ => map_add (Fb.matEq F a).symm _ _
      map_smul' := fun _ _ => map_smul (Fb.matEq F a).symm _ _ }
  have h3 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (Fb.matEq F a (Matrix.of X)) 0
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h3
  have h4 := ((LinearMap.toContinuousLinearMap T).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3).congr_deriv
    (show _ = X from (Fb.matEq F a).symm_apply_apply (Matrix.of X))
  have h2 := TR.hasDerivAt_curve φ g (fun t => (Fb.grpEq F a).symm ((isExpLieAlgebra F a).expG (t • Y))) X
    (by simp) h4
  refine h1.unique (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_))
  simp only [archSlice_apply, one_mul, ← Fb.infEmb_grpEq, MulEquiv.apply_symm_apply]
  rfl

open Classical in

theorem exists_stdBasis (F : Type) [Field F] [NumberField F] (a : ℕ) :
    ∃ b : Module.Basis (InfinitePlace F × Fin a × Fin a) ℝ (TR.Lie F a),
      ∀ l, b l = TR.toL (Matrix.single l.2.1 l.2.2 (Pi.single l.1 1)) := by
  let e : TR.Lie F a ≃ₗ[ℝ] (InfinitePlace F × Fin a × Fin a → ℝ) :=
    { toFun := fun X l => X l.2.1 l.2.2 l.1
      invFun := fun f i j v => f (v, i, j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ⟨Module.Basis.ofEquivFun e, fun ⟨v, i, j⟩ => ?_⟩
  funext i' j' v'
  simp only [Module.Basis.coe_ofEquivFun]
  change (Pi.single (v, i, j) (1 : ℝ) : InfinitePlace F × Fin a × Fin a → ℝ) (v', i', j') = Matrix.single i j (Pi.single v (1 : ℝ) : TR.Rinf F) i' j' v'
  by_cases hi : i = i' <;> by_cases hj : j = j' <;> by_cases hv : v = v' <;>
    simp [Pi.single_apply, Matrix.single_apply, hi, hj, hv, eq_comm]

theorem exists_Zalg_of_centerU {z : UEnv F a} (hz : z ∈ (isExpLieAlgebra F a).centerU) :
    ∃ z' ∈ TR.Zalg F a, ∀ φ, uAction z (toArch F a φ) = toArch F a (z' φ) := by
  classical
  obtain ⟨b, hb⟩ := exists_stdBasis F a
  have hm : ∀ (v v' : InfinitePlace F) (i j k l : Fin a), Matrix.of (b (v, i, j)) * Matrix.of (b (v', k, l)) =
      if j = k ∧ v = v' then Matrix.of (b (v, i, l)) else 0 := by
    intro v v' i j k l
    simp only [hb, Equiv.apply_symm_apply]
    by_cases h : j = k
    · subst h
      rw [Matrix.single_mul_single_same]
      by_cases hv : v = v'
      · subst hv; simp [← Pi.single_mul]
      · have : (Pi.single v 1 * Pi.single v' 1 : TR.Rinf F) = 0 := by
          funext w; by_cases h1 : w = v <;> simp [Pi.single_apply, h1, hv]
        simp [this, hv]
    · simp [Matrix.single_mul_single_of_ne _ _ _ _ h, h]
  have h := UpperTheory.map_center_envelopingProductGL_mem_capelliAlgebra _ _ a (b.map (Fb.lieEq F a))
    (fun v i j k l => by
      simp only [Module.Basis.map_apply, ← Fb.lieEq_lie, hm, map_sub, and_true]
      congr 1 <;> split_ifs <;> first | rfl | exact map_zero _)
    (fun v v' hv i j k l => by
      simp only [Module.Basis.map_apply, ← Fb.lieEq_lie, hm, hv, hv.symm, and_false, if_false, sub_self, map_zero])
    _ (uAction (K := F) (n := a)) z hz
  let S : Subalgebra ℂ (Module.End ℂ (archSmooth F a) × Module.End ℂ (TR.Sm F a)) :=
    { carrier := {p | ∀ φ, p.1 (toArch F a φ) = toArch F a (p.2 φ)}
      mul_mem' := fun {x y} hx hy φ => (congrArg x.1 (hy φ)).trans (hx _)
      add_mem' := fun {x y} hx hy φ => by
        simp only [Prod.fst_add, Prod.snd_add, LinearMap.add_apply, map_add, hx φ, hy φ]
      algebraMap_mem' := fun c φ => (map_smul (toArch F a) c φ).symm }
  have hle : capAlg (fun v i j => uAction (UniversalEnvelopingAlgebra.ι ℝ (b.map (Fb.lieEq F a) (v, i, j)))) ≤
      (S ⊓ (TR.Zalg F a).comap (AlgHom.snd ℂ _ _)).map (AlgHom.fst ℂ _ _) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨v, u, rfl⟩
    let E : Fin a → Fin a → S := fun i j =>
      ⟨(uAction (UniversalEnvelopingAlgebra.ι ℝ (b.map (Fb.lieEq F a) (v, i, j))), TR.Eop v i j), fun φ => by
        rw [Module.Basis.map_apply, hb]; exact uAction_lieEq _ φ⟩
    refine ⟨(Formalism.REAL.qdet E u : S), ⟨(Formalism.REAL.qdet E u).2, ?_⟩, map_qdet ((AlgHom.fst ℂ _ _).comp S.val) E u⟩
    refine Algebra.subset_adjoin ⟨v, u - ((a : ℂ) - 1) / 2, ?_⟩
    rw [TR.cap, sub_add_cancel]
    exact map_qdet ((AlgHom.snd ℂ _ _).comp S.val) E u
  obtain ⟨p, ⟨h1, h2⟩, h3⟩ := hle h
  exact ⟨p.2, h2, fun φ => h3 ▸ h1 φ⟩

theorem isZFinite_toArch {φ : TR.Sm F a}
    (h : FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (TR.Sm F a) => z φ) '' TR.Zalg F a))) :
    IsZFinite (toArch F a φ) := by
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ
    ((fun z : Module.End ℂ (TR.Sm F a) => z φ) '' TR.Zalg F a)).map (toArch F a)) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨z', h1, h2⟩ := exists_Zalg_of_centerU hz
  exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩

theorem isAutomorphicForm_of {φ : TR.Sm F a} (h : TR.IsAutForm φ) : IsAutomorphicForm φ.1 where
  isLeftInvariant := h.left
  isSmooth := ⟨(toArch F a φ).2, fun g => Filter.eventually_of_mem
    (h.level.mem_nhds (show TR.finRep F a 1 φ = φ by rw [map_one]; rfl)) fun k hk => by
      rw [Fb.finEmb_eq]; exact congrFun (congrArg Subtype.val hk) g⟩
  isKFinite := UpperTheory.isKFinite_totallyRealModel_of_isKFinite F a φ h.level h.kfin
  isZFinite := isZFinite_toArch h.zfin
  hasModerateGrowth := UpperTheory.moderateGrowth_totallyRealModel_of_moderateGrowth F a φ h.left h.level h.growth

theorem mem_cuspForms_of (φ : TR.Sm F a) (h : TR.IsCuspForm φ) : φ.1 ∈ cuspForms F a :=
  ⟨isAutomorphicForm_of h.1, UpperTheory.constantTerm_eq_zero_of_isCuspidal F a φ.1 h.1.left (isAutomorphicForm_of h.1).continuous h.2⟩

theorem eigenFinite_of (hc : ∀ φ : TR.Sm F a, TR.IsCuspForm φ → φ.1 ∈ cuspForms F a) (ι : Type) [Fintype ι]
    (b : Module.Basis ι ℝ (TR.Lie F a)) (P : Polynomial ℂ) (hP : P.Monic) (hd : 0 < P.natDegree) (c : ℂ)
    (L : Subgroup (GL (Fin a) (Af F))) (hL : IsOpen (L : Set (GL (Fin a) (Af F)))) :
    FiniteDimensional ℂ (Submodule.span ℂ {φ : TR.Sm F a | TR.IsCuspForm φ ∧ (∀ k ∈ L, TR.finRep F a k φ = φ) ∧
      Polynomial.aeval (∑ l, TR.lie F a (b l) * TR.lie F a (b l)) P φ = 0 ∧ TR.lie F a (TR.oneL F a) φ = c • φ}) := by
  let e : ℝ := UnitaryAdmissible.centralExp F a
  let S : Submodule ℂ (cuspForms F a) :=
    LinearMap.ker (Polynomial.aeval (uActionCusp F a (laplacianU F a (b.map (Fb.lieEq F a)))) P) ⊓
      LinearMap.ker (lieActionCusp F a (UnitaryAdmissible.centralZ F a) - ((e : ℂ) * c) • 1) ⊓
      ⨅ u : L, LinearMap.ker (finRepCusp F a u.1 - 1)
  have hS : FiniteDimensional ℂ S :=
    UnitaryAdmissible.finiteDimensional_of_eigen (b.map (Fb.lieEq F a)) P hP hd ((e : ℂ) * c)
      (L.subgroupOf (AdelicGLn.integralFiniteGL F a)) (hL.preimage continuous_subtype_val) S
      fun φ hφ => ⟨hφ.1.1, sub_eq_zero.1 hφ.1.2, fun u hu =>
        sub_eq_zero.1 ((Submodule.mem_iInf _).1 hφ.2 ⟨u.1, hu⟩)⟩
  let incl : cuspForms F a →ₗ[ℂ] archSmooth F a :=
    Submodule.inclusion (cuspForms_le_automorphicForms.trans automorphicForms_le_archSmooth)
  have hi : Function.Injective incl := Submodule.inclusion_injective _
  have hj : Function.Injective (toArch F a) := Submodule.inclusion_injective _
  refine UnitaryAdmissible.finiteDimensional_of_map_mem (E := S.map incl) (toArch F a) (fun φ hφ => ?_)
    fun φ _ h => hj (h.trans (map_zero _).symm)
  refine (Submodule.span_le (p := (S.map incl).comap (toArch F a))).2 ?_ hφ
  rintro φ ⟨h1, h2, h3, h4⟩
  have hψ : incl ⟨φ.1, hc φ h1⟩ = toArch F a φ := rfl
  refine ⟨⟨φ.1, hc φ h1⟩, ⟨⟨hi ?_, sub_eq_zero.2 (hi ?_)⟩, (Submodule.mem_iInf _).2 fun u => sub_eq_zero.2 ?_⟩, rfl⟩
  · rw [map_aeval_apply_of_intertwine incl (B := uAction (laplacianU F a (b.map (Fb.lieEq F a)))) (fun _ => rfl), hψ,
      ← map_aeval_apply_of_intertwine (toArch F a) (A := ∑ l, TR.lie F a (b l) * TR.lie F a (b l)), h3, map_zero, map_zero]
    intro m
    simp only [laplacianU, map_sum, map_mul, LinearMap.sum_apply, Module.End.mul_apply, Module.Basis.map_apply,
      uAction_lieEq]
  · have hz : UnitaryAdmissible.centralZ F a = Fb.lieEq F a (e • TR.oneL F a) := by
      refine Subtype.ext ?_
      rw [map_smul, UnitaryAdmissible.coe_centralZ, Algebra.algebraMap_eq_smul_one, ← Fb.lieEq_oneL]
      rfl
    change uAction (UniversalEnvelopingAlgebra.ι ℝ (UnitaryAdmissible.centralZ F a)) (toArch F a φ) =
      toArch F a (((e : ℂ) * c) • φ)
    rw [hz, uAction_lieEq, map_smul, LinearMap.smul_apply, h4, mul_smul]
    rfl
  · refine Subtype.ext (funext fun g => ?_)
    change φ.1 (g * finEmb F a u.1) = φ.1 g
    rw [Fb.finEmb_eq]
    exact congrFun (congrArg Subtype.val (h2 u.1 u.2)) g

end UpperTheory.V.Af.CuspFin
