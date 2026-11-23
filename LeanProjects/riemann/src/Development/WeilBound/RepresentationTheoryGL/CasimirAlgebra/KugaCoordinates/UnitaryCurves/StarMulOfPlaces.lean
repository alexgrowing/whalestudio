import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CompactUnitaryGroups.IsCompactUnitaryGroup
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.UnitaryCurves.ExistsUnitaryCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinitesimalCharacterQuantumDet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteCapOfCommuteEop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped Classical

namespace PositivityTheory.Rg.Cz.GK

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem exists_eval {π : CuspSub E a} (S : Submodule ℂ π.V) [FiniteDimensional ℂ S] (lam : π.V →ₗ[ℂ] ℂ) :
    ∃ (s : Finset (GA E a)) (c : GA E a → ℂ), ∀ v ∈ S, lam v = ∑ g ∈ s, c g * v.1.1 g := by
  let ev : GA E a → Module.Dual ℂ S := fun g =>
    { toFun := fun v => v.1.1.1 g
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  obtain ⟨s, c, h⟩ := exists_comb_of_sep ev (fun v hv => Subtype.ext (Subtype.ext (Subtype.ext (funext hv))))
    (lam ∘ₗ S.subtype)
  exact ⟨s, c, fun v hv => h ⟨v, hv⟩⟩

theorem continuous_eval (y : Sm E a) (g : GA E a) :
    Continuous fun k : Kinf E a => y.1 (g * infGL E a (Unitary.toUnits k)) := by
  have h1 : (fun k : Kinf E a => y.1 (g * infGL E a (Unitary.toUnits k))) =
      fun k => chart y.1 g (toL k.1) := funext fun k => (chart_val y.1 g (Unitary.toUnits k)).symm
  rw [h1]
  exact (y.2 g).continuousOn.comp_continuous continuous_subtype_val fun k => val_mem_invSet (Unitary.toUnits k)

omit [NumberField E] [IsTotallyComplex E] in

theorem star_mul_of_places (D : InfinitePlace E → Matrix (Fin a) (Fin a) ℂ) (h : ∀ w, star (D w) * D w = 1) :
    star (Matrix.of fun i j w => D w i j : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of (fun i j w => D w i j) = 1 := by
  ext i j w
  have := congrArg (fun M => M i j) (h w)
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply] at this ⊢
  rw [Finset.sum_apply]
  simp only [Pi.mul_apply, Pi.star_apply]
  rw [this, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

omit [NumberField E] [IsTotallyComplex E] in

theorem atEmb_apply (τ : E →+* ℂ) (z : ℂ) (w : InfinitePlace E) :
    atEmb τ z w = if w = InfinitePlace.mk τ then
      (if (InfinitePlace.mk τ).embedding = τ then z else starRingEnd ℂ z) else 0 := by
  unfold atEmb
  split_ifs <;> simp_all

theorem exists_curve (τ : E →+* ℂ) (X : Matrix (Fin a) (Fin a) ℂ) (hX : Xᴴ = -X) :
    ∃ c : ℝ → Kinf E a, c 0 = 1 ∧ (∀ i j, HasDerivAt (fun t => kap E a τ (c t) i j) (X i j) 0) ∧
      (∀ τ', τ' ≠ τ → τ' ≠ barE E τ → ∀ t, kap E a τ' (c t) = 1) ∧
      HasDerivAt (fun t => toL (c t).1) (fun i j => atEmb τ (X i j)) 0 := by
  set v := InfinitePlace.mk τ with hv
  set Y : Matrix (Fin a) (Fin a) ℂ := if v.embedding = τ then X else X.map (starRingEnd ℂ) with hYd
  have hY : Yᴴ = -Y := by
    rw [hYd]
    split_ifs
    · exact hX
    · ext i j
      have := congrArg (fun M => M i j) hX
      simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Matrix.map_apply] at this ⊢
      rw [← star_star (X j i), this, star_neg, Complex.star_def, Complex.conj_conj]
  obtain ⟨U, hU, hU0, hUd⟩ := exists_unitary_curve Y hY
  let D : ℝ → InfinitePlace E → Matrix (Fin a) (Fin a) ℂ := fun t w => if w = v then U t else 1
  have hD : ∀ t w, star (D t w) * D t w = 1 := fun t w => by
    simp only [D]; split_ifs
    · exact hU t
    · simp
  let C : ℝ → Matrix (Fin a) (Fin a) (Cinf E) := fun t => Matrix.of fun i j w => D t w i j
  have hC : ∀ t, C t ∈ Matrix.unitaryGroup (Fin a) (Cinf E) := fun t =>
    (Matrix.mem_unitaryGroup_iff').2 (star_mul_of_places (D t) (hD t))
  refine ⟨fun t => ⟨C t, hC t⟩, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    ext i j w
    simp only [C, D, hU0, Matrix.of_apply, ite_self]
    show (1 : Matrix (Fin a) (Fin a) ℂ) i j = (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w
    simp only [Matrix.one_apply]
    split_ifs <;> rfl
  · intro i j
    show HasDerivAt (fun t => coord τ (C t i j)) (X i j) 0
    have e : (fun t => coord τ (C t i j)) = fun t =>
        if v.embedding = τ then U t i j else starRingEnd ℂ (U t i j) := by
      funext t
      rw [PositivityTheory.Rg.Cz.J.coord_eq]
      simp only [C, D, Matrix.of_apply, ← hv, ↓reduceIte]
    rw [e]
    by_cases hε : v.embedding = τ
    · simp only [hε, if_true]
      have := hUd i j
      simpa [hYd, hε] using this
    · simp only [hε, if_false]
      have := (hUd i j).star
      simp only [hYd, hε, if_false, Matrix.map_apply] at this
      simpa [Complex.star_def] using this
  · intro τ' h1 h2 t
    have hw : InfinitePlace.mk τ' ≠ v := by
      rw [hv]
      intro h
      rcases InfinitePlace.mk_eq_iff.1 h with h | h
      · exact h1 h
      · apply h2
        show τ' = ComplexEmbedding.conjugate τ
        rw [← h]
        exact (star_star τ').symm
    ext i j
    show coord τ' (C t i j) = (1 : Matrix (Fin a) (Fin a) ℂ) i j
    rw [PositivityTheory.Rg.Cz.J.coord_eq]
    simp only [C, D, Matrix.of_apply, if_neg hw, Matrix.one_apply]
    split_ifs <;> simp
  · rw [hasDerivAt_pi]; intro i; rw [hasDerivAt_pi]; intro j; rw [hasDerivAt_pi]; intro w
    simp only [atEmb_apply, ← hv]
    show HasDerivAt (fun t => D t w i j) _ 0
    by_cases hw : w = v
    · simp only [D, hw, if_true]
      have := hUd i j
      rw [hYd] at this
      split_ifs at this ⊢ <;> simpa using this
    · simp only [D, hw, if_false]
      exact hasDerivAt_const _ _

theorem lieOp_atEmb (π : CuspSub E a) (τ : E →+* ℂ) (X : Matrix (Fin a) (Fin a) ℂ) :
    lieOp π (fun i j => atEmb τ (X i j)) =
      ∑ i, ∑ j, (X i j • cx τ (lieOp π) i j + star (X i j) • cx (barE E τ) (lieOp π) i j) := by
  have key : ∀ (z : ℂ) (i j : Fin a), lieS E a i j (atEmb τ z) =
      z • Eop τ i j + star z • Eop (barE E τ) i j := by
    intro z i j
    rw [atEmb_eq τ z, map_add, map_smul, map_smul, lieS_atEmb_one, lieS_atEmb_I]
    conv_rhs => rw [← Complex.re_add_im z]
    simp only [Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [← Complex.coe_smul, ← Complex.coe_smul]
    match_scalars <;> ring
  refine LinearMap.ext fun φ => Subtype.ext ?_
  have hX : lie E a (fun i j => atEmb τ (X i j)) = ∑ i, ∑ j, lieS E a i j (atEmb τ (X i j)) := by
    simp only [lieS_apply, ← map_sum]
    exact congrArg _ (Matrix.matrix_eq_sum_single (Matrix.of fun i j => atEmb τ (X i j)))
  change lie E a (fun i j => atEmb τ (X i j)) φ.1 = _
  rw [hX]
  simp only [key, LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_sum,
    Submodule.coe_add, Submodule.coe_smul]
  rfl

theorem fin_orbit (π : CuspSub E a) (y : π.V) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun γ => π.op (.cpt γ) y)) := by
  have h := (π.cusp y.1 y.2).1.kfin
  have e : (Submodule.span ℂ (Set.range fun γ => π.op (.cpt γ) y)).map π.V.subtype =
      Submodule.span ℂ (Set.range fun k => cptRep E a k y.1) := by
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  have : FiniteDimensional ℂ ((Submodule.span ℂ (Set.range fun γ => π.op (.cpt γ) y)).map π.V.subtype) := e ▸ h
  exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ π.V.injective_subtype _).symm

theorem gkData_holds : GKData := by
  intro E _ _ _ a π
  refine { gl := ?_, comm := ?_, one := ?_, mul := ?_, ad := ?_, fin := fin_orbit π, cont := ?_, der := ?_ }
  · intro τ i j k l
    let X : Fin a → Fin a → GlobalTheory.WigCap.keep π := fun i j => ⟨Eop τ i j, GlobalTheory.WigCap.Eop_mem π τ i j⟩
    have hX : (fun i j => GlobalTheory.WigCap.res π (X i j)) = cx τ (lieOp π) :=
      funext fun i => funext fun j => GlobalTheory.WigCap.res_Eop π τ i j
    have h := glRel_Eop (a := a) τ i j k l
    rw [← hX]
    simp only
    have h2 : X i j * X k l - X k l * X i j = (if j = k then X i l else 0) - (if l = i then X k j else 0) := by
      apply Subtype.ext
      simp only [Subalgebra.coe_sub, Subalgebra.coe_mul]
      rw [h]
      split_ifs <;> rfl
    rw [← map_mul, ← map_mul, ← map_sub, h2, map_sub]
    split_ifs <;> simp
  · intro τ τ' h i j k l
    refine LinearMap.ext fun φ => Subtype.ext ?_
    change Eop τ i j (Eop τ' k l φ.1) = Eop τ' k l (Eop τ i j φ.1)
    exact LinearMap.congr_fun (Eop_comm h i j k l) φ.1
  · refine LinearMap.ext fun φ => Subtype.ext ?_
    change cptRep E a 1 φ.1 = φ.1
    rw [map_one]; rfl
  · intro γ δ
    refine LinearMap.ext fun φ => Subtype.ext ?_
    change cptRep E a (γ * δ) φ.1 = cptRep E a γ (cptRep E a δ φ.1)
    rw [map_mul]; rfl
  · intro γ τ i j
    have h := GlobalTheory.CapAdInv.rt_Eop (Unitary.toUnits γ) τ i j
    refine LinearMap.ext fun φ => Subtype.ext ?_
    have h2 := LinearMap.congr_fun h φ.1
    change cptRep E a γ (Eop τ i j φ.1) = _
    refine h2.trans ?_
    simp only [Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum,
      Submodule.coe_smul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    congr 1
    show coord τ (γ.1 k i) * coord τ ((star γ.1) j l) = coord τ (γ.1 k i) * star (coord τ (γ.1 l j))
    rw [Matrix.star_apply, PositivityTheory.Rg.Cz.J.coord_star]
  · intro y lam
    have := fin_orbit π y
    obtain ⟨s, c, hc⟩ := exists_eval (Submodule.span ℂ (Set.range fun γ => π.op (.cpt γ) y)) lam
    have e : (fun γ => lam (π.op (.cpt γ) y)) =
        fun γ => ∑ g ∈ s, c g * y.1.1 (g * infGL E a (Unitary.toUnits γ)) :=
      funext fun γ => hc _ (Submodule.subset_span ⟨γ, rfl⟩)
    rw [e]
    exact continuous_finsetSum _ fun g _ => continuous_const.mul (continuous_eval y.1 g)
  · intro τ X hX
    obtain ⟨c, h0, hk, hoth, hZ⟩ := exists_curve τ X hX
    refine ⟨c, h0, hk, hoth, fun y lam => ?_⟩
    let Zl : Lie E a := fun i j => atEmb τ (X i j)
    let S := Submodule.span ℂ (Set.range fun γ => π.op (.cpt γ) y) ⊔ Submodule.span ℂ {lieOp π Zl y}
    have := fin_orbit π y
    have : FiniteDimensional ℂ S := Submodule.finiteDimensional_sup _ _
    obtain ⟨s, cc, hc⟩ := exists_eval S lam
    rw [← lieOp_atEmb π τ X]
    rw [hc _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))]
    have e : (fun t => lam (π.op (.cpt (c t)) y)) =
        fun t => ∑ g ∈ s, cc g * y.1.1 (g * infGL E a (Unitary.toUnits (c t))) :=
      funext fun t => hc _ (Submodule.mem_sup_left (Submodule.subset_span ⟨c t, rfl⟩))
    rw [e]
    have h0' : Unitary.toUnits (c 0) = 1 := by rw [h0, map_one]
    have hs := HasDerivAt.sum (u := s) (x := (0 : ℝ)) fun g (_ : g ∈ s) =>
      (hasDerivAt_curve y.1 g (fun t => Unitary.toUnits (c t)) Zl h0' hZ).const_mul (cc g)
    rw [Finset.sum_fn] at hs
    exact hs

end PositivityTheory.Rg.Cz.GK

end
