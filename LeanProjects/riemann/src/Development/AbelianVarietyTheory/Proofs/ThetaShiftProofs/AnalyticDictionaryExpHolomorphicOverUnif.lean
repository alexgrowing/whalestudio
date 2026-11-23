import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts

section Lift

variable [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]

theorem gtHol_toUnit_left :
    (show Sp ℂ ⟶ Sp ℂ from (toUnit (Out.TF (R := ℂ) ℂ)).left) = 𝟙 (Sp ℂ) := by
  have h : (show Sp ℂ ⟶ Sp ℂ from (toUnit (Out.TF (R := ℂ) ℂ)).left) =
      Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ := by
    have := Over.w (toUnit (Out.TF (R := ℂ) ℂ))
    exact (Category.comp_id _).symm.trans this
  refine h.trans ((Spec.map_comp _ _).symm.trans ?_)
  refine Eq.trans (congrArg Spec.map ?_) (Spec.map_id _)
  ext x
  exact (IsScalarTower.algebraMap_apply ℂ (FractionRing ℂ) ℂ x).symm

theorem gtHol_isLift (D₀ : Out.DegPre ℂ) {g : ℕ} (u : HolUnif D₀.P.A D₀.P.L g) (p : Out.TF (R := ℂ) ℂ ⟶ D₀.P.A)
    (χ : D₀.X) (c z : Fin g → ℂ) (hc : u.ex c = D₀.c χ) (hp : (show Sp ℂ ⟶ _ from p.left) = (u.ex z).left) :
    FrameValue.IsLift u (Out.DegPre.gtφ D₀ ℂ p χ) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![c + z, c, z, 0] := by
  have e : ∀ w, (show Sp ℂ ⟶ _ from (toUnit (Out.TF (R := ℂ) ℂ) ≫ u.ex w).left) = (u.ex w).left := fun w =>
    (congrArg (fun q : Sp ℂ ⟶ Sp ℂ => q ≫ (u.ex w).left) gtHol_toUnit_left).trans (Category.id_comp _)
  have hp' : p = toUnit _ ≫ u.ex z := Over.OverMorphism.ext (hp.trans (e z).symm)
  have h0 : u.ex 0 = η[D₀.P.A] := by
    rw [(u.ker 0).2 u.Λ.zero_mem, Hom.one_def]
    simp
  intro k
  refine (Category.id_comp _).trans ?_
  fin_cases k
  · refine Eq.trans ?_ (e (c + z))
    refine congrArg (fun m : Out.TF (R := ℂ) ℂ ⟶ D₀.P.A => m.left) ?_
    rw [u.ex_add, MonObj.comp_mul, hc, ← hp']
    rfl
  · refine Eq.trans ?_ (e c)
    rw [hc]
    rfl
  · exact hp
  · refine Eq.trans ?_ (e 0)
    rw [h0]
    rfl

end Lift

theorem analyticDictionaryExp_holomorphic_over_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a), IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ _ from (Λ.ex0 z).b.left)) ∧ ∀ x j, DifferentiableOn ℂ (fun z => chiVal (Λ.ex0 z) x j) {z | ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 z).b x) j} ∧ ∀ z, ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 z).b x) j → chiVal (Λ.ex0 z) x j = eTwoPi (z.1 (Λ.ε.symm x)) * FrameValue.frameProd Λ.u Out.DegPre.gtε ![Λ.A.ct (Λ.ε.symm x) + z.2, Λ.A.ct (Λ.ε.symm x), z.2, 0] j := by
  intro E _ _ _ H _ D l c O _ β _ _ b a Λ
  have hl : ∀ (z : Λ.A.V) (x : a.D₀.X), FrameValue.IsLift Λ.u (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 z).b x)
      (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![Λ.A.ct (Λ.ε.symm x) + z.2, Λ.A.ct (Λ.ε.symm x), z.2, 0] := fun z x =>
    gtHol_isLift a.D₀ Λ.u _ x _ _ (by rw [Λ.ct, LinearEquiv.apply_symm_apply]) (Λ.ex0_b z)
  have hv : ∀ x j z, ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 z).b x) j →
      chiVal (Λ.ex0 z) x j = eTwoPi (z.1 (Λ.ε.symm x)) * FrameValue.frameProd Λ.u Out.DegPre.gtε
        ![Λ.A.ct (Λ.ε.symm x) + z.2, Λ.A.ct (Λ.ε.symm x), z.2, 0] j := by
    intro x j z hj
    have h₁ := FrameValue.valAt'_gen a.D₀.P.isLB ((Λ.ex0 z).isGen x) (hl z x) (j := j) hj
    obtain ⟨y, rfl⟩ := Λ.ε.surjective x
    rw [LinearEquiv.symm_apply_apply] at h₁ ⊢
    rw [Λ.arcDict_expZero_section] at h₁
    exact h₁
  refine ⟨fun U f => ?_, fun x j => ⟨?_, hv x j⟩⟩
  · obtain ⟨ho, hd⟩ := Λ.u.hol U f
    simp only [Λ.ex0_b, Set.mem_univ, true_and]
    exact ⟨ho.preimage continuous_snd, hd.comp differentiable_snd.differentiableOn (fun _ h => h)⟩
  · refine DifferentiableOn.congr ?_ (hv x j)
    refine DifferentiableOn.fun_mul ?_ ?_
    · have : Differentiable ℂ (fun z : Λ.A.V => z.1 (Λ.ε.symm x)) :=
        (Λ.A.evalCLM (Λ.ε.symm x)).differentiable.comp differentiable_fst
      exact ((this.const_mul _).cexp).differentiableOn
    · intro z₀ hz₀
      refine DifferentiableAt.differentiableWithinAt ?_
      have hd : ∀ k, Differentiable ℂ fun z : Λ.A.V =>
          (![Λ.A.ct (Λ.ε.symm x) + z.2, Λ.A.ct (Λ.ε.symm x), z.2, 0] : Fin 4 → Fin Λ.A.gB → ℂ) k := fun k => by
        fin_cases k
        · exact differentiable_snd.const_add _
        · exact differentiable_const _
        · exact differentiable_snd
        · exact differentiable_const _
      have h : ∀ k, DifferentiableAt ℂ (fun z : Λ.A.V => Λ.u.fr (j k)
          ((![Λ.A.ct (Λ.ε.symm x) + z.2, Λ.A.ct (Λ.ε.symm x), z.2, 0] : Fin 4 → Fin Λ.A.gB → ℂ) k) ^
            Out.DegPre.gtε k) z₀ := fun k => by
        have hk := ((hl z₀ x).le_iff j).1 hz₀ k
        refine DifferentiableAt.zpow ?_ (Or.inl (Λ.u.fr_ne _ _ hk))
        exact ((Λ.u.fr_hol (j k)).differentiableAt ((Λ.u.hol _ 0).1.mem_nhds hk)).comp z₀ (hd k z₀)
      exact (HasFDerivAt.finsetProd (u := Finset.univ) fun k _ => (h k).hasFDerivAt).differentiableAt

end GlobalTheory.ArcPts
