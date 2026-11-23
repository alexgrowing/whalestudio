import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory.PowSec

section Transport

variable {X Y : Scheme.{0}} (L : LB X) (σ : Y ⟶ X) (ρ : X ⟶ Y) (e : ρ ≫ σ = 𝟙 X) (n : ℤ)

include e in
theorem chart_eq (j : PUnit → L.ι) :
    LB.wchart L (fun _ : PUnit => 𝟙 X) j = ρ ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => σ) (fun _ => j PUnit.unit) := by
  ext y
  have h : σ (ρ y) = y := by rw [← Scheme.Hom.comp_apply, e]; rfl
  constructor
  · intro hy
    refine Set.mem_iInter.2 fun _ => ?_
    have := Set.mem_iInter.1 hy PUnit.unit
    show σ (ρ y) ∈ L.U (j PUnit.unit)
    rw [h]; exact this
  · intro hy
    refine Set.mem_iInter.2 fun _ => ?_
    have : σ (ρ y) ∈ L.U (j PUnit.unit) := Set.mem_iInter.1 hy 0
    rw [h] at this; exact this

theorem appLE_congr {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens) (h₁ : V ≤ f ⁻¹ᵁ U) (h₂ : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V h₁ = g.appLE U V h₂ := by subst h; rfl

def down (b : (LB.LinComb L (K := Fin 1) (fun _ => σ) (fun _ => n)).Sec) :
    (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => n)).Sec where
  f j := (ρ.appLE _ _ (chart_eq L σ ρ e j).le).hom (b.f (fun _ => j PUnit.unit))
  compat i j := by
    have hle : LB.wchart L (fun _ : PUnit => 𝟙 X) i ⊓ LB.wchart L (fun _ : PUnit => 𝟙 X) j ≤
      ρ ⁻¹ᵁ (LB.wchart L (fun _ : Fin 1 => σ) (fun _ => i PUnit.unit) ⊓
        LB.wchart L (fun _ : Fin 1 => σ) (fun _ => j PUnit.unit)) :=
      inf_le_inf (chart_eq L σ ρ e i).le (chart_eq L σ ρ e j).le
    have := congrArg (ρ.appLE _ _ hle).hom (b.compat (fun _ => i PUnit.unit) (fun _ => j PUnit.unit))
    replace this := this.trans (map_mul _ _ _)
    refine Eq.trans ?_ (this.trans (congrArg₂ (· * ·) ?_ ?_))
    · exact (congrArg (fun φ => φ.hom (b.f fun _ => i PUnit.unit))
        ((Scheme.Hom.appLE_map ρ _ _).trans (Scheme.Hom.map_appLE ρ hle _).symm) :)
    · simp only [LB.LinComb, Fintype.prod_unique]
      refine (congrArg Units.val ((map_zpow (Units.map (ρ.appLE _ _ hle).hom.toMonoidHom) _ n).trans
        (congrArg (· ^ n) (Units.ext ?_))) :)
      have h1 : (σ.app (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) ≫ Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : Fin 1 => σ) (fun _ => i PUnit.unit) 0))
          (inf_le_right.trans (LB.wchart_le L (fun _ : Fin 1 => σ) (fun _ => j PUnit.unit) 0)))).op) ≫ ρ.appLE _ _ hle =
          (𝟙 X : X ⟶ X).app (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) ≫ X.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : PUnit => 𝟙 X) i PUnit.unit))
          (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit => 𝟙 X) j PUnit.unit)))).op :=
        (Scheme.Hom.appLE_comp_appLE ρ σ _ _ _ _ hle).trans (appLE_congr e _ _ _ _)
      exact congrArg (fun φ => φ.hom (L.g (i PUnit.unit) (j PUnit.unit)).val) h1
    · exact (congrArg (fun φ => φ.hom (b.f fun _ => j PUnit.unit))
        ((Scheme.Hom.map_appLE ρ hle _).trans (Scheme.Hom.appLE_map ρ _ _).symm) :)

theorem appLE_injective [IsIso ρ] (U : Y.Opens) (V : X.Opens) (h : V = ρ ⁻¹ᵁ U) :
    Function.Injective (ρ.appLE U V h.le).hom := by
  subst h
  rw [Scheme.Hom.appLE_eq_app]
  exact (ConcreteCategory.bijective_of_isIso (ρ.app U)).1

end Transport

attribute [local instance] Over.cartesianMonoidalCategory

open Out in

theorem exists_indep_sections (H : Out.GlobalSectionsRankAlgClosed) (P : Out.PolAV (Sp ℂ)) (n : ℕ) (hn : 1 ≤ n) :
    ∃ s : Fin (n ^ P.g) → (lbPow P.L n).Sec, ∀ a : Fin (n ^ P.g) → ℂ,
      (∀ j, ∑ i, constFn P.A.hom _ (a i) * (s i).f j = 0) → a = 0 := by
  have hr := H ℂ P n hn
  let T : Over (Sp ℂ) := baseOver (Sp ℂ)
  let c : Γ(T.left, ⊤) ≃+* ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
  haveI : Nontrivial Γ(T.left, ⊤) := c.symm.injective.nontrivial
  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_finrank (R := Γ(T.left, ⊤)) (M := SecM P.A P.L n T) hr.ge
  let ρ : P.A ⟶ T ⊗ P.A := lift (Over.homMk P.A.hom (Category.comp_id _)) (𝟙 _)
  have ρ₂ : ρ.left ≫ (snd T P.A).left = 𝟙 _ := congrArg (fun q => q.left) (lift_snd _ _ : ρ ≫ _ = _)
  have ρ₁ : ρ.left ≫ (fst T P.A).left = P.A.hom := congrArg (fun q => q.left) (lift_fst _ _ : ρ ≫ _ = _)
  have ρ₃ : (snd T P.A).left ≫ ρ.left = 𝟙 _ := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₁).trans (pullback.condition.symm.trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₂).trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  haveI : IsIso ρ.left := ⟨_, ρ₂, ρ₃⟩
  refine ⟨fun i => down P.L (snd T P.A).left ρ.left ρ₂ n (SecM.toSec P.A (b i)), fun a ha => ?_⟩
  have h0 : ∑ i, c.symm (a i) • b i = 0 := by
    refine Subtype.ext (funext fun j => ?_)
    obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
    refine appLE_injective ρ.left _ _ (chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)) ?_
    refine Eq.trans ?_ ((ha (fun _ => k)).trans (map_zero _).symm)
    rw [Submodule.coe_sum]
    refine (congrArg _ (Finset.sum_apply _ _ _)).trans ?_
    refine (map_sum (ρ.left.appLE _ _ (chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)).le).hom _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
    refine (map_mul _ (liftHom P.A _ (c.symm (a i))) ((b i).1 fun _ => k)).trans (congrArg₂ (· * ·) ?_ rfl)
    have h1 := (Scheme.Hom.appLE_comp_appLE ρ.left (fst T P.A).left ⊤ _ _ (fun _ _ => trivial)
      (chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)).le).trans (appLE_congr ρ₁ ⊤ _ _ (fun _ _ => trivial))
    exact congrArg (fun φ => φ.hom (c.symm (a i))) h1
  funext i
  exact c.symm.injective ((Fintype.linearIndependent_iff.1 hb _ h0 i).trans (map_zero _).symm)

end GlobalTheory.PowSec
