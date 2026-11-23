import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_isGen_linComb_of_pull {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (f : Z ⟶ Y) (c : LB.Gen ((LB.LinComb L φ ε).pull f))
    (hc : c.IsGen) : ∃ d : LB.Gen (LB.LinComb L (fun k => f ≫ φ k) ε), d.IsGen := by
  have hle : ∀ j : K → L.ι, LB.wchart L (fun k => f ≫ φ k) j ≤
      LB.wchart (LB.LinComb L φ ε) (K := PUnit) (fun _ => f) (fun _ => j) :=
    fun j _ hy => Set.mem_iInter.2 fun _ => LB.wchart_comp_le L f φ j hy
  refine ⟨⟨fun j => res (hle j) (LB.ts c (fun _ => j))⟩, ?_⟩
  refine (LB.isGen_iff L _).2 fun i j => ?_
  have key := congrArg (res (inf_le_inf (hle i) (hle j)))
    ((LB.isGen_iff (LB.LinComb L φ ε) c).1 hc (fun _ => i) (fun _ => j))
  have e := LB.lcg_pull (LB.LinComb L φ ε) f (fun _ => i) (fun _ => j)
  rw [LB.lcg_comp]
  refine (LB.res_res _ _ _).trans (((LB.res_res _ _ _).symm.trans key).trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ?_)))
  · exact (congrArg _ e).trans (LB.res_res _ _ _)
  · exact (LB.res_res _ _ _).trans (LB.res_res _ _ _).symm

theorem exists_isGen_translDiff_comp {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left)
    {T T' : Over S} (x : T ⟶ A) (g : T' ⟶ T) (V : T.left.Opens)
    (hg : ∀ q, g.left q ∈ V)
    (c : LB.Gen ((Out.translDiff A L x).pull ((fst T A).left ⁻¹ᵁ V).ι)) (hc : c.IsGen) :
    ∃ d : LB.Gen (Out.translDiff A L (g ≫ x)), d.IsGen := by
  obtain ⟨d, hd⟩ := exists_isGen_linComb_of_pull L _ _ _ c hc
  have hr : Set.range (g ▷ A).left ⊆ Set.range ((fst T A).left ⁻¹ᵁ V).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    change ((g ▷ A).left ≫ (fst T A).left) y ∈ V
    rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
    exact hg _
  have hl := IsOpenImmersion.lift_fac ((fst T A).left ⁻¹ᵁ V).ι (g ▷ A).left hr
  have h4 : ∃ w : LB.Gen (LB.LinComb L _ _), w.IsGen :=
    ⟨_, LB.isGen_pullGen L _ _ d hd (IsOpenImmersion.lift ((fst T A).left ⁻¹ᵁ V).ι (g ▷ A).left hr)⟩
  have h3 : (fun k : Fin 2 => IsOpenImmersion.lift ((fst T A).left ⁻¹ᵁ V).ι (g ▷ A).left hr ≫
      ((fst T A).left ⁻¹ᵁ V).ι ≫
        ![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] k) =
      ![(lift (fst T' A ≫ g ≫ x) (snd T' A) ≫ μ[A]).left, (snd T' A).left] := by
    funext k
    rw [← Category.assoc, hl]
    fin_cases k
    · change (g ▷ A ≫ lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left =
        (lift (fst T' A ≫ g ≫ x) (snd T' A) ≫ μ[A]).left
      rw [comp_lift_assoc, whiskerRight_fst_assoc, whiskerRight_snd]
    · change (g ▷ A ≫ snd T A).left = (snd T' A).left
      rw [whiskerRight_snd]
  rw [h3] at h4
  exact h4

theorem kTriv_of_global : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB →
    (∀ (R : Type) [CommRing R] [Algebra ℂ R], ∀ (x : Over.mk (spMap (algebraMap ℂ R)) ⟶ A),
      (∃ c : LB.Gen (Out.translDiff A L x), c.IsGen) → x = 1) → Out.KTriv A L := by
  intro A _ L _ _ H R _ t x hx
  have H' : ∀ (R' : CommRingCat.{0}) (t' : Spec R' ⟶ Sp ℂ) (y : Over.mk t' ⟶ A),
      (∃ c : LB.Gen (Out.translDiff A L y), c.IsGen) → y = 1 := by
    intro R' t'
    obtain ⟨φ, rfl⟩ := Spec.map_surjective t'
    let _ : Algebra ℂ R' := φ.hom.toAlgebra
    exact H R'
  change x = 1
  apply Over.OverMorphism.ext
  refine Scheme.hom_ext_of_forall _ _ fun p => ?_
  obtain ⟨V, hp, c, hc⟩ := hx p
  obtain ⟨U, hU, hpU, hUV⟩ := exists_isAffineOpen_mem_and_subset (U := V) (x := p) hp
  refine ⟨U, hpU, ?_⟩
  let g : Over.mk (hU.fromSpec ≫ t) ⟶ Over.mk t := Over.homMk hU.fromSpec rfl
  have h1 : g ≫ x = g ≫ 1 := by
    rw [MonObj.comp_one]
    exact H' _ _ _ (exists_isGen_translDiff_comp A L x g V
      (fun q => hUV (hU.range_fromSpec.le ⟨q, rfl⟩)) c hc)
  have h2 : hU.fromSpec ≫ x.left = hU.fromSpec ≫ (1 : Over.mk t ⟶ A).left :=
    congrArg (·.left) h1
  rw [IsAffineOpen.fromSpec, Category.assoc, Category.assoc, cancel_epi] at h2
  exact h2

end GlobalTheory
