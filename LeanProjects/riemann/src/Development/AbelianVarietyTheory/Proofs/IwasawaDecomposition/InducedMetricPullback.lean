import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.InducedPull

variable {X X' Z : Scheme.{0}}

theorem val_pull_g (B : LB X) (a : Z ⟶ X) (i i' : (B.pull a).ι)
    (l : (B.pull a).U i ⊓ (B.pull a).U i' ≤ a ⁻¹ᵁ (B.U (i PUnit.unit) ⊓ B.U (i' PUnit.unit))) :
    ((B.pull a).g i i').val = (a.appLE _ _ l).hom (B.g (i PUnit.unit) (i' PUnit.unit)).val := by
  have : (B.pull a).g i i' = res l (pullU a _ (B.g (i PUnit.unit) (i' PUnit.unit))) := by
    change ∏ _k : PUnit, _ = _
    exact (Fintype.prod_unique _).trans (zpow_one _)
  rw [this]
  rfl

theorem inf_le (B : LB X) (a : Z ⟶ X) (i i' : (B.pull a).ι) :
    (B.pull a).U i ⊓ (B.pull a).U i' ≤ a ⁻¹ᵁ (B.U (i PUnit.unit) ⊓ B.U (i' PUnit.unit)) :=
  fun _ hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩

theorem chart_le (B : LB X) (a : X' ⟶ X) (b : Z ⟶ X') (i : ((B.pull a).pull b).ι) :
    ((B.pull a).pull b).U i ≤ (B.pull (b ≫ a)).U fun _ => i PUnit.unit PUnit.unit :=
  fun _ hx => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (Set.mem_iInter.1 hx PUnit.unit) PUnit.unit

theorem presents_pull_pull [IsIntegral Z] {B : LB X} (hB : B.IsLB) (a : X' ⟶ X) (b : Z ⟶ X')
    {D : CartierDiv Z} {r : (B.pull (b ≫ a)).ι → Z.functionFieldˣ} (hr : Presents D (B.pull (b ≫ a)) r) :
    Presents D ((B.pull a).pull b) fun i => r fun _ => i PUnit.unit PUnit.unit := by
  refine ⟨LB.isLB_pull (LB.isLB_pull hB a) b, fun i j h => ?_,
    fun i x hx => hr.isEqn _ x (chart_le B a b i hx)⟩
  have l : ((B.pull a).pull b).U i ⊓ ((B.pull a).pull b).U j ≤
      (B.pull (b ≫ a)).U (fun _ => i PUnit.unit PUnit.unit) ⊓
        (B.pull (b ≫ a)).U fun _ => j PUnit.unit PUnit.unit :=
    inf_le_inf (chart_le B a b i) (chart_le B a b j)
  rw [hr.isRatSec _ _ (l h), ← fnOf_resG l h, val_pull_g _ b i j (inf_le _ b i j),
    val_pull_g B a _ _ (inf_le B a _ _)]
  congr 2
  refine (congrArg _ (val_pull_g B (b ≫ a) _ _ (inf_le B _ _ _))).trans ?_
  have e := (Scheme.Hom.appLE_map (b ≫ a) (inf_le B (b ≫ a) (fun _ => i PUnit.unit PUnit.unit)
    fun _ => j PUnit.unit PUnit.unit) (homOfLE l).op).trans
    (Scheme.Hom.appLE_comp_appLE b a _ _ _ (inf_le B a (i PUnit.unit) (j PUnit.unit))
      (inf_le _ b i j)).symm
  exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom e)
    (B.g (i PUnit.unit PUnit.unit) (j PUnit.unit PUnit.unit)).val

theorem induced_pull : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y)
    (M N : TrueGeo.Model Y) (π : N.X ⟶ M.X) (hπ : π ≫ M.p = N.p), N.j ≫ π = M.j →
    ∀ (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ),
      A.Induced M L k cf → A.Induced N (L.pull π hπ) k cf := by
  intro F _ _ C Y A M N π hπ hj L k cf h
  obtain ⟨MX, Mp, Mar, Mj, Mpb⟩ := M
  dsimp only at π hπ hj L
  subst hj
  obtain ⟨h₀, r, hr, h₁, h₂⟩ := h
  refine ⟨h₀, fun i => r fun _ => i PUnit.unit PUnit.unit, presents_pull_pull L.isLB π N.j hr, ?_, ?_⟩
  · intro σ y y' i f hy hi hf
    rw [h₁ σ y (Points.PtsOver.map π hπ _ y') (fun _ => i PUnit.unit PUnit.unit) f
      ((congrArg (· ≫ π) hy).trans (Category.assoc _ _ _)) (chart_le L.B π N.j i hi) hf]
    exact congrArg (fun t => _ * Real.exp (-t)) ((L.φ _).pull_φ π hπ _ y').symm
  · intro v e y yt i hy hi
    exact h₂ v e y (yt ≫ π) (fun _ => i PUnit.unit PUnit.unit)
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ π) hy).trans (Category.assoc _ _ _)))
      fun x hx => Set.mem_iInter.1 (hi hx) PUnit.unit

end GlobalTheory.TrueGeo.InducedPull
