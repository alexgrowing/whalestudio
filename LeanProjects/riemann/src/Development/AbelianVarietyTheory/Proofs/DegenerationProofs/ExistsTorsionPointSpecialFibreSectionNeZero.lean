import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrameUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLocalHomOfTest
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConj
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionTranslateZerosLt

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.TorsionNonzero

section Pull
variable {X Y : Scheme.{0}}

abbrev one (L : LB X) : LB X := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)

theorem chart_le (L : LB X) {V : X.Opens} (F : Y ⟶ X) (h : ⊤ ≤ F ⁻¹ᵁ V) (k : PUnit → L.ι) :
    (L.pull F).U k ≤ F ⁻¹ᵁ (V ⊓ (one L).U (fun _ => k PUnit.unit)) := fun x hx =>
  ⟨h (x := x) trivial, Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx PUnit.unit⟩

theorem appLE_res (F : Y ⟶ X) {U V : X.Opens} {W : Y.Opens} (e : V ≤ U) (h : W ≤ F ⁻¹ᵁ V) (h' : W ≤ F ⁻¹ᵁ U)
    (a : Γ(X, U)) : (F.appLE V W h).hom (resG X e a) = (F.appLE U W h').hom a := by
  rw [← Scheme.Hom.map_appLE F h (homOfLE e).op]
  rfl

theorem res_appLE (F : Y ⟶ X) {U : X.Opens} {W W' : Y.Opens} (e : W' ≤ W) (h : W ≤ F ⁻¹ᵁ U) (h' : W' ≤ F ⁻¹ᵁ U)
    (a : Γ(X, U)) : resG Y e ((F.appLE U W h).hom a) = (F.appLE U W' h').hom a := by
  rw [← Scheme.Hom.appLE_map F h (homOfLE e).op]
  rfl

theorem g_eq {K : Type} [Fintype K] [Unique K] (L : LB X) (F : Y ⟶ X) (i j : K → L.ι)
    (h : _ ≤ F ⁻¹ᵁ (L.U (i default) ⊓ L.U (j default))) :
    ((LB.LinComb L (K := K) (fun _ => F) (fun _ => 1)).g i j).val =
      (F.appLE _ _ h).hom (L.g (i default) (j default)).val := by
  simp only [LB.LinComb, Fintype.prod_unique, zpow_one]
  rfl

def pullSec (L : LB X) {V : X.Opens} (σ : ∀ j, Γ(X, V ⊓ (one L).U j)) (hσ : σ ∈ secOn (one L) V) (F : Y ⟶ X)
    (h : ⊤ ≤ F ⁻¹ᵁ V) : (L.pull F).Sec where
  f k := (F.appLE _ _ (chart_le L F h k)).hom (σ fun _ => k PUnit.unit)
  compat i j := by
    have hi := (inf_le_left : (L.pull F).U i ⊓ (L.pull F).U j ≤ _).trans (chart_le L F h i)
    have hj := (inf_le_right : (L.pull F).U i ⊓ (L.pull F).U j ≤ _).trans (chart_le L F h j)
    have hj' : (L.pull F).U i ⊓ (L.pull F).U j ≤ F ⁻¹ᵁ (one L).U (fun _ => j PUnit.unit) :=
      hj.trans (F.preimage_mono inf_le_right)
    have hi' : (L.pull F).U i ⊓ (L.pull F).U j ≤ F ⁻¹ᵁ (one L).U (fun _ => i PUnit.unit) :=
      hi.trans (F.preimage_mono inf_le_right)
    have hW : (L.pull F).U i ⊓ (L.pull F).U j ≤
        F ⁻¹ᵁ (V ⊓ (one L).U (fun _ => i PUnit.unit) ⊓ (one L).U (fun _ => j PUnit.unit)) := le_inf hi hj'
    have h₁ : (one L).U (fun _ => i PUnit.unit) ⊓ (one L).U (fun _ => j PUnit.unit) ≤
        𝟙 X ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) :=
      inf_le_inf (LB.wchart_le L _ _ 0) (LB.wchart_le L _ _ 0)
    have h₂ : (L.pull F).U i ⊓ (L.pull F).U j ≤ F ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) :=
      inf_le_inf (LB.wchart_le L _ _ PUnit.unit) (LB.wchart_le L _ _ PUnit.unit)
    have hU : (L.pull F).U i ⊓ (L.pull F).U j ≤
        F ⁻¹ᵁ ((one L).U (fun _ => i PUnit.unit) ⊓ (one L).U (fun _ => j PUnit.unit)) := le_inf hi' hj'
    have e := congrArg (F.appLE _ _ hW).hom (hσ (fun _ => i PUnit.unit) (fun _ => j PUnit.unit))
    rw [map_mul, appLE_res F _ hW hi, appLE_res F _ hW hj, appLE_res F _ hW hU] at e
    refine (res_appLE F _ _ hi _).trans (e.trans (congrArg₂ (· * ·) ?_ (res_appLE F _ _ hj _).symm))
    refine (congrArg (F.appLE _ _ hU).hom (g_eq L (𝟙 X) _ _ h₁)).trans (Eq.trans ?_ (g_eq L F i j h₂).symm)
    exact congrArg (fun φ => φ.hom (L.g (i PUnit.unit) (j PUnit.unit)).val)
      (Scheme.Hom.appLE_comp_appLE F (𝟙 X) _ _ _ h₁ hU)

theorem le_nonzeroLocus_iff (L : LB X) {V : X.Opens} (σ : ∀ j, Γ(X, V ⊓ (one L).U j)) (hσ : σ ∈ secOn (one L) V)
    (F : Y ⟶ X) (h : ⊤ ≤ F ⁻¹ᵁ V) {K : Type} [Field K] (x : Sp K ⟶ Y) :
    ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (pullSec L σ hσ F h) ↔ ∃ j, valF (x ≫ F) _ (σ j) ≠ 0 := by
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 ((Points.le_preimage_iff x _).1 hx)
    have h₁ := (Points.le_preimage_iff x _).2 hk
    have h₂ := Points.le_preimage_mono x (Y.basicOpen_le _) h₁
    have h₃ := (Points.le_preimage_basicOpen_iff x h₂ _).1 h₁
    refine ⟨fun _ => k PUnit.unit, ?_⟩
    rw [Points.valF_eq_valR, ← Points.valR_appLE x F (chart_le L F h k) h₂]
    exact h₃.ne_zero
  · rintro ⟨j, hj⟩
    obtain ⟨a, rfl⟩ : ∃ a, j = fun _ => a := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim _ _)⟩
    have h₁ : ⊤ ≤ (x ≫ F) ⁻¹ᵁ (V ⊓ (one L).U fun _ => a) := by
      by_contra hc
      exact hj (dif_neg hc)
    have h₂ : ⊤ ≤ x ⁻¹ᵁ (L.pull F).U (fun _ => a) := fun z hz =>
      Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (h₁ hz).2 0
    rw [Points.valF_eq_valR, ← Points.valR_appLE x F (chart_le L F h fun _ => a) h₂] at hj
    exact Points.le_preimage_mono x (le_iSup (fun k => Y.basicOpen ((pullSec L σ hσ F h).f k)) fun _ => a)
      ((Points.le_preimage_basicOpen_iff x h₂ _).2 hj.isUnit)

end Pull

theorem exists_torsion_valF_ne_zero : Laws → Laws2 → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Big → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∀ (F : u.G.left ⟶ Q.G.left) (ψ : pullback u.G.hom (jK u.V) ⟶ pullback ρ.P.A.hom Q.u₀), Q.TestMap u yV yK F ψ → LBIso (Q.L.L.pull F) u.U.LG.L → ∀ (N : M.Z.Opens) (σ : Q.SecFam N), σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → Q.FibNe N σ → y (cPt p) ∈ N → ∃ t : Over.mk (spMap (IsLocalRing.residue (OO p)) ≫ spMap jV) ⟶ u.G, t ^ (S.r * S.N) = 1 ∧ ∃ j, valF (X := Q.G.left) (t.left ≫ F) _ (σ j) ≠ 0 := by
  intro laws laws₂ o Ω _ _ _ _ S ρ M U₀ Q hbig p _ y y₀ u jV yV yK hfac F ψ hmap hiso N σ hσ hne hy
  obtain ⟨hj, hyV, -, -⟩ := hfac
  have hloc := ZHPre.isLocalHom_of_test u jV hj
  have hK : IsAlgClosed (IsLocalRing.ResidueField (OO p)) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have hsq := hmap.1.1
  set r : Sp (IsLocalRing.ResidueField (OO p)) ⟶ Sp u.V :=
    spMap (IsLocalRing.residue (OO p)) ≫ spMap jV with hr
  have key : ∀ x, r x = IsLocalRing.closedPoint u.V := fun x => by
    have hx : x = IsLocalRing.closedPoint _ :=
      Subsingleton.elim (α := PrimeSpectrum (IsLocalRing.ResidueField (OO p))) _ _
    subst hx
    exact (congrArg (PrimeSpectrum.comap jV)
      (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))).trans (IsLocalRing.comap_closedPoint jV)
  have hrange : Set.range r = {IsLocalRing.closedPoint u.V} := by
    ext x
    exact ⟨fun ⟨a, ha⟩ => ha ▸ key a, fun h => ⟨IsLocalRing.closedPoint _, (key _).trans h.symm⟩⟩
  have hyN : ⊤ ≤ yV ⁻¹ᵁ N := by
    refine (Points.le_preimage_iff yV N).2 ?_
    rw [← hyV] at hy
    rw [← IsLocalRing.comap_closedPoint jV]
    exact hy
  have hF : ⊤ ≤ F ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N) := by
    rw [← Scheme.Hom.comp_preimage, hsq.w]
    exact fun z _ => hyN (x := u.G.hom z) trivial
  let θ := pullSec Q.L.L σ hσ F hF
  have hθ : ∃ x ∈ nonzeroLocus θ, u.G.hom x = IsLocalRing.closedPoint u.V := by
    obtain ⟨g, j, hg, hv⟩ := hne _ (r ≫ yV) (by
      rintro _ ⟨z, rfl⟩
      exact hyN (x := r z) trivial)
    have h₁ := (le_nonzeroLocus_iff Q.L.L σ hσ F hF (hsq.lift g r hg)).2 ⟨j, by rwa [hsq.lift_fst]⟩
    refine ⟨hsq.lift g r hg (IsLocalRing.closedPoint _), h₁ (x := IsLocalRing.closedPoint _) trivial, ?_⟩
    exact (congrArg (fun φ : Sp _ ⟶ Sp u.V => φ (IsLocalRing.closedPoint _)) (hsq.lift_snd g r hg)).trans (key _)
  have hg : u.A.g = S.g := (H1.dim_unique u.A.A.hom u.A.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback u.cart.1 ρ.P.smoothDim)
    (eSec u.A.A (IsLocalRing.closedPoint (FractionRing u.V)))).trans ρ.g_eq
  have hN : 4 ≤ S.N := by
    rw [ρ.N_eq]
    have h₂ : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (two_pos.trans_le ρ.two_le).ne' _)
    exact Nat.pow_le_pow_left h₂ 2
  have hn : ((S.r * S.N : ℕ) : IsLocalRing.ResidueField (OO p)) ≠ 0 := by
    have := S.unit.map (Spec.preimage (r ≫ yV ≫ M.s)).hom
    rw [map_natCast] at this
    exact this.ne_zero
  have hlt : 6 * (S.N ^ u.A.g * u.A.g.factorial) < (S.r * S.N) ^ 2 := by
    rw [hg]
    exact hbig.2.2.trans_le (Nat.le_self_pow two_ne_zero _)
  have hc := GlobalTheory.FewZeros.card_torsion_translate_zeros_lt laws laws₂ u.V u.complete u.D u.A u.G u.U (Q.L.L.pull F) θ
    (pull_isLB Q.L.isLB F) hiso hθ _ r S.N (S.r * S.N) hrange hN hn hlt 1
  by_contra hcon
  have heq : Nat.card {h : Over.mk r ⟶ u.G // h ^ (S.r * S.N) = 1 ∧ ¬ ⊤ ≤ (1 * h).left ⁻¹ᵁ nonzeroLocus θ} =
      Nat.card {h : Over.mk r ⟶ u.G // h ^ (S.r * S.N) = 1} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun h => and_iff_left_of_imp fun hh hle => hcon ⟨h, hh, ?_⟩)
    rw [_root_.one_mul] at hle
    exact (le_nonzeroLocus_iff Q.L.L σ hσ F hF h.left).1 hle
  omega

end GlobalTheory.ZH.TorsionNonzero
end
