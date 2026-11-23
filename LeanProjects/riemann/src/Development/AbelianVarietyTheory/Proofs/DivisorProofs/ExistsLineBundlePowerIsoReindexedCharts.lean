import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

namespace GlobalTheory.PowIsoRe

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (e1 : W ≤ V) (e2 : V ≤ U) (x : Γ(X, U)ˣ) :
    res e1 (res e2 x) = res (e1.trans e2) x := by
  ext1
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem preimage_comp_le {X Y Z : Scheme.{0}} (h : X ⟶ Y) (φ : Y ⟶ Z) {W : Z.Opens} {V : Y.Opens}
    (e : V ≤ φ ⁻¹ᵁ W) : h ⁻¹ᵁ V ≤ (h ≫ φ) ⁻¹ᵁ W := by
  intro x hx
  exact e hx

theorem pullU_res_pullU {X Y Z : Scheme.{0}} (h : X ⟶ Y) (φ : Y ⟶ Z) {W : Z.Opens} {V : Y.Opens}
    (e : V ≤ φ ⁻¹ᵁ W) (u : Γ(Z, W)ˣ) :
    pullU h V (res e (pullU φ W u)) = res (preimage_comp_le h φ e) (pullU (h ≫ φ) W u) := by
  have key : φ.app W ≫ Y.presheaf.map (homOfLE e).op ≫ h.app V =
      (h ≫ φ).app W ≫ X.presheaf.map (homOfLE (preimage_comp_le h φ e)).op := by
    rw [Scheme.Hom.naturality, Scheme.Hom.comp_app]
    rfl
  ext1
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, key]

end GlobalTheory.PowIsoRe

namespace GlobalTheory.PowIsoRe

theorem res_pull_comp {X Y Z : Scheme.{0}} (h : X ⟶ Y) (m : Y ⟶ Z) {W : Z.Opens} {V1 : Y.Opens}
    {V2 V3 T : X.Opens} (u : Γ(Z, W)ˣ) (e1 : V1 ≤ m ⁻¹ᵁ W) (e2 : V2 ≤ h ⁻¹ᵁ V1) (e3 : T ≤ V2)
    (e4 : V3 ≤ (h ≫ m) ⁻¹ᵁ W) (e5 : T ≤ V3) :
    res e3 (res e2 (pullU h V1 (res e1 (pullU m W u)))) = res e5 (res e4 (pullU (h ≫ m) W u)) := by
  rw [pullU_res_pullU, res_res, res_res, res_res]

theorem res_res' {X : Scheme.{0}} {U V V' W : X.Opens} (x : Γ(X, U)ˣ) (e1 : W ≤ V) (e2 : V ≤ U)
    (e3 : W ≤ V') (e4 : V' ≤ U) : res e1 (res e2 x) = res e3 (res e4 x) := by
  rw [res_res, res_res]

end GlobalTheory.PowIsoRe

namespace GlobalTheory.PowIsoRe

theorem wchart_le_M {X Y Z : Scheme.{0}} (M : LB Z) (h : X ⟶ Y) (m : Y ⟶ Z) (j : Fin 1 → M.ι) :
    LB.wchart M (fun _ : Fin 1 => h ≫ m) j ≤
      LB.wchart (M.pull m) (fun _ : PUnit => h) (fun _ _ => j 0) := by
  intro x hx
  have hx0 := Set.mem_iInter.1 hx 0
  refine Set.mem_iInter.2 fun _ => ?_
  refine Set.mem_iInter.2 fun _ => ?_
  simpa using hx0

theorem wchart_le_L {X Z : Scheme.{0}} (L : LB Z) (f : X ⟶ Z) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => f) j ≤ LB.wchart L (fun _ : PUnit => f) (fun _ => j 0) := by
  intro x hx
  exact Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx 0

theorem exists_powIso {X Y Z₁ Z₂ : Scheme.{0}} (L : LB Z₁) (M : LB Z₂) (f : X ⟶ Z₁) (h : X ⟶ Y) (m : Y ⟶ Z₂)
    (k : ℕ) (w : LB.Gen (LB.div ((M.pull m).pull h) (L.pull f))) (hw : w.IsGen) :
    ∃ α : LB.Gen (LB.div (powPull M (h ≫ m) (k : ℤ)) (powPull L f (k : ℤ))), α.IsGen := by
  dsimp only [LB.Gen.IsGen, LB.div, LB.LinComb, LB.pull, powPull] at w hw ⊢
  have hle : ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      LB.wchart M (fun _ : Fin 1 => h ≫ m) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2 ≤
        LB.wchart (M.pull m) (fun _ : PUnit => h) (fun _ _ => p.1 0) ⊓
          LB.wchart L (fun _ : PUnit => f) (fun _ => p.2 0) := fun p =>
    inf_le_inf (wchart_le_M M h m p.1) (wchart_le_L L f p.2)
  dsimp only [LB.pull, LB.LinComb] at hle
  refine ⟨⟨fun p => (res (hle p) (w.s (fun _ _ => p.1 0, fun _ => p.2 0))) ^ k⟩, ?_⟩
  dsimp only
  intro p p'
  have e := congrArg (fun x => (res (inf_le_inf (hle p) (hle p')) x) ^ k)
    (hw (fun _ _ => p.1 0, fun _ => p.2 0) (fun _ _ => p'.1 0, fun _ => p'.2 0))
  simp only [map_mul, map_inv, map_pow, map_zpow, map_prod, res_res, pullU_res_pullU,
    Fin.prod_univ_one, Fintype.prod_unique, Fin.default_eq_zero, zpow_one, zpow_natCast, mul_pow, inv_pow] at e ⊢
  convert e using 5
  · exact (res_pull_comp h m (W := M.U (p.1 0) ⊓ M.U (p'.1 0))
      (V1 := LB.wchart M (fun _ : PUnit.{1} => m) (fun _ => p.1 0) ⊓ LB.wchart M (fun _ : PUnit.{1} => m) (fun _ => p'.1 0))
      (M.g (p.1 0) (p'.1 0)) _ _ _ _ _).symm
  · rfl
  · exact res_res' (U := f ⁻¹ᵁ (L.U (p.2 0) ⊓ L.U (p'.2 0))) (pullU f _ (L.g (p.2 0) (p'.2 0))) _ _ _ _

end GlobalTheory.PowIsoRe
