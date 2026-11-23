import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LbIsoLinComb

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SymBaseChange

variable {B B' : Scheme.{0}} {G : Over B} {G' : Over B'} [GrpObj G] [GrpObj G'] {f : B' ⟶ B} {φ : G'.left ⟶ G.left}

theorem pushPt_injective (h : IsGrpPullback G' G f φ) {T : Over B'} {x y : T ⟶ G'}
    (e : pushPt h.1.w x = pushPt h.1.w y) : x = y := by
  apply Over.OverMorphism.ext
  apply h.1.hom_ext
  · exact congrArg (fun z => z.left) e
  · rw [Over.w, Over.w]

theorem exists_endo (h : IsGrpPullback G' G f φ) (w : G ⟶ G) [IsMonHom w] :
    ∃ w' : G' ⟶ G', IsMonHom w' ∧ ∀ {T : Over B'} (x : T ⟶ G'), pushPt h.1.w (x ≫ w') = pushPt h.1.w x ≫ w := by
  let w' : G' ⟶ G' := Over.homMk (h.1.lift (φ ≫ w.left) G'.hom (by rw [Category.assoc, Over.w, h.1.w]))
    (h.1.lift_snd _ _ _)
  have hw : w'.left ≫ φ = φ ≫ w.left := h.1.lift_fst _ _ _
  have pa : ∀ {T : Over B'} (x : T ⟶ G'), pushPt h.1.w (x ≫ w') = pushPt h.1.w x ≫ w := fun x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hw, Category.assoc])
  have mul : ∀ (T : Over B') (x y : T ⟶ G'), (x * y) ≫ w' = (x ≫ w') * (y ≫ w') := by
    intro T x y
    apply pushPt_injective h
    have a : pushPt h.1.w (x * y) = pushPt h.1.w x * pushPt h.1.w y := map_mul (pushHom h T) x y
    have b : pushPt h.1.w ((x ≫ w') * (y ≫ w')) = pushPt h.1.w (x ≫ w') * pushPt h.1.w (y ≫ w') :=
      map_mul (pushHom h T) _ _
    rw [pa, a, b, pa, pa, MonObj.mul_comp]
  refine ⟨w', ⟨?_, ?_⟩, pa⟩
  · have h := mul (𝟙_ _) 1 1
    rw [_root_.mul_one] at h
    have h' : (1 : 𝟙_ (Over B') ⟶ G') ≫ w' = 1 := mul_eq_left.1 h.symm
    simpa [Hom.one_def] using h'
  · have h := mul (G' ⊗ G') (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]; congr 1

theorem hypS_baseChange : ∀ (B B' : Scheme.{0}) (G : Over B) (G' : Over B') [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (f : B' ⟶ B) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → HypS G L → HypS G' L' := by
  intro B B' G G' _ _ _ _ f φ L L' hL hL' h hb ⟨w, wd, hw, hwd, hs, hp, ha⟩
  obtain ⟨w', hw', pa⟩ := exists_endo h w
  obtain ⟨wd', hwd', pd⟩ := exists_endo h wd
  have hB : (L.pull φ).IsLB := pull_isLB hL φ
  refine ⟨w', wd', hw', hwd', ?_, ?_, ?_⟩
  · apply pushPt_injective h
    have b : pushPt h.1.w (w' * wd') = pushPt h.1.w w' * pushPt h.1.w wd' := map_mul (pushHom h G') _ _
    have c := pa (𝟙 G')
    have d := pd (𝟙 G')
    rw [Category.id_comp] at c d
    rw [b, c, d, ← MonObj.comp_mul, hs, Category.comp_id]
  · have h₁ : LBIso (L.pull φ) (cubeLB G' ![𝟙 G', w'] (L.pull φ)) := by
      let U := pushPt h.1.w (𝟙 G')
      refine LBIso.chartPull (chartPullPull L _ U.left (Category.id_comp _))
        (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) hp
      fin_cases i
      · simp [U]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _)
    have h₂ : LBIso (cubeLB G' ![𝟙 G', w'] (L.pull φ)) (cubeLB G' ![𝟙 G', w'] L') :=
      GlobalTheory.PowPrimitive.lbIso_linComb hb.symm _ _
    exact LBIso.trans hL' hB (DVR.linComb_isLB L' hL' _ _) hb
      (LBIso.trans hB (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB L' hL' _ _) h₁ h₂)
  · have h₁ : LBIso (cubeLB G' ![fst G' G' ≫ w', snd G' G'] (L.pull φ))
        (cubeLB G' ![fst G' G', snd G' G' ≫ wd'] (L.pull φ)) := by
      let U := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))
      refine LBIso.chartPull (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
        (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) ha
      · fin_cases i
        · exact (pa _).trans (by simp [U])
        · simp [U]
      · fin_cases i
        · simp [U]
        · exact (pd _).trans (by simp [U])
    exact LBIso.trans (DVR.linComb_isLB L' hL' _ _) (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB L' hL' _ _)
      (GlobalTheory.PowPrimitive.lbIso_linComb hb _ _)
      (LBIso.trans (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB L' hL' _ _) h₁
        (GlobalTheory.PowPrimitive.lbIso_linComb hb.symm _ _))

end GlobalTheory.SymBaseChange
