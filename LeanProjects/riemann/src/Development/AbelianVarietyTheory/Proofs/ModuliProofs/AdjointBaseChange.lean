import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LbIsoLinComb
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFibreAct

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELPeriod

theorem adjoint_baseChange {B B' : Scheme.{0}} {G : Over B} {G' : Over B'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : B' ⟶ B} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB)
    (hL' : L'.IsLB) (h : IsGrpPullback G' G f φ) (hb : LBIso L' (L.pull φ)) {w wd : G ⟶ G} {w' wd' : G' ⟶ G'}
    (hw : w'.left ≫ φ = φ ≫ w.left) (hwd : wd'.left ≫ φ = φ ≫ wd.left)
    (ha : LBIso (cubeLB G ![fst G G ≫ w, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ wd] L)) :
    LBIso (cubeLB G' ![fst G' G' ≫ w', snd G' G'] L') (cubeLB G' ![fst G' G', snd G' G' ≫ wd'] L') := by
  have pa : ∀ {T : Over B'} (x : T ⟶ G'), pushPt h.1.w (x ≫ w') = pushPt h.1.w x ≫ w := fun x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hw, Category.assoc])
  have pd : ∀ {T : Over B'} (x : T ⟶ G'), pushPt h.1.w (x ≫ wd') = pushPt h.1.w x ≫ wd := fun x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hwd, Category.assoc])
  have hB : (L.pull φ).IsLB := pull_isLB hL φ
  have h₁ : LBIso (cubeLB G' ![fst G' G' ≫ w', snd G' G'] (L.pull φ))
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

def tateIsoMap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {k : Type} [Field k]
    {Q Q' : Type} [Group Q] [Group Q'] {act : 𝓞 E → Q → Q} {act' : 𝓞 E → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop}
    {e' : ℕ → Q' → Q' → kˣ → Prop} (I : TateIso D k Q act e) (ψ : Q ≃* Q')
    (ha : ∀ c y, ψ (act c y) = act' c (ψ y)) (he : ∀ n y y' c, e n y y' c → e' n (ψ y) (ψ y') c) :
    TateIso D k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev n x := ψ (I.ev n x)
  add n x y := by rw [I.add, map_mul]
  lin n c x := by rw [I.lin, ha]
  ker n hn x := by rw [← I.ker n hn, map_eq_one_iff ψ ψ.injective]
  onto n hn x := by
    obtain ⟨x, rfl⟩ := ψ.surjective x
    rw [← map_pow, map_eq_one_iff ψ ψ.injective, I.onto n hn]
    simp only [ψ.injective.eq_iff]
  tower n m hn hm x := by rw [← map_pow, I.tower n m hn hm]
  isom n hn x y := he _ _ _ _ (I.isom n hn x y)

theorem exists_act {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {o : Type}
    [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {em : o →+* ℂ} {a : J → 𝓞 E}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La} {ρ : o} {t : TObj g k J b (spMap em)} (h : PELClass D a bas ρ em t) :
    ∃ act : OAct (𝓞 E) t.pol.A, (∀ j, act.act (a j) = t.act j) ∧ DetCond D act (𝟙 (Sp ℂ)) (em ρ) ∧
      (∀ c, LBIso (cubeLB t.pol.A ![fst t.pol.A t.pol.A ≫ act.act c, snd t.pol.A t.pol.A] t.pol.L)
        (cubeLB t.pol.A ![fst t.pol.A t.pol.A, snd t.pol.A t.pol.A ≫ act.act (H.bar c)] t.pol.L)) ∧
      ∃ I : TateIso D ℂ (Over.mk (𝟙 (Sp ℂ)) ⟶ t.pol.A) (fun c y => y ≫ act.act c)
          (fun n y y' c => Out.WeilIs t.pol.A t.pol.L n y y' (unitOn c)),
        (I.ζ k : ℂ) = em b.ζ ∧ ∀ i, (I.ev k (bas (Pi.single i 1))).left = (t.pt i).left := by
  obtain ⟨τ, φ, hφ, hL, hj, hd⟩ := h
  haveI := hφ
  haveI := t.ab.comm
  have hi : IsGrpPullback t.A τ.G (𝟙 _) φ.inv.left := GlobalTheory.FibreAct.isGrpPullback_of_iso φ.inv
  have e₁ : φ.inv.left ≫ φ.hom.left = 𝟙 _ := by rw [← Over.comp_left, φ.inv_hom_id, Over.id_left]
  have hL' : LBIso t.L (τ.PP.L.pull φ.inv.left) :=
    LBIso.chartPull (chartPullSec t.L _ _ e₁) (chartPullPull τ.PP.L _ _ rfl) hL.symm
  obtain ⟨act, hact⟩ := GlobalTheory.FibreAct.exists_lift_act hi τ.act
  have hact' : ∀ c, act.act c ≫ φ.inv = φ.inv ≫ τ.act.act c := fun c => Over.OverMorphism.ext (hact c)
  have hact'' : ∀ c, τ.act.act c ≫ φ.hom = φ.hom ≫ act.act c := fun c => by
    rw [← Iso.inv_comp_eq, ← Category.assoc, ← hact', Category.assoc, φ.inv_hom_id, Category.comp_id]
  obtain ⟨hdet, I, hζ, hpt⟩ := hd ℂ (𝟙 _) em (Category.id_comp _)
  refine ⟨act, fun j => ?_, fun σ => ?_, fun c => ?_, ?_⟩
  · exact (cancel_epi φ.hom).1 ((hact'' _).symm.trans (hj j))
  · have L : ∀ n, LieMult act (𝟙 _) σ n ↔ LieMult τ.act (𝟙 _) σ n := fun n => by
      rw [GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ hi hact ℂ _ σ n, Category.comp_id]
    exact ⟨fun hs => (L _).2 ((hdet σ).1 hs), fun hs => (L _).2 ((hdet σ).2 hs)⟩
  · exact adjoint_baseChange τ.PP.isLB t.isLB hi hL' (hact c) (hact _) (τ.adj c)
  · let ψ : (Over.mk (𝟙 (Sp ℂ)) ⟶ τ.G) ≃* (Over.mk (𝟙 (Sp ℂ)) ⟶ t.A) :=
      { toFun := fun y => y ≫ φ.hom
        invFun := fun y => y ≫ φ.inv
        left_inv := fun y => by simp
        right_inv := fun y => by simp
        map_mul' := fun y y' => MonObj.mul_comp _ _ _ }
    have W : ∀ (s : Sp ℂ ⟶ Sp ℂ), 𝟙 (Sp ℂ) ≫ 𝟙 (Sp ℂ) = s → ∀ (n : ℤ) (x y : Over.mk (𝟙 (Sp ℂ)) ⟶ t.A)
        (x₀ y₀ : Over.mk s ⟶ τ.G) (c : Γ(Sp ℂ, ⊤)ˣ), x₀.left = x.left ≫ φ.inv.left →
        y₀.left = y.left ≫ φ.inv.left → Out.WeilIs τ.G τ.PP.L n x₀ y₀ c → Out.WeilIs t.A t.L n x y c := by
      rintro _ rfl n x y x₀ y₀ c hx hy
      exact (GlobalTheory.weilIs_grpPullback_of_comm _ _ τ.G t.A _ _ _ _ τ.PP.isLB t.isLB hi hL' (Over.mk (𝟙 _)) n x y
        x₀ y₀ c hx hy).2
    have hψ : ∀ y : Over.mk (𝟙 (Sp ℂ)) ⟶ τ.G, y.left = (ψ y).left ≫ φ.inv.left := fun y => by
      show y.left = ((y ≫ φ.hom) ≫ φ.inv).left
      simp
    refine ⟨tateIsoMap I ψ (fun c y => ?_) (fun n y y' c => W _ (Category.id_comp _) n _ _ y y' _ (hψ y) (hψ y')),
      hζ, fun i => ?_⟩
    · show (y ≫ τ.act.act c) ≫ φ.hom = (y ≫ φ.hom) ≫ act.act c
      rw [Category.assoc, hact'', Category.assoc]
    · exact (congrArg (fun z => z.left) (hpt i)).trans (Category.id_comp _)

end GlobalTheory.PELPeriod
