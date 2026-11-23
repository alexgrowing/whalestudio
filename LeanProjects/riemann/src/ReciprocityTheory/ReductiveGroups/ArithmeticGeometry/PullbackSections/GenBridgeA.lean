import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsSecNeObj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

section Germs

variable {X Y Y' Z : Scheme.{0}}

theorem gs_comp_stalk (r : Z ⟶ Y) (ψ : Y ⟶ X) (z : Z) (V : X.Opens) (hV : ψ (r z) ∈ V) (b : Γ(X, V)) :
    gs (r ≫ ψ) z V b = (r.stalkMap z).hom (gs ψ (r z) V b) := by
  rw [← gs_pull r ψ z V hV b]
  have h1 : r z ∈ ψ ⁻¹ᵁ V := hV
  simp only [gs, dif_pos hV, dif_pos h1]
  exact (Scheme.Hom.germ_stalkMap_apply r (ψ ⁻¹ᵁ V) z h1 _).symm

theorem gm_of_id (r : Z ⟶ Y) (ψ : Y ⟶ X) (z : Z) {U : Y.Opens} {V : X.Opens} (hU : r z ∈ U)
    (hV : ψ (r z) ∈ V) (a : Γ(Y, U)ˣ) (b : Γ(X, V)ˣ) (h : gm (𝟙 Y) (r z) U a = gm ψ (r z) V b) :
    gm r z U a = gm (r ≫ ψ) z V b := by
  apply Units.ext
  rw [← gs_unit r z U hU a, ← gs_unit (r ≫ ψ) z V (by simpa using hV) b]
  have e1 := gs_comp_stalk r (𝟙 Y) z U (by simpa using hU) a.val
  have e2 := gs_comp_stalk r ψ z V hV b.val
  rw [Category.comp_id] at e1
  rw [e1, e2, gs_unit (𝟙 Y) (r z) U (by simpa using hU) a, gs_unit ψ (r z) V hV b, h]

theorem gs_of_id (r : Z ⟶ Y) (ψ : Y ⟶ X) (z : Z) {U : Y.Opens} {V : X.Opens} (hU : r z ∈ U)
    (hV : ψ (r z) ∈ V) (a : Γ(Y, U)) (b : Γ(X, V)) (h : gs (𝟙 Y) (r z) U a = gs ψ (r z) V b) :
    gs r z U a = gs (r ≫ ψ) z V b := by
  have e1 := gs_comp_stalk r (𝟙 Y) z U (by simpa using hU) a
  have e2 := gs_comp_stalk r ψ z V hV b
  rw [Category.comp_id] at e1
  rw [e1, e2, h]

structure PullOf (L : LB X) (ψ : Y ⟶ X) (A : LB Y) where
  c : A.ι → L.ι
  d : L.ι → A.ι
  cd : ∀ l, c (d l) = l
  mem : ∀ i (y : Y), y ∈ A.U i ↔ ψ y ∈ L.U (c i)
  g : ∀ (y : Y) i j, y ∈ A.U i → y ∈ A.U j →
    gm (𝟙 Y) y (A.U i ⊓ A.U j) (A.g i j) = gm ψ y (L.U (c i) ⊓ L.U (c j)) (L.g (c i) (c j))

def PullOf.lin {K : Type} [Fintype K] [Unique K] (L : LB X) (ψ : Y ⟶ X) :
    PullOf L ψ (LB.LinComb L (fun _ : K => ψ) (fun _ => 1)) where
  c J := J default
  d l := fun _ => l
  cd _ := rfl
  mem J y := ⟨fun hy => Set.mem_iInter.1 hy default,
    fun hy => Set.mem_iInter.2 fun k => by rw [Unique.eq_default k]; exact hy⟩
  g y J J' hJ hJ' := (gm_linComb L _ _ (𝟙 Y) y J J' hJ hJ').trans (by
    rw [Fintype.prod_unique, zpow_one, Category.id_comp])

def PullOf.pull {L : LB X} {ψ : Y ⟶ X} {A : LB Y} (pA : PullOf L ψ A) (F : Y' ⟶ Y) :
    PullOf L (F ≫ ψ) (A.pull F) where
  c J := pA.c (J PUnit.unit)
  d l := fun _ => pA.d l
  cd l := pA.cd l
  mem J y := mem_pull.trans (pA.mem _ (F y))
  g y J J' hJ hJ' := by
    have h1 := gm_pull_g A F (𝟙 Y') y J J' hJ hJ'
    rw [Category.id_comp] at h1
    rw [h1]
    have m1 : F y ∈ A.U (J PUnit.unit) := mem_pull.1 hJ
    have m2 : F y ∈ A.U (J' PUnit.unit) := mem_pull.1 hJ'
    exact gm_of_id (U := A.U (J PUnit.unit) ⊓ A.U (J' PUnit.unit))
      (V := L.U (pA.c (J PUnit.unit)) ⊓ L.U (pA.c (J' PUnit.unit))) F ψ y ⟨m1, m2⟩
      ⟨(pA.mem _ _).1 m1, (pA.mem _ _).1 m2⟩ _ _ (pA.g (F y) _ _ m1 m2)

theorem PullOf.cp_le {L : LB X} {ψ : Y ⟶ X} {ψ' : Y' ⟶ X} {A : LB Y} {A' : LB Y'} (pA : PullOf L ψ A)
    (pA' : PullOf L ψ' A') (h : Y' ⟶ Y) (e : h ≫ ψ = ψ') (i : A'.ι) :
    A'.U i ≤ h ⁻¹ᵁ A.U (pA.d (pA'.c i)) := by
  subst e
  intro y hy
  have h1 := (pA'.mem i y).1 hy
  show h y ∈ A.U (pA.d (pA'.c i))
  rw [pA.mem, pA.cd]
  simpa using h1

def PullOf.cp {L : LB X} {ψ : Y ⟶ X} {ψ' : Y' ⟶ X} {A : LB Y} {A' : LB Y'} (pA : PullOf L ψ A)
    (pA' : PullOf L ψ' A') (h : Y' ⟶ Y) (e : h ≫ ψ = ψ') : ChartPull A' A h where
  idx i := pA.d (pA'.c i)
  le := pA.cp_le pA' h e
  g y i j hi hj := by
    have hi' := pA.cp_le pA' h e i hi
    have hj' := pA.cp_le pA' h e j hj
    subst e
    rw [pA'.g y i j hi hj]
    have hg := pA.g (h y) _ _ hi' hj'
    rw [pA.cd, pA.cd] at hg
    have hi2 := (pA.mem _ _).1 hi'
    have hj2 := (pA.mem _ _).1 hj'
    rw [pA.cd] at hi2 hj2
    exact (gm_of_id (U := A.U (pA.d (pA'.c i)) ⊓ A.U (pA.d (pA'.c j)))
      (V := L.U (pA'.c i) ⊓ L.U (pA'.c j)) h ψ y ⟨hi', hj'⟩ ⟨hi2, hj2⟩ _ _ hg).symm

theorem cpSame_le {K : Type} [Fintype K] (L : LB X) (φ : K → (Y ⟶ X)) (φ' : K → (Y' ⟶ X)) (h : Y' ⟶ Y)
    (e : ∀ k, h ≫ φ k = φ' k) (j : K → L.ι) : LB.wchart L φ' j ≤ h ⁻¹ᵁ LB.wchart L φ j := by
  intro y hy
  have hy' : ∀ k, (φ' k).base y ∈ (L.U (j k) : Set X) := Set.mem_iInter.1 hy
  refine Set.mem_iInter.2 fun k => ?_
  have h2 := hy' k
  rw [← e k] at h2
  simpa using h2

def cpSame {K : Type} [Fintype K] (L : LB X) (φ : K → (Y ⟶ X)) (φ' : K → (Y' ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y)
    (e : ∀ k, h ≫ φ k = φ' k) : ChartPull (LB.LinComb L φ' ε) (LB.LinComb L φ ε) h where
  idx j := j
  le := cpSame_le L φ φ' h e
  g y j j' hj hj' :=
    (gm_linComb L φ' ε (𝟙 Y') y j j' hj hj').trans ((Finset.prod_congr rfl fun k _ => by
      rw [Category.id_comp, ← e k]).trans
      (gm_linComb L φ ε h y j j' (cpSame_le L φ φ' h e j hj) (cpSame_le L φ φ' h e j' hj')).symm)

def secCP {A' : LB Y'} {A : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h) (s : LB.Sec A) : LB.Sec A' where
  f i := (Y'.presheaf.map (homOfLE (a.le i)).op).hom ((h.app (A.U (a.idx i))).hom (s.f (a.idx i)))
  compat i j := fn_ext fun y hy => by
    have e : ∀ k, y ∈ A'.U k → gs (𝟙 Y') y (A'.U k)
        ((Y'.presheaf.map (homOfLE (a.le k)).op).hom ((h.app (A.U (a.idx k))).hom (s.f (a.idx k)))) =
          gs h y _ (s.f (a.idx k)) := fun k hk =>
      (gs_res (𝟙 Y') y (a.le k) hk _).trans ((gs_pull (𝟙 Y') h y _ (a.le k hk) _).trans (by rw [Category.id_comp]))
    rw [gs_res (𝟙 Y') y inf_le_left hy, e i hy.1, gs_mul (𝟙 Y') y _ hy, gs_res (𝟙 Y') y inf_le_right hy, e j hy.2,
      gs_unit (𝟙 Y') y _ hy, a.g y i j hy.1 hy.2]
    exact gs_compat s h y (a.le i hy.1) (a.le j hy.2)

theorem gs_secCP {A' : LB Y'} {A : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h) (s : LB.Sec A) (r : Z ⟶ Y') (z : Z)
    (i : A'.ι) (hz : r z ∈ A'.U i) :
    gs r z (A'.U i) ((secCP a s).f i) = gs (r ≫ h) z (A.U (a.idx i)) (s.f (a.idx i)) :=
  (gs_res r z (a.le i) hz _).trans (gs_pull r h z _ (a.le i hz) _)

end Germs

section Sab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def sabT (hC : ReciprocityTheory.ChartRestriction.G.Out.CubePullSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : SAB H S' :=
  have h := isGrpPullback_pullback t.G f
  have P := hC S S' t.G _ (cubeMapOf h) t.PP t.cub
  have hact : ∀ a, ((OAct.pullback f t.G t.act).act a).left ≫ pullback.fst t.G.hom f =
      pullback.fst t.G.hom f ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ (Over.pullback f).obj t.G) a,
      pushPt h.1.w (x ≫ (OAct.pullback f t.G t.act).act a) = pushPt h.1.w x ≫ t.act.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  ⟨(Over.pullback f).obj t.G, IsSemiAbelian.pullback f t.G t.semi, OAct.pullback f t.G t.act,
    (cubeMapOf h).rigLB t.PP P.choose P.choose_spec.choose, P.choose_spec.choose_spec.1.choose,
    P.choose_spec.choose_spec.2 t.sym, fun a => by
      let U := lift (pushPt h.1.w (fst ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
        (pushPt h.1.w (snd ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
      refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
        (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
      · fin_cases i
        · exact (pa _ a).trans (by simp [U])
        · simp [U]
      · fin_cases i
        · simp [U]
        · exact (pa _ _).trans (by simp [U]), by
      let U := pushPt h.1.w (𝟙 ((Over.pullback f).obj t.G))
      refine LBIso.chartPull (chartPullPull t.PP.L _ U.left (Category.id_comp _))
        (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
      fin_cases i
      · simp [U]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)⟩

def sabM (hC : ReciprocityTheory.ChartRestriction.G.Out.CubePullSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
    SABMap (sabT hC f t) t f :=
  have h := isGrpPullback_pullback t.G f
  have P := hC S S' t.G _ (cubeMapOf h) t.PP t.cub
  ⟨cubeMapOf h, h, rfl, fun a => pullback.lift_fst _ _ _, P.choose_spec.choose_spec.1.choose_spec⟩

theorem sabT_L (hC : ReciprocityTheory.ChartRestriction.G.Out.CubePullSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
    (sabT hC f t).PP.L = t.PP.L.pull (pullback.fst t.G.hom f) := rfl

theorem sabM_φ (hC : ReciprocityTheory.ChartRestriction.G.Out.CubePullSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
    (sabM hC f t).φ = pullback.fst t.G.hom f := rfl

theorem sabT_hom (hC : ReciprocityTheory.ChartRestriction.G.Out.CubePullSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
    (sabT hC f t).G.hom = pullback.snd t.G.hom f := rfl

end Sab

end ReciprocityTheory.ChartRestriction.G.PullbackSections
