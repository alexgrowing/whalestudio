import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpNaturality
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot
open GlobalTheory.LB (resG_resG resG_self fun_ext_of_cover exists_fun_of_cover)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover exists_sec_of_cover)

namespace GlobalTheory.LineQuot.ExMap

variable {T : Scheme.{0}} {L Q : T.Modules}

def HBij (a : L ⟶ Q) (W : T.Opens) : Prop := ∀ V : T.Opens, V ≤ W → Function.Bijective (a.app V)

theorem HBij.mono {a : L ⟶ Q} {W W' : T.Opens} (h : HBij a W) (hW : W' ≤ W) : HBij a W' :=
  fun V hV => h V (hV.trans hW)

theorem hbij_iSup (a : L ⟶ Q) {κ : Type} (W : κ → T.Opens) (h : ∀ k, HBij a (W k)) :
    HBij a (⨆ k, W k) := by
  intro V hV
  have hc : V ≤ ⨆ k, V ⊓ W k := by rw [← inf_iSup_eq]; exact le_inf le_rfl hV
  constructor
  · intro s t e
    refine sec_ext_of_cover (fun k => V ⊓ W k) (fun _ => inf_le_left) hc fun k =>
      (h k _ inf_le_right).1 ?_
    rw [app_resM, app_resM, e]
  · intro t
    choose s hs using fun k => (h k _ (inf_le_right : V ⊓ W k ≤ W k)).2
      (resM Q (inf_le_left : V ⊓ W k ≤ V) t)
    obtain ⟨r, hr⟩ := exists_sec_of_cover (fun k => V ⊓ W k) (fun _ => inf_le_left) hc s fun k l =>
        (h k _ (inf_le_left.trans inf_le_right)).1 (by
          rw [app_resM, app_resM, hs, hs, resM_resM, resM_resM])
    refine ⟨r, sec_ext_of_cover (fun k => V ⊓ W k) (fun _ => inf_le_left) hc fun k => ?_⟩
    rw [← app_resM, hr, hs]

def good (a : L ⟶ Q) : T.Opens := ⨆ W : {W : T.Opens // HBij a W}, W.1

theorem hbij_good (a : L ⟶ Q) : HBij a (good a) := hbij_iSup a _ fun W => W.2

theorem le_good {a : L ⟶ Q} {W : T.Opens} (h : HBij a W) : W ≤ good a :=
  le_iSup (fun W : {W : T.Opens // HBij a W} => W.1) ⟨W, h⟩

def IsRatio (a b : L ⟶ Q) (V : T.Opens) (c : Γ(T, V)) : Prop :=
  ∀ (V' : T.Opens) (h : V' ≤ V) (t : Γ(L, V')), b.app V' t = resG T h c • a.app V' t

theorem IsRatio.res {a b : L ⟶ Q} {V : T.Opens} {c : Γ(T, V)} (hc : IsRatio a b V c) {W : T.Opens}
    (h : W ≤ V) : IsRatio a b W (resG T h c) := fun V' h' t => by
  rw [resG_resG]; exact hc V' _ t

theorem smul_ext (hL : IsVB L 1) {V : T.Opens} {c c' : Γ(T, V)}
    (h : ∀ (V' : T.Opens) (h' : V' ≤ V) (t : Γ(L, V')), resG T h' c • t = resG T h' c' • t) :
    c = c' := by
  choose O e _ hx hO he using fun x : V => hL.exists_affine (V := V) x.2
  refine fun_ext_of_cover O hO (fun x hx' => Opens.mem_iSup.2 ⟨⟨x, hx'⟩, hx _⟩) fun x => ?_
  have := (he x (O x) le_rfl).1 (a₁ := fun _ => resG T (hO x) c) (a₂ := fun _ => resG T (hO x) c') (by
    simp only [Fintype.linearCombination_apply, Fin.sum_univ_one]
    exact h _ _ _)
  exact congrFun this 0

theorem isRatio_unique (hL : IsVB L 1) {a b : L ⟶ Q} {V : T.Opens} (hV : HBij a V) {c c' : Γ(T, V)}
    (hc : IsRatio a b V c) (hc' : IsRatio a b V c') : c = c' :=
  smul_ext hL fun V' h t => (hV V' h).1 (by
    rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, ← hc V' h t, ← hc' V' h t])

theorem exists_isRatio (hL : IsVB L 1) {a : L ⟶ Q} (b : L ⟶ Q) {U : T.Opens} (hU : HBij a U) :
    ∃ c : Γ(T, U), IsRatio a b U c := by
  have loc : ∀ x : U, ∃ (O : T.Opens) (_ : (x : T) ∈ O) (hO : O ≤ U) (c : Γ(T, O)), IsRatio a b O c := by
    intro x
    obtain ⟨O, e, -, hx, hO, he⟩ := hL.exists_affine (V := U) x.2
    obtain ⟨u, hu⟩ := (hU O hO).2 (b.app O (e 0))
    obtain ⟨d, hd⟩ := (he O le_rfl).2 u
    simp only [Fintype.linearCombination_apply, Fin.sum_univ_one, resM_self] at hd
    refine ⟨O, hx, hO, d 0, fun V' h t => ?_⟩
    obtain ⟨g, hg⟩ := (he V' h).2 t
    simp only [Fintype.linearCombination_apply, Fin.sum_univ_one] at hg
    subst hg
    rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, app_resM, app_resM, ← hu, ← hd,
      Scheme.Modules.Hom.app_smul, resM_smul, smul_comm]
  choose O hx hO c hc using loc
  have hcov : U ≤ ⨆ x, O x := fun x hx' => Opens.mem_iSup.2 ⟨⟨x, hx'⟩, hx _⟩
  obtain ⟨r, hr⟩ := exists_fun_of_cover O hO hcov c fun x y =>
    isRatio_unique hL (hU.mono (inf_le_left.trans (hO x))) ((hc x).res _) ((hc y).res _)
  refine ⟨r, fun V' h t => ?_⟩
  have hc' : V' ≤ ⨆ x, V' ⊓ O x := by rw [← inf_iSup_eq]; exact le_inf le_rfl (h.trans hcov)
  refine sec_ext_of_cover (fun x => V' ⊓ O x) (fun _ => inf_le_left) hc' fun x => ?_
  rw [← app_resM, resM_smul, ← app_resM, resG_resG,
    hc x _ (inf_le_right : V' ⊓ O x ≤ O x), ← hr x, resG_resG]

end GlobalTheory.LineQuot.ExMap

namespace GlobalTheory.LineQuot.ExMap

variable {T : Scheme.{0}} {L Q : T.Modules}

theorem isUnit_resG_basicOpen {V : T.Opens} (c : Γ(T, V)) {W : T.Opens} (h : W ≤ T.basicOpen c) :
    IsUnit (resG T (h.trans (T.basicOpen_le c)) c) := by
  have := (T.toRingedSpace.isUnit_res_basicOpen c).map (resG T h)
  exact (congrArg IsUnit (resG_resG (T.basicOpen_le c) h c)).mp this

variable {N : ℕ} (hL : IsVB L 1) (s : Fin (N + 1) → (L ⟶ Q))

def ratio (i j : Fin (N + 1)) : Γ(T, good (s i)) := (exists_isRatio hL (s j) (hbij_good (s i))).choose

theorem isRatio_ratio (i j : Fin (N + 1)) : IsRatio (s i) (s j) (good (s i)) (ratio hL s i j) :=
  (exists_isRatio hL (s j) (hbij_good (s i))).choose_spec

theorem isCoordFamily (hs : Gen s) : ProjSpace.IsCoordFamily (fun i => good (s i)) (ratio hL s) where
  cover := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨j, W, hx, hW⟩ := hs x
    exact Opens.mem_iSup.2 ⟨j, le_good hW hx⟩
  self i := isRatio_unique hL (hbij_good (s i)) (isRatio_ratio hL s i i)
    fun V' h t => by rw [map_one, one_smul]
  mul i j k := by
    refine isRatio_unique hL ((hbij_good (s i)).mono inf_le_left) ?_ ((isRatio_ratio hL s i k).res _)
    intro V' h t
    rw [(isRatio_ratio hL s j k) V' (h.trans inf_le_right) t,
      (isRatio_ratio hL s i j) V' (h.trans inf_le_left) t, smul_smul, map_mul, resG_resG, resG_resG,
      mul_comm]
  basicOpen_le i j := by
    refine le_good fun V hV => ?_
    have hV' : V ≤ good (s i) := hV.trans (T.basicOpen_le _)
    have e : ⇑((s j).app V) = (fun y => resG T hV' (ratio hL s i j) • y) ∘ ⇑((s i).app V) :=
      funext fun t => isRatio_ratio hL s i j V hV' t
    rw [e]
    exact (isUnit_resG_basicOpen _ hV).smul_bijective.comp (hbij_good (s i) V hV')

end GlobalTheory.LineQuot.ExMap

open GlobalTheory.LineQuot.ExMap in

theorem GlobalTheory.LineQuot.exists_toPSpace : ∀ (k : Type) [CommRing k] (N : ℕ) (T : Scheme.{0}) (f : T ⟶ Sp k)
    (L Q : T.Modules) (s : Fin (N + 1) → (L ⟶ Q)), IsVB L 1 → IsVB Q 1 → Gen s →
    ∃ φ : T ⟶ PSpace k N, φ ≫ PSpace.str k N = f ∧ Rel φ s := by
  intro k _ N T f L Q s hL _ hs
  let H := isCoordFamily hL s hs
  refine ⟨H.toHom f, H.toHom_str f, fun i j W h t => ?_⟩
  have hW : W ≤ good (s i) := h.trans (H.toHom_preimage f i).le
  rw [← ProjSpace.resG_pullRatio (hi := H.le_toHom_preimage f i) hW, H.pullRatio_toHom f i j]
  exact isRatio_ratio hL s i j W hW t
