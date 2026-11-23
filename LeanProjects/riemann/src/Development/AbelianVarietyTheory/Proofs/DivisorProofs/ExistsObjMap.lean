import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.UPel.Pull

variable {F : Type} [Field F] [NumberField F] [IsCMField F]

def tateMoveP {D : Datum F} {p : ℕ} {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q']
    {act : 𝓞 F → Q → Q} {act' : 𝓞 F → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop}
    (Φ : Q' ≃* Q) (hact : ∀ c x, Φ (act' c x) = act c (Φ x)) (he : ∀ n x y c, e n (Φ x) (Φ y) c → e' n x y c)
    (I : TateIsoP D p k Q act e) : TateIsoP D p k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev := fun n a => Φ.symm (I.ev n a)
  add := fun n a b => by simp only [I.add, map_mul]
  lin := fun n c a => by
    apply Φ.injective
    rw [MulEquiv.apply_symm_apply, hact, MulEquiv.apply_symm_apply]
    exact I.lin n c a
  ker := fun n hn hp a => (map_eq_one_iff _ Φ.symm.injective).trans (I.ker n hn hp a)
  onto := fun n hn hp x => by
    rw [← map_eq_one_iff Φ Φ.injective, map_pow, I.onto n hn hp]
    exact exists_congr fun a => Φ.symm_apply_eq.symm
  tower := fun n m hn hm hp a => by rw [← map_pow, I.tower n m hn hm hp a]
  isom := fun n hn hp a b => he _ _ _ _ (by
    rw [Φ.apply_symm_apply, Φ.apply_symm_apply]
    exact I.isom n hn hp a b)

theorem exists_objMap : ∀ (F : Type) [Field F] [NumberField F] [IsCMField F] (D : GlobalTheory.UPel.Datum F) (p N : ℕ)
    (S T : Scheme.{0}) (s : S ⟶ Sp (D.OEp p)) (o : GlobalTheory.UPel.Obj D p N s) (t : T ⟶ S),
    ∃ o' : GlobalTheory.UPel.Obj D p N (t ≫ s), Nonempty (GlobalTheory.UPel.ObjMap o' o t) := by
  intro F _ _ _ D p N S T s o t
  have h := isGrpPullback_pullback o.A t
  obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := Out.proved_CubePullSt S T o.A _ (cubeMapOf h) o.PP o.cub
  let act' := OAct.pullback t o.A o.act
  have hact : ∀ a, (act'.act a).left ≫ pullback.fst o.A.hom t = pullback.fst o.A.hom t ≫ (o.act.act a).left :=
    fun a => pullback.lift_fst _ _ _
  have pa : ∀ {U : Over T} (x : U ⟶ (Over.pullback t).obj o.A) a,
      pushPt h.1.w (x ≫ act'.act a) = pushPt h.1.w x ≫ o.act.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  let PP' := (cubeMapOf h).rigLB o.PP hL hr
  have adj' : ∀ a, LBIso (cubeLB ((Over.pullback t).obj o.A)
      ![fst ((Over.pullback t).obj o.A) ((Over.pullback t).obj o.A) ≫ act'.act a,
        snd ((Over.pullback t).obj o.A) ((Over.pullback t).obj o.A)] PP'.L)
      (cubeLB ((Over.pullback t).obj o.A) ![fst ((Over.pullback t).obj o.A) ((Over.pullback t).obj o.A),
        snd ((Over.pullback t).obj o.A) ((Over.pullback t).obj o.A) ≫ act'.act (D.bar a)] PP'.L) := fun a => by
    let U := lift (pushPt h.1.w (fst ((Over.pullback t).obj o.A) ((Over.pullback t).obj o.A)))
      (pushPt h.1.w (snd ((Over.pullback t).obj o.A) ((Over.pullback t).obj o.A)))
    refine LBIso.chartPull (chartPullLinComb o.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
      (chartPullLinComb o.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (o.adj a)
    · fin_cases i
      · exact (pa _ a).trans (by simp [U])
      · simp [U]
    · fin_cases i
      · simp [U]
      · exact (pa _ _).trans (by simp [U])
  have prim' : LBIso PP'.L (cubeLB ((Over.pullback t).obj o.A) ![𝟙 ((Over.pullback t).obj o.A), act'.act D.w] PP'.L) := by
    let U := pushPt h.1.w (𝟙 ((Over.pullback t).obj o.A))
    refine LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o.PP.L _ U.left (Category.id_comp _))
      (chartPullLinComb o.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) o.prim
    fin_cases i
    · simp [U]
    · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
  obtain ⟨w, hw, -⟩ := hc'
  have hLi : LBIso PP'.L (o.PP.L.pull (pullback.fst o.A.hom t)) := ⟨w, hw⟩
  obtain ⟨hab, hamp, hk⟩ := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally S T o.A _ t
    _ o.PP.L PP'.L o.PP.isLB PP'.isLB o.ab h hLi
  refine ⟨{ A := (Over.pullback t).obj o.A
            ab := hab
            act := act'
            PP := PP'
            cub := c'
            sym := hs o.sym
            adj := adj'
            prim := prim'
            ample := hamp o.ample
            ktriv := hk o.ktriv
            eta := fun a => GlobalTheory.ObjPull.secPull h (o.eta a)
            eta_add := fun a c => by rw [o.eta_add, map_mul]
            eta_ker := fun a => by rw [o.eta_ker a, map_one]
            geom := fun k _ _ x β hx => ?_ },
    ⟨{ φ := pullback.fst o.A.hom t
       cart := h
       act := hact
       pol := hLi
       eta := fun a => GlobalTheory.ObjPull.secPull_left h _ }⟩⟩
  obtain ⟨⟨β', hβ', hdet⟩, I, hI⟩ := o.geom k (x ≫ t) β (by rw [Category.assoc]; exact hx)
  refine ⟨⟨β', hβ', fun σ => (GlobalTheory.LiePull.lieMult_pull _ S T o.A _ t _ o.act act' h hact k x σ _).2 (hdet σ)⟩,
    tateMoveP (GlobalTheory.ObjPull.pushEquiv h (Over.mk x)) (fun c g => ?_) (fun n g g' c hc => ?_) I, fun a => ?_⟩
  · apply Over.OverMorphism.ext
    show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
    rw [Category.assoc, hact, Category.assoc]
  · exact (GlobalTheory.weilIs_grpPullback_of_comm S T o.A _ t _ o.PP.L PP'.L o.PP.isLB PP'.isLB h hLi
      (Over.mk x) n g g' _ _ _ rfl rfl).2 hc
  · exact (MulEquiv.eq_symm_apply _).2 ((GlobalTheory.ObjPull.pushEquiv_secPull h _ _).trans (hI a))

end GlobalTheory.UPel.Pull
