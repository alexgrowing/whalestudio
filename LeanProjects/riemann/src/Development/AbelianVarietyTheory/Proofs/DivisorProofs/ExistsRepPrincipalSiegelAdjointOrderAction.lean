import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointActionsOrderFiniteUnramifiedSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyExistsUniqueClassifySchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectOddLevelRigid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelFamilyCyclotomicAwayOddLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverCompOfIsFiniteNoetherianBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyNoetherianOfIsQProjOverNoeth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothProjectiveStalkFactorial
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SiegPairPBNonempty

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActSieg

section Pull

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
  {φ : A'.left ⟶ A.left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}

theorem one_left (h : IsGrpPullback A' A f φ) : (1 : A' ⟶ A').left ≫ φ = φ ≫ (1 : A ⟶ A).left := by
  have e : (1 : A' ⟶ A').left ≫ φ = (1 : Over.mk (A'.hom ≫ f) ⟶ A).left :=
    congrArg (fun q => q.left) (map_one (pushHom h A'))
  rw [e, Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, Over.toUnit_left, Over.toUnit_left,
    ← Category.assoc, h.1.w]
  rfl

theorem lift_one_id (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) :
    (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (1 : A ⟶ A) (𝟙 A)).left := by
  have := GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (φ ≫ A.hom)) (T' := A') (𝟙 A'.left) (1 : A' ⟶ A') (𝟙 A')
    (Z := A) φ (1 : A ⟶ A) (𝟙 A) (by exact (Category.id_comp _).trans (one_left h)) (by simp)
  exact (Category.id_comp _).symm.trans this

theorem lift_id_one (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) :
    (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ₂ = φ ≫ (lift (𝟙 A) (1 : A ⟶ A)).left := by
  have := GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (φ ≫ A.hom)) (T' := A') (𝟙 A'.left) (𝟙 A') (1 : A' ⟶ A')
    (Z := A) φ (𝟙 A) (1 : A ⟶ A) (by simp) (by exact (Category.id_comp _).trans (one_left h))
  exact (Category.id_comp _).symm.trans this

theorem lift_swap (sq : IsSquare φ φ₂) :
    (lift (snd A' A') (fst A' A')).left ≫ φ₂ = φ₂ ≫ (lift (snd A A) (fst A A)).left := by
  have := GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (φ₂ ≫ (A ⊗ A).hom)) (T' := A' ⊗ A') (𝟙 _) (snd A' A') (fst A' A')
    (Z := A ⊗ A) φ₂ (snd A A) (fst A A) (by exact (Category.id_comp _).trans sq.2.symm)
    (by exact (Category.id_comp _).trans sq.1.symm)
  exact (Category.id_comp _).symm.trans this

end Pull

section Obj

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B}

def onPull (c : SiegPre h M ζ s) (A' : Over S') [GrpObj A'] (φ : A'.left ⟶ c.A.left)
    (φ₂ : (A' ⊗ A').left ⟶ (c.A ⊗ c.A).left) (pb : IsGrpPullback A' c.A f φ) (sq : IsSquare φ φ₂) :
    SiegPre h M ζ (f ≫ s) :=
  haveI : IsCommMonObj A' := (GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback c.ab pb).comm
  { A := A'
    ab := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback c.ab pb
    P := c.P.pull φ₂
    isLB := pull_isLB c.isLB φ₂
    rig₁ := by
      obtain ⟨t, ht⟩ := c.rig₁
      exact gen_chartPull (chartPullLinComb c.P φ₂ _ _ _ φ fun _ => lift_one_id pb sq) t ht
    rig₂ := by
      obtain ⟨t, ht⟩ := c.rig₂
      exact gen_chartPull (chartPullLinComb c.P φ₂ _ _ _ φ fun _ => lift_id_one pb sq) t ht
    symm := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull c.P _ _ rfl) (chartPullLinComb c.P _ _ _ _ φ₂ fun _ => lift_swap sq) c.symm
    lev := fun a => GlobalTheory.SiegelPull.secPull pb (c.lev a)
    lev_add := fun a b => GlobalTheory.SiegelPull.push_injective pb _ (by
      rw [map_mul, GlobalTheory.SiegelPull.push_secPull', GlobalTheory.SiegelPull.push_secPull', GlobalTheory.SiegelPull.push_secPull', c.lev_add, MonObj.comp_mul])
    lev_tors := fun a => GlobalTheory.SiegelPull.push_injective pb _ (by
      rw [map_pow, map_one, GlobalTheory.SiegelPull.push_secPull', ← MonObj.comp_pow, c.lev_tors, MonObj.comp_one])
    geom := fun k _ _ x β z hx hz => by
      obtain ⟨g₁, g₂, g₃⟩ := c.geom k (x ≫ f) β z (by rw [Category.assoc]; exact hx) hz
      refine ⟨fun a => Iff.trans ?_ (g₁ a), fun g hg => ?_, fun a b => ?_⟩
      · rw [← (GlobalTheory.SiegelPull.push_injective pb (Over.mk x)).eq_iff, GlobalTheory.SiegelPull.push_secPull, map_one]
        rfl
      · obtain ⟨a, ha⟩ := g₂ (pushHom pb (Over.mk x) g) (by
          have := congrArg (pushHom pb (Over.mk x)) hg
          rw [map_pow, map_one] at this
          exact this)
        exact ⟨a, GlobalTheory.SiegelPull.push_injective pb _ ((GlobalTheory.SiegelPull.push_secPull pb _ _).trans ha)⟩
      · exact (weilIs_grpPullback_of_comm S S' c.A A' f φ _ _ (pull_isLB c.isLB _)
          (pull_isLB (pull_isLB c.isLB φ₂) _) pb
          (GlobalTheory.SiegelPull.diag_iso sq (ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ (pull_isLB c.isLB φ₂))) (Over.mk x) M _ _ _ _ _
          (congrArg (fun q => q.left) (GlobalTheory.SiegelPull.push_secPull pb (c.lev a) (Over.mk x)).symm)
          (congrArg (fun q => q.left) (GlobalTheory.SiegelPull.push_secPull pb (c.lev b) (Over.mk x)).symm)).2 (g₃ a b) }

theorem onPull_lev (c : SiegPre h M ζ s) (A' : Over S') [GrpObj A'] (φ : A'.left ⟶ c.A.left)
    (φ₂ : (A' ⊗ A').left ⟶ (c.A ⊗ c.A).left) (pb : IsGrpPullback A' c.A f φ) (sq : IsSquare φ φ₂)
    (a : Fin h ⊕ Fin h → ℤ) : ((onPull c A' φ φ₂ pb sq).lev a).left ≫ φ = f ≫ (c.lev a).left :=
  GlobalTheory.SiegelPull.secPull_left pb _

theorem onPull_siegPB (c : SiegPre h M ζ s) (A' : Over S') [GrpObj A'] (φ : A'.left ⟶ c.A.left)
    (φ₂ : (A' ⊗ A').left ⟶ (c.A ⊗ c.A).left) (pb : IsGrpPullback A' c.A f φ) (sq : IsSquare φ φ₂) :
    SiegPB (onPull c A' φ φ₂ pb sq) c f :=
  ⟨φ, φ₂, pb, sq, ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ (pull_isLB c.isLB φ₂), onPull_lev c A' φ φ₂ pb sq⟩

end Obj

theorem adj_of_lbIso {S : Scheme.{0}} {A : Over S} [GrpObj A] {O : Type} [Ring O] {P Q : LB (A ⊗ A).left}
    (hP : P.IsLB) (hQ : Q.IsLB) (e : LBIso P Q) {bar : O → O} {act : O → (A ⟶ A)} (h : Adj A P bar act) :
    Adj A Q bar act := by
  intro a
  have ha := (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP _)).2 (h a)
  have he := (GlobalTheory.CechPic.cls_eq_iff hP hQ).2 e
  refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hQ _) (pull_isLB hQ _)).1 ?_
  rw [GlobalTheory.CechPic.cls_pull hQ, GlobalTheory.CechPic.cls_pull hQ, ← he]
  exact ha

theorem exists_rep : ∀ (h' M : ℕ), 1 ≤ h' → 3 ≤ M → Odd M → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (eO : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d₀ : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range eO) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d₀ → ∑ i, ∑ j, W i j • (eO j * bar (eO i)) = (d₀ : O) → ∃ (H : Scheme.{0}) (sH : H ⟶ Sp (cycAway M)) (zH : SiegPre h' M (zetaAway M) sH) (actH : O → (zH.A ⟶ zH.A)), zH.Principal ∧ IsRAct zH.A actH ∧ Adj zH.A zH.P bar actH ∧ IsQProjOver sH ∧ IsLocallyNoetherian H ∧ ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)), z.Principal → IsRAct z.A act → Adj z.A z.P bar act → ∃! g : S ⟶ H, g ≫ sH = t ∧ ActPB z act zH actH g := by
  intro h' M hh hM hodd O _ bar r eO W d₀ hbar hspan hW hd hsum
  have hM0 : M ≠ 0 := by omega
  obtain ⟨F⟩ := exists_sFam_cycAway h' M hh hM hodd
  haveI : IsDedekindDomain (cycAway M) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway M
  haveI : IsLocallyNoetherian F.X := GlobalTheory.isLocallyNoetherian_of_isQProjOver_noeth (cycAway M) F.X F.s F.qproj
  obtain ⟨R, hRf, -⟩ := GlobalTheory.T.adjointActions_order_finite_unramified_scheme F.X F.univ.A F.univ.P F.univ.ab F.univ.isLB F.univ.rig₁ F.univ.rig₂
    F.univ.symm F.princ.1 O bar r eO W d₀ hbar hspan hW hd hsum
  have hq : IsQProjOver (R.π ≫ F.s) :=
    GlobalTheory.isQProjOver_comp_of_isFinite_noetherian (cycAway M) R.H F.X R.π F.s hRf F.qproj
  have hzH : SiegPB (onPull F.univ R.AH R.φ R.φ₂ R.pb R.sq) F.univ R.π := onPull_siegPB F.univ R.AH R.φ R.φ₂ R.pb R.sq
  refine ⟨R.H, R.π ≫ F.s, onPull F.univ R.AH R.φ R.φ₂ R.pb R.sq, R.act,
    (GlobalTheory.siegPre_pullback h' M (cycAway M) (zetaAway M) F.X R.H F.s (R.π ≫ F.s) R.π F.univ rfl).2 _ hzH F.princ,
    R.isAct, R.adj, hq, GlobalTheory.isLocallyNoetherian_of_isQProjOver_noeth (cycAway M) R.H _ hq, ?_⟩
  intro S t z act hz hact hadj
  obtain ⟨f, ⟨hfs, ⟨φz, φ₂z, pbz, sqz, isoz, levz⟩⟩, hfu⟩ := GlobalTheory.T.siegelFamily_existsUnique_classify_scheme h' M hh hM hodd F S t z hz
  have hadj' : Adj z.A (F.univ.P.pull φ₂z) bar act := adj_of_lbIso z.isLB (pull_isLB F.univ.isLB _) isoz hadj
  obtain ⟨g, ⟨hgπ, ψ, hψ, hψφ, hψa⟩, hgu⟩ := R.rep S f z.A φz φ₂z act pbz sqz hact hadj'
  have sqψ := GlobalTheory.LamPull.exists_isSquare hψ.1.w
  have e₂ := GlobalTheory.LamPull.isSquare_unique (GlobalTheory.TChart.AbPol.isSquare_comp sqψ R.sq) (by rw [hψφ]; exact sqz)
  have iso : LBIso z.P ((F.univ.P.pull R.φ₂).pull
      (lift (pushPt hψ.1.w (fst z.A z.A)) (pushPt hψ.1.w (snd z.A z.A))).left) := by
    refine (GlobalTheory.CechPic.cls_eq_iff z.isLB (pull_isLB (pull_isLB F.univ.isLB _) _)).1 ?_
    rw [(GlobalTheory.CechPic.cls_eq_iff z.isLB (pull_isLB F.univ.isLB _)).2 isoz, ← e₂, GlobalTheory.CechPic.cls_pull F.univ.isLB,
      GlobalTheory.CechPic.cls_pull (pull_isLB F.univ.isLB _), GlobalTheory.CechPic.cls_pull F.univ.isLB, GlobalTheory.CechPic.pull_comp]
  have hlev : ∀ a, (z.lev a).left ≫ ψ = g ≫ ((onPull F.univ R.AH R.φ R.φ₂ R.pb R.sq).lev a).left := fun a => by
    apply R.pb.1.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg ((z.lev a).left ≫ ·) hψφ).trans ((levz a).trans
        ((congrArg (· ≫ (F.univ.lev a).left) hgπ.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (g ≫ ·) (onPull_lev F.univ R.AH R.φ R.φ₂ R.pb R.sq a).symm).trans (Category.assoc _ _ _).symm)))))
    · exact ((Category.assoc _ _ _).trans ((congrArg _ hψ.1.w).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ g) (Over.w (z.lev a)))))).trans ((Category.id_comp g).trans ((Category.comp_id g).symm.trans
        ((congrArg (g ≫ ·) (Over.w ((onPull F.univ R.AH R.φ R.φ₂ R.pb R.sq).lev a)).symm).trans
        (Category.assoc _ _ _).symm)))
  refine ⟨g, ⟨by rw [← Category.assoc, hgπ, hfs], ψ, _, hψ, sqψ, iso, hlev, hψa⟩, ?_⟩
  rintro g' ⟨hg's, ψ', ψ₂', hψ', sqψ', iso', hlev', hact'⟩
  have hlev'' : ∀ a, (z.lev a).left ≫ ψ' ≫ R.φ = (g' ≫ R.π) ≫ (F.univ.lev a).left := fun a => by
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ R.φ) (hlev' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (g' ≫ ·) (onPull_lev F.univ R.AH R.φ R.φ₂ R.pb R.sq a)).trans (Category.assoc _ _ _).symm)))
  have iso'' : LBIso z.P (F.univ.P.pull (ψ₂' ≫ R.φ₂)) :=
    GlobalTheory.TChart.AbLevel.lbIso_comp F.univ.isLB (pull_isLB F.univ.isLB _) z.isLB
      (ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ (pull_isLB F.univ.isLB R.φ₂)) iso'
  have hf' : g' ≫ R.π = f := hfu _ ⟨by rw [Category.assoc]; exact hg's,
    ψ' ≫ R.φ, ψ₂' ≫ R.φ₂, hψ'.comp R.pb, GlobalTheory.TChart.AbPol.isSquare_comp sqψ' R.sq, iso'', hlev''⟩
  have s' : GlobalTheory.SiegLev.SRelBy z F.univ 1 1 f (ψ' ≫ R.φ) :=
    ⟨(hψ'.comp R.pb).congr hf' rfl, ⟨ψ₂' ≫ R.φ₂, GlobalTheory.TChart.AbPol.isSquare_comp sqψ' R.sq, iso''⟩,
      fun a => by simpa only [pow_one, hf'] using hlev'' a⟩
  have s : GlobalTheory.SiegLev.SRelBy z F.univ 1 1 f φz :=
    ⟨pbz, ⟨φ₂z, sqz, isoz⟩, fun a => by simpa only [pow_one] using levz a⟩
  have hφeq : ψ' ≫ R.φ = φz := GlobalTheory.SiegRigid.eq_of_sRelBy h' M M 1 (cycAway M) (cycAway M) (cycBase hM0)
    (zetaAway M) F.X S F.s t F.univ z f _ _ hM hodd F.princ s' s
  exact hgu g' ⟨hf', ψ', hψ', hφeq, hact'⟩

end GlobalTheory.ActSieg
