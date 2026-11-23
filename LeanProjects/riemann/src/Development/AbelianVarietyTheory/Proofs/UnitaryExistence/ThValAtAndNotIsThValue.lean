import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsThRule
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ColumnSectionIdeal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsVtOverIsUUOverBaseChange
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTranslationSectionsUniversalObject
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatCoverLevelSections
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicValueBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
  NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.VVRank (pullS isPullSec_pullS)
open GlobalTheory.TwistBaseChange (eq_pullS_of_isPullSec)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaRuleCompare

section Descent

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {a : ℤ}

omit [GrpObj A] in
theorem isPullback_whisker {T T' : Over S} (h : T' ⟶ T) :
    IsPullback (h ▷ A).left (fst T' A).left (fst T A).left h.left := by
  have h1 : IsPullback (snd T A).left (fst T A).left A.hom T.hom := (IsPullback.of_hasPullback T.hom A.hom).flip
  have h2 : IsPullback (snd T' A).left (fst T' A).left A.hom T'.hom := (IsPullback.of_hasPullback T'.hom A.hom).flip
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, whiskerRight_snd, Over.w h]; exact h2
  · rw [← Over.comp_left, ← Over.comp_left, whiskerRight_fst]

theorem sec_ext {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  obtain ⟨f₁, p₁⟩ := s
  obtain ⟨f₂, p₂⟩ := s'
  obtain rfl : f₁ = f₂ := funext h
  rfl

omit [GrpObj A] in
theorem chart_ge {T T' : Over S} (h : T' ⟶ T) (j : Fin 1 → L.ι) :
    (h ▷ A).left ⁻¹ᵁ (LPow A L a T).U j ≤ (LPow A L a T').U j := by
  intro y hy
  have h1 : ((h ▷ A).left ≫ (snd T A).left).base y ∈ (L.U (j 0) : Set A.left) := Set.mem_iInter.1 hy 0
  rw [← Over.comp_left, whiskerRight_snd] at h1
  exact Set.mem_iInter.2 fun i => by rw [Subsingleton.elim i 0]; exact h1

theorem gs_pullS {T T' : Over S} (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) {Z : Scheme.{0}}
    (r : Z ⟶ (T' ⊗ A).left) (z : Z) (j : Fin 1 → L.ι) (hz : r z ∈ (LPow A L a T').U j) :
    gs r z ((LPow A L a T').U j) ((pullS A a h s).f j) = gs (r ≫ (h ▷ A).left) z ((LPow A L a T).U j) (s.f j) :=
  (gs_res r z (chart_le_res A L (h ▷ A) (whiskerRight_snd _ _) a j) hz _).trans
    (gs_pull r (h ▷ A).left z _ (chart_le_res A L (h ▷ A) (whiskerRight_snd _ _) a j hz) _)

theorem pullS_comp {T T' T'' : Over S} (h' : T'' ⟶ T') (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) :
    pullS A a h' (pullS A a h s) = pullS A a (h' ≫ h) s :=
  sec_ext fun j => fn_ext fun y hy => by
    refine (gs_pullS h' _ _ y j hy).trans ((gs_pullS h _ _ y j
      (chart_le_res A L (h' ▷ A) (whiskerRight_snd _ _) a j hy)).trans (Eq.trans ?_ (gs_pullS _ _ _ y j hy).symm))
    rw [comp_whiskerRight, Over.comp_left]
    rfl

theorem exists_descend {T T' : Over S} (π : T' ⟶ T) [Flat π.left] [Surjective π.left] [QuasiCompact π.left]
    (F' : LB.Sec (LPow A L a T'))
    (H : ∀ (T'' : Over S) (g₁ g₂ : T'' ⟶ T'), g₁ ≫ π = g₂ ≫ π → pullS A a g₁ F' = pullS A a g₂ F') :
    ∃ F : LB.Sec (LPow A L a T), pullS A a π F = F' := by
  have P := (isPullback_whisker (A := A) π).flip
  have : Flat (π ▷ A).left := MorphismProperty.of_isPullback P ‹_›
  have : Surjective (π ▷ A).left := MorphismProperty.of_isPullback P ‹_›
  have : QuasiCompact (π ▷ A).left := MorphismProperty.of_isPullback P ‹_›
  have appLE : ∀ {Z Y : Scheme.{0}} (g : Z ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ g ⁻¹ᵁ U) (b : Γ(Y, U)) (z : Z),
      gs (𝟙 Z) z ⊤ ((g.appLE U ⊤ h).hom b) = gs g z U b := fun {Z Y} g U h b z =>
    (gs_res (𝟙 Z) z h trivial ((g.app U).hom b)).trans
      ((gs_pull (𝟙 Z) g z U (h (x := z) trivial) b).trans (by rw [Category.id_comp]))
  have desc : ∀ j : Fin 1 → L.ι, ∃ b : Γ((T ⊗ A).left, (LPow A L a T).U j), ((π ▷ A).left.app _).hom b =
      ((T' ⊗ A).left.presheaf.map (homOfLE (chart_ge π j)).op).hom (F'.f j) := fun j => by
    refine FunDescent.exists_app_eq _ _ _ fun Z g₁ g₂ h₁ h₂ e => fn_ext fun z _ => ?_
    rw [appLE, appLE, gs_res _ z _ (h₁ (x := z) trivial), gs_res _ z _ (h₂ (x := z) trivial)]
    have w : g₂ ≫ (T' ⊗ A).hom = g₁ ≫ (T' ⊗ A).hom := by
      rw [← Over.w (π ▷ A), ← Category.assoc, ← e, Category.assoc]
    let G₁ : Over.mk (g₁ ≫ (T' ⊗ A).hom) ⟶ T' ⊗ A := Over.homMk g₁ rfl
    let G₂ : Over.mk (g₁ ≫ (T' ⊗ A).hom) ⟶ T' ⊗ A := Over.homMk g₂ w
    have E : G₁ ≫ π ▷ A = G₂ ≫ π ▷ A := Over.OverMorphism.ext e
    have E₁ : (G₁ ≫ fst _ _) ≫ π = (G₂ ≫ fst _ _) ≫ π := by
      rw [Category.assoc, Category.assoc, ← whiskerRight_fst, ← Category.assoc, E, Category.assoc]
    have E₂ : G₂ ≫ snd _ _ = G₁ ≫ snd _ _ := by
      rw [← whiskerRight_snd π, ← Category.assoc, ← E, Category.assoc]
    have k : ∀ G : Over.mk (g₁ ≫ (T' ⊗ A).hom) ⟶ T' ⊗ A, G ≫ snd _ _ = G₁ ≫ snd _ _ →
        G.left z ∈ (LPow A L a T').U j → gs G.left z _ (F'.f j) =
          gs (lift (𝟙 _) (G₁ ≫ snd _ _)).left z _ ((pullS A a (G ≫ fst _ _) F').f j) := fun G hG hz => by
      have e' : (lift (𝟙 _) (G₁ ≫ snd _ _)).left ≫ ((G ≫ fst _ _) ▷ A).left = G.left := by
        rw [← Over.comp_left, lift_whiskerRight, Category.id_comp, ← hG, ← comp_lift, lift_fst_snd,
          Category.comp_id]
      refine Eq.trans ?_ (gs_pullS _ _ _ z j (chart_ge (G ≫ fst _ _) j ?_)).symm
      · rw [e']
      · exact (congrArg (fun q => q z ∈ (LPow A L a T').U j) e').mpr hz
    exact (k G₁ rfl (chart_ge π j (h₁ (x := z) trivial))).trans
      ((congrArg (fun u => gs _ z _ (LB.Sec.f u j)) (H _ _ _ E₁)).trans
        (k G₂ E₂ (chart_ge π j (h₂ (x := z) trivial))).symm)
  choose b hb using desc
  have hv : ∀ j (w : (T' ⊗ A).left), (π ▷ A).left w ∈ (LPow A L a T).U j →
      gs (𝟙 _ ≫ (π ▷ A).left) w _ (b j) = gs (𝟙 _) w _ (F'.f j) := fun j w hw =>
    (gs_pull (𝟙 _) _ w _ hw _).symm.trans ((congrArg (gs (𝟙 _) w _) (hb j)).trans
      (gs_res (𝟙 _) w (chart_ge π j) hw _))
  refine ⟨⟨b, fun j j' => FunDescent.app_injective (π ▷ A).left _ (fn_ext fun w hw => ?_)⟩,
    sec_ext fun j => fn_ext fun w hw => ?_⟩
  · have hw' : (𝟙 _ ≫ (π ▷ A).left) w ∈ (LPow A L a T).U j ⊓ (LPow A L a T).U j' := hw
    refine (gs_pull (𝟙 _) _ w _ hw' _).trans (Eq.trans ?_ (gs_pull (𝟙 _) _ w _ hw' _).symm)
    refine ((gs_res _ w _ hw' _).trans ((hv j w hw'.1).trans
      (sec_trans (L := L) (φ := fun _ : Fin 1 => (snd T' A).left) (ε := fun _ => a) F' (𝟙 _) w
        (chart_ge (a := a) π j hw'.1) (chart_ge (a := a) π j' hw'.2)))).trans (Eq.symm ?_)
    refine (gs_mul _ w _ hw' _ _).trans (congrArg₂ (· * ·) ((gs_unit _ w _ hw' _).trans (congrArg Units.val
      ((gm_linComb L _ _ _ w j j' hw'.1 hw'.2).trans ?_))) ((gs_res _ w _ hw' _).trans (hv j' w hw'.2)))
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Category.assoc, VVRank.whisker_snd_left]
  · exact (gs_pullS π _ _ w j hw).trans (hv j w (chart_le_res A L (π ▷ A) (whiskerRight_snd _ _) a j hw))

end Descent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

section Auxiliary

variable (Xo : Moduli Dw l) (c : Coeff l)

def jetEquiv : NabV Xo c ≃ IndefiniteRowSideFullHecke.ColumnSectionIdeal.Jet Xo c where
  toFun nab := fun _ _ _ y k F m => nab y k F (Finsupp.equivFunOnFinite.symm m)
  invFun J := fun {S} _ _ y k F α => J S y k F α
  left_inv nab := by
    funext S _ _ y k F α
    exact congrArg (nab y k F) (Finsupp.equivFunOnFinite_symm_coe α)
  right_inv J := rfl

variable {Xo c}

end Auxiliary

section Translates

variable (Xo : Moduli Dw l)

def LocVt {T : Over Xo.X} (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 T)) (t : T ⟶ Xo.univ.t.G)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) T)) : Prop :=
  ∀ p : T.left, ∃ (T' : Over Xo.X) (π : T' ⟶ T), Etale π.left ∧ (∃ q : T'.left, π.left.base q = p) ∧
    IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) (pullS _ _ π s) (π ≫ t) (pullS _ _ π F)

variable {Xo}

end Translates

section Values

variable {Xo : Moduli Dw l} {c : Coeff l}

def ExprNatural (nab : NabV Xo c) {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) : Prop :=
  ∀ (S S' : Type) [CommRing S] [Algebra c.F S] [CommRing S'] [Algebra c.F S'] (ψ : S →ₐ[c.F] S')
    (y : FrPt Xo c S) (y' : FrPt Xo c S'), ψ.toRingHom.FaithfullyFlat → FrMap ψ y y' →
    ∀ h : ptO Xo y'.x ⟶ ptO Xo y.x, h.left = spMap ψ.toRingHom →
    ∀ F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.x)),
      ψ (thExpr Xo c nab y P F) = thExpr Xo c nab y' P fun b => pullS _ _ h (F b)

def domainJump (Xo : Moduli Dw l) (c : Coeff l) : NabV Xo c :=
  fun {S} _ _ _ _ _ _ => open Classical in if IsDomain S then 0 else 1

end Values

end GlobalTheory.ThetaRuleCompare
