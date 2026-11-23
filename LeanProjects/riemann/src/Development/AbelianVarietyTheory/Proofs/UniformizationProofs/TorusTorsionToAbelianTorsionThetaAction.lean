import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionOverZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RedIffReduction
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsZeroOfRed
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionPointsIntegral
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionTranslationActsOnExpansionsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.Eqv

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem mem_of_nonempty {W : Type} [CommRing W] [IsDomain W] [Algebra R W] [Module.Finite R W]
    (φ : TF (R := R) F ⟶ TA R W) (z : (TF (R := R) F).left) (U : (TA R W).left.Opens)
    (hU : (U : Set (TA R W).left).Nonempty) : φ.left z ∈ U := by
  obtain ⟨x, hx⟩ := hU
  let p : PrimeSpectrum W := φ.left z
  have e : (TA R W).hom (φ.left z) = (TF (R := R) F).hom z := by
    rw [← Scheme.Hom.comp_apply, Over.w]
  have hp : p.asIdeal = ⊥ := by
    refine Ideal.eq_bot_of_comap_eq_bot (R := R) (eq_bot_iff.2 fun r hr => ?_)
    have h0 : r ∈ PrimeSpectrum.asIdeal (R := R) ((TA R W).hom (φ.left z)) := hr
    rw [e] at h0
    have h1 : algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) ∈ PrimeSpectrum.asIdeal (R := F) z := h0
    have hz : PrimeSpectrum.asIdeal (R := F) z = ⊥ := @Ideal.eq_bot_of_prime _ _ _ (PrimeSpectrum.isPrime _)
    rw [hz, Ideal.mem_bot, map_eq_zero,
      map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))] at h1
    exact Ideal.mem_bot.2 h1
  have hle : p.asIdeal ≤ PrimeSpectrum.asIdeal (R := W) x := hp ▸ bot_le
  exact ((PrimeSpectrum.le_iff_specializes _ _).1 hle).mem_open U.isOpen hx

section Pull
variable {T : Over (Spec (CommRingCat.of R))} {φ : TF (R := R) F ⟶ T}

theorem pull_b {g : GtPt D T} {g' : GtPtF D F} (h : GtPt.IsPullF F φ.left g g') : g'.b = φ ≫ g.b :=
  Over.OverMorphism.ext h.1

theorem pull_val {g : GtPt D T} {g' : GtPtF D F} (h : GtPt.IsPullF F φ.left g g') (χ : D.X) {y J}
    (hJ : Good D.P.L y J) : val (g'.s χ) (𝟙 _) y J = val (g.s χ) φ.left y J :=
  (val_corr hJ (h.2 χ) _).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))

theorem comp_cT (χ : D.X) : φ ≫ DegPre.cT D T χ = DegPre.cF D F χ := by
  rw [← Category.assoc, comp_toUnit]

theorem val_cubAtT {y J} (hJ : Good D.P.L y J) (χ : D.X) (a b : T ⟶ D.P.A) :
    val (DegPre.cubAtT D T (DegPre.cT D T χ) a b) φ.left y J =
      cubV D.cub y J (DegPre.cF D F χ) (φ ≫ a) (φ ≫ b) := by
  rw [← comp_cT (φ := φ)]
  exact val_cub D.cub φ hJ _ _ _

theorem isAdd_of_pull [IsReduced T.left] (hd : ∀ z (U : T.left.Opens), (U : Set T.left).Nonempty → φ.left z ∈ U)
    {g₁ g₂ g₃ : GtPt D T} {h₁ h₂ h₃ : GtPtF D F} (p₁ : GtPt.IsPullF F φ.left g₁ h₁) (p₂ : GtPt.IsPullF F φ.left g₂ h₂)
    (p₃ : GtPt.IsPullF F φ.left g₃ h₃) (H : h₁.IsAdd h₂ h₃) : g₁.IsAdd g₂ g₃ := by
  have : IsProper D.P.A.hom := D.P.isAb.proper
  have : D.P.A.left.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from D.P.A.hom]; infer_instance
  obtain ⟨z⟩ : Nonempty (TF (R := R) F).left := ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)⟩
  have dom : IsDominant φ.left := ⟨dense_iff_inter_open.2 fun U hU hne => ⟨φ.left z, hd z ⟨U, hU⟩ hne, z, rfl⟩⟩
  obtain ⟨hb, hv⟩ := (isAdd_iff _ _ _).1 H
  refine ⟨Over.OverMorphism.ext (ext_of_isDominant φ.left ?_), fun χ =>
    GlobalTheory.TauPull.corr_of_dense D.P.isLB φ.left z (hd z) fun J hJ => ?_⟩
  · rw [pull_b p₁, pull_b p₂, pull_b p₃, ← MonObj.comp_mul] at hb
    exact congrArg (fun q => q.left) hb
  · have e := hv χ z J hJ
    rw [pull_val p₁ χ hJ, pull_val p₂ χ hJ, pull_val p₃ χ hJ, pull_b p₁, pull_b p₂] at e
    exact (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) rfl (val_cubAtT hJ χ _ _)).trans
      (e.trans (val_mul hJ _ _ _).symm))

theorem pull_eq_of_isAdd {g₁ g₂ g₃ g₃' : GtPt D T} {h h' : GtPtF D F} (a : g₁.IsAdd g₂ g₃) (a' : g₁.IsAdd g₂ g₃')
    (p : GtPt.IsPullF F φ.left g₃ h) (p' : GtPt.IsPullF F φ.left g₃' h') : h = h' := by
  refine GlobalTheory.TorusExt.gt_ext_val (by rw [pull_b p, pull_b p', a.1, a'.1]) fun χ y J hJ => ?_
  refine (pull_val p χ hJ).trans (Eq.trans ?_ (pull_val p' χ hJ).symm)
  have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (a.2 χ) φ.left)
  have e' := (val_mul hJ _ _ _).symm.trans (val_corr hJ (a'.2 χ) φ.left)
  exact mul_right_cancel (e.trans e'.symm)

end Pull

section Generic
variable {G : Over (Spec (CommRingCat.of R))}

def liftK (y : TF (R := R) F ⟶ G) : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G :=
  Over.homMk (pullback.lift y.left (jFK (R := R) F) (Over.w y)) (pullback.lift_snd _ _ _)

theorem liftK_fst (y : TF (R := R) F ⟶ G) : (liftK y).left ≫ pullback.fst G.hom (jK R) = y.left :=
  pullback.lift_fst _ _ _

theorem liftK_mul [GrpObj G] (y y' : TF (R := R) F ⟶ G) : liftK (y * y') = liftK y * liftK y' := by
  have e := toBase_mul_pullback G (jK R) _ (liftK y) (liftK y')
  have a : ∀ u : TF (R := R) F ⟶ G, toBase (A := G) (A' := (Over.pullback (jK R)).obj G)
      (g := pullback.fst G.hom (jK R)) pullback.condition (liftK u) = u := fun u => Over.OverMorphism.ext (liftK_fst u)
  rw [a, a] at e
  refine Over.OverMorphism.ext (pullback.hom_ext ((liftK_fst _).trans (congrArg (fun q => q.left) e).symm) ?_)
  exact (Over.w (liftK (y * y'))).trans (Over.w (liftK y * liftK y')).symm

end Generic

theorem main : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {_} _ _ U => ∀ N : ℕ, 1 ≤ N → ∃ m : {g : GtPtF D (Kbar V) // GtTors D N g} → (TFK (R := V) (Kbar V) ⟶ A.A), Function.Injective m ∧ (∀ g, U.Acts (Kbar V) N 0 g.1 (m g)) ∧ ∀ g g' g'', GtPtF.IsAdd g.1 g'.1 g''.1 → m g'' = m g * m g') := by
  intro hL hL2 V _ _ _ hV D A G _ _ U N hN
  classical
  have := hV.1
  have := hV.2.2
  have : CharZero (Kbar V) := algebraRat.charZero _
  have hN0 : N ≠ 0 := by omega
  have hfin : Finite {g : GtPtF D (Kbar V) // GtTors D N g} :=
    Nat.finite_of_card_ne_zero (by
      rw [(GlobalTheory.GtCount.card_gtTors hL hL2 V D (Kbar V) N (Nat.cast_ne_zero.2 hN0)).1]
      exact pow_ne_zero _ hN0)
  have hs : {g : GtPtF D (Kbar V) | GtTors D N g}.Finite := hfin
  obtain ⟨W, _, _, _, φ, hW, hg⟩ := GlobalTheory.torsion_points_integral V hV D N hN hs.toFinset fun g h => hs.mem_toFinset.1 h
  have := hW.1
  have := hW.2.2.1
  have : IsReduced (TA V W).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of W)))
  have hd := mem_of_nonempty φ
  choose x hx hxu using GlobalTheory.UU.RedOnto.main V hV D A G U W hW
  have add := fun g g' g'' => GlobalTheory.UU.RedAdd.main hL.globalFns V hV D A G U W hW _ _ _ g g' g'' (hx g) (hx g') (hx g'')
  choose i ip ih using fun g : {g : GtPtF D (Kbar V) // GtTors D N g} => hg g.1 (hs.mem_toFinset.2 g.2)
  have := U.gen_hom
  have := U.semi.separated
  obtain ⟨z⟩ : Nonempty (TF (R := V) (Kbar V)).left := ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Kbar V))⟩
  have dom : IsDominant φ.left := ⟨dense_iff_inter_open.2 fun U hU hne => ⟨φ.left z, hd z ⟨U, hU⟩ hne, z, rfl⟩⟩
  refine ⟨fun g => liftK (φ ≫ x (i g)) ≫ U.gen.hom, fun g g' e => ?_, fun g => ?_, fun g g' g'' h => ?_⟩
  · have e₁ : liftK (φ ≫ x (i g)) = liftK (φ ≫ x (i g')) := (cancel_mono U.gen.hom).1 e
    have e₂ : φ.left ≫ (x (i g)).left = φ.left ≫ (x (i g')).left :=
      (liftK_fst _).symm.trans ((congrArg (fun q => q.left ≫ pullback.fst G.hom (jK V)) e₁).trans (liftK_fst _))
    have e₃ : x (i g) = x (i g') := Over.OverMorphism.ext
      (ext_of_isDominant_of_isSeparated G.hom ((Over.w _).trans (Over.w _).symm) φ.left e₂)
    obtain ⟨o, -, ho⟩ := ih g
    have o1 : x o = 1 := (add o o o).2.2 ho
    exact Subtype.ext (pull_eq_of_isAdd ((add (i g) o (i g)).1.1 (by rw [o1, _root_.mul_one]))
      ((add (i g) o (i g')).1.1 (by rw [o1, _root_.mul_one, e₃])) (ip g) (ip g'))
  · refine GlobalTheory.T.torsionTranslation_acts_on_expansions hL hL2 V hV D A G U W hW (Kbar V) φ N hN (x (i g)) (i g) g.1 _ ?_ (hx _) (ip g) ?_
    · obtain ⟨o, ⟨gs, h₀, hs, rfl⟩, ho⟩ := ih g
      have key : ∀ n (hn : n < N + 1), x (gs ⟨n, hn⟩) = x (i g) ^ n := by
        intro n
        induction n with
        | zero => exact fun _ => ((add (gs 0) (gs 0) (gs 0)).2.2 h₀).trans (pow_zero _).symm
        | succ n ihn =>
          exact fun hn => ((add _ _ _).1.2 (hs ⟨n, by omega⟩)).trans
            ((congrArg (· * x (i g)) (ihn (by omega))).trans (pow_succ _ _).symm)
      exact (key N (Nat.lt_succ_self N)).symm.trans ((add _ (i g) (i g)).2.2 ho)
    · show (liftK (φ ≫ x (i g)) ≫ U.gen.hom).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V) = _
      rw [← Category.assoc, ← Over.comp_left, Category.assoc, U.gen.hom_inv_id, Category.comp_id]
      exact liftK_fst _
  · have e : x (i g'') = x (i g) * x (i g') := (add _ _ _).1.2 (isAdd_of_pull hd (ip g) (ip g') (ip g'') h)
    show liftK (φ ≫ x (i g'')) ≫ U.gen.hom = _
    rw [e, MonObj.comp_mul, liftK_mul, MonObj.mul_comp]

end GlobalTheory.UU.Eqv
end
