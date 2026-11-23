import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmIdempotentAddStarEqOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionIsometryUniformisedModel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
open ReciprocityTheory.ChartRestriction.G.DVR
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ArcBuild

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem exists_tateIsoQ_of_torsionIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (T : CDVR) (t : SAB H (Sp T.V)) (P : PELUnif (maximalIdeal T.V) t), P.TorsionIso → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing T.V) F], letI := H.starRing; ∀ J : TateIso D F (Out.TFK (R := T.V) F ⟶ P.A.A) (fun a g => g ≫ P.oA.act a) (fun n g g' c => Out.WeilIs P.A.A P.A.L n g g' (unitOn c)), ∃ I : TateIsoQ D P.D.toPre P.oD F, I.ζ = J.ζ ∧ ∀ k, 0 < k → ∀ a q, P.ToA F k q (J.ev k a) → Out.QkPt.Equiv P.D.toPre F q (I.ev k a) := by
  intro E _ _ _ H D T t P hT F _ _ _
  letI := H.starRing
  intro J
  have hL := GlobalTheory.firstFiveLaws
  have hB := P.D.tau_bimult
  have hA : AdmBase T.V (maximalIdeal T.V) :=
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  choose f f₁ f₂ f₃ f₄ f₅ f₆ using hT F
  have tors : ∀ n (hn : 0 < n) p, f n hn p ^ n = 1 := fun n hn p => by
    obtain ⟨w, hw⟩ := P.U.ext
    exact ((f₁ n hn p _).2 rfl w hw).1
  have hev : ∀ n a, ∃ p : QkPt P.D.toPre F n, ∀ hn : 0 < n, f n hn p = J.ev n a := fun n a => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨GlobalTheory.TorusExt.qkZero hB F 0, fun h => absurd h (lt_irrefl 0)⟩
    · obtain ⟨p, hp⟩ := f₂ n hn (J.ev n a) ((J.onto n hn _).2 ⟨a, rfl⟩)
      exact ⟨p, fun _ => hp⟩
  choose ev evp using hev
  refine ⟨{ ζ := J.ζ, ζ_prim := J.ζ_prim, ζ_pow := J.ζ_pow, ev := ev
            add := fun n hn a b => ?_, lin := fun n hn c a => ?_, ker := fun n hn a b => ?_,
            onto := fun n hn p => ?_, tower := fun n m hn hm a => ?_, isom := fun n hn a b => ?_ },
    rfl, fun k hk a q h => ?_⟩
  · refine (GlobalTheory.TorusExt.qkAdd_iff hB _ _ _).2 ((f₃ n hn _ _).1 ?_)
    rw [f₄ n hn _ _ _ (GlobalTheory.TorusExt.qkAdd_qkAdd hB _ _), evp, evp, evp, J.add]
  · obtain ⟨p, hp⟩ := qkAct_exists hL.1.globalFns hB P.oD c (ev n a)
    have h₁ := f₅ n hn _ _ _ hp
    obtain ⟨q, q₁, q₂, q₃⟩ := hp
    refine ⟨q, q₁, q₂, GlobalTheory.TorusExt.equiv_trans hB q₃ ((f₃ n hn _ _).1 ?_)⟩
    rw [h₁, evp, evp, J.lin]
  · rw [← f₃ n hn, evp, evp]
    have h₁ : J.ev n a = J.ev n b * J.ev n (a - b) := by rw [← J.add, add_sub_cancel]
    rw [h₁, mul_eq_left, J.ker n hn]
    exact exists_congr fun c => sub_eq_iff_eq_add'
  · obtain ⟨a, ha⟩ := (J.onto n hn (f n hn p)).1 (tors n hn p)
    exact ⟨a, (f₃ n hn _ _).1 (by rw [evp, ha])⟩
  · obtain ⟨q, q₁, q₂⟩ := GlobalTheory.ModelData.ModelTate.exists_level_down hB n m (ev (n * m) a)
    have hN := Nat.mul_pos hn hm
    have h := (GlobalTheory.LevelCompat.qkToAkU_level hL T.V _ hA P.D P.A t.G t.semi P.U F n m _ hn hm rfl q
      (ev (n * m) a) _).2 q₁ q₂ ((f₁ _ hN _ _).2 rfl)
    refine ⟨q, q₁, q₂, (f₃ n hn _ _).1 ?_⟩
    rw [← (f₁ n hn _ _).1 h, evp, evp, J.tower n m hn hm]
  · refine (f₆ n hn _ _ _).2 ?_
    rw [evp, evp]
    exact J.isom n hn a b
  · refine (f₃ k hk _ _).1 ?_
    rw [← (f₁ k hk _ _).1 h, evp]

end GlobalTheory.ArcBuild
