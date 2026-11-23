import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
import Formalism.LocalToGlobal.ProjectiveLattices.ExtPtUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

def sabMapCast {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}} {t' : SAB H S'}
    {t : SAB H S} {f f' : S' ⟶ S} (m : SABMap t' t f) (h : f = f') : SABMap t' t f' := h ▸ m

theorem sabMapCast_φ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f f' : S' ⟶ S} (m : SABMap t' t f) (h : f = f') : (sabMapCast m h).φ = m.φ := by
  subst h
  rfl

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem unifAtInt_of_model (hE : ExtVStatement) (hC : Out.CubePullSt) (Y : Model Xo c β) (h3 : Y.N3) (T : CDVR)
    (io : c.F →+* T.Fr) (b : O →+* T.V) (hb : (algebraMap T.V T.Fr).comp b = io.comp β)
    (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y)
    (hS : ∃ S : SplitExt (Sp (IsLocalRing.ResidueField T.V)),
      S.IsGt ((Over.pullback (spMap (IsLocalRing.residue T.V))).obj I.G.G)) :
    ∃ P : PELUnif (IsLocalRing.maximalIdeal T.V) I.G, P.TorsionIso := by
  let _ := io.toAlgebra
  have hcond : y.x ≫ Xo.s = spMap io ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [y.x_over]
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let z : Sp T.Fr ⟶ Xo.XF c := pullback.lift y.x (spMap io) hcond
  have hzs : z ≫ pullback.snd _ _ = spMap io := pullback.lift_snd _ _ _
  have hzf : z ≫ pullback.fst _ _ = y.x := pullback.lift_fst _ _ _
  have hx : z ≫ Y.j ≫ Y.s = Out.jK T.V ≫ spMap b := by
    show z ≫ (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hzs]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hb]
  obtain ⟨yt, h1, -⟩ := extPt Y T b z hx

  obtain ⟨PP', cub, sym, adj, prim, mP, -⟩ := sabPull hC yt Y.t
  let tP : SAB H (Sp T.V) := ⟨(Over.pullback yt).obj Y.t.G, IsSemiAbelian.pullback _ Y.t.G Y.t.semi,
    OAct.pullback _ Y.t.G Y.t.act, PP', cub, sym, adj, prim⟩
  let mP' : SABMap tP Y.t yt := mP

  obtain ⟨mF, -⟩ := sabCancel pullCubCancel E H _ _ _ Xo.univ.t Y.oF.t I.t' (pullback.fst _ _) z Y.m0.toSABMap
    (sabMapCast I.m1 hzf.symm)
  obtain ⟨mJ, -⟩ := sabComp pullCubComp E H _ _ _ Y.t Y.oF.t I.t' (Y.jQ ≫ pullback.fst _ _) z Y.m mF
  have hj : z ≫ Y.jQ ≫ pullback.fst _ _ = Out.jK T.V ≫ yt := h1.symm
  obtain ⟨mK, -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t tP I.t' yt (Out.jK T.V) mP' (sabMapCast mJ hj)

  have hprop : IsProper I.t'.G.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) I.m1.cart.1 Xo.univ.proper
  obtain ⟨ψ, -⟩ := hE E H T.V inferInstance I.G tP I.t' hprop I.m2 mK
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ Y.t tP I.G yt (𝟙 _) mP' ψ
  let n' : SABMap I.G Y.t yt := sabMapCast n (Category.id_comp yt)

  have habs : (yt ⁻¹' abLocus Y.t.G).Nonempty := by
    obtain ⟨pt⟩ : Nonempty (Sp T.Fr) := inferInstance
    refine ⟨Out.jK T.V pt, ?_⟩
    have hz : Y.jQ (z pt) ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨_, rfl⟩
    have h2 : yt (Out.jK T.V pt) = (pullback.fst Y.s (spMap β)) (Y.jQ (z pt)) := by
      rw [← Scheme.Hom.comp_apply, h1]
      show (z ≫ Y.jQ ≫ pullback.fst _ _) pt = _
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    rw [Set.mem_preimage, h2]
    exact hz
  obtain ⟨P, -, hP⟩ := h3 T.V inferInstance inferInstance inferInstance yt I.G n' habs hS
  exact ⟨P, hP⟩

end Model

def UnifAtIntLaSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j)
    (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
    ((T.Q.l.M : 𝓞 T.Q.c.F) ∉ la.asIdeal) →
    ∀ I : IntData (T.Q.Xo j) T.Q.c Tc io yI.1,
      (∃ S : SplitExt (Sp (IsLocalRing.ResidueField Tc.V)),
        S.IsGt ((Over.pullback (spMap (IsLocalRing.residue Tc.V))).obj I.G.G)) →
      ∃ P : PELUnif (IsLocalRing.maximalIdeal Tc.V) I.G, P.TorsionIso

end ReciprocityTheory.ChartRestriction.G.PullbackSections
