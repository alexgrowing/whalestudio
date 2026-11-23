import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTranslSum
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGenOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormalisedMulPullIsoOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

noncomputable section

namespace GlobalTheory.RigIsoDescent

section General

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A}

theorem exists_isRigIso_of_gen {Y : Scheme.{0}} {x x' : Y ⟶ S} {Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left}
    {k : ℤ} (hΨ : IsPointed A Ψ) (t : LB.Gen (isoLB A L Ψ k)) (ht : t.IsGen) : ∃ β, IsRigIso A L Ψ k β := by
  obtain ⟨β, hβ, hc⟩ := DVR.exists_normalized_to L.isLB _ _ t ht (fst (Over.mk x) A).left
    (ptSecT A (1 : Over.mk x ⟶ A)).left ThetaReal.NormMul.ptSec_fst _ _
    (LB.mulGen L.L (Y := Y) _ _ _ _ (rigT A L.L L.rig (Over.mk x) k) (rigT A L.L L.rig (Over.mk x') (-1)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (ThetaReal.NormMul.rigT_isGen L.rigGen _) (ThetaReal.NormMul.rigT_isGen L.rigGen _))
    (by
      rw [DVR.fsum_sumElim, DVR.fsum, DVR.fsum, DVR.fsum, Fin.sum_univ_two, Fin.sum_univ_one, Fin.sum_univ_one]
      refine congrArg₂ (· + ·) (congrArg (Finsupp.single · k) ThetaReal.NormMul.ptSec_snd)
        (congrArg (Finsupp.single · (-1 : ℤ)) ?_)
      refine (Category.assoc _ _ _).symm.trans ?_
      rw [hΨ.2]
      exact ThetaReal.NormMul.ptSec_snd)
  exact ⟨β, hΨ, hβ, hc⟩

theorem exists_gen_of_field (hA : IsAbelianScheme A) {K K' : Type} [Field K] [Field K'] (φ : K →+* K')
    {x x' : Sp K ⟶ S} {w w' : Sp K' ⟶ S} {Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left}
    {Ψ' : (Over.mk w ⊗ A).left ⟶ (Over.mk w' ⊗ A).left} {k : ℤ} (hw : w = spMap φ ≫ x)
    (π : (Over.mk w ⊗ A).left ⟶ (Over.mk x ⊗ A).left)
    (h₁ : π ≫ (fst (Over.mk x) A).left = (fst (Over.mk w) A).left ≫ spMap φ)
    (h₂ : π ≫ (snd (Over.mk x) A).left = (snd (Over.mk w) A).left)
    (h₃ : π ≫ Ψ ≫ (snd (Over.mk x') A).left = Ψ' ≫ (snd (Over.mk w') A).left)
    (t : LB.Gen (isoLB A L Ψ' k)) (ht : t.IsGen) : ∃ u : LB.Gen (isoLB A L Ψ k), u.IsGen := by
  have := hA.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected
  let p : (Over.mk x ⊗ A).left ⟶ Sp K := (fst (Over.mk x) A).left
  have H₀ : IsPullback (snd (Over.mk x) A).left p A.hom x := (IsPullback.of_hasPullback x A.hom).flip
  have H₁ : IsPullback (snd (Over.mk w) A).left (fst (Over.mk w) A).left A.hom w :=
    (IsPullback.of_hasPullback w A.hom).flip
  have : IsProper p := MorphismProperty.of_isPullback (P := @IsProper) H₀ inferInstance
  have : GeometricallyIntegral p := MorphismProperty.of_isPullback (P := @GeometricallyIntegral) H₀ inferInstance
  have H : IsPullback π (fst (Over.mk w) A).left p (spMap φ) :=
    IsPullback.of_right (by rw [h₂, ← hw]; exact H₁) h₁ H₀
  obtain ⟨c, hc⟩ := gen_chartPull (chartPullOut L.L (isoφ A Ψ) ![k, -1] π (isoφ A Ψ') fun i => by
    fin_cases i
    exacts [h₂.symm, h₃.symm]) t ht
  exact FieldTriv.exists_gen_of_isPullback φ p π _ H (LB.isLB_linComb L.isLB _ _) c hc

end General

theorem eSec_fst {B B' : Scheme.{0}} (u : B' ⟶ B) (A : Over B) [GrpObj A] :
    eSec ((Over.pullback u).obj A) ≫ pullback.fst A.hom u = u ≫ eSec A := by
  rw [eSec, eSec, Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq,
    ← pullback.condition_assoc]
  exact (pullback.lift_fst _ _ _).trans (by simp)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem ptSec_swap {K : Type} [CommRing K] (x : Sp K ⟶ Xo.X) :
    (ptSecT Xo.univ.t.G (1 : Over.mk x ⟶ Xo.univ.t.G)).left ≫ (swap x).hom = eSec (Fib Xo x) := by
  refine pullback.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (swap_hom_fst x)).trans
      (ThetaReal.NormMul.ptSec_snd.trans (eSec_fst x _).symm))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (swap_hom_snd x)).trans
      (ThetaReal.NormMul.ptSec_fst.trans (Over.w η[Fib Xo x]).symm))

theorem isPointed_of_isMonHom {K : Type} [CommRing K] {x x' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x')
    (hf : IsMonHom f) : IsPointed Xo.univ.t.G (conj x x' f.left) := by
  refine ⟨(over_iff _).2 (Over.w f), ?_⟩
  have e : eSec (Fib Xo x) ≫ f.left = eSec (Fib Xo x') := congrArg (fun q => q.left) hf.one_hom
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (ptSec_swap x)).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans ?_)))
  exact (Iso.comp_inv_eq _).2 (ptSec_swap x').symm

theorem exists_isRigIso_of_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x') (g : Fib Xo w ⟶ Fib Xo w') (k : ℤ), IsBC φ f g → IsMonHom f → (∃ β, IsRigIso Xo.univ.t.G Xo.univ.t.PP (conj w w' g.left) k β) → ∃ β, IsRigIso Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) k β := by
  rintro E _ _ _ H Dw l Xo K L _ _ φ x x' w w' f g k ⟨hw, hw', hbc⟩ hf ⟨β, -, hβ, -⟩
  have mk : ∀ {y : Sp K ⟶ Xo.X} {v : Sp L ⟶ Xo.X}, v = spMap φ ≫ y →
      ∃ π : pullback Xo.univ.t.G.hom v ⟶ pullback Xo.univ.t.G.hom y,
        π ≫ pullback.fst _ _ = pullback.fst _ _ ∧ π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap φ := fun h =>
    ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap φ) (by rw [Category.assoc, ← h, pullback.condition]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨π, a₁, a₂⟩ := mk hw
  obtain ⟨π', b₁, b₂⟩ := mk hw'
  have e := hbc π π' a₁ a₂ b₁ b₂
  have hp := isPointed_of_isMonHom f hf
  obtain ⟨u, hu⟩ := exists_gen_of_field (L := Xo.univ.t.PP) (Ψ := conj x x' f.left) (UnivPol.pol Xo).isAb φ hw
    ((swap w).hom ≫ π ≫ (swap x).inv)
    (by rw [Category.assoc, Category.assoc, swap_inv_fst, a₂, swap_hom_snd_assoc])
    (by rw [Category.assoc, Category.assoc, swap_inv_snd, a₁, swap_hom_fst])
    (by
      simp only [conj_apply, Category.assoc, Iso.inv_hom_id_assoc, swap_inv_snd]
      rw [← reassoc_of% e, b₁]) β hβ
  exact exists_isRigIso_of_gen hp u hu

end GlobalTheory.RigIsoDescent
