import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocallyNoetherian
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsUniqueIsTwistPull
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalSymLiftExistsUniqueGlobal
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.SymMove

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {k : ℤ}

theorem act_unique (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {n : ℕ} (hn : Odd n) {x : T ⟶ A}
    {θ θ' : ThetaGrp A L k T} (h : SymLift A L k n x θ) (h' : SymLift A L k n x θ')
    {s t t' : LB.Sec (LPow A L k T)} (a : IsActOf A L k θ s t) (a' : IsActOf A L k θ' s t') : t = t' := by
  have hc := SymLiftOdd.symLift_unique hG hA hL hn θ θ' h h'
  have e : θ.pt = θ'.pt := h.pt_eq.trans h'.pt_eq.symm
  have key : ∀ j, t.f j = t'.f j :=
    sec_ext_val hL (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) (s := t) (s' := t')
      fun y J hJ => (twist_val a (𝟙 _) y hJ).trans (Eq.trans (congrArg₂ (· * ·)
        (congrArg Units.val (val_corr hJ hc (𝟙 _))) (by rw [e])) (twist_val a' (𝟙 _) y hJ).symm)
  obtain ⟨f₁, p₁⟩ := t
  obtain ⟨f₂, p₂⟩ := t'
  obtain rfl : f₁ = f₂ := funext key
  rfl

theorem exists_one (hL : L.IsLB) {ν : LB.Gen (negLB A L k T)} (hν : ν.IsGen) (n : ℕ) (s : LB.Sec (LPow A L k T)) :
    ∃ θ : ThetaGrp A L k T, SymLift A L k n 1 θ ∧ IsActOf A L k θ s s := by
  obtain ⟨o, ho, vo⟩ := ThetaCoord.exists_symLift_one hL hν n
  refine ⟨o, ho, VVRank.isTwistPull_of_sv A hL o.isGen fun z J hJ => ?_⟩
  have e : translT A (1 : T ⟶ A) = 𝟙 _ := by
    rw [translT, ThetaAct.translPt_one, lift_fst_snd]
  change _ = (CommPairing.tval o (𝟙 _) z J).val * _
  rw [vo _ _ z J hJ, ho.pt_eq, e, Units.val_one, _root_.one_mul, Over.id_left]
  rfl

end GlobalTheory.SymMove

namespace GlobalTheory

theorem existsUnique_moves : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (k : ℕ), Odd k → ∀ (b : (ptO Xo x ⟶ Xo.univ.t.G)), b ^ k = 1 → ∀ F : SecN Xo x k, (∃! F' : SecN Xo x k, Moves Xo b F F') ∧ Moves Xo 1 F F := by
  intro E _ _ _ H Dw l Xo S _ x k hk b hb F
  have hLaw : Laws := firstFiveLaws.1
  have := UnivPol.isLocallyNoetherian Xo
  have hA : IsAbelianScheme Xo.univ.t.G := (UnivPol.pol Xo).isAb
  have hL : Xo.univ.t.PP.L.IsLB := (UnivPol.pol Xo).isLB
  obtain ⟨U, hU⟩ : ∃ U : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo x),
      SymLift Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) k b U :=
    exists_symLift_global hLaw Xo.X (UnivPol.pol Xo) k hk (UnivPol.isUnit_natCast Xo _ hk.pos) _ b hb
  obtain ⟨F', hF', -⟩ := existsUnique_isTwistPull _ _ _ hL _ (translT _ U.pt) (translPt _ U.pt) (lift_snd _ _)
    k k U.φ U.isGen F
  obtain ⟨ν, hν, -⟩ := hU.sym
  refine ⟨⟨F', ⟨hb, U, hU, hF'⟩, fun F'' h => ?_⟩, one_pow k, SymMove.exists_one hL hν k F⟩
  obtain ⟨-, U', hU', a⟩ := h
  exact SymMove.act_unique hLaw.globalFns hA hL hk hU' hU a hF'

end GlobalTheory
