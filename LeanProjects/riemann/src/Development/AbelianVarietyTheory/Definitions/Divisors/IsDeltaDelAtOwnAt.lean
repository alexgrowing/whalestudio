import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.RealIndexBound GlobalTheory.OnTies

namespace GlobalTheory.BigOn

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

structure CoreTies (L : SizeData₂ D) (EX : ErrX D) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) : Prop where
  laws : LawsCore J.toCore
  canon : J.Q.Canon
  rank : ∀ j, 1 ≤ (J.Q.Dw j).p + (J.Q.Dw j).q
  halfEX : HalfEX J.toCore EX
  field₁ : FieldOK0 D D.host.pde
  field₂ : FieldOK0 D D.host.pde'
  small : FieldSmall D L
  level : J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal
  oneHalf : ∃ Pk : ℕ → HeightOneSpectrum (𝓞 D.host.K), ∀ v ∈ R.twPl, ((ownAt D v : ℕ) : 𝓞 D.host.K) ∈ (Pk (ownAt D v)).asIdeal ∧
    ∀ PP ∈ placesOver R (R.mu v) (ownAt D v),
      (Pk (ownAt D v)).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal
  delVal : ∀ x, ((R.C.del.1 x : ℂˣ) : ℂ) ∈ FO D
  delVal' : ∀ x, ((R.C.del'.1 x : ℂˣ) : ℂ) ∈ FO D

def OwnPin {J : CoreJ D} (r : TwoRuns J G) : Prop :=
  ∀ v (j n : ℕ), InR D j → ((r.used v).full.dδ j n).pd = ownAt D v

def PageNum {L : SizeData₂ D} {Pm : ParameterChoice' D L} (Tp : ParamsT D L Pm) (x₁ : ℝ) : Prop :=
  SizesAt L ∧ Pm.CnW = 10 ∧ (∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1) ∧ 1000 ≤ Tp.CP ∧ Tp.CP ^ 20 ≤ zBase L ∧ x₁ ≤ L.sc.x

def RunsHold {L : SizeData₂ D} {Pm : ParameterChoice' D L} (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (CK : ℝ) {J : CoreJ D}
    (r : TwoRuns J G) : Prop :=
  ∀ v (h : LawsP (r.used v).full.toTop) (hinj : Function.Injective D.what₂.OtoLL) (j : ℕ) (hj : InR D j),
    HypC L (recPJ h j hj) ⟨CK, 20, Tp.CP, Tp.eP, Tp.CP, Tp.eP, 7⟩ Tp.CP Tp.eP 7 0 L.Ct
        (scalOfP (recB h.toLawsCore) hinj EX (ownAt D v) (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO) (kaR Tp hK j) (lR Tp hK j)
        (fR Tp hK j) Tp.TO Tp.nP Tp.nWn (LevelStarExponents.h0 L - 4) (nusR h j (lR Tp hK j)) ∧
      Concl (recPJ h j hj) (scalOfP (recB h.toLawsCore) hinj EX (ownAt D v) (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO)
        (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO (nusR h j (lR Tp hK j))
        ((recPJ h j hj).rk (kaR Tp hK j) ((recB h.toLawsCore).Mlat j (kaR Tp hK j)) * D.R.f * D.R.m * L.sc.b * L.de2)

theorem isDelta_delAt_ownAt (C : Formalism.L2.Host.CharFrame D) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    Formalism.L2.Host.IsDelta (H := D.host) (ownAt D v) (C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) := by
  unfold ownAt Formalism.L2.Host.CharFrame.delAt
  split_ifs
  exacts [C.isDel', C.isDel]

theorem ownAt_ne_of_plc_eq {v : HeightOneSpectrum (𝓞 D.what₂.LL)} (h : Formalism.EigenvalueLevelCeiling.plc v = D.host.pde) :
    ownAt D v ≠ Formalism.EigenvalueLevelCeiling.plc v := by
  unfold ownAt
  rw [if_pos h, h]
  exact D.host.pde_ne.symm

namespace CoreTies

variable {L : SizeData₂ D} {EX : ErrX D} {J : CoreJ D} [Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F}

theorem inj (h : CoreTies L EX J R) : Function.Injective D.what₂.OtoLL := h.field₁.full.1

theorem fieldAt (h : CoreTies L EX J R) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) : FieldOK0 D (ownAt D v) := by
  unfold ownAt
  split_ifs
  exacts [h.field₂, h.field₁]

theorem delAt_mem (h : CoreTies L EX J R) (l : ℕ) (x) : (((R.C.delAt l).1 x : ℂˣ) : ℂ) ∈ FO D := by
  unfold Formalism.L2.Host.CharFrame.delAt
  split_ifs
  exacts [h.delVal' x, h.delVal x]

theorem delAt_valuesIn (h : CoreTies L EX J R) (l : ℕ) : (R.C.delAt l).ValuesIn 0 (FO D).val.toRingHom := fun v _ =>
  ⟨⟨_, h.delAt_mem l _⟩, by
    simp only [Formalism.L2.Host.HChar.valTw, Complex.ofReal_zero, neg_zero, Complex.cpow_zero, mul_one]
    rfl⟩

theorem reScal_iff (lam : type_of% R.lam) (kap : ℝ) : CoreTies L EX J (reScal R lam kap) ↔ CoreTies L EX J R :=
  ⟨fun h => { h with }, fun h => { h with }⟩

end CoreTies

omit [Group G] [Fintype G] in

theorem ownPin_of {J : CoreJ D} {r : TwoRuns J G} (h₁ : ∀ j n : ℕ, InR D j → (r.first.full.dδ j n).pd = D.host.pde)
    (h₂ : ∀ j n : ℕ, InR D j → (r.second.full.dδ j n).pd = D.host.pde') : OwnPin r := by
  intro v j n hj
  by_cases h : Formalism.EigenvalueLevelCeiling.plc v = D.host.pde
  · rw [show r.used v = r.second from if_pos h, show ownAt D v = D.host.pde' from if_pos h]
    exact h₂ j n hj
  · rw [show r.used v = r.first from if_neg h, show ownAt D v = D.host.pde from if_neg h]
    exact h₁ j n hj

theorem PageNum.mono {L : SizeData₂ D} {Pm : ParameterChoice' D L} {Tp : ParamsT D L Pm} {x₁ x₂ : ℝ} (h : PageNum Tp x₁) (hx : x₂ ≤ x₁) :
    PageNum Tp x₂ := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, hx.trans h.2.2.2.2.2⟩

example {L : SizeData₂ D} {Pm : ParameterChoice' D L} (Tp : ParamsT D L Pm) : ¬ PageNum Tp (L.sc.x + 1) := fun h => by
  linarith [h.2.2.2.2.2]

example (C : Formalism.L2.Host.CharFrame D) : C.delAt D.host.pde' = C.del := if_neg D.host.pde_ne.symm

example {x : ℝ} (h : RecOK D x) : ∃ (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm), PageNum Tp x ∧ FieldSmall D L := by
  obtain ⟨L, Pm, Tp, -, n2, n3, n4, n5, n6, n7, n8⟩ := h.num
  exact ⟨L, Pm, Tp, ⟨n2, n3, n4, n5, n6, n7⟩, n8⟩

end GlobalTheory.BigOn

end
