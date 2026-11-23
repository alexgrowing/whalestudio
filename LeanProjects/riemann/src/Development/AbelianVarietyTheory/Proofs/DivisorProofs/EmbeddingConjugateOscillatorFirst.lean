import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrAtEmb
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormIntegrality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaCharacterUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomEqOnAdjoinSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolShapeOfOverK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfConjOnFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CircleEqOneIffOfConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResEtaHasInfExpOfIsEtaConj

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne.Facts

theorem infPart_eq_one {D : D7} {v ε} (hε : IsPlaceIdem D v ε) {x : AE D}
    (hx : algebraMap (AF D.host.F) (AE D) ε * (x - 1) = x - 1) : infPart D x = 1 := by
  obtain ⟨α, rfl, -⟩ := hε
  have h3 := congrArg (infPart D) hx
  have h4 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    have e2 : fstA D.host.F (pairA D.host.F 0 α) = 0 := rfl
    have e3 := Algebra.TensorProduct.map_tmul (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (pairA D.host.F 0 α) 1
    rw [e2, TensorProduct.zero_tmul] at e3
    exact e3
  rw [map_mul, h4, zero_mul, map_sub, map_one] at h3
  exact (sub_eq_zero.1 h3.symm)

theorem sigW_add {D : D7} (i : Fin D.R.m) :
    (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = (Wc D i).rank := by
  have := D.R.m_add_three_le_k
  have hi := i.2
  rw [rank_Wc i]
  simp only [Ranks.sigW, Ranks.r]
  omega

theorem signs_of_overK {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ) (ρ : D.what₂.Tau) (a : Fin (Wc D i).rank) :
    (R.MW i σ).ε ρ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D ρ)).1) := by
  have hs : (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (inR i).1 (inR i).2 _
  have he := (R.MW i σ).enum ρ
  unfold Links.parAt at he
  rw [if_pos (((labels_overK σ).1 hσ).2 ρ)] at he
  exact (GlobalTheory.HolDict.isEnum_holPar_kapW _ (rank_Wc i) (by rw [hs]; exact sigW_add i) he a).2

theorem unramAt_conj {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (hR : R.Char F)
    (i : Fin D.R.m) {σ : D.what₂.LL →+* ℂ} {μ' η' : (AE D)ˣ →* Circle} (hμ : ChiAt R i σ μ') (hη : IsEtaConj σ R.eta η')
    {v ε} (hv : NonSplitAt D v ε) : UnramAt ε μ' ∧ UnramAt ε (μ' * η'⁻¹) := by
  have hc := chars_of_lift D G Pl0 T0 A Ks R F hR i
  have u1 : UnramAt ε μ' := fun x a b c => by
    have h0 : R.mu0 ((i : ℕ) + 1) x * R.xi A.μ0 x = 1 := (hc.2.2.2 A.μ0 v ε hv).1 x a b c
    rw [hc.2.1, MonoidHom.one_apply, mul_one] at h0
    exact (hμ.2.2.2.1 x (infPart_eq_one hv.1 a)).elim fun y hy =>
      (circle_eq_one_iff_of_conj D.what₂.embLL σ _ _ y hy.1 hy.2).2 h0
  refine ⟨u1, fun x a b c => ?_⟩
  show μ' x * (η' x)⁻¹ = 1
  rw [u1 x a b c, hη.2.1 x (infPart_eq_one hv.1 a) b c, inv_one, one_mul]

theorem factsAt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → FWTie T R κ v₀ → ∀ (i : Fin D.R.m) (O : OM T R i), Pinned κ v₀ O → ∀ (σ : D.what₂.LL →+* ℂ) (σ' : O.c'.F →+* ℂ), σ'.comp O.jL = σ → OverK σ → FactsAt O σ σ' := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR tie i O hP σ σ' hσ' hK
  have hin : InR D ((i : ℕ) + 1) := inR i
  have hf : (inC O.c').comp O.jL = D.what₂.embLL := hP.lift.field
  have e0 : res T D.what₂.embLL = T.σ₀ := res_embLL T tie.alg_eq tie.laws.pins.2.2.1
  have hj : ∀ x, O.jL (algebraMap T.Q.c.F D.what₂.LL x) = incF T.Q.c O.c' O.hle x := fun x =>
    (inC O.c').injective ((RingHom.congr_fun hf _).trans (RingHom.congr_fun e0 x))
  have hs : res T σ = sOf O σ' := RingHom.ext fun x =>
    (RingHom.congr_fun hσ' _).symm.trans (congrArg σ' (hj x))
  have hg : GoodEmb T.Q.c (res T σ) := (overK_iff_good T R F κ v₀ hR tie i σ).1 hK
  have hg' : GoodEmb T.Q.c (sOf O σ') := hs ▸ hg
  have hsig : ∀ ρ, (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := fun ρ => D.sp.W_sigval _ hin.1 hin.2 _
  have hq := (tie.laws.pins.2.2.2 _ hin).2.1
  have hpq : (D.R.sigW ((i : ℕ) + 1)).1 + (T.Q.Dw ((i : ℕ) + 1)).q = (Wc D i).rank := by
    rw [hq]; exact sigW_add i
  have hε : ∀ τ a, (R.MW i σ).ε τ a = decide ((a : ℕ) < (D.R.sigW ((i : ℕ) + 1)).1) := fun τ a => by
    rw [signs_of_overK R i hK τ a, hsig]
  have hl := (labels_overK σ).1 hK
  refine ⟨hs, hg', hg', signs_of_overK R i hK, FactsLat.isONeg_x0Mat _ hpq hε, FactsLat.cart_eq_cartZ _ hpq hε, ?_,
    fun ρ => ?_, fun μ' η' hμ hη => ⟨fun hV => ?_, fun v ε hv => unramAt_conj R F hR i hμ hη hv, ?_⟩⟩
  · have h : IsModelBaseFrameFamily (R.MW i σ) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) (res T σ)) := tie.x0 i σ hg
    rw [hs] at h
    exact h
  · refine Eq.trans ?_ (hl.2 ρ)
    unfold relab labE
    rw [← embV_eq_embF O.c' O.jL hf, ← hσ']
    rfl
  · have h : ChiAt R i σ (T.chiW ((i : ℕ) + 1) (res T σ)) := tie.chiR i σ hg
    rw [hs] at h
    rw [(GlobalTheory.ConjCharUnique.conjChar_unique R F hR i σ).1 _ _ hμ h]
    exact FactsLat.muVal_cast hV (tie.laws.muVal _ hin _ hg')
  · have h := GlobalTheory.EtaConjType.resEta_hasInfExp_of_isEtaConj R F hR i σ hK η' hη
    exact (hypConj_of_chars R F hR i σ hl.1 hl.2).2 μ' η' hμ hη h.1 h.2

end GlobalTheory.GalOne.Facts
