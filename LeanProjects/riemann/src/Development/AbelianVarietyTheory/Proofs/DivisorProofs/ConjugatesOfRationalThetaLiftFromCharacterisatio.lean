import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalLiftOfOneMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JEvExistsAndJEvBar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvInjOfIsModelsOfTie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefMapNormEquivariantBasisOfFive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIoConjOfFive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateCharactersEmbeddingsOfCharacterisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateLiftOfCharacterisationClausesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateLiftUniqueAndBaseDatumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShiftPhaseConjReadingsFiveClausesStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne GlobalTheory.GalLift.Assembly

namespace GlobalTheory.ConjRatLiftFive

set_option maxHeartbeats 1000000 in

theorem oneMapConj5 : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), ∀ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), OMPins T R κw v₀ O i → ∀ h, RepsAt (O i) (v₀ i (sg0 D A)) h → ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → CoefficientBaseChange R i (O i).jL (inC (O i).c') (c0L i) (O i).c0' → ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∀ (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i) (μ' η' : (AE D)ˣ →* Circle), ChiAt R i σ μ' → IsEtaConj σ R.eta η' → ∀ (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ (c0L i) c c₁ H j → ∀ (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (thP : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))), LiftData R i σ μ' η' c H ω f₀ f B io thP → ∃ (u : GA D (Wc D i) → ℂ) (z : G) (κ : ℂ), PhaseFun R i u ∧ z ∈ Subgroup.center G ∧ ‖κ‖ = 1 ∧ EquivBy (O i) κw σ hV u ∧ ∀ x₀ (n : ℕ) (a : Fin n → D.what₂.LL) (fs : Fin n → Cu T κw i), IsClassSum (O i) κw h x₀ a fs → ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, (fun ρ => (v ρ : (R.MW i σ).sm ρ)) = v₀ i σ → ∀ g, κ * thP ((c.ext ∘ₗ H.e).rangeRestrict (j x₀)) (PiTensorProduct.tprod ℂ v) g = ∑ k, σ (a k) * (u g * phiC T hV (wtA (κw i)) (actG (O i) z (fs k : T.R ((i : ℕ) + 1))) g) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR tie i O hO h hh gramR c0R c0L _ hc σ hσ hV μ' η' hμ hη c c₁ H j hj ω f₀ f B io thP hL
  refine hh.elim fun J' hJ => (exists_ext (O i) hO.1 hO.2 σ).elim fun σ' hσ' => ?_
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) f := by
    have h1 := hL.2.1.theta 1
    have e : (1 : PolF D (Wc D i).rank (Vc D i).rank) = MvPolynomial.basisMonomials _ ℂ 0 := by
      rw [MvPolynomial.coe_basisMonomials]; rfl
    rw [e, ptAt, pureTensorO, pureTensorL, Module.Basis.constr_basis] at h1
    simpa [opPow] using h1
  exact oneMap_of_ext_ofFive hR tie (O i) hO.2 hJ.1 hc hσ' (GlobalTheory.GalOne.Facts.factsAt_ofFive T R F κ v₀ hR tie i (O i) hO.2 σ σ' hσ' hσ).1 hV hj
    ⟨hσ, hμ, hη, hL.1, hL.2.1.vec, hth⟩ hL

section Main

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem base_lift5 (hR : GlobalTheory.Core5 R F) (fw : FWTie T R κw v₀) (i : Fin D.R.m) (hE : fw.Evaluates) (hI : EvInj T R v₀)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ) (hP : OMPins T R κw v₀ O i)
    (hO : (O i).OneMapOf (κw i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph)
    (h : (O i).Cl' () → GA D (Vc D i)) (hh : RepsAt (O i) (v₀ i (sg0 D A)) h) :
    ∃ (act : G → Cu T κw i → Cu T κw i) (z : G) (ze : D.what₂.LL),
      (∀ g f, (act g f : T.R ((i : ℕ) + 1)) = actG (O i) g (f : T.R ((i : ℕ) + 1))) ∧ z ∈ Subgroup.center G ∧
      (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x₀, ∃ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → Cu T κw i),
        IsClassSum (O i) κw h x₀ a f ∧ IsRatLift R i ph x₀ (ratOf fw i act z ze a f) := by
  choose act hact hj using (GlobalTheory.T.conjugateLift_unique_and_baseDatum).2.2.2.1 T R F κw v₀ hR fw i hE hI O hO.1
  have hq1 := (GlobalTheory.T.conjugateLift_unique_and_baseDatum).2.2.2.2 T R F κw v₀ hR fw i hE hI O ph hP hO h hh
  obtain ⟨z, hz, ze, hze, hx⟩ := hq1
  refine ⟨act, z, ze, hact, hz, hze, fun x₀ => ?_⟩
  have hq2 := hx x₀
  obtain ⟨n, a, f, hc, he⟩ := hq2
  refine ⟨n, a, f, hc, ?_⟩
  have hs : ∀ b, D.what₂.embLL b = sg0 D A b := fun b => by rw [sign_at_base_place_eq_embedding R]
  have h1 := he (fun k => act z (f k)) (fun k => hact z (f k))
  have h2 := read_sum (sg0 D A) ((R.FW i).j (sg0 D A)) (crdF fw i) act (R.FW i).chi (R.gW i (sg0 D A))
    (fun g f => by rw [← hs]; exact hj g f) (fun g => (idemOf A.X).coeff g) (fun k => ze * a k) (fun k => act z (f k))
  refine h2.trans (Eq.trans ?_ h1.symm)
  simp only [hs]
  rfl

set_option maxHeartbeats 800000 in

theorem conj_lift5 (hR : GlobalTheory.Core5 R F) (fw : FWTie T R κw v₀) (i : Fin D.R.m) (hE : fw.Evaluates)
    (hI : EvInj T R v₀) (hinj : Function.Injective ((R.FW i).j (sg0 D A)))
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ) (hP : OMPins T R κw v₀ O i)
    (hO : (O i).OneMapOf (κw i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph)
    {gramR c0R c0L} (hT : Comparison₂ R gramR c0R c0L) (hC : CoefficientBaseChange R i (O i).jL (inC (O i).c') (c0L i) (O i).c0')
    (σ : D.what₂.LL →+* ℂ) (hσ : OverK σ) {μ' η' : (AE D)ˣ →* Circle} (hμ : ChiAt R i σ μ') (hη : IsEtaConj σ R.eta η')
    {c : CoefA (Vc D i)} {c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W} {H : HMod (Bridge.Gf (Vc D i) → c.W)}
    {j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H} (hF : IsConjForms R i σ (c0L i) c c₁ H j) {ω f₀ f B io thP}
    (hL : LiftData R i σ μ' η' c H ω f₀ f B io thP) :
    ∃ (th : H.H →ₗ[ℂ] (R.HW i σ).H) (u : GA D (Wc D i) → ℂ) (U : (R.HW i σ).H ≃ₗᵢ[ℂ] (R.HW i σ).H) (z : G) (κ : ℂ),
      IsProjOf R i σ thP th ∧ IsCompPhase R i σ u U ∧ z ∈ Subgroup.center G ∧ ‖κ‖ = 1 ∧
      ∀ x y, IsRatLift R i ph x y → U ((R.FW i).j σ y) = κ • R.gW i σ z (th (j x)) := by
  refine (exists_reps hP).elim fun h hh => ?_
  have hg : GoodEmb T.Q.c (res T σ) := (GlobalTheory.GalLift.overK_iff_good_ofFive T R F κw v₀ hR fw i σ).1 hσ
  have hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i := fw.laws.toLawsM.spaceW _ (inR i) _ hg
  have hq3 := base_lift5 hR fw i hE hI O ph hP hO h hh
  obtain ⟨act, z₀, ze, hact, hz₀, ⟨m, hm, hze⟩, hx⟩ := hq3
  have hq4 := oneMapConj5 T R F κw v₀ hR fw i O hP h hh gramR c0R c0L hT hC σ hσ hV
    μ' η' hμ hη c c₁ H j hF ω f₀ f B io thP hL
  obtain ⟨u, z, κ, hu, hz, hκ, hEq, hid⟩ := hq4
  have hq5 := (GlobalTheory.T.centralShift_phase_conjReadings_fiveClauses).2.1 R F hR i σ u hu
  obtain ⟨U, hU⟩ := hq5
  have hq6 := (GlobalTheory.T.conjugateLift_unique_and_baseDatum).2.2.1 R F hR i
  obtain ⟨hlift, htr⟩ := hq6
  have hq7 := htr σ
  obtain ⟨htr, hW⟩ := hq7
  let J : (Fin (R.nW i) → D.what₂.LL) →ₛₗ[σ] (R.HW i σ).H := U.toLinearEquiv.toLinearMap.comp ((R.FW i).j σ)
  let ev : (R.HW i σ).H →ₗ[ℂ] (GA D (Wc D i) → ℂ) := evL (R.HW i σ).e (v₀ i σ)
  have hev : Function.Injective ev := hI i σ hg
  have hJ : ∀ (f : Cu T κw i) g, ev (J (crdF fw i f)) g =
      u g * phiC T hV (wtA (κw i)) (f : T.R ((i : ℕ) + 1)) g := fun f g =>
    (hU.2.2.2.2 _ _ _).trans (congrArg (u g * ·) (congrFun (hE i σ hg hV f) g))
  have hJa : ∀ z (f : Cu T κw i) g, ev (J (crdF fw i (act z f))) g =
      u g * phiC T hV (wtA (κw i)) (actG (O i) z (f : T.R ((i : ℕ) + 1))) g := fun z f g =>
    (hJ (act z f) g).trans (congrArg (fun w => u g * phiC T hV (wtA (κw i)) w g) (hact z f))
  have hJe : ∀ g f, J (crdF fw i (act g f)) = σ (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) • R.gW i σ g (J (crdF fw i f)) := by
    intro g f
    have hk := hlift g
    obtain ⟨k, hk⟩ := hk
    refine hev (Eq.trans (funext fun x => ?_) (ev.map_smul _ _).symm)
    exact (hJa g f x).trans ((hEq g k hk f x).trans (congrArg (σ (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) * ·)
      ((hJ f (x * k)).symm.trans (htr g k hk _ _ x).symm)))
  let v : ∀ ρ, lowT (R.MW i σ) ρ := fun ρ => ⟨v₀ i σ ρ, ((fw.hv₀ i σ).1 ρ).2.1⟩
  have hS : ∀ x₀ (n : ℕ) (a : Fin n → D.what₂.LL) (fs : Fin n → Cu T κw i), IsClassSum (O i) κw h x₀ a fs →
      κ • thP ((c.ext ∘ₗ H.e).rangeRestrict (j x₀)) (PiTensorProduct.tprod ℂ v) =
        ∑ k, σ (a k) • ev (J (crdF fw i (act z (fs k)))) := by
    intro x₀ n a fs hc
    funext g
    refine (hid x₀ n a fs hc v rfl g).trans (Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (Finset.sum_apply g Finset.univ fun k => σ (a k) • ev (J (crdF fw i (act z (fs k))))).symm)
    exact congrArg (σ (a k) * ·) (hJa z (fs k) g).symm
  have hex : ∀ x, ∃ t : (R.HW i σ).H, (R.HW i σ).e t (fun ρ => v ρ) =
      thP ((c.ext ∘ₗ H.e).rangeRestrict (j x)) (PiTensorProduct.tprod ℂ v) := fun x => by
    have h1 := hx x
    obtain ⟨n, a, fs, hc, -⟩ := h1
    exact exists_ev ev hκ _ _ _ (hS x n a fs hc)
  have h2 := (GlobalTheory.T.conjugateLift_of_characterisationClauses).2.2.2.2.2 R F hR i gramR c0R c0L hT σ hσ μ' η' c c₁ H j hF ω f₀ f B io thP hL v (fw.hv₀ i σ).1 hex
  obtain ⟨th, hth⟩ := h2
  refine ⟨th, u, U, z₀ * z⁻¹, σ ze * σ (((R.FW i).chi z₀ : D.what₂.LLˣ) : D.what₂.LL) *
    (σ (((R.FW i).chi z : D.what₂.LLˣ) : D.what₂.LL))⁻¹ * κ, hth, hU, mul_mem hz₀ (inv_mem hz), ?_, fun x y hy => ?_⟩
  · rw [norm_mul, norm_mul, norm_mul, norm_inv, norm_chi, norm_chi, hκ,
      norm_of_pow hm (a := σ ze) (by rw [← map_pow, hze, map_one])]
    norm_num
  · have h1 := hx x
    obtain ⟨n, a, fs, hc, hy'⟩ := h1
    have hyy : y = ratOf fw i act z₀ ze a fs := hinj (Eq.trans hy (Eq.symm hy'))
    refine (congrArg J hyy).trans ?_
    exact conj_abstract σ J (crdF fw i) act (R.FW i).chi (R.gW i σ) hJe (fun g => (idemOf A.X).coeff g) ev hev (R.eWf i σ)
      (fun y => hW y (v₀ i σ)) hz₀ hz ze κ a fs _ (hS x n a fs hc) (th (j x)) (hth (j x) v)

theorem hypConj5 (hR : GlobalTheory.Core5 R F) (i : Fin D.R.m) {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ) {μ' η' : (AE D)ˣ →* Circle}
    (hμ : ChiAt R i σ μ') (hη : IsEtaConj σ R.eta η') : HypConj R i σ μ' η' :=
  (GlobalTheory.GalLift.hypConj_of_chars_ofFive R F hR i σ ((GlobalTheory.GalLift.labels_overK σ).1 hσ).1 ((GlobalTheory.GalLift.labels_overK σ).1 hσ).2).2 μ' η' hμ hη
    (GlobalTheory.EtaConjType.resEta_hasInfExp_of_isEtaConj_ofFive R F hR i σ hσ η' hη).1 (GlobalTheory.EtaConjType.resEta_hasInfExp_of_isEtaConj_ofFive R F hR i σ hσ η' hη).2

theorem lift_unique5 (hR : GlobalTheory.Core5 R F) (fw : FWTie T R κw v₀) (hI : EvInj T R v₀) (i : Fin D.R.m) {gramR c0R c0L}
    (hT : Comparison₂ R gramR c0R c0L) {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ) {μ' η' c c₁ H j th μ'' η'' c' c₁' H' j' th'}
    (h : IsConjDatum R i σ (c0L i) μ' η' c c₁ H j th) (h' : IsConjDatum R i σ (c0L i) μ'' η'' c' c₁' H' j' th') :
    ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ x, th' (j' x) = κ • th (j x) := by
  have e1 : μ'' = μ' := (GlobalTheory.ConjCharUnique.conjChar_unique_ofFive R F hR i σ).1 _ _ h'.1 h.1
  have e2 : η'' = η' := (GlobalTheory.ConjCharUnique.conjChar_unique_ofFive R F hR i σ).2 _ _ h'.2.1 h.2.1
  subst e1 e2
  have h1 := (isConjLift_iff R i σ _ _ _ _ _).1 h.2.2.2
  obtain ⟨ω, f₀, f, B, io, thP, hL, hp⟩ := h1
  have h2 := (isConjLift_iff R i σ _ _ _ _ _).1 h'.2.2.2
  obtain ⟨ω', f₀', f', B', io', thP', hL', hp'⟩ := h2
  have h3 := (GlobalTheory.T.conjugateLift_unique_and_baseDatum).1 R F hR i gramR c0R c0L hT σ hσ _ _ c c₁ H j c' c₁' H' j' h.2.2.1 h'.2.2.1 ω f₀ f B io thP
    ω' f₀' f' B' io' thP' hL hL'
  obtain ⟨κ, hκ, he⟩ := h3
  have hg : GoodEmb T.Q.c (res T σ) := (GlobalTheory.GalLift.overK_iff_good_ofFive T R F κw v₀ hR fw i σ).1 hσ
  let v : ∀ ρ, lowT (R.MW i σ) ρ := fun ρ => ⟨v₀ i σ ρ, ((fw.hv₀ i σ).1 ρ).2.1⟩
  let ev : (R.HW i σ).H →ₗ[ℂ] (GA D (Wc D i) → ℂ) := evL (R.HW i σ).e (v₀ i σ)
  have hev : Function.Injective ev := hI i σ hg
  refine ⟨κ, hκ, fun x => hev (Eq.trans ?_ (ev.map_smul _ _).symm)⟩
  exact (hp' (j' x) v).trans ((congrArg (R.eWf i σ) (he x _)).trans
    (((R.eWf i σ).map_smul _ _).trans (congrArg (κ • ·) (hp (j x) v).symm)))

theorem conjugateRationalLift_at_embedding_of_datum (hR : GlobalTheory.Core5 R F) (fw : FWTie T R κw v₀) (hI : EvInj T R v₀) (i : Fin D.R.m) {gramR c0R c0L}
    (hT : Comparison₂ R gramR c0R c0L) {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ) (ph : ℂ) {μ' η' c c₁ H j th}
    (h : IsConjDatum R i σ (c0L i) μ' η' c c₁ H j th) {u U} (hU : IsCompPhase R i σ u U) (hu : σ = sg0 D A → ∀ h, u h = 1)
    {z : G} (hz : z ∈ Subgroup.center G) {κ : ℂ} (hκ : ‖κ‖ = 1)
    (he : ∀ x y, IsRatLift R i ph x y → U ((R.FW i).j σ y) = κ • R.gW i σ z (th (j x))) : ConjAt R i σ ph (c0L i) := by
  have h1 := (GlobalTheory.T.centralShift_phase_conjReadings_fiveClauses).1 R F hR i σ z hz
  obtain ⟨ζ, hζ⟩ := h1
  refine ⟨(GlobalTheory.GalLift.hypConj_of_chars_ofFive R F hR i σ ((GlobalTheory.GalLift.labels_overK σ).1 hσ).1 ((GlobalTheory.GalLift.labels_overK σ).1 hσ).2).1, ⟨_, _, _, _, _, _, _, h⟩,
    u, U, z, ζ, hU, hu, hζ, fun μ'' η'' c' c₁' H' j' th' h' => ⟨hypConj5 hR i hσ h'.1 h'.2.1, ?_⟩⟩
  have h2 := lift_unique5 hR fw hI i hT hσ h h'
  obtain ⟨κ', hκ', e⟩ := h2
  refine ⟨κ * κ'⁻¹, by rw [norm_mul, norm_inv, hκ, hκ']; norm_num, fun x y hy => ?_⟩
  exact (he x y hy).trans (smul_inv_of (R.gW i σ z) hκ' (e x))

theorem conjAt_base5 (hR : GlobalTheory.Core5 R F) (fw : FWTie T R κw v₀) (hI : EvInj T R v₀) (i : Fin D.R.m) {gramR c0R c0L}
    (hT : Comparison₂ R gramR c0R c0L) {ph : ℂ} (hph : ‖ph‖ = 1) : ConjAt R i (sg0 D A) ph (c0L i) := by
  have hσ : OverK (sg0 D A) := fun x _ => congrArg (fun s : D.what₂.LL →+* ℂ => s (D.embE x)) (sign_at_base_place_eq_embedding R)
  have h1 := (GlobalTheory.T.conjugateLift_unique_and_baseDatum).2.1 T R F κw v₀ hR fw i gramR c0R c0L hT ((GlobalTheory.T.conjugateCharacters_embeddings_of_characterisation).2.1 R F hR i)
  obtain ⟨c₁, j, hd, hj⟩ := h1
  refine conjugateRationalLift_at_embedding_of_datum hR fw hI i hT hσ ph hd (u := fun _ => 1) (U := LinearIsometryEquiv.refl ℂ _)
    ⟨fun _ => norm_one, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun y v h => (one_mul _).symm⟩
    (fun _ _ => rfl) (one_mem _) hph fun x y hy => ?_
  refine Eq.trans hy (congrArg (ph • ·) ?_)
  exact (congrArg (R.thG i A.μ0) (hj x).symm).trans (LinearMap.congr_fun (map_one (R.gW i (sg0 D A))) _).symm

theorem conjugateRationalLift_at_nonBaseEmbedding (hR : GlobalTheory.Core5 R F) (fw : FWTie T R κw v₀) (i : Fin D.R.m) (hE : fw.Evaluates)
    (hI : EvInj T R v₀) (hinj : Function.Injective ((R.FW i).j (sg0 D A)))
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ) (hP : OMPins T R κw v₀ O i)
    (hO : (O i).OneMapOf (κw i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph)
    {gramR c0R c0L} (hT : Comparison₂ R gramR c0R c0L) {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ) (hne : σ ≠ sg0 D A) :
    ConjAt R i σ ph (c0L i) := by
  have h0 := hP.2.lift.c0
  obtain ⟨gramR', c0R', c0L', hT', hC⟩ := h0
  have hg : GoodEmb T.Q.c (res T σ) := (GlobalTheory.GalLift.overK_iff_good_ofFive T R F κw v₀ hR fw i σ).1 hσ
  have hμ := fw.chiR i σ hg
  have h1 := (GlobalTheory.T.conjugateCharacters_embeddings_of_characterisation).2.2.1 R F hR i ((GlobalTheory.T.conjugateCharacters_embeddings_of_characterisation).2.1 R F hR i) σ hσ
  obtain ⟨η', hη⟩ := h1
  have hH := hypConj5 hR i hσ hμ hη
  have h2 := (GlobalTheory.T.conjugateLift_of_characterisationClauses).1 R F hR i gramR' c0R' c0L' hT' σ hσ
  obtain ⟨c, c₁, hc⟩ := h2
  have h3 := (GlobalTheory.T.conjugateLift_of_characterisationClauses).2.1 R F hR i gramR' c0R' c0L' hT' σ c c₁ hc
  obtain ⟨H, j, hF⟩ := h3
  have h4 := (GlobalTheory.T.conjugateCharacters_embeddings_of_characterisation).2.2.2.2.2.2.1 R F hR i σ _ η' hμ hη hH
  obtain ⟨ω, hω⟩ := h4
  have h5 := (GlobalTheory.T.conjugateLift_of_characterisationClauses).2.2.2.1 R F hR i σ hσ
  obtain ⟨f₀, f, B, hv⟩ := h5
  have h6 := GlobalTheory.MovedWeights.exists_io_conj_ofFive R F hR i σ hσ _ η' hμ hH c c₁ hc ω f₀ f B hω hv
  obtain ⟨io, hio⟩ := h6
  have h7 := (GlobalTheory.T.conjugateLift_of_characterisationClauses).2.2.2.2.1 R F hR i σ _ η' _ c c₁ H j hF ω f₀ f B io hω hv
  obtain ⟨thP, hth⟩ := h7
  have hL : LiftData R i σ _ η' c H ω f₀ f B io thP := ⟨hω, hv, hio, hth⟩
  have h8 := conj_lift5 hR fw i hE hI hinj O ph hP hO hT' hC σ hσ hμ hη hF hL
  obtain ⟨th, u, U, z, κ, hp, hU, hz, hκ, he⟩ := h8
  have h9 := (GlobalTheory.T.conjugateLift_of_characterisationClauses).2.2.1 R F hR i gramR c0R c0L hT gramR' c0R' c0L' hT' σ c c₁ H j hF
  obtain ⟨c₁', hF'⟩ := h9
  exact conjugateRationalLift_at_embedding_of_datum hR fw hI i hT hσ ph ⟨hμ, hη, hF', (isConjLift_iff R i σ _ _ _ _ _).2 ⟨ω, f₀, f, B, io, thP, hL, hp⟩⟩ hU
    (fun h => absurd h hne) hz hκ he

end Main

theorem conjRatLift5 : GlobalTheory.LowRow.ConjRatLift5 := by
  intro D G _ _ Pl0 T0 A T _ R F κw v₀ O ph hR _ fw hb _ hLU hP i hO
  have hJ' := GlobalTheory.ConjReading.jEvExists_and_jEvBar T R κw v₀ O hR.lev hR.models fw hP
  have hI : EvInj T R v₀ := GlobalTheory.EvalAtUnitVectorFinal.evInj_of_isModels_of_tie T R κw v₀ hR.models fw
  have hE : fw.Evaluates := fw.evaluates hJ'.1
  have hinj : Function.Injective ((R.FW i).j (sg0 D A)) := GlobalTheory.GalOne.inj_of_indep _ (hLU i (sg0 D A)).1
  refine ⟨fun x => ?_, fun gramR c0R c0L hT σ hσ => ?_, fun σ hσ => ⟨(GlobalTheory.GalLift.labels_overK σ).2 hσ, ?_⟩⟩
  · obtain ⟨h, hh⟩ := exists_reps (hP i)
    obtain ⟨act, z, ze, -, -, -, hx⟩ := base_lift5 hR fw i hE hI O ph (hP i) hO h hh
    obtain ⟨n, a, f, -, hy⟩ := hx x
    exact ⟨_, hy, fun y hy' => hinj (Eq.trans hy' (Eq.symm hy))⟩
  · by_cases hs : σ = sg0 D A
    · subst hs
      exact conjAt_base5 hR fw hI i hT hO.2.1.2.2.2.2.1
    · exact conjugateRationalLift_at_nonBaseEmbedding hR fw i hE hI hinj O ph (hP i) hO hT hσ hs
  · exact (GlobalTheory.T.centralShift_phase_conjReadings_fiveClauses).2.2 T R F κw v₀ hR fw i hJ'.1 hJ'.2 hb σ fun hg =>
      hσ ((GlobalTheory.GalLift.overK_iff_good_ofFive T R F κw v₀ hR fw i σ).2 hg)

end GlobalTheory.ConjRatLiftFive

end
