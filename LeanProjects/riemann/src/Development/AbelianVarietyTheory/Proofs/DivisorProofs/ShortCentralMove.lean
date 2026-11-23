import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseRatAtOfPhaseOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicLiftEqGeometricClassSumAllTuples
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameConstantsOfCharacterisationCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstUpToCenter
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeafDataOfOnTieOfIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistTrivialOnRational
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDetOfMemSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupLevelStructureActionFixedRuns
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLevelChangeActionOnCuspForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapAllComparison
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
import Formalism.LocalToGlobal.ProjectiveLattices.I2AtFramePointsAlpha
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionShortThetaSeriesRootOfUnityMul
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeTransferRankOne

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CentralLevelMove

section Const

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.ShortMove GlobalTheory.TraceLattice
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem exists_const_int {D : D7} (T : Full D) (hT : LawsFull T) {j : ℕ} (hj : InR D j) (hxi : TwistTrivialOnRational T j)
    {w : WeightFamilies.Wt D j} (hw : D.R.r ≤ w.n)
    (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l) :
    ∃ u : 𝓞 T.Q.c.F, (u : T.Q.c.F) ≠ 0 ∧ ∀ Λ N P x x' f f', GoodDatum T.toTop j w Λ N P → IsRightMul γ x' x →
      IsSeries T.toTop j w Λ N P x f → IsSeries T.toTop j w Λ N P x' f' → mv T.toTop j γ f = (u : T.Q.c.F) • f' := by
  have hC := GlobalTheory.chartIndependence_unconditional
  have hL := GlobalTheory.firstFiveLaws.1
  have hpq := rank_eq hT.p.pins hj
  have hA : T.Q.l.A = 1 := hT.p.pins.2.1.2
  have hAct := GlobalTheory.T.actLev_full_level_group_framedPoints D T.Q j hpq hA
  have hLev := hT.sh.dLev j hj w.n
  have hA₂ := hT.lvA j hj w.n
  obtain ⟨inst, hnab⟩ := hT.sh.dNab j hj w.n
  obtain ⟨ph, ψ, x₀, -, hpin, htie⟩ := hT.sh.dPhi j hj w.n hw
  have hTot := hT.sh.shTot j hj (wtA w) w.n (dom_wtA w)
  obtain ⟨g, hν, hγ, hg⟩ := GlobalTheory.T.exists_completed_isometry_inducing_half_level_automorphism _ _ (T.Q.Dw j) T.Q.l γ
  obtain ⟨ρ₂, hρ₂⟩ := GlobalTheory.LevelActionLaws.exists_levAut hpq (T.dδ j w.n).Xo₂ g (by rw [hν, sub_self]; exact dvd_zero _)
  obtain ⟨u, hu, hcd⟩ := GlobalTheory.ShortMove.exists_root T hT hj hxi hw g hν ρ₂ hρ₂
  refine ⟨u, hu, fun Λ N P x0 x0' f f' hG hx hf hf' => ?_⟩
  suffices key : IsSeries T.toTop j w Λ N P x0' ((u : T.Q.c.F)⁻¹ • mv T.toTop j γ f) by
    rw [← key.unique hT.sh hj hG hf', smul_inv_smul₀ hu]
  obtain ⟨hX, hsec, hR⟩ := hf
  obtain ⟨hU, hb, hb₂, hO, hP⟩ := hG
  refine ⟨hf'.1, Submodule.smul_mem _ _ (actL_mem _ _ _ _ hAct.total hAct.nat hAct.bor _ γ hsec), ?_⟩
  clear hf'
  generalize T.dδ j w.n = d at *
  have hM := hLev.2.1
  have hM₁ : 0 < T.Q.l.M := by have := T.Q.l.three_le; omega
  have hpd : 0 < d.pd := Nat.pos_of_mul_pos_left (hM ▸ (by have := d.l₂.three_le; omega : 0 < d.l₂.M))
  have hI : ∀ a, g.f d.l₂.M a - a ∈ d.I • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La) := fun a => by
    have hpI : ((d.pd : ℕ) : 𝓞 D.host.E) ∈ d.I := by
      refine (Ideal.mul_le_inf.trans inf_le_left : d.I * d.I.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ d.I) ?_
      rw [GlobalTheory.DatumInverseCharacter.half_prod hM hLev.2.2.2.1]
      exact Ideal.mem_span_singleton_self _
    have h1 := GlobalTheory.DatumInverseCharacter.mem_of_modN _ hpI (g.tower d.pd T.Q.l.M hpd hM₁ a)
    have h2 := GlobalTheory.DatumInverseCharacter.mem_of_modN _ hpI (hg d.pd hpd hLev.2.2.1 a)
    have := add_mem h1 h2
    rwa [sub_add_sub_cancel, mul_comm, ← hM] at this
  have hγ' : ∀ a, g.f d.l₂.M a - liftLa γ a ∈ T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La) := fun a => by
    have h1 := GlobalTheory.DatumInverseCharacter.mem_of_modN _ (natCast_mem_half T.Q.l).1 (g.tower T.Q.l.M d.pd hM₁ hpd a)
    have h2 : g.f T.Q.l.M a - liftLa γ a ∈ T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La) :=
      (Submodule.Quotient.eq _).1 ((hγ a).trans (liftLa_spec γ a).symm)
    have := add_mem h1 h2
    rwa [sub_add_sub_cancel, ← hM] at this
  obtain ⟨σq, hσ, -⟩ := GlobalTheory.T.levelCoverDatum_similitude_adjoint_transport _ _ _ _ _ _ _ d hM hLev.2.2.2.1 ph ψ x₀ hpin g hI
  have hw' := datum_move d hM hLev.2.2.2.1 hpin _ hI hγ' σq hσ hx
  obtain ⟨hρs, ν₂, hη, hηA⟩ := hρ₂
  have hmv₂ : IsLevMove ρ₂.hom ν₂ (g.f d.l₂.M) (g.f d.l₂.A) := ⟨hρs, hη, hηA⟩
  have hP₂ := (GlobalTheory.admissible_columns_le_and_harmonic_map_cover _ _ _ _ _ _ _ d).2 _ P hP.1
  intro k _ _ _ _ hk y y₂ ho
  have hev := evalAt_actL hAct (hT.p.evalWD j hj) frMap_trans_id γ hsec.1 y
  obtain ⟨ρ, ν, -, hmv, hfr⟩ := mvPt_spec hAct.total γ y
  generalize mvPt _ _ γ y = y' at hev hfr
  obtain ⟨y₂', hfr₂⟩ := (GlobalTheory.exists_unique_frMove _ _ _ _ d.Xo₂ d.c₂ ρ₂.hom ν₂ hρs k y₂).1
  obtain ⟨r', m', hr', hm', hE'⟩ := GlobalTheory.T.exists_conj_levelMap_by_levelMoves _ _ _ _ _ _ _ d hLev.2.2.2.2.2.1 ρ ν ρ₂ ν₂ _ _ _ _ hmv hmv₂ hγ'
    (fun a => ⟨_, by rw [hA, one_smul]⟩)
  have ho' := GlobalTheory.T.liesOverFramed_of_square_levelMoves _ _ _ _ _ _ _ d ρ ν ρ₂.hom ν₂ r' m' hr' hm' k y y' y₂ y₂' ho hfr hfr₂
  obtain ⟨z₂, hz₂⟩ := hLev.2.2.2.2.2.2.1 k hk y'
  obtain ⟨v, hv, hfv⟩ := hR k hk y' z₂ hz₂
  obtain ⟨v', hv', -⟩ := (hTot Λ N x0 P hU hb hb₂ hO hX hP).1 k y₂'
  have e₁ := GlobalTheory.ShortLiftInvariance.cover_product_indep_of_lift hL hC _ _ _ _ _ _ _ d
    (GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.2 _ _ _ hpq).1 hLev (hA₂.trans hA.symm) hnab ⟨ph, ψ, x₀, hpin, htie⟩ Λ N hU hb₂ hO _ _ hP₂ x0 _
    r' m' hE' k hk y' z₂ y₂' hz₂ ho' v v' hv hv'
  have e₂ := GlobalTheory.T.shortThetaValue_under_levelMove hL hC _ _ _ _ d.Xo₂ d.c₂ d.nab₂ hnab k ρ₂.hom ν₂ _ _ y₂ y₂' hmv₂ hfr₂ σq hσ
    _ _ _ hP₂ (d.w x0) Λ _ N v' hv'
  rw [funext hw'] at e₂
  refine ⟨v', e₂, (evalAt_smul _ _ _ _ y).trans ?_⟩
  refine (congrArg (_ * ·) (hev.trans (hfv.trans e₁))).trans ?_
  rw [hcd k y₂ y₂' hfr₂.1, hk, ← mul_assoc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hu, map_one, one_mul]

end Const

end GlobalTheory.CentralLevelMove

namespace GlobalTheory.CentralLevelMove

section SlopeTestRemainingChoices

open NumberField Formalism.L2.Pj GlobalTheory.OnTies
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

theorem isRightMul_of_symm {γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l} {n : ℕ} {x x' : Fin n → Dw.La}
    (h : IsRightMul γ.symm x x') : IsRightMul γ x' x := by
  intro b a
  have h1 := h b (liftLa γ a)
  have hq : liftLa γ.symm (liftLa γ a) - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
    rw [← Submodule.Quotient.eq]
    have e1 := liftLa_spec γ.symm (liftLa γ a)
    have e2 := liftLa_spec γ a
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at e1 e2
    rw [e1, e2, LinearEquiv.symm_apply_apply]
  have h2 := GlobalTheory.OnTies.dvd_pair_of_mem (x b) hq
  rw [smul_sub, map_sub] at h2
  have h3 := dvd_add h1 h2
  have e : Dw.EF (x b) (cSep l • a) - Dw.EF (x' b) (cSep l • liftLa γ a) =
      -((Dw.EF (x' b) (cSep l • liftLa γ a) - Dw.EF (x b) (cSep l • liftLa γ.symm (liftLa γ a))) +
        (Dw.EF (x b) (cSep l • liftLa γ.symm (liftLa γ a)) - Dw.EF (x b) (cSep l • a))) := by ring
  rw [e]
  exact dvd_neg.2 h3

end SlopeTestRemainingChoices

section Wrap

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceLattice
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem exists_const_n {D : D7} (T : Full D) (hT : LawsFull T) {j : ℕ} (hj : InR D j) (hxi : TwistTrivialOnRational T j)
    {w : WeightFamilies.Wt D j} {n : ℕ} (hn : w.n = n) (hnV : n = D.R.nV)
    (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l) :
    ∃ u : 𝓞 T.Q.c.F, (u : T.Q.c.F) ≠ 0 ∧ ∀ (Λ : GenLat D.host.E n) (N : ℕ) (P : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F)
      (x x' : Fin n → (T.Q.Dw j).La) (f : T.R j),
      Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ j n).l₂.M → Λ.LevOK N (T.dδ j n).l₂.M →
      P ∈ harmL (Dw := T.Q.Dw j) T.Q.c Λ (wtA w) → IsRightMul γ x' x → AdmX (l := T.Q.l) true x →
      AdmX (l := T.Q.l) true x' → f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n →
      IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) Λ N x P f →
      ∃ f' : T.R j, IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) Λ N x' P f' ∧ mv T.toTop j γ f = (u : T.Q.c.F) • f' := by
  subst hn
  have hd : decide (w.n = D.R.nV) = true := decide_eq_true hnV
  obtain ⟨u, hu, H⟩ := exists_const_int T hT hj hxi (w := w) (hnV ▸ Nat.le_add_right _ _) γ
  refine ⟨u, hu, fun Λ N P x x' f h1 h2 h3 h4 hP hx ha ha' hs hf => ?_⟩
  have hG : GoodDatum T.toTop j w Λ N P := ⟨h1, h2, h3, h4, hP⟩
  obtain ⟨f', hf'⟩ := exists_isSeries hT.sh hj hG (x := x') (hd ▸ ha')
  exact ⟨f', hf'.2.2, H Λ N P x x' f f' hG hx ⟨hd ▸ ha, hs, hf⟩ hf'⟩

end Wrap

end GlobalTheory.CentralLevelMove

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.CentralLevelMove

theorem phi_smul_rule {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
    (O : OMDat C R i Tp tup) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (s : C.Q.c.F) (f : C.R ((i : ℕ) + 1))
    (g : GA D (Wc D i)) : O.phi cc (s • f) g = C.σ₀ s * O.phi cc f g := by
  unfold OMDat.phi
  rw [map_smulₛₗ, map_smul, Pi.smul_apply, smul_eq_mul]
  rfl

end GlobalTheory.CentralLevelMove

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.CentralLevelMove.short_central_move : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∀ (cc : (T.J.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (ka : ℂ) (δ : ℤˣ) (c0 : ℂ), GlobalTheory.AdTh.CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.J.U ((i : ℕ) + 1) (O i).s0) (O i).dict (O i).mu (T.J.x₀ ((i : ℕ) + 1) (O i).s0) (R.ωP i A.μ0) (R.vacP i) cc → GlobalTheory.PtId.IoAt (O i) (v₀ i (sg0 D A)) ka → GlobalTheory.PtId.ClsAt R i (iotaW T.J i) δ → GlobalTheory.PtId.CovAt (O i) c0 → ‖ka‖ = 1 → ‖c0‖ = 1 → ∀ z ∈ Subgroup.center G, ∃ (x' : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (ε : D.what₂.LL), AdmX (l := T.Q.l) true x' ∧ IsIntegral ℤ ε ∧ ∀ F₀ : (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i), IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N x₀ P ((F₀).1 : T.R ((i : ℕ) + 1)) → ∃ F₁ : (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i), IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N x' P ((F₁).1 : T.R ((i : ℕ) + 1)) ∧ ∀ (cst : (T.J.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (g : GA D (Wc D i)), (O i).phi cst (actLev T.J.toCore.Q.c (O i).lev2 z⁻¹ ((F₀).1 : T.R ((i : ℕ) + 1))) g = D.what₂.embLL ε * (O i).phi cst ((F₁).1 : T.R ((i : ℕ) + 1)) g := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hc i hOP _ _ _ _ _ v _ _ _ _ _ _ hMb hRP ℓ _ _ χ ξR ω φ _ Λ h _ _ N x₀ P y
    h1 h2 h3 h4 ha₀ hP _ cc ka δ c0 _ _ _ _ _ _ z _
  classical
  have hlev : LevIs R i (iotaW T.J i) T.J.Q.l.M (Mfr T.J.Q.l) (O i).lev := hOP.2.lift.lev
  have hι : LatEmb (Wc D i) (iotaW T.J i) := GlobalTheory.TraceLattice.latEmb_iotaW hT i
  have hβ : IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1 := hc.lev.βW i
  obtain ⟨h1', hm⟩ := GlobalTheory.LevelActionPinned.congr_of_levIs R i hι hβ hMb hlev
  have hbij : Function.Bijective (GlobalTheory.LevelActionOnto.quotMap T.J.Q.l.Mb ((O i).lev z⁻¹)) := by
    refine GlobalTheory.LevelActionOnto.quotMap_bijective _ _ ((O i).lev z) (fun a => ?_) (fun a => ?_)
    · have e1 := hm z⁻¹ z a
      have e2 := h1' a
      rw [inv_mul_cancel] at e1
      have := Submodule.sub_mem _ e2 e1
      rwa [sub_sub_sub_cancel_left] at this
    · have e1 := hm z z⁻¹ a
      have e2 := h1' a
      rw [mul_inv_cancel] at e1
      have := Submodule.sub_mem _ e2 e1
      rwa [sub_sub_sub_cancel_left] at this
  set γ := GlobalTheory.LevelActionOnto.quotEquiv T.J.Q.l.Mb ((O i).lev z⁻¹) with hγ
  have hspec : ∀ a, liftLa γ a - (O i).lev z⁻¹ a ∈
      T.J.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (T.J.Q.Dw ((i : ℕ) + 1)).La) := fun a => by
    rw [← Submodule.Quotient.eq]
    have := liftLa_spec γ a
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at this
    rw [this]
    exact GlobalTheory.LevelActionOnto.quotEquiv_mk _ _ hbij a
  have hA : T.J.Q.l.A = 1 := hT.j.pins.2.1.2
  have hact_eq : actLev (Xo := T.J.Q.Xo ((i : ℕ) + 1)) T.J.Q.c (levFull (T.J.Q.Dw ((i : ℕ) + 1)) T.J.Q.l) γ =
      actLev T.J.toCore.Q.c (O i).lev2 z⁻¹ := by
    have e1 : actLev (Xo := T.J.Q.Xo ((i : ℕ) + 1)) T.J.Q.c (levFull (T.J.Q.Dw ((i : ℕ) + 1)) T.J.Q.l) γ =
        actLev (Xo := T.J.Q.Xo ((i : ℕ) + 1)) T.J.Q.c
          (fun _ : Unit => levFull (T.J.Q.Dw ((i : ℕ) + 1)) T.J.Q.l γ) () := rfl
    have e2 : actLev (Xo := T.J.Q.Xo ((i : ℕ) + 1)) T.J.Q.c (O i).lev2 z⁻¹ =
        actLev (Xo := T.J.Q.Xo ((i : ℕ) + 1)) T.J.Q.c (fun _ : Unit => (O i).lev2 z⁻¹) () := rfl
    rw [e1, e2, GlobalTheory.OneMapAllCompare.actLev_congr (lev' := fun _ : Unit => (O i).lev2 z⁻¹) T.J.Q.c hA
      (fun _ a => hspec a)]
  have hnV : (κ i).n = D.R.nV := (fw.kap i (D.eTau.symm 1)).2.2
  have hnV' : (Vc D i).rank = D.R.nV := (GlobalTheory.IndefiniteRowSideFullHecke.HeckeTransferRankOne.rank_Vc i).1
  have hxi := GlobalTheory.TraceLattice.twistTrivial_of_runPin hT hRP
  obtain ⟨u, hu0, H⟩ := GlobalTheory.CentralLevelMove.exists_const_n T hT (inR_succ i) hxi (w := κ i) (hnV.trans hnV'.symm) hnV' γ
  obtain ⟨x', hx'r, ha'⟩ := GlobalTheory.TraceLattice.exists_rightMul γ.symm ha₀
  have hx' : IsRightMul γ x' x₀ := GlobalTheory.CentralLevelMove.isRightMul_of_symm hx'r
  obtain ⟨act, hact⟩ := GlobalTheory.FormTies.exists_isLevAct D T.toTop hT.p ((i : ℕ) + 1) (inR_succ i) (κ i) Unit (fun _ => γ)
  have e0 : ∀ y, D.what₂.embLL (algebraMap T.J.Q.c.F D.what₂.LL y) = T.J.σ₀ y :=
    RingHom.congr_fun (res_embLL T.J fw.alg_eq fw.laws.pins.2.2.1)
  have hsI : IsIntegral ℤ (show T.J.Q.c.F from (u : T.Q.c.F)) := NumberField.RingOfIntegers.isIntegral_coe u
  refine ⟨x', algebraMap T.J.Q.c.F D.what₂.LL (show T.J.Q.c.F from (u : T.Q.c.F)), ha',
    hsI.algebraMap, fun F₀ hF₀ => ?_⟩
  obtain ⟨f', hf', he⟩ := H Λ N P x₀ x' F₀.1 h1 h2 h3 h4 hP hx' ha₀ ha' (cutR_le T.C _ _ F₀.2).1 hF₀
  have hmem : (u : T.Q.c.F)⁻¹ • ((act () F₀).1 : T.R ((i : ℕ) + 1)) ∈ cutR T.C ((i : ℕ) + 1) (κ i) :=
    Submodule.smul_mem _ _ (act () F₀).2
  let F₁ : (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i) := ⟨_, hmem⟩
  have hF₁ : (F₁.1 : T.R ((i : ℕ) + 1)) = f' := by
    show (u : T.Q.c.F)⁻¹ • ((act () F₀).1 : T.R ((i : ℕ) + 1)) = f'
    rw [hact () F₀]
    change (u : T.Q.c.F)⁻¹ • GlobalTheory.TraceLattice.mv T.toTop _ γ F₀.1 = f'
    rw [he, smul_smul, inv_mul_cancel₀ hu0, one_smul]
  refine ⟨F₁, hF₁ ▸ hf', fun cst g => ?_⟩
  rw [← hact_eq]
  change (O i).phi cst (GlobalTheory.TraceLattice.mv T.toTop _ γ F₀.1) g = _
  rw [he, hF₁]
  have e3 := GlobalTheory.CentralLevelMove.phi_smul_rule (O i) cst (show T.J.Q.c.F from (u : T.Q.c.F)) f' g
  refine e3.trans ?_
  rw [e0]
