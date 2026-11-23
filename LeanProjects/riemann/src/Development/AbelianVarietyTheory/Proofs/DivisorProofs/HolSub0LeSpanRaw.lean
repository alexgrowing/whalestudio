import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsVanishingOffFramesLeSpanShortTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnfoldingConstantTermsAgreeAtGoodEmbeddings
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIsNabUncond
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.InducedEqOne
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortValTotOfPinned
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EvaluationLemmaForNablaLevels
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueExistsUniqueNaturalOfLaws
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.BaseClassMove

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RawSpan

section Cover

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

abbrev idCover (nab : NabV Xo c) (n : ℕ) : DeltaDat Xo c n := noDelta Xo c nab (GlobalTheory.ObjLower.sabId Xo.univ.t) n

theorem frOver_self (nab : NabV Xo c) (n : ℕ) {S : Type} [CommRing S] [i : Algebra c.F S] (y : FrPt Xo c S) :
    @FrOver E _ _ _ H Dw l Xo c n (idCover nab n) S _ i i y y := by
  refine (@GlobalTheory.FrameLift.frOver_iff E _ _ _ H Dw l Xo S _ c n (idCover nab n) i i y y).2
    ⟨Category.comp_id _, fun _ _ => Category.comp_id _, GlobalTheory.ObjLower.idIso Xo.univ.t.PP.L, 𝟙 _,
      ⟨(isGen_iff _).2 (GlobalTheory.ObjLower.pgen_idIso Xo.univ.t.PP.isLB), ?_⟩,
      (Category.id_comp _).trans (Category.comp_id _).symm, Category.id_comp _, ?_⟩
  · exact (maps_iff (GlobalTheory.ObjLower.idIso Xo.univ.t.PP.L) _ (fun _ => eSec Xo.univ.t.G) _ Xo.univ.t.PP.rig
      Xo.univ.t.PP.rig (GlobalTheory.ObjLower.cubeId Xo.univ.t.G).e _
      (rigPull_le (GlobalTheory.ObjLower.cubeId Xo.univ.t.G).F (GlobalTheory.ObjLower.cubeId Xo.univ.t.G).e
        (GlobalTheory.ObjLower.cubeId Xo.univ.t.G).e_comm Xo.univ.t.PP.L) (fun _ => rfl)).2
      (GlobalTheory.ObjLower.pmaps_idIso _ _ _ _ Xo.univ.t.PP.rigGen)
  · intro Z r z i j hi hj
    have e := GlobalTheory.ObjLower.gw_idIso Xo.univ.t.PP.L (r ≫ (snd (Over.mk y.x) Xo.univ.t.G).left) z i j hi hj
    have e' := GlobalTheory.FrameLift.sv_trans (q := (snd (Over.mk y.x) Xo.univ.t.G).left) y.s r z hi hj
    exact (congrArg (fun t => GlobalTheory.FrameLift.sv (q := (snd (Over.mk y.x) Xo.univ.t.G).left) y.s t z i)
      (Category.comp_id r)).trans (e'.trans (congrArg (fun u : (Z.presheaf.stalk z)ˣ => u.val * _) e.symm))

theorem evR_one_field (S : Type) [Field S] [Algebra c.F S] (y : FrPt Xo c S) : evR Xo c 1 y = 1 :=
  evalAt_one _ _ y (GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c S y)

theorem idCover_isLev (nab : NabV Xo c) (n : ℕ) : (idCover nab n).IsLev := by
  refine ⟨⟨dvd_rfl, le_rfl, dvd_rfl⟩, (Nat.mul_one _).symm, Nat.coprime_one_left _, (Ideal.mul_top _).symm,
    top_sup_eq _, ?_, ?_, GlobalTheory.LevelCover.one_mem_sec_zero Xo c, ?_⟩
  · rw [GlobalTheory.LevelCoverDatum.noDelta_etaOK]
    exact ⟨fun a => Category.comp_id _, fun a => Category.comp_id _⟩
  · intro k _ _ i₁ i₂ hk y
    have e : i₂ = i₁ := Algebra.algebra_ext _ _ fun a => hk a
    rw [e]
    exact ⟨y, @frOver_self E _ _ _ H Dw l Xo c nab n k _ i₁ y⟩
  · intro k _ _ i y₂
    have := @evR_one_field E _ _ _ H Dw l Xo c k _ i y₂
    exact fun h => one_ne_zero (this.symm.trans h)

theorem idCover_unitC (nab : NabV Xo c) (n : ℕ) : GlobalTheory.Dict.UnitC (idCover nab n) := fun A y =>
  (congrArg norm (@evR_one_field E _ _ _ H Dw l Xo c ℂ _ A y)).trans norm_one

theorem idCover_psiTie (nab : NabV Xo c) (n : ℕ) : (idCover nab n).PsiTie 1 := by
  intro k g ρ _ _ _ _ K _ _ i y y' _
  have a := @evR_one_field E _ _ _ H Dw l Xo c K _ i y
  have b := @evR_one_field E _ _ _ H Dw l Xo c K _ i y'
  refine b.trans ?_
  refine Eq.symm ((congrArg _ a).trans ?_)
  simp

theorem betaH_ne_zero {n : ℕ} (Λ : GenLat E n) : betaH (Dw := Dw) c Λ ≠ 0 := by
  unfold betaH
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_ne_zero

theorem phiHat_indPhi_mk {n : ℕ} (x0 : Fin n → Dw.La) :
    phiHat c (indPhi c fun b => (Submodule.Quotient.mk (x0 b) : LevQc Dw l)) = x0Dat c x0 := by
  have h : phiHat c (indPhi c fun b => (Submodule.Quotient.mk (x0 b) : LevQc Dw l)) =
      x0Dat c fun b => qRep (Submodule.Quotient.mk (x0 b) : LevQc Dw l) := by
    funext q
    unfold phiHat x0Dat indPhi
    rw [finsum_eq_single _ (fun b => (Submodule.Quotient.mk (x0 b) : LevQc Dw l)) (fun x hx => by simp [hx])]
    simp
  rw [h, GlobalTheory.LevelPairing.levelFourierDatum_eq_iff]
  intro b
  exact (Submodule.Quotient.eq _).1 (Classical.choose_spec (Submodule.Quotient.mk_surjective _
    (Submodule.Quotient.mk (x0 b) : LevQc Dw l)))

theorem span_mk_eq_top {n : ℕ} (x0 : Fin n → Dw.La) (h : AdmX (l := l) true x0) :
    Submodule.span (𝓞 E) (Set.range fun b => (Submodule.Quotient.mk (x0 b) : LevQc Dw l)) = ⊤ := by
  unfold AdmX at h
  rw [sup_comm, ← Submodule.map_mkQ_eq_top, Submodule.map_span, Set.image_image] at h
  rw [← h]
  congr 1
  ext z
  simp

theorem thLaValAt_of_isShortRule [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab) {n : ℕ} {Λ : GenLat E n} {N : ℕ}
    (hU : Λ.Unimod) (hT : Λ.TrivAt l.M) (hO : Λ.LevOK N l.M) {a : (E →+* ℂ) × ℕ → ℕ}
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmL c Λ a) (x0 : Fin n → Dw.La) {f : Rul Xo c}
    (hf : f ∈ sec Xo c a n) (h : IsShortRule Xo c (idCover nab n) Λ N x0 P f) (p : TRing c.F) (y : FrPt Xo c p.R) :
    thLaValAt Xo c nab (x0Dat c x0) Λ N P y ((betaH (Dw := Dw) c Λ • f) p y) := by
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  haveI : _root_.IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  obtain ⟨hval, hnat⟩ := GlobalTheory.shortThetaValue_existsUnique_natural hL GlobalTheory.chartIndependence_unconditional E H Dw l Xo c
    nab hnab n Λ N hU hT hO a P hP.1 (x0Dat c x0) (betaH (Dw := Dw) c Λ)
  obtain ⟨v, hv, -⟩ := hval p.R y
  have e : f p y = v := by
    refine GlobalTheory.CoverDescent.eq_of_geometric_points _ _ fun k _ _ χ => ?_
    letI i1 : Algebra c.F k := (χ.comp (algebraMap c.F p.R)).toAlgebra
    let χa : p.R →ₐ[c.F] k := { χ with commutes' := fun _ => rfl }
    obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c p.R k χa y
    obtain ⟨u, hu, eu⟩ := @h k _ _ i1 i1 (fun _ => rfl) z z (frOver_self nab n z)
    have hu' : ShortValAt Xo c nab (x0Dat c x0) Λ (betaH (Dw := Dw) c Λ) N P z u := by
      have e1 : MvPolynomial.map ((idCover nab n).eF : c.F →+* (idCover nab n).c₂.F) P = P := MvPolynomial.map_id P
      rw [e1, GlobalTheory.LevelCoverDatum.noDelta_w] at hu
      exact hu
    have e2 := hnat p.R k χa y z hz v u hv hu'
    have e3 := GlobalTheory.CoverDescent.evR_of_test (GlobalTheory.Frames.algebraic_laws hL.secBaseChange E H Dw l Xo c).2.2.1 f hf.1
      p χa y z hz
    have e4 : evR Xo c f z = u := eu.trans ((congrArg (· * u) (evR_one_field k z)).trans (_root_.one_mul u))
    exact e3.symm.trans (e4.trans e2.symm)
  have e5 : (betaH (Dw := Dw) c Λ • f) p y = algebraMap c.F p.R (betaH (Dw := Dw) c Λ) * v := by
    rw [← e]
    exact Algebra.smul_def (betaH (Dw := Dw) c Λ) (f p y)
  rw [e5]
  exact (GlobalTheory.Survey.BaseClassMove.shortValAt_beta Xo c nab _ Λ _ (betaH_ne_zero Λ) N P y v).1 hv

end Cover

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option maxHeartbeats 1000000 in

theorem holSub0_le_span_raw : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.Pj.Unf Xo c σ r), Formalism.L2.Pj.GoodEmb c σ → Formalism.L2.Pj.IsUnf U → 1 ≤ r → l.A = 1 → (∀ k k', (U.X k).Gm = (U.X k').Gm ∧ (U.X k).ξ0 = (U.X k').ξ0) → (∀ k, GlobalTheory.Dict.HasPrinc (U.X k) l.M) → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (bad n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < bad → Dom a n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → (∀ k, GlobalTheory.Dict.ChiOne (U.X k) (Formalism.L2.Pj.laU U a n k)) → Formalism.L2.Pj.holSub0 U.X (Formalism.L2.Pj.laU U a n) ≤ Submodule.span ℂ (Formalism.L2.Pj.rdU U '' ⋃ (x0 : Fin n → LevQc Dw l) (_ : Submodule.span (𝓞 E) (Set.range x0) = ⊤), {f : Formalism.L2.Pj.Rul Xo c | f ∈ sec Xo c a n ∧ ∃ (La : GenLat E n) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F), La.Unimod ∧ La.TrivAt bad ∧ La.TrivAt l.M ∧ La.LevOK N l.M ∧ P ∈ harmL c La a ∧ ∀ (p : TRing c.F) (y : FrPt Xo c p.R), thLaValAt Xo c nab (phiHat c (indPhi c x0)) La N P y (f p y)}) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hr hA hG hP _ nab hnab bad n a hbad hdom hn hχ
  have hC := GlobalTheory.chartIndependence_unconditional
  have hrk : r = Dw.p + Dw.q := hU.1
  have h1 : 1 ≤ Dw.p + Dw.q := hrk ▸ hr
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  have hB : Out.SecBaseChangeSt := hL.secBaseChange
  have hpin := GlobalTheory.DeltaPinTest.noDelta_phiPin (n := n) nab (GlobalTheory.ObjLower.sabId Xo.univ.t)
  have hT := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c
  have hW := (GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c).2.2.1
  have htot : ShortValTot Xo c nab bad n a n (idCover nab n) :=
    GlobalTheory.shortValTot_of_pinned hL hC E H Dw l Xo c n (idCover nab n) (GlobalTheory.levelMaps_closed hL E H Dw h1) hW hT hW hT
      (idCover_isLev nab n) rfl ⟨_, hnab⟩ (fun _ => ⟨_, 1, _, hpin, idCover_psiTie nab n⟩) nab bad n a
  have key := GlobalTheory.Dict.holSub0_le_span_shortGen hC E H Dw l Xo c n (idCover nab n) σ r
    (Formalism.L2.PjFree.Unf.ofPj U) hσ hU hr hA hG hP (idCover_isLev nab n) ⟨_, hnab⟩ (idCover_unitC nab n)
    (by show ¬ 3 ∣ 1; decide) (fun _ => ⟨_, 1, _, hpin⟩) nab bad n a hbad hdom hn hχ htot
  intro Q hQ
  refine Submodule.span_le.2 ?_ (key hQ)
  rintro _ ⟨f, ⟨hf, Λ, N, x0, P, hΛ, hb, hM, hO, hX, hPm, hrule⟩, rfl⟩
  have hβ := betaH_ne_zero (Dw := Dw) (c := c) Λ
  have e : Formalism.L2.PjFree.rdU (Formalism.L2.PjFree.Unf.ofPj U) f =
      (σ (betaH (Dw := Dw) c Λ))⁻¹ • Formalism.L2.Pj.rdU U (betaH (Dw := Dw) c Λ • f) := by
    rw [LinearMap.map_smulₛₗ, smul_smul, inv_mul_cancel₀ ((map_ne_zero σ).2 hβ), one_smul]
    rfl
  rw [e]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
  rw [decide_eq_true (rfl : n = n)] at hX
  refine Set.mem_iUnion₂.2 ⟨fun b => Submodule.Quotient.mk (x0 b), span_mk_eq_top x0 hX,
    Submodule.smul_mem _ _ hf, Λ, N, P, hΛ, hb, hM, hO, hPm, fun p y => ?_⟩
  rw [phiHat_indPhi_mk]
  exact thLaValAt_of_isShortRule nab hnab hΛ hM hO hPm x0 hf hrule p y

end GlobalTheory.RawSpan
