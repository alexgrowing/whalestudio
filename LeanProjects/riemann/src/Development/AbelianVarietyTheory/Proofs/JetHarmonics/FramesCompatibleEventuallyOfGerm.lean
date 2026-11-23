import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GCorCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextCoeffSecondLinear
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartFormalBiext
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesCoeffEqZeroOfMulCoeffEqZero
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormEqZeroOfDiagExp
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValCastProdAlong

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameEventually

open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)

section Jets

variable {R : Type} [CommRing R] {ι : Type} {m : ℕ}

theorem mk_eq_zero_iff (p : MvPolynomial ι R) :
    (Ideal.Quotient.mk _ p : Jet R ι m) = 0 ↔ ∀ e : ι →₀ ℕ, e.degree ≤ m → p.coeff e = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, show orig R ι = MvPolynomial.idealOfVars ι R from rfl,
    MvPolynomial.mem_pow_idealOfVars_iff']
  simp [Nat.lt_succ_iff]

theorem mem_degLE [Fintype ι] [DecidableEq ι] (e : ι →₀ ℕ) : e ∈ degLE m ↔ e.degree ≤ m := by
  unfold degLE
  rw [Finset.mem_filter]
  have hd : (e.sum fun _ k => k) = e.degree := rfl
  rw [hd]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  refine Finset.mem_image.2 ⟨fun i => ⟨e i, Nat.lt_succ_of_le ((Finsupp.le_degree i e).trans h)⟩,
    Finset.mem_univ _, ?_⟩
  ext i
  simp

theorem coeff_psTrunc [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R) (e : ι →₀ ℕ) :
    (psTrunc m f).coeff e = if e.degree ≤ m then MvPowerSeries.coeff e f else 0 := by
  unfold psTrunc
  rw [MvPolynomial.coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp [mem_degLE]

theorem coeff_eq_of_psJet_eq [Fintype ι] [DecidableEq ι] {f g : MvPowerSeries ι R} (h : psJet m f = psJet m g)
    (e : ι →₀ ℕ) (he : e.degree ≤ m) : MvPowerSeries.coeff e f = MvPowerSeries.coeff e g := by
  rw [← sub_eq_zero, psJet, psJet, ← map_sub, mk_eq_zero_iff] at h
  have := h e he
  rwa [coeff_sub, coeff_psTrunc, coeff_psTrunc, if_pos he, if_pos he, sub_eq_zero] at this

theorem psJet_prod [Fintype ι] [DecidableEq ι] {α : Type} [DecidableEq α] (S : Finset α) (g : α → MvPowerSeries ι R) :
    psJet m (∏ i ∈ S, g i) = ∏ i ∈ S, psJet m (g i) := by
  induction S using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, FBIdJet.psJet_one]
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, FBIdJet.psJet_mul, ih]

theorem psJet_pow [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R) (q : ℕ) :
    psJet m (f ^ q) = psJet m f ^ q := by
  induction q with
  | zero => rw [pow_zero, pow_zero, FBIdJet.psJet_one]
  | succ q ih => rw [pow_succ, pow_succ, FBIdJet.psJet_mul, ih]

variable {K : Type} [CommRing K] (f : R →+* K)

theorem jetCoef_injective (hf : Function.Injective f) : Function.Injective (jetCoef f ι m) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [JetTr.jetCoef_mk, mk_eq_zero_iff] at ha
  rw [mk_eq_zero_iff]
  intro e he
  apply hf
  rw [map_zero, ← ha e he, coeff_map]

theorem map_psIn {d n n' : ℕ} (r : Fin n → Fin n') (g : MvPowerSeries (Fin n × Fin d) R) :
    MvPolynomial.map f (psIn d m r g) = psIn d m r (MvPowerSeries.map f g) := by
  rw [psIn, psIn, map_rename, JetTr.psTrunc_map]

theorem jetCoef_subst2 {d : ℕ} {κ : Type} (u v : Fin d → MvPolynomial κ R) (u' v' : Fin d → MvPolynomial κ K)
    (hu : ∀ j, MvPolynomial.map f (u j) = u' j) (hv : ∀ j, MvPolynomial.map f (v j) = v' j)
    (a : Jet R (Fin 2 × Fin d) m) :
    jetCoef f κ m (jetSubstP m (fun p : Fin 2 × Fin d => (![u, v] : Fin 2 → Fin d → MvPolynomial κ R) p.1 p.2) a) =
      jetSubstP m (fun p : Fin 2 × Fin d => (![u', v'] : Fin 2 → Fin d → MvPolynomial κ K) p.1 p.2)
        (jetCoef f (Fin 2 × Fin d) m a) := by
  have e : (fun p : Fin 2 × Fin d => (![u', v'] : Fin 2 → Fin d → MvPolynomial κ K) p.1 p.2) =
      fun p : Fin 2 × Fin d => MvPolynomial.map f ((![u, v] : Fin 2 → Fin d → MvPolynomial κ R) p.1 p.2) := by
    funext ⟨i, j⟩
    fin_cases i
    · exact (hu j).symm
    · exact (hv j).symm
  rw [e]
  exact RingHom.congr_fun (JetTr.jetCoef_substP f m _) a

end Jets

section Rat

variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}

theorem jetCopy_psJet {n : ℕ} (m : ℕ) (i : Fin n) (g : PS S 1 d) :
    (jetCopy (S := S) d m i : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m) (psJet m g) =
      psJet m (ev (n := n) ![pt S d i] g) := by
  rw [← jetSubstP_psJet m (fun p : Fin 1 × Fin d => (X (i, p.2) : MvPolynomial (Fin n × Fin d) S)) ![pt S d i]
    (fun ⟨a, j⟩ => by fin_cases a; exact cc_pt' i j) (fun p => by simp)
    (fun ⟨a, j⟩ => by fin_cases a; exact mk_X_psJet m (i, j))]
  refine DFunLike.congr_fun (GermD.jet_hom_ext fun p => ?_) _
  simp only [jetCopy, jetSubstP, GermD.jetMap_mk, aeval_X, constantCoeff_X, map_zero, sub_zero]

theorem jetCopy_graph {n : ℕ} (m : ℕ) (i : Fin n) (w : Pt S 1 d) (hw : ∀ j, MvPowerSeries.constantCoeff (w j) = 0)
    (g : PS S 2 d) :
    (jetCopy (S := S) d m i : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m)
      (jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((0 : Fin 1), j), fun j => psIn d m ![0] (w j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2) (psJet m g)) =
      psJet m (ev (n := n) ![pt S d i, comp1 w (pt S d i)] g) := by
  have hr : (![pt S (n := 1) d 0] : Fin 1 → Pt S 1 d) = fun i => pt S d ((![0] : Fin 1 → Fin 1) i) := by
    funext i; fin_cases i; rfl
  have ha : ∀ a j, MvPowerSeries.constantCoeff
      ((![pt S d 0, comp1 w (pt S d 0)] : Fin 2 → Pt S 1 d) a j) = 0 := by
    intro a j; fin_cases a
    · exact cc_pt' _ j
    · exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.cc_comp1 _ _ hw (fun i => cc_pt' _ i) j
  have hb : ∀ a j, MvPowerSeries.constantCoeff ((![pt S d i] : Fin 1 → Pt S n d) a j) = 0 := by
    intro a j; fin_cases a; exact cc_pt' _ j
  rw [jetSubstP_psJet m _ (![pt S d 0, comp1 w (pt S d 0)] : Fin 2 → Pt S 1 d) (fun p => ha p.1 p.2)
      (fun ⟨a, j⟩ => by
        fin_cases a
        · simp
        · show constantCoeff (psIn d m ![0] (w j)) = 0
          rw [FBIdPh.cc_psIn, hw])
      (fun ⟨a, j⟩ => by
        fin_cases a
        · exact mk_X_psJet m _
        · show _ = psJet m (ev ![pt S (n := 1) d 0] (w j))
          rw [hr]
          exact mk_psIn_psJet m _ _),
    jetCopy_psJet, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.ev_ev _ _ ha hb]
  congr 2
  funext a j
  fin_cases a
  · exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.ev_X _ hb 0 j
  · exact ev_at _ hb 0 (w j)

end Rat

theorem unit_eq_one {V F : Type} [CommRing V] [Field F] [CharZero F] [Algebra V F]
    (hf : Function.Injective (algebraMap V F)) {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB V d O)
    (bar : O → O) (w0 : O) (hw : w0 + bar w0 = 1) {n q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q) (h : PS F n d) (k : ℕ)
    (hk : ∀ (m : ℕ) (u : PS F n d), (∀ e : Fin n × Fin d →₀ ℕ, e.degree ≤ m → MvPowerSeries.coeff e (h * u) = 0) →
      ∀ e : Fin n × Fin d →₀ ℕ, e.degree + k ≤ m → MvPowerSeries.coeff e u = 0)
    (m : ℕ) (hm : k + 2 ≤ m) (U : (Jet V (Fin 2 × Fin d) m)ˣ)
    (h1 : jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => psIn d m (![0, 1] : Fin 2 → Fin 3) (B.G.F j),
        fun j => X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) V) p.1 p.2)
        (U : Jet V (Fin 2 × Fin d) m) =
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) V) p.1 p.2) (U : Jet V (Fin 2 × Fin d) m) *
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) V) p.1 p.2) (U : Jet V (Fin 2 × Fin d) m))
    (hs : jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) V) p.1 p.2) (U : Jet V (Fin 2 × Fin d) m) = U)
    (hb : ∀ a, jetSubstP m (fun p : Fin 2 × Fin d =>
        (![fun j => psIn d m ![0] (B.A.act a j), fun j => X ((1 : Fin 2), j)] :
          Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) V) p.1 p.2) (U : Jet V (Fin 2 × Fin d) m) =
      jetSubstP m (fun p : Fin 2 × Fin d =>
        (![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (B.A.act (bar a) j)] :
          Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) V) p.1 p.2) (U : Jet V (Fin 2 × Fin d) m))
    (hrel : psJet m h * ∏ i : Fin n,
      (jetCopy (S := F) d m i : Jet F (Fin 1 × Fin d) m →ₐ[F] Jet F (Fin n × Fin d) m)
        (jetCoef (algebraMap V F) (Fin 1 × Fin d) m (jetSubstP m (fun p : Fin 2 × Fin d =>
          (![fun j => X ((0 : Fin 1), j), fun j => psIn d m ![0] (B.A.act w0 j)] :
            Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) V) p.1 p.2) (U : Jet V (Fin 2 × Fin d) m))) ^ q =
      psJet m h) : U = 1 := by
  set f := algebraMap V F with hfd
  let BF : FB F d O := FBMap.mapFB f B
  let UF : (Jet F (Fin 2 × Fin d) m)ˣ := Units.map (jetCoef f (Fin 2 × Fin d) m).toMonoidHom U
  have hUF : (UF : Jet F (Fin 2 × Fin d) m) = jetCoef f (Fin 2 × Fin d) m U := rfl
  have hX : ∀ {r : ℕ} (i : Fin r) (j : Fin d),
      MvPolynomial.map f (X (i, j) : MvPolynomial (Fin r × Fin d) V) = X (i, j) := fun i j => map_X _ _
  obtain ⟨c, hcs, hcb, hc⟩ := CIndFrExp3.fixExp BF.G BF.A.act BF.A.const bar m UF
    (by
      have e := congrArg (jetCoef f (Fin 3 × Fin d) m) h1
      rw [map_mul, jetCoef_subst2 f _ _ _ _ (fun j => map_psIn f _ _) (hX 2),
        jetCoef_subst2 f _ _ _ _ (hX 0) (hX 2), jetCoef_subst2 f _ _ _ _ (hX 1) (hX 2)] at e
      exact e)
    (by
      have e := congrArg (jetCoef f (Fin 2 × Fin d) m) hs
      rw [jetCoef_subst2 f _ _ _ _ (hX 1) (hX 0)] at e
      exact e)
    (fun a => by
      have e := congrArg (jetCoef f (Fin 2 × Fin d) m) (hb a)
      rw [jetCoef_subst2 f _ _ _ _ (fun j => map_psIn f _ _) (hX 1),
        jetCoef_subst2 f _ _ _ _ (hX 0) (fun j => map_psIn f _ _)] at e
      exact e)
  have hc0 : c = 0 := by
    refine GlobalTheory.DiagExpZero.form_eq_zero_of_diag_exp F d BF.G (BF.A.act w0) (BF.A.act (bar w0)) (BF.A.const w0) ?_ c hcs (hcb w0) n q hn hq ?_
    · have e := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_add F B w0 (bar w0)
      rw [hw, ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_one] at e
      exact e.symm
    · intro e he
      refine hk m _ (fun e' he' => ?_) e (by omega)
      rw [jetCoef_subst2 f _ _ (fun j => X ((0 : Fin 1), j)) (fun j => psIn d m ![0] (BF.A.act w0 j)) (hX 0)
        (fun j => map_psIn f _ _), ← hUF, hc] at hrel
      simp only [jetCopy_graph m _ _ (BF.A.const w0)] at hrel
      simp only [← psJet_pow] at hrel
      rw [← psJet_prod, ← FBIdJet.psJet_mul] at hrel
      rw [mul_sub, mul_one, map_sub, coeff_eq_of_psJet_eq hrel e' he', sub_self]
  rw [hc0, CIndFrFix2c.twist_zero, FBIdJet.psJet_one, hUF] at hc
  exact Units.ext (jetCoef_injective f hf (by rw [hc, Units.val_one, map_one]))

end GlobalTheory.FrameEventually

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GCorCut Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem frames_compatible_eventually_of_germ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf pD pA pG U' P.U) (F : Type) [Field F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (q : ℕ) (σ' : U'.toUnifPre.SecGF F q) (h : PS F n (chD C.ch)), 1 ≤ n → 1 ≤ q → h ≠ 0 → IsGermN P C.xT C.actT C.eT C.wPT pG PU F q σ' h → ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → LB.Gen.Corr C.I.G.PP.L _ _ _ _ (LB.pullGen C.I.G.PP.L (cφG C.I.G ![jptG C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT (m + 1) (0 : Fin 2), jptG C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT (m + 1) (1 : Fin 2)]) (cε 2) (C.eT (m + 1)) (homAt (𝟙 (Sp T.V)) (jetTrunc : Jet T.V (Fin 2 × Fin (chD C.ch)) (m + 1) →ₐ[T.V] Jet T.V (Fin 2 × Fin (chD C.ch)) m)).left) (C.eT m) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C P n D' A' G' _ _ pD pA pG U' PU F _ _ _ _ _ q σ' h hn hq hh hg
  obtain ⟨k, hk⟩ := GlobalTheory.mvPowerSeries_coeff_eq_zero_of_mul_coeff_eq_zero F (Fin n × Fin (chD C.ch)) h hh
  obtain ⟨B, eF, eA, -⟩ := integralChart_formalBiext E H Dw l Xo c T io y C
  refine ⟨k + 2, fun m hm => ?_⟩
  obtain ⟨U, hU, h1, hs, hb⟩ := FrRatio.frRatioG C.chartT C.frameT m
  have hrel := GlobalTheory.GermRatio.main E H T.V (maximalIdeal T.V) C.I.G P (chD C.ch) n C.xT C.FT C.actT C.tgT _ C.chartT
    C.wPT C.primT D' A' G' pD pA pG U' PU F q σ' h C.eT C.frameT.gen hg m U hU
  have hinj : Function.Injective (algebraMap T.V F) := by
    rw [IsScalarTower.algebraMap_eq T.V T.Fr F]
    exact (algebraMap T.Fr F).injective.comp (IsFractionRing.injective T.V T.Fr)
  rw [← eF] at h1
  rw [← eA] at hb hrel
  have hone : U = 1 := FrameEventually.unit_eq_one hinj B H.bar H.w0 (ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.cmHostUnit_add_conj_eq_one H) hn hq h k
    hk m hm U h1 hs hb hrel
  subst hone
  refine corr_of_val C.I.G.PP.isLB fun z J hJ => ?_
  refine (val_corr hJ hU (𝟙 _)).trans ((GermB.val_scale _ _ _ _ _ _ z J hJ).trans ?_)
  rw [unitΓ, map_one, map_one, _root_.one_mul]

end GlobalTheory
