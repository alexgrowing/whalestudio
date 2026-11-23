import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ThetaIsometryFactsHold
import Formalism.LocalRingCardinality.FactDelDualNabla
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominantWeightPolynomialFunctionalMinorsStatement
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinorProductPairingDeterminedByCanonicalMapStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JetMapFrameEqApplyQAdaptedCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JetMapIdentityTransportComplexToPadicStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportDegreeEqOfMemWeightPolynomialsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelFormComplexPolynomialIdentityStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueKernelJetsLiftDegreesAlgebraicStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DtTiedTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelDetAdelicOfPinned
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChainsSatisfyConditions
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoThreeOfOfDeterminantCharacterFiniteOrderType
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPowEqSpanNormOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KernelCharactersEqReference

namespace GlobalTheory.KForm.KerJ

open GlobalTheory.KerJ

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.Mem.Chr (finPartI finPartI_eq_self unitIdl)

theorem mtType_of_hecke {D : D7} {C : CharFrame D} (Dt : DtTied D C) (ξ : HChar D.host.E) {n : ℕ} (hn : 0 < n) (hord : ξ.OrderDvd n)
    (mt : ℕ → D.Dt →* ℂˣ) (h : ∀ (j : Fin D.R.m) a, IsFinIdele a → mt (j.1 + 1) (Dt.eDt a) = (C.mu0 j * ξ).1 a) (u : D.what₂.Word) :
    MtType u mt := by
  letI := D.host.cmStar
  have hcm : IsCMField D.host.E := D.host.isCMField_hostE
  intro i hi
  have hun : (C.mu0 ⟨i, hi⟩ * ξ).IsUnitary := fun x => by
    have e : (C.mu0 ⟨i, hi⟩ * ξ).1 x = (C.mu0 ⟨i, hi⟩).1 x * ξ.1 x := rfl
    rw [e, Units.val_mul, norm_mul, (C.isMu0 ⟨i, hi⟩).unitary x, CharModel.isUnitary_of_orderDvd hn hord x, one_mul]
  refine ⟨fun k hk => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (Dt.UO_eq k).1 hk
    obtain ⟨m, hm, hu⟩ := GlobalTheory.UnUnitCmp.Val.finUnit_pow _ hun
    refine ⟨m, hm, Units.ext ?_⟩
    rw [← CharModel.eDt_finPart Dt a, h ⟨i, hi⟩ _ (CharModel.isFin_finPart a), Units.val_pow_eq_pow_val]
    exact hu _ (CharModel.isFin_finPart a) ha
  · choose e he using fun τ => (D.hcW u τ).e_int ⟨i, hi⟩
    refine ⟨e, fun τ => (he τ).symm, fun z => ?_⟩
    obtain ⟨k, hk⟩ := GlobalTheory.Mem.Col2.exists_eq_div_conj D.host z
    obtain ⟨m, hm, hinf⟩ := (C.isMu0 ⟨i, hi⟩).inf
    rw [← Dt.rat k z hk, ← CharModel.eDt_finPart Dt, h ⟨i, hi⟩ _ (CharModel.isFin_finPart _), GlobalTheory.Mem.Chr.DetGroupModel.fin_diag,
      HChar.inf_mul, GlobalTheory.TypeValues.inf_eq_one _ hn hord, mul_one, Units.val_inv_eq_inv_val, hinf k,
      ← Finset.prod_inv_distrib, ← D.eTau.prod_comp]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hme : m (D.eTau τ) = 2 * -e τ := by
      have h1 := hm (D.eTau τ)
      have h2 : eExp D ⟨i, hi⟩ (D.eTau τ) = e τ := by
        rw [← he τ, D.hcW_e]; simp [eExp]
      simp only [h2] at h1
      exact_mod_cast h1
    have h1 := congrArg (embPsi D.host (D.eTau τ)) hk
    rw [map_mul, GlobalTheory.Mem.Chr.DetGroupModel.emb_conj] at h1
    have h0 : embPsi D.host (D.eTau τ) (k : D.host.E) ≠ 0 := by simp
    show _ = embPsi D.host (D.eTau τ) z.1 ^ e τ
    generalize embPsi D.host (D.eTau τ) (k : D.host.E) = a at *
    generalize embPsi D.host (D.eTau τ) z.1 = b at *
    have hn' : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by simpa using h0
    have h2 : a * star a = ((‖a‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    have h3 : (a / ((‖a‖ : ℝ) : ℂ)) ^ (2 : ℤ) = b := by
      rw [zpow_ofNat, div_pow, div_eq_iff (pow_ne_zero _ hn'), ← h2]
      linear_combination (-a) * h1
    rw [hme, zpow_mul, h3, zpow_neg, inv_inv]

end GlobalTheory.KForm.KerJ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KForm.EntTrue

open Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.KerJ GlobalTheory.KForm.KerJ

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem powRatAll_true (l : I.Laws) (Z : TC.Later B (I.cols l)) : GL3Theta.PowRatAll (I.rec7 l Z) := by
  obtain ⟨idl, h⟩ := GlobalTheory.Mem.NormOneIdeal.pinned_of_finer (I.rec7 l Z) I.SQ (MulEquiv.refl _)
    (by
      show UOQ B.host I.SQ = _
      ext x
      constructor
      · intro h
        exact ⟨x, h, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact hy)
    (fun z => rfl)
    (fun N L L' t ht => by
      exact (trueDtPackQ_relDet I.SQ I.C N L L').trans ht)
  exact GL3Theta.powRatAll_of _ idl h (GlobalTheory.KernelScalarUnit.normOne_pow _)

theorem mtType_std (hok : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {Qp : I.ι → Finset ℕ}
    {O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)} (hO : I.StdO l Z Qp O) (u : (I.rec7 l Z).what₂.Word) (a : (I.rec7 l Z).what₂.Tup) :
    MtType u (O u a).mt := by
  obtain ⟨T, hT⟩ := TC.dtTied_true I hok hp l Z
  have ht : IsOfFinOrder (I.tup a : Chr B.fields.F B.fields.E B.fields.K) :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (I.tup a).2).1).1).1).2
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 ht
  have hk : KDq B.host I.SQ ≤ ((I.xi a).1.comp (finPartI B.host.E)).ker :=
    (KDq_anti B.host (I.Q_subset_SQ a)).trans ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hok).2.2 a).1
  refine mtType_of_hecke T (I.xi a) hn ((hok.xi_reads a).orderDvd hpow) _ (fun j x hx => ?_) u
  have hm : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ B.R.m := ⟨by omega, j.2⟩
  have e1 : (O u a).mt (j.1 + 1) = (I.rec7 l Z).muTil (j.1 + 1) * (show (I.rec7 l Z).Dt →* ℂˣ from tildeQ B.host I.SQ (I.xi a)) := by
    rw [hO.mt u a]
    exact if_pos hm
  rw [e1, MonoidHom.mul_apply, T.muTil_eq j x hx, hT x]
  have e2 : (tildeQ B.host I.SQ (I.xi a)) (QuotientGroup.mk x) = (I.xi a).1 x :=
    (tildeQ_mk B.host I.SQ hk x).trans (congrArg _ (finPartI_eq_self hx))
  exact congrArg _ e2

theorem rhoAlg_std (hok : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {Qp : I.ι → Finset ℕ}
    {O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)} (hO : I.StdO l Z Qp O) (u : (I.rec7 l Z).what₂.Word) (a : (I.rec7 l Z).what₂.Tup) :
    GL3Columns.RhoAlg (O u a) := by
  have h3 := GlobalTheory.KerJ.RhoThree.rhoThreeOf_of_mtType _ u ((I.rec7 l Z).chTw u a) (O u a).mt (mtType_std I hok hp l Z hO u a)
  have hq := powRatAll_true I l Z
  intro i hi
  refine ⟨fun c => ?_, fun c' => ?_⟩
  · obtain ⟨h, z, hz⟩ := hq ((O u a).dt i c)
    exact ((h3 i hi).1 _ h z hz).1.1
  · obtain ⟨h, z, hz⟩ := hq ((O u a).dt (i + 1) c')
    exact ((h3 i hi).1 _ h z hz).2.1

end GlobalTheory.KForm.EntTrue

noncomputable section

namespace GlobalTheory.KForm

open Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric

def tauE (D : D7) : (Bool × HH D) ≃ D.what₂.Tau := Equiv.ofBijective _ (tauPl_bij D)

theorem deX_cols (D : D7) {k : Type} [CommRing k] (N : ℕ) (nu : Bool × HH D → YoungDiagram) (hnu : ∀ z, (nu z).colLen 0 ≤ N)
    (y : Bool × HH D → Fin N → ℕ → k) :
    GL3Columns.DeX N nu y = GL3Columns.DeX N nu (fun s => GL3Columns.colsOf ((fun τ => Matrix.of fun a (b : Fin N) => y ((tauE D).symm τ) a b) (tauPl D s))) := by
  unfold GL3Columns.DeX
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  refine congrArg Matrix.det (Matrix.ext fun i j => ?_)
  simp only [Matrix.of_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hj : (j : ℕ) < N := lt_of_lt_of_le j.2 (le_trans ((nu s).colLen_anti 0 c (Nat.zero_le _)) (hnu s))
  have he : (tauE D).symm (tauPl D s) = s := (tauE D).symm_apply_apply s
  simp [GL3Columns.colsOf, hj, he]

theorem lamC_coe {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (x : Qbar) : lamC lam (x : ℂ) = lam x := by
  unfold lamC
  rw [dif_pos x.2]

theorem lamC_jetC (D : D7) {N N' p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (cD : D.what₂.Tau → ℂ) (hc : ∀ τ, cD τ ∈ Qbar)
    (G : VC D N N' → ℂ) (m : DVar D.what₂.Tau N N' →₀ ℕ) (hm : jetC cD G m ∈ Qbar) :
    lamC lam (jetC cD G m) = (m.prod fun k n => lamC lam (cD k.1) ^ n) * (m.prod fun _ n => (n.factorial : ℂ_[p])) *
      lamC lam (Formalism.MainNotions.TaylorLogMetric.taylor D G m) := by
  set c' : D.what₂.Tau → Qbar := fun τ => ⟨cD τ, hc τ⟩
  set a : Qbar := m.prod fun k n => c' k.1 ^ n
  set f : Qbar := m.prod fun _ n => (n.factorial : Qbar)
  have ha : (a : ℂ) = m.prod fun k n => cD k.1 ^ n := by
    simp only [a, c', Finsupp.prod]
    rw [show ((∏ k ∈ m.support, (⟨cD k.1, hc k.1⟩ : Qbar) ^ m k : Qbar) : ℂ) = algebraMap Qbar ℂ (∏ k ∈ m.support, (⟨cD k.1, hc k.1⟩ : Qbar) ^ m k) from rfl,
      map_prod]
    rfl
  have hf : (f : ℂ) = m.prod fun _ n => (n.factorial : ℂ) := by
    simp only [f, Finsupp.prod]
    rw [show ((∏ k ∈ m.support, ((m k).factorial : Qbar) : Qbar) : ℂ) = algebraMap Qbar ℂ (∏ k ∈ m.support, ((m k).factorial : Qbar)) from rfl,
      map_prod]
    simp
  have hf0 : (f : ℂ) ≠ 0 := by
    rw [hf, Finsupp.prod]
    exact Finset.prod_ne_zero_iff.2 fun k _ => by exact_mod_cast Nat.factorial_ne_zero (m k)
  have hd : derivAt0 G m = (f : ℂ) * Formalism.MainNotions.TaylorLogMetric.taylor D G m := by
    unfold Formalism.MainNotions.TaylorLogMetric.taylor
    rw [← hf, mul_div_cancel₀ _ hf0]
    rfl
  have hj : jetC cD G m = (a : ℂ) * (f : ℂ) * Formalism.MainNotions.TaylorLogMetric.taylor D G m := by
    unfold jetC
    rw [hd, ha, mul_assoc]
  have hla : (m.prod fun k n => lamC lam (cD k.1) ^ n) = lam a := by
    simp only [a, Finsupp.prod, map_prod, map_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← lamC_coe]
  have hlf : (m.prod fun _ n => (n.factorial : ℂ_[p])) = lam f := by
    simp only [f, Finsupp.prod, map_prod, map_natCast]
  rw [hla, hlf]
  by_cases ha0 : a = 0
  · have : jetC cD G m = ((0 : Qbar) : ℂ) := by rw [hj, ha0]; simp
    rw [this, lamC_coe, ha0]
    simp
  · have ha0' : (a : ℂ) ≠ 0 := fun h => ha0 (Subtype.ext h)
    have ht : Formalism.MainNotions.TaylorLogMetric.taylor D G m ∈ Qbar := by
      have : Formalism.MainNotions.TaylorLogMetric.taylor D G m = jetC cD G m / ((a : ℂ) * (f : ℂ)) := by
        rw [hj]; field_simp
      rw [this]
      exact div_mem hm (mul_mem a.2 f.2)
    have e : jetC cD G m = ((a * f * ⟨_, ht⟩ : Qbar) : ℂ) := hj
    rw [e, lamC_coe, map_mul, map_mul, show lamC lam (Formalism.MainNotions.TaylorLogMetric.taylor D G m) = lam ⟨_, ht⟩ from lamC_coe lam ⟨_, ht⟩]

theorem applyQ_C_mul {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (d : ℂ_[l]) (hd : d ≠ 0) (Q : MvPolynomial (Lt × Fin N0 × ℕ) ℂ_[l]) (y' : Lt → Fin N1 → ℕ → ℂ_[l]) :
    GL3Columns.applyQ l N0 N1 Th (MvPolynomial.C d * Q) y' = d * GL3Columns.applyQ l N0 N1 Th Q y' := by
  unfold GL3Columns.applyQ
  simp only [map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  rw [← MvPolynomial.smul_eq_C_mul, MvPolynomial.support_smul_eq hd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem eval_aeval' {σ τ R : Type} [CommRing R] (f : τ → R) (g : σ → MvPolynomial τ R) (P : MvPolynomial σ R) :
    MvPolynomial.eval f (MvPolynomial.aeval g P) = MvPolynomial.eval (fun k => MvPolynomial.eval f (g k)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p k hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X]

theorem qbar_of_numberField (M : IntermediateField ℚ ℂ) [NumberField M] (s : M) : (s : ℂ) ∈ Qbar :=
  mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) s).algHom M.val)

end GlobalTheory.KForm

open GlobalTheory.KForm.EntTrue Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G in

theorem GlobalTheory.Mem.Col2.TC.kerEnt_kform_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ u μ w, LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ (c : ((I.rec7 l Z).chTw u μ).cls i) (c' : ((I.rec7 l Z).chTw u μ).cls (i + 1)) (v : ValQ O u μ i) (v' : ValQ O u μ (i + 1)), evC O u μ (i + 1) v' = ((I.rec7 l Z).chTw u μ).Kmap i c c' (evC O u μ i v) → ∀ J, prTC Pl O Bs u μ w i c' v' J = unC Pl O Bs u μ w i c c' * prSC Pl O Bs u μ w i c v (KM.applyAt0 ((I.rec7 l Z).R.N i) ((I.rec7 l Z).R.N (i + 1)) ((I.rec7 l Z).what₂.places.resChar w) (thAtW Pl O Bs u μ w i c c') (KM.Gxz ((I.rec7 l Z).R.N i) ((I.rec7 l Z).R.N (i + 1)) (nuD (I.rec7 l Z) u i) J)) := by
  intro B X I hok hp l Z l0 Y O Pl Bs hq hs hB hent hU hJ u μ w hw i hi c c' v v' hK J
  have hR := GlobalTheory.KForm.EntTrue.rhoAlg_std I hok hp l Z hs u μ
  have hCo := GlobalTheory.T.toy_entPl_canOnto (I.rec7 l Z) Pl
  have hS := canS_of Pl Bs hCo
  have hT := canT_of Pl Bs hCo
  have hdg : ∀ τ, (O u μ).dgen τ ∈ Qbar := by
    obtain ⟨M, hM, -, hs'⟩ := (O u μ).dgen_gen
    intro τ
    obtain ⟨s, hs1, -⟩ := hs' τ
    rw [← hs1]
    exact GlobalTheory.KForm.qbar_of_numberField M s
  have hdet : ∀ τ, (Bs u μ w i c τ).det ≠ 0 := fun τ => (hB u μ w i hi.le c τ).1
  change tgtPh Pl O Bs u μ w i c' v' (MvPolynomial.map (Int.castRingHom _) (KM.nablaX _ (nuD (I.rec7 l Z) u i) J)) = _
  refine GlobalTheory.T.minorProductPairing_determined_by_canonicalMap (I.rec7 l Z) _ _ (N_le_succ _ i) (nuD (I.rec7 l Z) u i) (fun z => nuD_rows _ u i z)
    (thAtW Pl O Bs u μ w i c c') (prSC Pl O Bs u μ w i c v) (tgtPh Pl O Bs u μ w i c' v') (unC Pl O Bs u μ w i c c')
    (MvPolynomial.C (∏ τ, (Bs u μ w i c τ).det ^ (-((I.rec7 l Z).chTw u μ).sSharp i τ)) *
      MvPolynomial.aeval (fun k : GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N i) => ∑ a : Fin ((I.rec7 l Z).R.N i),
          MvPolynomial.C (Bs u μ w i c k.1 k.2.1 a) * MvPolynomial.X ((GlobalTheory.KForm.tauE _).symm k.1, a, (k.2.2 : ℕ)))
        (MvPolynomial.map (Pl.iL w) (srcPol u μ i (secC O u μ i v : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N i)) (I.rec7 l Z).what₂.LL))))
    ?_ ?_ J
  · intro y
    rw [GlobalTheory.KForm.deX_cols (I.rec7 l Z) _ (nuD (I.rec7 l Z) u i) (fun z => nuD_rows _ u i z) y]
    have h1 := congrFun (canInv_spec (I.rec7 l Z) w _ (nuD (I.rec7 l Z) u i) _ (hS u μ w i hi c (secC O u μ i v)))
      (fun τ => Matrix.of fun a (b : Fin ((I.rec7 l Z).R.N i)) => y ((GlobalTheory.KForm.tauE _).symm τ) a b)
    refine Eq.trans ?_ h1.symm
    rw [map_mul, MvPolynomial.eval_C, GlobalTheory.KForm.eval_aeval']
    show _ = (∏ τ, (Bs u μ w i c τ).det ^ (-((I.rec7 l Z).chTw u μ).sSharp i τ)) *
      MvPolynomial.eval (fun k : GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N i) =>
          (Bs u μ w i c k.1 * (fun τ => Matrix.of fun a (b : Fin ((I.rec7 l Z).R.N i)) => y ((GlobalTheory.KForm.tauE _).symm τ) a b) k.1) k.2.1 k.2.2)
        (MvPolynomial.map (Pl.iL w) (srcPol u μ i (secC O u μ i v : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N i)) (I.rec7 l Z).what₂.LL)))
    congr 2
    exact congrArg MvPolynomial.eval (funext fun k => by simp [Matrix.mul_apply, MvPolynomial.eval_X])
  · intro y'
    have h1 := congrFun (canInv_spec (I.rec7 l Z) w _ (nuD (I.rec7 l Z) u i) _ (hT u μ w i hi c' (secC O u μ (i + 1) v'))) y'
    refine h1.trans ?_
    have hmap : ∀ {N : ℕ} (Q : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) N) (I.rec7 l Z).what₂.LL),
        MvPolynomial.map (Pl.iL w) Q = MvPolynomial.map (Pl.lam w) (MvPolynomial.map (jL w) Q) := by
      intro N Q
      rw [MvPolynomial.map_map, lam_jL]
    have hρ : ((GL3Theta.rhoOf (I.rec7 l Z) (O u μ).mt i ((O u μ).dt i c) : ℂˣ) : ℂ) *
        ((GL3Theta.rhoOf' (I.rec7 l Z) (O u μ).mt i ((O u μ).dt (i + 1) c') : ℂˣ) : ℂ) ∈ Qbar :=
      mul_mem ((hR i hi).1 c) ((hR i hi).2 c')
    have htr := GlobalTheory.T.jetMap_identity_transport_complex_to_padic (I.rec7 l Z) (Pl.lam w) (jetC (O u μ).dgen ((O u μ).Th i c c'))
      (fun m => (m.prod fun k n => lamC (Pl.lam w) ((O u μ).dgen k.1) ^ n) * (m.prod fun _ n => (n.factorial : ℂ_[(I.rec7 l Z).what₂.places.resChar w])) *
        MvPowerSeries.coeff m (pSer (I.rec7 l Z) (Pl.lam w) ((O u μ).Th i c c')))
      (fun τ => ∑ r, nuT (I.rec7 l Z) u i τ r) ⟨_, hρ⟩
      (MvPolynomial.map (jL w) (secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL))
      (MvPolynomial.map (jL w) (srcPol u μ i (secC O u μ i v : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N i)) (I.rec7 l Z).what₂.LL)))
      (fun m hm => ⟨⟨_, GlobalTheory.T.trueKernelJets_liftDegrees_algebraic I hok hp l Z Y.Qp O hs hJ u μ i hi c c' m hm⟩, rfl,
        (GlobalTheory.KForm.lamC_coe _ _).symm.trans
          (GlobalTheory.KForm.lamC_jetC (I.rec7 l Z) (Pl.lam w) _ hdg _ m (GlobalTheory.T.trueKernelJets_liftDegrees_algebraic I hok hp l Z Y.Qp O hs hJ u μ i hi c c' m hm))⟩)
      (fun e he τ => GlobalTheory.T.support_degree_eq_of_mem_weightPolynomials (nuT (I.rec7 l Z) u i) _ (srcPol_mem u μ i hi _) e (MvPolynomial.support_map_subset _ _ he) τ)
      (by
        rw [MvPolynomial.map_map, MvPolynomial.map_map, alg_jL]
        exact GlobalTheory.T.kernelForm_complex_polynomial_identity (I.rec7 l Z) O u μ i hi (hU u μ i hi) c c' v v' hK)
    have hd0 : (∏ τ, (Bs u μ w i c τ).det ^ (-((I.rec7 l Z).chTw u μ).sSharp i τ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hdet τ)
    show (∏ τ, (Bs u μ w (i + 1) c' τ).det ^ (-((I.rec7 l Z).chTw u μ).sDiv i τ)) *
      MvPolynomial.eval (fun k : GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1)) => (Bs u μ w (i + 1) c' k.1 * y' k.1) k.2.1 k.2.2)
        (MvPolynomial.map (Pl.iL w) (secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL)) = _
    rw [hmap, htr, map_mul, MvPolynomial.eval_C, ← hmap,
      GlobalTheory.T.jetMap_frame_eq_applyQ_adapted_coordinates (I.rec7 l Z) _ _ (N_le_succ _ i) (pSer (I.rec7 l Z) (Pl.lam w) ((O u μ).Th i c c'))
        (fun τ => lamC (Pl.lam w) ((O u μ).dgen τ)) (Bs u μ w i c) (Bs u μ w (i + 1) c') hdet, GlobalTheory.KForm.applyQ_C_mul _ _ _ _ _ hd0]
    have hl : (Pl.lam w) ⟨_, hρ⟩ = lamC (Pl.lam w) ((GL3Theta.rhoOf (I.rec7 l Z) (O u μ).mt i ((O u μ).dt i c) : ℂˣ) : ℂ) *
        lamC (Pl.lam w) ((GL3Theta.rhoOf' (I.rec7 l Z) (O u μ).mt i ((O u μ).dt (i + 1) c') : ℂˣ) : ℂ) := by
      rw [show (⟨_, hρ⟩ : Qbar) = ⟨_, (hR i hi).1 c⟩ * ⟨_, (hR i hi).2 c'⟩ from rfl, map_mul, ← GlobalTheory.KForm.lamC_coe, ← GlobalTheory.KForm.lamC_coe]
    have hp : (∏ τ, (Bs u μ w i c τ).det ^ (((I.rec7 l Z).chTw u μ).sSharp i τ)) *
        (∏ τ, (Bs u μ w i c τ).det ^ (-((I.rec7 l Z).chTw u μ).sSharp i τ)) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun τ _ => by rw [← zpow_add₀ (hdet τ), add_neg_cancel, zpow_zero]
    have hun : unC Pl O Bs u μ w i c c' = unF Pl O Bs u μ w i c c' := by
      unfold unC
      rw [if_neg (unF_ne Pl O Bs hB u μ hR w i hi c c')]
    have key : ∀ A : ℂ_[(I.rec7 l Z).what₂.places.resChar w],
        (∏ τ, (Bs u μ w (i + 1) c' τ).det ^ (-((I.rec7 l Z).chTw u μ).sDiv i τ)) * ((Pl.lam w) ⟨_, hρ⟩ * A) =
          unC Pl O Bs u μ w i c c' * ((∏ τ, (Bs u μ w i c τ).det ^ (-((I.rec7 l Z).chTw u μ).sSharp i τ)) * A) := by
      intro A
      rw [hun, hl]
      unfold unF
      linear_combination (-(lamC (Pl.lam w) ((GL3Theta.rhoOf (I.rec7 l Z) (O u μ).mt i ((O u μ).dt i c) : ℂˣ) : ℂ) *
        lamC (Pl.lam w) ((GL3Theta.rhoOf' (I.rec7 l Z) (O u μ).mt i ((O u μ).dt (i + 1) c') : ℂˣ) : ℂ) *
        (∏ τ, (Bs u μ w (i + 1) c' τ).det ^ (-((I.rec7 l Z).chTw u μ).sDiv i τ)) * A)) * hp
    exact key _
