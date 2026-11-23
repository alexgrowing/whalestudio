import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelSplitPlacesEqJetClassicalThetaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockPolynomialJetValueEqJetLinearFormRescaledStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainMoveCharactersEqRhoUpToBaseStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnStepsAreStandardHermitianPairsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedDatumEqFiniteDatumRepresentativePairStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnPeriodLatticeVacuumSmooth
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntAtOfLocTop
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ClassicalThetaOfDatumSmulMoveStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleLevelPosOddBadPrimesPrimeToLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerTup

theorem jetP_cast (D : D7) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (s : ℂ) (cD : D.what₂.Tau → ℂ)
    (hcD : ∀ τ, cD τ ≠ 0) (G : VCx D.what₂.Tau a b → ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    jetP S T hS hT s G P = jetL cD G (mvZ (fun _ => 1) (fun τ => (s / cD τ) • 1) (castP hS hT P)) := by
  subst hS hT
  have h1 : castP (D := D) (rfl : S.rank = S.rank) (rfl : T.rank = T.rank) P = P := by
    conv_rhs => rw [← MvPolynomial.rename_id_apply P]
    rfl
  rw [h1]
  exact GlobalTheory.T.fockPolynomialJetValue_eq_jetLinearForm_rescaled D S T s cD hcD G P

theorem jetC_zero {ι : Type} [Fintype ι] {a b : ℕ} (cD : ι → ℂ) (m : Formalism.L2.Ker.DVar ι a b →₀ ℕ) :
    jetC cD (fun _ : VCx ι a b => (0 : ℂ)) m = 0 := by
  simp only [jetC, derivAt0, iteratedFDeriv_zero_fun, Pi.zero_apply, ContinuousMultilinearMap.zero_apply, mul_zero]

theorem jetP_zero (D : D7) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (s : ℂ)
    (P : MvPolynomial (FVar D T.rank S.rank) ℂ) : jetP S T hS hT s (fun _ => 0) P = 0 := by
  simp only [jetP, jetC_zero, mul_zero, Finset.sum_const_zero]

theorem jetL_zero {ι : Type} [Fintype ι] {a b : ℕ} (cD : ι → ℂ) : jetL cD (fun _ : VCx ι a b => (0 : ℂ)) = 0 := by
  have h : (fun m => jetC cD (fun _ : VCx ι a b => (0 : ℂ)) m) = 0 := funext fun m => jetC_zero cD m
  simp only [jetL, h, map_zero]

theorem toHom_surj {D : D7} (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b)
    (y : (Fin a → D.host.E) →ₗ[D.host.E] Fin b → D.host.E) : ∃ z, toHom S T hS hT z = y :=
  ⟨(Matrix.reindex (finCongr hT) (finCongr hS)).symm (LinearMap.toMatrix' y), by
    unfold toHom
    rw [Equiv.apply_symm_apply, Matrix.toLin'_toMatrix']⟩

theorem supp_per_of_inBox {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ}
    (SS : Finset (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ) (N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a))
    (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (Ξ : Formalism.L2.Col.HomE E a b → K)
    (hB : GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.InBox SS cA cB N N' Ξ) (f : K →+* ℂ) (p : ℂ) :
    (∀ y, p * f (Ξ y) ≠ 0 → ((cA * cB : ℕ) : E) • y ∈ Formalism.L2.Col.homAt SS N N') ∧
    (∀ y, ∀ z ∈ Formalism.L2.Col.homAt SS N N', p * f (Ξ (y + ((cA * cB : ℕ) : E) • z)) = p * f (Ξ y)) := by
  have key : ∀ (n : ℕ) (y : Formalism.L2.Col.HomE E a b), ((n : E) • y) = ((n : 𝓞 E) • y) := fun n y => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  refine ⟨fun y hy => ?_, fun y z hz => ?_⟩
  · have hx : Ξ y ≠ 0 := fun h0 => hy (by rw [h0, map_zero, mul_zero])
    have h1 := hB.1 y hx
    rw [Formalism.L2.Col.divLat, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply] at h1
    rw [key, Nat.cast_mul, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ h1
  · have hz' : ((cA * cB : ℕ) : E) • z ∈ Formalism.L2.Col.mulLat cB (Formalism.L2.Col.homAt SS N N') := by
      rw [key, Nat.cast_mul, mul_comm, mul_smul]
      exact Submodule.mem_map.2 ⟨_, Submodule.smul_mem _ _ hz, rfl⟩
    rw [hB.2 y _ hz']

theorem jetP_zero' (D : D7) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (s : ℂ)
    (P : MvPolynomial (FVar D T.rank S.rank) ℂ) : jetP S T hS hT s (0 : VCx D.what₂.Tau a b → ℂ) P = 0 :=
  jetP_zero D S T hS hT s P

theorem jetL_zero' {ι : Type} [Fintype ι] {a b : ℕ} (cD : ι → ℂ) : jetL cD (0 : VCx ι a b → ℂ) = 0 := jetL_zero cD

end GlobalTheory.KerTup

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 200000 in
open GlobalTheory.KerTup in

theorem GlobalTheory.KerTup.kernel_identity_tuple : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ Ch : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j) ψ θ x vac c₀ kom dd w Ram rd cK, PinX I l Z ψ θ x vac c₀ → PinColL A ι ψ θ x vac c₀ kom dd w Ram rd cK → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) (s : ℂ), (∀ f, IsHol θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) ψ f → ∀ P, pureTensorO ψ θ _ _ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P 0 = jetP _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) s (ColDat.xiS θ i hi f) P) → ∀ α γ (c : {c // A.chOf i c = ι i α}) (c' : {c // A.chOf (i + 1) c = ι (i + 1) γ}) P, (volLev (x i).vol (A.U i (ι i α)) : ℂ) * thetaKO (kom i) (A.h i _ c) (A.h (i + 1) _ c') (pureTensorO ψ θ _ _ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (comb ψ _ _ (dd i α γ) (vac i)) P) = cK i * A.abelian₂ i c.1 c'.1 (mvZ (fun _ => 1) (fun τ => (s / I.J.cD τ) • 1) (castP (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) P)) := by
  intro B X I hI hP l Z u a Ch₀ Ch A ι ψ θ x vac c₀ kom dd w Ram rd cK hX hC i hi s hHol α γ c c' P
  obtain ⟨hStd, hGram, hEmb, hcD, hDet⟩ := GlobalTheory.T.trueColumnSteps_are_standardHermitianPairs I hI hP l Z ψ θ hX.std hX.inf
  obtain ⟨hFin, Φ, hSB, hΦv, hTh⟩ := hC.dat i hi α γ
  obtain ⟨hMv, hMv', hΞ⟩ := GlobalTheory.T.movedDatum_eq_finiteDatum_representativePair I hI hP l Z u a Ch₀ A hC.is i hi (ι i α) (ι (i + 1) γ) Φ hSB (w i α γ) hΦv c c'
  obtain ⟨xg, hxg⟩ := hDet _ (A.h i (ι i α) c)
  obtain ⟨yh, hyh⟩ := hDet _ (A.h (i + 1) (ι (i + 1) γ) c')
  have hV := (hX.mv i hi).2 a (A.chr (i + 1)) (kom i) (hC.is.chr ⟨i, hi⟩) (hC.om i hi) (A.h i _ c)
    (hC.is.h i (Nat.le_of_succ_le hi) _ c).1 (A.h (i + 1) _ c') (hC.is.h (i + 1) hi _ c').1 _ _ hMv hMv' xg yh hxg hyh
  have hχ := GlobalTheory.T.chainMove_characters_eq_rho_up_to_base I hI hP l Z u a Ch₀ A hC.is i hi _ _ c c' xg yh hxg hyh
  obtain ⟨hc0, hcov, h2qd⟩ := GlobalTheory.T.tupleLevel_pos_odd_badPrimes_prime_to_level I hI hP u a
  obtain ⟨hXo, hPr, -⟩ := base_fields_primes_ok B X
  have hi' : i < B.R.m := hi
  have hbox := GlobalTheory.LvT.Built.Box.inBox_xiAt B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) _ _ u i hXo hPr
    hI.sel_ok (hI.T_mem u) hI.g_mem (hI.idx_ok a) hi' ⟨_, _, _, _, hI.ch_tied⟩ c.1.1 c'.1.1 ((I.stp u a i).rep c.1)
    ((I.stp u a (i + 1)).rep c'.1)
  have hLH := (TC.laHyp_eSmooth_true I hI hP l Z a u i hi').1
  have hLa := (hLH.2.2.2.2.2 _ _ ⟨((I.stp u a i).rep c.1).1.1.deco.2.lat, ((I.stp u a i).rep c.1).1.1.deco.2.uni⟩
    ⟨((I.stp u a (i + 1)).rep c'.1).1.1.deco.2.lat, ((I.stp u a (i + 1)).rep c'.1).1.1.deco.2.uni⟩).2
  have he : B.fields.embC I.A.σ₀ = tauE (I.rec7 l Z) := funext hEmb
  rw [he, ColIn.A_AA] at hLa
  set N := ((I.stp u a i).rep c.1).1.1.deco.1.N with hN
  set N' := ((I.stp u a (i + 1)).rep c'.1).1.1.deco.1.N with hN'
  have hΞ' : ∀ z, Φ (actO _ _ (A.h i _ c)⁻¹ (A.h (i + 1) _ c')⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r)) =
      w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1)
        ((I.stp u a (i + 1)).rep c'.1) (toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) z)) :=
    fun z => hΞ z
  obtain ⟨hsupp, hper⟩ := supp_per_of_inBox _ _ _ _ _ _ hbox B.embLL (w i α γ)
  have hth : I.th u a i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) =
      thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E)
        (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) (fun y => B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1
          ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) (I.A.e _ _ N N') := by
    rw [← he]
    have h2 : ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) = I.A.AA := (ColIn.A_AA I).symm
    rw [h2]
    rfl
  have hcore := fun (κ : ℂ) (E : VCx (I.rec7 l Z).what₂.Tau (B.R.N i) (B.R.N (i + 1)) → ℂ) => GlobalTheory.T.thetaKernel_splitPlaces_eq_jet_classicalTheta (I.rec7 l Z) ψ θ _ _ (B.R.N i) (B.R.N (i + 1)) (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi))
    (rankN (I.rec7 l Z) (i + 1) hi) I.A.δ I.A.sc (hStd i hi) s hHol (A.chr (i + 1)) (kom i) (hC.om i hi) A.e (ColIn.Sb I a u)
    hC.is.idem (vac i) Φ (comb ψ _ _ (dd i α γ) (vac i)) (hX.vc i hi) hSB hTh (A.h i _ c) (hC.is.h i (Nat.le_of_succ_le hi) _ c).1
    (A.h (i + 1) _ c') (hC.is.h (i + 1) hi _ c').1 N N' hMv hMv' (levC I.sel (I.tup a) (I.cst a) u) hc0 hcov h2qd hLa
    (fun y => w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) hΞ' hsupp hper κ E
  have hjet := fun G => jetP_cast (I.rec7 l Z) _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) s
    I.J.cD hcD G P
  have hxi0 : (∀ z, A.xi i hi (ι i α) (ι (i + 1) γ) z = 0) →
      ∀ y : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)), B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y) = 0 := by
    intro hz y
    obtain ⟨z, rfl⟩ := toHom_surj _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) y
    have h0 := (GlobalTheory.T.movedDatum_eq_finiteDatum_representativePair I hI hP l Z u a Ch₀ A hC.is i hi (ι i α) (ι (i + 1) γ) Φ hSB 0
      (fun z' => by simp only [hΦv z', hz z', mul_zero]) c c').2.2 z
    have h1 := (GlobalTheory.T.movedDatum_eq_finiteDatum_representativePair I hI hP l Z u a Ch₀ A hC.is i hi (ι i α) (ι (i + 1) γ) Φ hSB 1
      (fun z' => by simp only [hΦv z', hz z', mul_zero]) c c').2.2 z
    rw [h0, zero_mul, one_mul] at h1
    exact h1.symm
  by_cases hm : w i α γ ≠ 0 ∧ ∃ z, A.xi i hi (ι i α) (ι (i + 1) γ) z ≠ 0
  · obtain ⟨hw, hxz⟩ := hm
    have hVE : xiN θ _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) I.A.δ I.A.sc
        (kom i (A.h i _ c, A.h (i + 1) _ c') (vac i)) = fun z => (c₀ i * (A.chr (i + 1) (A.xr i (ι i α)) : ℂ) *
          (A.chr (i + 1) (A.xr (i + 1) (ι (i + 1) γ)) : ℂ)⁻¹ * ((I.chIn u a).rho i c.1 * (I.chIn u a).rho' i c'.1) * w i α γ) *
          ((w i α γ)⁻¹ * I.A.e _ _ N N' z) := by
      refine hV.trans (funext fun z => ?_)
      have h3 : I.A.e _ _ N N' z = I.A.chiF _ _ N N' * I.J.V.thMoved _ _ N N' z := rfl
      rw [h3, mul_assoc (c₀ i), hχ]
      field_simp
    have hwE : (fun z => w i α γ * ((w i α γ)⁻¹ * I.A.e _ _ N N' z)) = I.A.e _ _ N N' :=
      funext fun z => by rw [← mul_assoc, mul_inv_cancel₀ hw, one_mul]
    have hT : jetP _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) s
        (thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E)
          (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) (fun y => w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) (fun z => (w i α γ)⁻¹ * I.A.e _ _ N N' z)) P =
        jetL I.J.cD (I.th u a i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1))
          (mvZ (fun _ => 1) (fun τ => (s / I.J.cD τ) • 1) (castP (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) P)) := by
      have h6 : thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) (fun y => w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) (fun z => (w i α γ)⁻¹ * I.A.e _ _ N N' z) =
          I.th u a i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) :=
        (GlobalTheory.T.classicalThetaOfDatum_smul_move _ _ _ _ _ _ _ _ _ _ _ _).trans ((congrArg (fun G => thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) (fun y => B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) G) hwE).trans hth.symm)
      exact (congrArg (fun t => jetP _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) s t P) h6).trans (hjet _)
    rw [hcore _ _ hVE, hC.cst i hi α γ hxz]
    refine (congrArg (fun t => _ * (_ * t)) hT).trans ?_
    have hT'' : jetL I.J.cD (I.th u a i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1))
          (mvZ (fun _ => 1) (fun τ => (s / I.J.cD τ) • 1) (castP (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) P)) * ((I.chIn u a).rho i c.1 * (I.chIn u a).rho' i c'.1) = A.abelian₂ i c.1 c'.1 (mvZ (fun _ => 1) (fun τ => (s / I.J.cD τ) • 1) (castP (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) P)) := mul_comm _ _
    refine Eq.trans ?_ (congrArg (fun t => _ * t) hT'')
    ring
  · have hΞz : (fun y => w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) = fun _ => 0 := by
      funext y
      by_cases hw : w i α γ = 0
      · rw [hw, zero_mul]
      · have hz : ∀ z, A.xi i hi (ι i α) (ι (i + 1) γ) z = 0 := fun z => by_contra fun h => hm ⟨hw, z, h⟩
        rw [hxi0 hz y, mul_zero]
    have hT0 : jetP _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) s
        (thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E)
          (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) (fun y => w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) (I.J.V.thMoved _ _ N N')) P = 0 := by
      have h5 : thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) (fun y => w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) (I.J.V.thMoved _ _ N N') = 0 :=
        (congrArg (fun G : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)) → ℂ => thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) G (I.J.V.thMoved _ _ N N')) hΞz).trans (thC_zero _ _ _ _ _ _ _ _ _ _)
      exact (congrArg (fun t => jetP _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) s t P) h5).trans (jetP_zero' _ _ _ _ _ s P)
    rw [hcore _ _ hV]
    refine (congrArg (fun t => _ * (_ * t)) hT0).trans ?_
    simp only [mul_zero]
    by_cases hxz : ∃ z, A.xi i hi (ι i α) (ι (i + 1) γ) z ≠ 0
    · have hw : w i α γ = 0 := by
        by_contra hw
        exact hm ⟨hw, hxz⟩
      rw [hC.cst i hi α γ hxz, hw]
      simp
    · have hz : ∀ z, A.xi i hi (ι i α) (ι (i + 1) γ) z = 0 := fun z => by_contra fun h => hxz ⟨z, h⟩
      have hth0 : I.th u a i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) = 0 := by
        rw [hth]
        have h4 : (fun y => B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) = fun _ => 0 := funext (hxi0 hz)
        exact (congrArg (fun G : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)) → ℂ => thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) G (I.A.e _ _ N N')) h4).trans (thC_zero _ _ _ _ _ _ _ _ _ _)
      have hL0 : A.abelian₂ i c.1 c'.1 (mvZ (fun _ => 1) (fun τ => (s / I.J.cD τ) • 1) (castP (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) P)) = 0 := by
        show ((I.chIn u a).rho i c.1 * (I.chIn u a).rho' i c'.1) • jetL I.J.cD (I.th u a i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1))
          (mvZ (fun _ => 1) (fun τ => (s / I.J.cD τ) • 1) (castP (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) P)) = 0
        rw [hth0, jetL_zero', LinearMap.zero_apply, smul_zero]
      exact ((congrArg (fun t => cK i * t) hL0).trans (mul_zero _)).symm
