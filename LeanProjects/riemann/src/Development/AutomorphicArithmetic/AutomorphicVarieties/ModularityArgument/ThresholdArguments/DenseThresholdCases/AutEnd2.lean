import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.AutEnd2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PrDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQN
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NewformAut0
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EndsRankThreeOfLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Across2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.AutNewformW

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private kills_pow pairing2 from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.RankTwoDescentImagQuadratic
open private kills_open exists_two flag det_one sq_of_trace norm_lt' cont_val cont_of_open irr_sub comm_mem isIrr_of tw_tw det_star conj_mat from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.AutEnd2OfAutPt
open UpperTheory.GalN.V
open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V
open UpperTheory.V.Z.Win UpperTheory.V.Z
private theorem detAlg (H : _root_.UpperTheory.V.Af.HypothesesH') {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {W : G ℚ Ω →* GL (Fin 2) (Qbar l)} (hW : Continuous W) {M : ℕ} (hM : 1 ≤ M) (hχ : Af.KillsMu M (Matrix.GeneralLinearGroup.det.comp W)) :
    Af.IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W) := by
  obtain ⟨k, hk, hpow⟩ := kills_pow hM hχ
  refine (_root_.UpperTheory.V.Af.algOfCyc_s H ℚ Ω l ι).1 _ (Matrix.GeneralLinearGroup.continuous_det.comp hW) fun w _ => ?_
  obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
  exact ⟨A, hA, 0, k, hk, fun s _ => by rw [neg_zero, zpow_zero, mul_one, hpow]⟩
private theorem polTwo {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime]
    {ι : Qbar l ≃+* ℂ} (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (h : Af.IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W)) (c : G ℚ Ω)
    (hc : Sd.IsCC c) : Af.Sol.Pol ι (W.comp (Base.galEmb ℚ K Ω)) := by
  obtain ⟨Q, hQ⟩ := pairing2 W c
  exact ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, _, c, Q, h,
    Ws.auSign _, hc, fun s s' h => by
      have h' : Base.galEmb ℚ K Ω s' = c * Base.galEmb ℚ K Ω s * c⁻¹ := h
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h']
      exact hQ _ _ rfl⟩
open UpperTheory.V.Pr.LkAut2 in
theorem UpperTheory.V.Z.Win.Dn.autEnd2_alt (H : _root_.UpperTheory.V.Af.HypothesesH') (hPot : Dn.PotTwo) (hIne : Dn.Ine2) :
    RankTwoAutomorphyDescendsFromAbelianCMToRat → _root_.UpperTheory.V.Z.Win.RR.AutNewformA → Sd.TwC → Sd.AlgCyc → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
      {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] {Φ : Fr.Frame l (ResidueField c.O)} (k : GalLink D.η D.Ψ D.cc g₁ B M L Φ) [CharP (ResidueField c.O) l] {C₀ : ℕ}, Φ.Ok C₀ → l ∣ M → B.valuation (l : Ω) < 1 → LinkHyp c N e D.η D.cc B M →
      ∀ (ι : Qbar l ≃+* ℂ) (ka : G L Ω →* (Qbar l)ˣ), Sd.IsAlgChar ι ka → _root_.UpperTheory.V.Pr.AutPtAlt k 2 ι ka → _root_.UpperTheory.V.Z.Win.Dn.AutEnd2A c D.η D.Ψ D.cc g₁ B e ι := by
  intro hDown hNew hTw hAlg Ω _ _ _ K _ _ _ l hl c N _ e ψ D g₁ B M L _ _ _ _ Φ k _ C₀ hok hM hB hLk ι ka hka hA
  intro A _ _ r hr hII h11 W hW _
  obtain ⟨hcc, hηc, -, hηl, -, -, h2, hcm, -⟩ := dat_facts D
  obtain ⟨hk1, hk2, hk3, -⟩ := eta_killsMu D
  haveI := k.ab
  haveI := hcm
  haveI : IsAlgClosure K Ω := Th.Db.algClo K Ω
  haveI : Module.IsTorsionFree L Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
  haveI : FaithfulSMul c.O A := (faithfulSMul_iff_algebraMap_injective _ _).2 fun x y h =>
    Subtype.ext (congrArg A.val h)
  haveI : IsLocalHom (algebraMap c.O A) := Algebra.IsIntegral.isLocalHom _ _
  haveI : IsNoetherianRing A := PrincipalIdealRing.isNoetherianRing
  have hW' : ∀ g ∈ D.η.ker, (W g).val = (corner (r g).mat).map A.val := hW
  have hblk : Block D.η r := fun g hg a b h => Subtype.ext (hII.1 g hg a b h)
  have hirr : MatIrr D.η.ker fun g => (W g).val := fun V hV => hII.2 V fun g hg v hv => by
    have : (W g).val.mulVec v ∈ V := hV g hg v hv
    rwa [hW g hg] at this
  have hopen : IsOpen (D.η.ker : Set (G ℚ Ω)) := hηl.isOpen_fiber 1
  have hcont : Continuous W := by
    refine cont_of_open W D.η.ker hopen _ (continuous_matrix fun i j => ?_) hW
    exact cont_val (A.val : A →+* PadicAlgCl l) (norm_lt' c A) (fun g => (r g).mat (![0, 2] i) (![0, 2] j)) fun n =>
      (hr.cont n).comp fun X => X (![0, 2] i) (![0, 2] j)
  have hdW : ∀ g ∈ D.η.ker, (W g).val.det = A.val (corner (r g).mat).det := fun g hg => by
    rw [hW' g hg, AlgHom.map_det]
    rfl
  have hdet : ∀ g ∈ D.η.ker, (W g).val.det = 1 := fun g hg => by
    obtain ⟨s1, s2⟩ := mat_gstar r D.cc g hr.norm.atc ((hr.red.mult _).trans hηc) ((hr.red.mult _).trans hg)
    have e1 := hdW _ (show gstar D.cc g ∈ D.η.ker from (hr.red.mult _).symm.trans s2)
    rw [s1, det_star, ← hdW g hg] at e1
    have e2 : Matrix.GeneralLinearGroup.det (W (gstar D.cc g)) * Matrix.GeneralLinearGroup.det (W g) = 1 := by
      have := congrArg (Matrix.GeneralLinearGroup.det.comp W) hcc
      rw [map_mul, map_one] at this
      show (Matrix.GeneralLinearGroup.det.comp W) (D.cc * g⁻¹ * D.cc) * (Matrix.GeneralLinearGroup.det.comp W) g = 1
      rw [map_mul, map_mul, map_inv, mul_right_comm _ _⁻¹, this, one_mul, inv_mul_cancel]
    have e3 : (W (gstar D.cc g)).val.det * (W g).val.det = 1 := congrArg Units.val e2
    rw [e1, hdW g hg, ← map_mul] at e3
    rw [hdW g hg, det_one hr.red h2 g ((sq _).trans (Subtype.ext e3)), map_one]
  have hcyc : Af.IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W) :=
    ⟨_, Matrix.GeneralLinearGroup.det.comp W, hk2, fun s hs => Units.ext (hdet s (hk1 s hs)), by simp⟩
  obtain ⟨hg, eg⟩ := k.g0
  have hηg : D.η g₁ = 1 := by
    have h := k.del ⟨g₁, hg⟩
    rw [eg] at h
    exact h.symm.trans Φ.g0.2
  have hirrL : Af.IsIrr (W.comp (Base.galEmb ℚ L Ω)) := by
    refine isIrr_of W _ _ (Base.range_galEmb ℚ L Ω).ge (irr_sub W D.η.ker (Base.galOf ℚ L Ω) (comm_mem L Ω) hirr
      (barChar c.O D.Ψ) (fun g hg ht => sq_of_trace hr.red g (Subtype.ext ?_)) g₁ (k.gal ▸ ⟨hg, hηg⟩) hηg ?_)
    · rw [hW g hg, Matrix.trace_fin_two] at ht
      exact ht
    · have h := k.psi ⟨g₁, hg⟩
      rw [eg] at h
      exact h ▸ hok.baseSubgroup_spec
  obtain ⟨ρ, r1, r2, r3⟩ := exists_nrep2 k hok hM hcc r hr hblk
  obtain ⟨⟨π, p1, -, p3⟩, hWit⟩ := _root_.UpperTheory.GalN.V.csdN'_alt H.toClassicalTheorems (by norm_num) <| hA A ρ r1 r3 (W.comp (Base.galEmb ℚ L Ω)) (fun s => by
    rw [r2]
    exact hW' _ (k.gal.le (Base.galEmb_mem ℚ L Ω s)).2) hirrL
  have hC := hTw L Ω l ι 2 _ ka⁻¹ ((hAlg L Ω l ι).2.2 ka hka) ⟨π, p1, p3⟩
  rw [tw_tw] at hC
  have hR := hDown L Ω l ι W hcont hcyc hirrL
    ⟨D.η, D.cc, D.conj, hηc, fun s => (k.gal.le (Base.galEmb_mem ℚ L Ω s)).2⟩ hC
  have hΨ : ∀ g, Chr.dirG ℚ Ω ψ g = 1 → D.ΨQ g = cycBar ℚ Ω l g ^ (e : ℤ) := fun g hg => by
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (Base.chiO ℚ Ω l c.O g ^ (e : ℤ) * Chr.dirG ℚ Ω ψ g) = _
    rw [hg, mul_one, map_zpow]
    rfl
  suffices hfl : Af.IsFlagOn W ((D.η.ker ⊓ (Chr.dirG ℚ Ω ψ).ker) ⊓ Ine (F := ℚ) B)
      (fun i => ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)).comp ((D.η.ker ⊓ (Chr.dirG ℚ Ω ψ).ker) ⊓ Ine (F := ℚ) B).subtype) by
    have hop := hopen.inter (kills_open (NeZero.pos N) hk3)
    have hWL := hWit (Af.Bc.irrBasic.2 _ _ _ _ _ (hcont.comp (Af.continuous_restrictScalarsHom ℚ L Ω)) hka.1)
    have hirrQ := isIrr_of W (MonoidHom.id _) _ (fun g _ => ⟨g, rfl⟩) hirr
    obtain ⟨f, hf⟩ := _root_.UpperTheory.V.Z.Win.Dn.nw' hNew Ω l ι e D.gd.e_pos W hcont hirrQ hR
      ⟨hcyc, L, _, _, _, inferInstance, _, hirrL, ⟨D.η, D.cc, D.conj, hηc, fun s => (k.gal.le (Base.galEmb_mem ℚ L Ω s)).2⟩, ka, hka, hWL⟩
      B hB _ hop hfl
    refine ⟨⟨f, hf⟩, ?_⟩
    have hQ0 : IsAutomorphicOverImagQuad ι W := _root_.UpperTheory.GalN.V.newformAut0_alt H.toClassicalTheorems _ (by have := D.gd.e_pos; omega) f l Ω ι W _ hf
    have hP := hPot Ω l e D.gd.e_pos W B hB _ hop inferInstance hfl
    have hFl : Flagged W := fun v hv A' hA' => (hP v hv A' hA').imp fun _ x => x.1
    have hI : IneAb W := hIne Ω l c N e ψ D.η D.cc g₁ B M hLk L Φ C₀ k hok A r hr hblk h11 K D.η_ker hopen W hW
    obtain ⟨hc', art, χ, a, h'⟩ := (hAlg L Ω l ι).2.2 ka hka
    have h1 := _root_.UpperTheory.V.Z.Win.Dn.twist'_alt H.toClassicalTheorems ⟨χ, hc', art, a, h'⟩ hc' hWL
    rw [tw_tw] at h1
    obtain ⟨_, _⟩ := Th.Db.algKL K L Ω (D.η_ker ▸ (k.gal ▸ inf_le_right : Base.galOf ℚ L Ω ≤ D.η.ker))
    obtain ⟨_, hsol⟩ := Th.Db.galKL K L k.ab
    have i2 : Af.IsIrr ((W.comp (Base.galEmb ℚ K Ω)).comp (Base.galEmb K L Ω)) := hirrL
    have i1 : Af.IsIrr (W.comp (Base.galEmb ℚ K Ω)) := (Af.Bc.irrBasic.1 _ _ _ 2 _).1 _ i2
    have hcK : Continuous (W.comp (Base.galEmb ℚ K Ω)) := hcont.comp (Af.continuous_restrictScalarsHom ℚ K Ω)
    have halg : Af.IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W) := detAlg H hcont hk2 fun s hs => Units.ext (hdet s (hk1 s hs))
    have fl := (flagLaws ℚ Ω l 2 W).2.2.2 K
    have hWK : _root_.UpperTheory.V.Z.Win.WitA ι (W.comp (Base.galEmb ℚ K Ω)) :=
      _root_.UpperTheory.V.Z.Win.Dn.down'_alt L H hsol (by norm_num) hcK i2 (polTwo K W halg D.cc D.conj) (hQ0 hcont K D.gd.quad i1) (fl.2.1 hFl) (fl.1 hI)
        (Keep.keeps2 Ω l c N e ψ D.η D.cc g₁ B M hLk L Φ C₀ k hok A r hr hblk h11 K D.η_ker _
          fun s => hW _ (D.η_ker.ge (Base.galEmb_mem ℚ K Ω s))) h1
    exact _root_.UpperTheory.V.Z.Win.Dn.across2'_alt H K Ω D.gd.quad (by norm_num) hP hcont hQ0 ⟨_, halg, dual_two W⟩ hI hFl i1 hWK
  obtain ⟨h, -, hT⟩ := hr.ord
  obtain ⟨s₀, hs₀, hn⟩ := exists_two D.gd.l_odd B hB
  have hID : ∀ s ∈ Ine (F := ℚ) B, s ∈ Dec (F := ℚ) B := fun s hs => Ine_le_Dec B hs
  have hf := flag (D.η.ker ⊓ (Chr.dirG ℚ Ω ψ).ker ⊓ Ine (F := ℚ) B) W (cycBar ℚ Ω l ^ (e : ℤ))
    (fun g => (UnitaryThreeInertia.push A.val r g).mat) (Matrix.GeneralLinearGroup.map (A.val : A →+* PadicAlgCl l) h)
    (fun s hs => hW s hs.1.1) (fun s hs => hII.1 s hs.1.1) (fun s hs => congrArg Subtype.val (h11 s hs.1.1))
    (fun s hs => hdet s hs.1.1) (fun s hs => ?_) (fun s hs i j hij => ?_) ?_
  · convert hf using 1
    funext i
    fin_cases i
    · rfl
    · simp
  · refine (conj_mat _ r h s ((hr.red.mult _).trans hs.1.1) 0 0).trans ?_
    have := hT.ine ⟨s, hID s hs.2⟩ hs.2 hs.1.1 0
    refine (congrArg A.val this).trans ?_
    rw [MonoidHom.zpow_apply, ← hΨ s hs.1.2]
    simp [UnitaryThreeInertia.psi, wt1]
    rfl
  · refine (conj_mat _ r h s ((hr.red.mult _).trans hs.1.1) i j).trans ?_
    exact (congrArg A.val (hT.tri ⟨s, hID s hs.2⟩ hs.1.1 i j hij)).trans (map_zero _)
  · refine ⟨s₀ ^ (2 * Nat.card (ZMod N)ˣ), ⟨⟨?_, ?_⟩, pow_mem hs₀ _⟩, fun h0 => ?_⟩
    · show D.η _ = 1
      rw [map_pow, pow_mul, Int.units_sq, one_pow]
    · show ψ.toUnitHom (Chr.cls ℚ Ω N _) = 1
      rw [map_pow, pow_mul', pow_card_eq_one', one_pow, map_one]
    · have := hn (((2 * Nat.card (ZMod N)ˣ : ℕ) : ℤ) * e * 2) (Units.ext (by
        rw [_root_.zpow_mul, _root_.zpow_mul, zpow_two, ← sq, Units.val_pow_eq_pow_val, _root_.zpow_natCast _ (2 * _), ← map_pow]
        exact h0))
      have h3 : 0 < 2 * Nat.card (ZMod N)ˣ * e * 2 := by
        have := D.gd.e_pos
        have := Nat.card_pos (α := (ZMod N)ˣ)
        positivity
      exact h3.ne' (by exact_mod_cast this)
end
