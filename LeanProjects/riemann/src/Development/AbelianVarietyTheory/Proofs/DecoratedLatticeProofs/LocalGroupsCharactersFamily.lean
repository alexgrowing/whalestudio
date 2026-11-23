import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatNotSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmSplitHalves
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TupChars

section Loc

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def cmp (q : GlobalTheory.FinPl.SplitPt D k) (χ : (AE D)ˣ →* Circle) : kˣ →* ℂˣ :=
  (Circle.toUnits.comp χ).comp (GlobalTheory.LocChar.unitsHom (ofSplit q))

theorem isComp_cmp (q : GlobalTheory.FinPl.SplitPt D k) (χ : (AE D)ˣ →* Circle) : (ofSplit q).IsComp χ (cmp q χ) := by
  intro x a ha
  have : GlobalTheory.LocChar.unitsHom (ofSplit q) x = a := Units.ext ha.symm
  simp only [cmp, MonoidHom.comp_apply, this]
  rfl

theorem cmp_apply (q : GlobalTheory.FinPl.SplitPt D k) (χ : (AE D)ˣ →* Circle) (x : kˣ) :
    ((cmp q χ x : ℂˣ) : ℂ) = (χ (GlobalTheory.LocChar.unitsHom (ofSplit q) x) : ℂ) := rfl

theorem unitsHom_int (q : GlobalTheory.FinPl.SplitPt D k) (y : kˣ) (hy : valuation k (y : k) = 1) :
    finPart D ((GlobalTheory.LocChar.unitsHom (ofSplit q) y : (AE D)ˣ) : AE D) ∈ intAE D := by
  have he1 : q.e * q.e = q.e := q.split.1
  show finPart D (q.sec y + (1 - q.e)) ∈ intAE D
  rw [(finPart D).map_add, (finPart D).map_sub, (finPart D).map_one]
  exact add_mem ((q.int_iff _).1 ((Valuation.mem_integer_iff _ _).2 hy.le))
    (sub_mem (GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (mul_one 1))
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← (finPart D).map_mul, he1])))

theorem unit_trivial (q : GlobalTheory.FinPl.SplitPt D k) {χ : (AE D)ˣ →* Circle}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χ q.v) (x : kˣ) (hx : valuation k (x : k) = 1) :
    χ (GlobalTheory.LocChar.unitsHom (ofSplit q) x) = 1 := by
  obtain ⟨ε, hε, hsum⟩ := q.above
  have he1 : q.e * q.e = q.e := q.split.1
  have hec : q.e * cA D q.e = 0 := q.split.2.1
  have hes : q.e * q.sec x = q.sec x := by
    have := q.sec_pr (q.sec x)
    rw [q.pr_sec] at this
    exact this.symm
  have hz : algebraMap (AF D.host.F) (AE D) ε * (q.sec x - q.e) = q.sec x - q.e := by
    rw [← hsum]
    linear_combination (1 - cA D q.e) * hes - he1 + (q.sec x - 1) * hec
  obtain ⟨hi, hf⟩ := (GlobalTheory.VacStabFixed.supp_iff hε _).1 hz
  have hU : ((GlobalTheory.LocChar.unitsHom (ofSplit q) x : (AE D)ˣ) : AE D) = 1 + (q.sec x - q.e) := by
    show q.sec x + (1 - q.e) = _
    ring
  refine h _ ?_ (fun w hw => ?_) (unitsHom_int q x hx) ?_
  · rw [hU, (infPart D).map_add, (infPart D).map_one, hi, add_zero]
  · rw [hU, (finPart D).map_add, (finPart D).map_one, RingHom.map_add, RingHom.map_one, hf w hw, add_zero]
  · rw [← map_inv]
    exact unitsHom_int q x⁻¹ (by rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one])

theorem val_eq_one_of_sub (x : kˣ) (hx : valuation k ((x : k) - 1) < 1) : valuation k (x : k) = 1 := by
  have e : (x : k) = ((x : k) - 1) + 1 := by ring
  rw [e, Valuation.map_add_eq_of_lt_right _ (by rwa [map_one]), map_one]

end Loc

section Pack

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex}

theorem under_ne (hP : PkHyp W) (t : W.P.T) {PP P' : Formalism.L2.DIV.Pl D.host.E} (hPg : PP ∈ (pk W).Pg) (hQ : P' ∈ (pk W).Q t) :
    P'.under (𝓞 D.host.F) ≠ PP.under (𝓞 D.host.F) := by
  intro heq
  have hL := hP.bot.hyp.2.2.2.1.lev
  obtain ⟨k, hk⟩ := (hL.Pg PP).1 hPg
  obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hL.Q_pl t P' hQ
  have hmemK : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (PP.under (𝓞 D.host.K)).asIdeal := by
    have h := (pk W).C.P.pb_over k
    have hk' : PP.under (𝓞 D.host.K) = (pk W).C.P.pb k := hk
    rw [hk']; exact h
  have hmemE : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := hmemK
    simpa using h2
  have hmemF : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (PP.under (𝓞 D.host.F)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal
    simpa using hmemE
  rw [← heq] at hmemF
  have hmemE' : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal := by
    have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ P'.asIdeal := hmemF
    simpa using h2
  haveI : Finite (kP P') := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq.ne_zero)
  have : P'.asIdeal.IsPrime := P'.isPrime
  haveI : Nontrivial (kP P') := inferInstance
  haveI : Fintype (kP P') := Fintype.ofFinite _
  have h0g : ((D.host.g k : ℕ) : kP P') = 0 := by
    have := (Ideal.Quotient.eq_zero_iff_mem (I := P'.asIdeal)).2 hmemE'
    simpa using this
  have h0q : ((q : ℕ) : kP P') = 0 := by
    rw [← hcard, Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero (kP P')
  have hd1 : ringChar (kP P') ∣ D.host.g k := ringChar.dvd h0g
  have hd2 : ringChar (kP P') ∣ q := ringChar.dvd h0q
  have hcop : Nat.Coprime q (D.host.g k) := (Nat.coprime_primes hq (D.host.g_prime k)).2 (hne k)
  have h1 : ringChar (kP P') = 1 := Nat.eq_one_of_dvd_coprimes hcop hd2 hd1
  exact CharP.ringChar_ne_one h1

theorem xi_charUnramAt (hP : PkHyp W) (t : W.P.T) {PP : Formalism.L2.DIV.Pl D.host.E} (hPg : PP ∈ (pk W).Pg) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D ((pk W).toLevCh.xi t) (PP.under (𝓞 D.host.F)) := by
  have hL := hP.bot.hyp.2.2.2.1.lev
  refine GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => ?_
  refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.xi t) w).2 ?_
  by_contra hu
  rcases (hL.Q_ram t w).1 hu with h | ⟨P', hP', hc⟩
  · exact under_ne hP t hPg h hw
  · exact under_ne hP t hPg hP' ((GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc).trans hw)

theorem eta_charUnramAt (hP : PkHyp W) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (pk W).eta v := by
  have hL := hP.bot.hyp.2.2.2.1.lev
  exact GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w _ => (GlobalTheory.LFun.unrAt_iff_of_chrEq hL.eta w).2 ((pk W).C.isEta.unr w)

end Pack

theorem gLoc_chars : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (f : FamCh W u) (v : VCom f.c), f.RowOK → VTie f v → ∀ t (n : ℕ) (G : Fin n → GLoc v) pl, GRead f G pl → ∀ i, (G i).Chars (f.t t) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP f v hR _ t n G pl hG i
  have hq : (G i).q.v = (pl i).1.under (𝓞 D.host.F) := (hG.idem i).2
  have hxi : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D ((pk W).toLevCh.xi t) (G i).q.v := hq ▸ xi_charUnramAt hP t (pl i).2
  have heta : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (pk W).eta (G i).q.v := eta_charUnramAt hP _
  let M : ℕ → (AE D)ˣ →* Circle := (pk W).toLevCh.mu t
  let μ : ℕ → (G i).kˣ →* ℂˣ := fun m =>
    if 1 ≤ m ∧ m ≤ D.R.m then cmp (G i).q ((Lift.chrStep M (pk W).eta m).1⁻¹) else (G i).S.μ m
  have hμ : ∀ m, 1 ≤ m → m ≤ D.R.m → μ m = cmp (G i).q ((Lift.chrStep M (pk W).eta m).1⁻¹) :=
    fun m h1 h2 => if_pos ⟨h1, h2⟩
  have hunit : ∀ m (x : (G i).kˣ), valuation (G i).k (x : (G i).k) = 1 → μ m x = (G i).S.μ m x := by
    intro m x hx
    by_cases hm : 1 ≤ m ∧ m ≤ D.R.m
    · rw [hμ m hm.1 hm.2]
      apply Units.ext
      rw [cmp_apply, hG.mu i m hm.1 hm.2 x (GlobalTheory.LocChar.unitsHom (ofSplit (G i).q) x) rfl]
      have hx1 := unit_trivial (G i).q hxi x hx
      have e : (Lift.chrStep M (pk W).eta m).1 = (Lift.chrStep (pk W).mu0 (pk W).eta m).1 * (pk W).toLevCh.xi t := by
        simp only [Lift.chrStep, M, LevCh.mu, Lift.tup]
        split_ifs
        · exact mul_right_comm _ _ _
        · rfl
      rw [MonoidHom.inv_apply, MonoidHom.inv_apply, e, MonoidHom.mul_apply, hx1, mul_one]
    · simp only [μ, if_neg hm]
  have htame : ∀ m, GlobalTheory.SplitWeil.IsTame (μ m) := by
    intro m x hx
    rw [hunit m x (val_eq_one_of_sub x hx)]
    exact (G i).S.tame m x hx
  have hm2 : Even D.R.m := D.R.m_even
  refine ⟨μ, htame, hunit, fun j ρ h => ?_, fun j σ h => ?_⟩
  · obtain ⟨-, -, hV, hW⟩ := (hR.row t).sBF j ρ h
    have hV' : ((f.t t).sBF j ρ h).χV = M (j + 1) * (pk W).eta⁻¹ := hV
    have hW' : ((f.t t).sBF j ρ h).χW = M (j + 1) := hW
    have hodd : Odd (j + 1) := by
      obtain ⟨r, hr⟩ := hm2
      exact ⟨j / 2, by omega⟩
    have hμj : μ (j + 1) = cmp (G i).q ((M (j + 1) * (pk W).eta⁻¹)⁻¹) := by
      rw [hμ (j + 1) (by omega) (by omega)]
      simp only [Lift.chrStep, if_pos hodd]
    rw [hV', hW', hμj]
    refine ⟨isComp_cmp _ _, cmp (G i).q (M (j + 1)), isComp_cmp _ _, fun x hx => ?_⟩
    apply Units.ext
    rw [Units.val_mul, cmp_apply, cmp_apply, Units.val_one, ← Circle.coe_mul, ← MonoidHom.mul_apply]
    have e : M (j + 1) * (M (j + 1) * (pk W).eta⁻¹)⁻¹ = (pk W).eta := by
      rw [_root_.mul_inv_rev, inv_inv, mul_comm, mul_assoc, inv_mul_cancel, mul_one]
    rw [e, unit_trivial (G i).q heta x hx, Circle.coe_one]
  · obtain ⟨-, -, hV, hW⟩ := (hR.row t).sFB j σ h
    have hV' : ((f.t t).sFB j σ h).χV = M (j + 1 + 1) := hV
    have hW' : ((f.t t).sFB j σ h).χW = M (j + 1 + 1) * (pk W).eta⁻¹ := hW
    have heven : ¬ Odd (j + 1 + 1) := by
      obtain ⟨r, hr⟩ := hm2
      rw [Nat.not_odd_iff_even]
      exact ⟨j / 2 + 1, by omega⟩
    have hμj : μ (j + 1 + 1) = cmp (G i).q (M (j + 1 + 1))⁻¹ := by
      rw [hμ (j + 1 + 1) (by omega) (by omega)]
      simp only [Lift.chrStep, if_neg heven]
    rw [hV', hW', hμj]
    refine ⟨isComp_cmp _ _, cmp (G i).q (M (j + 1 + 1) * (pk W).eta⁻¹), isComp_cmp _ _, fun x hx => ?_⟩
    apply Units.ext
    rw [Units.val_mul, cmp_apply, cmp_apply, Units.val_one, ← Circle.coe_mul, ← MonoidHom.mul_apply]
    have e : M (j + 1 + 1) * (pk W).eta⁻¹ * (M (j + 1 + 1))⁻¹ = (pk W).eta⁻¹ := by
      rw [mul_right_comm, mul_inv_cancel, one_mul]
    rw [e, MonoidHom.inv_apply, unit_trivial (G i).q heta x hx, inv_one, Circle.coe_one]

end GlobalTheory.TupChars

end
