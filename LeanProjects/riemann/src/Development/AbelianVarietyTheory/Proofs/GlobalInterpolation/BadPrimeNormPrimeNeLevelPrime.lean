import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainSharpColumnValuationOfPointKernelLiftL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfMemZmu
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeUnit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationFinOrderApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnfoldingIsGoodCyclotomicInvariantReferenceLatti
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.VolqExistsPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntOfHomAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfPow

noncomputable section

namespace GlobalTheory.LvT.Built.IsTerm

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built
open GlobalTheory.ColPeriod GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator

section Generic

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] {a b : ℕ} {P : HeightOneSpectrum (𝓞 E)}

omit [StarRing E] in

theorem awayAt_of_fnModAt {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} {Φ : HomE E a b → K}
    (hq : (qOf P).Prime) (h : FnModAt P N N' Φ) (w : HeightOneSpectrum (𝓞 K)) {B : ℕ} (hB : 1 ≤ B) : AwayAt P w B N N' Φ := by
  refine ⟨fun x => valuation_le_one_of_mem_Zmu w hq (h.2.2 x), fun x z hz => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hB
  rw [pow_succ', mul_smul]
  refine h.2.1 x _ ?_
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hz _

theorem exists_place (K : Type) [Field K] [NumberField K] {T : ℕ} (hT : T.Prime) :
    ∃ w : HeightOneSpectrum (𝓞 K), (T : 𝓞 K) ∈ w.asIdeal := by
  have h1 : Ideal.span {(T : 𝓞 K)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro h
    have h2 := Formalism.L2.Col.Primes.natCast_dvd_intCast (E := K) (c := T) (n := 1) (by simpa using h.dvd)
    exact hT.one_lt.ne' (Nat.dvd_one.1 (by exact_mod_cast h2))
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h1
  have h3 : (T : 𝓞 K) ∈ M := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, fun h => ?_⟩, h3⟩
  rw [h, Ideal.mem_bot] at h3
  exact hT.ne_zero (by exact_mod_cast h3)

end Generic

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ} {u : Pr.Word}

theorem badPrimeNorm_prime_ne_levelPrime (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : Pr.T u ∈ S) (P : rowSG Pr sel mu) :
    (qOf P.1).Prime ∧ qOf P.1 ≠ Pr.T u := by
  have h := levelPrimes X Pr sel S mu hX hPr hsel P
  refine ⟨h.1.1, fun e => ?_⟩
  by_cases hP : P.1 ∈ Pr.vGs
  · obtain ⟨k, hk⟩ := exists_mem_vG hP
    exact hPr.T_ne_g u k (e.symm.trans (hPr.vG_norm k _ hk))
  · exact h.2 hP (e ▸ hS)

theorem localization_eq (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : Pr.T u ∈ S) {n : ℕ}
    {N N' : Submodule (𝓞 X.E) (Sp X.E n)} (h : SameOff (Pr.vT u) N N') (P : rowSG Pr sel mu) :
    localization₂ P.1.asIdeal N = localization₂ P.1.asIdeal N' := by
  have h1 := badPrimeNorm_prime_ne_levelPrime hX hPr hsel hS P
  have h2 : ((Pr.T u : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal :=
    natCast_notMem_of_ne (hPr.T_prime u) h1.1 h1.2.symm P.1 (Ideal.absNorm_mem _)
  refine h P.1 fun Q hQ => ?_
  have h3 := T_mem_of_piT_mem hPr u (GlobalTheory.ColPeriod.mem_divs hQ)
  refine ⟨fun e => h2 (e ▸ h3), fun e => h2 ?_⟩
  rw [e, mem_conjP, map_natCast]
  exact h3

theorem frsF_eq (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : Pr.T u ∈ S) {j : ℕ} {p q : PtAt R sel mu cst u j}
    (h : SameOffPt sel mu cst u p q) : frsF sel mu q.1.1 = frsF sel mu p.1.1 := by
  funext P
  unfold frsF
  split_ifs with hP
  · have e : q.1.1.deco.1.at P.1 = p.1.1.deco.1.at P.1 := (localization_eq hX hPr hsel hS h.1 P).symm
    unfold Deco.liftFr
    simp only [e, h.2.1]
  · rw [h.2.2.1]

theorem awayAt_locTop (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : Pr.T u ∈ S) (hL : L.Ok Ch sel mu cst G m2)
    (P : rowSG Pr sel mu) (w : HeightOneSpectrum (𝓞 X.K)) (hw : ((Pr.T u : ℕ) : 𝓞 X.K) ∈ w.asIdeal) {j : ℕ} (hj : j = R.m)
    (p : ChPt (R := R) sel mu u (m2 + 1)) {Y : Set (Sp X.E (R.N (m2 + 1)))} (hY : Y ∈ ybSet sel mu cst p.deco.1.N) :
    AwayAt P.1 w cst.B (stdLat X.E _) (stdLat X.E (R.N j)) fun x =>
      TopStep.locTop Ch sel mu cst m2 P (castSp X.E (congrArg R.N hj) ∘ₗ x) ((frsF sel mu p P).symm (repY Y)) := by
  subst hj
  have hc := hL.cst_ok
  have hm := hL.hm
  have hq := badPrimeNorm_prime_ne_levelPrime hX hPr hsel hS P
  have key : ∀ v : Sp X.E (R.N R.m), v ∈ stdAt X.E _ P.1 ↔
      prXp X.E R v ∈ stdAt X.E (R.N R.m - 1) P.1 ∧ IntAt P.1 (atNL X.E (R.N R.m) (R.N R.m - 1) v) := fun v => by
    rw [GlobalTheory.LastSteps.atNL_last]
    exact TopStep.mem_stdAt_succ (N_m_succ R)
  change AwayAt P.1 w cst.B _ _ fun x => TopStep.locTop Ch sel mu cst m2 P x ((frsF sel mu p P).symm (repY Y))
  by_cases hP : P.1 ∈ Pr.vGs
  · have hy : (qOf P.1 : X.E) • (frsF sel mu p P).symm (repY Y) ∈ stdAt X.E _ P.1 := by
      rw [← map_smul, GlobalTheory.LastSteps.frsF_symm_mem sel mu p P hP]
      exact GlobalTheory.LastSteps.q_smul_repY sel mu cst hY P hP
    refine awayAt_of_fnModAt hq.1 ?_ w hc.B_pos
    refine (GlobalTheory.LastSteps.fnModAt_iff _ _ _).2 ((GlobalTheory.LastSteps.good_PhiTop Ch mu hm cst.sharp hP).mul
      (GlobalTheory.LastSteps.good_ftY sel mu cst hc P hP hy)
      (fun x => prXp X.E R ∘ₗ x ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))))
      (fun x => atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ x) (fun x z => ?_) (fun x z => ?_) fun w => ?_)
    · rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul]
    · rw [LinearMap.comp_add, LinearMap.comp_smul]
    · rw [← LinearMap.comp_assoc, GlobalTheory.LastSteps.comp_funLeft_mem (GlobalTheory.LastSteps.cOf_top hm)]
      exact ⟨fun h => ⟨fun y hy => ((key _).1 (h y hy)).1, fun y hy => ((key _).1 (h y hy)).2⟩,
        fun h y hy => (key _).2 ⟨h.1 y hy, h.2 y hy⟩⟩
  · have hD := hL.depthQ P hP
    have hqw : ((qOf P.1 : ℕ) : 𝓞 X.K) ∉ w.asIdeal := natCast_notMem_of_ne hq.1 (hPr.T_prime u) hq.2 w hw
    have hy : ((qOf P.1 : X.E) ^ cst.M) • (frsF sel mu p P).symm (repY Y) ∈ stdAt X.E _ P.1 := by
      rw [← map_smul, ← TopTwist.frsF_mem' sel mu p P hP, LinearEquiv.apply_symm_apply]
      exact TopTwist.pow_smul_repY sel mu cst hY P hP
    refine ⟨fun x => ?_, fun x z hz => ?_⟩
    · unfold TopStep.locTop PhiTop
      rw [if_neg hP, map_mul]
      exact mul_le_one' (TopTwist.valuation_PhiQ w _ _ _ _ _ _ _ _ _) (TopTwist.valuation_ftY sel mu cst hc P hP hD w hqw hy _)
    · have hz' := fun y hy => (key _).1 (hz P.1 (Finset.mem_singleton_self _) y hy)
      have h1 : R.r ≤ R.N (m2 + 1) + cOf R (m2 + 1) := by
        unfold Ranks.r Ranks.N cOf
        rw [hm, mul_add (m2 + 1)]
        omega
      have h4 : R.N (m2 + 1) + cOf R (m2 + 1) ≤ R.N R.m - 1 + 0 := by
        unfold Ranks.N cOf
        rw [hm, show m2 + 2 = m2 + 1 + 1 from rfl, add_mul (m2 + 1)]
        omega
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hc.B_pos
      unfold TopStep.locTop PhiTop
      dsimp only
      rw [if_neg hP]
      congr 1
      · have e : prXp X.E R ∘ₗ (x + ((qOf P.1 : X.E) ^ cst.B) • z) ∘ₗ
              LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) =
            prXp X.E R ∘ₗ x ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) +
            (qOf P.1 : X.E) • ((((qOf P.1 : X.E) ^ k) • (prXp X.E R ∘ₗ z)) ∘ₗ
              LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) := by
          rw [hk, pow_succ', mul_smul]
          simp only [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.comp_assoc]
        rw [e]
        refine TopTwist.PhiQ_add _ h1 (h1.trans h4) _ _ ?_
        rw [GlobalTheory.LastSteps.comp_funLeft_mem (GlobalTheory.LastSteps.cOf_top hm), GlobalTheory.LastSteps.lamY_zero]
        exact fun y hy => TopStep.smul_mem_locP (TopStep.intAt_pow (TopStep.intAt_nat _) _) (hz' y hy).1
      · rw [LinearMap.comp_add, LinearMap.comp_smul]
        exact TopTwist.ftY_add sel mu cst hc P hP hD hy _ _ fun y hy => (hz' y hy).2

def MuqUnit (cst : LocCst X (rowSG Pr sel mu)) (R : Ranks) (u : Pr.Word) : Prop :=
  ∀ (P : rowSG Pr sel mu) (w : HeightOneSpectrum (𝓞 X.K)), P.1 ∉ Pr.vGs → ((Pr.T u : ℕ) : 𝓞 X.K) ∈ w.asIdeal →
    ∀ j, j < R.m → w.valuation X.K (cst.muq (j + 1) P) = 1

theorem muqUnit_of_tied (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : Pr.T u ∈ S) (hg : ∀ k, Pr.g k ∈ S)
    (hL : L.Ok Ch sel mu cst G m2) {σ₀ : X.K →+* ℂ} {e : Fin R.m → X.Tau → ℚ} {m0 : Fin R.m → Formalism.L2.Host.HChar X.E}
    {eta : Formalism.L2.Host.HChar X.E} (ht : Ch.Tied σ₀ e m0 eta) : MuqUnit cst R u := by
  intro P w hP hw j hj
  have hq := badPrimeNorm_prime_ne_levelPrime hX hPr hsel hS P
  have hn := (levelPrimes X Pr sel S mu hX hPr hsel P).2 hP
  have hg' : ∀ k, ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal := fun k =>
    natCast_notMem_of_ne (hPr.g_prime k) hq.1 (fun h => hn (h ▸ hg k)) P.1 (Ideal.absNorm_mem _)
  have hT : ((Pr.T u : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal :=
    natCast_notMem_of_ne (hPr.T_prime u) hq.1 hq.2.symm P.1 (Ideal.absNorm_mem _)
  have h1 : w.valuation X.K (Ch.muVal ⟨j, hj⟩ P.1 : X.K) = 1 :=
    heckeUnit X Pr R.m Ch σ₀ (e ⟨j, hj⟩) ⟨j, hj⟩ (m0 ⟨j, hj⟩) hX hPr (ht.mu0 _) (Pr.T u) w P.1 (hPr.T_prime u) hw hT
      (Formalism.L2.Host.unif P.1) _ (ht.muVal _ P.1 hg')
  rw [hL.muqQ j hj P hP, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀,
    (twistUnit X.F X.E X.K S mu P.1 w).2, h1]
  simp

theorem exists_local (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : Pr.T u ∈ S) (hL : L.Ok Ch sel mu cst G m2)
    (hU : MuqUnit cst R u) {i : ℕ} (hi : i < R.m) (b : Idx sel mu L i) (b' : Idx sel mu L (i + 1)) :
    ∃ Φ : rowSG Pr sel mu → Sp X.E (R.N i) → Sp X.E (R.N (i + 1)) → HomE X.E (R.N i) (R.N (i + 1)) → X.K,
      ∀ (p : PtAt R sel mu cst u i) (p' : PtAt R sel mu cst u (i + 1)),
        (∀ x, xiAt Ch sel mu cst L u i b b' p p' x = phiT X.K p.1.1.deco.1 p'.1.1.deco.1 x *
          ∏ P, Φ P ((frsF sel mu p.1.1 P).symm (repY p.1.2)) ((frsF sel mu p'.1.1 P).symm (repY p'.1.2))
            (inFr (frsF sel mu p.1.1 P) (frsF sel mu p'.1.1 P) x)) ∧
        ∀ (P : rowSG Pr sel mu) (w : HeightOneSpectrum (𝓞 X.K)), ((Pr.T u : ℕ) : 𝓞 X.K) ∈ w.asIdeal →
          AwayAt P.1 w cst.B (stdLat X.E _) (stdLat X.E _)
            (Φ P ((frsF sel mu p.1.1 P).symm (repY p.1.2)) ((frsF sel mu p'.1.1 P).symm (repY p'.1.2))) := by
  have hm := hL.hm
  have hq := badPrimeNorm_prime_ne_levelPrime hX hPr hsel hS (mu := mu)
  have hlp := levelPrimes X Pr sel S mu hX hPr hsel
  have heq := fun (P : rowSG Pr sel mu) (w : HeightOneSpectrum (𝓞 X.K)) (hw : ((Pr.T u : ℕ) : 𝓞 X.K) ∈ w.asIdeal)
    (hP : P.1 ∉ Pr.vGs) => EntQ.entryAtQ volumeAtQ X Pr R Ch sel S mu cst L G m2 hL P w hP (hlp P).1
      (natCast_notMem_of_ne (hq P).1 (hPr.T_prime u) (hq P).2 w hw) (hU P w hP hw)
  rcases lt_trichotomy (i + 2) R.m with h | h | h
  · refine ⟨fun P _ _ => XiAt Ch sel mu cst i P (L.h i (b.get (by omega)) P) (L.h (i + 1) (b'.get (by omega)) P),
      fun p p' => ⟨fun x => ?_, fun P w hw => ?_⟩⟩
    · rw [xiAt_entry Ch sel mu cst L h (b.some_get (by omega)).symm (b'.some_get (by omega)).symm]
      rfl
    · by_cases hP : P.1 ∈ Pr.vGs
      · exact awayAt_of_fnModAt (hq P).1 (entryAtG X Pr R Ch sel S mu cst L G m2 hL i (by omega) _ _ P hP (hlp P).1) w
          hL.cst_ok.B_pos
      · exact (heq P w hw hP).1 i (by omega) _ _
  · obtain rfl : i = m2 := by omega
    refine ⟨fun P _ y x => PsiAt Ch sel mu cst i P (L.h i (b.get (by omega)) P) x y, fun p p' => ⟨fun x => ?_, fun P w hw => ?_⟩⟩
    · rw [xiAt_penultimate_eq_xiCpl1 Ch sel mu cst L h (b.some_get (by omega)).symm]
      rfl
    · by_cases hP : P.1 ∈ Pr.vGs
      · exact awayAt_of_fnModAt (hq P).1 ((GlobalTheory.LastSteps.fnModAt_iff _ _ _).2
          (GlobalTheory.LastSteps.good_PsiAt Ch sel mu cst hm P hP (hL.stabG i _ P hP) _)) w hL.cst_ok.B_pos
      · exact (heq P w hw hP).2 _ _
  · obtain rfl : i = m2 + 1 := by omega
    have h1 : m2 + 1 + 1 = R.m := by omega
    refine ⟨fun P y _ x => TopStep.locTop Ch sel mu cst m2 P (castSp X.E (congrArg R.N h1) ∘ₗ x) y,
      fun p p' => ⟨fun x => ?_, fun P w hw => ?_⟩⟩
    · rw [xiAt_last Ch sel mu cst L h1]
      rfl
    · exact awayAt_locTop hX hPr hsel hS hL P w hw h1 p.1.1 (p.mem_ybSet h1)

theorem kerIsTerm_of_muqUnit (W : Wts X Pr.Word R) (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : Pr.T u ∈ S)
    (hL : L.Ok Ch sel mu cst G m2) (hU : MuqUnit cst R u) {i : ℕ} (hi : i < R.m) (A : Formalism.L2.Ker.Amb X) :
    KerIsTerm W Ch sel mu cst L A u i := by
  classical
  intro b b' p p'
  obtain ⟨Φ, hΦ⟩ := exists_local hX hPr hsel hS hL hU hi b b'
  have hA := fun P w hw => awayAt_inFr (isFrames_frsF p.1.1 P) (isFrames_frsF p'.1.1 P) ((hΦ p p').2 P w hw)
  refine ⟨fun x => if x ∈ divLat (cAof sel mu cst) (homAt (rowSG Pr sel mu) p.1.1.deco.1.N p'.1.1.deco.1.N) then
      ∏ P, Φ P ((frsF sel mu p.1.1 P).symm (repY p.1.2)) ((frsF sel mu p'.1.1 P).symm (repY p'.1.2))
        (inFr (frsF sel mu p.1.1 P) (frsF sel mu p'.1.1 P) x) else 0,
    ⟨fun x hx => ?_, fun x y hy => ?_⟩, fun w hw x => ?_, isFrames_frsF p.1.1, isFrames_frsF p'.1.1, fun q q' hq hq' => ?_⟩
  · by_contra h
    exact hx (if_neg h)
  · obtain ⟨w, hw⟩ := exists_place X.K (hPr.T_prime u)
    have hy' : y ∈ divLat (cAof sel mu cst) (homAt (rowSG Pr sel mu) p.1.1.deco.1.N p'.1.1.deco.1.N) := by
      obtain ⟨z, hz, rfl⟩ := hy
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hz)
    refine if_congr (Submodule.add_mem_iff_left _ hy') (Finset.prod_congr rfl fun P _ => ?_) rfl
    have hdv : qOf P.1 ^ cst.B ∣ cBof sel mu cst u :=
      Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ P)) _) _
    obtain ⟨z, hz, rfl⟩ := exists_of_mem_mulLat hdv hy P.2
    rw [Nat.cast_pow]
    exact (hA P w hw).2 x z hz
  · dsimp only
    split_ifs
    · rw [map_prod]
      exact Finset.prod_le_one' fun P _ => (hA P w hw).1 x
    · simp
  · unfold kAt GlobalTheory.KerT.term GlobalTheory.KerT.ker kerOf latSum
    rw [frsF_eq hX hPr hsel hS hq, frsF_eq hX hPr hsel hS hq']
    refine finsum_congr fun z => ?_
    generalize Function.surjInv _ z = x
    obtain ⟨x, hx⟩ := x
    have hx' : x ∈ divLat (cAof sel mu cst) (homAt (rowSG Pr sel mu) p.1.1.deco.1.N p'.1.1.deco.1.N) := by
      intro P hP y hy
      rw [localization_eq hX hPr hsel hS hq.1 ⟨P, hP⟩] at hy
      rw [localization_eq hX hPr hsel hS hq'.1 ⟨P, hP⟩]
      exact hx P (Finset.mem_union_right _ hP) y hy
    dsimp only
    rw [if_pos hx', (hΦ q q').1, frsF_eq hX hPr hsel hS hq, frsF_eq hX hPr hsel hS hq', ← hq.2.2.2, ← hq'.2.2.2]

end Chain

theorem kerIsTerm : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → L.Ok Ch sel mu cst G m2 → i < R.m → Ch.Ok → (∀ k, Pr.g k ∈ S) → (∃ (σ₀ : X.K →+* ℂ) (e : Fin R.m → X.Tau → ℚ) (m0 : Fin R.m → Formalism.L2.Host.HChar X.E) (eta : Formalism.L2.Host.HChar X.E), Ch.Tied σ₀ e m0 eta) → ∀ A : Formalism.L2.Ker.Amb X, KerIsTerm W Ch sel mu cst L A u i := by
  rintro X Pr R W Ch sel S mu cst L G m2 u i hX hPr hsel hS hL hi - hg ⟨σ₀, e, m0, eta, ht⟩ A
  exact kerIsTerm_of_muqUnit W hX hPr hsel hS hL (muqUnit_of_tied hX hPr hsel hS hg hL ht) hi A

end GlobalTheory.LvT.Built.IsTerm
