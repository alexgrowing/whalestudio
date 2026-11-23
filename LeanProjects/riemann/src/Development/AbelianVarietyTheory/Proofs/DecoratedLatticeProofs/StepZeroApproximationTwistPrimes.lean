import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartsReadingStepZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsK1PointCongruent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotTopPtOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartFromAdelicDictionary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepLevelContainsUnitaryNearOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ApproxZero

section Support
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem exists_K1_element_local_support : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))), (∀ P ∈ Q, P ∉ ST ∧ P ∉ SG ∧ conjPrime₂ P ∉ ST ∧ conjPrime₂ P ∉ SG ∧ conjPrime₂ P ∉ Q) → ∀ (g : GL (Fin n) (AfE F E)), g ∈ UAd hc n → ∀ c : ℕ, ∃ z ∈ K1 hc n ST SG, (∀ P : Q, Sm Valued.v (dep P.1 c) (locM P.1 z - 1)) ∧ (∀ w, w ∉ Q → conjPrime₂ w ∉ Q → locM w z = 1) ∧ ∃ p : DecoF E n ST SG Q, IsPtOf hc (g * z) p := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q hQ g hg c
  classical
  have hcc : ∀ P : HeightOneSpectrum (𝓞 E), conjPrime₂ (conjPrime₂ P) = P := fun P => by
    ext b
    rw [mem_conjP, mem_conjP, cO_cO]
  obtain ⟨p, hp⟩ := exists_near (ST := ST) (SG := SG) (Q := Q) hc c hg
  have hN : Formalism.UG.CS.globLat g (Formalism.L2.Col.stdLat E n) = p.deco.1.N := congrArg Deco.N hp.deco
  obtain ⟨g', hg', c1, c2, c3⟩ := PtExist.exists_modify (fun P hP => (hQ P hP).2.2.2.2) hg (ptFr p)
    fun P _ => hN ▸ isFr_ptFr p P
  have hoff : ∀ P, P ∈ ST ∨ P ∈ SG → P ∉ Q ∧ conjPrime₂ P ∉ Q := fun P hP => by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases hP with hP | hP
      · exact (hQ P h).1 hP
      · exact (hQ P h).2.1 hP
    · have := hQ _ h
      rw [hcc] at this
      rcases hP with hP | hP
      · exact this.2.2.1 hP
      · exact this.2.2.2.1 hP
  have hpt : IsPtOf hc g' p := by
    refine ⟨hg', hN ▸ c1, fun P v hv i hi => ?_, fun P v hv i => ?_, fun P i j => ?_⟩
    · have e : lastIdx n = i := Fin.ext (by simp [lastIdx]; omega)
      rw [← hN] at hv
      have ho := hoff P.1 (Or.inl P.2)
      rw [c3 _ ho.1 ho.2, ← hp.deco]
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hv), e]
      exact PtExist.hasRes_redA _ ((mem_globLat g v).1 hv i)
    · rw [← hN] at hv
      have ho := hoff P.1 (Or.inr P.2)
      rw [c3 _ ho.1 ho.2, ← hp.deco]
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hv)]
      exact PtExist.hasRes_redA _ ((mem_globLat g v).1 hv i)
    · rw [c2 _ P.2, ptFr_of_mem p (hQ P.1 P.2).2.1 P.2]
      rfl
  have hd : decoRaw ST SG g = decoRaw ST SG g' := hp.deco.trans (near_of_isPtOf hpt c).deco.symm
  refine ⟨g⁻¹ * g', mem_principal_of_same_decoration hc n ST SG hg hg' hd, fun P => ?_, fun w h1 h2 => ?_, p, by rwa [mul_inv_cancel_left]⟩
  · have e : locM P.1 g' = ratM P.1 (p.fr P) := Matrix.ext fun i j => hpt.fr P i j
    rw [locM_mul, e]
    exact hp.fr P
  · have hinv : locM w g'⁻¹ = locM w g⁻¹ := by
      refine Matrix.ext fun i j => ?_
      have := c3 w h1 h2 (Pi.single j 1) i
      simpa [GlobalTheory.Mem.Col2.pullV, Formalism.L2.Col.pullV, Matrix.mulVec, dotProduct, Pi.single_apply, locM] using this
    have hz : locM w (g⁻¹ * g')⁻¹ = 1 := by
      rw [_root_.mul_inv_rev, inv_inv, locM_mul, hinv, ← locM_mul, inv_mul_cancel, locM_one]
    calc locM w (g⁻¹ * g') = locM w (g⁻¹ * g') * locM w (g⁻¹ * g')⁻¹ := by rw [hz, Matrix.mul_one]
      _ = 1 := by rw [← locM_mul, mul_inv_cancel, locM_one]

end Support

section Conj
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem conj_small {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {hc : CMData F E}
    {n : ℕ} {z : GL (Fin n) (AfE F E)} (hz : z ∈ UAd hc n) {P : HeightOneSpectrum (𝓞 E)} {γ : WithZero (Multiplicative ℤ)}
    (h : Sm Valued.v γ (locM P z⁻¹ - 1)) : Sm Valued.v γ (locM (conjPrime₂ P) z - 1) := by
  classical
  intro i j
  have hcc : conjPrime₂ (conjPrime₂ P) = P := by
    ext b
    rw [mem_conjP, mem_conjP, cO_cO]
  have e := PtExist.inv_apply (inv_mem hz) i j
  rw [inv_inv] at e
  have h1 := h j i
  have e1 : (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j =
      Formalism.UG.sigR (CMData.sig hc) (FiniteAdeleRing (𝓞 F) F) ((1 : Matrix (Fin n) (Fin n) (AfE F E)) j i) := by
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij, if_neg (Ne.symm hij), map_zero]
  have key : (locM (conjPrime₂ P) z - 1) i j = adAt F (conjPrime₂ P) (Formalism.UG.sigR (CMData.sig hc) (FiniteAdeleRing (𝓞 F) F)
      (((z⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) j i - (1 : Matrix (Fin n) (Fin n) (AfE F E)) j i)) := by
    rw [map_sub, ← e, ← e1, map_sub, Matrix.sub_apply]
    simp [locM, Matrix.one_apply]
  have key2 : (locM P z⁻¹ - 1) j i = adAt F P
      (((z⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) j i - (1 : Matrix (Fin n) (Fin n) (AfE F E)) j i) := by
    rw [map_sub, Matrix.sub_apply]
    simp [locM, Matrix.one_apply]
  rw [key, valued_sigR, hcc]
  rw [key2] at h1
  exact h1

end Conj

section Small
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem val_lt_one_le {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le'
  · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega

theorem dep_le {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (d : ℕ) :
    dep P d ≤ WithZero.exp (-(d : ℤ)) := by
  unfold dep
  rw [map_pow]
  calc _ ≤ (WithZero.exp (-1 : ℤ)) ^ d := pow_le_pow_left₀ zero_le' (val_lt_one_le val_qOf_lt) d
    _ = WithZero.exp (-(d : ℤ)) := by
      rw [← WithZero.exp_nsmul]
      congr 1
      simp

theorem mem_unitaryAdelic_of_mem_principalCongruence {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {hc : CMData F E}
    {n : ℕ} [NeZero n] {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {z : GL (Fin n) (AfE F E)} (hz : z ∈ K1 hc n ST SG) :
    z ∈ UAd hc n := by
  obtain ⟨⟨z', hz'⟩, -, rfl⟩ := hz
  exact hz'.1.1

theorem small_pair {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {hc : CMData F E}
    {n : ℕ} [NeZero n] {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {z : GL (Fin n) (AfE F E)} (hz : z ∈ K1 hc n ST SG)
    {P : HeightOneSpectrum (𝓞 E)} {d : ℕ} (h : Sm Valued.v (dep P d) (locM P z - 1)) :
    (Sm Valued.v (WithZero.exp (-(d : ℤ))) (locM P z - 1) ∧ Sm Valued.v (WithZero.exp (-(d : ℤ))) (locM P z⁻¹ - 1)) ∧
      (Sm Valued.v (WithZero.exp (-(d : ℤ))) (locM (conjPrime₂ P) z - 1) ∧
        Sm Valued.v (WithZero.exp (-(d : ℤ))) (locM (conjPrime₂ P) z⁻¹ - 1)) := by
  have hzU := mem_unitaryAdelic_of_mem_principalCongruence hz
  have hle := dep_le P d
  have hi : Sm Valued.v (dep P d) (locM P z⁻¹ - 1) := by
    have h0 : Sm Valued.v 1 (locM P z⁻¹) := fun i j => valuation_entries_le_one_of_mem_levelGroupOne (inv_mem hz) P i j
    have h1 := h0.mul h
    have e : locM P z⁻¹ * (locM P z - 1) = -(locM P z⁻¹ - 1) := by
      rw [Matrix.mul_sub, ← locM_mul, inv_mul_cancel, locM_one, Matrix.mul_one]
      abel
    rw [e, one_mul] at h1
    intro i j
    have := h1 i j
    rwa [Matrix.neg_apply, Valuation.map_neg] at this
  have h' : Sm Valued.v (dep P d) (locM P z⁻¹⁻¹ - 1) := by rw [inv_inv]; exact h
  refine ⟨⟨fun i j => (h i j).trans hle, fun i j => (hi i j).trans hle⟩, fun i j => (conj_small hzU hi i j).trans hle,
    fun i j => (conj_small (inv_mem hzU) h' i j).trans hle⟩

theorem comm_of_support {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
    (Q : Finset (HeightOneSpectrum (𝓞 E))) {k z : GL (Fin n) (AfE F E)}
    (hk : ∀ w, w ∈ Q ∨ conjPrime₂ w ∈ Q → locM w k = 1) (hz : ∀ w, w ∉ Q → conjPrime₂ w ∉ Q → locM w z = 1) : z * k = k * z := by
  refine Units.ext (Matrix.ext fun i j => PtExist.ad_ext fun w => ?_)
  show locM w (z * k) i j = locM w (k * z) i j
  rw [locM_mul, locM_mul]
  by_cases h : w ∈ Q ∨ conjPrime₂ w ∈ Q
  · rw [hk w h, Matrix.one_mul, Matrix.mul_one]
  · rw [not_or] at h
    rw [hz w h.1 h.2, Matrix.one_mul, Matrix.mul_one]

end Small

set_option maxHeartbeats 800000 in

theorem approx_zero : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ (c : {c // A.chOf 0 c = β}) (x : TC.GA B (B.R.N 0)), x ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) → ∃ h : TC.GA B (B.R.N 0), h ∈ (A.K 0 (Nat.zero_le _) β).lev.U ∧ h ∈ Formalism.L2.Col.levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (Formalism.L2.Col.colLev I.Ch 0).grp ∧ ∃ q : Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0, TC.PtOf ((show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) β).y c).1) * (x * h) * TC.kStd X u (B.R.N 0)) q := by
  intro B X I hI hP l Z u a Ch A hA β hβ c x hx
  obtain ⟨c, rfl⟩ := c
  have hR := hA.reads 0 (Nat.zero_le _)
  have hpt := hR.pt c
  rw [hβ] at hpt
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  have hks := GlobalTheory.Mem.Col2.MemChart.kStd_spec hPr u (B.R.N 0)
  obtain ⟨p0, hp0, -⟩ := hks.1
  have hTw := (GlobalTheory.Mem.Col2.TwistPrimes.twist_primes_away I hI).2 u a
  have hsp := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 0 (Nat.zero_le _)
  have hcc : ∀ P : HeightOneSpectrum (𝓞 B.host.E), Formalism.L2.Col.conjPrime₂ (Formalism.L2.Col.conjPrime₂ P) = P := fun P => by
    ext b
    rw [Formalism.L2.Col.mem_conjP, Formalism.L2.Col.mem_conjP, Formalism.L2.Col.cO_cO]
  have hkT : ∀ w : HeightOneSpectrum (𝓞 B.host.E), w ∈ I.Q a ∨ Formalism.L2.Col.conjPrime₂ w ∈ I.Q a →
      GlobalTheory.Mem.ColAd.locM w (TC.kStd X u (B.R.N 0)) = 1 := by
    intro w hw
    have hT : (B.T u : 𝓞 B.host.F) ∉ (w.under (𝓞 B.host.F)).asIdeal := by
      rcases hw with hw | hw
      · exact (hTw w hw).2.2
      · have e : (Formalism.L2.Col.conjPrime₂ w).under (𝓞 B.host.F) = w.under (𝓞 B.host.F) :=
          (GlobalTheory.Mem.Col2.under_eq_iff B.host w _).2 (Or.inr rfl)
        have := (hTw _ hw).2.2
        rwa [e] at this
    exact GlobalTheory.Mem.Col2.TopPtModel.adAt_of_prV w (hks.2.1 _ hT)
  obtain ⟨d, hd⟩ := GlobalTheory.T.stepLevel_contains_unitary_near_one (A.K 0 (Nat.zero_le _) (A.chOf 0 c)).lev (I.Q a ∪ (I.Q a).image Formalism.L2.Col.conjPrime₂)
  generalize TC.kStd X u (B.R.N 0) = k at hpt hks hp0 hkT ⊢
  have hkU : k ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := hp0.1
  have hykU : (show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) * k ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := hpt.1
  have hyU : (show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := by
    have := mul_mem hykU (inv_mem hkU)
    rwa [mul_inv_cancel_right] at this
  have hg : (show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) * x * k ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := mul_mem (mul_mem hyU hx) hkU
  obtain ⟨z, hz, hsm, hsupp, p, hp⟩ := exists_K1_element_local_support _ _ B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs
    (I.Q a) (fun P hP => (hTw P hP).1) ((show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) * x * k) hg d
  have hzU : z ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := mem_unitaryAdelic_of_mem_principalCongruence hz
  have hcomm : z * k = k * z := comm_of_support (I.Q a) hkT hsupp
  refine ⟨z, hd z ?_ ?_ ?_, Formalism.L2.Col.kOne_le_unipotentLevel _ _ _ _ _ hz, p, ?_⟩
  · rw [hsp.1]
    exact hzU
  · intro w hw
    exact hsupp w (fun h => hw (Finset.mem_union_left _ h))
      (fun h => hw (Finset.mem_union_right _ (Finset.mem_image.2 ⟨_, h, hcc w⟩)))
  · intro w hw
    rcases Finset.mem_union.1 hw with hw | hw
    · exact (small_pair hz (hsm ⟨w, hw⟩)).1
    · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hw
      exact (small_pair hz (hsm ⟨P, hP⟩)).2
  · have e : (show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) * (x * z) * k = (show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) * x * k * z :=
      (mul_assoc (show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) (x * z) k).trans ((congrArg ((show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) * ·) ((mul_assoc x z k).trans ((congrArg (x * ·) hcomm).trans
        (mul_assoc x k z).symm))).trans ((mul_assoc (show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) (x * k) z).symm.trans (congrArg (· * z) (mul_assoc (show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) x k).symm)))
    show TC.PtOf ((show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) * (x * z) * k) p
    rw [e]
    exact hp

end GlobalTheory.ApproxZero

end
