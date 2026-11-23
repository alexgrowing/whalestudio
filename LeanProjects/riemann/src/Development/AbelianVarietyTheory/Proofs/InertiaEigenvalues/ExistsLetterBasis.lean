import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NBasisLoc
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.WachLettersFree
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.LettersFreeOfRank

noncomputable section

namespace GlobalTheory.NL.LetterFree

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem letE_mul (i : ZMod n) (a : LetA O n) : (letE i : LetA O n) * a = Pi.single i (a i) := by
  funext j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, h]

theorem single_mul_letE (i : ZMod n) (a : PowerSeries O) :
    (Pi.single i a : LetA O n) * letE i = Pi.single i a := by
  funext j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, h]

theorem letE_mul_self (i : ZMod n) : (letE i : LetA O n) * letE i = letE i :=
  single_mul_letE i 1

theorem letE_mul_ne {i j : ZMod n} (h : i ≠ j) : (letE i : LetA O n) * letE j = 0 := by
  rw [letE_mul]
  simp [letE, h]

theorem sum_letE [NeZero n] : ∑ i : ZMod n, (letE i : LetA O n) = 1 := by
  funext j
  simp [letE, Finset.sum_apply, Pi.single_apply]

theorem sum_letE_smul [NeZero n] (x : W.DD T) : ∑ i : ZMod n, (letE i : LetA O n) • x = x := by
  rw [← Finset.sum_smul, sum_letE, one_smul]

theorem mem_Nl_iff (i : ZMod n) (x : W.DD T) :
    x ∈ W.Nl T i ↔ x ∈ W.N T ∧ (letE i : LetA O n) • x = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(W.N T).smul_mem _ hy, ?_⟩
    change (letE i : LetA O n) • (letE i : LetA O n) • y = (letE i : LetA O n) • y
    rw [smul_smul, letE_mul_self]
  · rintro ⟨hx, he⟩
    exact ⟨x, hx, he⟩

theorem lettersDecompose [NeZero n] : GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.LettersDecompose W T := by
  refine ⟨?_, le_antisymm (iSup_le fun i x hx => ((mem_Nl_iff W T i x).1 hx).1) fun x hx => ?_⟩
  · intro i
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have hk : (⨆ (j) (_ : j ≠ i), W.Nl T j) ≤
        LinearMap.ker (LinearMap.lsmul (LetA O n) (W.DD T) (letE i)) := by
      refine iSup_le fun j => iSup_le fun hj y hy => ?_
      rw [LinearMap.mem_ker, LinearMap.lsmul_apply, ← ((mem_Nl_iff W T j y).1 hy).2, smul_smul,
        letE_mul_ne hj.symm, zero_smul]
    have h0 := hk hx'
    rw [LinearMap.mem_ker, LinearMap.lsmul_apply, ((mem_Nl_iff W T i x).1 hx).2] at h0
    exact h0
  · rw [← sum_letE_smul W T x]
    exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨x, hx, rfl⟩

theorem isLetterBasis {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (i : ZMod n) :
    GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness.IsLetterBasis W T i (fun k => (letE i : LetA O n) • (b k : W.DD T)) := by
  have hli : LinearIndependent (LetA O n) (fun k => (b k : W.DD T)) :=
    b.linearIndependent.map' (W.N T).subtype (W.N T).ker_subtype
  refine ⟨fun k => ⟨b k, (b k).2, rfl⟩, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  have hy' : y = ∑ k, b.repr ⟨y, hy⟩ k • (b k : W.DD T) := by
    have := congrArg Subtype.val (b.sum_repr ⟨y, hy⟩)
    rw [AddSubmonoidClass.coe_finsetSum] at this
    exact this.symm
  generalize b.repr ⟨y, hy⟩ = a at hy'
  subst hy'
  have key : (letE i : LetA O n) • (∑ k, a k • (b k : W.DD T)) =
      ∑ k, (Pi.single i (a k i) : LetA O n) • (b k : W.DD T) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [smul_smul, letE_mul]
  refine ⟨fun k => a k i, ?_, fun c hc => ?_⟩
  · change (letE i : LetA O n) • (∑ k, a k • (b k : W.DD T)) = _
    rw [key]
    exact Finset.sum_congr rfl fun k _ => by rw [smul_smul, single_mul_letE]
  · change (letE i : LetA O n) • (∑ k, a k • (b k : W.DD T)) = _ at hc
    rw [key] at hc
    simp only [smul_smul, single_mul_letE] at hc
    funext k
    have h0 := Fintype.linearIndependent_iff.1 hli
      (fun k => (Pi.single i (c k) : LetA O n) - Pi.single i (a k i))
      (by simp only [sub_smul, Finset.sum_sub_distrib, hc, sub_self]) k
    have h1 := congrFun h0 i
    simpa [sub_eq_zero] using h1

attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.letterModule

theorem exists_letter_basis {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (i : ZMod n) :
    ∃ c : Module.Basis (Fin r) (PowerSeries O) ↥(W.Nl T i),
      ∀ k, (c k : W.DD T) = (letE i : LetA O n) • (b k : W.DD T) := by
  obtain ⟨hm, hu⟩ := isLetterBasis W T b i
  let f : Fin r → ↥(W.Nl T i) := fun k => ⟨_, hm k⟩
  have hs : ∀ c : Fin r → PowerSeries O, ((∑ k, c k • f k : ↥(W.Nl T i)) : W.DD T) =
      ∑ k, (Pi.single i (c k) : LetA O n) • (letE i : LetA O n) • (b k : W.DD T) := by
    intro c
    rw [AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun k _ => GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.letter_smul W T i (c k) (f k)
  have hli : LinearIndependent (PowerSeries O) f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have h1 := hs c
    rw [hc] at h1
    have h2 := (hu 0 (Submodule.zero_mem _)).unique h1 (y₂ := fun _ => 0) (by simp)
    exact congrFun h2 k
  have hsp : ⊤ ≤ Submodule.span (PowerSeries O) (Set.range f) := by
    intro x _
    obtain ⟨c, hc, -⟩ := hu x.1 x.2
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨c, Subtype.ext ((hs c).trans hc.symm)⟩
  exact ⟨Module.Basis.mk hli hsp, fun k => by rw [Module.Basis.mk_apply]⟩

end Generic

theorem letters_loc {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ) :
    GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.LettersDecompose (H.W K s LL h) T ∧ GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.LettersFree (H.W K s LL h) T ∧
      ∀ i, ∃ b : Fin (Module.finrank ↥(OL LL) ↥T.L.T) → (H.W K s LL h).DD T,
        GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness.IsLetterBasis (H.W K s LL h) T i b := by
  haveI := (P.PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨b⟩ := N_basis_loc H K s LL h T hT
  exact ⟨lettersDecompose _ T, fun i => ⟨(exists_letter_basis _ T b i).choose⟩,
    fun i => ⟨_, isLetterBasis _ T b i⟩⟩

end GlobalTheory.NL.LetterFree
