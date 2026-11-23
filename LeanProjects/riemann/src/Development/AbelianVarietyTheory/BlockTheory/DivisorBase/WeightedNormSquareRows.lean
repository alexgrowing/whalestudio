import Mathlib
import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement
import Formalism.LocalToGlobal.Divisibility.Numbers
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Columns.ToHLat
import Formalism.LocalToGlobal.Columns.RowFormsLemmas

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors

open Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV

def normSqAt {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (h : S.Ok) (s : K →+* ℂ) (φ : S.D → S.V) : ℝ :=
  (S.ipAt h (InfinitePlace.mk s) φ φ).re

section Comparison₂

variable {X : Fields} {Word : Type} (Nd : NumDatum) (W : Wts X Word Nd.R)

structure NumTie (pl : X.Tau ≃ RPl Nd.R) : Prop where
  tops : ∀ τ, τ ∈ W.tops ↔ (pl τ).1 = false ∧ (pl τ).2 ∈ Nd.TT
  row : ∀ τ, W.row τ = RowPar.of (Nd.hc (pl τ))
  u_first : ∀ u τ (h : 0 < Nd.R.k), (W.hc u τ).u ⟨0, h⟩ = (Nd.hc (pl τ)).u ⟨0, h⟩
  u_last : ∀ u τ (h : Nd.R.k - 1 < Nd.R.k), (W.hc u τ).u ⟨Nd.R.k - 1, h⟩ = (Nd.hc (pl τ)).u ⟨Nd.R.k - 1, h⟩

structure WtRows (u : Word) (T : ℕ) : Prop where
  cloud : ∀ τ (i : Fin (Nd.R.k - 1)), 0 ≤ (((W.hc u τ).v i : ℚ) : ℝ) ∧ (((W.hc u τ).v i : ℚ) : ℝ) ≤ Nd.Sc
  nodes : ∀ τ (i j : Fin Nd.R.m), |(((W.hc u τ).b i - (W.hc u τ).e j : ℚ) : ℝ)| ≤ Nd.eta
  top_bottom : ∀ τ ∈ W.tops, ∀ h : Nd.R.k - 1 < Nd.R.k,
    ((-(W.hc u τ).u ⟨Nd.R.k - 1, h⟩ - ((Nd.R.k : ℚ) - 1) / 2 : ℚ) : ℝ) ≤ 2 * Nd.sc.b'
  off_last : ∀ τ ∉ W.tops, ∀ (h : Nd.R.k - 1 < Nd.R.k) (h' : Nd.R.k - 2 < Nd.R.k - 1),
    (W.hc u τ).u ⟨Nd.R.k - 1, h⟩ = (W.hc u τ).v ⟨Nd.R.k - 2, h'⟩ - 1 / 2
  off_first : ∀ τ ∉ W.tops, ∀ (h : 0 < Nd.R.k) (h' : 0 < Nd.R.k - 1),
    Nd.Sc ≤ (((W.hc u τ).u ⟨0, h⟩ - (W.hc u τ).v ⟨0, h'⟩ : ℚ) : ℝ) ∧ (((W.hc u τ).u ⟨0, h⟩ : ℚ) : ℝ) ≤ 3 * Nd.Sc
  spread : ∀ τ, (((W.lamTrue u Nd.R.m τ).spread : ℤ) : ℝ) ≤ 2 * Nd.sc.a
  level : 2 * Nd.sc.a < (T : ℝ)

end Comparison₂

section Ev

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ)

theorem mem_of_mem_divs {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {P : HeightOneSpectrum A} (h : P ∈ divs a) :
    a ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hf
  · simpa using h
  · simp at h

theorem evOk (hX : X.Ok) (hPr : Pr.Ok) (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word) :
    (evGSD W Ch sel (mu0 X.F X.E X.K Sg) P u).Ok := by
  have hM := mtildeOk W Ch sel (mu0 X.F X.E X.K Sg) hX P
  have hC := colVal_eqv W hX u R.m (Pr.vT u) (rowSG Pr sel (mu0 X.F X.E X.K Sg))
  have hT : ∀ Q : Pr.vT u, cO X.E (Pr.piT u) ∉ Q.1.asIdeal := by
    intro Q hQ
    have h1 : Pr.piT u ∈ Q.1.asIdeal := mem_of_mem_divs Q.2
    have h2 : X.conjO (Pr.piT u) ∈ Q.1.asIdeal := hQ
    obtain ⟨a, b, hab⟩ := hPr.piT_cop u
    exact Q.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)))
  have hG : ∀ w : rowSG Pr sel (mu0 X.F X.E X.K Sg), Pr.piT u ∉ w.1.asIdeal := by
    classical
    intro w hw
    have hw1 : w.1 ∈ Pr.vGs := by
      rcases Finset.mem_union.mp w.2 with h | h
      · exact h
      · rw [twistPrimes_trivialTuple_empty] at h
        simp at h
    have hg : ∃ i, ((Pr.g i : ℕ) : 𝓞 X.E) ∈ w.1.asIdeal := by
      rcases Finset.mem_union.mp hw1 with h | h
      · exact ⟨0, hPr.piG_norm 0 ▸ Ideal.mul_mem_left _ _ (mem_of_mem_divs h)⟩
      · exact ⟨1, hPr.piG_norm 1 ▸ Ideal.mul_mem_left _ _ (mem_of_mem_divs h)⟩
    have hgg : ((Pr.cond * (Pr.g 0 * Pr.g 1) ^ 2 : ℕ) : 𝓞 X.E) ∈ w.1.asIdeal := by
      push_cast
      refine Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ ?_ 2 two_pos)
      obtain ⟨i, hi⟩ := hg
      fin_cases i
      · exact Ideal.mul_mem_right _ _ hi
      · exact Ideal.mul_mem_left _ _ hi
    obtain ⟨c, hc⟩ := hPr.piT_cong u
    have h1 : Pr.piT u - 1 ∈ w.1.asIdeal := hc ▸ Ideal.mul_mem_right _ _ hgg
    exact w.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem hw h1))
  have hroot : ∀ g : FormG (rowTy Ch sel (mu0 X.F X.E X.K Sg) P).inv, ∃ m : ℕ, 0 < m ∧
      ((((rowTy Ch sel (mu0 X.F X.E X.K Sg) P).inv.chr g.2)⁻¹ : X.Kˣ) : X.K) ^ m = 1 := by
    intro g
    obtain ⟨m, hm, hc⟩ := (rowTy Ch sel (mu0 X.F X.E X.K Sg) P).inv.chr_root g.2
    exact ⟨m, hm, by rw [Units.val_inv_eq_inv_val, inv_pow, hc, inv_one]⟩
  refine ⟨hM.fin_orb, hM.fin_stab, ?_, ?_, ?_⟩
  · intro g d
    obtain ⟨m, hm, hc⟩ := hroot g
    have h1 := DecoSet.tilH_smul (N_m_succ R) (ST := Pr.vT u) (FormG.incl _ g) d hT hG
    exact (congrArg _ h1).trans ((hC.nab_smul _ _).trans (map_root_smul _ _ hm hc).symm)
  · intro g d
    obtain ⟨m, hm, hc⟩ := hroot g
    have h1 := DecoSet.tilH_smul (N_m_succ R) (ST := Pr.vT u) (FormG.incl _ g) d hT hG
    exact (congrArg _ h1).trans ((hC.del_smul _ _).trans (map_root_smul _ _ hm hc).symm)
  · intro g x y
    obtain ⟨m, hm, hc⟩ := hroot g
    show (colVal W u R.m (Pr.vT u) (rowSG Pr sel (mu0 X.F X.E X.K Sg))).pair
      (((((rowTy Ch sel (mu0 X.F X.E X.K Sg) P).inv.chr g.2)⁻¹ : X.Kˣ) : X.K) • _)
      (((((rowTy Ch sel (mu0 X.F X.E X.K Sg) P).inv.chr g.2)⁻¹ : X.Kˣ) : X.K) • _) =
      (colVal W u R.m (Pr.vT u) (rowSG Pr sel (mu0 X.F X.E X.K Sg))).pair x y
    rw [LinearMap.map_smulₛₗ₂, map_smul, hC.inv, smul_smul]
    show (star _ * _) • _ = _
    rw [star_mul_root hX.conjK hm hc, one_smul]

def PeriodBound (hX : X.Ok) (hPr : Pr.Ok) (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word) (A : ℝ) : Prop :=
  ∀ (s : X.K →+* ℂ) (ψ : (evGSD W Ch sel (mu0 X.F X.E X.K Sg) P u).EqFun) (F : MtildeV W Ch sel (mu0 X.F X.E X.K Sg) P),
    ‖s (PtilE W Ch sel (mu0 X.F X.E X.K Sg) P (mtildeOk W Ch sel (mu0 X.F X.E X.K Sg) hX P) u ψ F)‖ ^ 2 ≤
      Real.exp A *
        normSqAt (evGSD W Ch sel (mu0 X.F X.E X.K Sg) P u) (evOk W Ch sel Sg hX hPr P u) s ψ *
        normSqAt (mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P) (mtildeOk W Ch sel (mu0 X.F X.E X.K Sg) hX P) s F

end Ev

def LastMapBoundWith (CT C : ℝ) : Prop :=
  ∀ (Nd : NumDatum) (X : Fields) (hX : X.Ok) (Pr : Primes X) (hPr : Pr.Ok) (W : Wts X Pr.Word Nd.R) (_ : W.Ok)
    (Ch : Chars X Pr Nd.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ)
    (pl : X.Tau ≃ RPl Nd.R) (_ : NumTie Nd W pl) (u : Pr.Word) (_ : WtRows Nd W u (Pr.T u))
    (_ : Real.log (Pr.T u : ℝ) ≤ CT * (Nd.R.m : ℝ) * Nd.sc.L) (P : LevFam X.E X.K Nd.R.r Pr.vGs),
    PeriodBound W Ch sel Sg hX hPr P u (Nd.hA C (Pr.T u))

def LastMapBound : Prop :=
  ∀ CT : ℝ, ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ C, C₀ ≤ C → LastMapBoundWith CT C

theorem card_eq_f (Nd : NumDatum) (X : Fields) (pl : X.Tau ≃ RPl Nd.R) : X.f = Nd.R.f := by
  unfold Fields.f Ranks.f Ranks.n
  rw [Fintype.card_congr pl, Fintype.card_prod, Fintype.card_bool, Formalism.HC.Frame.card_A]

def wtsOfNum (Nd : NumDatum) (X : Fields) (Word : Type) (pl : X.Tau ≃ RPl Nd.R) : Wts X Word Nd.R where
  row τ := RowPar.of (Nd.hc (pl τ))
  hc _ τ := Nd.hc (pl τ)
  tops := Finset.univ.filter fun τ => (pl τ).1 = false ∧ (pl τ).2 ∈ Nd.TT

end GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors

end
