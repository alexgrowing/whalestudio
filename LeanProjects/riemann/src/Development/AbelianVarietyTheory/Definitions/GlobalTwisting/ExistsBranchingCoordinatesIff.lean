import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelChainSharpColumnValuationOwnChainIff

noncomputable section

namespace GlobalTheory.LvT

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

variable {D : D7} {u : D.what₂.Word}

structure Pend (X : Ch D u) where

  br : D.what₂.Tau → (MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ →ₗ[ℂ]
    MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ)

  coM : D.what₂.places.Pl → X.fm.clsP → ((X.C.Y D.R.m → ℂ) →ₗ[ℂ]
    MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ)

  coP : D.what₂.places.Pl → (X.P.Wrow →ₗ[ℂ] (X.fm.clsP →
    MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ))

  coM_mem : ∀ w c, ∀ φ ∈ X.fm.Fi D.R.m, coM w c (φ (X.fm.til c)) ∈ CSpan (X.fm.lam D.R.m)

  coM_inj : ∀ w c, ∀ φ ∈ X.fm.Fi D.R.m, coM w c (φ (X.fm.til c)) = 0 → φ (X.fm.til c) = 0

  coP_mem : ∀ w, ∀ z ∈ X.fm.ptC, ∀ c, coP w z c ∈ CSpan X.fm.sg

  coP_inj : ∀ w, ∀ z ∈ X.fm.ptC, coP w z = 0 → z = 0

  Pt_eq : ∀ w, ∀ φ ∈ X.fm.Fi D.R.m, ∀ c,
    coP w (Pt X φ) c = blk (fun τ => br τ) (coM w c (φ (X.fm.til c)))

  lat_co : ∀ w, ∀ x ∈ X.fm.S D.R.m w, ∀ c,
    coM w c (X.fm.emb D.R.m x (X.fm.til c)) ∈ IntSpan D w (X.fm.lam D.R.m)

  pt_co : ∀ w, ∀ z ∈ X.fm.ptC, (∃ y ∈ X.fm.SP w, X.fm.ptEmb y = z) ↔ ∀ c, coP w z c ∈ IntSpan D w X.fm.sg

  gP : D.what₂.places.Pl → X.fm.clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ

  ipV_co : ∀ w c, ∀ φ ∈ X.fm.Fi D.R.m, (X.fm.ipV D.R.m (X.fm.til c) (φ (X.fm.til c)) (φ (X.fm.til c))).re =
    (nfAll (X.fm.lam D.R.m)
      (blk (fun τ => sqAct ℂ _ (lamTr X τ) (gFull X (gP w c τ))) (coM w c (φ (X.fm.til c))))
      (blk (fun τ => sqAct ℂ _ (lamTr X τ) (gFull X (gP w c τ))) (coM w c (φ (X.fm.til c))))).re

  re_petersson_self_eq_sum_coord : ∀ w, ∀ z ∈ X.fm.ptC, (X.fm.ipP z z).re = ∑ c, ((Nat.card (X.fm.stabilizer₂ c) : ℝ))⁻¹ *
    (nfAll X.fm.sg (blk (fun τ => sqAct ℂ _ (sgTr X τ) (gP w c τ)) (coP w z c))
      (blk (fun τ => sqAct ℂ _ (sgTr X τ) (gP w c τ)) (coP w z c))).re

  beOn_eq : ∀ τ, X.fm.beOn τ = opNorm X τ (br τ)

  interlace : X.fm.SgInterlace

variable {X : Ch D u}

def ArchimedeanSignatureMatching (P : Pend X) : Prop :=
  ∀ τ, Formalism.MainNotions.PrimeDegreeVariant.IsBr (Nm_succ D.R) (lamTr X τ) (sgTr X τ) (P.br τ)

def Pend.ofRecord (P : Formalism.MainNotions.product_first_zeroth_parts.Pend D u) : Pend (own D u) :=
  ⟨P.br, P.coM, P.coP, P.coM_mem, P.coM_inj, P.coP_mem, P.coP_inj, P.Pt_eq, P.lat_co, P.pt_co, P.gP, P.ipV_co,
    P.re_petersson_self_eq_sum_coord, P.beOn_eq, P.interlace⟩

def Pend.toRecord (P : Pend (own D u)) : Formalism.MainNotions.product_first_zeroth_parts.Pend D u :=
  ⟨P.br, P.coM, P.coP, P.coM_mem, P.coM_inj, P.coP_mem, P.coP_inj, P.Pt_eq, P.lat_co, P.pt_co, P.gP, P.ipV_co,
    P.re_petersson_self_eq_sum_coord, P.beOn_eq, P.interlace⟩

def Pend.equivRecord (D : D7) (u : D.what₂.Word) : Formalism.MainNotions.product_first_zeroth_parts.Pend D u ≃ Pend (own D u) :=
  ⟨Pend.ofRecord, Pend.toRecord, fun _ => rfl, fun _ => rfl⟩

theorem branchingLaw_ofRecord_iff (P : Formalism.MainNotions.product_first_zeroth_parts.Pend D u) : ArchimedeanSignatureMatching (Pend.ofRecord P) ↔ Formalism.MainNotions.product_first_zeroth_parts.ArchimedeanSignatureMatching P := Iff.rfl

theorem branchingCoordinates_iff (P : Pend (own D u)) : Formalism.MainNotions.product_first_zeroth_parts.ArchimedeanSignatureMatching P.toRecord ↔ ArchimedeanSignatureMatching P := Iff.rfl

theorem exists_branchingCoordinates_iff : (∃ P : Pend (own D u), ArchimedeanSignatureMatching P) ↔ ∃ P : Formalism.MainNotions.product_first_zeroth_parts.Pend D u, Formalism.MainNotions.product_first_zeroth_parts.ArchimedeanSignatureMatching P := by
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨P.toRecord, (branchingCoordinates_iff P).2 hP⟩
  · rintro ⟨P, hP⟩
    exact ⟨Pend.ofRecord P, (branchingLaw_ofRecord_iff P).2 hP⟩

theorem Pend.interlaceTr (P : Pend X) (τ : D.what₂.Tau) :
    Formalism.MainNotions.PrimeDegreeVariant.Interlace (Nm_succ D.R) (lamTr X τ) (sgTr X τ) := by
  have h := P.interlace
  unfold Formalism.BasicNotions.MemberForms.SgInterlace at h
  unfold Formalism.MainNotions.PrimeDegreeVariant.Interlace lamTr sgTr
  intro i
  obtain ⟨h1, h2⟩ := h τ i
  exact ⟨sub_le_sub_right h1 _, sub_le_sub_right h2 _⟩

theorem delSq_lamTr (X : Ch D u) (R : Type) [CommRing R] (τ : D.what₂.Tau) :
    delSq R _ (lamTr X τ) = delSq R _ (X.fm.lam D.R.m τ) := by
  unfold lamTr delSq
  rw [Formalism.MainNotions.product_first_zeroth_parts.natW_wSh]

theorem delSq_sgTr (X : Ch D u) (R : Type) [CommRing R] (τ : D.what₂.Tau) :
    delSq R _ (sgTr X τ) = delSq R _ (X.fm.sg τ) := by
  unfold sgTr delSq
  rw [Formalism.MainNotions.product_first_zeroth_parts.natW_wSh]

theorem normFock_wSh {n : ℕ} (l : DomWeight n) (c : ℤ) : normFock (wSh l c) = normFock l := by
  funext f g
  unfold normFock
  rw [Formalism.MainNotions.product_first_zeroth_parts.extremal_wSh]

theorem degZ_tr (X : Ch D u) (τ : D.what₂.Tau) : Formalism.MainNotions.PrimeDegreeVariant.degZ (lamTr X τ) (sgTr X τ) = X.fm.deg τ := by
  unfold Formalism.MainNotions.PrimeDegreeVariant.degZ lamTr sgTr
  unfold Formalism.BasicNotions.MemberForms.deg
  unfold Formalism.MainNotions.PrimeDegreeVariant.wsum wSh cTw
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hN := Nm_succ D.R
  have hc : ((D.R.N D.R.m - 1 : ℕ) : ℤ) = (D.R.N D.R.m : ℤ) - 1 := by omega
  rw [hc]
  ring

theorem fockF_self_eq {σ : Type} (f : MvPolynomial σ ℂ) : Formalism.REAL.fockF f f =
    ((∑ m ∈ f.support, Complex.normSq (f.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
  unfold Formalism.REAL.fockF
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hc : f.coeff m * star (f.coeff m) = ((Complex.normSq (f.coeff m) : ℝ) : ℂ) := Complex.mul_conj _
  rw [hc, Complex.ofReal_mul, Complex.ofReal_natCast]

theorem fockF_self_pos {σ : Type} {f : MvPolynomial σ ℂ} (hf : f ≠ 0) : 0 < (Formalism.REAL.fockF f f).re := by
  rw [fockF_self_eq, Complex.ofReal_re]
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hf
  refine Finset.sum_pos (fun n hn => ?_) ⟨m, MvPolynomial.mem_support_iff.mpr hm⟩
  have h1 : f.coeff n ≠ 0 := MvPolynomial.mem_support_iff.mp hn
  have h2 : 0 < Complex.normSq (f.coeff n) := Complex.normSq_pos.mpr h1
  have h3 : (0 : ℝ) < ((∏ k ∈ n.support, (n k).factorial : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun k _ => Nat.factorial_pos _)
  exact mul_pos h2 h3

private lemma extremal_ne_zero_global_twisting {n : ℕ} (l : DomWeight n) : extremal ℂ n l ≠ 0 := by
  intro h
  have h1 : MvPolynomial.eval (fun p : Fin n × Fin n => if p.1 = p.2 then (1 : ℂ) else 0) (extremal ℂ n l) = 1 := by
    unfold extremal Formalism.GradedWeylDivisibility.hw Formalism.GradedWeylDivisibility.lpMinor
    rw [map_prod]
    refine Finset.prod_eq_one fun s _ => ?_
    rw [map_pow, RingHom.map_det]
    have hI : ∀ M : Matrix (Fin (s.val + 1)) (Fin (s.val + 1)) ℂ, M = 1 → M.det = 1 := fun M hM => hM ▸ Matrix.det_one
    rw [hI _ (by ext p q; simp [Matrix.one_apply, Fin.castLE_inj]), one_pow]
  rw [h, map_zero] at h1
  exact zero_ne_one h1

theorem normFock_self_pos {n : ℕ} (l : DomWeight n) {f : MvPolynomial (Fin n × Fin n) ℂ} (hf : f ≠ 0) :
    0 < (normFock l f f).re := by
  have h1 := fockF_self_pos hf
  have h2 := fockF_self_pos (extremal_ne_zero_global_twisting l)
  rw [fockF_self_eq, Complex.ofReal_re] at h1
  rw [fockF_self_eq, Complex.ofReal_re] at h2
  unfold normFock
  rw [fockF_self_eq f, fockF_self_eq (extremal ℂ n l), ← Complex.ofReal_div, Complex.ofReal_re]
  exact div_pos h1 h2

theorem ArchimedeanSignatureMatching.quot_le {P : Pend X} (h : ArchimedeanSignatureMatching P) (τ : D.what₂.Tau)
    {f : MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ} (hf : f ∈ delSq ℂ _ (X.fm.lam D.R.m τ)) (h0 : f ≠ 0) :
    Real.sqrt ((normFock (X.fm.sg τ) (P.br τ f) (P.br τ f)).re / (normFock (X.fm.lam D.R.m τ) f f).re) ≤
      Formalism.MainNotions.PrimeDegreeVariant.brBd (Nm_succ D.R) (lamTr X τ) (sgTr X τ) := by
  have hb := normFock_self_pos (X.fm.lam D.R.m τ) h0
  have hf' : f ∈ delSq ℂ _ (lamTr X τ) := by rw [delSq_lamTr]; exact hf
  obtain ⟨-, -, -, -, -, hN⟩ := h τ
  have hB := hN f hf'
  have hB0 : 0 ≤ Formalism.MainNotions.PrimeDegreeVariant.brBd (Nm_succ D.R) (lamTr X τ) (sgTr X τ) := by
    unfold Formalism.MainNotions.PrimeDegreeVariant.brBd Formalism.MainNotions.PrimeDegreeVariant.cBd
    refine mul_nonneg (Real.rpow_nonneg ?_ _) (Real.sqrt_nonneg _)
    have hs : 0 ≤ DomWeight.spread (lamTr X τ) := by
      unfold DomWeight.spread
      split_ifs with hN
      · have hw := (lamTr X τ).anti
          (show (⟨0, hN⟩ : Fin (D.R.N D.R.m)) ≤ ⟨D.R.N D.R.m - 1, by omega⟩ from Fin.mk_le_mk.mpr (Nat.zero_le _))
        omega
      · exact le_rfl
    have h2 : (0 : ℤ) ≤ 2 * DomWeight.spread (lamTr X τ) := by omega
    exact_mod_cast h2
  simp only [lamTr, sgTr, normFock_wSh] at hB
  rw [Real.sqrt_le_iff]
  refine ⟨hB0, ?_⟩
  rw [div_le_iff₀ hb]
  exact hB

theorem ArchimedeanSignatureMatching.bddAbove {P : Pend X} (h : ArchimedeanSignatureMatching P) (τ : D.what₂.Tau) :
    BddAbove ((fun f => Real.sqrt ((normFock (X.fm.sg τ) (P.br τ f) (P.br τ f)).re /
      (normFock (X.fm.lam D.R.m τ) f f).re)) '' {f | f ∈ delSq ℂ _ (X.fm.lam D.R.m τ) ∧ f ≠ 0}) := by
  refine ⟨Formalism.MainNotions.PrimeDegreeVariant.brBd (Nm_succ D.R) (lamTr X τ) (sgTr X τ), ?_⟩
  rintro _ ⟨f, ⟨hf, h0⟩, rfl⟩
  exact h.quot_le τ hf h0

private lemma normFock_self_re_nonneg' {n : ℕ} (l : DomWeight n) (f : MvPolynomial (Fin n × Fin n) ℂ) :
    0 ≤ (normFock l f f).re := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp [normFock, Formalism.REAL.fockF]
  · exact (normFock_self_pos l hf).le

theorem ArchimedeanSignatureMatching.br_le {P : Pend X} (h : ArchimedeanSignatureMatching P) (τ : D.what₂.Tau)
    {f : MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ} (hf : f ∈ delSq ℂ _ (X.fm.lam D.R.m τ)) :
    (normFock (X.fm.sg τ) (P.br τ f) (P.br τ f)).re ≤ X.fm.beOn τ ^ 2 * (normFock (X.fm.lam D.R.m τ) f f).re := by
  rcases eq_or_ne f 0 with rfl | h0
  · simp [normFock, Formalism.REAL.fockF]
  have hb := normFock_self_pos (X.fm.lam D.R.m τ) h0
  have ha := normFock_self_re_nonneg' (X.fm.sg τ) (P.br τ f)
  have hle : Real.sqrt ((normFock (X.fm.sg τ) (P.br τ f) (P.br τ f)).re /
      (normFock (X.fm.lam D.R.m τ) f f).re) ≤ X.fm.beOn τ := by
    rw [P.beOn_eq τ]
    unfold opNorm
    exact le_csSup (h.bddAbove τ) ⟨f, ⟨hf, h0⟩, rfl⟩
  have hsq : (normFock (X.fm.sg τ) (P.br τ f) (P.br τ f)).re / (normFock (X.fm.lam D.R.m τ) f f).re ≤
      X.fm.beOn τ ^ 2 := by
    rw [← Real.sq_sqrt (div_nonneg ha hb.le)]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
  rwa [div_le_iff₀ hb] at hsq

theorem ArchimedeanSignatureMatching.beOn_pos {P : Pend X} (h : ArchimedeanSignatureMatching P) (τ : D.what₂.Tau) : 0 < X.fm.beOn τ := by
  obtain ⟨-, -, ⟨f, hf, hne⟩, -⟩ := h τ
  have hf' : f ∈ delSq ℂ _ (X.fm.lam D.R.m τ) := by rw [← delSq_lamTr X ℂ τ]; exact hf
  have h0 : f ≠ 0 := by
    rintro rfl
    exact hne (map_zero _)
  have ha := normFock_self_pos (X.fm.sg τ) hne
  have hb := normFock_self_pos (X.fm.lam D.R.m τ) h0
  rw [P.beOn_eq τ]
  unfold opNorm
  exact lt_of_lt_of_le (Real.sqrt_pos.mpr (div_pos ha hb)) (le_csSup (h.bddAbove τ) ⟨f, ⟨hf', h0⟩, rfl⟩)

theorem ArchimedeanSignatureMatching.beOn_le {P : Pend X} (h : ArchimedeanSignatureMatching P) (τ : D.what₂.Tau) :
    X.fm.beOn τ ≤ Formalism.MainNotions.PrimeDegreeVariant.brBd (Nm_succ D.R) (lamTr X τ) (sgTr X τ) := by
  obtain ⟨-, -, ⟨f, hf, hne⟩, -⟩ := h τ
  have hf' : f ∈ delSq ℂ _ (X.fm.lam D.R.m τ) := by rw [← delSq_lamTr X ℂ τ]; exact hf
  have h0 : f ≠ 0 := by
    rintro rfl
    exact hne (map_zero _)
  rw [P.beOn_eq τ]
  unfold opNorm
  refine csSup_le ⟨_, ⟨f, ⟨hf', h0⟩, rfl⟩⟩ ?_
  rintro _ ⟨g, ⟨hg, hg0⟩, rfl⟩
  exact h.quot_le τ hg hg0

example (P : Pend X) (w) (c) (φ) (hφ : φ ∈ X.fm.Fi D.R.m) (f) (hf : P.coM w c (φ (X.fm.til c)) = ten f) :
    P.coP w (Pt X φ) c = ten fun τ => P.br τ (f τ) := by
  rw [P.Pt_eq w φ hφ c, hf, Formalism.MainNotions.product_first_zeroth_parts.blk_ten]

example (P : Pend X) (τ : D.what₂.Tau) (h : P.br τ = 0) : ¬ ArchimedeanSignatureMatching P := fun H => by
  obtain ⟨f, -, hf⟩ := (H τ).2.2.1
  exact hf (by rw [h]; rfl)

example (τ : D.what₂.Tau) (h : X.fm.beOn τ = 0) : ¬ ∃ P : Pend X, ArchimedeanSignatureMatching P := fun ⟨_, H⟩ => (H.beOn_pos τ).ne' h

example (P : Pend X) (h : ArchimedeanSignatureMatching P) (τ : D.what₂.Tau) (f) (hf : f ∈ delSq ℂ _ (X.fm.lam D.R.m τ)) :
    ((sqrtT X : ℂˣ) : ℂ) ^ 2 = X.A.T ∧
    P.br τ (sqAct ℂ _ (lamTr X τ) (Formalism.MainNotions.PrimeDegreeVariant.lastGL ℂ _ (sqrtT X)) f) =
      ((sqrtT X ^ X.fm.deg τ : ℂˣ) : ℂ) • P.br τ f := by
  refine ⟨?_, ?_⟩
  · show ((Real.sqrt (X.A.T : ℝ) : ℝ) : ℂ) ^ 2 = _
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  · rw [← degZ_tr]
    exact (h τ).2.2.2.2.1 _ f (by rw [delSq_lamTr]; exact hf)

end GlobalTheory.LvT
