import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Formalism.LocalToGlobal.Columns.RowFormsLemmas
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.TopStep

section Cong

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

variable (P) in

def CongQ (a b : E) : Prop := IntAt P a ∧ IntAt P b ∧ IntAt P ((a - b) / (qOf P : E))

omit [StarRing E] in
theorem CongQ.red {a b : E} (h : CongQ P a b) : redP P a = redP P b := by
  have := redP_eq_zero_of_div h.2.2
  rwa [reduction_sub h.1 h.2.1, sub_eq_zero] at this

omit [StarRing E] in
theorem CongQ.div_iff {a b : E} (h : CongQ P a b) : IntAt P (a / (qOf P : E)) ↔ IntAt P (b / (qOf P : E)) := by
  constructor
  · intro ha
    have := intAt_sub ha h.2.2
    rwa [← sub_div, sub_sub_cancel] at this
  · intro hb
    have := h.2.2.add hb
    rwa [← add_div, sub_add_cancel] at this

omit [StarRing E] in
theorem congQ_zero : CongQ P (0 : E) 0 := ⟨intAt_zero, intAt_zero, by simpa using intAt_zero⟩

omit [StarRing E] in
theorem unitV_congr (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a b : E} (h : redP P a = redP P b) : LocE.unitV χ a = LocE.unitV χ b := by
  classical
  exact congrArg (fun c : 𝓞 E ⧸ P.asIdeal => if h : IsUnit c then ((χ h.unit : Kˣ) : K) else 0) h

omit [StarRing E] in
theorem unitV_det_congr (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {s : ℕ} {A B : Fin s → Fin s → E} (h : ∀ i j, CongQ P (A i j) (B i j)) :
    LocE.unitV χ (Matrix.det (Matrix.of A)) = LocE.unitV χ (Matrix.det (Matrix.of B)) := by
  apply unitV_congr
  rw [(det_int (A := Matrix.of A) fun i j => (h i j).1).2, (det_int (A := Matrix.of B) fun i j => (h i j).2.1).2]
  congr 1
  ext i j
  exact (h i j).red

omit [StarRing E] in
theorem reduction_sum_congr (s : Finset ℕ) {f g : ℕ → E} (h : ∀ i, CongQ P (f i) (g i)) :
    redP P (∑ i ∈ s, f i) = redP P (∑ i ∈ s, g i) := by
  rw [reduction_sum₂ _ fun i _ => (h i).1, reduction_sum₂ _ fun i _ => (h i).2.1]
  exact Finset.sum_congr rfl fun i _ => (h i).red

variable (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)

theorem PhiG_congr (sharp : Bool) (k₀ r t j c' n' c n : ℕ) {x y : HomE E (n' + c') (n + c)}
    (h : ∀ p p', CongQ P (LocE.entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p p')
      (LocE.entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) y p p')) :
    LocE.PhiG (qOf P) ψ₀ χ sharp k₀ r t j c' n' c n x = LocE.PhiG (qOf P) ψ₀ χ sharp k₀ r t j c' n' c n y := by
  unfold LocE.PhiG LocE.lamGv
  dsimp only
  refine @if_congr _ _ _ (_) (_) _ _ _ _ ?_ ?_ rfl
  · simp only [(h _ _).1, (h _ _).2.1, (h _ _).div_iff, (h _ _).red]
  · rw [reduction_sum_congr _ fun i => h i (i + 1), unitV_det_congr _ fun s s' => h s.1 s'.1]
    congr 2
    exact Finset.prod_congr rfl fun i _ => unitV_det_congr _ fun s s' => h _ _

theorem PhiGS_congr (k₀ rS r t j c' n' c n : ℕ) {x y : HomE E (n' + c') (n + c)}
    (h : ∀ p p', CongQ P (LocE.entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p p')
      (LocE.entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) y p p')) :
    LocE.PhiGS (qOf P) ψ₀ χ k₀ rS r t j c' n' c n x = LocE.PhiGS (qOf P) ψ₀ χ k₀ rS r t j c' n' c n y := by
  unfold LocE.PhiGS LocE.lamGvS
  dsimp only
  refine @if_congr _ _ _ (_) (_) _ _ _ _ ?_ ?_ rfl
  · simp only [(h _ _).1, (h _ _).2.1, (h _ _).div_iff, (h _ _).red]
  · rw [reduction_add (intAt_sum _ fun i _ => (h _ _).1) (intAt_sum _ fun i _ => (h _ _).1),
      reduction_add (intAt_sum _ fun i _ => (h _ _).2.1) (intAt_sum _ fun i _ => (h _ _).2.1),
      reduction_sum_congr _ fun i => h i (i + 1), reduction_sum_congr _ fun i => h (k₀ + i) (k₀ + i + 1),
      unitV_det_congr _ fun s s' => h s.1 s'.1]
    congr 2
    exact Finset.prod_congr rfl fun i _ => unitV_det_congr _ fun s s' => h _ _

omit [NumberField E] [StarRing E] in

theorem entB_zero (q k₀ c' n' n : ℕ) (hc : c' = 0) (ex : ℕ → ℕ) (x : HomE E (n' + c') (n + 0)) (p p' : ℕ) :
    LocE.entB q k₀ c' n' 0 n ex ex x p p' =
      if h : p < n ∧ p' < n' then x (Pi.single ⟨p', by omega⟩ 1) ⟨p, h.1⟩ else 0 := by
  subst hc
  have e : ∀ m s, LocE.fIdx k₀ 0 m s = s := fun m s => by
    unfold LocE.fIdx
    split_ifs <;> omega
  unfold LocE.entB
  rw [e, e]
  by_cases h1 : p < n
  · by_cases h2 : p' < n'
    · have : Loc.eN E (n' + 0) p' = Pi.single ⟨p', h2⟩ 1 := by
        funext l
        simp [Loc.eN, Pi.single_apply, Fin.ext_iff]
      rw [dif_pos ⟨h1, h2⟩, this]
      simp [LocE.scE, Loc.atN, h1, h2]
    · have : Loc.eN E (n' + 0) p' = 0 := by
        funext l
        have := l.2
        simp only [Loc.eN, Pi.zero_apply]
        rw [if_neg (by omega)]
      rw [dif_neg fun h => h2 h.2, this]
      simp [Loc.atN]
  · rw [dif_neg fun h => h1 h.1]
    simp [Loc.atN, h1]

omit [StarRing E] in

theorem locChar_mul (q : ℕ) (cq : K) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {u : E} (hu : ∀ a, redP P (a * u) = redP P a) (a : E) :
    LocE.locChar q cq ξ (a * u) = LocE.locChar q cq ξ a := by
  have e : ∀ z : ℤ, redP P (a * u / (q : E) ^ z) = redP P (a / (q : E) ^ z) := fun z => by
    rw [mul_div_right_comm, hu]
  have ev : LocE.vP P q (a * u) = LocE.vP P q a := by
    unfold LocE.vP
    simp only [e]
  unfold LocE.locChar
  rw [ev, unitV_congr ξ (e _)]

end Cong

section Tame

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))}
  {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

def TameFr (th : ThDist E K a b SB V V') : Prop :=
  ∀ (N : Submodule (𝓞 E) (Sp E a)) (fr : Frs E a SB) (N' : Submodule (𝓞 E) (Sp E b)) (fr' : Frs E b SB) (c : ℕ) (x : HomE E a b)
    (κ : GLQ E b SB), IsSdLat N → IsSdLat N' → (∀ P : SB, redGL b P.1 (κ P) = 1) →
    th N fr N' (fun P => fr' P * (κ P).1) c x = th N fr N' fr' c x

end Tame

section TameC

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem tameFr_thDistC (A : Amb X) {a b : ℕ} (Sall SB : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ)
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (cq : SB → X.K) (ξ : ∀ P : SB, (𝓞 X.E ⧸ P.1.asIdeal)ˣ →* X.Kˣ)
    (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ) :
    TameFr (thDistC A Sall SB D sel mU (fun P => LocE.locChar (qOf P.1) (cq P) (ξ P)) lam lam' n) := by
  intro N fr N' fr' c x κ _ _ hκ
  have e : muInvDet sel SB mU (fun P => LocE.locChar (qOf P.1) (cq P) (ξ P)) N' (fun P => fr' P * (κ P).1) =
      muInvDet sel SB mU (fun P => LocE.locChar (qOf P.1) (cq P) (ξ P)) N' fr' := by
    unfold muInvDet
    congr 1
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [map_mul, Units.val_mul]
    exact locChar_mul _ _ _ (redP_mul_det (κ P) (hκ P)) _
  unfold thDistC
  rw [e]

theorem tameFr_chTh (A : Amb X) (u : Pr.Word) (m2 : ℕ) : TameFr (chTh W Ch sel mu cst A u m2).top :=
  tameFr_thDistC sel A _ _ _ _ _ _ _ _ _

end TameC

section Unif

variable {X : Fields} {Pr : Primes X}

theorem qOf_notMem_sq (hX : X.Ok) (hPr : Pr.Ok) {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vGs) :
    ((qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, w ∈ Pr.vG i := (Finset.mem_union.1 hw).elim (fun h => ⟨0, h⟩) fun h => ⟨1, h⟩
  have hg0 : (Pr.g i : 𝓞 X.E) ≠ 0 := by exact_mod_cast (hPr.g_prime i).ne_zero
  set b := X.conjO (Pr.piG i) with hb
  have h0 : b ≠ 0 := fun h => hg0 (by rw [← hPr.piG_norm i, ← hb, h, mul_zero])
  have hnorm : Ideal.absNorm (Ideal.span {b}) = Pr.g i ^ X.f := by
    have h1 : Ideal.absNorm (Ideal.span {Pr.piG i}) * Ideal.absNorm (Ideal.span {b}) = Pr.g i ^ (2 * X.f) := by
      rw [← map_mul, Ideal.span_singleton_mul_span_singleton, hPr.piG_norm, X.absNorm_nat, hX.rankQ]
    rw [← X.absNorm_conjO] at h1
    have h2 : Ideal.absNorm (Ideal.span {b}) ^ 2 = (Pr.g i ^ X.f) ^ 2 := by
      rw [sq, h1, ← pow_mul, mul_comm]
    exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) h2
  intro hT
  rw [qOf, hPr.vG_norm i w hi] at hT
  have hbw : b ∈ w.asIdeal := decoFin_mem_of_mem_divs hi
  have hmem : b ∈ w.asIdeal ^ 2 := by
    obtain ⟨s, t, e⟩ := hPr.piG_cop i
    have e1 : b = s * (Pr.g i : 𝓞 X.E) + t * (b * b) := by
      rw [← hPr.piG_norm i]
      calc b = (s * Pr.piG i + t * b) * b := by rw [e, one_mul]
        _ = _ := by ring
    rw [e1]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hT) (Ideal.mul_mem_left _ _ ?_)
    rw [sq]
    exact Ideal.mul_mem_mul hbw hbw
  have hdvd : (∏ Q ∈ Pr.vG i, Q.asIdeal ^ (if Q = w then 2 else 1)) ∣ Ideal.span {b} := by
    refine Finset.prod_dvd_of_coprime (fun Q _ Q' _ hne => ?_) fun Q hQ => ?_
    · refine IsCoprime.pow ?_
      rw [Ideal.isCoprime_iff_sup_eq]
      exact Ideal.IsMaximal.coprime_of_ne Q.isMaximal Q'.isMaximal fun h => hne (HeightOneSpectrum.ext h)
    · rw [Ideal.dvd_span_singleton]
      split_ifs with h
      · rw [h]; exact hmem
      · rw [pow_one]; exact decoFin_mem_of_mem_divs hQ
  have hN : Ideal.absNorm (∏ Q ∈ Pr.vG i, Q.asIdeal ^ (if Q = w then 2 else 1)) = Pr.g i ^ (X.f + 1) := by
    rw [map_prod]
    have h1 : ∀ Q ∈ Pr.vG i, Ideal.absNorm (Q.asIdeal ^ (if Q = w then 2 else 1)) = Pr.g i * (if Q = w then Pr.g i else 1) := by
      intro Q hQ
      rw [map_pow, hPr.vG_norm i Q hQ]
      split_ifs
      · rw [sq]
      · rw [pow_one, mul_one]
    rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_const, hPr.vG_card, Finset.prod_ite_eq', if_pos hi, pow_succ]
  have h3 := map_dvd Ideal.absNorm hdvd
  rw [hN, hnorm] at h3
  have := (Nat.pow_dvd_pow_iff_le_right (hPr.g_prime i).one_lt).1 h3
  omega

end Unif

end GlobalTheory.TopStep
