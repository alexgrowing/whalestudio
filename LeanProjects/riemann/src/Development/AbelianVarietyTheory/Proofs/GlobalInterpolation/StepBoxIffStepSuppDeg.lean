import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.MovementLaw

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.MoveCompare

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions
open GlobalTheory.IndefiniteRowSideFullHecke

section Clauses

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem mulLat_le_divLat {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (cA cB : ℕ) (M : Submodule (𝓞 E) H) :
    mulLat cB M ≤ divLat cA M := by
  rintro _ ⟨z, hz, rfl⟩
  exact M.smul_mem _ (M.smul_mem _ hz)

open Classical in

theorem inRange_indicator (K : Type) [Field K] {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) :
    MovementLaw.InRangeOf S cA cB N N' (fun x => if x ∈ divLat cA (homAt S N N') then (1 : K) else 0) := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · by_contra h
    exact hx (if_neg h)
  · have hy' := mulLat_le_divLat cA cB _ hy
    have : x + y ∈ divLat cA (homAt S N N') ↔ x ∈ divLat cA (homAt S N N') := Submodule.add_mem_iff_left _ hy'
    simp only [this]

end Clauses

open Classical in

theorem degAt_eq {X : Fields} {a b : ℕ} (m : DVar X.Tau a b →₀ ℕ) (τ : X.Tau) :
    IndexExponentDegree.degAt m τ = ∑ k ∈ m.support.filter (fun k => k.1 = τ), m k := by
  unfold IndexExponentDegree.degAt
  rw [Finset.sum_filter, Finset.sum_subset (Finset.subset_univ m.support) (by
    intro k _ hk
    simp [Finsupp.notMem_support_iff.1 hk]), Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · rw [Fintype.sum_prod_type]
    simp
  · intro σ _ hσ
    simp [hσ]
  · simp

theorem nuW_detShift_nonneg {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R) (u : Word) {i : ℕ} (hi : i < R.m) (τ : X.Tau) :
    0 ≤ (W.nuW u (i + 1) τ).detShift := by
  have hpos : 0 < R.N i := R.N_pos i
  have hlt : R.N i < R.N R.m := by
    unfold Ranks.N
    exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right hi (Nat.succ_pos R.t)) _
  have hb : Examples₂.blkN R (R.N i) = i := by
    unfold Examples₂.blkN Ranks.N
    rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel _ (Nat.succ_pos _)]
  have h1 : Examples₂.wtN (W.hc u τ) (R.N i) = -wG R ((W.hc u τ).e ⟨i, hi⟩) (i + 1) := by
    unfold Examples₂.wtN
    rw [dif_neg (by unfold Ranks.N; omega), dif_pos (by rw [hb]; exact hi)]
    simp only [hb]
  have h2 := Examples₂.wtN_anti (W.hc u τ) (Nat.sub_le (R.N i) 1) hlt
  have h3 := Examples₂.lamOf_eq (W.hc u τ) i hi.le ⟨R.N i - 1, by omega⟩
  rw [Examples₂.wtQ_eq_wtN] at h3
  have h4 : (W.nuW u (i + 1) τ).detShift =
      (Examples₂.lamOf (W.hc u τ) i).w ⟨R.N i - 1, by omega⟩ + ⌊wG R ((W.hc u τ).e ⟨i, hi⟩) (i + 1)⌋ := by
    unfold DomWeight.detShift
    rw [dif_pos (show 0 < R.N (i + 1 - 1) from hpos)]
    simp only [Wts.nuW, shiftW, Wts.lamN, RowPar.eAt, RowPar.of, Nat.add_sub_cancel, hi, dif_pos]
    rfl
  rw [h4]
  have h5 : -(Examples₂.lamOf (W.hc u τ) i).w ⟨R.N i - 1, by omega⟩ ≤ ⌊wG R ((W.hc u τ).e ⟨i, hi⟩) (i + 1)⌋ := by
    rw [Int.le_floor]
    push_cast
    rw [h3]
    simp only at h2 ⊢
    linarith
  omega

theorem degNu_eq {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (u : Pr.Word) {i : ℕ} (hi : i < R.m) (τ : X.Tau) :
    IndexExponentDegree.degNu (W.lamTrue u i) (nuLast W u i) τ = ∑ k, (W.nuW u (i + 1) τ).w k := by
  have hpos : 0 < R.N i := R.N_pos i
  unfold IndexExponentDegree.degNu nuLast
  rw [Int.toNat_of_nonneg (nuW_detShift_nonneg W u hi τ)]
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold DomWeight.detShift
  rw [dif_pos (show 0 < R.N (i + 1 - 1) from hpos), dif_pos hpos]
  show ((W.lamN u i τ).w s + _) - ((W.lamN u i τ).w ⟨R.N i - 1, _⟩ + _) + ((W.lamN u i τ).w ⟨R.N i - 1, _⟩ + _) =
    (W.lamN u i τ).w s + _
  ring

theorem delta_ne_zero {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) : δ ≠ 0 := by
  rintro rfl
  have h1 : B.L.ω₁ ∈ TaylorLogMetric.lamOf D cc 0 := by
    rw [← B.lat]
    exact B.L.ω₁_mem_lattice
  have h2 : TaylorLogMetric.lamOf D cc 0 ≤ ⊥ := by
    unfold TaylorLogMetric.lamOf
    rw [AddSubgroup.closure_le]
    rintro w ⟨c, -, rfl⟩
    simp
  have h3 : B.L.ω₁ = 0 := h2 h1
  exact B.L.indep.ne_zero 0 (by simpa using h3)

section Jets

variable {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ)

def JetsAll (deg : X.Tau → ℤ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : Prop :=
  ∀ Ξ : HomE X.E a b → X.K, MovementLaw.InRangeOf S cA cB N N' Ξ → MovementLaw.JetsIn A S cB deg N N' Ξ

theorem jetsIn_iff (lam : X.Tau → DomWeight a) (n : X.Tau → ℕ) (deg : X.Tau → ℤ) (h : ∀ τ, IndexExponentDegree.degNu lam n τ = deg τ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) :
    IndexExponentDegree.JetsIn A S cA cB lam n N N' ↔ JetsAll A S cA cB deg N N' := by
  constructor
  · intro hJ Ξ hΞ x hx m hm
    refine hJ x (hΞ.1 x hx) m fun τ => ?_
    rw [degAt_eq, h τ, ← hm τ]
  · intro hJ x hx m hm
    refine hJ _ (inRange_indicator X.K S cA cB N N') x (by simp [hx]) m fun τ => ?_
    rw [← h τ, ← hm τ, degAt_eq]

open Classical in

def JetsDeg (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (M : ℕ) (deg : X.Tau → ℤ) : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b), InRange S M c N N' x →
    ∀ m : DVar X.Tau a b →₀ ℕ, (∀ τ, ((∑ k ∈ m.support.filter (fun k => k.1 = τ), m k : ℕ) : ℤ) = deg τ) →
      ∃ k : X.K, A.σ₀ k = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd S N N' c x) m

theorem jetsAll_of_deg (deg : X.Tau → ℤ) (h : JetsDeg A a b S (cA * cB) deg) (hB : 0 < cB)
    {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)} (hN : IsSdLat N) (hN' : IsSdLat N') :
    JetsAll A S cA cB deg N N' := by
  intro Ξ hΞ x hx m hm
  refine h N N' cB x ⟨hN, hN', hB, Dvd.intro_left _ rfl, ?_⟩ m hm
  have h1 : ((cA : ℕ) : 𝓞 X.E) • x ∈ homAt S N N' := hΞ.1 x hx
  show ((cA * cB : ℕ) : 𝓞 X.E) • x ∈ homAt S N N'
  rw [Nat.cast_mul, mul_comm, mul_smul]
  exact Submodule.smul_mem _ _ h1

end Jets

theorem cBof_pos {X : Fields} {Pr : Primes X} (hP : Pr.Ok) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) : 0 < cBof sel mu cst u := by
  unfold cBof
  refine Nat.mul_pos (hP.T_prime u).pos (pow_pos (Finset.prod_pos fun P _ => ?_) _)
  exact Nat.pos_of_ne_zero (by unfold Formalism.L2.Col.qOf; rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.1.ne_bot)

abbrev StepSt : Type 1 :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (_ : Wts X Pr.Word R) (_ : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (_ : LocCst X (rowSG Pr sel mu)) (_ : Pr.Word) (_ : Amb X) (_ : ℕ) (b : ℕ) (_ : X.Tau → DomWeight b), Prop

def StepBox : StepSt := fun X Pr R W Ch sel _ mu cst u A i b lam' =>
  ∀ (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E (R.N i))) (N₁' N₂' : Submodule (𝓞 X.E) (Sp X.E b))
    (fr : Frs X.E (R.N i) (rowSG Pr sel mu)) (fr' : Frs X.E b (rowSG Pr sel mu)) (Ξ : HomE X.E (R.N i) b → X.K),
    IsSdLat N₁ → IsSdLat N₂ → IsSdLat N₁' → IsSdLat N₂' →
    IndexExponentDegree.AgreeOff (Pr.T u) N₁ N₂ → IndexExponentDegree.AgreeOff (Pr.T u) N₁' N₂' →
    IndexExponentDegree.InBox (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ N₁' Ξ →
    IndexExponentDegree.InBox (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ N₂' Ξ →
    IndexExponentDegree.JetsIn A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (W.lamTrue u i) (nuLast W u i) N₁ N₁' →
    IndexExponentDegree.JetsIn A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (W.lamTrue u i) (nuLast W u i) N₂ N₂' →
    kerOf (stepT W Ch sel mu cst A u i lam') (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ fr N₁' fr' Ξ =
      IndexExponentDegree.moveScal Ch mu u i N₁ N₂ N₁' N₂' •
        kerOf (stepT W Ch sel mu cst A u i lam') (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ fr N₂' fr' Ξ

def StepSupp : StepSt := fun X Pr R W Ch sel _ mu cst u A i b lam' =>
  ∀ (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E (R.N i))) (N₁' N₂' : Submodule (𝓞 X.E) (Sp X.E b)),
    IsSdLat N₁ → IsSdLat N₂ → IsSdLat N₁' → IsSdLat N₂' →
    MovementLaw.AgreeOff (Pr.T u) N₁ N₂ → MovementLaw.AgreeOff (Pr.T u) N₁' N₂' →
  ∀ (fr : Frs X.E (R.N i) (rowSG Pr sel mu)) (fr' : Frs X.E b (rowSG Pr sel mu)) (Ξ : HomE X.E (R.N i) b → X.K),
    MovementLaw.InRangeOf (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ N₁' Ξ →
    MovementLaw.InRangeOf (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ N₂' Ξ →
    MovementLaw.JetsIn A (Sall sel mu u) (cBof sel mu cst u) (fun τ => ∑ k, (W.nuW u (i + 1) τ).w k) N₁ N₁' Ξ →
    MovementLaw.JetsIn A (Sall sel mu u) (cBof sel mu cst u) (fun τ => ∑ k, (W.nuW u (i + 1) τ).w k) N₂ N₂' Ξ →
    kerOf (stepT W Ch sel mu cst A u i lam') (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ fr N₁' fr' Ξ =
      MovementLaw.moveScal Ch mu u i N₁ N₂ N₁' N₂' •
        kerOf (stepT W Ch sel mu cst A u i lam') (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ fr N₂' fr' Ξ

def StepAll : StepSt := fun X Pr R W Ch sel _ mu cst u A i b lam' =>
  ∀ (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E (R.N i))) (N₁' N₂' : Submodule (𝓞 X.E) (Sp X.E b)),
    IsSdLat N₁ → IsSdLat N₂ → IsSdLat N₁' → IsSdLat N₂' →
    MovementLaw.AgreeOff (Pr.T u) N₁ N₂ → MovementLaw.AgreeOff (Pr.T u) N₁' N₂' →
  ∀ (fr : Frs X.E (R.N i) (rowSG Pr sel mu)) (fr' : Frs X.E b (rowSG Pr sel mu)) (Ξ : HomE X.E (R.N i) b → X.K),
    MovementLaw.InRangeOf (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ N₁' Ξ →
    MovementLaw.InRangeOf (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ N₂' Ξ →
    JetsAll A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (fun τ => ∑ k, (W.nuW u (i + 1) τ).w k) N₁ N₁' →
    JetsAll A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (fun τ => ∑ k, (W.nuW u (i + 1) τ).w k) N₂ N₂' →
    kerOf (stepT W Ch sel mu cst A u i lam') (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ fr N₁' fr' Ξ =
      MovementLaw.moveScal Ch mu u i N₁ N₂ N₁' N₂' •
        kerOf (stepT W Ch sel mu cst A u i lam') (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ fr N₂' fr' Ξ

def StepField : StepSt := fun _ _ R W _ sel _ mu cst u A i b _ =>
  JetsDeg A (R.N i) b (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) (fun τ => ∑ k, (W.nuW u (i + 1) τ).w k)

def OverField (St : StepSt) : StepSt := fun X Pr R W Ch sel S mu cst u A i b lam' =>
  StepField X Pr R W Ch sel S mu cst u A i b lam' → St X Pr R W Ch sel S mu cst u A i b lam'

section Step

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (A : Amb X) {i : ℕ} {b : ℕ} (lam' : X.Tau → DomWeight b)

end Step

def OverWide (St : StepSt) : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word)
    (D : D7) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ),
    X.Ok → Pr.Ok → Ch.FromHecke W s.σ₀ → IsSel X sel → Pr.T u ∈ S → (∀ k, Pr.g k ∈ S) →
    s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsChi D χ →
    (∀ P ∈ Sall sel mu u, Nat.Coprime (Ideal.absNorm cc) (Ideal.absNorm P.asIdeal)) →
    ∀ (i : ℕ), i < R.m → ∀ (b : ℕ), b = R.N (i + 1) → ∀ (lam' : X.Tau → DomWeight b),
      St X Pr R W Ch sel S mu cst u (ambOf s B χ cD) i b lam'

def OverNarrow (St : StepSt) : Prop :=
  ∀ (Dt : Dat), Dt.Ok →
  ∀ (D : D7) (s : Seam D Dt.X), s.Ok → s.σ₀ = Dt.sig0 →
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → δ ≠ 0 →
  ∀ (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ →
  ∀ (cD : D.what₂.Tau → ℂ)
    (sel : HeightOneSpectrum (𝓞 Dt.X.F) → HeightOneSpectrum (𝓞 Dt.X.E)), IsSel Dt.X sel →
  ∀ (S : Set ℕ), hostS D.host.q D.host.d (Dt.Pr.g 0) (Dt.Pr.g 1) (Set.range Dt.Pr.T ∪ (D.host.small : Set ℕ)) ⊆ S →
  ∀ (mu : Tup Dt.X.F Dt.X.E Dt.X.K S) (cst : LocCst Dt.X (rowSG Dt.Pr sel mu)) (u : Dt.Pr.Word),
    (∀ P ∈ Sall (Pr := Dt.Pr) sel mu u, Nat.Coprime (Ideal.absNorm cc) (Formalism.L2.Col.qOf P)) →
  ∀ (i j : ℕ), j = i + 1 → j ≤ Dt.R.m →
    St Dt.X Dt.Pr Dt.R Dt.W Dt.Ch sel S mu cst u (ambOf s B χ cD) i (Dt.R.N j) (Dt.W.lamTrue u j)

end GlobalTheory.MoveCompare
