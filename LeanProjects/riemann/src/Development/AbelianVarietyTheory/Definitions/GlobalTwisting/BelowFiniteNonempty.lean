import Mathlib
import Formalism.LocalToGlobal.Columns.CoefCol
import Formalism.LocalToGlobal.Columns.DecoFin
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.CharacterValuation

noncomputable section

namespace GlobalTheory.KerT

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree (AgreeOff InBox JetsIn moveScal)

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (A : Amb X) (u : Pr.Word) (i j : ℕ)

def ker (N : Submodule (𝓞 X.E) (Sp X.E (R.N i))) (fr : Frs X.E (R.N i) (rowSG Pr sel mu))
    (N' : Submodule (𝓞 X.E) (Sp X.E (R.N j))) (fr' : Frs X.E (R.N j) (rowSG Pr sel mu)) (Ξ : HomE X.E (R.N i) (R.N j) → X.K) :
    VV X.K (W.lamTrue u i) →ₗ[X.K] VV X.K (W.lamTrue u j) :=
  kerOf (stepT W Ch sel mu cst A u i (W.lamTrue u j)) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N fr N' fr' Ξ

def term {SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet X.E (R.N i) (Pr.vT u) SG)
    (fr : Frs X.E (R.N i) (rowSG Pr sel mu)) (d' : DecoSet X.E (R.N j) (Pr.vT u) SG') (fr' : Frs X.E (R.N j) (rowSG Pr sel mu))
    (Ξ₀ : HomE X.E (R.N i) (R.N j) → X.K) : VV X.K (W.lamTrue u i) →ₗ[X.K] VV X.K (W.lamTrue u j) :=
  ker W Ch sel mu cst A u i j d.1.N fr d'.1.N fr' fun x => phiT X.K d.1 d'.1 x * Ξ₀ x

def InBoxOfRowSelection {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ₀ : HomE X.E a b → X.K) : Prop :=
  InBox (rowSG Pr sel mu) (cAof sel mu cst) (cBof sel mu cst u) N N' Ξ₀

abbrev Framed {n : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} (N : Submodule (𝓞 X.E) (Sp X.E n)) (fr : Frs X.E n SB) : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.IsFrames N fr

def JetsAll : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E (R.N i))) (N' : Submodule (𝓞 X.E) (Sp X.E (R.N j))), IsSdLat N → IsSdLat N' →
    JetsIn A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (W.lamTrue u i) (nuLast W u i) N N'

def MoveStep : Prop :=
  ∀ (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E (R.N i))) (N₁' N₂' : Submodule (𝓞 X.E) (Sp X.E (R.N j)))
    (fr : Frs X.E (R.N i) (rowSG Pr sel mu)) (fr' : Frs X.E (R.N j) (rowSG Pr sel mu)) (Ξ : HomE X.E (R.N i) (R.N j) → X.K),
    IsSdLat N₁ → IsSdLat N₂ → IsSdLat N₁' → IsSdLat N₂' → AgreeOff (Pr.T u) N₁ N₂ → AgreeOff (Pr.T u) N₁' N₂' →
    InBox (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ N₁' Ξ →
    InBox (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ N₂' Ξ →
    ker W Ch sel mu cst A u i j N₁ fr N₁' fr' Ξ = moveScal Ch mu u i N₁ N₂ N₁' N₂' • ker W Ch sel mu cst A u i j N₂ fr N₂' fr' Ξ

def RatStep : Prop :=
  ThEquivP (stepT W Ch sel mu cst A u i (W.lamTrue u j)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
    ((rhoVr X.emb (W.lamTrue u i)).comp (ufGL X.E (R.N i))) ((rhoVr X.emb (W.lamTrue u j)).comp (ufGL X.E (R.N j)))

def RatTerm : Prop :=
  ∀ {SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet X.E (R.N i) (Pr.vT u) SG) (fr : Frs X.E (R.N i) (rowSG Pr sel mu))
    (d' : DecoSet X.E (R.N j) (Pr.vT u) SG') (fr' : Frs X.E (R.N j) (rowSG Pr sel mu)) (Ξ₀ : HomE X.E (R.N i) (R.N j) → X.K)
    (γ : UF X.E (R.N i)) (γ' : UF X.E (R.N j)), InBoxOfRowSelection sel mu cst u d.1.N d'.1.N Ξ₀ →
    term W Ch sel mu cst A u i j (((γ, 1) : UF X.E (R.N i) × GLG X.E (R.N i) SG) • d) (fun P => γ.1 * fr P)
        (((γ', 1) : UF X.E (R.N j) × GLG X.E (R.N j) SG') • d') (fun P => γ'.1 * fr' P)
        (fun x => Ξ₀ (γ'.1.symm.toLinearMap ∘ₗ x ∘ₗ γ.1.toLinearMap)) =
      (rhoVr X.emb (W.lamTrue u j) (ufGL X.E (R.N j) γ')) ∘ₗ term W Ch sel mu cst A u i j d fr d' fr' Ξ₀ ∘ₗ
        (rhoVr X.emb (W.lamTrue u i) (ufGL X.E (R.N i) γ⁻¹))

def UKTerm : Prop :=
  ∀ {SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet X.E (R.N i) (Pr.vT u) SG) (fr : Frs X.E (R.N i) (rowSG Pr sel mu))
    (d' : DecoSet X.E (R.N j) (Pr.vT u) SG') (fr' : Frs X.E (R.N j) (rowSG Pr sel mu)) (Ξ₀ : HomE X.E (R.N i) (R.N j) → X.K)
    (P : Pr.vT u) (y : VV X.K (W.lamTrue u i)), MoveHyp (Pr.vT u) SG P → MoveHyp (Pr.vT u) SG' P →
    InBoxOfRowSelection sel mu cst u d.1.N d'.1.N Ξ₀ →
    (∑ᶠ d₁ ∈ {d₁ : DecoSet X.E (R.N j) (Pr.vT u) SG' | d'.1.IsUp P (Pr.T u : 𝓞 X.E) d₁.1},
        term W Ch sel mu cst A u i j d fr d₁ fr' Ξ₀ y) =
      ((Pr.T u : X.K) ^ ((R.t + 1) / 2)) •
        ∑ᶠ d₀ ∈ {d₀ : DecoSet X.E (R.N i) (Pr.vT u) SG | d₀.1.IsUp P (Pr.T u : 𝓞 X.E) d.1},
          term W Ch sel mu cst A u i j d₀ fr d' fr' Ξ₀ y

def valAt (w : HeightOneSpectrum (𝓞 X.K)) {n : ℕ} (lam : X.Tau → DomWeight n) (L : Submodule (𝓞 X.E) (Sp X.E n)) :
    Submodule (𝓞 X.K) (VV X.K lam) := localization₂ w.asIdeal (delAtr X.emb lam L)

def BarTerm (w : HeightOneSpectrum (𝓞 X.K)) : Prop :=
  ∀ {SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet X.E (R.N i) (Pr.vT u) SG) (fr : Frs X.E (R.N i) (rowSG Pr sel mu))
    (d' : DecoSet X.E (R.N j) (Pr.vT u) SG') (fr' : Frs X.E (R.N j) (rowSG Pr sel mu)) (Ξ₀ : HomE X.E (R.N i) (R.N j) → X.K),
    Framed d.1.N fr → Framed d'.1.N fr' → InBoxOfRowSelection sel mu cst u d.1.N d'.1.N Ξ₀ → (∀ x, w.valuation X.K (Ξ₀ x) ≤ 1) →
    ∀ y ∈ valAt w (W.lamTrue u i) d.1.Lsh, ∃ y' ∈ valAt w (W.lamTrue u j) d'.1.Lsh,
      term W Ch sel mu cst A u i j d fr d' fr' Ξ₀ y = ((Pr.T u : X.K) ^ (X.f * ((R.t + 1) / 2))) • y'

def PTerm (w : HeightOneSpectrum (𝓞 X.K)) : Prop :=
  ∀ {SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet X.E (R.N i) (Pr.vT u) SG) (fr : Frs X.E (R.N i) (rowSG Pr sel mu))
    (d' : DecoSet X.E (R.N j) (Pr.vT u) SG') (fr' : Frs X.E (R.N j) (rowSG Pr sel mu)) (Ξ₀ : HomE X.E (R.N i) (R.N j) → X.K),
    Framed d.1.N fr → Framed d'.1.N fr' → InBoxOfRowSelection sel mu cst u d.1.N d'.1.N Ξ₀ → (∀ x, w.valuation X.K (Ξ₀ x) ≤ 1) →
    ∀ y ∈ valAt w (W.lamTrue u i) d.1.Lsh,
      ((Pr.T u : X.K) ^ (((X.f * R.N i : ℕ) : ℤ) - ∑ τ, (W.lamTrue u j τ).detShift)) •
        term W Ch sel mu cst A u i j d fr d' fr' Ξ₀ y ∈ valAt w (W.lamTrue u j) d'.1.L

def StdOnly {SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet X.E (R.N i) (Pr.vT u) SG)
    (d' : DecoSet X.E (R.N j) (Pr.vT u) SG') : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.StdAtT d.1 ∧ GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.StdAtT d'.1

def AlcoveAt : Prop :=
  ∀ τ (a b : Fin (R.N j)), 2 * ((W.lamTrue u j τ).w a - (W.lamTrue u j τ).w b + (R.N j : ℤ)) < (Pr.T u : ℤ)

structure Hyp (Z : Dat) {H : D7} (s : Seam H Z.X) (cc : Ideal (𝓞 H.host.K)) (δ : ℂ) (χ : TaylorLogMetric.IdE H → ℂ) (cD : H.what₂.Tau → ℂ)
    (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (S : Set ℕ) (mu : Tup Z.X.F Z.X.E Z.X.K S)
    (cst : LocCst Z.X (rowSG Z.Pr sel mu)) (u : Z.Pr.Word) : Prop where
  ok : Z.Ok
  ana : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.AnaOk Z s cc δ χ cD
  chiK : GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.ChiInK s χ
  isSel : IsSel Z.X sel
  host : hostS H.host.q H.host.d (Z.Pr.g 0) (Z.Pr.g 1) (Set.range Z.Pr.T) ⊆ S
  small : ∀ l ∈ H.host.small, l ∈ S
  cop : ∀ P ∈ Sall sel mu u, Nat.Coprime (Ideal.absNorm cc) (Ideal.absNorm P.asIdeal)
  cst_ok : cst.Ok
  tied : ∃ (m0 : Fin Z.R.m → Formalism.L2.Host.HChar Z.X.E) (eta : Formalism.L2.Host.HChar Z.X.E),
    Z.Ch.Tied Z.sig0 (fun j τ => (Z.W.row τ).e j) m0 eta ∧ MuqTieG (Pr := Z.Pr) (R := Z.R) sel mu cst Z.sig0 m0

section Position

variable {Pr : Primes X} {u : Pr.Word} {SG : Finset (HeightOneSpectrum (𝓞 X.E))} {n : ℕ}

theorem moveHyp_of_notMem (hPr : Pr.Ok) (h : ∀ w ∈ SG, (Pr.T u : 𝓞 X.E) ∉ w.asIdeal) (P : Pr.vT u) :
    MoveHyp (Pr.vT u) SG P := by
  refine ⟨(moveHyp_of_ok hPr u P).ne, (moveHyp_of_ok hPr u P).st, fun w => ⟨fun e => ?_, fun e => ?_⟩⟩
  · apply h w.1 w.2
    rw [e]
    exact T_mem hPr u P
  · apply h w.1 w.2
    rw [e, mem_conjP, map_natCast]
    exact T_mem hPr u P

theorem above_finite_nonempty (hX : X.Ok) (hPr : Pr.Ok) {P : Pr.vT u} (hP : MoveHyp (Pr.vT u) SG P)
    (d' : DecoSet X.E n (Pr.vT u) SG) :
    {d₁ : DecoSet X.E n (Pr.vT u) SG | d'.1.IsUp P (Pr.T u : 𝓞 X.E) d₁.1}.Finite ∧
      {d₁ : DecoSet X.E n (Pr.vT u) SG | d'.1.IsUp P (Pr.T u : 𝓞 X.E) d₁.1}.Nonempty :=
  ⟨d'.upSet_finite P _, d'.upSet_nonempty P hP (T_unif hX hPr u P).1 (T_unif hX hPr u P).2⟩

theorem below_eq_dnSet (hX : X.Ok) (hPr : Pr.Ok) {P : Pr.vT u} (hP : MoveHyp (Pr.vT u) SG P)
    (d : DecoSet X.E n (Pr.vT u) SG) :
    {d₀ : DecoSet X.E n (Pr.vT u) SG | d₀.1.IsUp P (Pr.T u : 𝓞 X.E) d.1} = d.dnSet P (Pr.T u : 𝓞 X.E) :=
  Set.ext fun d₀ => DecoSet.mem_upSet_iff_mem_dnSet hP (T_unif hX hPr u P).1 (T_unif hX hPr u P).2 d₀ d

theorem below_finite_nonempty (hX : X.Ok) (hPr : Pr.Ok) {P : Pr.vT u} (hP : MoveHyp (Pr.vT u) SG P)
    (d : DecoSet X.E n (Pr.vT u) SG) :
    {d₀ : DecoSet X.E n (Pr.vT u) SG | d₀.1.IsUp P (Pr.T u : 𝓞 X.E) d.1}.Finite ∧
      {d₀ : DecoSet X.E n (Pr.vT u) SG | d₀.1.IsUp P (Pr.T u : 𝓞 X.E) d.1}.Nonempty := by
  rw [below_eq_dnSet hX hPr hP]
  exact ⟨d.dnSet_finite P hP.ne _, d.dnSet_nonempty P hP (T_unif hX hPr u P).1 (T_unif hX hPr u P).2⟩

end Position

variable {sel u} in

theorem T_notMem_rowSG (hPr : Pr.Ok) (hsel : IsSel X sel) (hT : Pr.T u ∈ S) :
    ∀ w ∈ rowSG Pr sel mu, (Pr.T u : 𝓞 X.E) ∉ w.asIdeal := by
  classical
  intro w hw hm
  rcases Finset.mem_union.1 hw with h | h
  · exact T_notMem_vGs hPr u ⟨w, h⟩ hm
  · unfold QE at h
    split_ifs at h with hf
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
      have hv' : v ∈ Qprime (mu : Chr X.F X.E X.K) := hf.mem_toFinset.1 hv
      have hg : GoodPl X.E S v := by
        by_contra hg
        exact hv' (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 mu.2.2 v) hg)
      have h1 : (Pr.T u : 𝓞 X.F) ∈ v.asIdeal := by
        rw [← hsel v, Ideal.under_def, Ideal.mem_comap, map_natCast]
        exact hm
      apply hg.2.2
      have h2 : ringChar (𝓞 X.F ⧸ v.asIdeal) = Pr.T u := by
        have := v.isPrime
        have h3 : ((Pr.T u : ℕ) : 𝓞 X.F ⧸ v.asIdeal) = 0 := by
          rw [← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
          exact h1
        exact ((Nat.dvd_prime (hPr.T_prime u)).1 (ringChar.dvd h3)).resolve_left CharP.ringChar_ne_one
      show ringChar (𝓞 X.F ⧸ v.asIdeal) ∈ S
      rw [h2]
      exact hT
    · simp at h

variable {W u j} in

theorem alcoveAt_of_sizes {a : ℝ} (h : Sizes Pr W a) (hj : j ≤ R.m) : AlcoveAt W u j := by
  intro τ s t
  have h1 := h.two_spread_lt u j hj τ
  have h0 := R.N_pos j
  rw [DomWeight.spread, dif_pos h0] at h1
  have h2 : (W.lamTrue u j τ).w s ≤ (W.lamTrue u j τ).w ⟨0, h0⟩ := (W.lamTrue u j τ).anti (Nat.zero_le _)
  have h3 : (W.lamTrue u j τ).w ⟨R.N j - 1, by omega⟩ ≤ (W.lamTrue u j τ).w t :=
    (W.lamTrue u j τ).anti (show t.1 ≤ R.N j - 1 by have := t.2; omega)
  omega

namespace Hyp

variable {Z : Dat} {H : D7} {s : Seam H Z.X} {cc : Ideal (𝓞 H.host.K)} {δ : ℂ} {χ : TaylorLogMetric.IdE H → ℂ} {cD : H.what₂.Tau → ℂ}
  {sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)} {S : Set ℕ} {mu : Tup Z.X.F Z.X.E Z.X.K S}
  {cst : LocCst Z.X (rowSG Z.Pr sel mu)} {u : Z.Pr.Word}

theorem T_mem (h : Hyp Z s cc δ χ cD sel S mu cst u) : Z.Pr.T u ∈ S := h.host (Or.inr ⟨u, rfl⟩)

theorem g_mem (h : Hyp Z s cc δ χ cD sel S mu cst u) (k : Fin 2) : Z.Pr.g k ∈ S := by
  apply h.host
  fin_cases k <;> simp [hostS]

theorem ram_mem (h : Hyp Z s cc δ χ cD sel S mu cst u) {p : ℕ} (hp : p.Prime) (hd : p ∣ H.host.condN) : p ∈ S := by
  rcases hp.dvd_mul.1 hd with h1 | h1
  · rcases hp.dvd_mul.1 h1 with h2 | h2
    · exact h.small p (Nat.mem_primeFactors.2 ⟨hp, h2, H.host.QS_pos.ne'⟩)
    · rw [(Nat.prime_dvd_prime_iff_eq hp H.host.hyp.1).1 h2]
      exact h.host (by simp [hostS])
  · rw [(Nat.prime_dvd_prime_iff_eq hp H.host.hyp.2.1).1 h1]
    exact h.host (by simp [hostS])

theorem moveHyp (h : Hyp Z s cc δ χ cD sel S mu cst u) {SG : Finset (HeightOneSpectrum (𝓞 Z.X.E))}
    (hSG : SG ⊆ rowSG Z.Pr sel mu) (P : Z.Pr.vT u) : MoveHyp (Z.Pr.vT u) SG P :=
  moveHyp_of_notMem h.ok.primes (fun w hw => T_notMem_rowSG mu h.ok.primes h.isSel h.T_mem w (hSG hw)) P

theorem alcoveAt (h : Hyp Z s cc δ χ cD sel S mu cst u) {j : ℕ} (hj : j ≤ Z.R.m) : AlcoveAt Z.W u j :=
  alcoveAt_of_sizes h.ok.sizes hj

end Hyp

open Classical in

theorem offBox_indicator {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) :
    InBoxOfRowSelection sel mu cst u N N' fun x => if x ∈ homAt (rowSG Pr sel mu) N N' then (1 : X.K) else 0 := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · have h : x ∈ homAt (rowSG Pr sel mu) N N' := by
      by_contra h
      exact hx (if_neg h)
    exact Submodule.smul_mem _ _ h
  · obtain ⟨z, hz, rfl⟩ := hy
    have h : ((cBof sel mu cst u : 𝓞 X.E) • (LinearMap.id : HomE X.E a b →ₗ[𝓞 X.E] HomE X.E a b)) z ∈
        homAt (rowSG Pr sel mu) N N' := Submodule.smul_mem _ _ hz
    simp only [Submodule.add_mem_iff_left _ h]

example {n : ℕ} (SB : Finset (HeightOneSpectrum (𝓞 X.E))) : Framed (SB := SB) (stdLat X.E n) fun _ => 1 := fun _ _ => Iff.rfl

example (hPr : Pr.Ok) (P : Pr.vT u) : MoveHyp (Pr.vT u) ∅ P ∧ MoveHyp (Pr.vT u) Pr.vGs P :=
  ⟨moveHyp_of_notMem hPr (by simp) P, moveHyp_of_ok hPr u P⟩

example (P : Pr.vT u) : ¬ MoveHyp (Pr.vT u) {P.1} P := fun h => (h.sg ⟨P.1, Finset.mem_singleton_self _⟩).1 rfl

theorem term_congr {SG₁ SG₂ SG₁' SG₂' : Finset (HeightOneSpectrum (𝓞 X.E))} (d₁ : DecoSet X.E (R.N i) (Pr.vT u) SG₁)
    (d₂ : DecoSet X.E (R.N i) (Pr.vT u) SG₂) (d₁' : DecoSet X.E (R.N j) (Pr.vT u) SG₁') (d₂' : DecoSet X.E (R.N j) (Pr.vT u) SG₂')
    (hN : d₁.1.N = d₂.1.N) (hf : d₁.1.f = d₂.1.f) (hN' : d₁'.1.N = d₂'.1.N) (hf' : d₁'.1.f = d₂'.1.f)
    (fr : Frs X.E (R.N i) (rowSG Pr sel mu)) (fr' : Frs X.E (R.N j) (rowSG Pr sel mu)) (Ξ₀ : HomE X.E (R.N i) (R.N j) → X.K) :
    term W Ch sel mu cst A u i j d₁ fr d₁' fr' Ξ₀ = term W Ch sel mu cst A u i j d₂ fr d₂' fr' Ξ₀ := by
  have h : phiT X.K d₁.1 d₁'.1 = phiT X.K d₂.1 d₂'.1 := by
    funext x
    unfold phiT Deco.at
    rw [hN, hf, hN', hf']
  unfold term
  rw [h, hN, hN']

example {SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet X.E (R.N i) (Pr.vT u) SG)
    (fr : Frs X.E (R.N i) (rowSG Pr sel mu)) (d' : DecoSet X.E (R.N j) (Pr.vT u) SG') (fr' : Frs X.E (R.N j) (rowSG Pr sel mu)) :
    term W Ch sel mu cst A u i j d fr d' fr' (fun _ => 0) = 0 := by
  simp [term, ker, kerOf, latSum]

end GlobalTheory.KerT
