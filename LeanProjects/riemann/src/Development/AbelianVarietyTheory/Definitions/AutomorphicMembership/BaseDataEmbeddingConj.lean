import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

noncomputable section

open Formalism.L2.Col

@[reducible] def Base.fields (B : Base) : Fields where
  F := B.host.F
  E := B.host.E
  K := B.LL
  starE := B.host.cmStar
  Tau := Tau B.R
  deTau := Classical.decEq _
  emb := B.tauLL

@[reducible] def Base.primes (B : Base) (X : PreX B.toPre) : Primes B.fields where
  cond := B.host.QS * B.host.q * B.host.d
  g := B.host.g
  piG := X.piG
  Word := B.Word
  deWord := Classical.decEq _
  T := B.T
  piT := X.piT

open Classical in

@[reducible] def Base.wts (B : Base) : Wts B.fields B.Word B.R where
  row := fun τ => RowPar.of (B.hc τ)
  hc := B.hcW
  tops := Finset.univ.filter fun τ : Tau B.R => (τ : B.R.GG) ∈ B.host.topPlaces

@[reducible] def Base.dat (B : Base) (X : PreX B.toPre) (Ch : Chars B.fields (B.primes X) B.R.m) : Dat where
  R := B.R
  X := B.fields
  sig0 := B.embLL
  Pr := B.primes X
  Ch := Ch
  W := B.wts
  a := X.a

namespace Base

variable (B : Base)

theorem fields_star (x : B.host.E) : letI := B.fields.starE; star x = B.host.conj x := bridge_star_holds B.R B.host x

theorem fields_sig (x : B.host.E) : B.fields.sig x = B.host.conj x := bridge_star_holds B.R B.host x

theorem fields_emb_apply (τ : Tau B.R) (x : B.host.E) :
    B.fields.emb τ x = B.embE (B.host.sigmaOf (τ : B.R.GG) x) := rfl

theorem fields_f : B.fields.f = B.R.f := card_Tau B.host

theorem fields_embC (τ : Tau B.R) : B.fields.embC B.embLL τ = B.host.emb (τ : B.R.GG) := by
  unfold Fields.embC Host.emb
  rw [← B.embE_φ₀]
  rfl

theorem fields_conjO_coe (x : 𝓞 B.host.E) :
    ((B.fields.conjO x : 𝓞 B.host.E) : B.host.E) = B.host.conj (x : B.host.E) :=
  B.fields_star (x : B.host.E)

theorem primes_piGCong (X : PreX B.toPre) : (B.primes X).PiGCong := X.piG_cong

theorem primes_piG_norm (X : PreX B.toPre) (i : Fin 2) :
    (B.primes X).piG i * B.fields.conjO ((B.primes X).piG i) = ((B.primes X).g i : 𝓞 B.fields.E) := by
  apply RingOfIntegers.coe_injective
  have h := X.piG_norm i
  rw [← B.fields_conjO_coe] at h
  simpa using h

theorem primes_piT_norm (X : PreX B.toPre) (u : B.Word) :
    (B.primes X).piT u * B.fields.conjO ((B.primes X).piT u) = ((B.primes X).T u : 𝓞 B.fields.E) := by
  apply RingOfIntegers.coe_injective
  have h := X.piT_norm u
  rw [← B.fields_conjO_coe] at h
  simpa using h

theorem mem_wts_tops (τ : Tau B.R) : τ ∈ B.wts.tops ↔ (τ : B.R.GG) ∈ B.host.topPlaces := by
  classical
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem wts_isOk : B.wts.Ok where
  row_ok τ := ⟨B.hc τ, rfl⟩
  hc_row u τ := by
    show RowPar.of (B.hcW u τ) = RowPar.of (B.hc τ)
    unfold RowPar.of
    rw [B.hcW_v, B.hcW_b, B.hcW_e]
  u_first u u' τ h := (B.hcW_first u τ h).trans (B.hcW_first u' τ h).symm
  u_last u u' τ h := (B.hcW_last u τ (by omega)).trans (B.hcW_last u' τ (by omega)).symm

theorem primes_sizes (X : PreX B.toPre) : Sizes (B.primes X) B.wts X.a where
  g_big i := by rw [B.fields_f]; exact X.g_big i
  T_gt := X.T_gt
  a_gt := by rw [B.fields_f]; exact X.a_gt
  spread_le u j hj τ := by
    unfold Wts.lamTrue
    rw [spread_shiftW]
    exact X.spread_le u j hj τ

theorem baseData_embedding_conj (X : PreX B.toPre) (Ch : Chars B.fields (B.primes X) B.R.m) (x : (B.dat X Ch).X.K) :
    (B.dat X Ch).sig0 (star x) = starRingEnd ℂ ((B.dat X Ch).sig0 x) := B.starLL_cx x

theorem dat_e_even (X : PreX B.toPre) (Ch : Chars B.fields (B.primes X) B.R.m) (j : Fin (B.dat X Ch).R.m) :
    ∃ z : ℤ, ∑ τ, ((B.dat X Ch).W.row τ).e j = 2 * (z : ℚ) := (X.e_even j).even

end Base

example (B : Base) : B.fields.f = 2 * B.R.n := B.fields_f

example (B : Base) (X : PreX B.toPre) (i : Fin 2) : B.host.g i ≡ 1 [MOD B.host.QS * B.host.q * B.host.d] :=
  (B.primes_piGCong X).g_cong (B.primes_piG_norm X) i

example (B : Base) (X : PreX B.toPre) (Ch : Chars B.fields (B.primes X) B.R.m) (u : B.Word) :
    0 < (B.dat X Ch).a ∧ 2 * B.fields.f * B.R.N B.R.m + 1 < B.T u :=
  ⟨(B.primes_sizes X).a_pos, (B.primes_sizes X).T_big u⟩

end

end GlobalTheory.Mem
