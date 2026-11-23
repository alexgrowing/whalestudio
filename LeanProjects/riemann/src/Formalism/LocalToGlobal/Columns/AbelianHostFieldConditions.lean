import Mathlib
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataCoeff
import Formalism.LocalRingCardinality.SpanPowerMembership.FmZeroHLatEmpty
import Formalism.LocalToGlobal.UnitaryNorms.RealCyclotomicTwoPower
import Formalism.LocalToGlobal.UnitaryNorms.AdjoinCycZeta
import Formalism.LocalToGlobal.Divisibility.ConjugationAtDistinguishedPlace
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

open NumberField IsDedekindDomain IntermediateField

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.Host Formalism.L2.DIV Formalism.FrobeniusOrbits

structure Fields where

  F : Type

  E : Type

  K : Type
  [fieldF : Field F]
  [nfF : NumberField F]
  [fieldE : Field E]
  [nfE : NumberField E]
  [fieldK : Field K]
  [nfK : NumberField K]
  [algFE : Algebra F E]

  [starE : StarRing E]

  [starK : StarRing K]

  Tau : Type
  [ftTau : Fintype Tau]
  [deTau : DecidableEq Tau]

  emb : Tau → (E →+* K)

attribute [instance] Fields.fieldF Fields.nfF Fields.fieldE Fields.nfE Fields.fieldK Fields.nfK Fields.algFE
  Fields.starE Fields.starK Fields.ftTau Fields.deTau

namespace Fields

variable (X : Fields)

def f : ℕ := Fintype.card X.Tau

def sig : X.E →+* X.E := starRingEnd X.E

def conjO : 𝓞 X.E →+* 𝓞 X.E := RingOfIntegers.mapRingHom (starRingEnd X.E)

def embBar (τ : X.Tau) : X.E →+* X.K := (X.emb τ).comp (starRingEnd X.E)

def Kq : Subfield X.E where
  carrier := {x | ∀ τ τ' : X.Tau, X.emb τ x = X.emb τ' x}
  mul_mem' := by
    intro a b ha hb τ τ'
    rw [map_mul, map_mul, ha τ τ', hb τ τ']
  one_mem' := by
    intro τ τ'
    rw [map_one, map_one]
  add_mem' := by
    intro a b ha hb τ τ'
    rw [map_add, map_add, ha τ τ', hb τ τ']
  zero_mem' := by
    intro τ τ'
    rw [map_zero, map_zero]
  neg_mem' := by
    intro a ha τ τ'
    rw [map_neg, map_neg, ha τ τ']
  inv_mem' := by
    intro a ha τ τ'
    rw [map_inv₀, map_inv₀, ha τ τ']

structure Ok : Prop where

  realF : IsTotallyReal X.F

  rankE : Module.finrank X.F X.E = 2

  star_F : ∀ x : X.F, star (algebraMap X.F X.E x) = algebraMap X.F X.E x

  conjE : ∀ (φ : X.E →+* ℂ) (x : X.E), φ (star x) = starRingEnd ℂ (φ x)

  cplxE : IsTotallyComplex X.E

  emb_star : ∀ (τ : X.Tau) (x : X.E), X.emb τ (star x) = star (X.emb τ x)

  card_Tau : Fintype.card X.Tau = Module.finrank ℚ X.F

  emb_inj : Function.Injective X.emb

  emb_ne : ∀ τ τ' : X.Tau, X.emb τ ≠ X.embBar τ'

  emb_all : ∀ φ : X.E →+* X.K, ∃ τ : X.Tau, φ = X.emb τ ∨ φ = X.embBar τ

  cplxK : IsTotallyComplex X.K

  normalK : Normal ℚ X.K

  conjK : ∃ σ₀ : X.K →+* ℂ, ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)

  quad : Module.finrank ℚ X.Kq = 2

structure AbelianUnramifiedExtensionConditions : Prop where
  ok : X.Ok

  eight_dvd : 8 ∣ X.f

  galE : IsGalois ℚ X.E

  abelE : ∀ s t : X.E ≃ₐ[ℚ] X.E, s * t = t * s

  unram : ∀ P : HeightOneSpectrum (𝓞 X.E),
    ¬ (P.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E))).map (algebraMap (𝓞 X.F) (𝓞 X.E)) ≤ P.asIdeal ^ 2

variable {X} in

theorem AbelianUnramifiedExtensionConditions.f_even (h : X.AbelianUnramifiedExtensionConditions) : Even X.f := (even_iff_two_dvd).2 (dvd_trans (by norm_num) h.eight_dvd)

variable {X} in

theorem Ok.f_pos (h : X.Ok) : 0 < X.f := by
  show 0 < Fintype.card X.Tau
  rw [h.card_Tau]
  exact Module.finrank_pos

variable {X} in

theorem AbelianUnramifiedExtensionConditions.eight_le_f (h : X.AbelianUnramifiedExtensionConditions) : 8 ≤ X.f := Nat.le_of_dvd h.ok.f_pos h.eight_dvd

variable {X} in

theorem AbelianUnramifiedExtensionConditions.two_le_f (h : X.AbelianUnramifiedExtensionConditions) : 2 ≤ X.f := le_trans (by norm_num) h.eight_le_f

variable {X} in

theorem AbelianUnramifiedExtensionConditions.four_dvd_f (h : X.AbelianUnramifiedExtensionConditions) : 4 ∣ X.f := dvd_trans (by norm_num) h.eight_dvd

structure Core : Prop where
  realF : IsTotallyReal X.F
  rankE : Module.finrank X.F X.E = 2
  star_F : ∀ x : X.F, star (algebraMap X.F X.E x) = algebraMap X.F X.E x
  conjE : ∀ (φ : X.E →+* ℂ) (x : X.E), φ (star x) = starRingEnd ℂ (φ x)
  cplxE : IsTotallyComplex X.E
  emb_star : ∀ (τ : X.Tau) (x : X.E), X.emb τ (star x) = star (X.emb τ x)
  card_Tau : Fintype.card X.Tau = Module.finrank ℚ X.F
  emb_inj : Function.Injective X.emb
  emb_ne : ∀ τ τ' : X.Tau, X.emb τ ≠ X.embBar τ'
  emb_all : ∀ φ : X.E →+* X.K, ∃ τ : X.Tau, φ = X.emb τ ∨ φ = X.embBar τ
  conjK : ∃ σ₀ : X.K →+* ℂ, ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)
  quad : Module.finrank ℚ X.Kq = 2

variable {X} in
theorem Ok.core (h : X.Ok) : X.Core := ⟨h.realF, h.rankE, h.star_F, h.conjE, h.cplxE, h.emb_star, h.card_Tau, h.emb_inj, h.emb_ne,
  h.emb_all, h.conjK, h.quad⟩

def IsCond (N : ℕ) : Prop := ∀ j : X.E →ₐ[ℚ] Qb, Formalism.L2.Host.IsCond j.fieldRange N

def embC (σ₀ : X.K →+* ℂ) (τ : X.Tau) : X.E →+* ℂ := σ₀.comp (X.emb τ)

end Fields

open Classical in

def divs {A : Type} [CommRing A] [IsDedekindDomain A] (a : A) : Finset (HeightOneSpectrum A) :=
  if h : {P : HeightOneSpectrum A | a ∈ P.asIdeal}.Finite then h.toFinset else ∅

structure Primes (X : Fields) where

  cond : ℕ

  g : Fin 2 → ℕ

  piG : Fin 2 → 𝓞 X.E

  Word : Type
  [ftWord : Fintype Word]
  [deWord : DecidableEq Word]

  T : Word → ℕ

  piT : Word → 𝓞 X.E

attribute [instance] Primes.ftWord Primes.deWord

namespace Primes

variable {X : Fields} (Pr : Primes X)

def vT (u : Pr.Word) : Finset (HeightOneSpectrum (𝓞 X.E)) := divs (Pr.piT u)

def vTbar (u : Pr.Word) : Finset (HeightOneSpectrum (𝓞 X.E)) := divs (X.conjO (Pr.piT u))

def vG (i : Fin 2) : Finset (HeightOneSpectrum (𝓞 X.E)) := divs (X.conjO (Pr.piG i))

open Classical in

def vGs : Finset (HeightOneSpectrum (𝓞 X.E)) := Pr.vG 0 ∪ Pr.vG 1

structure Ok : Prop where

  g_prime : ∀ i, (Pr.g i).Prime

  piG_Kq : ∀ i, ((Pr.piG i : 𝓞 X.E) : X.E) ∈ X.Kq

  piG_norm : ∀ i, Pr.piG i * X.conjO (Pr.piG i) = (Pr.g i : 𝓞 X.E)

  piG_cop : ∀ i, IsCoprime (Pr.piG i) (X.conjO (Pr.piG i))

  vG_card : ∀ i, (Pr.vG i).card = X.f

  vG_norm : ∀ i, ∀ w ∈ Pr.vG i, Ideal.absNorm w.asIdeal = Pr.g i

  g_cong : ∀ i, Pr.g i ≡ 1 [MOD Pr.cond]

  g_ne : Pr.g 0 ≠ Pr.g 1

  T_prime : ∀ u, (Pr.T u).Prime

  piT_Kq : ∀ u, ((Pr.piT u : 𝓞 X.E) : X.E) ∈ X.Kq
  piT_norm : ∀ u, Pr.piT u * X.conjO (Pr.piT u) = (Pr.T u : 𝓞 X.E)

  piT_cop : ∀ u, IsCoprime (Pr.piT u) (X.conjO (Pr.piT u))

  vT_card : ∀ u, (Pr.vT u).card = X.f
  vT_norm : ∀ u, ∀ P ∈ Pr.vT u, Ideal.absNorm P.asIdeal = Pr.T u

  piT_cong : ∀ u, ((Pr.cond * (Pr.g 0 * Pr.g 1) ^ 2 : ℕ) : 𝓞 X.E) ∣ Pr.piT u - 1

  T_ne_g : ∀ u i, Pr.T u ≠ Pr.g i

def PiGCong : Prop := ∀ i, ((Pr.cond : ℕ) : 𝓞 X.E) ∣ Pr.piG i - 1

theorem natCast_dvd_intCast {E : Type} [Field E] [NumberField E] {c : ℕ} {n : ℤ} (h : ((c : ℕ) : 𝓞 E) ∣ ((n : ℤ) : 𝓞 E)) :
    (c : ℤ) ∣ n := by
  classical
  let b := NumberField.RingOfIntegers.basis E
  have hd := map_dvd (Algebra.norm ℤ) h
  have e1 : ((c : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (c : ℤ) := by simp
  have e2 : ((n : ℤ) : 𝓞 E) = algebraMap ℤ (𝓞 E) n := by simp
  rw [e1, e2, Algebra.norm_algebraMap_of_basis b, Algebra.norm_algebraMap_of_basis b] at hd
  have hpos : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) ≠ 0 := by
    rw [← Module.finrank_eq_card_basis b]
    exact Module.finrank_pos.ne'
  exact (Int.pow_dvd_pow_iff hpos).1 hd

variable {Pr} in

theorem PiGCong.g_cong (h : Pr.PiGCong) (hn : ∀ i, Pr.piG i * X.conjO (Pr.piG i) = (Pr.g i : 𝓞 X.E)) (i : Fin 2) :
    Pr.g i ≡ 1 [MOD Pr.cond] := by
  have hx := h i
  have hc : ((Pr.cond : ℕ) : 𝓞 X.E) ∣ X.conjO (Pr.piG i) - 1 := by
    have := map_dvd X.conjO hx
    rwa [map_sub, map_one, map_natCast] at this
  have hg : ((Pr.cond : ℕ) : 𝓞 X.E) ∣ (((Pr.g i : ℤ) - 1 : ℤ) : 𝓞 X.E) := by
    have he : (((Pr.g i : ℤ) - 1 : ℤ) : 𝓞 X.E)
        = (Pr.piG i - 1) * X.conjO (Pr.piG i) + (X.conjO (Pr.piG i) - 1) := by
      push_cast
      rw [← hn i]
      ring
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_left hx _) hc
  exact (Nat.modEq_iff_dvd.2 (natCast_dvd_intCast hg)).symm

end Primes

structure Chars (X : Fields) (Pr : Primes X) (m : ℕ) where

  psi0 : ∀ w : {w // w ∈ Pr.vGs}, AddChar (𝓞 X.E ⧸ w.1.asIdeal) X.K

  chi : Fin m → ∀ w : {w // w ∈ Pr.vGs}, (𝓞 X.E ⧸ w.1.asIdeal)ˣ →* X.Kˣ

  muVal : Fin m → HeightOneSpectrum (𝓞 X.E) → X.Kˣ

  etaVal : HeightOneSpectrum (𝓞 X.E) → X.Kˣ

namespace Chars

variable {X : Fields} {Pr : Primes X} {m : ℕ} (Ch : Chars X Pr m)

structure Ok : Prop where

  psi_zero_nontrivial_character : ∀ w, Ch.psi0 w ≠ 1

  chi_inj : ∀ w, Function.Injective fun j => Ch.chi j w

  chi_same : ∀ (i : Fin 2) (w w' : {w // w ∈ Pr.vGs}), w.1 ∈ Pr.vG i → w'.1 ∈ Pr.vG i →
    ∀ (j : Fin m) (a : ℤ) (x : (𝓞 X.E ⧸ w.1.asIdeal)ˣ) (x' : (𝓞 X.E ⧸ w'.1.asIdeal)ˣ),
      (x : 𝓞 X.E ⧸ w.1.asIdeal) = (a : 𝓞 X.E ⧸ w.1.asIdeal) →
      (x' : 𝓞 X.E ⧸ w'.1.asIdeal) = (a : 𝓞 X.E ⧸ w'.1.asIdeal) → Ch.chi j w x = Ch.chi j w' x'

  characterAgreesOnPlaces : ∀ (i : Fin 2) (w w' : {w // w ∈ Pr.vGs}), w.1 ∈ Pr.vG i → w'.1 ∈ Pr.vG i →
    ∀ a : ℤ, Ch.psi0 w (a : 𝓞 X.E ⧸ w.1.asIdeal) = Ch.psi0 w' (a : 𝓞 X.E ⧸ w'.1.asIdeal)

  chi_om : ∀ i : Fin 2, ∃ om : (ZMod (Pr.g i))ˣ →* X.Kˣ, Function.Injective om ∧
    ∀ w : {w // w ∈ Pr.vGs}, w.1 ∈ Pr.vG i → ∀ (j : Fin m) (a : (ZMod (Pr.g i))ˣ) (x : (𝓞 X.E ⧸ w.1.asIdeal)ˣ),
      (x : 𝓞 X.E ⧸ w.1.asIdeal) = (((a : ZMod (Pr.g i)).val : ℕ) : 𝓞 X.E ⧸ w.1.asIdeal) →
      Ch.chi j w x = om a ^ (2 * (j.1 + 1))

end Chars

structure IsEtaT (X : Fields) (σ₀ : X.K →+* ℂ) (χ : HChar X.E) : Prop where
  unitary : χ.IsUnitary
  unr : ∀ v, χ.UnrAt v
  res : χ.ResEta X.F
  inf : χ.HasInf (X.embC σ₀) (fun _ => 1)

structure IsMu0 {X : Fields} {Pr : Primes X} {m : ℕ} (Ch : Chars X Pr m) (σ₀ : X.K →+* ℂ) (e : X.Tau → ℚ) (j : Fin m)
    (χ : HChar X.E) : Prop where
  unitary : χ.IsUnitary
  triv : χ.TrivOn X.F
  inf : χ.HasInfQ (X.embC σ₀) (fun τ => -e τ)
  unr : ∀ v : HeightOneSpectrum (𝓞 X.E), (∀ i, ((Pr.g i : ℕ) : 𝓞 X.E) ∉ v.asIdeal) → χ.UnrAt v
  tame : ∀ v, χ.TameAt v
  atg : ∀ (w : {w // w ∈ Pr.vGs}) (x : X.Eˣ) (y : 𝓞 X.E) (c : (𝓞 X.E ⧸ w.1.asIdeal)ˣ), (x : X.E) = (y : X.E) →
    (c : 𝓞 X.E ⧸ w.1.asIdeal) = Ideal.Quotient.mk w.1.asIdeal y →
    ((χ.locK w.1 x : ℂˣ) : ℂ) = σ₀ (((Ch.chi j w c)⁻¹ : X.Kˣ) : X.K)

structure Chars.Tied {X : Fields} {Pr : Primes X} {m : ℕ} (Ch : Chars X Pr m) (σ₀ : X.K →+* ℂ) (e : Fin m → X.Tau → ℚ)
    (mu : Fin m → HChar X.E) (eta : HChar X.E) : Prop where
  mu0 : ∀ j, IsMu0 Ch σ₀ (e j) j (mu j)
  muVal : ∀ (j : Fin m) (v : HeightOneSpectrum (𝓞 X.E)), (∀ i, ((Pr.g i : ℕ) : 𝓞 X.E) ∉ v.asIdeal) →
    σ₀ (Ch.muVal j v : X.K) = (((mu j).val v : ℂˣ) : ℂ)
  etaT : IsEtaT X σ₀ eta
  etaVal : ∀ v : HeightOneSpectrum (𝓞 X.E), σ₀ (Ch.etaVal v : X.K) = eta.valTw (1 / 2) v

structure QDat (X : Fields) where

  Q : Finset (HeightOneSpectrum (𝓞 X.E))

  xi : ∀ P : {P // P ∈ Q}, (𝓞 X.E ⧸ P.1.asIdeal)ˣ →* X.Kˣ

namespace QDat

variable {X : Fields} (Z : QDat X)

def empty (X : Fields) : QDat X := ⟨∅, fun _ => 1⟩

structure Ok : Prop where

  deg_one : ∀ P ∈ Z.Q, (Ideal.absNorm P.asIdeal).Prime

  unram : ∀ P ∈ Z.Q, ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2

  one_over : ∀ P ∈ Z.Q, ∀ P' ∈ Z.Q, P'.asIdeal ≠ P.asIdeal.comap X.conjO

  xi_ne : ∀ P, Z.xi P ≠ 1

def Off (Pr : Primes X) : Prop :=
  ∀ P ∈ Z.Q, (∀ i, ((Pr.g i : ℕ) : 𝓞 X.E) ∉ P.asIdeal) ∧ ∀ u, ((Pr.T u : ℕ) : 𝓞 X.E) ∉ P.asIdeal

open Classical in

structure HasBase (p : ℕ) : Prop where
  prime : p.Prime
  all : (Z.Q.filter fun P => ((p : ℕ) : 𝓞 X.E) ∈ P.asIdeal).card = X.f
  ord : ∀ P : {P // P ∈ Z.Q}, ((p : ℕ) : 𝓞 X.E) ∈ P.1.asIdeal → orderOf (Z.xi P) = 15

structure TiedTo (ξ : Formalism.L2.DIV.Chr X.F X.E X.K) : Prop where
  places : ∀ v : HeightOneSpectrum (𝓞 X.F), v ∈ Formalism.L2.DIV.Qprime ξ ↔
    ∃ P ∈ Z.Q, P.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) = v.asIdeal
  res : ∀ P : {P // P ∈ Z.Q}, Z.xi P = Formalism.L2.DIV.resChar ξ P.1

end QDat

def shiftW {N : ℕ} (lam : DomWeight N) (c : ℤ) : DomWeight N where
  w := fun i => lam.w i + c
  anti := by
    intro i j hij
    have h := lam.anti hij
    simp only
    omega

theorem spread_shiftW {N : ℕ} (lam : DomWeight N) (c : ℤ) : (shiftW lam c).spread = lam.spread := by
  unfold DomWeight.spread
  split_ifs with h
  · simp only [shiftW]
    ring
  · rfl

open Classical in

def ofQ {N : ℕ} (x : Fin N → ℚ) : DomWeight N :=
  if h : Antitone x then ⟨fun i => ⌊x i⌋, fun _ _ hij => Int.floor_mono (h hij)⟩ else ⟨fun _ => 0, fun _ _ _ => le_rfl⟩

structure RowPar (R : Ranks) where
  v : Fin (R.k - 1) → ℚ
  b : Fin R.m → ℚ
  e : Fin R.m → ℚ

namespace RowPar

variable {R : Ranks}

def of (P : HCParam R) : RowPar R := ⟨P.v, P.b, P.e⟩

variable (S : RowPar R)

def bAt (n : ℕ) : ℚ := if h : n < R.m then S.b ⟨n, h⟩ else 0

def eAt (n : ℕ) : ℚ := if h : n < R.m then S.e ⟨n, h⟩ else 0

def vb (n : ℕ) : ℚ := if h : n < R.k - 1 then S.v ⟨n, h⟩ else -S.bAt (n - (R.k - 1))

def sgHC (n : ℕ) : ℚ :=
  ((R.m : ℚ) * ((R.t : ℚ) + 1)) / 2 +
  if h1 : n < R.k - 1 then S.v ⟨n, h1⟩
  else if (n - (R.k - 1)) % (R.t + 1) = 0 then -S.bAt ((n - (R.k - 1)) / (R.t + 1))
  else -S.eAt ((n - (R.k - 1)) / (R.t + 1)) + ((R.t : ℚ) - 1) / 2 - ((((n - (R.k - 1)) % (R.t + 1) : ℕ) : ℚ) - 1)

def sgQ (i : Fin (R.N R.m - 1)) : ℚ := S.sgHC i.1 - rhoVec (R.N R.m - 1) i

def sg : DomWeight (R.N R.m - 1) := ofQ S.sgQ

def sgTrue : DomWeight (R.N R.m - 1) := shiftW S.sg (-((R.m : ℤ) * (((R.t + 1) / 2 : ℕ) : ℤ)))

def pOf (R : Ranks) (j : ℕ) : ℕ := R.k + j - 1

def qOf (R : Ranks) (j : ℕ) : ℕ := R.m - j

def dV (j : ℕ) : ℚ := ((pOf R j : ℚ) - (qOf R j : ℚ)) / 2 - S.eAt (j - 1) - 1 / 2

def aPlus (j i : ℕ) : ℚ :=
  (S.vb (i - 1) + S.eAt (j - 1)) - ((R.nV : ℚ) + 1 - 2 * (i : ℚ)) / 2 - ((pOf R j : ℚ) - (qOf R j : ℚ)) / 2

def aMinusRev (j c : ℕ) : ℚ := (S.bAt (j + c - 1) - S.eAt (j - 1)) + (1 - (R.t : ℚ) - 2 * (c : ℚ)) / 2

def lamVQ (j : ℕ) (i : Fin R.nV) : ℚ :=
  (if i.1 < pOf R j then S.aPlus j (i.1 + 1)
   else if i.1 < pOf R j + R.t then 0
   else -S.aMinusRev j (i.1 - (pOf R j + R.t) + 1)) + S.dV j

def lamV (j : ℕ) : DomWeight R.nV := ofQ (S.lamVQ j)

end RowPar

structure Wts (X : Fields) (Word : Type) (R : Ranks) where

  row : X.Tau → RowPar R

  hc : Word → X.Tau → HCParam R

  tops : Finset X.Tau

namespace Wts

variable {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R)

structure Ok : Prop where

  row_ok : ∀ τ, ∃ P : HCParam R, RowPar.of P = W.row τ
  hc_row : ∀ u τ, RowPar.of (W.hc u τ) = W.row τ
  u_first : ∀ u u' τ (h : 0 < R.k), (W.hc u τ).u ⟨0, h⟩ = (W.hc u' τ).u ⟨0, h⟩
  u_last : ∀ u u' τ (h : R.k - 1 < R.k), (W.hc u τ).u ⟨R.k - 1, h⟩ = (W.hc u' τ).u ⟨R.k - 1, h⟩

def lamN (u : Word) (j : ℕ) (τ : X.Tau) : DomWeight (R.N j) := Examples₂.lamOf (W.hc u τ) j

def lamTrue (u : Word) (j : ℕ) (τ : X.Tau) : DomWeight (R.N j) :=
  shiftW (W.lamN u j τ) (-((j : ℤ) * (((R.t + 1) / 2 : ℕ) : ℤ)))

def nuW (u : Word) (j : ℕ) (τ : X.Tau) : DomWeight (R.N (j - 1)) :=
  shiftW (W.lamN u (j - 1) τ) ⌊wG R ((RowPar.of (W.hc u τ)).eAt (j - 1)) j⌋

def sgW (τ : X.Tau) : DomWeight (R.N R.m - 1) := (W.row τ).sg

def sgTrue (τ : X.Tau) : DomWeight (R.N R.m - 1) := (W.row τ).sgTrue

def lamV (j : ℕ) (τ : X.Tau) : DomWeight R.nV := (W.row τ).lamV j

def aTop (u : Word) (τ : X.Tau) : ℤ := (W.lamN u 0 τ).w ⟨0, R.N_pos 0⟩

def bTop (u : Word) (τ : X.Tau) : ℤ := -(W.lamN u 0 τ).detShift

def deg (u : Word) (τ : X.Tau) : ℤ := (∑ i, (W.lamN u R.m τ).w i) - ∑ i, (W.sgW τ).w i

def degTrue (u : Word) (τ : X.Tau) : ℤ := (∑ i, (W.lamTrue u R.m τ).w i) - ∑ i, (W.sgTrue τ).w i

end Wts

structure Sizes {X : Fields} (Pr : Primes X) {R : Ranks} (W : Wts X Pr.Word R) (a : ℝ) : Prop where

  g_big : ∀ i, 2 * X.f * R.k < Pr.g i - 1

  T_gt : ∀ u, 4 * a < (Pr.T u : ℝ)

  a_gt : ((2 * X.f * R.N R.m + 1 : ℕ) : ℝ) < 4 * a

  spread_le : ∀ u j, j ≤ R.m → ∀ τ, ((W.lamTrue u j τ).spread : ℝ) ≤ 2 * a

namespace Sizes

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {a : ℝ}

theorem a_pos (h : Sizes Pr W a) : 0 < a := by
  have h1 := h.a_gt
  have h2 : (0 : ℝ) ≤ ((2 * X.f * R.N R.m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

theorem T_big (h : Sizes Pr W a) (u : Pr.Word) : 2 * X.f * R.N R.m + 1 < Pr.T u := by
  have h1 := h.a_gt
  have h2 := h.T_gt u
  exact_mod_cast h1.trans h2

theorem spread_le_N (h : Sizes Pr W a) (u : Pr.Word) (j : ℕ) (hj : j ≤ R.m) (τ : X.Tau) :
    ((W.lamN u j τ).spread : ℝ) ≤ 2 * a := by
  have h1 := h.spread_le u j hj τ
  rwa [Wts.lamTrue, spread_shiftW] at h1

theorem two_spread_lt (h : Sizes Pr W a) (u : Pr.Word) (j : ℕ) (hj : j ≤ R.m) (τ : X.Tau) :
    2 * (W.lamTrue u j τ).spread < (Pr.T u : ℤ) := by
  have h1 := h.spread_le u j hj τ
  have h2 := h.T_gt u
  have h3 : (2 * (W.lamTrue u j τ).spread : ℝ) < (Pr.T u : ℝ) := by linarith
  exact_mod_cast h3

theorem T_spread (h : Sizes Pr W a) (u : Pr.Word) (j : ℕ) (hj : j ≤ R.m) (τ : X.Tau) :
    (W.lamN u j τ).spread < (Pr.T u : ℤ) := by
  have h1 := h.spread_le_N u j hj τ
  have h2 := h.T_gt u
  have h3 := h.a_pos
  have h4 : ((W.lamN u j τ).spread : ℝ) < (Pr.T u : ℝ) := by linarith
  exact_mod_cast h4

theorem T_spread_true (h : Sizes Pr W a) (u : Pr.Word) (j : ℕ) (hj : j ≤ R.m) (τ : X.Tau) :
    (W.lamTrue u j τ).spread < (Pr.T u : ℤ) := by
  have h1 := h.spread_le u j hj τ
  have h2 := h.T_gt u
  have h3 := h.a_pos
  have h4 : ((W.lamTrue u j τ).spread : ℝ) < (Pr.T u : ℝ) := by linarith
  exact_mod_cast h4

end Sizes

theorem two_le_N (R : Ranks) : 2 ≤ R.N R.m := by
  show 2 ≤ R.k + R.m * (R.t + 1)
  have := R.m_add_three_le_k
  exact le_add_right (by omega)

def Chars.FromHecke {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (W : Wts X Pr.Word R)
    (σ₀ : X.K →+* ℂ) : Prop :=
  ∃ (mu : Fin R.m → HChar X.E) (eta : HChar X.E), Ch.Tied σ₀ (fun j τ => (W.row τ).e j) mu eta

structure Dat where
  R : Ranks
  X : Fields

  sig0 : X.K →+* ℂ
  Pr : Primes X
  Ch : Chars X Pr R.m
  W : Wts X Pr.Word R

  a : ℝ

structure Dat.Ok (D : Dat) : Prop where
  fields : D.X.Ok

  fieldsConditions : D.X.AbelianUnramifiedExtensionConditions

  embeddingStarConj : ∀ x : D.X.K, D.sig0 (star x) = starRingEnd ℂ (D.sig0 x)

  f_eq : D.X.f = D.R.f
  primes : D.Pr.Ok

  piG_cong : D.Pr.PiGCong

  cond : D.X.IsCond D.Pr.cond
  chars : D.Ch.Ok

  hecke : D.Ch.FromHecke D.W D.sig0
  wts : D.W.Ok

  e_even : ∀ j : Fin D.R.m, ∃ z : ℤ, ∑ τ, (D.W.row τ).e j = 2 * (z : ℚ)
  sizes : Sizes D.Pr D.W D.a

theorem finite_pow_eq (n : ℕ) (hn : 0 < n) (a : Qb) : {z : Qb | z ^ n = a}.Finite := by
  classical
  refine (Polynomial.nthRoots n a).toFinset.finite_toSet.subset ?_
  intro z hz
  simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn]
  exact hz

theorem fin_adjoin {S : Set Qb} (hS : S.Finite) : FiniteDimensional ℚ (adjoin ℚ S) := by
  haveI : Finite S := hS.to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

theorem normal_of_map_le (L : Fld) (h : ∀ s : Qb ≃ₐ[ℚ] Qb, L.map (s : Qb →ₐ[ℚ] Qb) ≤ L) : Normal ℚ L := IntermediateField.normal_iff_forall_map_le'.2 h

theorem map_le_of_normal (L : Fld) [hL : Normal ℚ L] (s : Qb ≃ₐ[ℚ] Qb) : L.map (s : Qb →ₐ[ℚ] Qb) ≤ L := IntermediateField.normal_iff_forall_map_le'.1 hL s

theorem normal_adjoin {S : Set Qb} (hS : ∀ (s : Qb ≃ₐ[ℚ] Qb), ∀ x ∈ S, s x ∈ S) : Normal ℚ (adjoin ℚ S) := by
  apply normal_of_map_le
  intro s
  rw [IntermediateField.adjoin_map]
  refine IntermediateField.adjoin_le_iff.2 ?_
  rintro x ⟨y, hy, rfl⟩
  exact IntermediateField.subset_adjoin ℚ S (hS s y hy)

theorem normal_sup' (L M : Fld) [Normal ℚ L] [Normal ℚ M] : Normal ℚ (L ⊔ M : Fld) := by
  have e : (L ⊔ M : Fld) = IntermediateField.adjoin ℚ ((L : Set Qb) ∪ (M : Set Qb)) := by
    apply le_antisymm
    · exact sup_le (fun x hx => IntermediateField.subset_adjoin ℚ _ (Or.inl hx))
        (fun x hx => IntermediateField.subset_adjoin ℚ _ (Or.inr hx))
    · exact IntermediateField.adjoin_le_iff.2
        (Set.union_subset (fun x hx => (le_sup_left : L ≤ L ⊔ M) hx) (fun x hx => (le_sup_right : M ≤ L ⊔ M) hx))
  rw [e]
  refine normal_adjoin fun s x hx => ?_
  rcases hx with h | h
  · exact Or.inl (map_le_of_normal L s ((IntermediateField.mem_map _).2 ⟨x, h, rfl⟩))
  · exact Or.inr (map_le_of_normal M s ((IntermediateField.mem_map _).2 ⟨x, h, rfl⟩))

instance fin_sqQ (m : ℤ) : FiniteDimensional ℚ (sqQ m) := fin_adjoin (finite_pow_eq 2 (by norm_num) _)

instance normal_sqQ (m : ℤ) : Normal ℚ (sqQ m) := normal_adjoin fun s x hx => by
  show (s x) ^ 2 = (m : Qb)
  rw [← map_pow, show x ^ 2 = (m : Qb) from hx, map_intCast]

instance fin_F1Q (e : ℕ) : FiniteDimensional ℚ (realCyclotomicTwoPower e) :=
  fin_adjoin ((finite_pow_eq (2 ^ (e + 2)) (by positivity) 1).image _)

instance normal_F1Q (e : ℕ) : Normal ℚ (realCyclotomicTwoPower e) := normal_adjoin fun s x hx => by
  obtain ⟨z, hz, rfl⟩ := hx
  refine ⟨s z, ?_, ?_⟩
  · show (s z) ^ (2 ^ (e + 2)) = 1
    rw [← map_pow, show z ^ (2 ^ (e + 2)) = 1 from hz, map_one]
  · simp

instance fin_EQ (e q d : ℕ) : FiniteDimensional ℚ (EQ e q d) := by
  unfold EQ biquadraticField; infer_instance

instance normal_EQ (e q d : ℕ) : Normal ℚ (EQ e q d) := by
  unfold EQ biquadraticField
  have := normal_sup' (sqQ (-(q : ℤ))) (sqQ (-(d : ℤ)))
  exact normal_sup' _ _

instance fin_FQ (e q d : ℕ) : FiniteDimensional ℚ (FQ e q d) := by
  unfold FQ; infer_instance

theorem FQ_le_EQ (e q d : ℕ) : FQ e q d ≤ EQ e q d := by
  unfold FQ EQ
  apply sup_le_sup_right
  unfold sqQ
  rw [adjoin_le_iff]
  intro z hz
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq ((-(q : ℤ) : ℤ) : Qb) (n := 2) (by norm_num)
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq ((-(d : ℤ) : ℤ) : Qb) (n := 2) (by norm_num)
  have haE : a ∈ biquadraticField q d := (le_sup_left : sqQ (-(q : ℤ)) ≤ biquadraticField q d) (subset_adjoin ℚ _ ha)
  have hbE : b ∈ biquadraticField q d := (le_sup_right : sqQ (-(d : ℤ)) ≤ biquadraticField q d) (subset_adjoin ℚ _ hb)
  have hz2 : z ^ 2 = (a * b) ^ 2 := by
    rw [mul_pow, ha, hb, show z ^ 2 = (((q : ℤ) * (d : ℤ) : ℤ) : Qb) from hz]
    push_cast; ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hz2 with h | h
  · rw [h]; exact mul_mem haE hbE
  · rw [h]; exact neg_mem (mul_mem haE hbE)

open Classical in

def embQ {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) (g : φ.GG) : H.EQ →ₐ[ℚ] Qb :=
  if h : ∃ s : H.EQ →ₐ[ℚ] Qb, H.ActsAs s g then h.choose else H.EQ.val

instance fintypePsi (φ : Formalism.HC.Frame) : Fintype φ.Psi := Fintype.ofFinite _

def hostFields {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL]
    (hE : H.EQ ≤ LL) : Fields where
  F := H.FQ
  E := H.EQ
  K := CoF ι LL
  nfF := { to_charZero := inferInstance, to_finiteDimensional := H.fin_FQ }
  nfE := { to_charZero := inferInstance, to_finiteDimensional := H.fin_EQ }
  algFE := (inclusion H.FQ_le_EQ).toRingHom.toAlgebra
  starE := starLL ι H.EQ
  Tau := φ.Psi
  emb := fun g => (tauLL hE (embQ H (g : φ.GG))).toRingHom

open Classical in

def hostTops (φ : Formalism.HC.Frame) (TT : Finset φ.A) : Finset φ.Psi :=
  Finset.univ.filter fun g => (g : φ.GG) ∈ TT.image φ.tau1

end Formalism.L2.Col
