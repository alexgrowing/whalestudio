import Mathlib
import Formalism.LocalToGlobal.Columns.UnipotentRightActionFunctionsW
import Formalism.LocalToGlobal.Columns.HeckeSpCount
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.LocalToGlobal.Columns.MemWmPerp
import Formalism.LocalToGlobal.Columns.GSetLemmas

open NumberField IsDedekindDomain Module Polynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Nb

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (V : Type) [AddCommGroup V] [Module X.K V]

theorem trF_nbFun (a : GLG X.E n SG) (P : Ideal (𝓞 X.E)) (i : ℕ) (ψ : DecoSet X.E n ST SG → V) :
    trF X n ST SG V a (nbFun X.K V P i ψ) = nbFun X.K V P i (trF X n ST SG V a ψ) := by
  funext d
  rw [trF_apply]
  show ∑ d₁ ∈ ((((1 : UF X.E n), a⁻¹) : UF X.E n × GLG X.E n SG) • d).heckeNb P i, ψ d₁ =
    ∑ d₁ ∈ d.heckeNb P i, ψ ((((1 : UF X.E n), a⁻¹) : UF X.E n × GLG X.E n SG) • d₁)
  set g : UF X.E n × GLG X.E n SG := ((1 : UF X.E n), a⁻¹)
  refine Finset.sum_nbij' (fun e => g⁻¹ • e) (fun e => g • e) ?_ ?_ ?_ ?_ ?_
  · intro e he
    have : g • (g⁻¹ • e) ∈ (g • d).heckeNb P i := by rwa [smul_inv_smul]
    exact (DecoSet.smul_mem_heckeNb_iff g).1 this
  · intro e he
    exact (DecoSet.smul_mem_heckeNb_iff g).2 he
  · intro e _
    exact smul_inv_smul g e
  · intro e _
    exact inv_smul_smul g e
  · intro e _
    rw [smul_inv_smul]

end Nb

section Poly

variable {L : Type} [Field L]

end Poly

section HV

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end HV

section FromRel

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end FromRel

section Inh

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
  {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

def wmTh0 : WmTh E K a b SG K K := fun _ _ _ =>
  { toFun := fun Φ => Φ 0 • LinearMap.id
    map_add' := fun Φ Ψ => by simp [add_smul]
    map_smul' := fun c Φ => by simp [smul_smul] }

end Inh

section Fub

variable {K : Type} [Field K] [NumberField K] [StarRing K]

end Fub

section Rev

open Pointwise

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def DecoSet.revSet (P : Ideal (𝓞 E)) (i : ℕ) (d₁ : DecoSet E n ST SG) : Set (DecoSet E n ST SG) :=
  {d | d₁ ∈ d.heckeSet P i}

open Classical in

def DecoSet.revNb (P : Ideal (𝓞 E)) (i : ℕ) (d₁ : DecoSet E n ST SG) : Finset (DecoSet E n ST SG) :=
  if h : (d₁.revSet P i).Finite then h.toFinset else ∅

end Rev

section PhiLem

open Pointwise

variable {E : Type} [Field E] [NumberField E] [StarRing E] {SG : Finset (HeightOneSpectrum (𝓞 E))}

variable {K : Type} [Field K] {a b : ℕ}

open Classical in

theorem WmSchw.insert {S : Finset (HeightOneSpectrum (𝓞 E))} {Φ : (Sp E a →ₗ[E] Sp E b) → K} (hΦ : WmSchw S Φ)
    (P : HeightOneSpectrum (𝓞 E)) (hP : P ∉ S) {N' : Submodule (𝓞 E) (Sp E a)} {N : Submodule (𝓞 E) (Sp E b)}
    (hN' : Submodule.IsLattice E N') (hN : Submodule.IsLattice E N) :
    WmSchw (insert P S) (fun x => open Classical in if wmIntAt P N' N x then Φ x else 0) := by
  classical
  obtain ⟨A', B', A, B, hl, hper, hsupp⟩ := hΦ
  refine ⟨fun Q => if Q = P then N' else A' Q, fun Q => if Q = P then N' else B' Q,
    fun Q => if Q = P then N else A Q, fun Q => if Q = P then N else B Q, ?_, ?_, ?_⟩
  · intro Q hQ
    by_cases e : Q = P
    · simp only [if_pos e]
      exact ⟨hN', hN, hN', hN⟩
    · simp only [if_neg e]
      exact hl Q ((Finset.mem_insert.1 hQ).resolve_left e)
  · intro x y hy
    have hyP : wmIntAt P N' N y := by simpa using hy P (Finset.mem_insert_self P S)
    have hyS : ∀ Q ∈ S, wmIntAt Q (A' Q) (A Q) y := by
      intro Q hQ
      have hne : Q ≠ P := fun e => hP (e ▸ hQ)
      simpa [hne] using hy Q (Finset.mem_insert_of_mem hQ)
    have hiff : wmIntAt P N' N (x + y) ↔ wmIntAt P N' N x := by
      constructor
      · intro h z hz
        have := Submodule.sub_mem _ (h z hz) (hyP z hz)
        simpa using this
      · intro h z hz
        rw [LinearMap.add_apply]
        exact Submodule.add_mem _ (h z hz) (hyP z hz)
    simp only [hiff, hper x y hyS]
  · intro x hx Q hQ
    by_cases hint : wmIntAt P N' N x
    · have hx' : Φ x ≠ 0 := by simpa [hint] using hx
      by_cases e : Q = P
      · simp only [if_pos e]
        exact e ▸ hint
      · simp only [if_neg e]
        exact hsupp x hx' Q ((Finset.mem_insert.1 hQ).resolve_left e)
    · exact absurd (by simp [hint]) hx

end PhiLem

section Gauss

variable {L : Type} [Field L]

end Gauss

section Count

variable (E : Type) [Field E] [NumberField E] [StarRing E]

open Classical in

def WmCount : Prop :=
  ∀ {a b : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))} (P : HeightOneSpectrum (𝓞 E)), conjPrime₂ P ≠ P → P ∉ SG → conjPrime₂ P ∉ SG →
    ∀ (d' : DecoSet E a ∅ SG) (d₁ : DecoSet E b ∅ SG) (x : Sp E a →ₗ[E] Sp E b),
      ∃ ρ, ρ ≤ a ∧ ρ ≤ b ∧ ∀ i j,
        ((d₁.revNb P.asIdeal i).filter fun d => wmIntAt P d'.1.N d.1.N x).card =
          (if wmIntAt P d'.1.N d₁.1.N x then gaussBin (Nat.card (𝓞 E ⧸ P.asIdeal)) (b - ρ) i else 0) ∧
        ((d'.heckeNb P.asIdeal j).filter fun d'₁ => wmIntAt P d'₁.1.N d₁.1.N x).card =
          (if wmIntAt P d'.1.N d₁.1.N x then gaussBin (Nat.card (𝓞 E ⧸ P.asIdeal)) (a - ρ) j else 0)

end Count

section ClassRel

open Classical

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
  {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

end ClassRel

section RelOf

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

def WmKerInv (th : ThM W Ch sel mu (rKg X Pr R)) : Prop :=
  ∀ (g : (mtKGSD W Ch sel mu R.m).G) (d : (mtKGSD W Ch sel mu R.m).D) (d' : (wmKGSD W sel mu).D) (x : (mtKGSD W Ch sel mu R.m).V),
    wmKer W Ch sel mu (rKg X Pr R) th (g • d) d' ((mtKGSD W Ch sel mu R.m).ρ g x) =
      wmKer W Ch sel mu (rKg X Pr R) th d d' x

end RelOf

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end Main

end Formalism.L2.Col
