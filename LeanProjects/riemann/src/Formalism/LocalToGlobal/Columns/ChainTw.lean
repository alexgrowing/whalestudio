import Formalism.LocalToGlobal.Columns.ChainOneOk

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwDC

variable {X : Fields} {Pr : Primes X} {R : Ranks}

def TwBdd (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) : Prop :=
  ∀ x ∈ lamYat (Pr := Pr) (R := R) j P, h⁻¹ x ∈ lamYat (Pr := Pr) (R := R) j P ∧
    ((qOf P : X.E) ^ j) • h x ∈ lamYat (Pr := Pr) (R := R) j P

def TwNF (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) : Prop :=
  ∃ (n : ℕ → ℤ) (z : Sp X.E (R.N j)), (∀ i, -(j : ℤ) ≤ n i ∧ n i ≤ 0) ∧ z ∈ stdAt X.E (R.N j) P ∧
    ∀ v : Sp X.E (R.N j + cOf R j), h⁻¹ v ∈ lamYat (Pr := Pr) (R := R) j P ↔
      (∀ l : Fin (R.N j), IntAt P (v (Fin.castAdd _ l) - Loc.atN v (R.N j) * z l)) ∧
        ∀ i : Fin (cOf R j), IntAt P (((qOf P : X.E) ^ n i.1)⁻¹ * v (Fin.natAdd _ i))

theorem twDC_refl (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) :
    SameDC (Pr := Pr) sharp j P h h :=
  ⟨1, (Loc.R1 X.E (R.N j) (cOf R j)).one_mem, 1, (Jat (Pr := Pr) sharp j P).one_mem, by simp⟩

theorem twDC_symm {sharp : Bool} {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} {h h' : AutY X R j}
    (H : SameDC (Pr := Pr) sharp j P h h') : SameDC (Pr := Pr) sharp j P h' h := by
  obtain ⟨r, hr, κ, hκ, rfl⟩ := H
  exact ⟨r⁻¹, inv_mem hr, κ⁻¹, inv_mem hκ, by simp [mul_assoc]⟩

theorem twDC_trans {sharp : Bool} {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} {h h' h'' : AutY X R j}
    (H : SameDC (Pr := Pr) sharp j P h h') (H' : SameDC (Pr := Pr) sharp j P h' h'') : SameDC (Pr := Pr) sharp j P h h'' := by
  obtain ⟨r, hr, κ, hκ, rfl⟩ := H
  obtain ⟨r', hr', κ', hκ', rfl⟩ := H'
  exact ⟨r' * r, mul_mem hr' hr, κ * κ', mul_mem hκ hκ', by simp [mul_assoc]⟩

def twSetoid (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) : Setoid (AutY X R j) where
  r := SameDC (Pr := Pr) sharp j P
  iseqv := ⟨twDC_refl sharp j P, twDC_symm, twDC_trans⟩

structure TwSt (X : Fields) (Pr : Primes X) (R : Ranks) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) (j : ℕ) : Type 1 where
  β : Type
  [fin : Fintype β]
  h : β → uSG Pr.vGs Q → AutY X R j

attribute [instance] TwSt.fin

def twUnitSt (Q : Finset (HeightOneSpectrum (𝓞 X.E))) (j : ℕ) : TwSt X Pr R Q j where
  β := Unit
  h _ _ := 1

def twEmptySt (Q : Finset (HeightOneSpectrum (𝓞 X.E))) (j : ℕ) : TwSt X Pr R Q j where
  β := Empty
  h e := e.elim

end TwDC

section TwIdx

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

open Classical

abbrev twQOff : Finset (HeightOneSpectrum (𝓞 X.E)) := QE sel (mu : Chr X.F X.E X.K) \ Pr.vGs

def twRow {sel} {mu : Tup X.F X.E X.K S} (P : twQOff (Pr := Pr) sel mu) : rowSG Pr sel mu :=
  ⟨P.1, Finset.mem_union_right _ (Finset.mem_sdiff.1 P.2).1⟩

def TwCand {i : ℕ} (st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i) (P : twQOff (Pr := Pr) sel mu) (h : AutY X R (i + 1)) : Prop :=
  TwBdd (Pr := Pr) (i + 1) P.1 h ∧ ∃ al : st.β, FiniteSumNonzeroLargeDepth Ch sel mu cst i (twRow P) (st.h al (twRow P)) h

def twCSet {i : ℕ} (st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i) (P : twQOff (Pr := Pr) sel mu) :
    Set (Quotient (twSetoid (Pr := Pr) (R := R) cst.sharp (i + 1) P.1)) :=
  {D | ∃ h, Quotient.mk _ h = D ∧ TwCand Ch sel mu cst st P h}

open Classical in

def twCFin {i : ℕ} (st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i) (P : twQOff (Pr := Pr) sel mu) :
    Finset (Quotient (twSetoid (Pr := Pr) (R := R) cst.sharp (i + 1) P.1)) :=
  if hf : (twCSet Ch sel mu cst st P).Finite then hf.toFinset else ∅

def twRep {i : ℕ} (st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i) (P : twQOff (Pr := Pr) sel mu)
    (D : Quotient (twSetoid (Pr := Pr) (R := R) cst.sharp (i + 1) P.1)) : AutY X R (i + 1) :=
  @Classical.epsilon _ ⟨1⟩ fun h => Quotient.mk _ h = D ∧ TwCand Ch sel mu cst st P h ∧ TwNF (Pr := Pr) (i + 1) P.1 h ∧
    prCat (Pr := Pr) cst.sharp (i + 1) P.1 h ≤ GLint X.E (R.N (i + 1)) P.1

open Classical in

def twNext {i : ℕ} (st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i) : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) (i + 1) where
  β := {d : ∀ P : twQOff (Pr := Pr) sel mu, ↥(twCFin Ch sel mu cst st P) //
    ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → ∃ al : st.β, FiniteSumNonzeroLargeDepth Ch sel mu cst i P (st.h al P) 1}
  h d P := if hP : P.1 ∈ twQOff (Pr := Pr) sel mu then twRep Ch sel mu cst st ⟨P.1, hP⟩ (d.1 ⟨P.1, hP⟩).1 else 1

def twSt (m2 : ℕ) : (j : ℕ) → TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) j
  | 0 => twUnitSt _ 0
  | i + 1 => if i + 1 ≤ m2 then twNext Ch sel mu cst (twSt m2 i)
      else if i + 1 = m2 + 1 then twUnitSt _ (i + 1) else twEmptySt _ (i + 1)

def TwChrOk (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) : Prop :=
  (∀ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) h, chiInv Ch sel mu cst j P h r ≠ 0) ∧
  ∀ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) h, ∀ r' ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) h,
    ∀ r'' ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) h,
    (∀ x, r'' (Loc.inX X.E (R.N j) (cOf R j) x) = r (r' (Loc.inX X.E (R.N j) (cOf R j) x))) →
      chiInv Ch sel mu cst j P h r'' = chiInv Ch sel mu cst j P h r * chiInv Ch sel mu cst j P h r'

def twChiVal (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) (g : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) : X.K :=
  chiInv Ch sel mu cst j P h (@Classical.epsilon _ ⟨1⟩ fun r => r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) h ∧
    ∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g x))

variable {Ch sel mu cst} in
theorem twChiVal_spec {j : ℕ} {P : rowSG Pr sel mu} {h : AutY X R j} {g : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)}
    (hg : g ∈ prCat (Pr := Pr) cst.sharp j P.1 h) :
    ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) h, (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g x)) ∧
      twChiVal Ch sel mu cst j P h g = chiInv Ch sel mu cst j P h r := by
  obtain ⟨r, hr, hx⟩ := hg
  have hs := @Classical.epsilon_spec _ (fun r => r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) h ∧
    ∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g x)) ⟨r, hr, hx⟩
  exact ⟨_, hs.1, hs.2, rfl⟩

variable {Ch sel mu cst} in

theorem twChiVal_eq {j : ℕ} {P : rowSG Pr sel mu} {h : AutY X R j} (hok : TwChrOk Ch sel mu cst j P h)
    {g : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)} {r : AutY X R j} (hr : r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) h)
    (hx : ∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g x)) :
    twChiVal Ch sel mu cst j P h g = chiInv Ch sel mu cst j P h r := by
  obtain ⟨r₀, hr₀, hx₀, he⟩ := twChiVal_spec (Ch := Ch) (g := g) ⟨r, hr, hx⟩
  have one := (Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) h).one_mem
  have h1 : chiInv Ch sel mu cst j P h 1 = 1 := by
    have e := hok.2 1 one 1 one 1 one (fun _ => rfl)
    have ne := hok.1 1 one
    have : chiInv Ch sel mu cst j P h 1 * (chiInv Ch sel mu cst j P h 1 - 1) = 0 := by rw [mul_sub, mul_one, ← e, sub_self]
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 ne
    · exact sub_eq_zero.1 h0
  have e := hok.2 r₀ hr₀ 1 one r hr (fun x => by rw [hx]; exact (hx₀ x).symm)
  rw [he, e, h1, mul_one]

open Classical in

def twLam (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) :
    ↥((prCat (Pr := Pr) cst.sharp j P.1 h).subgroupOf (GLint X.E (R.N j) P.1)) →* X.Kˣ :=
  if hok : TwChrOk Ch sel mu cst j P h then
    { toFun := fun g => Units.mk0 (twChiVal Ch sel mu cst j P h g.1.1) (by
        obtain ⟨r, hr, -, he⟩ := twChiVal_spec (Ch := Ch) (Subgroup.mem_subgroupOf.1 g.2)
        rw [he]; exact hok.1 r hr)
      map_one' := by
        apply Units.ext
        show twChiVal Ch sel mu cst j P h 1 = 1
        have one := (Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) h).one_mem
        rw [twChiVal_eq hok one (fun _ => rfl)]
        have e := hok.2 1 one 1 one 1 one (fun _ => rfl)
        have ne := hok.1 1 one
        have : chiInv Ch sel mu cst j P h 1 * (chiInv Ch sel mu cst j P h 1 - 1) = 0 := by rw [mul_sub, mul_one, ← e, sub_self]
        rcases mul_eq_zero.1 this with h0 | h0
        · exact absurd h0 ne
        · exact sub_eq_zero.1 h0
      map_mul' := fun a b => by
        apply Units.ext
        show twChiVal Ch sel mu cst j P h (a.1.1 * b.1.1) = twChiVal Ch sel mu cst j P h a.1.1 * twChiVal Ch sel mu cst j P h b.1.1
        obtain ⟨r, hr, hx, he⟩ := twChiVal_spec (Ch := Ch) (Subgroup.mem_subgroupOf.1 a.2)
        obtain ⟨s, hs, hy, hf⟩ := twChiVal_spec (Ch := Ch) (Subgroup.mem_subgroupOf.1 b.2)
        have hrs : ∀ x, (r * s) (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) ((a.1.1 * b.1.1) x) := fun x => by
          show r (s _) = _
          rw [hy, hx]; rfl
        rw [twChiVal_eq hok (mul_mem hr hs) hrs, he, hf]
        exact hok.2 r hr s hs (r * s) (mul_mem hr hs) (fun _ => rfl) }
  else 1

def twLevQ (j : ℕ) (hh : rowSG Pr sel mu → AutY X R j) : LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)) := fun P =>
  ⟨(prCat (Pr := Pr) cst.sharp j P.1 (hh ⟨P.1, Finset.mem_union_right _ P.2⟩)).subgroupOf (GLint X.E (R.N j) P.1),
    twLam Ch sel mu cst j ⟨P.1, Finset.mem_union_right _ P.2⟩ (hh ⟨P.1, Finset.mem_union_right _ P.2⟩)⟩

open Classical in

def twIdx (m2 : ℕ) : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)) where
  β j := (twSt Ch sel mu cst m2 j).β
  finβ j := (twSt Ch sel mu cst m2 j).fin
  decβ _ := Classical.decEq _
  h j b := (twSt Ch sel mu cst m2 j).h b
  levG j _ := colLevSym Ch j
  levQ j b := if j = 0 then LevQFam.top X.E X.K (R.N j) _ else twLevQ Ch sel mu cst j ((twSt Ch sel mu cst m2 j).h b)

end TwIdx

section TwCst

variable {X : Fields} {Pr : Primes X} {R : Ranks}

def twZeta (σ₀ : X.K →+* ℂ) (N : ℕ) : X.K :=
  @Classical.epsilon _ ⟨1⟩ fun z => σ₀ z = Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))

open Classical in

def twPsiQ (σ₀ : X.K →+* ℂ) (xi0 : X.E) (P : HeightOneSpectrum (𝓞 X.E)) (D : ℕ) (a : X.E) : X.K :=
  if hb : ∃ b : ℤ, IntAt P ((qOf P : X.E) ^ D * a) ∧ IntAt P (xi0 * a - (b : X.E) / (qOf P : X.E) ^ D) then
    twZeta σ₀ (qOf P ^ D) ^ hb.choose else 1

def twSqrt (P : HeightOneSpectrum (𝓞 X.E)) : X.K := @Classical.epsilon _ ⟨1⟩ fun z => z ^ 2 = (qOf P : X.K)

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

open Classical

open Classical in

def twMuq (G : ChGlob X R.m) (j : ℕ) (P : rowSG Pr sel mu) : X.K :=
  if P.1 ∈ Pr.vGs then ciMuq G (mu : Chr X.F X.E X.K) j P
  else if hj : j - 1 < R.m then (((Ch.muVal ⟨j - 1, hj⟩ P.1)⁻¹ * (qValC (mu : Chr X.F X.E X.K) P.1)⁻¹ : X.Kˣ) : X.K) else 1

open Classical in

def twCst (G : ChGlob X R.m) : LocCst X (rowSG Pr sel mu) where
  psi P := if P.1 ∈ Pr.vGs then ciPsi Ch P else twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m)
  D P := if P.1 ∈ Pr.vGs then 1 else 2 * R.m
  sq P := if P.1 ∈ Pr.vGs then ciSq Ch P.1 else twSqrt P.1
  muq := twMuq Ch sel mu G
  A := R.m + 1
  B := R.m + 1
  M := R.m
  sharp := true

end TwCst

end Formalism.L2.Col
