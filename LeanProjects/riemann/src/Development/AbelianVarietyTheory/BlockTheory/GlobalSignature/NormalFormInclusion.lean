import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.NormalFormInclusion

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Lattice

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def nfVec (q : ℕ) (n c : ℕ) (ex : Fin c → ℤ) (z : Sp E n) (i : Fin c) : Sp E (n + c) :=
  ((q : E) ^ ex i) • (Loc.eN E (n + c) (n + i.1) + if i.1 = 0 then Loc.inX E n c z else 0)

def nfLat (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (n c : ℕ) (ex : Fin c → ℤ) (z : Sp E n) : Submodule (𝓞 E) (Sp E (n + c)) :=
  (stdAt E n P).map ((Loc.inX E n c).restrictScalars (𝓞 E)) ⊔
    (stdAt E c P).map ((Fintype.linearCombination E (nfVec q n c ex z)).restrictScalars (𝓞 E))

end Lattice

variable {X : Fields} {R : Ranks}

def NF (Pr : Primes X) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) : Prop :=
  ∃ (ex : Fin (cOf R j) → ℤ) (z : Sp X.E (R.N j)),
    (∀ i, -(j : ℤ) ≤ ex i ∧ ex i ≤ 0) ∧
    z ∈ stdAt X.E (R.N j) P ∧
    gmap h (lamYat (Pr := Pr) (R := R) j P) = nfLat P (qOf P) (R.N j) (cOf R j) ex z

def NFIncl (X : Fields) (Pr : Primes X) (R : Ranks) : Prop :=
  ∀ (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ h : AutY X R j, NF Pr j P h →
    ∀ k ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P),
      lamYat (Pr := Pr) (R := R) j P ≤ gmap (h * k : AutY X R j) (lamYat (Pr := Pr) (R := R) j P) ∧
      ∀ x ∈ lamYat (Pr := Pr) (R := R) j P, ((qOf P : X.E) ^ j) • (h * k : AutY X R j) x ∈ lamYat (Pr := Pr) (R := R) j P

section Chain

variable {Pr : Primes X} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

def PsiReads (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) : Prop :=
  ∃ d : ℕ,
    (∀ x y : X.E, IntAt P.1 ((qOf P.1 : X.E) ^ d * x) → IntAt P.1 ((qOf P.1 : X.E) ^ d * y) →
      cst.psi P (x + y) = cst.psi P x * cst.psi P y) ∧
    ∀ x ∈ lamYat (Pr := Pr) (R := R) j P.1, ((qOf P.1 : X.E) ^ d) • h x ∈ lamYat (Pr := Pr) (R := R) j P.1

def RepExists : Prop :=
  cst.Ok → ∀ i : ℕ, i + 1 ≤ R.m - 2 → ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → DegOne P.1 →
    ∀ hal : AutY X R i, NF Pr i P.1 hal →
    ∀ h h₁ : AutY X R (i + 1), SameDC (Pr := Pr) cst.sharp (i + 1) P.1 h h₁ → PsiReads sel mu cst (i + 1) P h₁ →
      FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h₁ →
      ∃ h' : AutY X R (i + 1), SameDC (Pr := Pr) cst.sharp (i + 1) P.1 h h' ∧ NF Pr (i + 1) P.1 h'

def IdxNF (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ R.m - 2 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs → NF Pr j P.1 (L.h j b P)

def ChoiceExists : Prop :=
  (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → DegOne P.1) →
  ∀ (G : ChGlob X R.m) (m2 : ℕ) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))), L.Ok Ch sel mu cst G m2 →
    ∃ (h' : ∀ j, L.β j → rowSG Pr sel mu → AutY X R j)
      (lq : ∀ j, L.β j → LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K))) (A₀ B₀ : ℕ),
      (∀ j b P, SameDC (Pr := Pr) cst.sharp j P.1 (L.h j b P) (h' j b P)) ∧
      (∀ j b (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → h' j b P = L.h j b P) ∧
      IdxNF sel mu { L with h := h', levQ := lq } ∧
      ∀ A' B' : ℕ, A₀ ≤ A' → B₀ ≤ B' →
        ChIdx.Ok Ch sel mu { cst with A := A', B := B' } { L with h := h', levQ := lq } G m2

end Chain

def NormalFormAtQ : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks), NFIncl X Pr R ∧
    ∀ (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
      (cst : LocCst X (rowSG Pr sel mu)), RepExists Ch sel mu cst ∧ ChoiceExists Ch sel mu cst

theorem nf_one (Pr : Primes X) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (hP : P ∉ Pr.vGs) : NF Pr j P (1 : AutY X R j) := by
  classical
  refine ⟨fun _ => 0, 0, fun _ => ⟨by simp, le_rfl⟩, zero_mem _, ?_⟩
  have hL : ∀ y, y ∈ lamYat (Pr := Pr) (R := R) j P ↔ ∀ l, IntAt P (y l) := by
    intro y
    unfold lamYat LocE.lamY LocE.sclLat stdAt
    rw [if_neg hP, Submodule.mem_comap, mem_localization_standardLattice]
    refine forall_congr' fun l => ?_
    simp [LocE.scE]
  have hg : gmap (1 : AutY X R j) (lamYat (Pr := Pr) (R := R) j P) = lamYat (Pr := Pr) (R := R) j P := by
    ext y
    simp [gmap, Submodule.mem_map]
  have h0 : IntAt P (0 : X.E) := by simpa using IntAt.coe P 0
  have hc : ∀ (s : Fin (cOf R j) → X.E) (l : Fin (R.N j + cOf R j)),
      (Fintype.linearCombination X.E (nfVec (qOf P) (R.N j) (cOf R j) (fun _ => 0) (0 : Sp X.E (R.N j))) s) l =
        if h : R.N j ≤ l.1 then s ⟨l.1 - R.N j, by have := l.2; omega⟩ else 0 := by
    intro s l
    rw [Fintype.linearCombination_apply, Finset.sum_apply]
    simp only [nfVec, zpow_zero, one_smul, map_zero, ite_self, add_zero, Pi.smul_apply, Loc.eN, smul_eq_mul, mul_ite, mul_one, mul_zero]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨l.1 - R.N j, by have := l.2; omega⟩]
      · rw [if_pos (by simp; omega)]
      · intro b _ hb
        rw [if_neg]
        intro e
        exact hb (Fin.ext (by simp; omega))
      · simp
    · exact Finset.sum_eq_zero fun b _ => if_neg (by omega)
  have hx : ∀ (x : Sp X.E (R.N j)) (l : Fin (R.N j + cOf R j)),
      Loc.inX X.E (R.N j) (cOf R j) x l = if h : l.1 < R.N j then x ⟨l.1, h⟩ else 0 := by
    intro x l
    unfold Loc.inX
    rw [LinearMap.pi_apply]
    split_ifs <;> simp
  rw [hg]
  apply le_antisymm
  · intro y hy
    rw [hL] at hy
    refine Submodule.mem_sup.2 ⟨Loc.inX X.E (R.N j) (cOf R j) (fun i => y (Fin.castAdd _ i)), ⟨_, ?_, rfl⟩,
      Fintype.linearCombination X.E (nfVec (qOf P) (R.N j) (cOf R j) (fun _ => 0) (0 : Sp X.E (R.N j))) (fun i => y (Fin.natAdd _ i)),
      ⟨_, ?_, rfl⟩, ?_⟩
    · exact (mem_localization_standardLattice P _).2 fun i => hy _
    · exact (mem_localization_standardLattice P _).2 fun i => hy _
    · funext l
      rw [Pi.add_apply, hx, hc]
      by_cases h : l.1 < R.N j
      · rw [dif_pos h, dif_neg (by omega), add_zero]
        rfl
      · rw [dif_neg h, dif_pos (by omega), zero_add]
        congr 1
        exact Fin.ext (by simp; omega)
  · refine sup_le ?_ ?_
    · rintro _ ⟨x, hx', rfl⟩
      rw [hL]
      intro l
      have := (mem_localization_standardLattice P _).1 hx'
      rw [LinearMap.restrictScalars_apply, hx]
      split_ifs
      · exact this _
      · exact h0
    · rintro _ ⟨s, hs, rfl⟩
      rw [hL]
      intro l
      have := (mem_localization_standardLattice P _).1 hs
      rw [LinearMap.restrictScalars_apply, hc]
      split_ifs
      · exact this _
      · exact h0

end GlobalTheory.IndefiniteRowSideFullHecke.NormalFormInclusion
