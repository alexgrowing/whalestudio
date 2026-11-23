import Formalism.LocalToGlobal.Columns.ChainOne
import Formalism.LocalToGlobal.Columns.ChainInstS

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Core

open Classical in

def ocbChiV {k : Type} [Field k] (χ : kˣ →* ℂˣ) (x : k) : ℂ := if h : x = 0 then 0 else ((χ (Units.mk0 x h) : ℂˣ) : ℂ)

def ocbEnt {k : Type} [Field k] {A B : ℕ} (k₀ cA nA cB nB : ℕ) (x : (Fin A → k) →ₗ[k] (Fin B → k)) (p p' : ℕ) : k :=
  Loc.atN (x (Loc.eN k A (LocE.fIdx k₀ cA nA p'))) (LocE.fIdx k₀ cB nB p)

def ocbAllow (k₀ m t N p p' : ℕ) : Prop :=
  if p' < k₀ then p < p' ∨ (k₀ ≤ p ∧ p < k₀ + (m / 2 - 1))
  else if p' < k₀ + m - 1 then (k₀ ≤ p ∧ p < p') ∨ (m / 2 < p' + 1 - k₀ ∧ p < k₀)
  else p < k₀ + m - 1 ∨ (p < N ∧ (p - (k₀ + m - 1)) / t ≤ (p' - (k₀ + m - 1)) / t)

open Classical in

def ocbPhiS {k : Type} [Field k] (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ) (k₀ m t j n' c n : ℕ) : Loc.SF k ℂ (n' + (c + 1)) (n + c) :=
  fun x =>
    let M := ocbEnt k₀ (c + 1) n' c n x
    let r := k₀ + m - 1
    let a := r + (j - 1) * t
    if (∀ p', p' < r → M p' p' = 1) ∧ (∀ p p', p < n + c → p' < a → p ≠ p' → M p p' ≠ 0 → ocbAllow k₀ m t a p p')
    then ψ₀ (∑ i ∈ Finset.range (r - 1), M i (i + 1)) *
        (∏ i ∈ Finset.range (j - 1),
          ocbChiV (χ i) (Matrix.det (Matrix.of fun s s' : Fin t => M (r + i * t + s.1) (r + i * t + s'.1)))) *
        (ocbChiV (χ (j - 1)) (Matrix.det (Matrix.of fun s s' : Fin a => M s.1 s'.1)))⁻¹
    else 0

def ocbInJS {k : Type} [Field k] (k₀ m t c n : ℕ) (κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : Prop :=
  (∀ p', p' < k₀ + m - 1 → ocbEnt k₀ c n c n κ.toLinearMap p' p' = 1) ∧
    ∀ p p', p < n + c → p' < n + c → p ≠ p' → ocbEnt k₀ c n c n κ.toLinearMap p p' ≠ 0 → ocbAllow k₀ m t (n + c) p p'

def ocbNe {k : Type} [Field k] [Fintype k] (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ) (k₀ m t j n' c n : ℕ)
    (h : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : Prop :=
  ∃ xj : (Fin n' → k) →ₗ[k] (Fin n → k),
    Loc.E1 (n' := n') (c' := c + 1) (n := n) (c := c) (fun u => ψ₀ u) Finset.univ 1
      (Loc.om (fun _ => 1) (fun _ => 0) 1 (LinearEquiv.refl k _) h (ocbPhiS ψ₀ χ k₀ m t j n' c n)) xj ≠ 0

def ocbIn {k : Type} [Field k] (k₀ m t c n : ℕ) (h : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : Prop :=
  ∃ ρ ∈ Loc.R1 k n c, ∃ κ, ocbInJS k₀ m t c n κ ∧ h = ρ * κ

def ocbRanks (k₀ m t j n' c n : ℕ) : Prop :=
  1 ≤ k₀ ∧ Even m ∧ 4 ≤ m ∧ 1 ≤ j ∧ j ≤ m - 2 ∧ c = m - 1 - j ∧
    n' + (c + 1) = k₀ + m - 1 + (j - 1) * t ∧ n + c = k₀ + m - 1 + j * t

def ResidueFieldUnfoldingSupport : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ) (k₀ m t j n' c n : ℕ), ψ₀ ≠ 1 → ocbRanks k₀ m t j n' c n →
    ∀ h : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k), ocbNe ψ₀ χ k₀ m t j n' c n h → ocbIn k₀ m t c n h

def ResidueFieldUnfoldingNonzero : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ) (k₀ m t j n' c n : ℕ), ψ₀ ≠ 1 → ocbRanks k₀ m t j n' c n →
    ∃ xj : (Fin n' → k) →ₗ[k] (Fin n → k),
      Loc.E1 (n' := n') (c' := c + 1) (n := n) (c := c) (fun u => ψ₀ u) Finset.univ 1 (ocbPhiS ψ₀ χ k₀ m t j n' c n) xj ≠ 0

theorem ocbNe_one {k : Type} [Field k] [Fintype k] (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ) (k₀ m t j n' c n : ℕ) :
    ocbNe ψ₀ χ k₀ m t j n' c n 1 ↔
      ∃ xj : (Fin n' → k) →ₗ[k] (Fin n → k),
        Loc.E1 (n' := n') (c' := c + 1) (n := n) (c := c) (fun u => ψ₀ u) Finset.univ 1 (ocbPhiS ψ₀ χ k₀ m t j n' c n) xj ≠ 0 := by
  have e : Loc.om (fun _ : k => (1 : ℂ)) (fun _ => (0 : ℤ)) 1 (LinearEquiv.refl k (Fin (n' + (c + 1)) → k))
      (1 : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) (ocbPhiS ψ₀ χ k₀ m t j n' c n) = ocbPhiS ψ₀ χ k₀ m t j n' c n := by
    funext x
    have hx : ((1 : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)).symm.toLinearMap ∘ₗ x ∘ₗ
        (LinearEquiv.refl k (Fin (n' + (c + 1)) → k)).toLinearMap) = x := LinearMap.ext fun _ => rfl
    unfold Loc.om
    rw [hx]
    simp
  unfold ocbNe
  rw [e]

end Core

section Red

variable {E : Type} [Field E] [NumberField E]

def ocbIsRed (P : HeightOneSpectrum (𝓞 E)) (q n c : ℕ) (h₀ : Sp E (n + c) ≃ₗ[E] Sp E (n + c))
    (hbar : (Fin (n + c) → 𝓞 E ⧸ P.asIdeal) ≃ₗ[𝓞 E ⧸ P.asIdeal] (Fin (n + c) → 𝓞 E ⧸ P.asIdeal)) : Prop :=
  ∀ l s, l < n + c → s < n + c →
    IntAt P (Loc.atN (h₀ (Loc.eN E (n + c) s)) l * (q : E) ^ (LocE.scE n (fun i => i + 1) s - LocE.scE n (fun i => i + 1) l)) ∧
      Loc.atN (hbar (Loc.eN (𝓞 E ⧸ P.asIdeal) (n + c) s)) l =
        redP P (Loc.atN (h₀ (Loc.eN E (n + c) s)) l * (q : E) ^ (LocE.scE n (fun i => i + 1) s - LocE.scE n (fun i => i + 1) l))

end Red

section Glob

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

structure OcbBase (m2 : ℕ) : Prop where
  hX : X.Ok
  hPr : Pr.Ok
  hCh : Ch.Ok
  hm : R.m = m2 + 2
  cst_ok : cst.Ok
  sharp : cst.sharp = true
  psi0 : ∀ (P : rowSG Pr sel mu) (a : X.E), P.1 ∈ Pr.vGs → IntAt P.1 a →
    cst.psi P (a / (qOf P.1 : X.E)) = psi0P Ch P.1 (redP P.1 a)
  depthG : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → cst.D P = 1

def ocbPsiC (σ : X.K →+* ℂ) (P : HeightOneSpectrum (𝓞 X.E)) : AddChar (𝓞 X.E ⧸ P.asIdeal) ℂ :=
  (σ : X.K →* ℂ).compAddChar (psi0P Ch P)

def ocbChiC (σ : X.K →+* ℂ) (P : HeightOneSpectrum (𝓞 X.E)) (i : ℕ) : (𝓞 X.E ⧸ P.asIdeal)ˣ →* ℂˣ :=
  (Units.map (σ : X.K →* ℂ)).comp (chiP Ch P i)

def ocbNeAt (σ : X.K →+* ℂ) (i : ℕ) (P : HeightOneSpectrum (𝓞 X.E))
    (hbar : (Fin (R.N (i + 1) + cOf R (i + 1)) → 𝓞 X.E ⧸ P.asIdeal) ≃ₗ[𝓞 X.E ⧸ P.asIdeal] (Fin (R.N (i + 1) + cOf R (i + 1)) → 𝓞 X.E ⧸ P.asIdeal)) :
    Prop :=
  @ocbNe (𝓞 X.E ⧸ P.asIdeal) (resField P) (resFintype P) (ocbPsiC Ch σ P) (ocbChiC Ch σ P) R.k R.m R.t (i + 1) (R.N i) (cOf R (i + 1))
    (R.N (i + 1)) hbar

variable (R) in

def ocbInAt (i : ℕ) (P : HeightOneSpectrum (𝓞 X.E))
    (hbar : (Fin (R.N (i + 1) + cOf R (i + 1)) → 𝓞 X.E ⧸ P.asIdeal) ≃ₗ[𝓞 X.E ⧸ P.asIdeal] (Fin (R.N (i + 1) + cOf R (i + 1)) → 𝓞 X.E ⧸ P.asIdeal)) :
    Prop :=
  @ocbIn (𝓞 X.E ⧸ P.asIdeal) (resField P) R.k R.m R.t (cOf R (i + 1)) (R.N (i + 1)) hbar

def NonvanishingGivesLatticeRepresentative (m2 : ℕ) : Prop :=
  OcbBase Ch sel mu cst m2 → ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → ∀ h : AutY X R (i + 1),
    FiniteSumNonzeroLargeDepth Ch sel mu cst i P 1 h →
      ∃ ρ ∈ Loc.R1 X.E (R.N (i + 1)) (cOf R (i + 1)), ∃ h₀ ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P.1),
        h = ρ * h₀ ∧ FiniteSumNonzeroLargeDepth Ch sel mu cst i P 1 h₀

def ReductionExistsInLatticeStabilizer (σ : X.K →+* ℂ) (m2 : ℕ) : Prop :=
  OcbBase Ch sel mu cst m2 → ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs →
    ∀ h₀ ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P.1),
      (∃ hbar, ocbIsRed P.1 (qOf P.1) (R.N (i + 1)) (cOf R (i + 1)) h₀ hbar) ∧
      ∀ hbar, ocbIsRed P.1 (qOf P.1) (R.N (i + 1)) (cOf R (i + 1)) h₀ hbar →
        (FiniteSumNonzeroLargeDepth Ch sel mu cst i P 1 h₀ ↔ ocbNeAt Ch σ i P.1 hbar)

def LiftFromResidueParabolicProduct (m2 : ℕ) : Prop :=
  OcbBase Ch sel mu cst m2 → ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs →
    ∀ h₀ ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P.1), ∀ hbar, ocbIsRed P.1 (qOf P.1) (R.N (i + 1)) (cOf R (i + 1)) h₀ hbar →
      ocbInAt R i P.1 hbar → SameDC (Pr := Pr) cst.sharp (i + 1) P.1 1 h₀

def OcbPatSubJ (m2 : ℕ) : Prop :=
  OcbBase Ch sel mu cst m2 → ∀ j, j ≤ m2 + 1 → ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → ∀ κ ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P.1),
    (∀ p', p' < R.r → redP P.1 (LocE.entB (qOf P.1) R.k (cOf R j) (R.N j) (cOf R j) (R.N j) (fun i => i + 1) (fun i => i + 1) κ.toLinearMap p' p') = 1) →
    (∀ p p', p < R.N j + cOf R j → p' < R.r → p ≠ p' →
      (R.r ≤ p ∨ symIdx R.k R.rS p' < symIdx R.k R.rS p ∨ (p' = R.k + R.rS ∧ p < R.k)) →
      redP P.1 (LocE.entB (qOf P.1) R.k (cOf R j) (R.N j) (cOf R j) (R.N j) (fun i => i + 1) (fun i => i + 1) κ.toLinearMap p p') = 0) →
    (∀ p p', R.r ≤ p' → p' < R.N j + cOf R j → p < R.N j + cOf R j → (p' - R.r) / R.t < (p - R.r) / R.t →
      redP P.1 (LocE.entB (qOf P.1) R.k (cOf R j) (R.N j) (cOf R j) (R.N j) (fun i => i + 1) (fun i => i + 1) κ.toLinearMap p p') = 0) →
    κ ∈ Jat (Pr := Pr) true j P.1

def OcbLamChar (m2 : ℕ) : Prop :=
  OcbBase Ch sel mu cst m2 → ∀ j, j ≤ m2 + 1 → ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs →
    LamGBSChar P.1 (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k R.rS R.r R.t j (R.N j) (cOf R j)

end Glob

section Ent

variable {κ K : Type} [CommRing κ] [Field K] {N : ℕ}

def ocbM (hbar : GL (Fin N) κ) (p p' : ℕ) : κ := if h : p < N ∧ p' < N then hbar.1 ⟨p, h.1⟩ ⟨p', h.2⟩ else 0

def ocbXAllow (k₀ rS j t p p' : ℕ) : Prop :=
  if p' < k₀ then p < p' ∨ (k₀ ≤ p ∧ p + rS + 2 ≤ k₀ + j)
  else if p' < k₀ + j then (k₀ ≤ p ∧ p < p') ∨ (p < k₀ ∧ k₀ + j < p' + rS + 1)
  else p < k₀ + j ∨ (p - (k₀ + j)) / t ≤ (p' - (k₀ + j)) / t

def ocbXPat (k₀ rS j t : ℕ) (hbar : GL (Fin N) κ) : Prop :=
  (∀ p, p < k₀ + j → ocbM hbar p p = 1) ∧ ∀ p p', p < N → p' < N → p ≠ p' → ocbM hbar p p' ≠ 0 → ocbXAllow k₀ rS j t p p'

open Classical in

def ocbChiK (χ : κˣ →* Kˣ) (x : κ) : K := if h : IsUnit x then ((χ h.unit : Kˣ) : K) else 0

def ocbXLam (ψ₀ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (k₀ j t : ℕ) (hbar : GL (Fin N) κ) : K :=
  ψ₀ (∑ i ∈ Finset.range (k₀ - 1), ocbM hbar i (i + 1) + ∑ i ∈ Finset.range (j - 1), ocbM hbar (k₀ + i) (k₀ + i + 1)) *
    ∏ i ∈ Finset.range j,
      ocbChiK (χ i) (Matrix.det (Matrix.of fun s s' : Fin t => ocbM hbar (k₀ + j + i * t + s.1) (k₀ + j + i * t + s'.1)))

end Ent

section Lev

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

def OcbGrpGLoc (m2 : ℕ) : Prop :=
  OcbBase Ch sel mu cst m2 → ∀ j, j ≤ m2 + 1 → ∀ (w : {w // w ∈ Pr.vGs}) (hbar : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)),
    (∃ g ∈ prCat (Pr := Pr) cst.sharp j w.1 (1 : AutY X R j),
      ∀ x ∈ stdAt X.E (R.N j) w.1, redV w.1 (g x) = hbar.1.mulVec (redV w.1 x)) ↔ ocbXPat R.k R.rS j R.t hbar

open Classical in

def OcbChrGLoc (m2 : ℕ) : Prop :=
  OcbBase Ch sel mu cst m2 → ∀ j, j ≤ m2 + 1 → ∀ (w : {w // w ∈ Pr.vGs}) (hbar : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal))
    (g : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (r : AutY X R j),
    r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j w.1) (1 : AutY X R j) →
    (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g x)) →
    (∀ x ∈ stdAt X.E (R.N j) w.1, redV w.1 (g x) = hbar.1.mulVec (redV w.1 x)) →
    chiInv Ch sel mu cst j ⟨w.1, Finset.mem_union_left _ w.2⟩ (1 : AutY X R j) r = ocbXLam (psi0P Ch w.1) (chiP Ch w.1) R.k j R.t hbar

structure OcbLevIs (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (m2 : ℕ) : Prop where
  H : ∀ j, j ≤ m2 + 1 → ∀ (w : {w // w ∈ Pr.vGs}) (hbar : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)),
    hbar ∈ (Λ j w).H ↔ ocbXPat R.k R.rS j R.t hbar
  lam : ∀ j, j ≤ m2 + 1 → ∀ (w : {w // w ∈ Pr.vGs}) (hbar : ↥(Λ j w).H),
    (((Λ j w).lam hbar : X.Kˣ) : X.K) = ocbXLam (psi0P Ch w.1) (chiP Ch w.1) R.k j R.t hbar.1

variable {Ch sel mu cst}

theorem ocbPsiC_ne (hCh : Ch.Ok) (σ : X.K →+* ℂ) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs) : ocbPsiC Ch σ P ≠ 1 := by
  have h1 : psi0P Ch P ≠ 1 := by
    unfold psi0P
    rw [dif_pos hP]
    exact hCh.psi_zero_nontrivial_character ⟨P, hP⟩
  obtain ⟨a, ha⟩ := (AddChar.ne_one_iff).1 h1
  refine (AddChar.ne_one_iff).2 ⟨a, fun h => ha ?_⟩
  have h2 : σ (psi0P Ch P a) = σ 1 := by
    rw [map_one]
    exact h
  exact σ.injective h2

theorem ocbRanks_step {m2 i : ℕ} (hm : R.m = m2 + 2) (hi : i < m2) :
    ocbRanks R.k R.m R.t (i + 1) (R.N i) (cOf R (i + 1)) (R.N (i + 1)) := by
  have hk := R.m_add_three_le_k
  obtain ⟨a, ha⟩ := R.m_even
  have e1 : i * (R.t + 1) = i * R.t + i := by ring
  have e2 : (i + 1) * (R.t + 1) = (i + 1) * R.t + i + 1 := by ring
  refine ⟨by omega, R.m_even, by omega, by omega, by omega, rfl, ?_, ?_⟩
  · unfold cOf Ranks.N
    rw [e1, Nat.add_sub_cancel]
    omega
  · unfold cOf Ranks.N
    rw [e2]
    omega

theorem oneCoset_surj (σ : X.K →+* ℂ) {m2 : ℕ} (hB : OcbBase Ch sel mu cst m2) (hQ : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs)
    (c1 : ResidueFieldUnfoldingSupport) (b2 : ReductionExistsInLatticeStabilizer Ch sel mu cst σ m2) (b3 : LiftFromResidueParabolicProduct Ch sel mu cst m2) :
    ∀ i, i < m2 → ∀ hh : rowSG Pr sel mu → AutY X R (i + 1),
      (∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → hh P ∈ stabL X.E _ (lamYat (Pr := Pr) (i + 1) P.1)) →
      (∀ P, FiniteSumNonzeroLargeDepth Ch sel mu cst i P 1 (hh P)) → ∀ P, SameDC (Pr := Pr) cst.sharp (i + 1) P.1 1 (hh P) := by
  intro i hi hh hs H P
  obtain ⟨⟨hbar, hred⟩, hiff⟩ := b2 hB i hi P (hQ P) (hh P) (hs P (hQ P))
  have hin : ocbInAt R i P.1 hbar :=
    @c1 (𝓞 X.E ⧸ P.1.asIdeal) (resField P.1) (resFintype P.1) (ocbPsiC Ch σ P.1) (ocbChiC Ch σ P.1) R.k R.m R.t (i + 1) (R.N i)
      (cOf R (i + 1)) (R.N (i + 1)) (ocbPsiC_ne hB.hCh σ (hQ P)) (ocbRanks_step hB.hm hi) hbar ((hiff hbar hred).1 (H P))
  exact b3 hB i hi P (hQ P) (hh P) (hs P (hQ P)) hbar hred hin

theorem ocbIsRed_one {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (q n c : ℕ) : ocbIsRed P q n c 1 1 := by
  intro l s hl hs
  have h1 : Loc.atN ((1 : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (Loc.eN E (n + c) s)) l = if l = s then 1 else 0 := by
    show Loc.atN (Loc.eN E (n + c) s) l = _
    unfold Loc.atN Loc.eN
    rw [dif_pos hl]
  have h2 : Loc.atN ((1 : (Fin (n + c) → 𝓞 E ⧸ P.asIdeal) ≃ₗ[𝓞 E ⧸ P.asIdeal] (Fin (n + c) → 𝓞 E ⧸ P.asIdeal))
      (Loc.eN (𝓞 E ⧸ P.asIdeal) (n + c) s)) l = if l = s then 1 else 0 := by
    show Loc.atN (Loc.eN (𝓞 E ⧸ P.asIdeal) (n + c) s) l = _
    unfold Loc.atN Loc.eN
    rw [dif_pos hl]
  rw [h1, h2]
  by_cases hls : l = s
  · subst hls
    rw [if_pos rfl, if_pos rfl, sub_self, zpow_zero, mul_one]
    exact ⟨⟨1, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩, redP_one.symm⟩
  · rw [if_neg hls, if_neg hls, zero_mul]
    exact ⟨⟨0, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩, redP_zero.symm⟩

theorem nonVanSym_of (σ : X.K →+* ℂ) {m2 : ℕ} (hB : OcbBase Ch sel mu cst m2) (hQ : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs)
    (c2 : ResidueFieldUnfoldingNonzero) (b2 : ReductionExistsInLatticeStabilizer Ch sel mu cst σ m2) : NonVanSym Ch sel mu cst m2 := by
  intro i hi P
  have h := (b2 hB i hi P (hQ P) 1 (Subgroup.one_mem _)).2 1 (ocbIsRed_one P.1 (qOf P.1) _ _)
  refine h.2 ?_
  exact (@ocbNe_one (𝓞 X.E ⧸ P.1.asIdeal) (resField P.1) (resFintype P.1) (ocbPsiC Ch σ P.1) (ocbChiC Ch σ P.1) R.k R.m R.t (i + 1) (R.N i)
    (cOf R (i + 1)) (R.N (i + 1))).2
    (@c2 (𝓞 X.E ⧸ P.1.asIdeal) (resField P.1) (resFintype P.1) (ocbPsiC Ch σ P.1) (ocbChiC Ch σ P.1) R.k R.m R.t (i + 1) (R.N i)
      (cOf R (i + 1)) (R.N (i + 1)) (ocbPsiC_ne hB.hCh σ (hQ P)) (ocbRanks_step hB.hm hi))

theorem oneCosetSym_of (σ : X.K →+* ℂ) {m2 : ℕ} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs} (hB : OcbBase Ch sel mu cst m2)
    (hQ : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs) (c1 : ResidueFieldUnfoldingSupport) (c2 : ResidueFieldUnfoldingNonzero)
    (b2 : ReductionExistsInLatticeStabilizer Ch sel mu cst σ m2) (b3 : LiftFromResidueParabolicProduct Ch sel mu cst m2) (hG : OcbGrpGLoc Ch sel mu cst m2) (hC : OcbChrGLoc Ch sel mu cst m2)
    (hΛ : OcbLevIs Ch Λ m2) : OneCosetSym Ch sel mu cst Λ m2 ∧ NonVanSym Ch sel mu cst m2 :=
  ⟨{ surj := oneCoset_surj σ hB hQ c1 b2 b3
     grpG := fun j hj w hbar => (hΛ.H j hj w hbar).trans (hG hB j hj w hbar).symm
     chrG := fun j hj w hbar g r hr hg hred => (hΛ.lam j hj w hbar).trans (hC hB j hj w hbar.1 g r hr hg hred).symm },
    nonVanSym_of σ hB hQ c2 b2⟩

end Lev

end Formalism.L2.Col
