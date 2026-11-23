import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

section GenU

variable (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S)

theorem genU_self (a : Fin (r s)) : genU Ω r s a a = 1 := by
  simp [genU]

theorem genU_of_lt {a b : Fin (r s)} (h : a < b) : genU Ω r s a b = 0 := by
  simp [genU, not_lt.2 h.le, h.ne]

theorem genU_of_gt {l k : Fin (r s)} (h : k < l) :
    genU Ω r s l k = algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X ⟨s, ⟨(l, k), h⟩⟩) :=
  dif_pos h

end GenU

variable {Ψ : Type} {p q : ℕ} (Ω : Type) [Field Ω]

theorem symm_omEmb (a : Fin q) : (blockEquiv p q).symm (omEmb p q a) = .inl a := by
  rw [← blockEquiv_inl, Equiv.symm_apply_apply]

theorem symm_wEmb (a : Fin p) : (blockEquiv p q).symm (wEmb p q a) = .inr a := by
  rw [← blockEquiv_inr, Equiv.symm_apply_apply]

theorem gMat_apply (τ : Ψ) (i j : Fin (p + q)) :
    gMat p q Ω τ i j = (Matrix.fromBlocks (genU Ω (rk Ψ p q) (.inr τ) : Matrix (Fin q) (Fin q) _) 0 0
      (genU Ω (rk Ψ p q) (.inl τ) : Matrix (Fin p) (Fin p) _)) ((blockEquiv p q).symm i) ((blockEquiv p q).symm j) :=
  rfl

theorem gMat_om (τ : Ψ) (a b : Fin q) :
    gMat p q Ω τ (omEmb p q a) (omEmb p q b) = genU Ω (rk Ψ p q) (.inr τ) a b := by
  rw [gMat_apply, symm_omEmb, symm_omEmb]
  rfl

theorem gMat_w (τ : Ψ) (a b : Fin p) :
    gMat p q Ω τ (wEmb p q a) (wEmb p q b) = genU Ω (rk Ψ p q) (.inl τ) a b := by
  rw [gMat_apply, symm_wEmb, symm_wEmb]
  rfl

theorem gMat_om_w (τ : Ψ) (a : Fin q) (b : Fin p) : gMat p q Ω τ (omEmb p q a) (wEmb p q b) = 0 := by
  rw [gMat_apply, symm_omEmb, symm_wEmb]
  rfl

theorem gMat_lowerUni (τ : Ψ) : IsLowerUni (gMat p q Ω τ) := by
  constructor
  · intro a
    obtain ⟨x, rfl⟩ := (blockEquiv p q).surjective a
    rcases x with x | x
    · rw [blockEquiv_inl, gMat_om]
      exact genU_self Ω (rk Ψ p q) (.inr τ) x
    · rw [blockEquiv_inr, gMat_w]
      exact genU_self Ω (rk Ψ p q) (.inl τ) x
  · intro a b hab
    obtain ⟨x, rfl⟩ := (blockEquiv p q).surjective a
    obtain ⟨y, rfl⟩ := (blockEquiv p q).surjective b
    rcases x with x | x <;> rcases y with y | y
    · rw [blockEquiv_inl, blockEquiv_inl] at hab ⊢
      rw [gMat_om]
      exact genU_of_lt Ω (rk Ψ p q) (.inr τ) ((omEmb_strictMono p q).lt_iff_lt.1 hab)
    · rw [blockEquiv_inl, blockEquiv_inr, gMat_om_w]
    · rw [blockEquiv_inr, blockEquiv_inl] at hab
      have h : q + (x : ℕ) < (y : ℕ) := hab
      have := y.2
      omega
    · rw [blockEquiv_inr, blockEquiv_inr] at hab ⊢
      rw [gMat_w]
      exact genU_of_lt Ω (rk Ψ p q) (.inl τ) ((wEmb_strictMono p q).lt_iff_lt.1 hab)

def loc (t : GenIx (rk Ψ p q)) : Ψ × Fin (p + q) × Fin (p + q) :=
  match t with
  | ⟨.inl τ, lk⟩ => (τ, wEmb p q lk.1.1, wEmb p q lk.1.2)
  | ⟨.inr τ, lk⟩ => (τ, omEmb p q lk.1.1, omEmb p q lk.1.2)

theorem exists_var (x : LowIdx Ψ (p + q) p) :
    ∃ t : GenIx (rk Ψ p q), loc t = x.1 ∧ gMat p q Ω x.1.1 x.1.2.1 x.1.2.2 =
      algebraMap (MvPolynomial (GenIx (rk Ψ p q)) Ω) (GenField Ω (rk Ψ p q)) (MvPolynomial.X t) := by
  obtain ⟨⟨τ, a, b⟩, hlt, hiff⟩ := x
  obtain ⟨a, rfl⟩ := (blockEquiv p q).surjective a
  obtain ⟨b, rfl⟩ := (blockEquiv p q).surjective b
  rcases a with a | a <;> rcases b with b | b
  · simp only [blockEquiv_inl] at hlt hiff ⊢
    have h : b < a := (omEmb_strictMono p q).lt_iff_lt.1 hlt
    exact ⟨⟨.inr τ, ⟨(a, b), h⟩⟩, rfl, by
      rw [gMat_om]; exact genU_of_gt Ω (rk Ψ p q) (.inr τ) h⟩
  · exfalso
    simp only [blockEquiv_inl, blockEquiv_inr] at hlt
    have h : q + (b : ℕ) < (a : ℕ) := hlt
    have := a.2
    omega
  · exfalso
    simp only [blockEquiv_inl, blockEquiv_inr] at hiff
    have h : (q + (a : ℕ) < p + q - p ↔ (b : ℕ) < p + q - p) := hiff
    have := b.2
    omega
  · simp only [blockEquiv_inr] at hlt hiff ⊢
    have h : b < a := (wEmb_strictMono p q).lt_iff_lt.1 hlt
    exact ⟨⟨.inl τ, ⟨(a, b), h⟩⟩, rfl, by
      rw [gMat_w]; exact genU_of_gt Ω (rk Ψ p q) (.inl τ) h⟩

theorem gMat_indep :
    AlgebraicIndependent Ω fun x : LowIdx Ψ (p + q) p => gMat p q Ω x.1.1 x.1.2.1 x.1.2.2 := by
  choose e he₁ he₂ using exists_var (Ψ := Ψ) (p := p) (q := q) Ω
  have hinj : Function.Injective e := fun x y h => Subtype.ext (by rw [← he₁ x, ← he₁ y, h])
  have hX : AlgebraicIndependent Ω fun t : GenIx (rk Ψ p q) =>
      algebraMap (MvPolynomial (GenIx (rk Ψ p q)) Ω) (GenField Ω (rk Ψ p q)) (MvPolynomial.X t) :=
    (MvPolynomial.algebraicIndependent_X (GenIx (rk Ψ p q)) Ω).map'
      (f := IsScalarTower.toAlgHom Ω (MvPolynomial (GenIx (rk Ψ p q)) Ω) (GenField Ω (rk Ψ p q)))
      (IsFractionRing.injective _ _)
  have e' : (fun x : LowIdx Ψ (p + q) p => gMat p q Ω x.1.1 x.1.2.1 x.1.2.2) =
      (fun t : GenIx (rk Ψ p q) =>
        algebraMap (MvPolynomial (GenIx (rk Ψ p q)) Ω) (GenField Ω (rk Ψ p q)) (MvPolynomial.X t)) ∘ e :=
    funext he₂
  rw [e']
  exact hX.comp e hinj

theorem gMat_isGenericFlag : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω],
    GlobalTheory.CompanionTheory.Ar.PB.IsGenericFlag Ω p (gMat (Ψ := Ψ) p q Ω) := fun _ _ _ _ Ω _ =>
  IsGenericFlag.of_lowerUni (fun τ => gMat_lowerUni Ω τ) (gMat_indep Ω)

end GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat
