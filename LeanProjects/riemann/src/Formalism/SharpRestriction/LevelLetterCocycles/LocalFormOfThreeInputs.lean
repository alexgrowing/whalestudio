import Formalism.SharpRestriction.LevelLetterCocycles.LocalTheoremOfGoodExtensions

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l)

def genA : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (r S η m h : ℕ)
    (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ),
    HypA P K LL T₁ T₂ F r S η m h up b →
    ∃ s : Finset (↥(GK K) → T₂.V),
      s.card ≤ 2 * ((finrank ℚ_[l] ↥(K0 K) * finrank ↥(K0 K) ↥K.1 + 1) * r) ∧
      Submodule.span ↥(OL LL) (s : Set (↥(GK K) → T₂.V)) ⊔ latticeCoboundaries T₂.L = latticeFiniteCocycles (P.PD K) T₂.L

def liftA : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (r S η m h : ℕ)
    (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ),
    HypA P K LL T₁ T₂ F r S η m h up b →
    ∃ J : Finset ℤ, J ⊆ Finset.Icc (-(h : ℤ)) (2 * h) ∧ (0 : ℤ) ∉ J ∧
      F.LiftF (P.PD K) (expLift l h J)

def killA : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (r S η m h : ℕ)
    (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ),
    HypA P K LL T₁ T₂ F r S η m h up b →
    ∃ s h' : ℕ, finrank ↥(K0 K) ↥K.1 * s = l - 1 ∧ 1 ≤ h' ∧ h' ≤ h + S + 1 ∧
      ∃ s₀ : Finset (↥(GK K) → T₂.V),
        s₀.card ≤ finrank ℚ_[l] ↥(K0 K) * finrank ↥(K0 K) ↥K.1 * (finrank ↥(K0 K) ↥K.1 + 1) * m ∧
        (s₀ : Set (↥(GK K) → T₂.V)) ⊆ latticeFiniteCocycles (P.PD K) T₂.L ∧
        ∀ p ∈ latticeFiniteCocycles (P.PD K) T₂.L,
          (l ^ YA l (finrank ↥(K0 K) ↥K.1) s h' S η : ℕ) • p ∈
            Submodule.span ↥(OL LL) (s₀ : Set (↥(GK K) → T₂.V)) ⊔ F.ImF (P.PD K)

theorem claimA_of_steps (hG : genA P K LL) (hL : liftA P K LL) (hK : killA P K LL) :
    claimA P K LL := by
  intro T₁ T₂ F r S η m h up b hH
  obtain ⟨s, hs, hgen⟩ := hG T₁ T₂ F r S η m h up b hH
  obtain ⟨J, hJ, h0, hlift⟩ := hL T₁ T₂ F r S η m h up b hH
  obtain ⟨σ, h', hes, hh', hle, s₀, hs₀, hsub, hkill⟩ := hK T₁ T₂ F r S η m h up b hH
  refine ⟨σ, h', s.card, J, hes, hh', hle, hJ, h0, hs, s, s₀, le_rfl, hgen, hs₀, hsub, hkill, ?_⟩
  intro p hp
  have hpZ : p ∈ latticeFiniteCocycles (P.PD K) T₂.L := (Submodule.span_le.mpr hsub) hp
  have h1 := hlift p hpZ
  have e1 : ((l ^ expLift l h J : ℕ) : ↥(OL LL)) =
      ((((P.PD K).p : ℕ) : ↥(OL LL))) ^ expLift l h J := by
    rw [P.PD_p K]; push_cast; rfl
  rw [← Nat.cast_smul_eq_nsmul ↥(OL LL), e1]
  exact h1

end Local

def genR (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → genA (D.loc l) K LL

def liftR (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → liftA (D.loc l) K LL

def killR (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → killA (D.loc l) K LL

theorem local_form_of_three_inputs (D : D7) (hG : genR D) (hL : liftR D) (hK : killR D) : LocalTheoremAtGoodExtensions D :=
  fun l _ hl K LL hg =>
    claimA_of_steps (D.loc l) K LL (hG l hl K LL hg) (hL l hl K LL hg) (hK l hl K LL hg)

theorem local_theorem_of_three_inputs (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CA CB CK C : ℝ) (hC : 160 ≤ C)
    (hG : Adm1 D HW F Cm CA CB CK → genR D) (hL : Adm1 D HW F Cm CA CB CK → liftR D)
    (hK : Adm1 D HW F Cm CA CB CK → killR D) : IntegralityFromMetric D HW F Cm CA CB CK C :=
  fun hA => local_theorem_of_good_extensions D C hC (local_form_of_three_inputs D (hG hA) (hL hA) (hK hA))

end Formalism.MainNotions.N.Ln34

end
