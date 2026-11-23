import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictAll

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.LatDictZ.Z0

open Formalism.MainNotions.S PIW.AdelClassFin Formalism.L2.SG.Pf.LatDictZ

def SemiGenus : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
    Formalism.HermitianLatticesTheory.IsCMUnram E → Formalism.UG.IsHerm (starRingEnd E) J → J.det ≠ 0 →
    ∀ L M : Submodule (𝓞 E) (Fin n → E), L.FG → M.FG →
      Submodule.span E (L : Set (Fin n → E)) = ⊤ → Submodule.span E (M : Set (Fin n → E)) = ⊤ →
      SelfDual J L → SelfDual J M →
      ∀ p : Ideal (𝓞 E), p.IsMaximal →
        ∃ γ : GL (Fin n) E, γ ∈ Formalism.UG.UJ (starRingEnd E) J ∧
          ∀ v, v ∈ Formalism.HermitianLatticesTheory.loc (K := E) p M ↔
            ∃ w ∈ Formalism.HermitianLatticesTheory.loc (K := E) p L, (γ : Matrix (Fin n) (Fin n) E) *ᵥ w = v

def SemiGenusZ : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
    Formalism.HermitianLatticesTheory.IsCMUnram E → Formalism.UG.IsHerm (starRingEnd E) J → J.det ≠ 0 →
    ∀ {r : ℕ} (s : Fin r → Fin n → E) (z : Fin n → E) (L M : Submodule (𝓞 E) (Fin n → E)),
      L.FG → M.FG →
      Submodule.span E (L : Set (Fin n → E)) = ⊤ → Submodule.span E (M : Set (Fin n → E)) = ⊤ →
      SelfDual J L → SelfDual J M →
      (∀ a, Formalism.UG.hform (starRingEnd E) J (s a) z = 0) →
      (∀ w ∈ Submodule.span E (Set.range s), w ∈ L ↔ w ∈ M) →
      (∀ w ∈ L, ∃ w₁ ∈ L, w₁ ∈ Submodule.span E (Set.range s) ∧
        ∀ a, Formalism.UG.hform (starRingEnd E) J (s a) (w - w₁) = 0) →
      (∀ w ∈ M, ∃ w₁ ∈ M, w₁ ∈ Submodule.span E (Set.range s) ∧
        ∀ a, Formalism.UG.hform (starRingEnd E) J (s a) (w - w₁) = 0) →
      z ∈ L → z ∈ M →
      (∀ c : E, c • z ∈ L → c ∈ (algebraMap (𝓞 E) E).range) →
      (∀ c : E, c • z ∈ M → c ∈ (algebraMap (𝓞 E) E).range) →
      ∀ p : Ideal (𝓞 E), p.IsMaximal →
        ∃ γ : GL (Fin n) E, γ ∈ Formalism.UG.UJ (starRingEnd E) J ∧
          (∀ a, (γ : Matrix (Fin n) (Fin n) E) *ᵥ s a = s a) ∧ (γ : Matrix (Fin n) (Fin n) E) *ᵥ z = z ∧
          ∀ v, v ∈ Formalism.HermitianLatticesTheory.loc (K := E) p M ↔
            ∃ w ∈ Formalism.HermitianLatticesTheory.loc (K := E) p L, (γ : Matrix (Fin n) (Fin n) E) *ᵥ w = v

def LocFinite : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)),
    L.FG → M.FG →
    Submodule.span E (L : Set (Fin n → E)) = ⊤ → Submodule.span E (M : Set (Fin n → E)) = ⊤ →
    {p : Ideal (𝓞 E) | p.IsMaximal ∧ Formalism.HermitianLatticesTheory.loc (K := E) p M ≠ Formalism.HermitianLatticesTheory.loc (K := E) p L}.Finite

def AdelGlue : Prop :=
  ∀ (I : AutInst) {r : ℕ} (s : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (M : Submodule (𝓞 I.E) (Fin I.n → I.E)),
    M.FG → Submodule.span I.E (M : Set (Fin I.n → I.E)) = ⊤ →
    {p : Ideal (𝓞 I.E) | p.IsMaximal ∧ locE I p M ≠ locE I p I.L}.Finite →
    ∀ γ : Ideal (𝓞 I.E) → GL (Fin I.n) I.E,
      (∀ p, γ p ∈ Formalism.UG.UJ (starRingEnd I.E) I.J) →
      (∀ p a, (γ p : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ s a = s a) →
      (∀ p, (γ p : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z = z) →
      (∀ p : Ideal (𝓞 I.E), p.IsMaximal → ∀ v, v ∈ locE I p M ↔
        ∃ w ∈ locE I p I.L, (γ p : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ w = v) →
      ∃ x : I.Gf, (∀ a, I.fmat x *ᵥ iv I (s a) = iv I (s a)) ∧ I.fmat x *ᵥ iv I z = iv I z ∧ abelian₂ I x = M

theorem lamGenus_of (hG : SemiGenus) : LamGenus := by
  intro I x p hp
  obtain ⟨hfg, hsp⟩ := lattice_m_is_lattice I x
  exact hG I.E I.n I.J I.cm.cmUnram I.J_herm I.J_det I.L (abelian₂ I x) I.L_fg hfg I.L_span hsp
    I.L_dual (lattice_m_dual I x) p hp

theorem zOrbit_of (hZ : SemiGenusZ) (hA : AdelGlue) (hF : LocFinite) : ZOrbit := by
  intro I r s z M hMfg hMspan hMdual hsz hspan hsL hsM hzL hzM hpL hpM
  have hloc := fun (p : Ideal (𝓞 I.E)) (hp : p.IsMaximal) =>
    hZ I.E I.n I.J I.cm.cmUnram I.J_herm I.J_det s z I.L M I.L_fg hMfg I.L_span hMspan
      I.L_dual hMdual hsz hspan hsL hsM hzL hzM hpL hpM p hp
  choose γ hγU hγs hγz hγL using hloc
  obtain ⟨p₀, hp₀⟩ := Ideal.exists_maximal (𝓞 I.E)
  classical
  refine hA I s z M hMfg hMspan (hF I.E I.n I.L M I.L_fg hMfg I.L_span hMspan)
    (fun p => if hp : p.IsMaximal then γ p hp else γ p₀ hp₀) ?_ ?_ ?_ ?_
  · intro p
    by_cases hp : p.IsMaximal
    · simp only [dif_pos hp]; exact hγU p hp
    · simp only [dif_neg hp]; exact hγU p₀ hp₀
  · intro p a
    by_cases hp : p.IsMaximal
    · simp only [dif_pos hp]; exact hγs p hp a
    · simp only [dif_neg hp]; exact hγs p₀ hp₀ a
  · intro p
    by_cases hp : p.IsMaximal
    · simp only [dif_pos hp]; exact hγz p hp
    · simp only [dif_neg hp]; exact hγz p₀ hp₀
  · intro p hp v
    simp only [dif_pos hp]
    exact hγL p hp v

end Formalism.L2.SG.Pf.LatDictZ.Z0
