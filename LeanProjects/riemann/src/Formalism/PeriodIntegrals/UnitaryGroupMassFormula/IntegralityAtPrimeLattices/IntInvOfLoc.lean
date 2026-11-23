import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.NatNotMemPv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.RootOfUnityInt

noncomputable section

open NumberField Ideal Matrix

namespace PI.UnitaryGroupMassFormula.IAT

open Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Host Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.UG

variable {D : D7} {u : D.what₂.Word}

theorem le_locP' {E : Type} [Field E] [NumberField E] {n : ℕ} (P : Ideal (𝓞 E)) [P.IsPrime]
    (L : Submodule (𝓞 E) (Fin n → E)) : L ≤ Formalism.HermitianLatticesTheory.localization₂ P L := by
  unfold Formalism.HermitianLatticesTheory.localization₂ Formalism.HermitianLatticesTheory.locS
  intro x hx
  exact ⟨1, P.primeCompl.one_mem, by simpa using hx⟩

theorem localization_mono' {E : Type} [Field E] [NumberField E] {n : ℕ} (P : Ideal (𝓞 E)) [P.IsPrime]
    {L M : Submodule (𝓞 E) (Fin n → E)} (h : L ≤ M) : Formalism.HermitianLatticesTheory.localization₂ P L ≤ Formalism.HermitianLatticesTheory.localization₂ P M := by
  unfold Formalism.HermitianLatticesTheory.localization₂ Formalism.HermitianLatticesTheory.locS
  rintro x ⟨s, hs, hx⟩
  exact ⟨s, hs, h hx⟩

theorem intInv_of_loc (A : AtTTied u) (w : D.what₂.places.Pl) (hw : Formalism.MainNotions.product_first_zeroth_parts.OverT D u w)
    (hseen : (D.fm u).seenP w = true) (v : (D.mem u).A.vT) {n : ℕ} {X Y : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (Bx By g : GL (Fin n) D.host.E)
    (hBx : IsLocBasis (D.mem u).A.T (X : Set (Fin n → D.host.E)) Bx)
    (hBy : IsLocBasis (D.mem u).A.T (Y : Set (Fin n → D.host.E)) By)
    (h1 : Y ≤ Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat (g : Matrix (Fin n) (Fin n) D.host.E) X))
    (h2 : mulLat (g : Matrix (Fin n) (Fin n) D.host.E) X ≤ Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) Y) :
    IntInv w (atInf (embT D) ((Bx⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) ((D.fm u).tauOf w v) *
      atInf (embT D) ((g⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) ((D.fm u).tauOf w v) *
      atInf (embT D) (By : Matrix (Fin n) (Fin n) D.host.E) ((D.fm u).tauOf w v)) := by
  have hT1 : ¬ (D.mem u).A.T ∣ 1 := (D.mem u).A.T_prime.not_dvd_one
  have hcol : ∀ (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (B : GL (Fin n) D.host.E),
      IsLocBasis (D.mem u).A.T (L : Set (Fin n → D.host.E)) B → ∀ b : Fin n, ∃ s : ℕ,
        ¬ (D.mem u).A.T ∣ s ∧
          (s : D.host.E) • ((B : Matrix (Fin n) (Fin n) D.host.E) *ᵥ Pi.single b 1) ∈ L := by
    intro L B hB b
    refine (hB _).mpr ⟨1, hT1, fun a => ?_⟩
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Nat.cast_one, one_mul]
    by_cases h : a = b
    · subst h
      rw [Pi.single_eq_same]
      exact ⟨1, map_one _⟩
    · rw [Pi.single_eq_of_ne h]
      exact ⟨0, map_zero _⟩
  have hprime : ∀ (t : 𝓞 D.host.E) (s : ℕ), t ∉ A.Pv v → ¬ (D.mem u).A.T ∣ s →
      t * (s : 𝓞 D.host.E) ∉ A.Pv v := by
    intro t s ht hs hmem
    rcases (inferInstance : (A.Pv v).IsPrime).mem_or_mem hmem with h | h
    · exact ht h
    · exact nat_not_mem_Pv A v s hs h
  have hsmul : ∀ (t : 𝓞 D.host.E) (s : ℕ) (z : Fin n → D.host.E),
      (t * (s : 𝓞 D.host.E)) • z = t • ((s : D.host.E) • z) := by
    intro t s z
    rw [mul_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  have hN : ∀ a b, embT D ((D.fm u).tauOf w v)
      ((((Bx⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *
        ((g⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *
        (By : Matrix (Fin n) (Fin n) D.host.E)) a b) ∈ bwA_Ow D w := by
    intro a b
    obtain ⟨s, hs, hsY⟩ := hcol Y By hBy b
    obtain ⟨t, ht, htm⟩ : ∃ t ∈ (A.Pv v).primeCompl, t • ((s : D.host.E) •
        ((By : Matrix (Fin n) (Fin n) D.host.E) *ᵥ Pi.single b 1)) ∈
        mulLat (g : Matrix (Fin n) (Fin n) D.host.E) X := h1 hsY
    obtain ⟨x', hx', hgx⟩ := Submodule.mem_map.mp htm
    have hgx' : (g : Matrix (Fin n) (Fin n) D.host.E) *ᵥ x' = t • ((s : D.host.E) •
        ((By : Matrix (Fin n) (Fin n) D.host.E) *ᵥ Pi.single b 1)) := hgx
    have hx'eq : x' = (t * (s : 𝓞 D.host.E)) •
        (((g⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *ᵥ
          ((By : Matrix (Fin n) (Fin n) D.host.E) *ᵥ Pi.single b 1)) := by
      calc x' = ((g⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *ᵥ
            ((g : Matrix (Fin n) (Fin n) D.host.E) *ᵥ x') := by
              rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
        _ = _ := by rw [hgx', Matrix.mulVec_smul, Matrix.mulVec_smul, hsmul]
    have hmemX := hx'eq ▸ hx'
    have hc := coord_mem A w hw hseen v hBx _ _ (hprime t s ht hs) hmemX a
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at hc
    exact hc
  have hN' : ∀ a b, embT D ((D.fm u).tauOf w v)
      ((((By⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *
        (g : Matrix (Fin n) (Fin n) D.host.E) *
        (Bx : Matrix (Fin n) (Fin n) D.host.E)) a b) ∈ bwA_Ow D w := by
    intro a b
    obtain ⟨s, hs, hsX⟩ := hcol X Bx hBx b
    have hm : (g : Matrix (Fin n) (Fin n) D.host.E) *ᵥ ((s : D.host.E) •
        ((Bx : Matrix (Fin n) (Fin n) D.host.E) *ᵥ Pi.single b 1)) ∈
        mulLat (g : Matrix (Fin n) (Fin n) D.host.E) X := Submodule.mem_map_of_mem hsX
    obtain ⟨t, ht, htY⟩ : ∃ t ∈ (A.Pv v).primeCompl, t • ((g : Matrix (Fin n) (Fin n) D.host.E) *ᵥ
        ((s : D.host.E) • ((Bx : Matrix (Fin n) (Fin n) D.host.E) *ᵥ Pi.single b 1))) ∈ Y := h2 hm
    have heq : (t * (s : 𝓞 D.host.E)) • ((g : Matrix (Fin n) (Fin n) D.host.E) *ᵥ
        ((Bx : Matrix (Fin n) (Fin n) D.host.E) *ᵥ Pi.single b 1)) =
        t • ((g : Matrix (Fin n) (Fin n) D.host.E) *ᵥ
        ((s : D.host.E) • ((Bx : Matrix (Fin n) (Fin n) D.host.E) *ᵥ Pi.single b 1))) := by
      rw [hsmul, Matrix.mulVec_smul]
    rw [← heq] at htY
    have hc := coord_mem A w hw hseen v hBy _ _ (hprime t s ht hs) htY a
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at hc
    exact hc
  have hprod : ((Bx⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *
      ((g⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *
      (By : Matrix (Fin n) (Fin n) D.host.E) *
      (((By⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *
        (g : Matrix (Fin n) (Fin n) D.host.E) * (Bx : Matrix (Fin n) (Fin n) D.host.E)) = 1 := by
    simp [mul_assoc]
  refine ⟨(((By⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *
      (g : Matrix (Fin n) (Fin n) D.host.E) * (Bx : Matrix (Fin n) (Fin n) D.host.E)).map
        (embT D ((D.fm u).tauOf w v)), ?_, ?_, ?_⟩
  · show ((Bx⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E).map
        (embT D ((D.fm u).tauOf w v)) *
      ((g⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E).map
        (embT D ((D.fm u).tauOf w v)) *
      (By : Matrix (Fin n) (Fin n) D.host.E).map (embT D ((D.fm u).tauOf w v)) * _ = 1
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, hprod,
      Matrix.map_one _ (map_zero _) (map_one _)]
  · intro a b
    show (((Bx⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E).map
        (embT D ((D.fm u).tauOf w v)) *
      ((g⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E).map
        (embT D ((D.fm u).tauOf w v)) *
      (By : Matrix (Fin n) (Fin n) D.host.E).map (embT D ((D.fm u).tauOf w v))) a b ∈ bwA_Ow D w
    rw [← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]
    exact hN a b
  · intro a b
    exact hN' a b

end PI.UnitaryGroupMassFormula.IAT

end
