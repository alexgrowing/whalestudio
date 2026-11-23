import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsLevPairA

noncomputable section

open Finset

namespace PositivityTheory.RgBcC.RealD

variable {n : ℕ}

def BdSqL : Prop :=
  ∀ (n : ℕ) (S : Lt n → Prop), (∀ l m k : Lt n, S l → S m → l.2.1.2 = m.2.1.1 → k.1 = xor l.1 m.1 →
      k.2.1 = (l.2.1.1, m.2.1.2) → S k) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 →
      bdL S E1 E2 * bdL S E1 E2 = 0

def VanKL : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      AdmFor lam lev E1 E2 → ∀ (B : Finset (Lt n)) (j : ℕ) (z : Cq n V), B.Nonempty →
        (∀ l ∈ B, l.1 = true ∧ inUU lev l) → PartL B z → DegL j z →
        WtL E1 E2 (muQ lam lev + (2 : ℝ) • rhoV n) z → bdL isK E1 E2 z = 0 →
        ∃ t : Cq n V, PartL B t ∧ DegL (j + 1) t ∧ WtL E1 E2 (muQ lam lev + (2 : ℝ) • rhoV n) t ∧ bdL isK E1 E2 t = z

def InjRL : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      AdmFor lam lev E1 E2 → ∀ (u : V) (y : Cq n V), u ∈ hwSp E1 E2 (muQ lam lev) → SuppL (inRR lev) y →
        DegL ((omN n).card + 1) y → bdL (inRR lev) E1 E2 y = Pi.single (omN n) u → u = 0

def InjUU : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      AdmFor lam lev E1 E2 → ∀ (u : V) (y : Cq n V), u ∈ hwSp E1 E2 (muQ lam lev) → SuppL (inUU lev) y →
        DegL ((omU lev).card + 1) y → bdL (inUU lev) E1 E2 y = Pi.single (omU lev) u → u = 0

def HCdecL : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ), Monotone lev → ∀ a : FreeAlgebra ℂ (Bool × Fin n × Fin n),
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 →
      ∀ c d, Commute (kA E1 E2 c d) (evKP E1 E2 a)) →
    ∃ b : FreeAlgebra ℂ (Bool × Fin n × Fin n),
      (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 →
        ∀ c d, lev c = lev d → Commute (kA E1 E2 c d) (evLv lev E1 E2 b)) ∧
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 →
        ∀ x : V, ∃ w : Lt n → V, evKP E1 E2 a x - evLv lev E1 E2 b x = ∑ l : Lt n, if inUU lev l then xL E1 E2 l (w l) else 0

def HCdecLv : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ), Monotone lev → ∀ a : FreeAlgebra ℂ (Bool × Fin n × Fin n),
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 →
      ∀ c d, Commute (kA E1 E2 c d) (evKP E1 E2 a)) →
    ∃ b : FreeAlgebra ℂ (Bool × Fin n × Fin n),
      (∀ (H : Type) [AddCommGroup H] [Module ℂ H] (F1 F2 : Fin n → Fin n → Module.End ℂ H), IsLevPairA lev F1 F2 →
        ∀ c d, lev c = lev d → Commute (kA F1 F2 c d) (evLv lev F1 F2 b)) ∧
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 →
        ∀ x : V, ∃ w : Lt n → V, evKP E1 E2 a x - evLv lev E1 E2 b x = ∑ l : Lt n, if inUU lev l then xL E1 E2 l (w l) else 0

theorem isLevPairA_of {V : Type} [AddCommGroup V] [Module ℂ V] {E1 E2 : Fin n → Fin n → Module.End ℂ V}
    (h : IsPairA E1 E2) (lev : Fin n → ℕ) : IsLevPairA lev E1 E2 :=
  fun a b c d _ _ => ⟨h.1 a b c d, h.2.1 a b c d, h.2.2 a b c d⟩

theorem hcdecL_of (h : HCdecLv) : HCdecL := by
  intro n lev hlev a ha
  obtain ⟨b, hb, hb'⟩ := h n lev hlev a ha
  exact ⟨b, fun V _ _ E1 E2 hE c d hcd => hb V E1 E2 (isLevPairA_of hE lev) c d hcd, hb'⟩

def ActUU : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ), Monotone lev → ∀ a b : FreeAlgebra ℂ (Bool × Fin n × Fin n),
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 →
      ∀ c d, Commute (kA E1 E2 c d) (evKP E1 E2 a)) →
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 →
      ∀ x : V, ∃ w : Lt n → V, evKP E1 E2 a x - evLv lev E1 E2 b x = ∑ l : Lt n, if inUU lev l then xL E1 E2 l (w l) else 0) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 →
      ∀ v : V, (∀ l : Lt n, l.1 = false → inUU lev l → xL E1 E2 l v = 0) →
        ∃ w : Cq n V, SuppL (inUU lev) w ∧ DegL ((omU lev).card + 1) w ∧
          Pi.single (omU lev) (evKP E1 E2 a v) - evLc lev E1 E2 b (Pi.single (omU lev) v) = bdL (inUU lev) E1 E2 w

def InjectiveDecompositionAction : Prop := InjUU ∧ HCdecL ∧ ActUU

theorem injective_decomposition_action_of (hB : BdSqL) (hV : VanKL) (hR : BdSqL → VanKL → InjRL) (hU : InjRL → InjUU) (hH : HCdecL) (hA : ActUU) :
    InjectiveDecompositionAction :=
  ⟨hU (hR hB hV), hH, hA⟩

end PositivityTheory.RgBcC.RealD
