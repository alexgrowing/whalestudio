import Development.EtaleCohomology.KummerTheory.AdicDegPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def AdicKer : Prop := A11 → ∀ (l : ℕ) [Fact l.Prime] (E : Spc) (i : ℤ), (∀ b, BockData l b E i) →
  (∀ (k : ℕ) (n : ℤ), Finite (Ht (l ^ k) E n i)) → ∀ (n : ℤ) (k : ℕ) (x : Hl l E n i), lev l x k = 0 →
    ∃ y : Hl l E n i, x = ((l : ℤ_[l]) ^ k) • y

def AdicFin : Prop := ∀ (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ), (∀ k : ℕ, Finite (Ht (l ^ k) E n i)) →
  (∀ (k : ℕ) (x : Hl l E n i), lev l x k = 0 → ∃ y : Hl l E n i, x = ((l : ℤ_[l]) ^ k) • y) →
    Module.Finite ℤ_[l] (Hl l E n i)

def AdicCok : Prop := A11 → ∀ (l : ℕ) [Fact l.Prime] (E : Spc) (i : ℤ), (∀ b, BockData l b E i) →
  (∀ (k : ℕ) (n : ℤ), Finite (Ht (l ^ k) E n i)) → ∀ n : ℤ, Module.Finite ℤ_[l] (Hl l E (n + 1) i) →
    ∃ M : ℕ, 0 < M ∧ ∀ (k : ℕ) (z : Ht (l ^ k) E n i), ∃ x : Hl l E n i, lev l x k = M • z

theorem AdicLim_of (hK : AdicKer) (hF : AdicFin) (hC : AdicCok) : AdicLim := by
  intro hA l _ E i hB hFin n
  have hker : ∀ m : ℤ, ∀ (k : ℕ) (x : Hl l E m i), lev l x k = 0 → ∃ y : Hl l E m i, x = ((l : ℤ_[l]) ^ k) • y :=
    fun m => hK hA l E i hB hFin m
  have hfin : ∀ m : ℤ, Module.Finite ℤ_[l] (Hl l E m i) := fun m => hF l E m i (fun k => hFin k m) (hker m)
  exact ⟨hfin n, hker n, hC hA l E i hB hFin n (hfin (n + 1))⟩

end LateralTheory.KummerTheory
