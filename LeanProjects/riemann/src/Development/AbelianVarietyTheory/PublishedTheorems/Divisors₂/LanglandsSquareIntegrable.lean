import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar

namespace GlobalTheory.Published

def LanglandsSquareIntegrable : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
        ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
          ∀ (T : Finset (Fin r)) (φ : GAd σ J → ℂ), IsAutOn σ J X Y T K φ →
            (IsSqIntOn σ J X Y T φ ↔ ∀ S, T ⊆ S → ∀ s, IsCuspExp σ J X Y S K φ s → NegExp S T s)

def LanglandsLemmaUnitary : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
        ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
          ∀ (T : Finset (Fin r)) (φ : GAd σ J → ℂ), IsAutOn σ J X Y T K φ →
            (∀ S, T ⊆ S → ∃! φc, IsCuspComp σ J X Y S K φ φc) ∧
            ((∀ S, T ⊆ S → IsCuspComp σ J X Y S K φ 0) → φ = 0) ∧
            (φ ≠ 0 → ∃ S, T ⊆ S ∧ ∃ s, IsCuspExp σ J X Y S K φ s)

def AutomorphicFormsUnitary : Prop := LanglandsSquareIntegrable ∧ LanglandsLemmaUnitary

end GlobalTheory.Published

namespace GlobalTheory.StdPar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E} {K : Subgroup (GAd σ J)} {φ : GAd σ J → ℂ}

theorem isSqInt_iff (H : GlobalTheory.Published.LanglandsSquareIntegrable) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (hW : IsWittFrame σ J X Y) (hK : IsMaxCpt σ J K) (hφ : IsAut σ J K φ) :
    IsSqInt σ J φ ↔ ∀ S s, IsCuspExp σ J X Y S K φ s → ∀ k ∈ S, ∑ i with i ≤ k, (s i).re < 0 := by
  simpa only [isSqIntOn_empty, negExp_empty, Finset.empty_subset, forall_const] using
    H F E σ h n J hJ r X Y hW K hK ∅ φ (isAutOn_empty.2 hφ)

theorem IsAutOn.isConstAlong_self {S : Finset (Fin r)} (hφ : IsAutOn σ J X Y S K φ) : IsConstAlong σ J X S φ φ :=
  fun μ 𝓕 _ _ h1 g => by simp [fun u : unip σ J X S => hφ.leftN u u.2 g, Measure.real, h1]

omit [NumberField E] in

theorem isConstAlong_empty {c : GAd σ J → ℂ} (hc : IsConstAlong σ J X ∅ φ c) : c = φ := by
  unfold IsConstAlong at hc
  rw [unip_empty] at hc
  haveI : Finite (⊥ : Subgroup (GAd σ J)) := inferInstance
  haveI : Subsingleton ((ratPts σ J).subgroupOf ⊥) := inferInstance
  have e : (Measure.haarMeasure ⊤ : Measure (⊥ : Subgroup (GAd σ J))) Set.univ = 1 := Measure.haarMeasure_self
  funext g
  rw [hc (Measure.haarMeasure ⊤) Set.univ inferInstance
    ⟨nullMeasurableSet_univ, .of_forall fun _ => ⟨1, trivial⟩, Subsingleton.pairwise⟩ e g]
  simp [fun u : (⊥ : Subgroup (GAd σ J)) => Subgroup.mem_bot.1 u.2, Measure.real, e]

theorem isCuspComp_self (H : GlobalTheory.Published.LanglandsLemmaUnitary) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (hW : IsWittFrame σ J X Y) (hK : IsMaxCpt σ J K) (hφ : IsCuspOn σ J X Y ∅ K φ) : IsCuspComp σ J X Y ∅ K φ φ := by
  obtain ⟨_, ⟨-, c, h1, h2⟩, -⟩ := (H F E σ h n J hJ r X Y hW K hK ∅ φ hφ.1).1 ∅ le_rfl
  obtain rfl := isConstAlong_empty h1
  exact ⟨hφ, c, h1, fun ψ hψ μ 𝓕 a b g g' => ⟨(h2 ψ hψ μ 𝓕 a b g g').1, (h2 ψ hψ μ 𝓕 a b g g').1, rfl⟩⟩

example (H : GlobalTheory.Published.LanglandsSquareIntegrable) (h : IsCMExt F E σ) (hJ : IsHermND σ J) {X Y : Matrix (Fin n) (Fin 0) E}
    (hW : IsWittFrame σ J X Y) (hK : IsMaxCpt σ J K) (hφ : IsAut σ J K φ) : IsSqInt σ J φ :=
  (isSqInt_iff H h hJ hW hK hφ).2 fun _ _ _ k => k.elim0

end GlobalTheory.StdPar

end
