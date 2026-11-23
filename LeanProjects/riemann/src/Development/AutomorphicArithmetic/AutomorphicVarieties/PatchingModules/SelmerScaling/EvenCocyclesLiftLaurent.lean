import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelScale
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.AlgebraMapMemSecondOrder

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.k2F :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), K2 h k → EvenCocyclesLiftLaurent h k := by
  intro l _ L G G0 h n x k hK z hz
  set f := algebraMap x.A x.Fr with hf
  have ht : f x.t ≠ 0 := by
    intro h0
    apply PowerSeries.X_ne_zero (R := x.K)
    exact IsFractionRing.injective x.A x.Fr (h0.trans (map_zero f).symm)
  choose s₀ hs using fun i j => selScale l L G G0 h n x true (z i j) (hz i j).1 (hz i j).2
  set S := Finset.univ.sup (fun p : Fin (k.g + 1) × Fin k.g => s₀ p.1 p.2) with hSdef
  have hS : ∀ i j, s₀ i j ≤ S := fun i j =>
    Finset.le_sup (f := fun p : Fin (k.g + 1) × Fin k.g => s₀ p.1 p.2) (Finset.mem_univ (i, j))
  choose z' hz' hzz using fun i j => hs i j S (hS i j)
  obtain ⟨c, hc, Ψ, hΨ, hΨe⟩ := hK z' (fun i j => hz' i j)
  obtain ⟨hΨ1, hΨ2⟩ := selMap2 l L G G0 h n x k Ψ hΨ
  refine ⟨fun i => f (c i) * f x.t ^ S, ?_, _, hΨ1, hΨ2, ?_⟩
  · intro h0
    apply hc
    funext i
    have e := congrFun h0 i
    rcases mul_eq_zero.1 e with e | e
    · exact IsFractionRing.injective x.A x.Fr (e.trans (map_zero f).symm)
    · exact absurd e (pow_ne_zero S ht)
  · intro j γ a b
    have hz2 : ∀ i, f (z' i j γ a b) = f x.t ^ S * z i j γ a b := fun i => by
      have e := congrArg (fun M => M a b) (hzz i j γ)
      simpa using e
    show f ((Ψ γ a b).ep' j) = _
    rw [hΨe j γ a b]
    simp only [Matrix.sum_apply, Finset.sum_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
      map_sum, map_mul, hz2]
    refine Finset.sum_congr rfl fun i _ => by ring
