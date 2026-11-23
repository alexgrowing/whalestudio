import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSubAug
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RkSubSuccLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteLengthLeviQuotientStatement

noncomputable section

open GlobalTheory.SplitWeil GlobalTheory.ThetaGLSub GlobalTheory.ThetaGLRank GlobalTheory.SmGL

namespace GlobalTheory.ThetaGLLayer

theorem exists_chain_bound {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (h : IsFiniteLength R M) :
    ∃ L : ℕ, ∀ (r : ℕ) (s : Fin r → Submodule R M), StrictMono s → r ≤ L := by
  refine ⟨(Module.length R M).toNat + 1, fun r s hs => ?_⟩
  rcases r with _ | r
  · exact Nat.zero_le _
  let p : LTSeries (Submodule R M) := ⟨r, s, fun i => hs Fin.castSucc_lt_succ⟩
  have h1 : (r : ℕ∞) ≤ Module.length R M := by
    rw [Module.length_eq_height]
    exact (Order.length_le_height_last (p := p)).trans (Order.height_mono le_top)
  have h2 : Module.length R M ≠ ⊤ := Module.length_ne_top_iff.2 h
  have h3 : r ≤ (Module.length R M).toNat := by
    rw [← ENat.coe_le_coe, ENat.coe_toNat h2]; exact h1
  omega

theorem exists_subrep_chain_bound {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (h : HasFiniteLength π) :
    ∃ L : ℕ, ∀ (r : ℕ) (s : Fin r → Subrepresentation π), StrictMono s → r ≤ L := by
  obtain ⟨L, hL⟩ := exists_chain_bound h
  exact ⟨L, fun r s hs => hL r _ (Subrepresentation.subrepresentationSubmoduleOrderIso.strictMono.comp hs)⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n m : ℕ}

theorem layer_bound_of_cover (χ : GL (Fin n) k →* ℂˣ) (ρ : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin m) k) V) (hπ : HasFiniteLength π)
    (f : V →ₗ[ℂ] (Matrix (Fin n) (Fin m) k → ℂ))
    (hf : ∀ (g : GL (Fin m) k) (v : V),
      f (π g v) - om 1 g (1 : GL (Fin n) k) (f v) ∈ aug m χ ⊔ rkSub k n m (ρ + 1))
    (hs : rkSub k n m ρ ≤ aug m χ ⊔ rkSub k n m (ρ + 1) ⊔ LinearMap.range f) :
    ∃ L : ℕ, ∀ (r : ℕ) (N : Fin r → Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)),
      StrictMono N → (∀ i, IsSub χ (N i) ∧
        aug m χ ⊔ rkSub k n m (ρ + 1) ≤ N i ∧ N i ≤ aug m χ ⊔ rkSub k n m ρ) → r ≤ L := by
  obtain ⟨L, hL⟩ := exists_subrep_chain_bound hπ
  refine ⟨L, fun r N hN hNi => ?_⟩
  set C1 := aug m χ ⊔ rkSub k n m (ρ + 1) with hC1

  have key : ∀ i, N i = C1 ⊔ ((N i).comap f).map f := by
    intro i
    have hle : N i ≤ C1 ⊔ LinearMap.range f := by
      refine (hNi i).2.2.trans (sup_le ?_ ?_)
      · exact (le_sup_left : aug m χ ≤ C1).trans (le_sup_left : C1 ≤ C1 ⊔ LinearMap.range f)
      · exact hs
    rw [Submodule.map_comap_eq, ← sup_inf_assoc_of_le _ (hNi i).2.1]
    exact (inf_eq_left.2 hle).symm.trans (inf_comm _ _)
  let S : Fin r → Subrepresentation π := fun i =>
    ⟨(N i).comap f, fun g v hv => by
      show f (π g v) ∈ N i
      have h1 := (hNi i).1.2.2 g (f v) hv
      have h2 : f (π g v) - om 1 g (1 : GL (Fin n) k) (f v) ∈ N i := (hNi i).2.1 (hf g v)
      simpa using Submodule.add_mem _ h2 h1⟩
  have hS : StrictMono S := by
    intro i j hij
    have hle : S i ≤ S j := fun v hv => (hN hij).le hv
    refine lt_of_le_of_ne hle fun he => (hN hij).ne ?_
    have he' : (N i).comap f = (N j).comap f := congrArg Subrepresentation.toSubmodule he
    rw [key i, key j, he']
  exact hL r S hS

end GlobalTheory.ThetaGLLayer

namespace GlobalTheory.ThetaGLLayer

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n m : ℕ}

theorem rkSub_eq_bot_of_lt {ρ : ℕ} (h : m < ρ) : rkSub k n m ρ = ⊥ := by
  refine eq_bot_iff.2 fun Φ hΦ => ?_
  refine funext fun x => hΦ.2 x ?_
  have : x.rank ≤ m := by simpa using Matrix.rank_le_width x
  omega

theorem om_zero (g : GL (Fin m) k) :
    om (1 : kˣ →* ℂˣ) g (1 : GL (Fin n) k) (0 : Matrix (Fin n) (Fin m) k → ℂ) = 0 :=
  funext fun x => by simp [om]

end GlobalTheory.ThetaGLLayer

open GlobalTheory.ThetaGLLayer in

theorem GlobalTheory.ThetaGLLayer.layer_bound : GlobalTheory.FunPr.Hypotheses₂ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) (χ : GL (Fin n) k →* ℂˣ), IsOpen {g | χ g = 1} → ∀ ρ : ℕ,
    ∃ L : ℕ, ∀ (r : ℕ) (N : Fin r → Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)),
      StrictMono N → (∀ i, GlobalTheory.ThetaGLSub.IsSub χ (N i) ∧
        GlobalTheory.ThetaGLSub.aug m χ ⊔ GlobalTheory.ThetaGLRank.rkSub k n m (ρ + 1) ≤ N i ∧
        N i ≤ GlobalTheory.ThetaGLSub.aug m χ ⊔ GlobalTheory.ThetaGLRank.rkSub k n m ρ) → r ≤ L := by
  intro hP k _ _ _ _ n m χ hχ ρ
  by_cases hρ : ρ ≤ m
  · have h : ρ + (m - ρ) = m := Nat.add_sub_cancel' hρ
    obtain ⟨W, _, _, τ, hτs, hτl, f, hf, hs⟩ := GlobalTheory.T.exists_finite_length_levi_quotient k n m χ hχ ρ (m - ρ) h
    have hπ := ((hP.bernsteinZelevinskyFiniteness k).2.2.1).lower (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) hτs hτl
    exact layer_bound_of_cover χ ρ _ hπ f hf hs
  · have hπ : GlobalTheory.SmGL.HasFiniteLength (GlobalTheory.SmGL.ofChar (1 : GL (Fin m) k →* ℂˣ)) :=
      GlobalTheory.SmGL.hasFiniteLength_of_isIrreducible (GlobalTheory.SmGL.isIrreducible_ofChar _)
    refine layer_bound_of_cover χ ρ _ hπ 0 (fun g v => ?_) ?_
    · simp [om_zero]
    · rw [rkSub_eq_bot_of_lt (by omega)]; exact bot_le
