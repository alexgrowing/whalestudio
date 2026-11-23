import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtOfMulRight
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

section Core

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {N : ℕ}

theorem chartQ_ratEval_mem (x : Fin (N + 1) → Ω) (c : Fin (N + 1))
    (g : MRing (fun _ : Unit => Fin (N + 1))) : ratEval x c g ∈ chartQ x c := by
  induction g using MvPolynomial.induction_on with
  | C a => simpa using intCast_mem (chartQ x c) a
  | add a b ha hb => simpa using (chartQ x c).add_mem ha hb
  | mul_X a i ha =>
    have hi : x i.2 / x c ∈ chartQ x c := Algebra.subset_adjoin ⟨i.2, rfl⟩
    simpa using (chartQ x c).mul_mem ha hi

theorem adjoin_insert_eq_invAdj (R : Set Ω) (h : Ω) :
    Algebra.adjoin ℚ (insert h⁻¹ R) = invAdj (Algebra.adjoin ℚ R) h := by
  apply le_antisymm
  · exact Algebra.adjoin_mono (Set.insert_subset_insert Algebra.subset_adjoin)
  · refine Algebra.adjoin_le (Set.insert_subset (Algebra.subset_adjoin (Set.mem_insert _ _)) ?_)
    exact fun _ hs => Algebra.adjoin_mono (Set.subset_insert _ _) hs

theorem exists_sum_eq_one_of_span_eq_top {R : Type} [CommRing R] (T : Set R) (hT : Ideal.span T = ⊤) :
    ∃ (m : ℕ) (f a : Fin m → R), (∀ l, f l ∈ T) ∧ ∑ l, a l * f l = 1 := by
  classical
  have h1 : (1 : R) ∈ Ideal.span T := hT ▸ Submodule.mem_top
  obtain ⟨w, hw, hs⟩ := Submodule.mem_span_set.1 h1
  let ε := w.support.equivFin
  refine ⟨w.support.card, fun l => (ε.symm l : R), fun l => w (ε.symm l), fun l => hw (ε.symm l).2, ?_⟩
  rw [← hs, Finsupp.sum, ← Finset.sum_coe_sort w.support (fun i => w i • i)]
  exact Equiv.sum_comp ε.symm (fun i : w.support => w i • (i : R))

theorem chart_cover_core {P : Type} (u : P → Ω → Prop) (hu0 : ∀ p h, u p h → h ≠ 0) (C B : Set P)
    (Pt Bd : Set (Subring Ω)) (x : Fin (N + 1) → Ω) (c : Fin (N + 1)) (e : ℕ)
    (bd : Ideal (MRing (fun _ : Unit => Fin (N + 1))))
    (h1 : ∀ p ∈ C, ∃ h ∈ chartQ x c, u p h ∧ ∃ (z : Fin e → invAdj (chartQ x c) h) (n : ℕ),
      IsSncPatch Pt Bd e (invAdj (chartQ x c) h) z n)
    (h2 : ∀ I : Ideal (chartQ x c), I.IsPrime → ∃ p ∈ C, ∀ s : chartQ x c, s ∉ I ↔ u p (s : Ω))
    (h3 : ∀ h, h ∈ chartQ x c → h ≠ 0 → ∀ q : Ideal (invAdj (chartQ x c) h), q.IsPrime →
      ∃ p ∈ C, (∀ s : invAdj (chartQ x c) h, s ∉ q ↔ u p (s : Ω)) ∧
        ∀ (z : Fin e → invAdj (chartQ x c) h) (n : ℕ), IsSncPatch Pt Bd e (invAdj (chartQ x c) h) z n →
          (p ∈ B ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q))
    (h4 : ∀ p ∈ C, (p ∈ B ↔ ∀ g ∈ bd, ¬ u p (ratEval x c g))) :
    ∃ (m : ℕ) (f a : Fin m → Ω), (∀ l, f l ∈ chartQ x c) ∧ (∀ l, a l ∈ chartQ x c) ∧
      ∑ l, a l * f l = 1 ∧ ∀ l, f l ≠ 0 → ∀ S : Subalgebra ℚ Ω,
        S = Algebra.adjoin ℚ (insert (f l)⁻¹ (Set.range fun j => x j / x c)) →
        Algebra.Smooth ℚ S ∧ ∃ (z : Fin e → S) (n : ℕ), n ≤ e ∧
          LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)) ∧
          Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ ∧
          ∀ q : Ideal S, q.IsPrime →
            ((∀ g ∈ bd, ∀ s : S, (s : Ω) = ratEval x c g → s ∈ q) ↔
              ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q) := by
  let T : Set (chartQ x c) := {t | (t : Ω) ≠ 0 ∧ ∃ (z : Fin e → invAdj (chartQ x c) (t : Ω)) (n : ℕ),
    IsSncPatch Pt Bd e (invAdj (chartQ x c) (t : Ω)) z n}
  have hT : Ideal.span T = ⊤ := by
    by_contra hne
    obtain ⟨I, hI, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨p, hp, hs⟩ := h2 I hI.isPrime
    obtain ⟨h, hh, hu, z, n, hz⟩ := h1 p hp
    have hmem : (⟨h, hh⟩ : chartQ x c) ∈ T := ⟨hu0 p h hu, z, n, hz⟩
    exact (hs ⟨h, hh⟩).2 hu (hle (Ideal.subset_span hmem))
  obtain ⟨m, f, a, hf, hsum⟩ := exists_sum_eq_one_of_span_eq_top T hT
  refine ⟨m, fun l => f l, fun l => a l, fun l => (f l).2, fun l => (a l).2, ?_, ?_⟩
  · have := congrArg (Subtype.val) hsum
    simpa using this
  · intro l hl S hS
    rw [adjoin_insert_eq_invAdj] at hS
    subst hS
    obtain ⟨-, z, n, hz⟩ := hf l
    refine ⟨hz.smooth, z, n, hz.le, hz.li, hz.span, fun q hq => ?_⟩
    obtain ⟨p, hp, hs, hb⟩ := h3 _ (f l).2 hl q hq
    rw [← hb z n hz, h4 p hp]
    constructor
    · intro H g hg hu
      exact (hs ⟨ratEval x c g, le_invAdj _ _ (chartQ_ratEval_mem x c g)⟩).2 hu (H g hg _ rfl)
    · intro H g hg s hsg
      by_contra hn
      exact H g hg (hsg ▸ (hs s).1 hn)

end Core

theorem range_ratios_unit {Ω : Type} [Field Ω] {N : ℕ} (x : Fin (N + 1) → Ω) (c : Unit → Fin (N + 1)) :
    (Set.range fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2 / x (c p.1)) =
      Set.range fun j => x j / x (c ()) := by
  ext w
  constructor
  · rintro ⟨⟨_, j⟩, rfl⟩
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨⟨(), j⟩, rfl⟩

theorem isSncModel_of_chart_patches : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ) (B : Set (Cpt ξ)) (bd : Ideal (MRing (fun _ : Unit => Fin (N + 1)))), (∀ c (p : Cpt ξ), Char0 ξ p → InChart ξ x c p → ∃ h ∈ Mdl.chartQ x c, unitAt ξ p h ∧ ∃ (z : Fin e → Mdl.invAdj (Mdl.chartQ x c) h) (n : ℕ), IsSncPatch (Pts ξ) (regAt ξ '' B) e (Mdl.invAdj (Mdl.chartQ x c) h) z n) → (∀ c, x c ≠ 0 → ∀ I : Ideal (Mdl.chartQ x c), I.IsPrime → ∃ p : Cpt ξ, Char0 ξ p ∧ InChart ξ x c p ∧ ∀ s : Mdl.chartQ x c, s ∉ I ↔ unitAt ξ p (s : Ω)) → (∀ c h, x c ≠ 0 → h ∈ Mdl.chartQ x c → h ≠ 0 → ∀ q : Ideal (Mdl.invAdj (Mdl.chartQ x c) h), q.IsPrime → ∃ p : Cpt ξ, Char0 ξ p ∧ InChart ξ x c p ∧ (∀ s : Mdl.invAdj (Mdl.chartQ x c) h, s ∉ q ↔ unitAt ξ p (s : Ω)) ∧ ∀ (z : Fin e → Mdl.invAdj (Mdl.chartQ x c) h) (n : ℕ), IsSncPatch (Pts ξ) (regAt ξ '' B) e (Mdl.invAdj (Mdl.chartQ x c) h) z n → (p ∈ B ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)) → (∀ c (p : Cpt ξ), Char0 ξ p → InChart ξ x c p → (p ∈ B ↔ ∀ g ∈ bd, ¬ unitAt ξ p (Mdl.ratEval x c g))) → Cmp.IsSncModel (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) e bd := by
  intro Ω _ _ X ξ N x e B bd h1 h2 h3 h4
  unfold Cmp.IsSncModel
  intro c hc
  have hx : x (c ()) ≠ 0 := hc ()
  have key := chart_cover_core (P := Cpt ξ) (fun p h => unitAt ξ p h) (fun p h hh => hh.1)
    {p | Char0 ξ p ∧ InChart ξ x (c ()) p} B (Pts ξ) (regAt ξ '' B) x (c ()) e bd
    (fun p hp => h1 _ p hp.1 hp.2)
    (fun I hI => by
      obtain ⟨p, a, b, d⟩ := h2 _ hx I hI
      exact ⟨p, ⟨a, b⟩, d⟩)
    (fun h hh h0 q hq => by
      obtain ⟨p, a, b, d, f⟩ := h3 _ h hx hh h0 q hq
      exact ⟨p, ⟨a, b⟩, d, f⟩)
    (fun p hp => h4 _ p hp.1 hp.2)
  beta_reduce
  rw [range_ratios_unit x c]
  exact key

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
