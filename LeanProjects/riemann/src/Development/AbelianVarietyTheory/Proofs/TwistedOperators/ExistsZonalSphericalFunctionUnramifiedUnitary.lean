import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSatVecUOfDiag
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
open Formalism.UG (IsUnramInv GU KU Hecke dosetInd)

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ZonalExists

open Formalism.UG

section Generic

variable {G : Type} [Group G] {K : Subgroup G}

def cosetsIn (K : Subgroup G) (g : G) : Set (G ⧸ K) := {x | ∃ a b : K, x.out = (a : G) * g * b}

theorem mem_cosetsIn_iff (x : G ⧸ K) (t : G) :
    x ∈ cosetsIn K t ↔ x.out ∈ DoubleCoset.doubleCoset t (K : Set G) K := by
  rw [DoubleCoset.mem_doubleCoset]
  exact ⟨fun ⟨a, b, e⟩ => ⟨a, a.2, b, b.2, e⟩, fun ⟨a, ha, b, hb, e⟩ => ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩⟩

theorem cosetsIn_eq {g g' : G} (h : g' ∈ DoubleCoset.doubleCoset g (K : Set G) K) :
    cosetsIn K g' = cosetsIn K g := by
  ext x
  rw [mem_cosetsIn_iff, mem_cosetsIn_iff, DoubleCoset.doubleCoset_eq_of_mem h]

theorem dosetInd_eq {g g' : G} (h : g' ∈ DoubleCoset.doubleCoset g (K : Set G) K) :
    dosetInd ℂ K g' = dosetInd ℂ K g := by
  rw [dosetInd, dosetInd, DoubleCoset.doubleCoset_eq_of_mem h]

theorem cosetsIn_ncard_ne_zero (hK : IsCommensurated K) (g : G) : (cosetsIn K g).ncard ≠ 0 := by
  refine ((Set.ncard_pos (P.finite_cosets_in_doset hK g)).2 ⟨(g : G ⧸ K), ?_⟩).ne'
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul K g
  exact ⟨1, u, by simpa using hu⟩

theorem cosetsIn_one : cosetsIn K 1 = {((1 : G) : G ⧸ K)} := by
  ext x
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, b, e⟩
    rw [← QuotientGroup.out_eq' x, e]
    exact QuotientGroup.eq.2 (by simpa using K.inv_mem (K.mul_mem a.2 b.2))
  · rintro rfl
    refine ⟨⟨((1 : G) : G ⧸ K).out, ?_⟩, 1, by simp⟩
    have := QuotientGroup.eq.1 (QuotientGroup.out_eq' ((1 : G) : G ⧸ K))
    simpa using K.inv_mem this

end Generic

theorem exists_isZonal : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ α : Fin (n / 2) → ℂˣ, ∃ w : GU σ n → ℂ,
      GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsZonal ϖ q α w := by
  intro L _ _ _ ϖ σ q n hU α
  classical
  have hK := P.isCommensurated_integral_unitary_of_unramified hU n
  have law := GlobalTheory.LFun.SatCompare.satU_laws (n := n) hU α
  have hN : ∀ g : GU σ n, ((cosetsIn (KU σ n) g).ncard : ℂ) ≠ 0 := fun g =>
    Nat.cast_ne_zero.2 (cosetsIn_ncard_ne_zero hK g)
  let w : GU σ n → ℂ := fun g =>
    SatU ϖ q (dosetInd ℂ (KU σ n) g) (fun i => (α i : ℂ)) / ((cosetsIn (KU σ n) g).ncard : ℂ)
  have hw : ∀ g g' : GU σ n, g' ∈ DoubleCoset.doubleCoset g (KU σ n : Set (GU σ n)) (KU σ n) → w g' = w g :=
    fun g g' h => by simp only [w, dosetInd_eq h, cosetsIn_eq h]
  refine ⟨w, fun a b g => hw _ _ (DoubleCoset.mem_doubleCoset.2 ⟨a, a.2, b, b.2, rfl⟩), ?_, fun h hh => ?_⟩
  · simp only [w, law.2.2, cosetsIn_one, Set.ncard_singleton, Nat.cast_one, div_one]
  refine GlobalTheory.LFun.hecke_induction (K := KU σ n)
    (p := fun f => hAct (KU σ n) f w 1 = SatU ϖ q f fun i => (α i : ℂ)) ?_ ?_ ?_ hh
  · simpa [hAct] using (law.2.1 0 0 (zero_mem _)).symm
  · intro f hf f' hf' e e'
    have fin : ∀ f ∈ Hecke ℂ (KU σ n), (Function.support fun x : GU σ n ⧸ KU σ n => f x.out • w (1 * x.out)).Finite :=
      fun f hf => (P.finite_support_cosets hK hf.2).subset fun x hx h0 => hx (by simp [h0])
    rw [law.1 _ hf _ hf', ← e, ← e', hAct, hAct, hAct]
    simp only [Pi.add_apply, add_smul]
    exact finsum_add_distrib (fin f hf) (fin f' hf')
  · intro r g
    have hfin := P.finite_cosets_in_doset hK g
    have hterm : ∀ x ∈ hfin.toFinset, (r • dosetInd ℂ (KU σ n) g) x.out • w (1 * x.out) = r * w g := fun x hx => by
      have hm := (mem_cosetsIn_iff x g).1 ((Set.Finite.mem_toFinset _).1 hx)
      rw [Pi.smul_apply, dosetInd, Set.indicator_of_mem hm, one_mul, hw g _ hm]
      simp
    rw [law.2.1 r _ (Final.DosetIndMem _ _ ℂ g), hAct,
      finsum_eq_sum_of_support_subset (s := hfin.toFinset), Finset.sum_congr rfl hterm,
      Finset.sum_const, ← Set.ncard_eq_toFinset_card _ hfin, nsmul_eq_mul]
    · have := hN g
      simp only [w]
      rw [← cosetsIn]
      field_simp
    · intro x hx
      rw [Set.Finite.coe_toFinset]
      by_contra h
      refine hx ?_
      show (r • dosetInd ℂ (KU σ n) g) x.out • w (1 * x.out) = 0
      rw [Pi.smul_apply, dosetInd, Set.indicator_of_notMem (fun h' => h ((mem_cosetsIn_iff x g).2 h'))]
      simp

end GlobalTheory.IndefiniteRowSideFullHecke.ZonalExists
