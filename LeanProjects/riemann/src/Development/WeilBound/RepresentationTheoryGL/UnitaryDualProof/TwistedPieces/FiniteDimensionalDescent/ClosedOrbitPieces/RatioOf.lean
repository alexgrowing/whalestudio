import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.TefFinrank
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.PiRatio
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.RankPosOfNe
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.SqSumLe

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

open PositivityTheory.RgUd.TP.Desc.Piece Module

abbrev dA (A : Subalgebra k (Matrix (Fin N) (Fin N) k)) (e : Matrix (Fin N) (Fin N) k) : ℕ :=
  finrank k (A.toSubmodule.map (LinearMap.mulLeft k e))

theorem ratio_of (A : Subalgebra k (Matrix (Fin N) (Fin N) k)) (hA : CR A) {e : Matrix (Fin N) (Fin N) k}
    (he : e ∈ primIdem A) :
    0 < dA A e ∧ dA A e ∣ e.rank ∧
      finrank k ((cenSub A).map (LinearMap.mulLeft k e)) / dA A e = (e.rank / dA A e) ^ 2 := by
  obtain ⟨h0, hd, h⟩ := pi_ratio hA.1 he.1 he.2.1 he.2.2.1 (fun a ha => pi_field hA he ha)
  exact ⟨h0, hd, by rw [h, Nat.mul_div_cancel _ h0]⟩

theorem mu_sum (A : Subalgebra k (Matrix (Fin N) (Fin N) k)) (hA : CR A) :
    mu A = ∑ e ∈ (pi_fin hA).toFinset, (e.rank / dA A e) ^ 2 := by
  unfold mu
  rw [finsum_mem_eq_finite_toFinset_sum _ (pi_fin hA)]
  exact Finset.sum_congr rfl fun e he => (ratio_of A hA ((Set.Finite.mem_toFinset _).mp he)).2.2

theorem m_pos (A : Subalgebra k (Matrix (Fin N) (Fin N) k)) (hA : CR A) {e : Matrix (Fin N) (Fin N) k}
    (he : e ∈ primIdem A) : 1 ≤ e.rank / dA A e := by
  obtain ⟨h0, hd, -⟩ := ratio_of A hA he
  have hr := rank_pos_of_ne he.2.2.1
  obtain ⟨c, hc⟩ := hd
  rw [hc, Nat.mul_div_cancel_left _ h0]
  rcases Nat.eq_zero_or_pos c with rfl | h
  · simp at hc; omega
  · exact h

open Classical in
theorem dich_pt {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q)
    {x : Matrix (Fin N) (Fin N) k} (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) :
    mu (Sx D x) < mu Z ∨ ∃ c ∈ Z, IsNilpotent (x - c) := by
  have hS := sx_cr D hZ hx hχ
  set P := (pi_fin hS).toFinset with hP
  set Q := (pi_fin hZ).toFinset with hQ
  have mP : ∀ {e}, e ∈ P ↔ e ∈ primIdem (Sx D x) := fun {e} => Set.Finite.mem_toFinset _
  have mQ : ∀ {f}, f ∈ Q ↔ f ∈ primIdem Z := fun {f} => Set.Finite.mem_toFinset _

  have hsplit : mu (Sx D x) = ∑ f ∈ Q, ∑ e ∈ P with e * f = e, (e.rank / dA (Sx D x) e) ^ 2 := by
    rw [mu_sum _ hS]
    calc ∑ e ∈ P, (e.rank / dA (Sx D x) e) ^ 2
        = ∑ e ∈ P, ∑ f ∈ Q, if e * f = e then (e.rank / dA (Sx D x) e) ^ 2 else 0 := by
          refine Finset.sum_congr rfl fun e he => ?_
          obtain ⟨f₀, hf₀, hef₀⟩ := ef_exists D hZ hx hχ (mP.mp he)
          rw [Finset.sum_eq_single_of_mem f₀ (mQ.mpr hf₀) fun f hf hne => if_neg fun h =>
            hne (ef_unique D hZ hx hχ (mP.mp he) (mQ.mp hf) hf₀ h hef₀), if_pos hef₀]
      _ = ∑ f ∈ Q, ∑ e ∈ P with e * f = e, (e.rank / dA (Sx D x) e) ^ 2 := by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun f _ => (Finset.sum_filter _ _).symm

  have hfib : ∀ f ∈ Q, ∑ e ∈ P with e * f = e, (e.rank / dA (Sx D x) e) ^ 2 ≤ (f.rank / dA Z f) ^ 2 ∧
      (∑ e ∈ P with e * f = e, (e.rank / dA (Sx D x) e) ^ 2 = (f.rank / dA Z f) ^ 2 →
        f ∈ primIdem (Sx D x) ∧ dA (Sx D x) f ≤ dA Z f) := by
    intro f hf
    have hf' := mQ.mp hf
    have hmem : ∀ e ∈ P.filter (fun e => e * f = e), e ∈ primIdem (Sx D x) ∧ e * f = e := fun e he =>
      ⟨mP.mp (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩
    have hfs := fib_sum D hZ hx hχ hf'
    obtain ⟨hdF, hdvF, -⟩ := ratio_of Z hZ hf'
    have hsum : f.rank / dA Z f * dA Z f =
        ∑ e ∈ P with e * f = e, e.rank / dA (Sx D x) e * dA (Sx D x) e := by
      rw [Nat.div_mul_cancel hdvF]
      conv_lhs => rw [← hfs]
      rw [rank_sum_orth _ _ (fun e he => (hmem e he).1.2.1)
        (fun e he e' he' hne => pi_orth hS (hmem e he).1 (hmem e' he').1 hne)]
      exact Finset.sum_congr rfl fun e he => (Nat.div_mul_cancel (ratio_of _ hS (hmem e he).1).2.1).symm
    obtain ⟨hle, heq⟩ := num_fib (P.filter (fun e => e * f = e)) (fun e => e.rank / dA (Sx D x) e)
      (fun e => dA (Sx D x) e) (f.rank / dA Z f) (dA Z f) hdF (fun e he => m_pos _ hS (hmem e he).1)
      (fun e he => dim_le D hZ hx hχ (hmem e he).1 hf' (hmem e he).2) hsum
    refine ⟨hle, fun h => ?_⟩
    have hne : (P.filter (fun e => e * f = e)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      rw [h0, Finset.sum_empty] at hfs
      exact hf'.2.2.1 hfs.symm
    obtain ⟨e, he⟩ := hne
    obtain ⟨hsing, hde⟩ := heq h ⟨e, he⟩ e he
    have hef : e = f := by rw [← hfs, hsing, Finset.sum_singleton]
    subst hef
    exact ⟨(hmem e he).1, hde⟩

  have hle : mu (Sx D x) ≤ mu Z := by
    rw [hsplit, mu_sum _ hZ]
    exact Finset.sum_le_sum fun f hf => (hfib f hf).1
  by_cases hlt : mu (Sx D x) < mu Z
  · exact Or.inl hlt
  right
  have heq : mu (Sx D x) = mu Z := le_antisymm hle (not_lt.mp hlt)
  rw [hsplit, mu_sum _ hZ] at heq
  have hall := (Finset.sum_eq_sum_iff_of_le fun f hf => (hfib f hf).1).mp heq
  exact zn_of_eq D hZ hx hχ fun f hf => (hfib f (mQ.mpr hf)).2 (hall f (mQ.mpr hf))

variable (k) in
theorem dich : PositivityTheory.RgUd.TP.Desc.Piece.Dich k := by
  intro N q Z hZ χ D τ x₀ hx₀
  exact dich_pt D hZ hx₀.1 hx₀.2.1

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
