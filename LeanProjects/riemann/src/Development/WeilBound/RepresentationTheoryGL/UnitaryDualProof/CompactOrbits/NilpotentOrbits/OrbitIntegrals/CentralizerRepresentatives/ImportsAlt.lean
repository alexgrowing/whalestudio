import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ZNClosed
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.Imports
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.GradeColMatMulVec
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.ExistsEquivLs

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem reps [CharZero k] : Reps (k := k) := by
  unfold Reps
  intro n Z hZ c hc
  obtain ⟨hcomm, hred⟩ := hZ
  obtain ⟨M, hM, L, hLf, hL, R, o, hF⟩ := exists_frames Z hcomm hred
  classical
  have hcZ : ∀ a ∈ Z, a * c = c * a := fun a ha => hcomm a ha c hc
  have hN : ∀ x ∈ Bz Z, ∀ z ∈ Z, z * (x - c) = (x - c) * z := by
    intro x hx z hz
    rw [mul_sub, sub_mul, hx z hz, hcZ z hz]
  let S : Type := {p : Sp k n // p.1 ∈ Bz Z ∧ IsNilpotent (p.1 - c) ∧ p.2 ≠ 0}
  let F : (p : S) → Frame Z M L R o (p.1.1 - c) p.1.2 := fun p =>
    Classical.choice (hF _ (hN _ p.2.1) p.2.2.1 p.1.2)
  have hb : ∀ (p : S) (m : M) (ℓ σ : ℕ),
      Nat.card {a : (F p).ι m // (F p).l m a = ℓ ∧ (F p).s m a = σ} < n + 1 := by
    intro p m ℓ σ
    haveI := (F p).fι m
    exact Nat.lt_succ_of_le ((Finite.card_subtype_le _).trans ((F p).card_le m))
  let τ : S → M → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) := fun p m ℓ σ =>
    ⟨Nat.card {a : (F p).ι m // (F p).l m a = ℓ.1 ∧ (F p).s m a = σ.1}, hb p m ℓ σ⟩
  have hrep : ∀ t : Set.range τ, ∃ p : S, τ p = t.1 := fun t => t.2
  let rep : Set.range τ → S := fun t => Classical.choose (hrep t)
  have hrepτ : ∀ t, τ (rep t) = t.1 := fun t => Classical.choose_spec (hrep t)
  refine ⟨(Set.finite_range (fun t : Set.range τ => (rep t).1)).toFinset, ?_, ?_⟩
  · intro p hp
    rw [Set.Finite.mem_toFinset] at hp
    obtain ⟨t, rfl⟩ := hp
    obtain ⟨h1, h2, h3⟩ := (rep t).2
    obtain ⟨P, w, hPw, hu⟩ := grade_of_frame (F (rep t))
    refine ⟨h1, h2, h3, P, w, hPw, ?_⟩
    intro a haZ hax
    apply hu a haZ
    have hac : a * c = c * a := (haZ c hc).symm
    rw [mul_sub, sub_mul, hac]
    show a * (rep t).1.1 - c * a = (rep t).1.1 * a - c * a
    rw [hax]
  · intro x hx hnil v hv
    let q : S := ⟨(x, v), hx, hnil, hv⟩
    let t : Set.range τ := ⟨τ q, q, rfl⟩
    refine ⟨(rep t).1, ?_, ?_⟩
    · rw [Set.Finite.mem_toFinset]
      exact ⟨t, rfl⟩
    · have he : τ (rep t) = τ q := hrepτ t
      obtain ⟨g, hgZ, hgN, hgv⟩ := conj_of_frames (F (rep t)) (F q) (by
        intro m ℓ σ hℓ hσ
        exact congrArg (fun f => (f m ⟨ℓ, Nat.lt_succ_of_le hℓ⟩ ⟨σ, Nat.lt_succ_of_le hσ⟩).1) he)
      refine ⟨g, hgZ, ?_⟩
      have hgc : (g : Matrix (Fin n) (Fin n) k) * c = c * g := (hgZ c hc).symm
      have key : (g : Matrix (Fin n) (Fin n) k) * (rep t).1.1 = x * g := by
        have h := hgN
        simp only [mul_sub, sub_mul] at h
        rw [hgc] at h
        simpa using h
      refine Prod.ext ?_ ?_
      · show (g : Matrix (Fin n) (Fin n) k) * (rep t).1.1 * ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = x
        rw [key, mul_assoc, Units.mul_inv, mul_one]
      · exact hgv

end PositivityTheory.RgUd.T.Nil.Orb.BReps
