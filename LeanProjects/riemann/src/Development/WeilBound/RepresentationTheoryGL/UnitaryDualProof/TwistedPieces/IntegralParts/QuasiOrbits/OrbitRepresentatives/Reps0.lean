import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ZNClosed
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.Imports
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.GradeColMatMulVec
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.ExistsEquivLs

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.TP.Nil.Orb

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BReps

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Reps0 : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → ∃ s : Finset (Sp k n),
    (∀ p ∈ s, p.1 ∈ Bz Z ∧ IsNilpotent p.1 ∧ p.2 ≠ 0 ∧
      ∃ (P : GL (Fin n) k) (w : Fin n → ℤ), (∀ t : kˣ,
        let g : Matrix (Fin n) (Fin n) k := P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val
        (∀ a ∈ Z, a * g = g * a) ∧ g * p.1 = (t : k) • (p.1 * g) ∧ g *ᵥ p.2 = p.2) ∧
      ∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * p.1 = p.1 * a →
        ∃ u : Fin n → k, a *ᵥ p.2 = P.val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0) ∧
    ∀ x ∈ Bz Z, IsNilpotent x → ∀ v : Fin n → k, v ≠ 0 → ∃ p ∈ s, (x, v) ∈ orb Z p

theorem repsP : PositivityTheory.RgUd.T.Nil.Orb.Reps (k := k) := by
  classical
  intro n Z hZ c hc
  obtain ⟨M, _, L, _, hL, R, o, hF⟩ := PositivityTheory.RgUd.T.Nil.Orb.BReps.exists_frames Z hZ.1 hZ.2
  haveI := hL
  let typ : ∀ (N : Matrix (Fin n) (Fin n) k) (v : Fin n → k),
      PositivityTheory.RgUd.T.Nil.Orb.BReps.Frame Z M L R o N v →
      (M → Fin (n + 1) → Fin (n + 1) → Fin (n + 1)) := fun N v F m ℓ σ =>
    ⟨Nat.card {a : F.ι m // F.l m a = (ℓ : ℕ) ∧ F.s m a = (σ : ℕ)}, by
      haveI := F.fι m
      exact Nat.lt_succ_of_le ((Finite.card_subtype_le _).trans (F.card_le m))⟩
  let Good : (M → Fin (n + 1) → Fin (n + 1) → Fin (n + 1)) → Prop := fun θ =>
    ∃ q : Sp k n, q.1 ∈ Bz Z ∧ IsNilpotent (q.1 - c) ∧ q.2 ≠ 0 ∧
      ∃ F : PositivityTheory.RgUd.T.Nil.Orb.BReps.Frame Z M L R o (q.1 - c) q.2, typ _ _ F = θ
  refine ⟨(Finset.univ.filter Good).image
    (fun θ => if h : Good θ then Classical.choose h else ((0 : Matrix (Fin n) (Fin n) k), (0 : Fin n → k))),
    ?_, ?_⟩
  · intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨θ, hθ, rfl⟩ := hp
    have hG : Good θ := (Finset.mem_filter.1 hθ).2
    simp only [dif_pos hG]
    obtain ⟨h1, h2, h3, F, -⟩ := Classical.choose_spec hG
    refine ⟨h1, h2, h3, ?_⟩
    obtain ⟨P, w, hPw, hA⟩ := PositivityTheory.RgUd.T.Nil.Orb.BReps.grade_of_frame F
    refine ⟨P, w, hPw, ?_⟩
    intro a ha hap
    apply hA a ha
    have hca : c * a = a * c := ha c hc
    rw [mul_sub, sub_mul, hap, hca]
  · intro x hx hnil v hv
    have hcomm : ∀ z ∈ Z, z * (x - c) = (x - c) * z := by
      intro z hz
      rw [mul_sub, sub_mul, hx z hz, hZ.1 z hz c hc]
    obtain ⟨F⟩ := hF (x - c) hcomm hnil v
    have hG : Good (typ _ _ F) := ⟨(x, v), hx, hnil, hv, F, rfl⟩
    refine ⟨Classical.choose hG, ?_, ?_⟩
    · rw [Finset.mem_image]
      exact ⟨typ _ _ F, Finset.mem_filter.2 ⟨Finset.mem_univ _, hG⟩, dif_pos hG⟩
    · obtain ⟨h1, h2, h3, F', hF'⟩ := Classical.choose_spec hG
      obtain ⟨g, hgZ, hgN, hgv⟩ := PositivityTheory.RgUd.T.Nil.Orb.BReps.conj_of_frames F' F (by
        intro m ℓ σ hℓ hσ
        have e := congrFun (congrFun (congrFun hF' m) ⟨ℓ, Nat.lt_succ_of_le hℓ⟩)
          ⟨σ, Nat.lt_succ_of_le hσ⟩
        exact congrArg Fin.val e)
      refine ⟨g, hgZ, ?_⟩
      have hcg : c * (g : Matrix (Fin n) (Fin n) k) = g * c := hgZ c hc
      have e : (g : Matrix (Fin n) (Fin n) k) * (Classical.choose hG).1 = x * g := by
        have h4 := hgN
        rw [mul_sub, sub_mul, ← hcg] at h4
        exact sub_left_inj.mp h4
      show ((g : Matrix (Fin n) (Fin n) k) * (Classical.choose hG).1 *
          ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k),
          (g : Matrix (Fin n) (Fin n) k) *ᵥ (Classical.choose hG).2) = (x, v)
      rw [e, mul_assoc, Units.mul_inv, mul_one, hgv]

theorem reps0 : Reps0 k := by
  intro n Z hZ
  obtain ⟨s, hs1, hs2⟩ := repsP k n Z hZ 0 Z.zero_mem
  refine ⟨s, ?_, ?_⟩
  · intro p hp
    simpa using hs1 p hp
  · intro x hx hnil v hv
    exact hs2 x hx (by simpa using hnil) v hv

end PositivityTheory.RgUd.TP.Nil.Orb
