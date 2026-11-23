import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfG
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.GlobalConditionOfLocalAgreement

noncomputable section

open scoped Classical

open ValuativeRel NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.Pf.StabIntSh

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem gS_ne : ((gS D : ℕ) : D.host.E) ≠ 0 := by
  unfold gS; push_cast
  exact mul_ne_zero (by exact_mod_cast (D.host.g_prime 0).ne_zero) (by exact_mod_cast (D.host.g_prime 1).ne_zero)

theorem qdPow_mem_iff (k : ℕ) (w : D.host.E) : w ∈ qdPow D k ↔ w / ((gS D : ℕ) : D.host.E) ∈ ddPow D k := by
  unfold qdPow qq
  rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.mem_singleton_mul]
  have h0 := gS_ne (D := D)
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [map_natCast, mul_div_cancel_left₀ _ h0]; exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    rw [map_natCast, mul_div_cancel₀ _ h0]

theorem mem_span_mul_iff {K : Type*} [CommRing K] (O : Subring K) (t : K) (ht : IsUnit t) (S : Set K) (y : K) :
    y ∈ Submodule.span O ((fun s => t * s) '' S) ↔ Ring.inverse t * y ∈ Submodule.span O S := by
  have hinv : Ring.inverse t * t = 1 := Ring.inverse_mul_cancel t ht
  have fwd : ∀ (t' : K) (T : Set K) (x : K), x ∈ Submodule.span O T →
      t' * x ∈ Submodule.span O ((fun s => t' * s) '' T) := by
    intro t' T x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [mul_zero]; exact zero_mem _
    | add x z _ _ hx hz => rw [mul_add]; exact add_mem hx hz
    | smul o x _ hx =>
      rw [Subring.smul_def, smul_eq_mul, mul_left_comm, ← smul_eq_mul, ← Subring.smul_def]
      exact Submodule.smul_mem _ o hx
  constructor
  · intro hy
    have := fwd (Ring.inverse t) _ y hy
    rwa [Set.image_image, show (fun s => Ring.inverse t * (t * s)) = id by
      funext s; rw [← mul_assoc, hinv, one_mul]; rfl, Set.image_id] at this
  · intro hy
    have := fwd t S _ hy
    rwa [← mul_assoc, Ring.mul_inverse_cancel t ht, one_mul] at this

variable (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ q, Agree δ M q) (p : PlF D)

theorem ιgS_mul_inv : (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * (D.s.atP p).ιE (((gS D : ℕ) : D.host.E)⁻¹) = 1 := by
  rw [← map_mul, mul_inv_cancel₀ gS_ne, map_one]

def uGS : (D.s.atP p).Epˣ :=
  ⟨(D.s.atP p).ιE ((gS D : ℕ) : D.host.E), (D.s.atP p).ιE (((gS D : ℕ) : D.host.E)⁻¹), ιgS_mul_inv p,
    by rw [mul_comm]; exact ιgS_mul_inv p⟩

theorem locMem_qd_iff (k : ℕ) (z : D.host.E) :
    LocMem D p (qdPow D k) z ↔ LocMem D p (ddPow D k) (z / ((gS D : ℕ) : D.host.E)) := by
  unfold LocMem
  set ι := (D.s.atP p).ιE
  have hu : IsUnit (ι ((gS D : ℕ) : D.host.E)) := (uGS p).isUnit
  have hset : ι '' (qdPow D k : Set D.host.E) =
      (fun s => ι ((gS D : ℕ) : D.host.E) * s) '' (ι '' (ddPow D k : Set D.host.E)) := by
    rw [Set.image_image]
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w / ((gS D : ℕ) : D.host.E), (qdPow_mem_iff k w).1 hw, ?_⟩
      show ι ((gS D : ℕ) : D.host.E) * ι (w / ((gS D : ℕ) : D.host.E)) = ι w
      rw [← map_mul, mul_div_cancel₀ _ gS_ne]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨((gS D : ℕ) : D.host.E) * y, (qdPow_mem_iff k _).2 (by rwa [mul_div_cancel_left₀ _ gS_ne]), ?_⟩
      show ι (((gS D : ℕ) : D.host.E) * y) = ι ((gS D : ℕ) : D.host.E) * ι y
      rw [map_mul]
  rw [hset, mem_span_mul_iff _ _ hu]
  have hi : Ring.inverse (ι ((gS D : ℕ) : D.host.E)) = ι (((gS D : ℕ) : D.host.E)⁻¹) := by
    rw [show ι ((gS D : ℕ) : D.host.E) = ((uGS p : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) from rfl, Ring.inverse_unit]
    rfl
  rw [hi, ← map_mul, div_eq_mul_inv, mul_comm z]

include hA in

theorem qLocG_of_data (g : Loc.SplitG (M p).L) (hs : (M p).split = some g) (k : ℕ) (hk : k ≤ D.R.rS)
    (z : D.host.E) :
    LocMem D p (qdPow D k) z ↔ ∃ o ∈ (D.s.atP p).O,
      cc δ p ^ k * (D.s.atP p).ιE z = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * o := by
  rw [locMem_qd_iff, locMem_iff δ M hA p hk]
  set ι := (D.s.atP p).ιE

  obtain ⟨sg, hsg, hq⟩ : ∃ sg, (D.s.atP p).split = some sg ∧ g.q = sg.q := by
    have h6 := (hA p).2.2.2.2.2
    cases hD : (D.s.atP p).split with
    | none => rw [hs, hD] at h6; exact h6.elim
    | some sg => rw [hs, hD] at h6; exact ⟨sg, rfl, h6.2⟩
  have hgp := Formalism.MainNotions.BridgeLemma.gpart_some p sg hsg

  have hgS : ι ((gS D : ℕ) : D.host.E) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * ι ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) := by
    rw [hq, sg.q_eq, ← Formalism.MainNotions.BridgeLemma.gpart_mul_oth p, hgp]
    simp only [Nat.cast_mul, map_mul, map_natCast]
  have huP : ι (uP p : D.host.E) * ι ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) = 1 := by
    rw [← map_mul, Formalism.MainNotions.BridgeLemma.unitAt_eq p]
    have h0 : ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) ≠ 0 := by
      exact_mod_cast Formalism.MainNotions.BridgeLemma.oth_ne_zero p
    push_cast
    rw [inv_mul_cancel₀ h0, map_one]
  have huO : ι (uP p : D.host.E) ∈ (D.s.atP p).O := LocFacts.unitPart_mem₂ p
  have hoO : ι ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) ∈ (D.s.atP p).O := by
    rw [map_natCast]; exact natCast_mem _ _
  have hz : ι z = ι (z / ((gS D : ℕ) : D.host.E)) * ι ((gS D : ℕ) : D.host.E) := by
    rw [← map_mul, div_mul_cancel₀ _ gS_ne]
  constructor
  · intro h
    refine ⟨ι ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) * (cc δ p ^ k * ι (z / ((gS D : ℕ) : D.host.E))),
      mul_mem hoO h, ?_⟩
    rw [hz, hgS]; ring
  · rintro ⟨o, ho, he⟩
    have : cc δ p ^ k * ι (z / ((gS D : ℕ) : D.host.E)) = o * ι (uP p : D.host.E) := by
      have h1 : cc δ p ^ k * ι (z / ((gS D : ℕ) : D.host.E)) * ι ((gS D : ℕ) : D.host.E) =
          o * ι (uP p : D.host.E) * ι ((gS D : ℕ) : D.host.E) := by
        rw [mul_assoc, ← hz, he, hgS]
        linear_combination (-(algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * o)) * huP
      have hu : IsUnit (ι ((gS D : ℕ) : D.host.E)) := (uGS p).isUnit
      exact hu.mul_right_cancel h1
    rw [this]; exact mul_mem ho huO

theorem qLocG : QLocG D := fun δ M hA p g hs k hk z => qLocG_of_data δ M hA p g hs k hk z

theorem locShapeG : LocShapeG D := locShapeG_of qLocG

end Formalism.L2.SG.Pf.StabIntSh
