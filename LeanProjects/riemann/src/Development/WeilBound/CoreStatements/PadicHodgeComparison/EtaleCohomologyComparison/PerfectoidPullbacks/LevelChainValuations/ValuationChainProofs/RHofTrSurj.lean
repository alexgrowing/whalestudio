import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.TwistAcrisZeroPreservesFiltration

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime]

theorem acris_zero_surjective : Function.Surjective (PAlg.base l).cris0 := by
  rintro ⟨y, hy⟩
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    have hx : xi0 l ∈ RingHom.ker (theta0 l) := by
      rw [ker_theta0]; exact Ideal.mem_span_singleton_self _
    refine ⟨⟨dpw k (xi0 l), ACris.dpow_mem hx k⟩, Subtype.ext ?_⟩
    show awayW (RingHom.id (Ob l)) (dpw k (xi0 l)) = _
    rw [awayW_id, RingHom.id_apply, dpw]
    show _ = Ring.inverse _ * algebraMap _ _ (WittVector.map (RingHom.id (Ob l)) (xi0 l)) ^ k
    rw [wmap_id]
    rfl
  | algebraMap r =>
    refine ⟨algebraMap (Ainf l) (Acris0 l) r, Subtype.ext ?_⟩
    show awayW (RingHom.id (Ob l)) (algebraMap (Ainf l) (WL l (Ob l)) r) = _
    rw [awayW_id, RingHom.id_apply]
    rfl
  | add x y hx hy ihx ihy =>
    obtain ⟨a, ha⟩ := ihx
    obtain ⟨b, hb⟩ := ihy
    exact ⟨a + b, by rw [map_add, ha, hb]; rfl⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨a, ha⟩ := ihx
    obtain ⟨b, hb⟩ := ihy
    exact ⟨a * b, by rw [map_mul, ha, hb]; rfl⟩

theorem acris_level_surjective (n : ℕ) : Function.Surjective ((PAlg.base l).cris n) := by
  intro w
  obtain ⟨y, rfl⟩ := (PAlg.base l).mkAcr_surjective n w
  obtain ⟨z, rfl⟩ := acris_zero_surjective (l := l) y
  exact ⟨AdicCompletion.of _ _ z, (PAlg.base l).cris_of n z⟩

end CrystallineSemistableComparison.Pb.Kap
