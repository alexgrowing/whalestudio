import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZChartSmulSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleZTwist
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleTwistLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

theorem ZChartSmul.proof : ZChartSmul.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ G H r h hh J j hj I a ha z hz
  classical
  have hmem : ∀ l, h l ∈ H.sub I := fun l => (Submodule.mem_iInf _).mp (hh l) I
  refine Submodule.span_induction (p := fun z _ => a • z ∈ secsOnZChart G H h I J) ?_ ?_ ?_ ?_ hz
  · rintro e ⟨m, hm⟩
    obtain ⟨n, hn⟩ := Set.mem_iInter.mp ha I
    rw [one_mul] at hn
    set u := ∏ l ∈ J.1.erase j, h l with hu
    have hxu : xProd J = h j * u := (Finset.mul_prod_erase J.1 h hj).symm
    have hk : J.1.card = (J.1.erase j).card + 1 := by
      rw [Finset.card_erase_of_mem hj]
      have := Finset.card_pos.mpr ⟨j, hj⟩
      omega
    have hun : u ^ n ∈ (H.pow ((J.1.erase j).card * n)).sub I :=
      AmpleTwistLocal.pow_mem_pow H I (VeryAmpleZTwist.prod_mem_pow H I hmem _) n
    have hw : a * h j ^ n * u ^ n ∈ (H.pow (n + (J.1.erase j).card * n)).sub I :=
      AmpleTwistLocal.mul_mem_pow H I hn _ hun
    have h1 := VeryAmpleZTwist.smul_mem_twist_pow G H I hw hm
    refine Submodule.subset_span ⟨m + n, ?_⟩
    have e1 : xProd J ^ (m + n) • a • e = (a * h j ^ n * u ^ n) • xProd J ^ m • e := by
      rw [smul_smul, smul_smul, hxu]; ring_nf
    have e2 : J.1.card * (m + n) = J.1.card * m + (n + (J.1.erase j).card * n) := by
      rw [hk]; ring
    rw [e1, e2]
    exact h1
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro b c _ _ hb hc; rw [smul_add]; exact Submodule.add_mem _ hb hc
  · intro s y _ hy; rw [smul_comm]; exact Submodule.smul_mem _ s hy

end

end GroundTheory.Heights₂.Heights.Kleiman
