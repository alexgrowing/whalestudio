import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StFramePlaneGraph
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StFrameGraphGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial

theorem FramePlaneGraph.zeroSetEuc_sup_span {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (q : MvPolynomial (Fin n) ℂ) :
    zeroSetEuc (J ⊔ Ideal.span {q}) = zeroSetEuc J ∩ {z | eval (fun i => z i) q = 0} := by
  ext z
  simp only [zeroSetEuc, Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun p hp => h p (Ideal.mem_sup_left hp),
      h q (Ideal.mem_sup_right (Ideal.mem_span_singleton_self q))⟩
  · rintro ⟨h1, h2⟩ p hp
    have hle : J ⊔ Ideal.span {q} ≤ RingHom.ker (eval fun i => z i) :=
      sup_le (fun p hp => RingHom.mem_ker.mpr (h1 p hp))
        ((Ideal.span_singleton_le_iff_mem _).mpr (RingHom.mem_ker.mpr h2))
    exact RingHom.mem_ker.mp (hle hp)

theorem FramePlaneGraph.lt_of_add_one_le_nat {x : WithBot ℕ∞} {d : ℕ} (h : x + 1 ≤ (d : WithBot ℕ∞)) :
    x < d := by
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe y =>
    have h' : y + 1 ≤ (d : ℕ∞) := by exact_mod_cast h
    have hy : y ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top d) (le_trans le_self_add h')
    have : y < d := (ENat.add_one_le_iff hy).mp h'
    exact_mod_cast this

theorem FramePlaneGraph.dim_sup_span_lt {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : J.IsPrime)
    (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) {q : MvPolynomial (Fin n) ℂ} (hq : q ∉ J) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {q})) < d := by
  have hr : Ideal.Quotient.mk J q ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ J) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have hle : J ≤ J ⊔ Ideal.span {q} := le_sup_left
  have h1 := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
    (Ideal.Quotient.factor_surjective hle) hr (by
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self q))
  exact FramePlaneGraph.lt_of_add_one_le_nat (hd ▸ h1)

theorem FramePlaneGraph.proof (hG : FrameGraphGeneric.Statement) : FramePlaneGraph.Statement := by
  intro n d J hJ hd b
  obtain ⟨I₀, q, hcard, hq, hloc⟩ := hG n d J hJ hd b
  refine ⟨I₀, J ⊔ Ideal.span {q}, hcard, FramePlaneGraph.dim_sup_span_lt hJ hd hq, ?_⟩
  set W : Set (EuclideanSpace ℂ (Fin n)) := {z | eval (fun i => z i) q ≠ 0} with hWdef
  have hS : zeroSetEuc J \ zeroSetEuc (J ⊔ Ideal.span {q}) = zeroSetEuc J ∩ W := by
    rw [FramePlaneGraph.zeroSetEuc_sup_span]
    ext z
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq, hWdef]
    tauto
  have hW : IsOpen W := isOpen_ne_fun ((MvPolynomial.continuous_eval q).comp
    (by fun_prop : Continuous fun z : EuclideanSpace ℂ (Fin n) => fun i => z i)) continuous_const
  rw [hS]
  intro z hz
  obtain ⟨Ω, V, g, hΩ, hV, hzV, hg, hπ, hgraph⟩ := hloc z hz.1 hz.2
  refine ⟨Ω ∩ g ⁻¹' W, V ∩ W, g, hg.continuousOn.isOpen_inter_preimage hΩ hW, hV.inter hW,
    ⟨hzV, hz.2⟩, hg.mono Set.inter_subset_left, fun w hw => hπ w hw.1, ?_⟩
  ext x
  constructor
  · rintro ⟨⟨hxJ, hxW⟩, hxV, -⟩
    have hx : x ∈ g '' Ω := hgraph ▸ ⟨hxJ, hxV⟩
    obtain ⟨w, hw, rfl⟩ := hx
    exact ⟨w, ⟨hw, hxW⟩, rfl⟩
  · rintro ⟨w, ⟨hw, hwW⟩, rfl⟩
    have hx : g w ∈ zeroSetEuc J ∩ V := hgraph.symm ▸ ⟨w, hw, rfl⟩
    exact ⟨⟨hx.1, hwW⟩, hx.2, hwW⟩

end

end GroundTheory.Heights₂.Heights
