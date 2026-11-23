import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section G

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem exists_of_mem_smulLat {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    {c : E} {abelian₂ : Submodule M.L.O V} {x : V} (hx : x ∈ H.smulLat c abelian₂) : ∃ l ∈ abelian₂, x = c • l := by
  unfold Formalism.MainNotions.S.Loc.HermSp.smulLat at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact ⟨l, hl, rfl⟩
  | zero => exact ⟨0, abelian₂.zero_mem, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨l, hl, rfl⟩ := hy
    obtain ⟨m, hm, rfl⟩ := hz
    exact ⟨l + m, abelian₂.add_mem hl hm, by simp [smul_add]⟩
  | smul a y _ hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact ⟨a • l, abelian₂.smul_mem a hl, smul_comm a c l⟩

def Lemma0G (M : Model F E) (r : ℕ) : Prop :=
  ∀ g : SplitG M.L, M.split = some g →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (t : Term V M r),
    H.IsGeneric t → ∀ (w : V) (hw : w ∈ H.W0 t.f t.f'),
      (w ∈ t.abelian₂ ↔ (H.mkW t.f ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩ ∈ H.Lset t.abelian₂ t.f ∧
        H.mkW t.f' ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩ ∈ H.Lset t.abelian₂ t.f' ∧
        (H.mkW t.f' ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩, H.mkW t.f ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩) ∈ H.iotaGraph g t))

theorem lemma0G_holds (M : Model F E) (r : ℕ) : Lemma0G M r := by
  intro g hg V _ _ H t hgen w hw
  constructor
  · intro hwL
    refine ⟨⟨⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩, hwL, rfl⟩, ⟨⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩, hwL, rfl⟩, ?_⟩
    refine ⟨⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩, ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩, hwL, hwL, ?_, rfl⟩
    simp only [sub_self]
    exact Submodule.zero_mem _
  · rintro ⟨-, -, x', x, hx'L, hxL, hxx, hp⟩
    simp only [Prod.mk.injEq] at hp
    obtain ⟨hp1, hp2⟩ := hp
    simp only [HermSp.mkW, Submodule.mkQ_apply] at hp1 hp2

    have ha' : w - (x' : V) ∈ H.X t.f' := by
      simpa [Submodule.mem_comap] using (Submodule.Quotient.eq _).1 hp1
    have ha : w - (x : V) ∈ H.X t.f := by
      simpa [Submodule.mem_comap] using (Submodule.Quotient.eq _).1 hp2
    obtain ⟨α', hα'⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 ha'
    obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 ha
    obtain ⟨l, hl, hxl⟩ := exists_of_mem_smulLat H hxx
    have hq0 : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (by exact_mod_cast h0)
    have hqqi : algebraMap F E (g.q : F) * algebraMap F E ((g.q : F)⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hq0, map_one]
    have hqiq : algebraMap F E ((g.q : F)⁻¹) * algebraMap F E (g.q : F) = 1 := by
      rw [mul_comm, hqqi]
    have hMM : H.MMfam t =
        Sum.elim t.f (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) := by
      simp only [HermSp.MMfam, hg]
    obtain ⟨-, hli, hprim⟩ := hgen.2
    rw [hMM] at hli hprim

    let γ : Fin (r + 1) ⊕ Fin (r + 1) → E := Sum.elim
      (Fin.snoc (fun i => algebraMap F E ((g.q : F)⁻¹) * (α' i - α i)) 0) (Fin.snoc α' 0)
    have hsum : ∑ j, γ j • Sum.elim t.f
        (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) j = l := by
      have key : algebraMap F E (g.q : F) • ∑ j, γ j • Sum.elim t.f
          (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) j =
          algebraMap F E (g.q : F) • l := by
        rw [← hxl, Fintype.sum_sum_type]
        simp only [γ, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
          Fin.snoc_last, zero_smul, add_zero, smul_add, Finset.smul_sum]
        have e1 : (x : V) - x' = (w - x') - (w - x) := by abel
        rw [e1, ← hα', ← hα, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, ← mul_assoc, hqqi, one_mul, smul_comm (algebraMap F E (g.q : F)) (α' i),
          smul_smul (algebraMap F E (g.q : F)), hqqi, one_smul, sub_smul, smul_sub]
        abel
      calc _ = (algebraMap F E ((g.q : F)⁻¹) * algebraMap F E (g.q : F)) • ∑ j, γ j • Sum.elim t.f
              (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) j := by
            rw [hqiq, one_smul]
        _ = l := by rw [mul_smul, key, ← mul_smul, hqiq, one_smul]
    have hlO := hprim l hl ((Submodule.mem_span_range_iff_exists_fun E).2 ⟨γ, hsum⟩)
    obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 hlO
    have hβ' : ∑ j, (β j : E) • Sum.elim t.f
        (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) j = l := by
      simpa only [Subring.smul_def] using hβ
    have hzero := Fintype.linearIndependent_iff.1 hli (fun j => (β j : E) - γ j) (by
      simp only [sub_smul, Finset.sum_sub_distrib, hβ', hsum, sub_self])

    have hmem : ∀ i : Fin r, α' i ∈ M.L.O := by
      intro i
      have := hzero (Sum.inr i.castSucc)
      simp only [γ, Sum.elim_inr, Fin.snoc_castSucc, sub_eq_zero] at this
      rw [← this]
      exact (β _).2
    have hf'L := hgen.1.2.2.1.1.1
    have hw' : w = (x' : V) + ∑ i, α' i • t.f' i.castSucc := by rw [hα']; abel
    rw [hw']
    refine t.abelian₂.add_mem hx'L (Submodule.sum_mem _ fun i _ => ?_)
    have := t.abelian₂.smul_mem (⟨α' i, hmem i⟩ : M.L.O) (hf'L i.castSucc)
    simpa only [Subring.smul_def] using this

end G

end Formalism.L2.SG.LsDatumA
