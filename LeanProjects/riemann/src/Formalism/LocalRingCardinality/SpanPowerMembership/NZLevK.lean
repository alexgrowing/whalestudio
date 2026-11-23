import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevJ
import Formalism.SharpRestriction.GrowthBounds.TensorLatticeBounds.ExampleFunctionModuleEqSpan

open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.G.Model Formalism.MainNotions.G.LatticeSystems

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf] (P : Places p O Kf) (hp : (p : Kf) ≠ 0) (C : Type) [Fintype C] [DecidableEq C]

abbrev gatC : GAtP p where
  O := O
  Kf := Kf
  P := P
  comp := C
  lev := fun _ => levB P hp
  e := 0

def Fb (c : C) : (gatC P hp C).Fn := fun (c' : C) (L : P.Tup) => if c' = c then valE P hp L else 0

variable (v0 : Fin P.nV)

include v0 in
theorem Fb_mem (c : C) : Fb P hp C c ∈ (gatC P hp C).M := by
  classical
  intro c' _
  refine (Formalism.MainNotions.G.Inhab.mem_funMod (levB P hp) P.HtupW (Fb P hp C c c')).mpr ⟨fun L hL => ?_, fun L hL => ?_,
    fun γ L => ?_⟩
  · unfold Fb; split_ifs
    · exact valE_mem P hp L hL
    · exact Submodule.zero_mem _
  · unfold Fb; split_ifs
    · unfold valE; rw [dif_neg hL]
    · rfl
  · unfold Fb; split_ifs
    · exact valE_smul P hp v0 γ L
    · rw [map_zero, smul_zero]

include v0 in

theorem value_standardTuple_integral (F : (gatC P hp C).Fn) (hF : F ∈ (gatC P hp C).M) (c : C) :
    ∃ o : O, F c (standardTuple P) = algebraMap O Kf o • EV P := by
  have hF' := (Formalism.MainNotions.G.Inhab.mem_funMod (levB P hp) P.HtupW (F c)).mp (hF c (Set.mem_univ c))
  set e : P.Xsp := F c (standardTuple P) with he
  have hmem : e ∈ P.HtupW (standardTuple P) := hF'.1 _ (standardTuple_isLattice P)
  choose cc hcz hc using fun v a => natAct_tor P v a
  choose u hu hnat using fun v a => tor_mem P hp v a
  have hc0 : ∀ v a, cc v a ≠ 0 := fun v a => by
    obtain ⟨z, hz⟩ := hcz v a; rw [hz]; exact zpow_ne_zero _ two_ne_zero
  have hwt : IsWeightedHomogeneous (om P) e (LamTot P) := by
    refine isWH_of_eigen P e (EV P) (EV_ne P) (EV_isWH P)
      (fun v a => (cc v a)⁻¹ * algebraMap O Kf (((u v a)⁻¹ : Oˣ) : O)) (fun v a => ?_) (fun v a => ?_)
    · have h1 := hF'.2.2 ⟨(torM P v a, u v a), hu v a⟩ (standardTuple P)
      rw [tor_stab P hp v a _ (hu v a)] at h1
      have h2 : P.natAct (torM P v a) e = algebraMap O Kf (((u v a)⁻¹ : Oˣ) : O) • e := by
        have h3 : e = ((u v a : O)) • P.natAct (torM P v a) e := h1
        conv_rhs => rw [h3]
        rw [← algebraMap_smul Kf ((u v a : Oˣ) : O) (P.natAct (torM P v a) e), smul_smul, ← map_mul, Units.inv_mul,
          map_one, one_smul]
      rw [hc, LinearMap.smul_apply, AlgHom.toLinearMap_apply] at h2
      rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ (hc0 v a), one_smul]
    · have h2 := hnat v a
      rw [hc, LinearMap.smul_apply, AlgHom.toLinearMap_apply] at h2
      rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ (hc0 v a), one_smul]
  have hlat : ∀ v (s : Fin (P.n' v)), IsLattice O (extO O (P.ι v) (P.σ v) s.val (standardTuple P v)) := fun v s => by
    show IsLattice O (extO O (P.ι v) (P.σ v) s.val (L0 P v))
    rw [extension_standardLattice]; exact ⟨1, by simp, rfl⟩
  obtain ⟨a, ha⟩ := mem_line P e (htupW_le P (standardTuple P) hlat hmem) hwt
  have hint := eval_int P _ (htupW_int P _ hmem)
  rw [ha, smul_eval, eval_EV, mul_one] at hint
  obtain ⟨o, ho⟩ := hint
  exact ⟨o, by rw [ha, ho]⟩

include v0 in
theorem M_eq : Submodule.span (gatC P hp C).O (Set.range (Fb P hp C)) = (gatC P hp C).M := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    exact Fb_mem P hp C v0 c
  · intro F hF
    choose o ho using value_standardTuple_integral P hp C v0 F hF
    have hFeq : F = ∑ c, o c • Fb P hp C c := by
      funext c' L
      rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single c']
      · have hF' := (Formalism.MainNotions.G.Inhab.mem_funMod (levB P hp) P.HtupW (F c')).mp (hF c' (Set.mem_univ c'))
        show F c' L = o c' • (if c' = c' then valE P hp L else 0)
        rw [if_pos rfl]
        unfold valE
        split_ifs with hL
        · have h1 := hF'.2.2 (gOf P hp L hL) (standardTuple P)
          rw [gOf_spec] at h1
          rw [h1, ho, LinearMap.map_smul_of_tower, smul_comm, ← algebraMap_smul Kf (o c')]
        · rw [hF'.2.1 L hL, smul_zero]
      · intro c _ hc
        show o c • (if c' = c then valE P hp L else 0) = 0
        rw [if_neg (Ne.symm hc), smul_zero]
      · intro h; exact absurd (Finset.mem_univ c') h
    rw [hFeq]
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

include v0 in
theorem Fb_li : LinearIndependent Kf (Fb P hp C) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha c
  have h1 := congrFun (congrFun ha c) (standardTuple P)
  rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single c] at h1
  · change a c • (if c = c then valE P hp (standardTuple P) else 0) = 0 at h1
    rw [if_pos rfl, value_standardTuple P hp v0] at h1
    exact (smul_eq_zero.mp h1).resolve_right (EV_ne P)
  · intro c' _ hc'
    show a c' • (if c = c' then valE P hp (standardTuple P) else 0) = 0
    rw [if_neg (Ne.symm hc'), smul_zero]
  · intro h; exact absurd (Finset.mem_univ c) h

include v0 in
theorem gatC_d : (gatC P hp C).d = Fintype.card C := by
  unfold GAtP.d
  rw [← M_eq P hp C v0]
  haveI := (P.setting v0).frac_O
  have : FaithfulSMul (gatC P hp C).O (gatC P hp C).Kf :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective O Kf)
  exact finrank_span_eq_card ((Fb_li P hp C v0).restrict_scalars' (gatC P hp C).O)

end Formalism.BasicNotions.Examples₂.NZ
