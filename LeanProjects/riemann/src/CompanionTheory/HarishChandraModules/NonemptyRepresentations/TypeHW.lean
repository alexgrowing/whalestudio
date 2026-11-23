import Formalism.HermitianCurvature.HermitianCurvatureProofs.SingleMulVecOne
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Matrix

noncomputable section

namespace CompanionTheory.D.Inhab.TypeHW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

def res (S : Submodule ℂ W) (π : Mx k r → (W →L[ℂ] W)) (g : Mx k r) : S →L[ℂ] S :=
  S.orthogonalProjection.comp ((π g).comp S.subtypeL)

theorem res_coe {S : Submodule ℂ W} {π : Mx k r → (W →L[ℂ] W)} {g : Mx k r} (hg : ∀ v ∈ S, π g v ∈ S) (v : S) :
    (res S π g v : W) = π g v := by
  have := S.orthogonalProjection_mem_subspace_eq_self ⟨π g v, hg v v.2⟩
  exact congrArg Subtype.val this

theorem res_isRepW {z : Fin (2 * r + k + 1) → ℂ} {S : Submodule ℂ W} {π : Mx k r → (W →L[ℂ] W)}
    (hπ : IsRepW k r z π) (hS : ∀ h ∈ UWset k r z, ∀ v ∈ S, π h v ∈ S) : IsRepW k r z (res S π) := by
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, ?_⟩
  · ext v
    rw [res_coe (hS 1 (Qx8.uw_one z)), hπ.1.1]; rfl
  · ext v
    have hab : ∀ v ∈ S, π (a * b) v ∈ S := fun v hv => by
      rw [hπ.1.2 a ha b hb]; exact hS a ha _ (hS b hb v hv)
    rw [res_coe hab, ContinuousLinearMap.comp_apply, res_coe (hS a ha), res_coe (hS b hb), hπ.1.2 a ha b hb]; rfl
  · exact continuousOn_const.clm_comp (hπ.2.clm_comp continuousOn_const)

theorem res_capRep {z : Fin (2 * r + k + 1) → ℂ} {S : Submodule ℂ W} {π : Mx k r → (W →L[ℂ] W)}
    (hπ : IsRepW k r z π) (hS : ∀ h ∈ UWset k r z, ∀ v ∈ S, π h v ∈ S) {m : ℕ}
    {Bs : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : IsFrameOf k r [z] Bs) (w : ℂ) (v : S) :
    ((capRep k r (res S π) Bs w v : S) : W) = capRep k r π Bs w v := by
  have hR := res_isRepW hπ hS
  unfold capRep
  refine Qx8.qmF_intertwine _ _ S.subtype ?_ _ _ _ v
  intro a b v
  have hU := Qx8.frame_InU hB (z := z) (by simp) a b
  show S.subtypeL (dRep (res S π) _ v + Complex.I • dRep (res S π) _ v) =
    dRep π _ (S.subtypeL v) + Complex.I • dRep π _ (S.subtypeL v)
  rw [map_add, map_smul]
  congr 1
  · exact Qx8.dRep_intertwine S.subtypeL (Qx8.rep_hasDeriv hR.1 hR.2 hU.1 v) fun t => res_coe (hS _ (hU.1 t)) v
  · congr 1
    exact Qx8.dRep_intertwine S.subtypeL (Qx8.rep_hasDeriv hR.1 hR.2 hU.2 v) fun t => res_coe (hS _ (hU.2 t)) v

theorem prod_Icc (n : ℕ) (f : ℕ → ℂ) : ∏ i ∈ Finset.Icc 1 n, f i = ∏ j : Fin n, f ((j : ℕ) + 1) := by
  rw [Fin.prod_univ_eq_prod_range (fun j => f (j + 1)) n]
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]

theorem exists_type {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {π : Mx k r → (W →L[ℂ] W)} (hπ : IsRepW k r z π) (hu : ∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖)
    {B0 : Fin k → Fin (2 * r + k + 1) → ℂ} (hB0 : IsFrameOf k r [z] B0) {ν : Fin k → ℂ} {v0 : W} (hv0 : v0 ≠ 0)
    (hw : IsHW (EB π B0) ν v0) (u : ℕ → ℝ)
    (hν : ∀ j : Fin k, (u ((j : ℕ) + 1) : ℂ) = ν j + ((k : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)) :
    ∃ S : Submodule ℂ W, (∀ h ∈ UWset k r z, ∀ v ∈ S, π h v ∈ S) ∧ IsType k r z (res S π) u := by
  classical
  have hgl := (frame_general_linear W k r k z π B0 hπ hB0).1
  let c : ℂ → ℂ := fun w => ∏ j : Fin k, (w - (j : ℂ) + ν j)
  let K : Submodule ℂ W :=
    { carrier := {v | ∀ w, qdet (EB π B0) w v = c w • v}
      add_mem' := fun ha hb w => by rw [map_add, ha w, hb w, smul_add]
      zero_mem' := fun w => by simp
      smul_mem' := fun s v hv w => by rw [map_smul, hv w, smul_comm] }
  have hKs : Stab (EB π B0) K := by
    intro a b v hv w
    have := congrArg (fun T : Module.End ℂ W => T v) (Formalism.REAL.qDetCentral _ k _ hgl w a b)
    simp only [Module.End.mul_apply] at this
    rw [this, hv w, map_smul]
  have hK := lie_stabilizer W k r z π B0 hz hT hπ hB0 K hKs
  have hv0K : v0 ∈ K := fun w => Formalism.REAL.qDetHW W k _ ν v0 hgl hw w
  have hex : ∃ n, ∃ S : Submodule ℂ W, S ≤ K ∧ S ≠ ⊥ ∧ (∀ h ∈ UWset k r z, ∀ v ∈ S, π h v ∈ S) ∧
      Module.finrank ℂ S = n :=
    ⟨_, K, le_rfl, (Submodule.ne_bot_iff K).2 ⟨v0, hv0K, hv0⟩, hK, rfl⟩
  obtain ⟨S, hSK, hS0, hS, hn⟩ := Nat.find_spec hex
  have hR := res_isRepW hπ hS
  refine ⟨S, hS, Submodule.nontrivial_iff_ne_bot.2 hS0, hR.1, hR.2, fun h hh v => ?_, fun S' hS' => ?_, ?_⟩
  · rw [← Submodule.norm_coe, res_coe (hS h hh), hu h hh, Submodule.norm_coe]
  · by_cases h0 : S' = ⊥
    · exact Or.inl h0
    refine Or.inr ?_
    have hle : Nat.find hex ≤ Module.finrank ℂ (S'.map S.subtype) := by
      refine Nat.find_min' hex ⟨S'.map S.subtype, (Submodule.map_subtype_le S S').trans hSK, ?_, ?_, rfl⟩
      · intro h
        exact h0 (Submodule.map_injective_of_injective S.subtype_injective (by rw [h, Submodule.map_bot]))
      · rintro h hh _ ⟨v, hv, rfl⟩
        exact ⟨_, hS' h hh v hv, res_coe (hS h hh) v⟩
    rw [Submodule.finrank_map_subtype_eq, ← hn] at hle
    exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le S') hle)
  · intro Bs hB w v
    apply Subtype.ext
    rw [res_capRep hπ hS hB, (frame_general_linear W k r k z π Bs hπ hB).2, QrCap.capChange hz hT hπ hB hB0,
      hSK v.2 w, prod_Icc, Submodule.coe_smul]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hν]; ring

end CompanionTheory.D.Inhab.TypeHW
