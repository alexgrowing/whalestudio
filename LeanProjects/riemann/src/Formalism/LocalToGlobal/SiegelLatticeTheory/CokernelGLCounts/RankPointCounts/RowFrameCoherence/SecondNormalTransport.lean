import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarEquivalenceGeneral.ScalarFactorEqOneOfLe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.GramNondeg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Lemmas
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarPairOrthogonal.XLeOrthXplus

noncomputable section

open scoped Classical

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.RowForm.ClassFramePositivePartDecomposition

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

section Basic

variable {r : ℕ} {T : E}

theorem hswap (x y : S.V) : S.hT y x = star (S.hT x y) := PI.ScalarPairDr.W.hT_swap (S := S) x y

theorem e_X (F : FlagG S r T) (a : Fin r) {x : S.V} (hx : x ∈ F.X) : S.hT (F.e a) x = 0 :=
  ((PI.ScalarPairDr.W.mem_orth_Xplus (S := S) F).1 (PI.ScalarPairDr.W.X_le_orth_Xplus (S := S) F hx)).1 a

theorem z_X (F : FlagG S r T) {x : S.V} (hx : x ∈ F.X) : S.hT F.z x = 0 :=
  ((PI.ScalarPairDr.W.mem_orth_Xplus (S := S) F).1 (PI.ScalarPairDr.W.X_le_orth_Xplus (S := S) F hx)).2

theorem xplus_dec (F : FlagG S r T) {v : S.V} (hv : v ∈ F.Xplus) : ∃ a : E, ∃ x ∈ F.X, v = a • F.z + x := by
  change v ∈ F.X ⊔ Submodule.span E {F.z} at hv
  obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
  exact ⟨a, x, hx, by abel⟩

theorem xplus_mem (F : FlagG S r T) (a : E) {x : S.V} (hx : x ∈ F.X) : a • F.z + x ∈ F.Xplus :=
  Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
    (Submodule.mem_sup_left hx)

theorem zz_ne (F : FlagG S r T) (hT : T ≠ 0) : S.hT F.z F.z ≠ 0 := by
  rw [F.z_norm]; exact neg_ne_zero.mpr hT

theorem indep {T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0) (C C' : Fin (r + 1) → E)
    (h : ∑ a, C a • F.fvec a + ∑ b, C' b • F'.fvec b = 0) : C = 0 ∧ C' = 0 :=
  PI.UnitaryGroupMassFormula.BetaLUniq.GN.coeffs_zero F F' C C' 0 h.symm (fun _ => by simp) (fun _ => by simp) hG

theorem sum_fvec (F : FlagG S r T) (c : Fin r → E) (a : E) :
    ∑ i, (Fin.snoc (α := fun _ => E) c a : Fin (r + 1) → E) i • F.fvec i = a • F.z + ∑ i, c i • F.e i := by
  rw [Fin.sum_univ_castSucc]
  simp only [FlagG.fvec, Fin.snoc_castSucc, Fin.snoc_last]
  abel

theorem x_sum (F : FlagG S r T) {x : S.V} (hx : x ∈ F.X) : ∃ c : Fin r → E, ∑ i, c i • F.e i = x :=
  (Submodule.mem_span_range_iff_exists_fun E).1 hx

theorem disj {T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0) {v : S.V} (hv : v ∈ F.X)
    (hv' : v ∈ F'.Xplus) : v = 0 := by
  obtain ⟨c, hc⟩ := x_sum F hv
  obtain ⟨a', x', hx', e'⟩ := xplus_dec F' hv'
  obtain ⟨c', hc'⟩ := x_sum F' hx'
  have h := indep F F' hG (Fin.snoc (α := fun _ => E) c 0) (Fin.snoc (α := fun _ => E) (-c') (-a')) (by
    rw [sum_fvec, sum_fvec]
    simp only [zero_smul, zero_add, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
    rw [hc, hc', e']; abel)
  have ha : a' = 0 := by
    have := congrFun h.2 (Fin.last r)
    simpa using this
  have hc0 : c' = 0 := by
    funext i
    have := congrFun h.2 (Fin.castSucc i)
    simpa using this
  rw [e', ← hc', ha, hc0]
  simp

theorem indep' {T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0) (C' : Fin (r + 1) → E)
    (h : ∑ b, C' b • F'.fvec b = 0) : C' = 0 :=
  (indep F F' hG 0 C' (by simp [h])).2

end Basic

section Pair

variable {Λ : Submodule (𝓞 E) S.V} {r : ℕ} {T T' : E} {F : LFlag S r T} {F' F'' : LFlag S r T'}
  {β : S.V ≃ₗ[E] S.V}

theorem zt_mem (F : LFlag S r T) (F' : LFlag S r T') : F.zt ∈ UUE Λ F F' ∧ F'.zt ∈ UUE Λ F F' := by
  constructor
  · apply Submodule.subset_span
    show F.zt ∈ UU Λ F F'
    unfold UU
    exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
  · apply Submodule.subset_span
    show F'.zt ∈ UU Λ F F'
    unfold UU
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

theorem xplus_le (hΛ : Submodule.IsLattice E Λ) (F : LFlag S r T) (F' : LFlag S r T') (hz : F.zt = F.fl.z) :
    Xplus F ≤ UUE Λ F F' := by
  change F.fl.X ⊔ Submodule.span E {F.fl.z} ≤ _
  refine sup_le (PI.UnitaryGroupMassFormula.BetaLUniq.Xsp_le_UUE S Λ hΛ F F') ?_
  rw [Submodule.span_le, Set.singleton_subset_iff, ← hz]
  exact (zt_mem (Λ := Λ) F F').1

theorem xplus_le' (hΛ : Submodule.IsLattice E Λ) (F : LFlag S r T) (F' : LFlag S r T') (hz' : F'.zt = F'.fl.z) :
    Xplus F' ≤ UUE Λ F F' := by
  change F'.fl.X ⊔ Submodule.span E {F'.fl.z} ≤ _
  refine sup_le (PI.UnitaryGroupMassFormula.BetaLUniq.Xsp_le_UUE' S Λ hΛ F F') ?_
  rw [Submodule.span_le, Set.singleton_subset_iff, ← hz']
  exact (zt_mem (Λ := Λ) F F').2

theorem orth_xplus_iff {T₀ : E} (G : LFlag S r T₀) {v : S.V} :
    v ∈ orth S (Xplus G) ↔ (∀ a, S.hT (G.fl.e a) v = 0) ∧ S.hT G.fl.z v = 0 :=
  PI.ScalarPairDr.W.mem_orth_Xplus (S := S) G.fl

theorem ylift_rev (hTh : Th Λ F F' F'' β = Hp Λ F F') {y : S.V} (hy : y ∈ Ylift Λ F F'') : y ∈ UUE Λ F F' := by
  rw [← PI.UnitaryGroupMassFormula.ScalEquivGen.orthOrthQ (UUE Λ F F'), PI.UnitaryGroupMassFormula.ScalEquivGen.memOrthQ]
  intro h hh
  change h ∈ Hp Λ F F' at hh
  rw [← hTh] at hh
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hh
  rw [PI.UnitaryGroupMassFormula.ScalEquivGen.memThPairsQ] at hp
  have hp2 : p.2 ∈ orth S (UUE Λ F F'') := hp.1.1.2
  have hy1 : y ∈ UUE Λ F F'' := hy.1
  have hy2 : y ∈ orth S (Xplus F) := hy.2
  have e1 : S.hT p.2 y = 0 :=
    PI.UnitaryGroupMassFormula.ScalEquivGen.hTCommQ.mp ((PI.UnitaryGroupMassFormula.ScalEquivGen.memOrthQ.mp hp2) y hy1)
  have e2 : S.hT (p.1 - p.2) y = 0 :=
    PI.UnitaryGroupMassFormula.ScalEquivGen.memOrthQ.mp (PI.UnitaryGroupMassFormula.ScalEquivGen.orthAntiQ (PI.UnitaryGroupMassFormula.ScalEquivGen.XspLeXplusQ F) hy2) _ hp.1.2
  show S.hT p.1 y = 0
  have e : p.1 = (p.1 - p.2) + p.2 := by abel
  rw [e, map_add, LinearMap.add_apply, e1, e2, add_zero]

variable (hΛ : Submodule.IsLattice E Λ) (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) (hz'' : F''.zt = F''.fl.z)
include hΛ hz hz' hz''

theorem firstNormal_transport (hT : T ≠ 0) (hTh : Th'' Λ F F' F'' β = Hp Λ F F'') (hSc : IsScalar Λ F F' F'' β)
    {ν : S.V} (hν : ν ∈ Xplus F') (he : ∀ a, S.hT (F.fl.e a) ν = 0) (hzν : S.hT F.fl.z ν = 1) :
    ∃ ν₂ ∈ Xplus F'', (∀ a, S.hT (F.fl.e a) ν₂ = 0) ∧ S.hT F.fl.z ν₂ = 1 ∧ ν - ν₂ ∈ Xsp F := by
  have hzz := zz_ne F.fl hT
  set c : E := (S.hT F.fl.z F.fl.z)⁻¹ with hc
  set y : S.V := ν - c • F.fl.z with hy
  have hyU : y ∈ UUE Λ F F' :=
    Submodule.sub_mem _ (xplus_le' hΛ F F' hz' hν)
      (Submodule.smul_mem _ _ (hz ▸ (zt_mem (Λ := Λ) F F').1))
  have hyO : y ∈ orth S (Xplus F) := by
    rw [orth_xplus_iff]
    refine ⟨fun a => ?_, ?_⟩
    · rw [hy, map_sub, map_smul, he a, F.fl.z_orth a, smul_zero, sub_zero]
    · rw [hy, map_sub, map_smul, hzν, smul_eq_mul, hc, inv_mul_cancel₀ hzz, sub_self]
  have hy' : y ∈ Ylift Λ F F' := ⟨hyU, hyO⟩
  have hy'' : y ∈ Ylift Λ F F'' := ⟨PI.UnitaryGroupMassFormula.ScalEquivGen.yliftMemQ hTh hy', hyO⟩
  obtain ⟨α', x', hx', hνe⟩ := xplus_dec F'.fl hν
  have hsg : SgRel F F' y 0 (-c) α' := by
    refine ⟨0, Submodule.zero_mem _, x', hx', ?_⟩
    rw [hz, hz', hy, hνe, neg_smul]
    abel
  have h0 : y - y ∈ Xsp F := by rw [sub_self]; exact Submodule.zero_mem _
  have h0' : (0 : S.V) - β 0 ∈ Xsp F'' := by simp
  obtain ⟨x₂, hx₂, x'', hx'', h3⟩ :=
    (hSc y hy' y hy'' 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) h0 h0' (-c) α').1 hsg
  rw [hz, hz''] at h3
  refine ⟨α' • F''.fl.z + x'', xplus_mem F''.fl α' hx'', ?_⟩
  have hd : ν - (α' • F''.fl.z + x'') = x₂ := by
    have h4 : ν = (-c) • F.fl.z + x₂ + (α' • F''.fl.z + x'') + c • F.fl.z := by
      rw [← h3, hy]; abel
    rw [h4, neg_smul]; abel
  have hν₂ : α' • F''.fl.z + x'' = ν - x₂ := by rw [← hd]; abel
  refine ⟨fun a => ?_, ?_, hd ▸ hx₂⟩
  · rw [hν₂, map_sub, he a, e_X F.fl a hx₂, sub_zero]
  · rw [hν₂, map_sub, hzν, z_X F.fl hx₂, sub_zero]

theorem ker_transport (hG' : Gflag F.fl F'.fl ≠ 0) (hTh : Th'' Λ F F' F'' β = Hp Λ F F'')
    (hSc : IsScalar Λ F F' F'' β) {d : S.V} (hd : d ∈ Xplus F') (hdO : d ∈ orth S (Xplus F)) (hd0 : d ≠ 0) :
    ∃ d₂ ∈ Xplus F'', d₂ ∈ orth S (Xplus F) ∧ d₂ ≠ 0 := by
  have hy' : d ∈ Ylift Λ F F' := ⟨xplus_le' hΛ F F' hz' hd, hdO⟩
  have hy'' : d ∈ Ylift Λ F F'' := ⟨PI.UnitaryGroupMassFormula.ScalEquivGen.yliftMemQ hTh hy', hdO⟩
  obtain ⟨α', x', hx', hde⟩ := xplus_dec F'.fl hd
  have hsg : SgRel F F' d 0 0 α' := by
    refine ⟨0, Submodule.zero_mem _, x', hx', ?_⟩
    rw [hz', hde, zero_smul]
    abel
  have h0 : d - d ∈ Xsp F := by rw [sub_self]; exact Submodule.zero_mem _
  have h0' : (0 : S.V) - β 0 ∈ Xsp F'' := by simp
  obtain ⟨x₂, hx₂, x'', hx'', h3⟩ :=
    (hSc d hy' d hy'' 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) h0 h0' 0 α').1 hsg
  rw [hz''] at h3
  have hd2 : α' • F''.fl.z + x'' = d - x₂ := by
    rw [sub_zero] at h3; rw [h3, zero_smul]; abel
  refine ⟨α' • F''.fl.z + x'', xplus_mem F''.fl α' hx'', ?_, ?_⟩
  · rw [hd2]
    exact Submodule.sub_mem _ hdO (PI.ScalarPairDr.W.X_le_orth_Xplus (S := S) F.fl hx₂)
  · intro h
    rw [hd2, sub_eq_zero] at h
    exact hd0 (disj F.fl F'.fl hG' (h ▸ hx₂) hd)

theorem ker_transport_rev (hG'' : Gflag F.fl F''.fl ≠ 0) (hTh : Th Λ F F' F'' β = Hp Λ F F')
    (hSc : IsScalar Λ F F' F'' β) {d : S.V} (hd : d ∈ Xplus F'') (hdO : d ∈ orth S (Xplus F)) (hd0 : d ≠ 0) :
    ∃ d₁ ∈ Xplus F', d₁ ∈ orth S (Xplus F) ∧ d₁ ≠ 0 := by
  have hy'' : d ∈ Ylift Λ F F'' := ⟨xplus_le' hΛ F F'' hz'' hd, hdO⟩
  have hy' : d ∈ Ylift Λ F F' := ⟨ylift_rev hTh hy'', hdO⟩
  obtain ⟨α', x', hx', hde⟩ := xplus_dec F''.fl hd
  have hsg : SgRel F F'' d 0 0 α' := by
    refine ⟨0, Submodule.zero_mem _, x', hx', ?_⟩
    rw [hz'', hde, zero_smul]
    abel
  have h0 : d - d ∈ Xsp F := by rw [sub_self]; exact Submodule.zero_mem _
  have h0' : (0 : S.V) - β 0 ∈ Xsp F'' := by simp
  obtain ⟨x₂, hx₂, x'', hx'', h3⟩ :=
    (hSc d hy' d hy'' 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) h0 h0' 0 α').2 hsg
  rw [hz'] at h3
  have hd2 : α' • F'.fl.z + x'' = d - x₂ := by
    rw [sub_zero] at h3; rw [h3, zero_smul]; abel
  refine ⟨α' • F'.fl.z + x'', xplus_mem F'.fl α' hx'', ?_, ?_⟩
  · rw [hd2]
    exact Submodule.sub_mem _ hdO (PI.ScalarPairDr.W.X_le_orth_Xplus (S := S) F.fl hx₂)
  · intro h
    rw [hd2, sub_eq_zero] at h
    exact hd0 (disj F.fl F''.fl hG'' (h ▸ hx₂) hd)

omit hz hz' hz'' hΛ in
theorem xflag_map (hβe : ∀ b, β (F'.fl.e b) = F''.fl.e b) (j : ℕ) :
    (Xflag F' j).map (β : S.V →ₗ[E] S.V) = Xflag F'' j := by
  show (Submodule.span E (F'.fl.e '' {i | i.1 < j})).map (β : S.V →ₗ[E] S.V) =
    Submodule.span E (F''.fl.e '' {i | i.1 < j})
  rw [Submodule.map_span, Set.image_image]
  congr 1
  exact Set.image_congr fun b _ => by simp [hβe]

omit hz hz' hz'' hΛ in
theorem symm_X (hβe : ∀ b, β (F'.fl.e b) = F''.fl.e b) {x : S.V} (hx : x ∈ Xsp F'') : β.symm x ∈ Xsp F' := by
  have h := xflag_map hβe r
  rw [PI.UnitaryGroupMassFormula.ScalEquivGen.XflagTopQ, PI.UnitaryGroupMassFormula.ScalEquivGen.XflagTopQ] at h
  rw [← h] at hx
  obtain ⟨x', hx', rfl⟩ := Submodule.mem_map.mp hx
  simpa using hx'

theorem secondNormal_transport (hT' : T' ≠ 0) (hi : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hβe : ∀ b, β (F'.fl.e b) = F''.fl.e b)
    (hβz : β F'.fl.z = F''.fl.z) (hTh : Th'' Λ F F' F'' β = Hp Λ F F'') (hSc : IsScalar Λ F F' F'' β)
    {x₁ : S.V} (hx : x₁ ∈ Xplus F) (he : ∀ b, S.hT x₁ (F'.fl.e b) = 0) (hzx : S.hT x₁ F'.fl.z = 1) :
    ∃ x₂ ∈ Xplus F, (∀ b, S.hT x₂ (F''.fl.e b) = 0) ∧ S.hT x₂ F''.fl.z = 1 ∧ β.symm x₂ - x₁ ∈ Xsp F' := by
  have hzz := zz_ne F'.fl hT'
  set c : E := (S.hT F'.fl.z F'.fl.z)⁻¹ with hc
  set y : S.V := x₁ - c • F'.fl.z with hy
  have hyU : y ∈ UUE Λ F F' :=
    Submodule.sub_mem _ (xplus_le hΛ F F' hz hx)
      (Submodule.smul_mem _ _ (hz' ▸ (zt_mem (Λ := Λ) F F').2))
  have hyO : y ∈ orth S (Xplus F') := by
    rw [orth_xplus_iff]
    refine ⟨fun b => ?_, ?_⟩
    · rw [hy, map_sub, map_smul, hswap, he b, F'.fl.z_orth b, star_zero, smul_zero, sub_zero]
    · rw [hy, map_sub, map_smul, hswap, hzx, star_one, smul_eq_mul, hc, inv_mul_cancel₀ hzz, sub_self]
  have hy' : y ∈ Ylift' Λ F F' := ⟨hyU, hyO⟩
  have hby : β y ∈ UUE Λ F F'' := PI.UnitaryGroupMassFormula.ScalEquivGen.ylift'MemQ hi (xflag_map hβe) hTh hy'
  have hyO' := (orth_xplus_iff F').1 hyO
  have hbyO : β y ∈ orth S (Xplus F'') := by
    rw [orth_xplus_iff]
    refine ⟨fun b => ?_, ?_⟩
    · rw [← hβe b, hi]; exact hyO'.1 b
    · rw [← hβz, hi]; exact hyO'.2
  have hby' : β y ∈ Ylift' Λ F F'' := ⟨hby, hbyO⟩
  obtain ⟨a, ξ, hξ, hxe⟩ := xplus_dec F.fl hx
  have hsg : SgRel F F' 0 y (-a) c := by
    refine ⟨-ξ, Submodule.neg_mem _ hξ, 0, Submodule.zero_mem _, ?_⟩
    rw [hz, hz', hy, hxe, neg_smul]
    abel
  have h0 : (0 : S.V) - 0 ∈ Xsp F := by simp
  have h0' : β y - β y ∈ Xsp F'' := by rw [sub_self]; exact Submodule.zero_mem _
  obtain ⟨x₃, hx₃, x'', hx'', h3⟩ :=
    (hSc 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) y hy' (β y) hby' h0 h0' (-a) c).1 hsg
  rw [hz, hz''] at h3
  have hx2 : a • F.fl.z + -x₃ = β y + c • F''.fl.z + x'' := by
    have h4 : β y = -((-a) • F.fl.z + x₃ + (c • F''.fl.z + x'')) := by rw [← h3]; abel
    rw [h4, neg_smul]; abel
  refine ⟨a • F.fl.z + -x₃, xplus_mem F.fl a (Submodule.neg_mem _ hx₃), ?_⟩
  have hzz'' : S.hT F''.fl.z F''.fl.z = S.hT F'.fl.z F'.fl.z := by rw [← hβz, hi]
  have k1 : ∀ b, S.hT (F''.fl.e b) (a • F.fl.z + -x₃) = 0 := by
    intro b
    rw [hx2, map_add, map_add, map_smul, (orth_xplus_iff F'').1 hbyO |>.1 b, F''.fl.z_orth b,
      e_X F''.fl b hx'', smul_zero, zero_add, add_zero]
  have k2 : S.hT F''.fl.z (a • F.fl.z + -x₃) = 1 := by
    rw [hx2, map_add, map_add, map_smul, (orth_xplus_iff F'').1 hbyO |>.2, z_X F''.fl hx'', hzz'', smul_eq_mul,
      hc, inv_mul_cancel₀ hzz, zero_add, add_zero]
  refine ⟨fun b => ?_, ?_, ?_⟩
  · rw [hswap, k1 b, star_zero]
  · rw [hswap, k2, star_one]
  · have hs : β.symm F''.fl.z = F'.fl.z := by rw [← hβz]; simp
    rw [hx2, map_add, map_add, map_smul, LinearEquiv.symm_apply_apply, hs, hy]
    have : x₁ - c • F'.fl.z + c • F'.fl.z + β.symm x'' - x₁ = β.symm x'' := by abel
    rw [this]
    exact symm_X hβe hx''

omit hz hz' hz'' hΛ in

theorem orthogonal_transport (hTh : Th'' Λ F F' F'' β = Hp Λ F F'') {y₂ : S.V} (hy : y₂ ∈ Hp Λ F F'') :
    ∃ y₁ ∈ Hp Λ F F', y₁ - y₂ ∈ Xsp F ∧ β y₁ - y₂ ∈ Xsp F'' := by
  rw [← hTh] at hy
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hy
  rw [PI.UnitaryGroupMassFormula.ScalEquivGen.memThPairsQ] at hp
  exact ⟨p.1, hp.1.1.1, hp.1.2, hp.2⟩

end Pair

end Formalism.L2.SG.Pf.RowForm.ClassFramePositivePartDecomposition
