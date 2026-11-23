import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc

section Generic

variable {I G : Type} [Group G] {Gv : I → Type} [∀ v, Group (Gv v)] {K : ∀ v, Subgroup (Gv v)} (P : RPG G Gv K)

private theorem mem_box (U : ∀ v, Subgroup (Gv v)) (g : G) : g ∈ P.box U ↔ ∀ v, P.p v g ∈ U v := by
  simp [RPG.box, Subgroup.mem_iInf]

end Generic

variable {F : Type} [Field F] [NumberField F] {Δ : F}

theorem normOneLevel_le_maximalCompact (D : Dat Δ) (h : D.Ok) : D.U2 ≤ (rpg _ _).box fun v => KD (cv v Δ) (Ov v) := by
  intro g hg
  rw [Dat.U2, mem_box] at hg
  rw [mem_box]
  intro v
  have hv' := hg v
  unfold Dat.J2v at hv'
  split_ifs at hv' with hv
  · exact (h.sig v hv).levelTwoLeIntegral hv'
  · exact hv'

theorem relIndex_normOneLevel_maximalCompact_ne_zero (D : Dat Δ) (h : D.Ok) : D.U2.relIndex ((rpg _ _).box fun v => KD (cv v Δ) (Ov v)) ≠ 0 := by
  set L := (rpg (fun v => ↥(DX (cv v Δ))) fun v => KD (cv v Δ) (Ov v)).box fun v => KD (cv v Δ) (Ov v) with hL
  set M := ⨅ v : (D.Sg : Set (Pl F)), Subgroup.comap ((rpg (fun v => ↥(DX (cv v Δ))) fun v => KD (cv v Δ) (Ov v)).p v) (D.S v).J2 with hM
  have hsub : L ⊓ M ≤ D.U2 := by
    intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgL, hgM⟩ := hg
    rw [hL, mem_box] at hgL
    rw [hM, Subgroup.mem_iInf] at hgM
    rw [Dat.U2, mem_box]
    intro v
    unfold Dat.J2v
    split_ifs with hv
    · exact hgM ⟨v, hv⟩
    · exact hgL v
  have hMne : M.relIndex L ≠ 0 := by
    rw [hM]
    haveI : Finite (D.Sg : Set (Pl F)) := D.Sg.finite_toSet.to_subtype
    apply Subgroup.relIndex_iInf_ne_zero
    rintro ⟨v, hv⟩
    rw [Subgroup.relIndex_comap]
    have hmap : Subgroup.map ((rpg (fun v => ↥(DX (cv v Δ))) fun v => KD (cv v Δ) (Ov v)).p v) L ≤ KD (cv v Δ) (Ov v) := by
      rw [Subgroup.map_le_iff_le_comap]
      intro g hg
      rw [hL, mem_box] at hg
      exact hg v
    intro h0
    exact (h.sig v hv).levelTwoFiniteIndex (Subgroup.relIndex_eq_zero_of_le_right hmap h0)
  have hinf : (L ⊓ M).relIndex L ≠ 0 :=
    Subgroup.relIndex_inf_ne_zero (by rw [Subgroup.relIndex_self]; exact one_ne_zero) hMne
  intro h0
  exact hinf (Subgroup.relIndex_eq_zero_of_le_left hsub h0)

private theorem conj_mul {G : Type} [Group G] (x a b : G) : x⁻¹ * (a * b) * x = x⁻¹ * a * x * (x⁻¹ * b * x) := by group

private theorem fs_mul_left_right_eq_of_mem_u2 (D : Dat Δ) (h : D.Ok) (t : Dat.Par F) (ht : D.Cone t) (a b : DA Δ) (ha : a ∈ D.U2) :
    D.FS t (a * b) = D.FS t b ∧ D.FS t (b * a) = D.FS t b := by
  rw [Dat.U2, mem_box] at ha
  constructor
  all_goals
    unfold Dat.FS
    apply finprod_congr
    intro v
    have hav := ha v
    change (a : ∀ v, ↥(DX (cv v Δ))) v ∈ Dat.J2v D v at hav
    unfold Dat.J2v at hav
    unfold Dat.fSv
    simp only [Subgroup.coe_mul, Pi.mul_apply]
    split_ifs at hav ⊢ with hv
  · exact ((h.sig v hv).S_inv (t v) (ht v hv) _ hav _).1
  · rw [Subgroup.mul_mem_cancel_left _ hav]
  · exact ((h.sig v hv).S_inv (t v) (ht v hv) _ hav _).2
  · rw [Subgroup.mul_mem_cancel_right _ hav]

private theorem fSv_apply_ne_zero_of_fs_ne_zero (D : Dat Δ) (t : Dat.Par F) (g : DA Δ) (hg : D.FS t g ≠ 0) (v : Pl F) :
    D.fSv t v ((g : ∀ v, ↥(DX (cv v Δ))) v) ≠ 0 := by
  intro h0
  apply hg
  unfold Dat.FS
  apply finprod_eq_zero _ v h0
  have hfin : {w | ¬ (g : ∀ v, ↥(DX (cv v Δ))) w ∈ KD (cv w Δ) (Ov w)}.Finite := Filter.eventually_cofinite.1 g.2
  apply ((D.Sg.finite_toSet.union hfin)).subset
  intro w hw
  rw [Function.mem_mulSupport] at hw
  by_contra hc
  simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at hc
  apply hw
  unfold Dat.fSv
  rw [if_neg hc.1]
  simp [one, hc.2]

set_option maxHeartbeats 1000000 in
theorem finS_test : ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (ch : F → ℂ) (x : DA Δ) (B : Base (SU Δ) (SA Δ) V), D.IsBS ch x B → ∀ t, D.Cone t → (Base.Tw.one B).IsTest (D.FSx t x) := by
  intro F _ _ Δ D hD V _ _ ch x B hB t ht
  refine ⟨?_, ?_, ?_⟩
  · intro u y
    rw [hB.ω]
    simp only [MonoidHom.one_apply, inv_one, Units.val_one, one_mul]
    unfold Dat.FSx
    rw [Subgroup.coe_mul, conj_mul]
    exact (fs_mul_left_right_eq_of_mem_u2 D hD t ht _ _ ((hB.U u).1 u.2)).1
  · intro u y
    rw [hB.ω]
    simp only [MonoidHom.one_apply, inv_one, Units.val_one, one_mul]
    unfold Dat.FSx
    change D.FS t (x⁻¹ * ↑(y * ↑u) * x) = D.FS t (x⁻¹ * ↑y * x)
    rw [Subgroup.coe_mul, conj_mul]
    exact (fs_mul_left_right_eq_of_mem_u2 D hD t ht _ _ ((hB.U u).1 u.2)).2
  · change {q : ↥(SA Δ) ⧸ B.U | D.FSx t x (Quotient.out q) ≠ 0}.Finite
    have hc : ∀ (y : ↥(SA Δ)) (v : Pl F), ((x⁻¹ * ↑y * x : DA Δ) : ∀ v, ↥(DX (cv v Δ))) v ∈ SU (cv v Δ) := by
      intro y v
      have hy : (y : DA Δ) ∈ SA Δ := y.2
      unfold SA at hy
      rw [Subgroup.mem_iInf] at hy
      have hyv : ((y : DA Δ) : ∀ v, ↥(DX (cv v Δ))) v ∈ SU (cv v Δ) := hy v
      haveI : (SU (cv v Δ)).Normal := by
        unfold SU
        infer_instance
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Pi.mul_apply, Pi.inv_apply]
      exact Subgroup.Normal.conj_mem' inferInstance _ hyv _
    let Φ : ↥(SA Δ) ⧸ B.U → ((v : ↥D.Sg) → ↥(SU (cv v.1 Δ)) ⧸ (D.S v.1).J2.subgroupOf (SU (cv v.1 Δ))) :=
      fun q v => QuotientGroup.mk ⟨_, hc (Quotient.out q) v.1⟩
    have hT : (Set.univ.pi fun v : ↥D.Sg => {c : ↥(SU (cv v.1 Δ)) ⧸ (D.S v.1).J2.subgroupOf (SU (cv v.1 Δ)) |
        (D.S v.1).fS (t v.1) ((Quotient.out c : ↥(SU (cv v.1 Δ))) : ↥(DX (cv v.1 Δ))) ≠ 0}).Finite :=
      Set.Finite.pi fun v => (hD.sig v.1 v.2).S_fin (t v.1) (ht v.1 v.2)
    apply Set.Finite.of_finite_image (f := Φ)
    · apply hT.subset
      rintro _ ⟨q, hq, rfl⟩ v -
      obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul ((D.S v.1).J2.subgroupOf (SU (cv v.1 Δ)))
        (⟨_, hc (Quotient.out q) v.1⟩ : ↥(SU (cv v.1 Δ)))
      show (D.S v.1).fS (t v.1) ((Quotient.out (QuotientGroup.mk _ : ↥(SU (cv v.1 Δ)) ⧸ _) : ↥(SU (cv v.1 Δ))) : ↥(DX (cv v.1 Δ))) ≠ 0
      rw [hj, Subgroup.coe_mul]
      have hjm : ((j : ↥(SU (cv v.1 Δ))) : ↥(DX (cv v.1 Δ))) ∈ (D.S v.1).J2 := Subgroup.mem_subgroupOf.1 j.2
      rw [((hD.sig v.1 v.2).S_inv (t v.1) (ht v.1 v.2) _ hjm _).2]
      have hne := fSv_apply_ne_zero_of_fs_ne_zero D t _ hq v.1
      unfold Dat.fSv at hne
      rw [if_pos v.2] at hne
      exact hne
    · intro q1 hq1 q2 hq2 heq
      rw [← QuotientGroup.out_eq' q1, ← QuotientGroup.out_eq' q2, QuotientGroup.eq, hB.U]
      have hsplit : x⁻¹ * ((((Quotient.out q1)⁻¹ * Quotient.out q2 : ↥(SA Δ))) : DA Δ) * x =
          (x⁻¹ * ↑(Quotient.out q1) * x)⁻¹ * (x⁻¹ * ↑(Quotient.out q2) * x) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [hsplit, Dat.U2, mem_box]
      intro v
      have hk : ∀ q : ↥(SA Δ) ⧸ B.U, D.FSx t x (Quotient.out q) ≠ 0 → v ∉ D.Sg →
          ((x⁻¹ * ↑(Quotient.out q) * x : DA Δ) : ∀ v, ↥(DX (cv v Δ))) v ∈ KD (cv v Δ) (Ov v) := by
        intro q hq hv
        have hne := fSv_apply_ne_zero_of_fs_ne_zero D t _ hq v
        unfold Dat.fSv at hne
        rw [if_neg hv] at hne
        simpa [one] using hne
      have key : (((x⁻¹ * ↑(Quotient.out q1) * x : DA Δ) : ∀ v, ↥(DX (cv v Δ))) v)⁻¹ *
          ((x⁻¹ * ↑(Quotient.out q2) * x : DA Δ) : ∀ v, ↥(DX (cv v Δ))) v ∈ D.J2v v := by
        unfold Dat.J2v
        split_ifs with hv
        · have hv' := congrFun heq ⟨v, hv⟩
          simp only [Φ] at hv'
          rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hv'
          exact hv'
        · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hk q1 hq1 hv)) (hk q2 hq2 hv)
      exact key

end UpperTheory.V.Z.Sym.Glob
