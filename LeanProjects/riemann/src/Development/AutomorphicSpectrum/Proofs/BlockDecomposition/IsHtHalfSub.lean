import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2

noncomputable section

open NumberField Matrix
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.So GroundTheory.Global

namespace GlobalTheory.CompanionTheory.EisJMir

section Gen

variable {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']

theorem isHt_pull (j : G →* G') (hj : Continuous j) {Γ K P : Subgroup G} {Γ' K' P' : Subgroup G'} {η : G' → ℝ}
    (h : IsHt Γ' K' P' η) (hΓ : ∀ γ ∈ Γ, j γ ∈ Γ') (hK : ∀ k ∈ K, j k ∈ K') (hP : ∀ p ∈ P, j p ∈ P') :
    IsHt Γ K P (fun x => η (j x)) := by
  refine ⟨fun p hp g => ?_, fun g k hk => ?_, fun γ hγ hγP => ?_, h.cont.comp hj⟩
  · rw [map_mul]
    exact h.left (j p) (hP p hp) (j g)
  · rw [map_mul]
    exact h.right (j g) (j k) (hK k hk)
  · exact h.rat (j γ) (hΓ γ hγ) (hP γ hγP)

theorem isHt_of_top {Γ K P : Subgroup G} {η : G → ℝ} (h : IsHt Γ K ⊤ η) : IsHt Γ K P η := by
  exact ⟨fun p _ g => h.left p (Subgroup.mem_top p) g, h.right, fun γ hγ _ => h.rat γ hγ (Subgroup.mem_top γ),
    h.cont⟩

theorem isHt_half_add {Γ K P : Subgroup G} {a b : G → ℝ} (ha : IsHt Γ K P a) (hb : IsHt Γ K P b) :
    IsHt Γ K P (fun x => (a x + b x) / 2) := by
  refine ⟨fun p hp g => ?_, fun g k hk => ?_, fun γ hγ hγP => ?_, (ha.cont.add hb.cont).div_const 2⟩
  · rw [ha.left p hp g, hb.left p hp g]
    ring
  · rw [ha.right g k hk, hb.right g k hk]
  · rw [ha.rat γ hγ hγP, hb.rat γ hγ hγP]
    norm_num

theorem isHt_half_sub {Γ K P : Subgroup G} {a b : G → ℝ} (ha : IsHt Γ K P a) (hb : IsHt Γ K P b) :
    IsHt Γ K P (fun x => (a x - b x) / 2) := by
  refine ⟨fun p hp g => ?_, fun g k hk => ?_, fun γ hγ hγP => ?_, (ha.cont.sub hb.cont).div_const 2⟩
  · rw [ha.left p hp g, hb.left p hp g]
    ring
  · rw [ha.right g k hk, hb.right g k hk]
  · rw [ha.rat γ hγ hγP, hb.rat γ hγ hγP]
    norm_num

theorem isCh_pull (j : G →* G') (hj : Continuous j) {Γ P : Subgroup G} {Γ' P' : Subgroup G'} {u : G' → ℂ} {c : G → ℂ}
    (hu : IsCh Γ' P' u) (hc : IsCh Γ ⊤ c) (hΓ : ∀ γ ∈ Γ, j γ ∈ Γ') (hP : ∀ p ∈ P, j p ∈ P') :
    IsCh Γ P (fun x => u (j x) * (c x)⁻¹) := by
  have hc0 : ∀ x, c x ≠ 0 := fun x h0 => by
    have h1 := hc.norm x (Subgroup.mem_top x)
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  refine ⟨fun p hp q hq => ?_, fun p hp => ?_, fun γ hγ hγP => ?_, ?_⟩
  · rw [map_mul, hu.mul (j p) (hP p hp) (j q) (hP q hq), hc.mul p (Subgroup.mem_top p) q (Subgroup.mem_top q),
      mul_inv]
    ring
  · rw [norm_mul, norm_inv, hu.norm (j p) (hP p hp), hc.norm p (Subgroup.mem_top p)]
    norm_num
  · rw [hu.rat (j γ) (hΓ γ hγ) (hP γ hγP), hc.rat γ hγ (Subgroup.mem_top γ)]
    norm_num
  · refine (hu.cont.comp hj.continuousOn (fun x hx => hP x hx)).mul ?_
    exact (hc.cont.mono (fun x _ => Subgroup.mem_top x)).inv₀ (fun x _ => hc0 x)

end Gen

theorem jmir : StdGood → GrpTop → BdetLaw → ExtLaw → ParLaw → JTop → JCpt → JPar → JIwa → JRat → JCh → JMir := by
  intro hStd hGT hBd hExt hPar hJT hJC hJP hJI hJR hJCh F E R _ _ _ _ _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i j hA hB
    hi hJ hIwa
  obtain ⟨hjc, -, -, -⟩ := hJT F E R A ε ν r δ α ω ι i j hA hB hi hJ
  have hcK := hJC F E R A ε ν r δ α ω ι i j hA hB hi hJ
  obtain ⟨hst, hQeq, hbd⟩ := hJP F E R A ε ν r δ α ω ι i j hA hB hi hJ
  have hIw := hJI F E R A ε ν r δ α ω ι i j hA hB hi hJ
  obtain ⟨hmapΓ, htr⟩ := hJR F E R A ε ν r δ α ω ι i j hA hB hi hJ
  obtain ⟨hc0, hld⟩ := hJCh F E R A ε ν r δ α ω ι i j hA hB hi hJ
  obtain ⟨hparU, hhtU, -⟩ := (hPar E R A hA ι ε Set.univ).2 (by rw [inf_idem]; exact hIwa)
  rw [inf_idem] at hparU
  have hGL := hA.toGoodL
  have hSG := (hStd F).lgmul
  have hlg1 : A.lg 1 = 0 := by
    have h := hGL.lgmul 1 1
    rw [mul_one] at h
    linarith
  have hP : ∀ p ∈ Subgroup.comap (prj A ν ι) (stab 𝔸[𝓞 F, F] {(Sum.inl i : ι ⊕ ι)}),
      j p ∈ A.uQ ε Set.univ := by
    intro p hp
    rw [← hQeq] at hp
    exact hp
  have hK : ∀ k ∈ cK α j, j k ∈ A.uK ε ι := fun k hk => (Subgroup.mem_inf.1 hk).1
  have hΓ : ∀ γ ∈ cΓ A ν ι, j γ ∈ A.uΓ ε ι := by
    intro γ hγ
    rw [← hmapΓ]
    exact Subgroup.mem_map_of_mem j hγ
  have hωsq : ∀ y : IdeleGroup F, ω.toIdele y * ω.toIdele y = 1 := by
    intro y
    rw [hB.ωχ, mul_eq_one_iff_eq_inv]
    have h1 := hA.χσ (Units.map (ν : 𝔸[𝓞 F, F] →* R) y)
    convert h1 using 2
    all_goals (ext; simp [hB.fix])
  have hcov : ∀ x : cover A ν ι, A.lg (x : Rˣ × GL (ι ⊕ ι) 𝔸[𝓞 F, F]).1 =
      -(adStd F).lg (Matrix.GeneralLinearGroup.det (prj A ν ι x)) ∧
      A.χ (Units.map (ν : 𝔸[𝓞 F, F] →* R) (Matrix.GeneralLinearGroup.det (prj A ν ι x))) = 1 := by
    intro x
    have hx := MonoidHom.mem_ker.1 x.2
    simp only [MonoidHom.mul_apply, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst,
      MonoidHom.coe_snd] at hx
    constructor
    · have h := congrArg A.lg hx
      rw [hGL.lgmul, hGL.lgmul, hB.lgσ, hB.lg, hlg1] at h
      show A.lg (x : Rˣ × GL (ι ⊕ ι) 𝔸[𝓞 F, F]).1 = -(adStd F).lg (Matrix.GeneralLinearGroup.det (x : Rˣ × GL (ι ⊕ ι) 𝔸[𝓞 F, F]).2)
      linarith
    · have h := congrArg A.χ hx
      rw [map_mul, map_mul, hA.χσ, map_one, mul_inv_cancel, one_mul] at h
      exact h
  have hext : ∀ x ∈ Subgroup.comap (prj A ν ι) (stab 𝔸[𝓞 F, F] {(Sum.inl i : ι ⊕ ι)}),
      A.uH ε Set.univ (j x) = A.lg (bdet (Sum.inl '' (Set.univ : Set ι)) ((j x : A.U ε ι) : GL (ι ⊕ ι) R)) := by
    intro x hx
    obtain ⟨-, -, -, hT2U, -, -, hKc⟩ := hGT E R A hA ι ε
    haveI := hT2U
    obtain ⟨-, hmulS, hcontS, hratS, hkS, -⟩ := hBd E R A hGL (ι ⊕ ι) (Sum.inl '' (Set.univ : Set ι))
    have h := (hExt (A.U ε ι) (A.uΓ ε ι) (A.uK ε ι) (A.uQ ε Set.univ)
      (fun p => A.lg (bdet (Sum.inl '' (Set.univ : Set ι)) (p : GL (ι ⊕ ι) R))) hKc hparU.closed hIwa
      (fun p hp q hq => by
        show A.lg (bdet _ ((p * q : A.U ε ι) : GL (ι ⊕ ι) R)) = _
        rw [Subgroup.coe_mul, hmulS _ (Subgroup.mem_subgroupOf.1 hp) _ (Subgroup.mem_subgroupOf.1 hq), hGL.lgmul])
      (hGL.lgcont.comp_continuousOn (hcontS.comp continuous_subtype_val.continuousOn
        (fun p hp => Subgroup.mem_subgroupOf.1 hp)))
      (fun p hp hk => hkS _ (Subgroup.mem_subgroupOf.1 hp) (Subgroup.mem_subgroupOf.1 hk))
      (fun p hp hg => by
        obtain ⟨e, he⟩ := hratS _ (Subgroup.mem_subgroupOf.1 hp) (Subgroup.mem_subgroupOf.1 hg)
        show A.lg _ = 0
        rw [he]
        exact hGL.lgi e)).2 (j x) (hP x hx) 1 (Subgroup.one_mem _)
    rw [mul_one] at h
    exact h
  refine ⟨?_, ?_, ?_, hcK, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hld, ?_, ?_, fun g => rfl⟩
  · have h1 : 0 < Fintype.card ι := Fintype.card_pos_iff.2 ⟨i⟩
    rw [Fintype.card_sum]
    omega
  · refine ContinuousMonoidHom.ext fun x => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    exact hωsq y
  · exact continuous_snd.comp continuous_subtype_val
  · intro κ hκ
    obtain ⟨κ', hκ', hEq⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hκ).2)
    refine ⟨κ', hκ', ?_⟩
    have hd : (fun k : ι ⊕ ι => ((Sum.elim (fun _ => (1 : IdeleGroup F)) (fun _ => α) k : IdeleGroup F) : 𝔸[𝓞 F, F])) =
        (Sum.elim (fun _ => 1) (fun _ => (α : 𝔸[𝓞 F, F])) : ι ⊕ ι → 𝔸[𝓞 F, F]) := by
      funext k
      rcases k with k | k <;> rfl
    rw [hd]
    change ((prj A ν ι κ : GL (ι ⊕ ι) 𝔸[𝓞 F, F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[𝓞 F, F]) * ((dg ι α : GL (ι ⊕ ι) 𝔸[𝓞 F, F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[𝓞 F, F]) =
      ((dg ι α : GL (ι ⊕ ι) 𝔸[𝓞 F, F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[𝓞 F, F]) * (κ' : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[𝓞 F, F])
    rw [← hEq]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← Units.val_mul, inv_mul_cancel_right, Units.val_mul]
  · intro γ hγ
    exact (Subgroup.mem_prod.1 (Subgroup.mem_subgroupOf.1 hγ)).2
  · intro s hs g hg
    obtain ⟨γ, hγ, h⟩ := htr g hg
    refine ⟨γ, hγ, ?_⟩
    rcases hs with rfl | rfl
    · exact h
    · rw [hst]
      exact h
  · refine ⟨?_, hIw, isCh_pull j hjc hparU.ch hc0 hΓ hP⟩
    rw [← hQeq, Subgroup.coe_comap]
    exact hparU.closed.preimage hjc
  · rw [hst]
    refine ⟨?_, hIw, isCh_pull j hjc hparU.ch hc0 hΓ hP⟩
    rw [← hQeq, Subgroup.coe_comap]
    exact hparU.closed.preimage hjc
  · exact isHt_half_add (isHt_pull j hjc hhtU hΓ hK hP) (isHt_of_top hld)
  · rw [hst]
    exact isHt_half_sub (isHt_pull j hjc hhtU hΓ hK hP) (isHt_of_top hld)
  · intro p hp
    obtain ⟨hb1, -⟩ := hbd p hp
    obtain ⟨hl, -⟩ := hcov p
    refine ⟨?_, ?_⟩
    · show (A.χ (bdet (Sum.inl '' Set.univ) ((j p : A.U ε ι) : GL (ι ⊕ ι) R)) : ℂ) *
          ((A.χ (p : Rˣ × GL (ι ⊕ ι) 𝔸[𝓞 F, F]).1 : ℂ))⁻¹ = _
      rw [hb1, map_mul, Circle.coe_mul, hB.ωχ, mul_comm, ← mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero _),
        one_mul]
    · show (A.uH ε Set.univ (j p) + ld p) / 2 = _
      rw [hext p hp, hb1, hGL.lgmul, hB.lg, hl]
      simp only [So.ld]
      ring
  · intro p hp
    rw [hst] at hp
    obtain ⟨hb1, hb2⟩ := hbd p hp
    obtain ⟨hl, hχ⟩ := hcov p
    have hωb : ω.toIdele (bdet {Sum.inl i} (prj A ν ι p)) = ω.toIdele (bdet {Sum.inr i} (prj A ν ι p)) := by
      have h3 : ω.toIdele (bdet {Sum.inl i} (prj A ν ι p)) * ω.toIdele (bdet {Sum.inr i} (prj A ν ι p)) = 1 := by
        rw [hB.ωχ, hB.ωχ, ← map_mul, ← map_mul, ← hb2]
        exact hχ
      exact mul_right_cancel (h3.trans (hωsq _).symm)
    refine ⟨?_, ?_⟩
    · show (A.χ (bdet (Sum.inl '' Set.univ) ((j p : A.U ε ι) : GL (ι ⊕ ι) R)) : ℂ) *
          ((A.χ (p : Rˣ × GL (ι ⊕ ι) 𝔸[𝓞 F, F]).1 : ℂ))⁻¹ = _
      rw [hb1, map_mul, Circle.coe_mul, ← hωb, hB.ωχ, mul_comm, ← mul_assoc,
        inv_mul_cancel₀ (Circle.coe_ne_zero _), one_mul]
    · show (A.uH ε Set.univ (j p) - ld p) / 2 = _
      rw [hext p hp, hb1, hGL.lgmul, hB.lg, hl]
      simp only [So.ld]
      rw [hb2, hSG]
      ring

end GlobalTheory.CompanionTheory.EisJMir
