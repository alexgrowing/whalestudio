import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarRelationReflexive.MapMemSupThree

noncomputable section

open scoped Classical

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

namespace PI.UnitaryGroupMassFormula.ScalRelRepFree

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

structure DC (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (y y' : LFlag S r T')
    (n m : S.V ≃ₗ[E] S.V) : Prop where
  hF : IsLift Λ F
  hy : IsLift Λ y
  hn : n ∈ NLam Λ F
  hm : m ∈ NLam Λ y
  hfr : ∀ a, frame y' a = n (m (frame y a))
  hzt : y'.zt = n (m y.zt)

theorem X_le_Xplus {T₀ : E} (G : LFlag S r T₀) : Xsp G ≤ Xplus G := by
  simp only [Xplus, FlagG.Xplus]
  exact le_sup_left

section Move

variable {Λ : Submodule (𝓞 E) S.V} {T T' : E} {F : LFlag S r T} {y y' : LFlag S r T'}
  {n m : S.V ≃ₗ[E] S.V}

theorem e_eq (h : DC Λ F y y' n m) (a : Fin r) : y'.fl.e a = n (m (y.fl.e a)) := by
  have := h.hfr a.castSucc
  simpa [frame, FlagG.fvec] using this

theorem z_eq (h : DC Λ F y y' n m) : y'.fl.z = n (m y.fl.z) := by
  have := h.hfr (Fin.last r)
  simpa [frame, FlagG.fvec] using this

theorem Xflag_eq (h : DC Λ F y y' n m) (j : ℕ) :
    Xflag y' j = (Xflag y j).map ((m.trans n : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V) := by
  have he : y'.fl.e = fun i => ((m.trans n : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V) (y.fl.e i) :=
    funext fun i => by rw [e_eq h i]; rfl
  simp only [Xflag, FlagG.Xa]
  rw [Submodule.map_span, Set.image_image, he]

theorem mem_X' (h : DC Λ F y y' n m) {v : S.V} : v ∈ Xsp y' ↔ n.symm v ∈ Xsp y := by
  rw [← Xa_ge y' le_rfl, Xflag_eq h, Xa_ge y le_rfl, Submodule.mem_map_equiv, LinearEquiv.symm_trans_apply]
  exact nl_symm_X_iff h.hm

theorem mem_XLam' (h : DC Λ F y y' n m) {v : S.V} : v ∈ XLam Λ y' ↔ n.symm v ∈ XLam Λ y := by
  rw [mem_XLam, mem_XLam, mem_X' h]
  exact and_congr_left' ⟨aut_symm_mem h.hn.1, fun hv => by simpa using aut_mem h.hn.1 hv⟩

theorem mz_sub (h : DC Λ F y y' n m) : m y.zt - y.zt ∈ XLam Λ y := by
  rw [h.hy.2]
  exact nl_sub_XLam h.hm h.hy.1 (z_orth y)

theorem nzF_sub (h : DC Λ F y y' n m) : n F.zt - F.zt ∈ XLam Λ F := by
  rw [h.hF.2]
  exact nl_sub_XLam h.hn h.hF.1 (z_orth F)

theorem nzF_symm_sub (h : DC Λ F y y' n m) : n.symm F.zt - F.zt ∈ XLam Λ F := by
  rw [h.hF.2]
  exact nl_symm_sub_XLam h.hn h.hF.1 (z_orth F)

theorem uue_symm (h : DC Λ F y y' n m) {v : S.V} (hv : v ∈ UUE Λ F y') : n.symm v ∈ UUE Λ F y := by
  refine uue_map (n.symm : S.V →ₗ[E] S.V) ?_ ?_ ?_ ?_ hv
  · intro w hw
    exact uue_of (uu_A (nl_symm_XLam h.hn hw))
  · have e : (n.symm : S.V →ₗ[E] S.V) F.zt = F.zt + (n.symm F.zt - F.zt) := by simp
    rw [e]
    exact add_mem (uue_of uu_B) (uue_of (uu_A (nzF_symm_sub h)))
  · intro w hw
    exact uue_of (uu_C ((mem_XLam' h).mp hw))
  · have e : (n.symm : S.V →ₗ[E] S.V) y'.zt = y.zt + (m y.zt - y.zt) := by simp [h.hzt]
    rw [e]
    exact add_mem (uue_of uu_D) (uue_of (uu_C (mz_sub h)))

theorem uue_fwd (h : DC Λ F y y' n m) {v : S.V} (hv : v ∈ UUE Λ F y) : n v ∈ UUE Λ F y' := by
  refine uue_map (n : S.V →ₗ[E] S.V) ?_ ?_ ?_ ?_ hv
  · intro w hw
    exact uue_of (uu_A (nl_XLam h.hn hw))
  · have e : (n : S.V →ₗ[E] S.V) F.zt = F.zt + (n F.zt - F.zt) := by simp
    rw [e]
    exact add_mem (uue_of uu_B) (uue_of (uu_A (nzF_sub h)))
  · intro w hw
    have : n w ∈ XLam Λ y' := (mem_XLam' h).mpr (by simpa using hw)
    exact uue_of (uu_C this)
  · have e : (n : S.V →ₗ[E] S.V) y.zt = y'.zt - n (m y.zt - y.zt) := by simp [h.hzt]
    rw [e]
    have : n (m y.zt - y.zt) ∈ XLam Λ y' := (mem_XLam' h).mpr (by simpa using mz_sub h)
    exact sub_mem (uue_of uu_D) (uue_of (uu_C this))

theorem mem_UUE' (h : DC Λ F y y' n m) {v : S.V} : v ∈ UUE Λ F y' ↔ n.symm v ∈ UUE Λ F y :=
  ⟨uue_symm h, fun hv => by simpa using uue_fwd h hv⟩

theorem mem_Hp' (h : DC Λ F y y' n m) (w : S.V) : w ∈ Hp Λ F y' ↔ n.symm w ∈ Hp Λ F y := by
  unfold Hp
  exact orth_transport h.hn.1.1 (fun v => mem_UUE' (v := v) h) w

theorem mem_Xplus' (h : DC Λ F y y' n m) {v : S.V} : v ∈ Xplus y' ↔ n.symm v ∈ Xplus y := by
  constructor
  · intro hv
    have hz : (n.symm : S.V →ₗ[E] S.V) y'.fl.z - y.fl.z ∈ Xsp y := by
      have e : (n.symm : S.V →ₗ[E] S.V) y'.fl.z - y.fl.z = m y.fl.z - y.fl.z := by simp [z_eq h]
      rw [e]
      exact nl_orth h.hm (z_orth y)
    exact xplus_map (n.symm : S.V →ₗ[E] S.V) (fun w hw => (mem_X' h).mp hw) hz hv
  · intro hv
    have hz : (n : S.V →ₗ[E] S.V) y.fl.z - y'.fl.z ∈ Xsp y' := by
      rw [mem_X' h]
      have e : n.symm ((n : S.V →ₗ[E] S.V) y.fl.z - y'.fl.z) = -(m y.fl.z - y.fl.z) := by
        simp [z_eq h]
      rw [e]
      exact (Xsp y).neg_mem (nl_orth h.hm (z_orth y))
    have := xplus_map (A := y) (B := y') (n : S.V →ₗ[E] S.V)
      (fun w hw => (mem_X' h).mpr (by simpa using hw)) hz hv
    simpa using this

theorem mem_YL (h : DC Λ F y y' n m) (w : S.V) : w ∈ Ylift Λ F y' ↔ n.symm w ∈ Ylift Λ F y := by
  simp only [Ylift, Submodule.mem_inf]
  rw [mem_UUE' h, orth_transport h.hn.1.1 (fun v => nl_Xplus_iff h.hn (v := v)) w]

theorem mem_YL' (h : DC Λ F y y' n m) (w : S.V) : w ∈ Ylift' Λ F y' ↔ n.symm w ∈ Ylift' Λ F y := by
  simp only [Ylift', Submodule.mem_inf]
  rw [mem_UUE' h, orth_transport h.hn.1.1 (fun v => mem_Xplus' h (v := v)) w]

theorem mem_NgX' (h : DC Λ F y y' n m) (g : ℕ) {v : S.V} :
    v ∈ NgX Λ g F y' ↔ n.symm v ∈ NgX Λ g F y := by
  unfold NgX
  constructor
  · intro hv
    exact map_mem_sup_three (n.symm : S.V →ₗ[E] S.V) (fun w hw => gL_map _ (fun u hu => aut_symm_mem h.hn.1 hu) g hw)
      (fun w hw => nl_symm_XLam h.hn hw) (fun w hw => (mem_XLam' h).mp hw) hv
  · intro hv
    have := map_mem_sup_three (n : S.V →ₗ[E] S.V) (fun w hw => gL_map _ (fun u hu => aut_mem h.hn.1 hu) g hw)
      (fun w hw => nl_XLam h.hn hw) (fun w hw => (mem_XLam' h).mpr (by simpa using hw)) hv
    simpa using this

theorem sg_move (h : DC Λ F y y' n m) (a b : S.V) (al al' : E) :
    SgRel F y (n.symm a) (n.symm b) al al' ↔ SgRel F y' a b al al' := by
  constructor
  · rintro ⟨u, hu, u', hu', e⟩
    refine ⟨n u + al • (n F.zt - F.zt), ?_, n u' - al' • n (m y.zt - y.zt), ?_, ?_⟩
    · exact add_mem (nl_X_mem h.hn hu) (Submodule.smul_mem _ _ (mem_XLam.mp (nzF_sub h)).2)
    · refine sub_mem ((mem_X' h).mpr (by simpa using hu')) (Submodule.smul_mem _ _ ((mem_X' h).mpr ?_))
      simpa using (mem_XLam.mp (mz_sub h)).2
    · have e2 : a - b = n (n.symm a - n.symm b) := by simp
      rw [e2, e, h.hzt]
      simp only [map_add, map_sub, map_smul, smul_sub]
      abel
  · rintro ⟨U, hU, U', hU', e⟩
    refine ⟨n.symm U + al • (n.symm F.zt - F.zt), ?_, n.symm U' + al' • (m y.zt - y.zt), ?_, ?_⟩
    · exact add_mem (nl_symm_X h.hn hU) (Submodule.smul_mem _ _ (mem_XLam.mp (nzF_symm_sub h)).2)
    · exact add_mem ((mem_X' h).mp hU') (Submodule.smul_mem _ _ (mem_XLam.mp (mz_sub h)).2)
    · have e2 : n.symm a - n.symm b = n.symm (a - b) := by simp
      rw [e2, e, h.hzt]
      simp only [map_add, map_sub, map_smul, LinearEquiv.symm_apply_apply, smul_sub]
      abel

end Move

theorem mem_ThP (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (F' F'' : LFlag S r T')
    (β : S.V ≃ₗ[E] S.V) (p : S.V × S.V) :
    p ∈ ThPairs Λ F F' F'' β ↔ p.1 ∈ Hp Λ F F' ∧ p.2 ∈ Hp Λ F F'' ∧ p.1 - p.2 ∈ Xsp F ∧
      β p.1 - p.2 ∈ Xsp F'' := by
  simp only [ThPairs, Submodule.mem_inf, Submodule.mem_prod, Submodule.mem_comap, LinearMap.sub_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  tauto

theorem orth_beta {T' : E} {β : S.V ≃ₗ[E] S.V} (hβ : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) {x y : LFlag S r T'}
    (hX : (Xsp x).map (β : S.V →ₗ[E] S.V) = Xsp y) {v : S.V} (hv : v ∈ orth S (Xsp x)) :
    β v ∈ orth S (Xsp y) :=
  (orth_transport hβ (U := Xsp x) (U' := Xsp y)
    (fun w => by rw [← hX, Submodule.mem_map_equiv]) (β v)).mpr (by simpa using hv)

theorem scalRel_move (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (g k : ℕ) {T T' : E}
    (F : LFlag S r T) (x y y' : LFlag S r T') (n m : S.V ≃ₗ[E] S.V) (h : DC Λ F y y' n m)
    (hs : PI.ScalRelRepFree.ScalRel Λ g k F x y) : PI.ScalRelRepFree.ScalRel Λ g k F x y' := by
  obtain ⟨β, ⟨hAut, hfl, hz, hI⟩, hs0, hsc⟩ := hs
  let β' : S.V ≃ₗ[E] S.V := (β.trans m).trans n
  have hb' : ∀ v, β' v = n (m (β v)) := fun v => rfl
  have hXβ : (Xsp x).map (β : S.V →ₗ[E] S.V) = Xsp y := by
    rw [← Xa_ge x le_rfl, ← Xa_ge y le_rfl]
    exact hfl r
  have hβo : ∀ v ∈ orth S (Xsp x), β v ∈ orth S (Xsp y) := fun v hv => orth_beta hAut.1 hXβ hv
  have oF : ∀ b ∈ Hp Λ F y', b ∈ orth S (Xsp F) := fun b hb =>
    orth_anti' (PI.UnitaryGroupMassFormula.BetaLUniq.Xsp_le_UUE S Λ hΛ F y') hb
  have oF' : ∀ b ∈ Hp Λ F y, b ∈ orth S (Xsp F) := fun b hb =>
    orth_anti' (PI.UnitaryGroupMassFormula.BetaLUniq.Xsp_le_UUE S Λ hΛ F y) hb
  have oX : ∀ a ∈ Hp Λ F x, a ∈ orth S (Xsp x) := fun a ha =>
    orth_anti' (PI.UnitaryGroupMassFormula.BetaLUniq.Xsp_le_UUE' S Λ hΛ F x) ha
  have hTh : Th Λ F x y' β' = Th Λ F x y β := by
    ext v
    simp only [Th, Submodule.mem_map]
    constructor
    · rintro ⟨⟨a, b⟩, hp, rfl⟩
      obtain ⟨ha, hb, hab, hbb⟩ := (mem_ThP Λ F x y' β' _).mp hp
      refine ⟨(a, n.symm b), (mem_ThP Λ F x y β _).mpr ⟨ha, (mem_Hp' h b).mp hb, ?_, ?_⟩, rfl⟩
      · have e : a - n.symm b = (a - b) - (n.symm b - b) := by abel
        rw [e]
        exact sub_mem hab (nl_symm_sub h.hn (oF b hb))
      · have e : β a - n.symm b = n.symm (β' a - b) - (m (β a) - β a) := by
          rw [hb']; simp
        rw [e]
        exact sub_mem ((mem_X' h).mp hbb) (nl_orth h.hm (hβo a (oX a ha)))
    · rintro ⟨⟨a, b⟩, hp, rfl⟩
      obtain ⟨ha, hb, hab, hbb⟩ := (mem_ThP Λ F x y β _).mp hp
      refine ⟨(a, n b), (mem_ThP Λ F x y' β' _).mpr ⟨ha, (mem_Hp' h _).mpr (by simpa using hb), ?_, ?_⟩, rfl⟩
      · have e : a - n b = (a - b) - (n b - b) := by abel
        rw [e]
        exact sub_mem hab (nl_orth h.hn (oF' b hb))
      · rw [mem_X' h]
        have e : n.symm (β' a - n b) = (m (β a) - β a) + (β a - b) := by
          rw [hb']; simp
        rw [e]
        exact add_mem (nl_orth h.hm (hβo a (oX a ha))) hbb
  refine ⟨β', ⟨aut_trans (aut_trans hAut h.hm.1) h.hn.1, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j
    have hc : (β' : S.V →ₗ[E] S.V) = ((m.trans n : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V).comp (β : S.V →ₗ[E] S.V) := by
      ext v; rfl
    rw [hc, Submodule.map_comp, hfl j, Xflag_eq h j]
  · show n (m (β x.fl.z)) = y'.fl.z
    rw [hz, z_eq h]
  · intro x' hx' l hl
    rw [hI x' hx' l hl, mem_NgX' h g]
    rw [mem_Lrep] at hx' hl
    have d1 : n.symm l - l ∈ NgX Λ g F y :=
      Submodule.mem_sup_left (Submodule.mem_sup_right (nl_symm_sub_XLam h.hn hl.1 hl.2))
    have d2 : m (β x') - β x' ∈ NgX Λ g F y :=
      Submodule.mem_sup_right (nl_sub_XLam h.hm (aut_mem hAut hx'.1) (hβo x' hx'.2))
    have e : n.symm (l - β' x') = (l - β x') + ((n.symm l - l) - (m (β x') - β x')) := by
      rw [hb']; simp only [map_sub, LinearEquiv.symm_apply_apply]; abel
    rw [e, Submodule.add_mem_iff_left _ (sub_mem d1 d2)]
  · show k - finrank E (Th Λ F x y' β') = 1
    rw [hTh]
    exact hs0
  · intro y1 hy1 Y2 hY2 y1' hy1' Y2'' hY2'' h1 h2 al al'
    have hy2 := (mem_YL h Y2).mp hY2
    have hy2'' := (mem_YL' h Y2'').mp hY2''
    have oY2 : Y2 ∈ orth S (Xsp F) := orth_anti' (X_le_Xplus F) (Submodule.mem_inf.mp hY2).2
    have oy1' : y1' ∈ orth S (Xsp x) := orth_anti' (X_le_Xplus x) (Submodule.mem_inf.mp hy1').2
    have k1 : y1 - n.symm Y2 ∈ Xsp F := by
      have e : y1 - n.symm Y2 = (y1 - Y2) - (n.symm Y2 - Y2) := by abel
      rw [e]
      exact sub_mem h1 (nl_symm_sub h.hn oY2)
    have k2 : n.symm Y2'' - β y1' ∈ Xsp y := by
      have e : n.symm Y2'' - β y1' = n.symm (Y2'' - β' y1') + (m (β y1') - β y1') := by
        rw [hb']; simp only [map_sub, LinearEquiv.symm_apply_apply]; abel
      rw [e]
      exact add_mem ((mem_X' h).mp h2) (nl_orth h.hm (hβo y1' oy1'))
    rw [hsc y1 hy1 (n.symm Y2) hy2 y1' hy1' (n.symm Y2'') hy2'' k1 k2 al al']
    exact sg_move h Y2 Y2'' al al'

end PI.UnitaryGroupMassFormula.ScalRelRepFree
