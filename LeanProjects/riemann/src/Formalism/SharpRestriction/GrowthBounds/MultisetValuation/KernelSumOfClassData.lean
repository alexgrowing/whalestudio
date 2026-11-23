import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.InLatCSmulC

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def Eqv (j : ℕ) (F : X.Fm j) : Prop :=
  (∀ c (L : (X.Pj j).Tup), ¬ (X.Pj j).IsLatTup L → F c L = 0) ∧
  ∀ c (γ : (X.Lv.lev j c).Γ) (L : (X.Pj j).Tup),
    F c ((X.Lv.lev j c).smul γ L) = ((X.Lv.lev j c).χ γ : X.G.O) • (X.Lv.lev j c).actX γ (F c L)

theorem mem_Int_iff (j : ℕ) (F : X.Fm j) :
    F ∈ X.Int j ↔ (∀ c (L : (X.Pj j).Tup), (X.Pj j).IsLatTup L → F c L ∈ (X.Pj j).HtupW L) ∧ Eqv X j F := by
  simp only [Sys.Int, Levels.Int, Submodule.mem_pi, Set.mem_univ, true_implies, Level.M, Level.funMod,
    Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_ker, LinearMap.proj_apply,
    LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.restrictScalars_apply,
    sub_eq_zero, Eqv, forall_and, and_assoc]

theorem Eqv_smul {j : ℕ} {F : X.Fm j} (a : X.G.Kf) (h : Eqv X j F) : Eqv X j (a • F) := by
  refine ⟨fun c L hL => ?_, fun c γ L => ?_⟩
  · simp [h.1 c L hL]
  · simp only [Pi.smul_apply, h.2 c γ L]
    rw [smul_comm, map_smul]

theorem Eqv_add {j : ℕ} {F F' : X.Fm j} (h : Eqv X j F) (h' : Eqv X j F') : Eqv X j (F + F') := by
  refine ⟨fun c L hL => ?_, fun c γ L => ?_⟩
  · simp [h.1 c L hL, h'.1 c L hL]
  · simp [h.2 c γ L, h'.2 c γ L, smul_add]

theorem Eqv_zero (j : ℕ) : Eqv X j 0 := by
  refine ⟨fun _ _ _ => rfl, fun c γ L => ?_⟩
  simp

theorem Eqv_of_FQ {j : ℕ} {F : X.Fm j} (h : F ∈ X.FQ j) : Eqv X j F := by
  unfold Sys.FQ at h
  induction h using Submodule.span_induction with
  | mem x hx => exact ((mem_Int_iff X j x).1 hx).2
  | zero => exact Eqv_zero X j
  | add x y _ _ hx hy => exact Eqv_add X hx hy
  | smul a x _ hx => exact Eqv_smul X a hx

variable {X}

theorem vGe_of (Y : Pend X) {j : ℕ} {F : X.Fm j} {g : ℝ} (hE : Eqv X j F)
    (hv : ∀ c (L : (X.Pj j).Tup), (X.Pj j).IsLatTup L → F c L ∈ scale (X.vsc g) ((X.Pj j).HtupW L)) :
    X.vGe j F g := by
  unfold Sys.vGe scale
  rw [Submodule.mem_map]
  by_cases hc : X.vsc g = 0
  · refine ⟨0, zero_mem _, ?_⟩
    funext c L
    simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, hc, zero_smul, Pi.zero_apply]
    by_cases hL : (X.Pj j).IsLatTup L
    · obtain ⟨y, _, hy⟩ := hv c L hL
      simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, hc, zero_smul] at hy
      exact hy
    · exact (hE.1 c L hL).symm
  · refine ⟨(X.vsc g)⁻¹ • F, ?_, ?_⟩
    · rw [mem_Int_iff]
      refine ⟨fun c L hL => ?_, Eqv_smul X _ hE⟩
      obtain ⟨y, hy, hy'⟩ := hv c L hL
      simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply] at hy'
      simp only [Pi.smul_apply]
      rw [← hy', smul_smul, inv_mul_cancel₀ hc, one_smul]
      exact hy
    · simp [smul_smul, inv_mul_cancel₀ hc, mul_inv_cancel₀ hc]

variable (X)

def ERel (J : ℕ) (i0 : X.Pl → ℕ) (L'' L' : (X.Pj J).Tup) : Prop :=
  ∀ v' : Fin (X.Pj J).nV, (i0 (X.vB J v') = 0 ∧ L'' v' = L' v') ∨
    (1 ≤ i0 (X.vB J v') ∧ IsEdge p ((X.Pj J).n' v') (i0 (X.vB J v')) ⟨L'' v', L' v'⟩)

def pN (J : ℕ) (i0 : X.Pl → ℕ) (v : X.Pl) : X.G.Kf := (p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) J (i0 v))

theorem pN_zero (J : ℕ) (i0 : X.Pl → ℕ) (v : X.Pl) (h : i0 v = 0) : pN X J i0 v = 1 := by
  simp [pN, h, Nprime]

theorem vB_vJ (J : ℕ) (v : X.Pl) : X.vB J (X.vJ J v) = v := by
  simp [Sys.vB, Sys.vJ]

theorem vJ_vB (J : ℕ) (v' : Fin (X.Pj J).nV) : X.vJ J (X.vB J v') = v' := by
  simp [Sys.vB, Sys.vJ]

theorem TtL_mem (J : ℕ) (i0 : X.Pl → ℕ) (c' : X.Lv.comp J) (T : Submodule X.G.O (X.Pj J).Xsp) (F : X.Fm J) :
    ∀ (vs : List X.Pl), vs.Nodup → ∀ (a : X.G.Kf) (Lc : (X.Pj J).Tup),
      (∀ L'', ERel X J (fun v => if v ∈ vs then i0 v else 0) L'' Lc →
        (a * (vs.map (pN X J i0)).prod) • F c' L'' ∈ T) →
      a • TtL X J i0 vs F c' Lc ∈ T := by
  intro vs
  induction vs with
  | nil =>
    intro _ a Lc H
    have := H Lc (fun v' => Or.inl ⟨by simp, rfl⟩)
    simpa [TtL] using this
  | cons v vs ih =>
    intro hnd a Lc H
    have hv : v ∉ vs := (List.nodup_cons.mp hnd).1
    have hnd' : vs.Nodup := (List.nodup_cons.mp hnd).2
    have hT : TtL X J i0 (v :: vs) F = X.Tt v (i0 v) J (TtL X J i0 vs F) := rfl
    rw [hT]
    by_cases h0 : i0 v = 0
    · unfold Sys.Tt
      rw [if_pos h0]
      apply ih hnd' a Lc
      intro L'' hrel
      have hfun : (fun u => if u ∈ v :: vs then i0 u else 0) = (fun u => if u ∈ vs then i0 u else 0) := by
        funext u
        by_cases hu : u = v
        · subst hu; simp [h0, hv]
        · simp [hu]
      have := H L'' (by rw [hfun]; exact hrel)
      rwa [List.map_cons, List.prod_cons, pN_zero X J i0 v h0, one_mul] at this
    · unfold Sys.Tt
      rw [if_neg h0]
      show a • ((p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) J (i0 v)) •
        ∑ᶠ (L1 : Submodule ((X.Pj J).W (X.vJ J v)) (Fin ((X.Pj J).m + 1) → (X.Pj J).Qq (X.vJ J v)))
          (_ : IsEdge p ((X.Pj J).n' (X.vJ J v)) (i0 v) ⟨L1, Lc (X.vJ J v)⟩),
          TtL X J i0 vs F c' (Function.update Lc (X.vJ J v) L1)) ∈ T
      rw [smul_smul]
      refine finsum_induction (fun x => (a * (p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) J (i0 v))) • x ∈ T)
        (by rw [smul_zero]; exact T.zero_mem) (fun x y hx hy => by rw [smul_add]; exact T.add_mem hx hy) ?_
      intro L1
      refine finsum_induction (fun x => (a * (p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) J (i0 v))) • x ∈ T)
        (by rw [smul_zero]; exact T.zero_mem) (fun x y hx hy => by rw [smul_add]; exact T.add_mem hx hy) ?_
      intro hE
      apply ih hnd'
      intro L'' hrel
      have := H L'' ?_
      · rwa [List.map_cons, List.prod_cons, ← mul_assoc] at this
      · intro v'
        by_cases hv' : v' = X.vJ J v
        · subst hv'
          right
          have h1 := hrel (X.vJ J v)
          simp only [vB_vJ, if_neg hv] at h1
          rcases h1 with ⟨_, h1⟩ | ⟨h1, _⟩
          · simp only [vB_vJ, List.mem_cons, true_or, if_true]
            refine ⟨Nat.one_le_iff_ne_zero.mpr h0, ?_⟩
            have e1 : Function.update (β := fun a => Submodule ((X.Pj J).W a) (Fin ((X.Pj J).m + 1) → (X.Pj J).Qq a))
                Lc (X.vJ J v) L1 (X.vJ J v) = L1 := Function.update_self _ _ _
            have h1' : L'' (X.vJ J v) = L1 := h1.trans e1
            rw [h1']
            exact hE
          · omega
        · have hne : X.vB J v' ≠ v := by
            intro h
            apply hv'
            rw [← h, vJ_vB]
          have e2 : Function.update (β := fun a => Submodule ((X.Pj J).W a) (Fin ((X.Pj J).m + 1) → (X.Pj J).Qq a))
              Lc (X.vJ J v) L1 v' = Lc v' := Function.update_of_ne hv' _ _
          have hval : (if X.vB J v' ∈ v :: vs then i0 (X.vB J v') else 0) =
              (if X.vB J v' ∈ vs then i0 (X.vB J v') else 0) := by
            simp only [List.mem_cons, hne, false_or]
          show (if X.vB J v' ∈ v :: vs then i0 (X.vB J v') else 0) = 0 ∧ L'' v' = Lc v' ∨
            1 ≤ (if X.vB J v' ∈ v :: vs then i0 (X.vB J v') else 0) ∧
              IsEdge p ((X.Pj J).n' v') (if X.vB J v' ∈ v :: vs then i0 (X.vB J v') else 0) ⟨L'' v', Lc v'⟩
          rw [hval]
          rcases hrel v' with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · exact Or.inl ⟨ha, hb.trans e2⟩
          · exact Or.inr ⟨ha, (congrArg (fun Z => IsEdge p ((X.Pj J).n' v')
              (if X.vB J v' ∈ vs then i0 (X.vB J v') else 0) ⟨L'' v', Z⟩) e2).mp hb⟩

variable {X}

theorem map_smulK (Y : Pend X) {σ : Type*} (a : X.G.Kf) (x : MvPolynomial σ X.G.Kf) :
    MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (a • x) = a • MvPolynomial.map (algebraMap X.G.Kf Y.Kc) x := by
  ext m
  simp [MvPolynomial.coeff_map, MvPolynomial.coeff_smul, Algebra.smul_def, map_mul]

def KSum (Y : Pend X) (j : ℕ) (cK : Y.Kc) (Cl Yb : Type) [Fintype Cl] [Fintype Yb] (wt : Cl → ℕ)
    (La : Cl → Yb → X.Lt j) : Prop :=
  (∀ x y, (X.Pj j).IsLatTup (La x y).2) ∧ (∀ x, 0 < wt x ∧ padicValNat p (wt x) ≤ X.dG j) ∧
  ∀ F ∈ X.FQ j, ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
    MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' L') =
      ∑ x : Cl, (((wt x : Y.Kc))⁻¹ * cK) • ∑ y : Yb, Y.ker j (La x y) (c', L') (F (La x y).1 (La x y).2)

theorem ksum_entry (Y : Pend X) {j : ℕ} (hj : j ≤ X.mm) {cK : Y.Kc}
    (h4 : ∀ F ∈ X.FQ j, ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' L') =
        ∑ La ∈ Y.Rep j, (((X.stab j La : Y.Kc))⁻¹ * cK) • Y.ker j La (c', L') (F La.1 La.2)) :
    KSum Y j cK {La // La ∈ Y.Rep j} Unit (fun x => X.stab j x.1) (fun x _ => x.1) := by
  refine ⟨fun x _ => Y.Rep_lat j x.1 x.2, fun x => ⟨Y.stab_fin j hj x.1 (Y.Rep_lat j x.1 x.2),
    X.dG_spec j hj x.1.1 x.1.2 (Y.Rep_lat j x.1 x.2)⟩, fun F hF c' L' hL' => ?_⟩
  rw [h4 F hF c' L' hL']
  simp only [Finset.univ_unique, Finset.sum_singleton]
  exact (Finset.sum_coe_sort (Y.Rep j)
    (fun La => (((X.stab j La : Y.Kc))⁻¹ * cK) • Y.ker j La (c', L') (F La.1 La.2))).symm

theorem kernel_sum_of_class_data (D : Formalism.BasicNotions.D7) (Y : Pend X) (h4 : ArchimedeanSignatureMatching D X Y) {j : ℕ} (hj : j < X.mm) :
    ∃ cK : Y.Kc, cK ∈ Y.Oc ∧ ∃ (Cl Yb : Type) (_ : Fintype Cl) (_ : Fintype Yb) (wt : Cl → ℕ) (La : Cl → Yb → X.Lt j),
      KSum Y j cK Cl Yb wt La := by
  rcases Nat.lt_or_ge (j + 1) X.mm with h | h
  · obtain ⟨cK, hcK, _, h4'⟩ := h4.1 j h
    exact ⟨cK, hcK, _, _, inferInstance, inferInstance, _, _, ksum_entry Y hj.le h4'⟩
  · obtain ⟨cK, hcK, _, Cl, Yb, iC, iY, wt, La, h1, h2, h3, _⟩ := h4.2 j (by omega)
    exact ⟨cK, hcK, Cl, Yb, iC, iY, wt, La, h1, h2, h3⟩

theorem entry_mem (D : Formalism.BasicNotions.D7) (Y : Pend X) (hA : admitted D X Y) {j : ℕ} (hj : j < X.mm) (i0 : X.Pl → ℕ) (g : ℝ)
    (hi0 : ∀ v, i0 v ≤ X.G.P.r) (hE : EntB X Y j i0 g) (G : X.Fm j) (hG : G ∈ X.Int j) (c' : X.Lv.comp (j + 1))
    (L' L'' : (X.Pj (j + 1)).Tup) (hL' : (X.Pj (j + 1)).IsLatTup L') (hrel : ERel X (j + 1) i0 L'' L') :
    (∏ v : X.Pl, pN X (j + 1) i0 v) • X.Kz j G c' L'' ∈
      scale (X.vsc (g - X.dG j)) ((X.Pj (j + 1)).HtupW L') := by
  obtain ⟨_, _, _, _, _, _, h4, _, _, _, h7, _, _⟩ := hA
  apply descent Y
  have hL'' : (X.Pj (j + 1)).IsLatTup L'' := fun v' =>
    (hrel v').elim (fun h => h.2 ▸ hL' v') (fun h => h.2.1)
  obtain ⟨cK, hcK, Cl, Yb, iC, iY, wt, La, hlat, hwt, h4'⟩ := kernel_sum_of_class_data D Y h4 hj
  have e := h4' G (Submodule.subset_span hG) c' L'' hL''
  rw [map_smulK, e, Finset.smul_sum]
  apply inLatC_sum
  intro x _
  rw [smul_comm]
  have hb : (((wt x : Y.Kc))⁻¹ * cK) * (p : Y.Kc) ^ ((X.dG j : ℕ) : ℤ) ∈ Y.Oc := by
    have := Y.Oc.mul_mem (wt_inv Y (wt x) (X.dG j) (hwt x).1 (hwt x).2) hcK
    convert this using 1
    ring
  have hy : Y.inLatC (j + 1) g L' ((∏ v : X.Pl, pN X (j + 1) i0 v) •
      ∑ y : Yb, Y.ker j (La x y) (c', L'') (G (La x y).1 (La x y).2)) := by
    rw [Finset.smul_sum]
    apply inLatC_sum
    intro y _
    have hLaL := hlat x y
    obtain ⟨φ, hφ⟩ := h7 j hj (La x y) c' L' L'' i0 hLaL hL' hi0 hrel
    have h7' := hφ (X.ThZA Y.Kc j (Y.ThA j (La x y) (c', L'') φ)) g
      (fun I n => hE (La x y) (c', L'') hLaL hL'' φ I n)
      (G (La x y).1 (La x y).2) (((mem_Int_iff X j G).mp hG).1 (La x y).1 (La x y).2 hLaL)
    rw [← Y.ThF_frm] at h7'
    exact h7'
  have := inLatC_smulC Y _ _ hb hy
  rw [Int.cast_natCast] at this
  exact this

def RestTmEquiv (X : Sys p) : Prop :=
  ∀ (J : ℕ) (v : X.Pl) (i : ℕ) (F : X.Fm J), Eqv X J F → Eqv X J (X.Tm v i J F)

theorem Eqv_TtL (hR : RestTmEquiv X) (J : ℕ) (i0 : X.Pl → ℕ) (F : X.Fm J) (hF : Eqv X J F) (vs : List X.Pl) :
    Eqv X J (TtL X J i0 vs F) := by
  induction vs with
  | nil => simpa [TtL] using hF
  | cons v vs ih =>
    show Eqv X J (X.Tt v (i0 v) J (TtL X J i0 vs F))
    unfold Sys.Tt
    split_ifs
    · exact ih
    · exact Eqv_smul X _ (hR J v (i0 v) _ ih)

theorem formB_of (D : Formalism.BasicNotions.D7) (Y : Pend X) (hA : admitted D X Y) (hR : RestTmEquiv X) : FormB X Y := by
  intro j hj i0 vs g hnd hi0 hoff hE G hG
  have h3b : adm3b D X := hA.2.2.2.2.2.1
  have hFQ := h3b j hj G (Submodule.subset_span hG)
  apply vGe_of Y (Eqv_TtL hR (j + 1) i0 _ (Eqv_of_FQ X hFQ) vs)
  intro c' L' hL'
  have hfun : (fun v => if v ∈ vs then i0 v else 0) = i0 := by
    funext v
    by_cases hv : v ∈ vs
    · simp [hv]
    · simp [hv, hoff v hv]
  have hprod : (vs.map (pN X (j + 1) i0)).prod = ∏ v : X.Pl, pN X (j + 1) i0 v := by
    rw [← List.prod_toFinset _ hnd]
    apply Finset.prod_subset (Finset.subset_univ _)
    intro v _ hv
    exact pN_zero X (j + 1) i0 v (hoff v (by simpa using hv))
  have := TtL_mem X (j + 1) i0 c' (scale (X.vsc (g - X.dG j)) ((X.Pj (j + 1)).HtupW L')) (X.Kz j G) vs hnd 1 L'
    (by
      intro L'' hrel
      rw [hfun] at hrel
      rw [one_mul, hprod]
      exact entry_mem D Y hA hj i0 g hi0 hE G hG c' L' L'' hL' hrel)
  rwa [one_smul] at this

end Formalism.MainNotions.FormalGroupSystem.Pf
