import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermitianJmBracket
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsKFinDRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorsModerateGrowthSmoothFrechetRepStatement

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

section SlopeTestRemainingChoices

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem cwb_val_mem (l : List (lie (Jm ε))) : ∀ X ∈ l.map Subtype.val, X ∈ lieSet ε := by
  intro X hX
  obtain ⟨Y, -, rfl⟩ := List.mem_map.1 hX
  exact Y.2

theorem cwb_isKFin_Dw (h : Std ε σ) {v : H} (hv : IsKFin ε σ v) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) :
    IsKFin ε σ (Dw σ l v) := by
  induction l with
  | nil => exact hv
  | cons X l ih =>
    have hl' : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => hl Y (List.mem_cons_of_mem X hY)
    exact isKFin_dRep n ε H σ h _ (ih hl') X (hl X (by simp))

theorem cwb_dRep_lin (h : Std ε σ) {w : H} (hw : Sm ε σ w) (a : ℝ) {X Y : Mx n} (hX : X ∈ lieSet ε)
    (hY : Y ∈ lieSet ε) : dRep σ (a • X + Y) w = (a : ℂ) • dRep σ X w + dRep σ Y w := by
  have hG : IsUnit (Formalism.REAL.Jm ε) := GlobalTheory.SmVec.gram_unit (ε := ε) (P := 1) isUnit_one (by simp)
  have hh : (Formalism.REAL.Jm ε).IsHermitian := GlobalTheory.SmVec.gram_herm (ε := ε) (P := 1) (by simp)
  have hd : (Formalism.REAL.Jm ε).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hG).ne_zero
  exact GlobalTheory.HolDict.LieAct.dRep_lin hh hd h.1 hw a hX hY

theorem cwb_Dw_sub (h : Std ε σ) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) {x y : H} (hx : Sm ε σ x)
    (hy : Sm ε σ y) : Dw σ l x - Dw σ l y = Dw σ l (x - y) := by
  have hG : IsUnit (Formalism.REAL.Jm ε) := GlobalTheory.SmVec.gram_unit (ε := ε) (P := 1) isUnit_one (by simp)
  have hxy : x - y ∈ GlobalTheory.SmVec.smSub (Formalism.REAL.Jm ε) σ := Submodule.sub_mem _ hx hy
  have e := GlobalTheory.SmVec.word_add hG h.1 hl hy hxy
  have e' : Dw σ l x = GlobalTheory.SmVec.word σ l (y + (x - y)) := by rw [add_sub_cancel]; rfl
  rw [e', e]
  change GlobalTheory.SmVec.word σ l y + GlobalTheory.SmVec.word σ l (x - y) - GlobalTheory.SmVec.word σ l y = GlobalTheory.SmVec.word σ l (x - y)
  abel

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ρ : Mx n → (E →L[ℂ] E)}

theorem cwb_mem_Fam (h : Std ε σ) {T₀ : H →ₗ[ℂ] E}
    (hd : ∀ X ∈ lieSet ε, ∀ v, IsKFin ε σ v →
      HasDerivAt (fun t : ℝ => ρ (NormedSpace.exp (t • X)) (T₀ v)) (T₀ (dRep σ X v)) 0)
    {v : H} (hv : IsKFin ε σ v) : (fun l : List (lie (Jm ε)) => T₀ (Dw σ (l.map Subtype.val) v)) ∈ Fam ε ρ := by
  have hG : IsUnit (Formalism.REAL.Jm ε) := GlobalTheory.SmVec.gram_unit (ε := ε) (P := 1) isUnit_one (by simp)
  have happ : ∀ (L₁ L₂ : List (Mx n)) (x : H), Dw σ (L₁ ++ L₂) x = Dw σ L₁ (Dw σ L₂ x) :=
    fun L₁ L₂ x => GlobalTheory.SmVec.word_append (π := σ) L₁ L₂ x
  have hcons : ∀ (Z : Mx n) (L : List (Mx n)) (x : H), Dw σ (Z :: L) x = dRep σ Z (Dw σ L x) :=
    fun _ _ _ => rfl
  have hK : ∀ l : List (lie (Jm ε)), IsKFin ε σ (Dw σ (l.map Subtype.val) v) :=
    fun l => cwb_isKFin_Dw h hv (cwb_val_mem l)
  have hS : ∀ l : List (lie (Jm ε)), Sm ε σ (Dw σ (l.map Subtype.val) v) :=
    fun l => h.2.2.1 _ (hK l)
  have hmem : ∀ X : lie (Jm ε), (X : Mx n) ∈ lieSet ε := fun X => cwb_val_mem [X] _ (by simp)
  unfold Fam
  refine ⟨?_, ?_, ?_⟩
  · intro l X
    exact hd X (hmem X) _ (hK l)
  · intro l₁ l₂ a X Y
    have hc : ((a • X + Y : lie (Jm ε)) : Mx n) = a • (X : Mx n) + (Y : Mx n) := rfl
    simp only [List.map_append, List.map_cons, happ, hcons, hc]
    have hw := hS l₂
    rw [cwb_dRep_lin h hw a (hmem X) (hmem Y)]
    have h1 : dRep σ (X : Mx n) (Dw σ (l₂.map Subtype.val) v) ∈ GlobalTheory.SmVec.smSub (Formalism.REAL.Jm ε) σ :=
      GlobalTheory.SmVec.dRep_mem hG h.1 hw (hmem X)
    have h2 : dRep σ (Y : Mx n) (Dw σ (l₂.map Subtype.val) v) ∈ GlobalTheory.SmVec.smSub (Formalism.REAL.Jm ε) σ :=
      GlobalTheory.SmVec.dRep_mem hG h.1 hw (hmem Y)
    have e1 := GlobalTheory.SmVec.word_add hG h.1 (cwb_val_mem l₁) (Submodule.smul_mem _ (a : ℂ) h1) h2
    have e2 := GlobalTheory.SmVec.word_smul hG h.1 (cwb_val_mem l₁) (a : ℂ) h1
    change T₀ (GlobalTheory.SmVec.word σ _ _) = _ • T₀ (GlobalTheory.SmVec.word σ _ _) + T₀ (GlobalTheory.SmVec.word σ _ _)
    rw [e1, e2, map_add, map_smul]
  · intro l₁ l₂ X Y Z hZ
    simp only [List.map_append, List.map_cons, happ, hcons]
    have hw := hS l₂
    have h1 : dRep σ (X : Mx n) (dRep σ (Y : Mx n) (Dw σ (l₂.map Subtype.val) v)) ∈
        GlobalTheory.SmVec.smSub (Formalism.REAL.Jm ε) σ :=
      GlobalTheory.SmVec.dRep_mem hG h.1 (GlobalTheory.SmVec.dRep_mem hG h.1 hw (hmem Y)) (hmem X)
    have h2 : dRep σ (Y : Mx n) (dRep σ (X : Mx n) (Dw σ (l₂.map Subtype.val) v)) ∈
        GlobalTheory.SmVec.smSub (Formalism.REAL.Jm ε) σ :=
      GlobalTheory.SmVec.dRep_mem hG h.1 (GlobalTheory.SmVec.dRep_mem hG h.1 hw (hmem X)) (hmem Y)
    rw [← map_sub, cwb_Dw_sub h (cwb_val_mem l₁) h1 h2,
      dRep_bracket n ε H σ h _ hw _ (hmem X) _ (hmem Y), ← hZ]

private theorem isKFin_add {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Mx n → (H →L[ℂ] H)} {v w : H} (hv : IsKFin ε σ v) (hw : IsKFin ε σ w) :
    IsKFin ε σ (v + w) := by
  obtain ⟨S, hS, hvS, hSK⟩ := hv
  obtain ⟨S', hS', hwS, hSK'⟩ := hw
  refine ⟨S ⊔ S', ?_, Submodule.add_mem_sup hvS hwS, ?_⟩
  · haveI := hS
    haveI := hS'
    infer_instance
  · unfold IsKStableOn at hSK hSK' ⊢
    intro g hg x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem_sup (hSK g hg y hy) (hSK' g hg z hz)

private theorem isKFin_smul {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Mx n → (H →L[ℂ] H)} (c : ℂ) {v : H} (hv : IsKFin ε σ v) :
    IsKFin ε σ (c • v) := by
  obtain ⟨S, hS, hvS, hSK⟩ := hv
  exact ⟨S, hS, S.smul_mem c hvS, hSK⟩

private theorem isKFin_zero {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Mx n → (H →L[ℂ] H)} : IsKFin ε σ (0 : H) := by
  refine ⟨⊥, inferInstance, Submodule.zero_mem _, ?_⟩
  unfold IsKStableOn
  intro g _ x hx
  rw [Submodule.mem_bot] at hx
  rw [hx, map_zero]
  exact Submodule.zero_mem _

private theorem mem_UJset_of_mem_Kset_iwasawa_decomposition {n : ℕ} {ε : Fin n → Bool} {k : Mx n} (hk : k ∈ Kset ε) : k ∈ UJset ε := by
  obtain ⟨hu, hc⟩ := hk
  have hu' : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hu
  show kᴴ * Jm ε * k = Jm ε
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, show kᴴ * k = 1 from hu', Matrix.one_mul]

private theorem dw_apply_sigma_eq_sigma_dw_conj {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mx n → (H →L[ℂ] H)} (h : Std ε σ) {g : Mx n}
    (hg : g ∈ UJset ε) (l : List (Mx n)) (hl : ∀ X ∈ l, X ∈ lieSet ε) {w : H} (hw : Sm ε σ w) :
    Dw σ l (σ g w) = σ g (Dw σ (l.map fun X => g⁻¹ * X * g) w) := by
  have hG : IsUnit (Formalism.REAL.Jm ε) := GlobalTheory.SmVec.gram_unit (ε := ε) (P := 1) isUnit_one (by simp)
  induction l with
  | nil => rfl
  | cons X l ih =>
    have hl' : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => hl Y (List.mem_cons_of_mem X hY)
    have hX : X ∈ lieSet ε := hl X (by simp)
    change dRep σ X (Dw σ l (σ g w)) =
      σ g (dRep σ (g⁻¹ * X * g) (Dw σ (l.map fun X => g⁻¹ * X * g) w))
    rw [ih hl']
    have hs : Dw σ (l.map fun X => g⁻¹ * X * g) w ∈ GlobalTheory.SmVec.smSub (Formalism.REAL.Jm ε) σ := by
      have hl'' : ∀ Y ∈ l.map (fun X => g⁻¹ * X * g), Y ∈ GlobalTheory.SmVec.lieG (Formalism.REAL.Jm ε) := by
        intro Y hY
        obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hY
        exact GlobalTheory.SmVec.conj_mem_lieG hG hg (hl' Z hZ)
      exact GlobalTheory.SmVec.word_mem hG h.1 hl'' hw
    exact GlobalTheory.SmVec.dRep_rep hG h.1 hs hg hX

end SlopeTestRemainingChoices

theorem casselmanWallach_banach : GlobalTheory.Published.CasselmanWallach → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (ρ : Mx n → (E →L[ℂ] E)), ModRep ε ρ → ∀ T₀ : H →ₗ[ℂ] E, (∀ k ∈ Kset ε, ∀ v, IsKFin ε σ v → T₀ (σ k v) = ρ k (T₀ v)) → (∀ X ∈ lieSet ε, ∀ v, IsKFin ε σ v → HasDerivAt (fun t : ℝ => ρ (NormedSpace.exp (t • X)) (T₀ v)) (T₀ (dRep σ X v)) 0) → ∃ T : H →ₗ[ℂ] E, (∀ v, IsKFin ε σ v → T v = T₀ v) ∧ (∀ g ∈ UJset ε, ∀ w, Sm ε σ w → T (σ g w) = ρ g (T w)) ∧ ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ ∀ w, Sm ε σ w → ‖T w‖ ≤ C * sobNorm σ S w := by
  intro hCW n ε H _ _ _ σ hσ E _ _ _ ρ hρ T₀ hK hd
  unfold GlobalTheory.Published.CasselmanWallach at hCW
  obtain ⟨hcl, p, π, dπ, hsm, hπ, hdπ, hp0⟩ := GlobalTheory.T.smooth_vectors_moderate_growth_smooth_frechet_rep n ε E ρ hρ
  haveI : IsUniformAddGroup (Fam ε ρ) := (Fam ε ρ).toAddSubgroup.isUniformAddGroup
  haveI : CompleteSpace (Fam ε ρ) := hcl.completeSpace_coe
  have hG : IsUnit (Formalism.REAL.Jm ε) := GlobalTheory.SmVec.gram_unit (ε := ε) (P := 1) isUnit_one (by simp)
  have happ : ∀ (L₁ L₂ : List (Mx n)) (x : H), Dw σ (L₁ ++ L₂) x = Dw σ L₁ (Dw σ L₂ x) :=
    fun L₁ L₂ x => GlobalTheory.SmVec.word_append (π := σ) L₁ L₂ x
  have hcons : ∀ (Z : Mx n) (L : List (Mx n)) (x : H), Dw σ (Z :: L) x = dRep σ Z (Dw σ L x) :=
    fun _ _ _ => rfl
  have hnil : ∀ x : H, Dw σ [] x = x := fun _ => rfl
  let KF : Submodule ℂ H :=
    { carrier := {v | IsKFin ε σ v}
      add_mem' := fun ha hb => isKFin_add ha hb
      zero_mem' := isKFin_zero
      smul_mem' := fun c _ hv => isKFin_smul c hv }
  let J : KF →ₗ[ℂ] Fam ε ρ :=
    { toFun := fun v => ⟨fun l => T₀ (Dw σ (l.map Subtype.val) v.1), cwb_mem_Fam hσ hd v.2⟩
      map_add' := fun v w => by
        apply Subtype.ext
        funext l
        have e := GlobalTheory.SmVec.word_add hG hσ.1 (cwb_val_mem l) (hσ.2.2.1 _ v.2) (hσ.2.2.1 _ w.2)
        show T₀ (Dw σ _ (v.1 + w.1)) = T₀ (Dw σ _ v.1) + T₀ (Dw σ _ w.1)
        rw [← map_add]
        exact congrArg T₀ e
      map_smul' := fun c v => by
        apply Subtype.ext
        funext l
        have e := GlobalTheory.SmVec.word_smul hG hσ.1 (cwb_val_mem l) c (hσ.2.2.1 _ v.2)
        show T₀ (Dw σ _ (c • v.1)) = c • T₀ (Dw σ _ v.1)
        rw [← map_smul]
        exact congrArg T₀ e }
  obtain ⟨T₁, hT₁⟩ := LinearMap.exists_extend J
  have hT₁v : ∀ (v : H) (hv : IsKFin ε σ v), T₁ v = J ⟨v, hv⟩ := fun v hv =>
    LinearMap.congr_fun hT₁ ⟨v, hv⟩
  have hJ : ∀ (v : H) (hv : IsKFin ε σ v) (l : List (lie (Jm ε))),
      (J ⟨v, hv⟩).1 l = T₀ (Dw σ (l.map Subtype.val) v) := fun _ _ _ => rfl
  have hGK : IsGKMap ε σ π dπ T₁ := by
    refine ⟨?_, ?_⟩
    · intro k hk v hv
      have hk' : k ∈ UJset ε := mem_UJset_of_mem_Kset_iwasawa_decomposition hk
      have hkv : IsKFin ε σ (σ k v) := by
        obtain ⟨S, hS, hvS, hSK⟩ := hv
        exact ⟨S, hS, hSK k hk v hvS, hSK⟩
      rw [hT₁v _ hkv, hT₁v _ hv]
      apply Subtype.ext
      funext l
      rw [hπ k hk' (J ⟨v, hv⟩) l, hJ, hJ, dw_apply_sigma_eq_sigma_dw_conj hσ hk' _ (cwb_val_mem l) (hσ.2.2.1 _ hv)]
      have hl : (l.map Subtype.val).map (fun X => k⁻¹ * X * k) = (l.map (adInv hk')).map Subtype.val := by
        simp only [List.map_map]
        rfl
      rw [hl, hK k hk _ (cwb_isKFin_Dw hσ hv (cwb_val_mem _))]
    · intro X hX v hv
      have hXv : IsKFin ε σ (dRep σ X v) := isKFin_dRep n ε H σ hσ v hv X hX
      rw [hT₁v _ hXv, hT₁v _ hv]
      apply Subtype.ext
      funext l
      rw [show (dπ X (J ⟨v, hv⟩)).1 l = (J ⟨v, hv⟩).1 (l ++ [⟨X, hX⟩]) from hdπ ⟨X, hX⟩ _ l, hJ, hJ]
      simp only [List.map_append, List.map_cons, List.map_nil, happ, hcons, hnil]
      try rfl
  obtain ⟨T', hT'0, hSG, -⟩ := hCW n ε H σ hσ.1 hσ.2.1 (Fam ε ρ) p π dπ hsm T₁ hGK
  unfold IsSmoothGMap at hSG
  obtain ⟨hTeq, hTbd⟩ := hSG
  refine ⟨(GlobalTheory.TypeSum.SmoothFrechet.ev ρ []).comp T', ?_, ?_, ?_⟩
  · intro v hv
    show (T' v).1 [] = T₀ v
    rw [hT'0 v hv, hT₁v v hv]
    rfl
  · intro g hg w hw
    show (T' (σ g w)).1 [] = ρ g ((T' w).1 [])
    rw [hTeq g hg w hw, hπ g hg (T' w) []]
    rfl
  · obtain ⟨S, C, hS, hSC⟩ := hTbd 0
    exact ⟨S, C, hS, fun w hw => (hp0 (T' w)).trans (hSC w hw)⟩

end GlobalTheory.TypeSum
