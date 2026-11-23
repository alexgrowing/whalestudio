import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.ActsByFrameAct

noncomputable section

open scoped Classical

namespace PI.NRL

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem Xflag_mono (F : LFlag S r T) (j : ℕ) : Xflag F j ≤ Xflag F (j + 1) := by
  show Submodule.span E (F.fl.e '' {i | i.1 < j}) ≤ Submodule.span E (F.fl.e '' {i | i.1 < j + 1})
  exact Submodule.span_mono (Set.image_mono fun i hi => by
    simp only [Set.mem_setOf_eq] at hi ⊢
    omega)

theorem Xflag_le (F : LFlag S r T) (j : ℕ) : Xflag F j ≤ Xsp F := by
  show Submodule.span E (F.fl.e '' {i | i.1 < j}) ≤ Submodule.span E (Set.range F.fl.e)
  exact Submodule.span_mono (Set.image_subset_range _ _)

theorem X_le_orth (F : LFlag S r T) : Xsp F ≤ orth S (Xsp F) := by
  intro x hx
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro y hy
  refine span_zero (φ := S.hT y) (fun z hz => ?_) hx
  obtain ⟨i, rfl⟩ := hz
  rw [herm_eq, span_zero (φ := S.hT (F.fl.e i)) (fun z hz => by
    obtain ⟨k, rfl⟩ := hz
    exact F.fl.e_iso i k) hy, star_zero]

theorem NLam_mul (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) {n₁ n₂ : S.V ≃ₗ[E] S.V}
    (h₁ : n₁ ∈ NLam Λ F) (h₂ : n₂ ∈ NLam Λ F) : n₁ * n₂ ∈ NLam Λ F := by
  simp only [NLam, IsAutLam, Set.mem_setOf_eq] at h₁ h₂ ⊢
  obtain ⟨⟨hi₁, hg₁⟩, hf₁, ho₁⟩ := h₁
  obtain ⟨⟨hi₂, hg₂⟩, hf₂, ho₂⟩ := h₂
  refine ⟨⟨Subgroup.mul_mem _ hi₁ hi₂, ?_⟩, ?_, ?_⟩
  · rw [gmap_eq_iff] at hg₁ hg₂ ⊢
    refine ⟨fun y hy => hg₁.1 _ (hg₂.1 y hy), fun y hy => ?_⟩
    obtain ⟨w₁, hw₁, rfl⟩ := hg₁.2 y hy
    obtain ⟨w₂, hw₂, rfl⟩ := hg₂.2 w₁ hw₁
    exact ⟨w₂, hw₂, rfl⟩
  · intro j x hx
    have h2 := hf₂ j x hx
    have hmem : n₂ x ∈ Xflag F (j + 1) := by
      have h3 := Submodule.add_mem _ (Xflag_mono F j h2) hx
      rwa [sub_add_cancel] at h3
    have h1 := hf₁ j (n₂ x) hmem
    have h4 := Submodule.add_mem _ h1 h2
    rw [sub_add_sub_cancel] at h4
    exact h4
  · intro x hx
    have h2 := ho₂ x hx
    have hmem : n₂ x ∈ orth S (Xsp F) := by
      have h3 := Submodule.add_mem _ (X_le_orth F h2) hx
      rwa [sub_add_cancel] at h3
    have h1 := ho₁ (n₂ x) hmem
    have h4 := Submodule.add_mem _ h1 h2
    rw [sub_add_sub_cancel] at h4
    exact h4

theorem modG_of_mem (Λ : Submodule (𝓞 E) S.V) (g : ℕ) {x : S.V}
    (hx : x ∈ Ideal.span {(g : 𝓞 E)} • Λ) : ModG S Λ g x := by
  intro P hP
  haveI := P.isPrime
  show ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ Ideal.span {(g : 𝓞 E)} • Λ
  exact ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩

theorem modG_add (Λ : Submodule (𝓞 E) S.V) (g : ℕ) {x y : S.V} (hx : ModG S Λ g x) (hy : ModG S Λ g y) :
    ModG S Λ g (x + y) := by
  intro P hP
  exact Submodule.add_mem _ (hx P hP) (hy P hP)

theorem modG_map (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (n : S.V ≃ₗ[E] S.V) (hn : Formalism.HermitianLatticesTheory.gmap n Λ = Λ)
    {x : S.V} (hx : ModG S Λ g x) : ModG S Λ g (n x) := by
  intro P hP
  have hx' := hx P hP
  haveI := P.isPrime
  obtain ⟨s, hs, hsx⟩ : ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ Ideal.span {(g : 𝓞 E)} • Λ := hx'
  show ∃ s ∈ P.asIdeal.primeCompl, s • n x ∈ Ideal.span {(g : 𝓞 E)} • Λ
  refine ⟨s, hs, ?_⟩
  have hmap : (Ideal.span {(g : 𝓞 E)} • Λ).map ((n : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)) =
      Ideal.span {(g : 𝓞 E)} • Λ := by
    rw [Submodule.map_smul'']
    unfold Formalism.HermitianLatticesTheory.gmap at hn
    rw [hn]
  have hmem := Submodule.mem_map_of_mem (f := (n : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)) hsx
  rw [hmap] at hmem
  have he : ((n : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)) (s • x) = s • n x :=
    map_smul ((n : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)) s x
  rw [he] at hmem
  exact hmem

theorem frameAct_mem (Λ : Submodule (𝓞 E) S.V) {n : ℕ} (f : Fin n → S.V) (hf : ∀ c, f c ∈ Λ)
    (Q : Matrix (Fin n) (Fin n) (𝓞 E)) (b : Fin n) : frameAct f Q b ∈ Λ := by
  unfold frameAct
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [smul_coe]
  exact Λ.smul_mem _ (hf a)

theorem frameAct_one_add {n : ℕ} (f : Fin n → S.V) (g : 𝓞 E) (Q : Matrix (Fin n) (Fin n) (𝓞 E)) (b : Fin n) :
    frameAct f (1 + g • Q) b = f b + g • frameAct f Q b := by
  have h1 := frameAct_one f b
  unfold frameAct at h1 ⊢
  simp only [smul_coe] at h1 ⊢
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib, h1,
    mul_smul, Finset.smul_sum]

theorem exists_undo (Λ : Submodule (𝓞 E) S.V) (hint : IntLat Λ) (F : LFlag S r T) (g : 𝓞 E)
    (hrow : ∀ (a : Fin r) (t : Fin (r + 1) → 𝓞 E), ∃ v ∈ Λ, ∃ l : 𝓞 E,
      (l : E) + star (l : E) = -S.hT v v ∧ (∀ i, i ≤ a → S.hT v (F.fl.e i) = 0) ∧
      ∀ c, Fin.castSucc a < c → ∃ q : 𝓞 E, S.hT v (frame F c) = ((t c + g * q : 𝓞 E) : E))
    (hfe : ∀ a, F.fl.e a ∈ Λ)
    (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) (hξ : UniUp ξ) :
    ∃ n ∈ NLam Λ F, ∃ M, ActsBy n (frame F) M ∧ ∃ Q, M * ξ = 1 + g • Q := by
  have hone : (1 : S.V ≃ₗ[E] S.V) ∈ NLam Λ F := by
    simp only [NLam, IsAutLam, Set.mem_setOf_eq]
    refine ⟨⟨Subgroup.one_mem _, ?_⟩, fun j x _ => ?_, fun x _ => ?_⟩
    · rw [gmap_eq_iff]
      exact ⟨fun y hy => hy, fun y hy => ⟨y, hy, rfl⟩⟩
    · show x - x ∈ _
      rw [sub_self]
      exact Submodule.zero_mem _
    · show x - x ∈ _
      rw [sub_self]
      exact Submodule.zero_mem _
  have hrow' : ∀ a : Fin (r + 1), a.val < r → ∀ t : Fin (r + 1) → 𝓞 E, ∃ w : Fin (r + 1) → 𝓞 E,
      (∀ c, c ≤ a → w c = 0) ∧ (∀ c, a < c → ∃ q, w c = t c + g * q) ∧
      (∃ n ∈ NLam Λ F, ActsBy n (frame F) (1 + rowMat a w)) := by
    intro a ha t
    obtain ⟨v, hv, l, hl, hperp, hcong⟩ := hrow ⟨a.val, ha⟩ t
    have hca : Fin.castSucc (⟨a.val, ha⟩ : Fin r) = a := Fin.ext rfl
    rw [hca] at hcong
    choose q hq using hcong
    let w : Fin (r + 1) → 𝓞 E := fun c => if h : a < c then t c + g * q c h else 0
    have hee : S.hT (F.fl.e ⟨a.val, ha⟩) (F.fl.e ⟨a.val, ha⟩) = 0 := F.fl.e_iso _ _
    have hve : S.hT v (F.fl.e ⟨a.val, ha⟩) = 0 := hperp _ le_rfl
    have hev : S.hT (F.fl.e ⟨a.val, ha⟩) v = 0 := by rw [herm_eq, hve, star_zero]
    have hw : ∀ c, S.hT v (frame F c) = (w c : E) := by
      intro c
      by_cases hc : a < c
      · simp only [w, dif_pos hc]
        exact hq c hc
      · simp only [w, dif_neg hc]
        have hcr : c.val < r := by
          have h' : ¬ a.val < c.val := fun h => hc (Fin.lt_def.mpr h)
          omega
        obtain ⟨c', rfl⟩ : ∃ c' : Fin r, Fin.castSucc c' = c := ⟨⟨c.val, hcr⟩, Fin.ext rfl⟩
        have hfc : frame F (Fin.castSucc c') = F.fl.e c' := by
          show Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z (Fin.castSucc c') = F.fl.e c'
          exact Fin.snoc_castSucc ..
        have hle : c' ≤ (⟨a.val, ha⟩ : Fin r) := by
          have h' : ¬ a.val < c'.val := fun h => hc (Fin.lt_def.mpr (by simpa using h))
          exact Fin.le_def.mpr (by simp only; omega)
        rw [hfc, hperp c' hle]
        simp
    refine ⟨w, fun c hc => ?_, fun c hc => ⟨q c hc, by simp only [w, dif_pos hc]⟩, ?_⟩
    · have hnc : ¬ a < c := not_lt.mpr hc
      simp only [w, dif_neg hnc]
    · refine ⟨tvEquiv (F.fl.e ⟨a.val, ha⟩) v (l : E) hee hev hve,
        tv_mem_NLam Λ hint F ⟨a.val, ha⟩ (hfe _) v hv hperp l hl hee hev hve, ?_⟩
      have hact := tv_actsBy F ⟨a.val, ha⟩ v (l : E) hee hev hve w hw
      rw [hca] at hact
      exact hact
  obtain ⟨M, ⟨n, hn, hact⟩, Q, hQ⟩ := row_elim g (fun M => ∃ n ∈ NLam Λ F, ActsBy n (frame F) M)
    ⟨1, hone, actsBy_one _⟩
    (fun M N hM hN => by
      obtain ⟨n₁, h₁, a₁⟩ := hM
      obtain ⟨n₂, h₂, a₂⟩ := hN
      exact ⟨n₁ * n₂, NLam_mul Λ F h₁ h₂, actsBy_mul a₁ a₂⟩)
    hrow' ξ hξ
  exact ⟨n, hn, M, hact, Q, hQ⟩

end PI.NRL
