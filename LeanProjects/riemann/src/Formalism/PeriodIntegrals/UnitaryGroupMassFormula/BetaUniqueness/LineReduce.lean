import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Skeleton
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Lemmas

noncomputable section

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.UnitaryGroupMassFormula.BetaLUniq

def LineReduce' : Prop :=
  ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (Λ : Submodule (𝓞 E) S.V) {r : ℕ} {T T' : E} (F : LFlag S r T) (F' F'' : LFlag S r T')
    (β₁ β₂ : S.V ≃ₗ[E] S.V) (k : ℕ), finrank E S.V = k + 2 * r + 1 →
    Submodule.IsLattice E Λ → IsLift Λ F' →
    (finrank E (UUE Λ F F') = 2 * r + 2 ∧ UUE Λ F F' ⊓ orth S (UUE Λ F F') = ⊥) →
    (∀ w ∈ orth S (Xplus F'), S.hT w w = 0 → w ∈ Xsp F') →
    β₁ ∈ Formalism.HermitianLatticesTheory.isom S.hT → β₂ ∈ Formalism.HermitianLatticesTheory.isom S.hT →
    (∀ j, (Xflag F' j).map (β₁ : S.V →ₗ[E] S.V) = Xflag F'' j) →
    (∀ j, (Xflag F' j).map (β₂ : S.V →ₗ[E] S.V) = Xflag F'' j) →
    β₁ F'.fl.z = F''.fl.z → β₂ F'.fl.z = F''.fl.z →
    (∀ x ∈ Hp Λ F F', β₂ x - β₁ x ∈ Xsp F'') →
    EigenOne Λ F F' β₁ β₂ →
      ∀ x ∈ orth S (Xsp F'), β₂ x - β₁ x ∈ Xsp F''

namespace LR

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem hT_comm {x y : S.V} : S.hT x y = 0 ↔ S.hT y x = 0 := S.herm.eq_iff

theorem orth_anti {U U' : Submodule E S.V} (h : U ≤ U') : orth S U' ≤ orth S U := by
  intro v hv
  rw [mem_orth] at hv ⊢
  exact fun x hx => hv x (h hx)

theorem mem_orth_sup {U U' : Submodule E S.V} {v : S.V} :
    v ∈ orth S (U ⊔ U') ↔ v ∈ orth S U ∧ v ∈ orth S U' := by
  constructor
  · intro h; exact ⟨orth_anti le_sup_left h, orth_anti le_sup_right h⟩
  · rintro ⟨h1, h2⟩
    rw [mem_orth] at h1 h2 ⊢
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, LinearMap.add_apply, h1 a ha, h2 b hb, add_zero]

theorem mem_orth_span {s : Set S.V} {v : S.V} :
    v ∈ orth S (Submodule.span E s) ↔ ∀ x ∈ s, S.hT x v = 0 := by
  rw [mem_orth]
  refine ⟨fun h x hx => h x (Submodule.subset_span hx), fun h x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hx, smul_zero]

theorem mem_orth_span_singleton {z v : S.V} :
    v ∈ orth S (Submodule.span E {z}) ↔ S.hT z v = 0 := by
  rw [mem_orth_span]; simp

theorem Xsp_le_orth {r : ℕ} {T : E} (F : LFlag S r T) : Xsp F ≤ orth S (Xsp F) := by
  show Submodule.span E (Set.range F.fl.e) ≤ orth S (Submodule.span E (Set.range F.fl.e))
  rw [Submodule.span_le]
  rintro _ ⟨b, rfl⟩
  rw [SetLike.mem_coe, mem_orth_span]
  rintro _ ⟨a, rfl⟩
  exact F.fl.e_iso a b

theorem z_mem_orth {r : ℕ} {T : E} (F : LFlag S r T) : F.fl.z ∈ orth S (Xsp F) := by
  show F.fl.z ∈ orth S (Submodule.span E (Set.range F.fl.e))
  rw [mem_orth_span]
  rintro _ ⟨a, rfl⟩
  exact F.fl.z_orth a

theorem finrank_Xsp {r : ℕ} {T : E} (F : LFlag S r T) : finrank E (Xsp F) = r := by
  show finrank E (Submodule.span E (Set.range F.fl.e)) = r
  rw [finrank_span_eq_card F.fl.e_indep]; simp

theorem Xflag_r {r : ℕ} {T : E} (F : LFlag S r T) : Xflag F r = Xsp F := by
  show Submodule.span E (F.fl.e '' {i | i.1 < r}) = Submodule.span E (Set.range F.fl.e)
  congr 1
  rw [← Set.image_univ]
  congr 1
  ext i
  simp

theorem inf_span_eq_bot {P : Submodule E S.V} {v : S.V} (hv : v ∉ P) :
    P ⊓ Submodule.span E {v} = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy.2
  by_cases hc : c = 0
  · simp [hc]
  · exfalso; apply hv
    have := P.smul_mem c⁻¹ hy.1
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

theorem finrank_sup_span {P : Submodule E S.V} {v : S.V} (hv : v ∉ P) :
    finrank E (P ⊔ Submodule.span E {v} : Submodule E S.V) = finrank E P + 1 := by
  have hv0 : v ≠ 0 := fun h => hv (h ▸ P.zero_mem)
  have := Submodule.finrank_sup_add_finrank_inf_eq P (Submodule.span E {v})
  rw [inf_span_eq_bot hv, finrank_bot, finrank_span_singleton hv0] at this
  omega

theorem isom_apply {β : S.V ≃ₗ[E] S.V} (h : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) (x y : S.V) :
    S.hT (β x) (β y) = S.hT x y := h x y

theorem isom_symm_apply {β : S.V ≃ₗ[E] S.V} (h : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) (x y : S.V) :
    S.hT (β.symm x) (β.symm y) = S.hT x y := by
  rw [← isom_apply h, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end LR

open LR in
theorem line_reduction_holds : LineReduce' := by
  intro E _ _ _ S Λ r T T' F F' F'' β₁ β₂ k hdim hΛ hL hU hW h1 h2 hf1 hf2 hz1 hz2 hH hE
  set X' := Xsp F' with hX'def
  set z' := F'.fl.z with hz'def
  set U := UUE Λ F F' with hUdef
  set H := Hp Λ F F' with hHdef
  have hHU : H = orth S U := rfl

  have hzU : z' ∈ U := by
    have : F'.zt ∈ UU Λ F F' := Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    rw [hL.2] at this
    exact Submodule.subset_span this
  have hXU : X' ≤ U := Xsp_le_UUE' S Λ hΛ F F'
  have hX'r : finrank E X' = r := finrank_Xsp F'
  have hHdim : finrank E H + finrank E U = finrank E S.V := finrank_orth_add S U
  have hX'o : finrank E (orth S X') + finrank E X' = finrank E S.V := finrank_orth_add S X'
  have hHinf : H ⊓ U = ⊥ := by rw [inf_comm, hHU]; exact hU.2

  have hzX : z' ∉ X' := by
    intro hz
    set B : Submodule E S.V := Xsp F ⊔ Submodule.span E {F.zt} ⊔ X'
    have hUU : UU Λ F F' ≤ toO S B := by
      unfold UU
      refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
      · intro x hx
        rw [XLam, Submodule.mem_inf] at hx
        exact (Submodule.mem_sup_left (Submodule.mem_sup_left hx.2) : x ∈ B)
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)) : F.zt ∈ B)
      · intro x hx
        rw [XLam, Submodule.mem_inf] at hx
        exact (Submodule.mem_sup_right hx.2 : x ∈ B)
      · rw [Submodule.span_le, Set.singleton_subset_iff, hL.2]
        exact (Submodule.mem_sup_right hz : z' ∈ B)
    have hUB : U ≤ B := by
      show Submodule.span E (UU Λ F F' : Set S.V) ≤ B
      rw [Submodule.span_le]
      intro x hx
      exact hUU hx
    have hB1 : finrank E B ≤ finrank E (Xsp F ⊔ Submodule.span E {F.zt} : Submodule E S.V) + finrank E X' :=
      Submodule.finrank_add_le_finrank_add_finrank _ _
    have hB2 := Submodule.finrank_add_le_finrank_add_finrank (Xsp F) (Submodule.span E {F.zt})
    have hB3 : finrank E (Submodule.span E {F.zt}) ≤ 1 :=
      (finrank_span_le_card ({F.zt} : Set S.V)).trans (by simp)
    have hB4 := Submodule.finrank_mono hUB
    have hXr := finrank_Xsp F
    have := hU.1
    omega

  set Xp := Xplus F' with hXpdef
  have hXp : Xp = X' ⊔ Submodule.span E {z'} := rfl
  have hXpr : finrank E Xp = r + 1 := by rw [hXp, finrank_sup_span hzX, hX'r]
  have hXpU : Xp ≤ U := sup_le hXU ((Submodule.span_singleton_le_iff_mem _ _).mpr hzU)
  set A := H ⊔ Xp with hAdef
  have hAr : finrank E A = finrank E H + (r + 1) := by
    have := Submodule.finrank_sup_add_finrank_inf_eq H Xp
    have hb : H ⊓ Xp = ⊥ := eq_bot_iff.mpr (hHinf ▸ inf_le_inf_left H hXpU)
    rw [hb, finrank_bot, hXpr] at this
    omega
  have hAo : finrank E (orth S A) + finrank E A = finrank E S.V := finrank_orth_add S A
  have hXA : X' ≤ A := le_sup_left.trans le_sup_right

  have hUH : ∀ u ∈ U, ∀ h ∈ H, S.hT h u = 0 := by
    intro u hu h hh
    rw [hHU, mem_orth] at hh
    exact hT_comm.mp (hh u hu)
  have hXorth : ∀ x ∈ X', x ∈ orth S X' := fun x hx => Xsp_le_orth F' hx
  have hzorth : z' ∈ orth S X' := z_mem_orth F'
  have hXinA : ∀ x ∈ X', x ∈ orth S A := by
    intro x hx
    rw [hAdef, mem_orth_sup, hXp, mem_orth_sup, mem_orth_span_singleton, mem_orth]
    refine ⟨fun h hh => hUH x (hXU hx) h hh, hXorth x hx, ?_⟩
    rw [mem_orth] at hzorth
    exact hT_comm.mp (hzorth x hx)

  obtain ⟨v, hv, hvX⟩ : ∃ v ∈ orth S A, v ∉ X' := by
    refine SetLike.not_le_iff_exists.mp fun h => ?_
    have := Submodule.finrank_mono h
    omega
  have hvXp : v ∈ orth S Xp := orth_anti le_sup_right hv
  have hvH : v ∈ orth S H := orth_anti le_sup_left hv
  have hvX' : v ∈ orth S X' := orth_anti hXA hv
  have hvA : v ∉ A := by
    intro h
    have hvv : S.hT v v = 0 := (mem_orth S).mp hv v h
    exact hvX (hW v hvXp hvv)

  have hAv : orth S X' = A ⊔ Submodule.span E {v} := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · refine sup_le (sup_le ?_ (sup_le ?_ ?_)) ?_
      · exact orth_anti hXU
      · exact fun x hx => hXorth x hx
      · exact (Submodule.span_singleton_le_iff_mem _ _).mpr hzorth
      · exact (Submodule.span_singleton_le_iff_mem _ _).mpr hvX'
    · rw [finrank_sup_span hvA]
      omega

  have hAo' : orth S A = X' ⊔ Submodule.span E {v} := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · exact sup_le (fun x hx => hXinA x hx) ((Submodule.span_singleton_le_iff_mem _ _).mpr hv)
    · rw [finrank_sup_span hvX]
      omega

  have hX'' : Xsp F'' = X'.map (β₁ : S.V →ₗ[E] S.V) := by
    rw [← Xflag_r F'', ← hf1 r, Xflag_r F']
  have hX''2 : Xsp F'' = X'.map (β₂ : S.V →ₗ[E] S.V) := by
    rw [← Xflag_r F'', ← hf2 r, Xflag_r F']
  have hγX : ∀ x ∈ X', β₁.symm (β₂ x) ∈ X' := by
    intro x hx
    have : β₂ x ∈ Xsp F'' := by rw [hX''2]; exact Submodule.mem_map_of_mem hx
    rw [hX''] at this
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp this
    rw [← hyx]; simpa using hy
  have hγiX : ∀ x ∈ X', β₂.symm (β₁ x) ∈ X' := by
    intro x hx
    have : β₁ x ∈ Xsp F'' := by rw [hX'']; exact Submodule.mem_map_of_mem hx
    rw [hX''2] at this
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp this
    rw [← hyx]; simpa using hy
  have hγ : ∀ x y, S.hT (β₁.symm (β₂ x)) (β₁.symm (β₂ y)) = S.hT x y := by
    intro x y; rw [isom_symm_apply h1, isom_apply h2]
  have hinv : ∀ x, β₁.symm (β₂ (β₂.symm (β₁ x))) = x := by intro x; simp
  have hHW : ∀ h ∈ H, β₁.symm (β₂ h) - h ∈ X' := by
    intro h hh
    have := hH h hh
    rw [hX''] at this
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp this
    have : y = β₁.symm (β₂ h) - h := by
      have := congrArg β₁.symm hyx
      simpa [map_sub] using this
    rw [← this]; exact hy

  set w := β₁.symm (β₂ v) with hwdef
  have hw : w ∈ orth S A := by
    rw [hAdef, mem_orth_sup, hXp, mem_orth_sup, mem_orth_span_singleton, mem_orth, mem_orth]
    refine ⟨?_, ?_, ?_⟩
    · intro h hh
      rw [← hinv h, hγ]
      have key : β₂.symm (β₁ h) = h - β₂.symm (β₁ (β₁.symm (β₂ h) - h)) := by
        simp [map_sub]
      rw [key, map_sub, LinearMap.sub_apply, (mem_orth S).mp hvH h hh,
        (mem_orth S).mp hvX' _ (hγiX _ (hHW h hh)), sub_zero]
    · intro x hx
      rw [← hinv x, hγ]
      exact (mem_orth S).mp hvX' _ (hγiX x hx)
    · have hγz : β₁.symm (β₂ z') = z' := by
        rw [hz2, ← hz1, LinearEquiv.symm_apply_apply]
      rw [← hγz, hγ]
      rw [hXp, mem_orth_sup, mem_orth_span_singleton] at hvXp
      exact hvXp.2
  rw [hAo'] at hw
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hw
  obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hb
  have hμ : μ = 1 := by
    refine hE v hvXp hvX (fun h hh => (mem_orth S).mp hvH h hh) μ ?_
    rw [← hwdef, ← hab, add_sub_cancel_right]; exact ha
  have hvW : β₁.symm (β₂ v) - v ∈ X' := by
    rw [← hwdef, ← hab, hμ, one_smul, add_sub_cancel_right]; exact ha

  let Wd : Submodule E S.V := X'.comap
    (((β₁.symm : S.V →ₗ[E] S.V) ∘ₗ (β₂ : S.V →ₗ[E] S.V)) - LinearMap.id)
  have hWmem : ∀ x, x ∈ Wd ↔ β₁.symm (β₂ x) - x ∈ X' := by
    intro x; simp [Wd]
  have hle : orth S X' ≤ Wd := by
    rw [hAv]
    refine sup_le (sup_le ?_ (sup_le ?_ ?_)) ?_
    · intro h hh; rw [hWmem]; exact hHW h hh
    · intro x hx; rw [hWmem]; exact X'.sub_mem (hγX x hx) hx
    · rw [Submodule.span_singleton_le_iff_mem, hWmem, hz2, ← hz1, LinearEquiv.symm_apply_apply, sub_self]
      exact X'.zero_mem
    · rw [Submodule.span_singleton_le_iff_mem, hWmem]; exact hvW
  intro x hx
  have hx' := (hWmem x).mp (hle hx)
  rw [hX'']
  refine Submodule.mem_map.mpr ⟨_, hx', ?_⟩
  simp [map_sub]

section D7

open PI.BetaLUniq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem betaLUniq_of' (h1 : GramNondeg) (h2 : AgreeOnH) (h3 : WAniso) (h4 : LineReduce')
    (h5 : EigenvalueLastLineOne) : PI.BetaLUniq := by
  intro D u u' Λ F F' F'' β₁ β₂ hF hT' hT'' hG' hG'' hP1 hP2 hs1 hs2
  have hdim := finrank_hS D
  have n' := h1 (hS D) Λ F F' hF.1 hF.2.2.1 hT'.1 hT'.2.2
  have n'' := h1 (hS D) Λ F F'' hF.1 hF.2.2.1 hT''.1 hT''.2.2
  have hH := h2 (hS D) Λ F F' F'' β₁ β₂ D.R.k hF.1 hF.2.2.1 hT''.1 hdim n' n'' hs1 hs2
  exact h4 (hS D) Λ F F' F'' β₁ β₂ D.R.k hdim hF.1 hT'.1 n' (h3 D u' F') hP1.1.1 hP2.1.1 hP1.2.1
    hP2.2.1 hP1.2.2.1 hP2.2.2.1 hH (h5 D u u' Λ F F' F'' β₁ β₂ hF hT' hT'' hG' hG'' hP1 hP2 hs1 hs2)

theorem betaLUniq_of'' (h1 : GramNondeg) (h2 : AgreeOnH) (h3 : WAniso) (h5 : EigenvalueLastLineOne) :
    PI.BetaLUniq := betaLUniq_of' h1 h2 h3 line_reduction_holds h5

end D7

end PI.UnitaryGroupMassFormula.BetaLUniq
