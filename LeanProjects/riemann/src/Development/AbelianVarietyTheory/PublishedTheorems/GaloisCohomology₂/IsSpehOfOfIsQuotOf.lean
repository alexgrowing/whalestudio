import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ResidualSpectrumByClass
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DegreesPos

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DiscSpec.ByClassModel

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

variable (E N) in

def Clauses : Prop :=
  (∃ J : (a : ℕ) → CuspSub E a → ℕ → Submodule ℂ (Sm E N),
      (∀ (a d : ℕ) (π : CuspSub E a), d * a = N → π.IsUnitary → IsNormalised π →
        GlobalTheory.UnitaryBC.IsDiscrete (J a π d) ∧ IsSpehOf (J a π d) π d) ∧
      ∀ V : Submodule ℂ (Sm E N), GlobalTheory.UnitaryBC.IsDiscrete V →
        V ≤ ⨆ (a : ℕ) (d : ℕ) (π : CuspSub E a) (_ : d * a = N ∧ π.IsUnitary ∧ IsNormalised π), J a π d) ∧
    (∀ V V' : Submodule ℂ (Sm E N), GlobalTheory.UnitaryBC.IsDiscrete V → GlobalTheory.UnitaryBC.IsDiscrete V' →
      ∀ (a d : ℕ) (π : CuspSub E a),
      π.IsUnitary → IsNormalised π → IsSpehOf V π d → IsSpehOf V' π d → IsIsoGL V V') ∧
    ∀ V : Submodule ℂ (Sm E N), GlobalTheory.UnitaryBC.IsDiscrete V → ∀ (a d : ℕ) (π : CuspSub E a),
      π.IsUnitary → IsNormalised π → IsSpehOf V π d → ∀ w σ σ', π.IsLocComp w σ → IsLocCompGL V w σ' →
        GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ

theorem byClass_iff : GlobalTheory.Published.ResidualSpectrumByClass ↔
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ), 1 ≤ N → Clauses E N := Iff.rfl

theorem clauses_of
    (h1 : ∀ V : Submodule ℂ (Sm E N), GlobalTheory.UnitaryBC.IsDiscrete V →
      ∃ (a d : ℕ) (π : CuspSub E a), π.IsUnitary ∧ IsNormalised π ∧ IsSpehOf V π d)
    (h2 : ∀ (a d : ℕ) (π : CuspSub E a), d * a = N → IsNormalised π →
      ∃! V : Submodule ℂ (Sm E N), GlobalTheory.UnitaryBC.IsDiscrete V ∧ IsSpehOf V π d)
    (h5 : ∀ V : Submodule ℂ (Sm E N), GlobalTheory.UnitaryBC.IsDiscrete V → ∀ (a d : ℕ) (π : CuspSub E a),
      IsNormalised π → IsSpehOf V π d → ∀ w, (∃ σ σ', π.IsLocComp w σ ∧ IsLocCompGL V w σ') ∧
        ∀ σ σ', π.IsLocComp w σ → IsLocCompGL V w σ' →
          GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ) : Clauses E N := by
  classical
  refine ⟨⟨fun a π d => if h : d * a = N ∧ IsNormalised π then (h2 a d π h.1 h.2).exists.choose else ⊥,
    fun a d π h _ hn => ?_, fun V hV => ?_⟩, fun V V' hV hV' a d π _ hn e e' => ?_,
    fun V hV a d π _ hn e w => (h5 V hV a d π hn e w).2⟩
  · simp only [dif_pos (And.intro h hn)]
    exact (h2 a d π h hn).exists.choose_spec
  · obtain ⟨a, d, π, hu, hn, e⟩ := h1 V hV
    refine le_iSup_of_le a (le_iSup_of_le d (le_iSup_of_le π (le_iSup_of_le ⟨e.mul_eq, hu, hn⟩ ?_)))
    simp only [dif_pos (And.intro e.mul_eq hn)]
    exact ((h2 a d π e.mul_eq hn).unique ⟨hV, e⟩ (h2 a d π e.mul_eq hn).exists.choose_spec).le
  · obtain rfl := (h2 a d π e.mul_eq hn).unique ⟨hV, e⟩ ⟨hV', e'⟩
    exact ⟨.refl _ _, fun _ _ _ h => h⟩

theorem of_residual (H : GlobalTheory.Published.DiscreteSpectrumResidual) : GlobalTheory.Published.ResidualSpectrumByClass :=
  fun E _ _ _ N hN => let ⟨h1, h2, _, _, h5⟩ := H E N hN; clauses_of h1 h2 h5

theorem clauses_one : Clauses E 1 :=
  let ⟨h1, h2, _, _, h5⟩ := ResidualModel.residual_one E; clauses_of h1 h2 h5

section Algebra

variable {M O : Type} [AddCommGroup M] [Module ℂ M] (A : O → Module.End ℂ M)

theorem apply_mem_of_stable {V : Submodule ℂ M} (hV : ∀ o, ∀ φ ∈ V, A o φ ∈ V) {z : Module.End ℂ M}
    (hz : z ∈ Algebra.adjoin ℂ (Set.range A)) : ∀ φ ∈ V, z φ ∈ V := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨o, rfl⟩ := hx; exact hV o
  | algebraMap c => exact fun φ hφ => by simpa using V.smul_mem c hφ
  | add x y _ _ hx hy => exact fun φ hφ => add_mem (hx φ hφ) (hy φ hφ)
  | mul x y _ _ hx hy => exact fun φ hφ => hx _ (hy φ hφ)

def toOp (V : Submodule ℂ M) (hV : ∀ o, ∀ φ ∈ V, A o φ ∈ V) : Submodule (Algebra.adjoin ℂ (Set.range A)) M where
  toAddSubmonoid := V.toAddSubmonoid
  smul_mem' z φ hφ := apply_mem_of_stable A hV z.2 φ hφ

def IsIrr (V : Submodule ℂ M) : Prop :=
  (∀ o, ∀ φ ∈ V, A o φ ∈ V) ∧ V ≠ ⊥ ∧ ∀ W ≤ V, (∀ o, ∀ φ ∈ W, A o φ ∈ W) → W = ⊥ ∨ W = V

theorem isSimpleModule_toOp {V : Submodule ℂ M} (hV : IsIrr A V) :
    IsSimpleModule (Algebra.adjoin ℂ (Set.range A)) (toOp A V hV.1) := by
  refine isSimpleModule_iff_isAtom.2 ⟨fun h => hV.2.1 (eq_bot_iff.2 fun φ hφ => h.le hφ), fun W hW => ?_⟩
  rcases hV.2.2 (W.restrictScalars ℂ) (fun φ hφ => hW.le hφ) (fun o φ hφ =>
    W.smul_mem (⟨A o, Algebra.subset_adjoin ⟨o, rfl⟩⟩ : Algebra.adjoin ℂ (Set.range A)) hφ) with h | h
  · exact eq_bot_iff.2 fun φ hφ => h.le hφ
  · exact absurd (fun φ hφ => h.ge hφ) hW.not_ge

theorem exists_map_eq {s : Set (Submodule ℂ M)} (hs : ∀ J ∈ s, IsIrr A J) {V : Submodule ℂ M} (hV : IsIrr A V)
    (hle : V ≤ sSup s) : ∃ J ∈ s, ∃ g : M →ₗ[ℂ] M, J.map g = V ∧ ∀ o, ∀ φ ∈ J, g (A o φ) = A o (g φ) := by
  let t : Set (Submodule (Algebra.adjoin ℂ (Set.range A)) M) := {S | ∃ (J : _) (h : J ∈ s), S = toOp A J (hs J h).1}
  haveI : ∀ m : t, IsSimpleModule (Algebra.adjoin ℂ (Set.range A)) m := by
    rintro ⟨_, J, h, rfl⟩
    exact isSimpleModule_toOp A (hs J h)
  haveI := isSimpleModule_toOp A hV
  have ht : toOp A V hV.1 ≤ sSup t := fun φ hφ => by
    have : sSup s ≤ (sSup t).restrictScalars ℂ := sSup_le fun J h ψ hψ =>
      (le_sSup (s := t) ⟨J, h, rfl⟩ : toOp A J (hs J h).1 ≤ _) hψ
    exact this (hle hφ)
  obtain ⟨_, ⟨J, hJ, rfl⟩, ⟨T⟩⟩ := (toOp A V hV.1).linearEquiv_of_le_sSup t ht
  replace T := T.symm
  let T₀ : J →ₗ[ℂ] M :=
    { toFun := fun φ => (T ⟨φ.1, φ.2⟩).1
      map_add' := fun φ ψ => congrArg Subtype.val (T.map_add ⟨φ.1, φ.2⟩ ⟨ψ.1, ψ.2⟩)
      map_smul' := fun c φ => congrArg Subtype.val ((T.toLinearMap.restrictScalars ℂ).map_smul c ⟨φ.1, φ.2⟩) }
  obtain ⟨g, hg⟩ := T₀.exists_extend
  have hg' : ∀ φ (hφ : φ ∈ J), g φ = (T ⟨φ, hφ⟩).1 := fun φ hφ => LinearMap.congr_fun hg ⟨φ, hφ⟩
  refine ⟨J, hJ, g, le_antisymm ?_ fun ψ hψ => ⟨(T.symm ⟨ψ, hψ⟩).1, (T.symm ⟨ψ, hψ⟩).2, ?_⟩, fun o φ hφ => ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    rw [hg' φ hφ]
    exact (T ⟨φ, hφ⟩).2
  · rw [hg' _ hφ, hg' _ ((hs J hJ).1 o φ hφ)]
    exact congrArg Subtype.val
      (T.map_smul (⟨A o, Algebra.subset_adjoin ⟨o, rfl⟩⟩ : Algebra.adjoin ℂ (Set.range A)) ⟨φ, hφ⟩)
  · rw [hg' _ (T.symm ⟨ψ, hψ⟩).2]
    exact congrArg Subtype.val (T.apply_symm_apply ⟨ψ, hψ⟩)

end Algebra

theorem isSpehOf_of_isQuotOf {V V' : Submodule ℂ (Sm E N)} (hq : IsQuotOf V' V) {a d : ℕ} {π : CuspSub E a}
    (h : IsSpehOf V π d) : IsSpehOf V' π d := by
  obtain ⟨h, ν, hν, f, hf, hc⟩ := h
  obtain ⟨g, hg, hd⟩ := hq
  refine ⟨h, ν, hν, g ∘ₗ f, by rw [Submodule.map_comp, hf, hg], fun o φ hφ => ?_⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hc o φ hφ, hd o _ (hf ▸ Submodule.mem_map_of_mem hφ)]

theorem exhaustion (H : Clauses E N) {V : Submodule ℂ (Sm E N)} (hV : GlobalTheory.UnitaryBC.IsDiscrete V) :
    ∃ (a d : ℕ) (π : CuspSub E a), π.IsUnitary ∧ IsNormalised π ∧ IsSpehOf V π d := by
  obtain ⟨⟨J, hJ, hle⟩, -⟩ := H
  obtain ⟨_, ⟨a, d, π, h, hu, hn, rfl⟩, hq⟩ := exists_map_eq (act (E := E) (a := N))
    (s := {S | ∃ (a d : ℕ) (π : CuspSub E a), d * a = N ∧ π.IsUnitary ∧ IsNormalised π ∧ S = J a π d})
    (by
      rintro _ ⟨a, d, π, h, hu, hn, rfl⟩
      have := (hJ a d π h hu hn).1
      exact ⟨this.stable, this.ne_bot, this.irred⟩) ⟨hV.stable, hV.ne_bot, hV.irred⟩
    ((hle V hV).trans (iSup_le fun a => iSup_le fun d => iSup_le fun π => iSup_le fun h =>
      le_sSup ⟨a, d, π, h.1, h.2.1, h.2.2, rfl⟩))
  exact ⟨a, d, π, hu, hn, isSpehOf_of_isQuotOf hq (hJ a d π h hu hn).2⟩

theorem exists_hyp : ∃ (V : Submodule ℂ (Sm E 1)) (π : CuspSub E 1),
    GlobalTheory.UnitaryBC.IsDiscrete V ∧ π.IsUnitary ∧ IsNormalised π ∧ IsSpehOf V π 1 :=
  let ⟨V, π, h1, h2, h3⟩ := Model.exists_discrete_speh (E := E)
  ⟨V, π, h1, Model.isUnitary_of_isNormalised h2, h2, h3⟩

end GlobalTheory.DiscSpec.ByClassModel

end
