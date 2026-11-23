import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RootSumApply

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas

open ReciprocityTheory.ChartRestriction.DS

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T : S7.KType ε Λ)

open Classical in

def rhoS (h : Matrix (Fin k) (Fin k) ℂ) : spanW (k := k) (r := r) T →L[ℂ] spanW (k := k) (r := r) T :=
  if hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ then
    LinearMap.toContinuousLinearMap ((rhoK (k := k) (r := r) T h : T.V →ₗ[ℂ] T.V).restrict
      (fun _ hv => spanW_stable T hh hv))
  else 0

theorem rhoS_apply {h : Matrix (Fin k) (Fin k) ℂ} (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ)
    (v : spanW (k := k) (r := r) T) : (rhoS T h v : T.V) = rhoK (k := k) (r := r) T h v := by
  simp only [rhoS, dif_pos hh]
  rfl

theorem uj_unit {h : Matrix (Fin k) (Fin k) ℂ} (hh : h ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k)) :
    h ∈ Matrix.unitaryGroup (Fin k) ℂ := by
  exact (HW.uqU_mem_Kset hh).1

theorem unit_ks {h : Matrix (Fin k) (Fin k) ℂ} (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    h ∈ Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k) := by
  refine ⟨hh, ?_⟩
  simp [Formalism.REAL.Jm, Formalism.MainNotions.S.allPos]

theorem unit_uj {h : Matrix (Fin k) (Fin k) ℂ} (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    h ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k) := by
  have hJ : Formalism.REAL.Jm (Formalism.MainNotions.S.allPos k) = 1 := by simp [Formalism.REAL.Jm, Formalism.MainNotions.S.allPos]
  show hᴴ * Formalism.REAL.Jm (Formalism.MainNotions.S.allPos k) * h = Formalism.REAL.Jm (Formalism.MainNotions.S.allPos k)
  rw [hJ, Matrix.mul_one, ← Matrix.star_eq_conjTranspose]
  exact Unitary.star_mul_self_of_mem hh

theorem wtS_iff {μ : Fin k → ℝ} {v : spanW (k := k) (r := r) T} :
    Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoS T) μ v ↔
      Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k := k) (r := r) T) μ (v : T.V) := by
  constructor
  · intro h t ht
    have := congrArg Subtype.val (h t ht)
    rw [rhoS_apply T ht.1] at this
    exact this
  · intro h t ht
    apply Subtype.ext
    rw [rhoS_apply T ht.1]
    exact h t ht

theorem rhoS_hc (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {u : Fin k → ℝ}
    (hΛ : ∀ q : Fin k, Λ (fI k r q) = Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u q) :
    Formalism.MainNotions.S.IsHCTypeU k u (rhoS T) := by
  have hΛ' : (fun q => Λ (fI k r q)) = Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u := funext hΛ
  refine ⟨⟨⟨⟨T.w, w_mem_spanW T⟩, 0, fun h => HW.KType.w_ne_zero T (congrArg Subtype.val h)⟩⟩,
    inferInstance, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨inferInstance, fun _ _ _ _ => Submodule.mem_top, ?_, ?_, ?_⟩⟩
  · ext v
    rw [rhoS_apply T (one_mem _), rhoK_one]
    rfl
  · intro a ha b hb
    ext v
    rw [rhoS_apply T (mul_mem (uj_unit ha) (uj_unit hb)), rhoK_mul T hε (uj_unit ha) (uj_unit hb)]
    change _ = ((rhoS T a (rhoS T b v)) : T.V)
    rw [rhoS_apply T (uj_unit ha), rhoS_apply T (uj_unit hb)]
  · intro g hg v
    change ‖(rhoS T g v : T.V)‖ = ‖(v : T.V)‖
    rw [rhoS_apply T (uj_unit hg), rhoK_norm T hε (uj_unit hg)]
  · intro v
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    have hc : ContinuousOn (fun g => rhoK (k := k) (r := r) T g v) (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k)) :=
      ((HW.torep_isURepOn T).2.2 v).comp kE_cont.continuousOn
        (fun g hg => kE_mem_Kset hε (uj_unit hg))
    refine hc.congr fun g hg => ?_
    exact rhoS_apply T (uj_unit hg) v
  · intro S' _ hS'
    let S'' : Submodule ℂ T.V := S'.map (spanW (k := k) (r := r) T).subtype
    have hle : S'' ≤ spanW (k := k) (r := r) T := by
      rintro _ ⟨v, _, rfl⟩
      exact v.2
    have hst : ∀ h ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ v ∈ S'', rhoK (k := k) (r := r) T h v ∈ S'' := by
      rintro h hh _ ⟨v, hv, rfl⟩
      refine ⟨rhoS T h v, hS' h (unit_ks hh) v hv, ?_⟩
      exact rhoS_apply T hh v
    rcases spanW_irred T hε S'' hle hst with h | h
    · left
      rw [Submodule.eq_bot_iff]
      intro v hv
      have : (v : T.V) ∈ S'' := ⟨v, hv, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact Subtype.ext this
    · right
      rw [eq_top_iff]
      intro v _
      obtain ⟨v', hv', he⟩ := h v.2
      have : v' = v := Subtype.ext he
      rw [← this]; exact hv'
  · refine ⟨⟨T.w, w_mem_spanW T⟩, Submodule.mem_top,
      fun h => HW.KType.w_ne_zero T (congrArg Subtype.val h), ?_⟩
    rw [wtS_iff, ← hΛ']
    exact w_wtK T
  · intro μ v _ hv hwt
    rw [wtS_iff] at hwt
    rw [← hΛ']
    exact wt_cdom T hε v.2 (fun h => hv (Subtype.ext h)) hwt

theorem lowestKType_intertwiner_exists (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {u : Fin k → ℝ}
    (hΛ : ∀ q : Fin k, Λ (fI k r q) = Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u q)
    {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    (π' : Matrix (Fin k) (Fin k) ℂ → (Vp →L[ℂ] Vp)) (hπ : Formalism.MainNotions.S.IsHCTypeU k u π') {ξ : Vp}
    (hξ : Formalism.MainNotions.S.IsWtOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k)) π' (Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u) ξ) :
    ∃ (U : Vp ≃ₗᵢ[ℂ] spanW (k := k) (r := r) T) (α : ℂ),
      (∀ g ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ v, rhoK (k := k) (r := r) T g (U v) = (U (π' g v) : T.V)) ∧
        (U ξ : T.V) = α • T.w := by
  obtain ⟨U, hU⟩ := HW.hcTypeU_unique π' (rhoS T) hπ (rhoS_hc T hε hΛ)
  have hint : ∀ g ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ v,
      rhoK (k := k) (r := r) T g (U v) = (U (π' g v) : T.V) := fun g hg v => by
    rw [← rhoS_apply T hg, hU g (unit_uj hg) v]
  have hΛ' : (fun q => Λ (fI k r q)) = Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u := funext hΛ
  have hwt : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k := k) (r := r) T)
      (Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u) (U ξ : T.V) := by
    intro t ht
    rw [hint _ ht.1, hξ t (unit_uj ht.1), map_smul]
    rfl
  rw [← hΛ'] at hwt
  have hfull := wt_full T hε (U ξ).2 hwt
  have hfix : (fun a : Fin (2 * r + k + 1) => if h : a.val < k then (fun q => Λ (fI k r q)) ⟨a.val, h⟩ else Λ a) = Λ := by
    funext a; split_ifs <;> rfl
  rw [hfix] at hfull
  obtain ⟨α, hα⟩ := eq_smul_highestWeight_of_isWeight T hfull
  exact ⟨U, α, hint, hα⟩

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas
