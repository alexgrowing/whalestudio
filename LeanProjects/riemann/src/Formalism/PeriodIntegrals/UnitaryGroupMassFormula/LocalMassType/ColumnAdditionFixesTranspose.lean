import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.StepW

noncomputable section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory NumberField
  IsDedekindDomain
open scoped TensorProduct

section Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
  (Λ : Set (Fin n → E))

theorem smul_apply_lin (k : HA (Fv F v) σ J) {a : ℕ} (X : TupV (E := E) v n a) (i : Fin a) :
    (k • X) i = lin (Fv F v) σ J k (X i) := rfl

theorem kv_lin {k : HA (Fv F v) σ J} (hk : k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    (y : Fin n → Fv F v ⊗[F] E) :
    lin (Fv F v) σ J k y ∈ latLoc (E := E) v Λ ↔ y ∈ latLoc (E := E) v Λ :=
  (hk y).symm

theorem locF_smul (k : HA (Fv F v) σ J) {r : ℕ} (X : TupV (E := E) v n (r + 1)) :
    locF v (k • X) = k • locF v X := by
  funext a
  show sc (E := E) v (alp v r a) • lin (Fv F v) σ J k (X a) =
    lin (Fv F v) σ J k (sc (E := E) v (alp v r a) • X a)
  rw [map_smul]

def GM (g : ℕ) (z : Fin n → Fv F v ⊗[F] E) : Prop :=
  ∃ y ∈ latLoc (E := E) v Λ, z = sc (E := E) v (g : Fv F v) • y

variable {σ J v Λ}

theorem gm_add {g : ℕ} {z w : Fin n → Fv F v ⊗[F] E} (hz : GM v Λ g z) (hw : GM v Λ g w) :
    GM v Λ g (z + w) := by
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨y', hy', rfl⟩ := hw
  exact ⟨y + y', Submodule.add_mem _ hy hy', by rw [smul_add]⟩

theorem gm_neg {g : ℕ} {z : Fin n → Fv F v ⊗[F] E} (hz : GM v Λ g z) : GM v Λ g (-z) := by
  obtain ⟨y, hy, rfl⟩ := hz
  exact ⟨-y, Submodule.neg_mem _ hy, by rw [smul_neg]⟩

theorem gm_lin {g : ℕ} {k : HA (Fv F v) σ J} (hk : k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    {z : Fin n → Fv F v ⊗[F] E} (hz : GM v Λ g z) : GM v Λ g (lin (Fv F v) σ J k z) := by
  obtain ⟨y, hy, rfl⟩ := hz
  exact ⟨lin (Fv F v) σ J k y, (kv_lin σ J v Λ hk y).2 hy, by rw [map_smul]⟩

theorem kv_inv' {k : HA (Fv F v) σ J} (hk : k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v) :
    k⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v := (Kloc (E := E) v Λ).inv_mem hk

theorem kv_mul' {a b : HA (Fv F v) σ J} (ha : a ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    (hb : b ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v) : a * b ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v :=
  (Kloc (E := E) v Λ).mul_mem ha hb

theorem prim_smul {k : HA (Fv F v) σ J} (hk : k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v) {a : ℕ}
    {Y : TupV (E := E) v n a} (hY : IsPrim v Λ Y) : IsPrim v Λ (k • Y) := by
  refine ⟨fun i => ?_, fun c hc => ?_⟩
  · rw [smul_apply_lin, kv_lin σ J v Λ hk]; exact hY.1 i
  · apply hY.2 c
    have : (∑ i, c i • (k • Y) i) = lin (Fv F v) σ J k (∑ i, c i • Y i) := by
      simp only [smul_apply_lin, map_sum, map_smul]
    rw [this, kv_lin σ J v Λ hk] at hc
    exact hc

def CongL (g : ℕ) {r : ℕ} (X X' : TupV (E := E) v n (r + 1)) : Prop :=
  ∀ a, GM v Λ g (locF v X' a - locF v X a)

theorem congL_smul {g : ℕ} {r : ℕ} {k : HA (Fv F v) σ J} (hk : k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    {X X' : TupV (E := E) v n (r + 1)} (h : CongL (Λ := Λ) g X X') : CongL (Λ := Λ) g (k • X) (k • X') := by
  intro a
  rw [locF_smul, locF_smul, smul_apply_lin, smul_apply_lin, ← map_sub]
  exact gm_lin hk (h a)

theorem congL_trans {g : ℕ} {r : ℕ} {X Y Z : TupV (E := E) v n (r + 1)}
    (h1 : CongL (Λ := Λ) g X Y) (h2 : CongL (Λ := Λ) g Y Z) : CongL (Λ := Λ) g X Z := by
  intro a
  have := gm_add (h2 a) (h1 a)
  simpa using this

theorem congL_symm {g : ℕ} {r : ℕ} {X Y : TupV (E := E) v n (r + 1)}
    (h1 : CongL (Λ := Λ) g X Y) : CongL (Λ := Λ) g Y X := by
  intro a
  have := gm_neg (h1 a)
  simpa using this

theorem mem_congruence_subgroup_iff {g : ℕ} {r : ℕ} {P : Frame E n r} {k : HA (Fv F v) σ J} :
    k ∈ K1 σ J v Λ g P ↔ k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v ∧
      CongL (Λ := Λ) g (ratTup (F := F) (Fv F v) (F0 P)) (k • ratTup (F := F) (Fv F v) (F0 P)) :=
  Iff.rfl

theorem congruence_mul_mem {g : ℕ} {r : ℕ} {P : Frame E n r} {a b : HA (Fv F v) σ J}
    (ha : a ∈ K1 σ J v Λ g P) (hb : b ∈ K1 σ J v Λ g P) : a * b ∈ K1 σ J v Λ g P := by
  rw [mem_congruence_subgroup_iff] at *
  refine ⟨kv_mul' ha.1 hb.1, ?_⟩
  rw [mul_smul]
  exact congL_trans ha.2 (congL_smul ha.1 hb.2)

theorem column_addition_fixes_transpose {g : ℕ} {r : ℕ} {P : Frame E n r} {a : HA (Fv F v) σ J}
    (ha : a ∈ K1 σ J v Λ g P) : a⁻¹ ∈ K1 σ J v Λ g P := by
  rw [mem_congruence_subgroup_iff] at *
  refine ⟨kv_inv' ha.1, ?_⟩
  have := congL_smul (kv_inv' ha.1) ha.2
  rw [inv_smul_smul] at this
  exact congL_symm this

theorem congruence_mul_mem_iff {g : ℕ} {r : ℕ} {P : Frame E n r} {a : HA (Fv F v) σ J}
    (ha : a ∈ K1 σ J v Λ g P) (m : HA (Fv F v) σ J) :
    a * m ∈ K1 σ J v Λ g P ↔ m ∈ K1 σ J v Λ g P := by
  refine ⟨fun h => ?_, fun h => congruence_mul_mem ha h⟩
  have := congruence_mul_mem (column_addition_fixes_transpose ha) h
  rwa [← mul_assoc, inv_mul_cancel, one_mul] at this

theorem conj_mem_congruence_iff {g : ℕ} {r : ℕ} {P P' : Frame E n r} {κ : HA (Fv F v) σ J}
    (hκ : κ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    (hc : CongL (Λ := Λ) g (ratTup (F := F) (Fv F v) (F0 P)) (κ • ratTup (F := F) (Fv F v) (F0 P')))
    {h : HA (Fv F v) σ J} (hh : h • ratTup (F := F) (Fv F v) (F0 P') = ratTup (F := F) (Fv F v) (F0 P')) :
    κ * h * κ⁻¹ ∈ K1 σ J v Λ g P ↔ h ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v := by
  constructor
  · intro hm
    have h1 := kv_mul' (kv_mul' (kv_inv' hκ) hm.1) hκ
    rwa [show κ⁻¹ * (κ * h * κ⁻¹) * κ = h by group] at h1
  · intro hK
    have hm : κ * h * κ⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v := kv_mul' (kv_mul' hκ hK) (kv_inv' hκ)
    refine (mem_congruence_subgroup_iff).2 ⟨hm, ?_⟩

    have h1 := congL_smul hm hc
    rw [show (κ * h * κ⁻¹) • κ • ratTup (F := F) (Fv F v) (F0 P') = κ • ratTup (F := F) (Fv F v) (F0 P') by
      rw [← mul_smul, show κ * h * κ⁻¹ * κ = κ * h by group, mul_smul, hh]] at h1
    exact congL_trans hc (congL_symm h1)

end Alg

end PI.LocMassTypW
