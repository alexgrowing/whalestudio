import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.UnitaryLevelClosureSubgroup

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def KfBridgeStep : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (hb : AdBridgeIso I) (y : I.Gf), y ∈ I.Kset →
    (splitA I.cm.sig I.J (toHA I hb (1, y))).2 ∈ Kf I.cm.sig I.J (I.L : Set (Fin I.n → I.E))

theorem finHA_mul {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (x y : X.B.I.Gf) :
    finHA X hb (x * y) = finHA X hb x * finHA X hb y := by
  unfold finHA
  have e : ((1 : X.B.I.Ginf), x * y) = ((1 : X.B.I.Ginf), x) * ((1 : X.B.I.Ginf), y) := by
    ext <;> simp
  rw [e, map_mul, map_mul, Prod.snd_mul]

theorem finHA_inv {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (x : X.B.I.Gf) :
    finHA X hb x⁻¹ = (finHA X hb x)⁻¹ := by
  unfold finHA
  have e : ((1 : X.B.I.Ginf), x⁻¹) = ((1 : X.B.I.Ginf), x)⁻¹ := by
    ext <;> simp
  rw [e, map_inv, map_inv, Prod.snd_inv]

theorem finHA_one {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) : finHA X hb 1 = 1 := by
  unfold finHA
  have e : ((1 : X.B.I.Ginf), (1 : X.B.I.Gf)) = 1 := rfl
  rw [e, map_one, map_one, Prod.snd_one]

theorem mem_conjugate_level_iff {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word)
    (z : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) :
    z ∈ K2u X hb u ↔
      ∃ k ∈ X.K2, finHA X hb (X.xu u) * finHA X hb k * (finHA X hb (X.xu u))⁻¹ = z := by
  unfold K2u levelUnitary
  constructor
  · rintro ⟨y, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, ⟨k, hk, rfl⟩, rfl⟩

def unitaryLevelIntersection {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word) :
    Subgroup (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) where
  carrier := Subtype.val ⁻¹' K2u X hb u
  one_mem' := by
    refine (mem_conjugate_level_iff X hb u _).2 ⟨1, hK.1, ?_⟩
    rw [finHA_one, mul_one, mul_inv_cancel]
    rfl
  mul_mem' := by
    intro a b ha hb'
    obtain ⟨k1, hk1, e1⟩ := (mem_conjugate_level_iff X hb u _).1 ha
    obtain ⟨k2, hk2, e2⟩ := (mem_conjugate_level_iff X hb u _).1 hb'
    refine (mem_conjugate_level_iff X hb u _).2 ⟨k1 * k2, hK.2.1 _ hk1 _ hk2, ?_⟩
    change _ = (a : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) * (b : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)
    rw [finHA_mul, ← e1, ← e2]
    group
  inv_mem' := by
    intro a ha
    obtain ⟨k1, hk1, e1⟩ := (mem_conjugate_level_iff X hb u _).1 ha
    refine (mem_conjugate_level_iff X hb u _).2 ⟨k1⁻¹, hK.2.2.1 _ hk1, ?_⟩
    change _ = (a : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)⁻¹
    rw [finHA_inv, ← e1]
    group

theorem idxGroupStep_of (hKf : KfBridgeStep) : IdxGroupStep := by
  intro D X hb hK u _hM hL

  have hEq : unitaryLevelClosureSubgroup X hb u = unitaryLevelIntersection X hb hK u := by
    unfold unitaryLevelClosureSubgroup
    exact Subgroup.closure_eq (unitaryLevelIntersection X hb hK u)

  have hfin : ∀ y ∈ X.B.I.Kset,
      finHA X hb y ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    fun y hy => by
      unfold finHA
      exact hKf X.B.I hb y hy
  have hx : X.xu u ∈ X.B.I.Kset := X.xu_K u
  refine ⟨by rw [hEq]; rfl, ?_⟩
  rw [hEq]
  intro z hz
  obtain ⟨k, hk, e⟩ := (mem_conjugate_level_iff X hb u _).1 hz
  rw [KHg, Subgroup.mem_subgroupOf, ← e]
  have h1 := hfin _ hx
  have h2 := hfin k (hL.2.1 k hk)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) (Subgroup.inv_mem _ h1)

theorem kfBridgeStep_of_adBridgeK (h : ∀ I : Formalism.MainNotions.S.AutInst, AdBridgeK I) : KfBridgeStep := by
  intro I hb y hy
  have hbr : IsBridge I (toHA I hb) := hb.choose_spec
  have hmem : ((1 : I.Ginf), y) ∈ KGA I := by
    refine ⟨fun v a b hab => ?_, hy⟩
    have hne : a ≠ b := fun hab' => hab (hab' ▸ rfl)
    simp [Formalism.MainNotions.S.uMat, Pi.one_apply, Matrix.one_apply_ne hne]
  have hK : toHA I hb ((1 : I.Ginf), y) ∈ KHA I := by
    rw [← h I (toHA I hb) hbr]
    exact ⟨_, hmem, rfl⟩
  rw [Kf, Subgroup.mem_iInf]
  intro v
  exact hK.2 v

end PIW.MassDataColumns
