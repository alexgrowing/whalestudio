import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem tangent_of_form {κ B : Type} [Field κ] [CommRing B] [Algebra κ B] (ε : B →ₐ[κ] κ)
    (d : B →ₗ[κ] κ) (h1 : d 1 = 0) (h2 : ∀ x ∈ RingHom.ker ε.toRingHom ^ 2, d x = 0) :
    ∃ v : B →ₐ[κ] DualNumber κ, (TrivSqZeroExt.fstHom κ κ κ).comp v = ε ∧ ∀ x, (v x).snd = d x := by
  have hmem : ∀ x, x - algebraMap κ B (ε x) ∈ RingHom.ker ε.toRingHom := by
    intro x
    rw [RingHom.mem_ker]
    change ε (x - algebraMap κ B (ε x)) = 0
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have key : ∀ x y, d (x * y) = ε x * d y + ε y * d x := by
    intro x y
    have hm : (x - algebraMap κ B (ε x)) * (y - algebraMap κ B (ε y)) ∈
        RingHom.ker ε.toRingHom ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (hmem x) (hmem y)
    have hz := h2 _ hm
    have e : x * y = (x - algebraMap κ B (ε x)) * (y - algebraMap κ B (ε y)) + ε y • x
        + ε x • y - (ε x * ε y) • (1 : B) := by
      simp only [Algebra.smul_def, map_mul, mul_one]
      ring
    rw [e, map_sub, map_add, map_add, hz, map_smul, map_smul, map_smul, h1]
    simp only [smul_eq_mul]
    ring
  let f : B →ₗ[κ] DualNumber κ :=
    { toFun := fun x => TrivSqZeroExt.inl (ε x) + TrivSqZeroExt.inr (d x)
      map_add' := by
        intro x y
        ext <;> simp <;> ring
      map_smul' := by
        intro a x
        ext <;> simp }
  have hf : ∀ x, f x = TrivSqZeroExt.inl (ε x) + TrivSqZeroExt.inr (d x) := fun _ => rfl
  refine ⟨AlgHom.ofLinearMap f ?_ ?_, ?_, ?_⟩
  · rw [hf]
    ext <;> simp [h1]
  · intro x y
    rw [hf, hf, hf]
    ext <;> simp [key] <;> ring
  · ext x
    simp [hf]
  · intro x
    simp [hf]

theorem UpperTheory.Gal.crystallineComparison.Mod.cotanOne_of :
    CotanOne := by
  intro κ B _ _ _ ε v₀ hall
  classical
  let m := RingHom.ker ε.toRingHom
  let s : B → κ := fun x => (v₀ x).snd
  have hs_sub : ∀ x y, s (x - y) = s x - s y := by
    intro x y
    simp [s]
  have hs_smul : ∀ (a : κ) x, s (a • x) = a * s x := by
    intro a x
    simp [s]
  have hkill : ∀ y ∈ m, s y = 0 → y ∈ m ^ 2 := by
    intro y hy hsy
    by_contra hy2
    let P : Submodule κ B := (m ^ 2).restrictScalars κ ⊔ Submodule.span κ {(1 : B)}
    have hyP : y ∉ P := by
      intro hyP
      obtain ⟨z, hz, w, hw, hzw⟩ := Submodule.mem_sup.1 hyP
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
      have hz' : z ∈ m ^ 2 := hz
      have hzm : z ∈ m := Ideal.pow_le_self two_ne_zero hz'
      have e1 : ε y = ε z + a * ε 1 := by
        rw [← hzw, map_add, map_smul, smul_eq_mul]
      have hεy : ε y = 0 := hy
      have hεz : ε z = 0 := hzm
      simp only [hεy, hεz, _root_.map_one, zero_add] at e1
      have ha : a = 0 := by simpa using e1.symm
      apply hy2
      rw [← hzw, ha, zero_smul, add_zero]
      exact hz'
    obtain ⟨d, hdy, hdP⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hyP inferInstance
    have hdP' : ∀ p ∈ P, d p = 0 := by
      intro p hp
      have h3 : d p ∈ Submodule.map d P := ⟨p, hp, rfl⟩
      rw [hdP, Submodule.mem_bot] at h3
      exact h3
    have hd1 : d 1 = 0 := hdP' 1 (Submodule.mem_sup_right (Submodule.mem_span_singleton_self 1))
    have hd2 : ∀ x ∈ m ^ 2, d x = 0 := fun x hx => hdP' x (Submodule.mem_sup_left hx)
    obtain ⟨v, hv, hvd⟩ := tangent_of_form ε d hd1 hd2
    obtain ⟨c, hc⟩ := hall v hv
    apply hdy
    rw [← hvd, hc]
    change c * s y = 0
    rw [hsy, mul_zero]
  by_cases hex : ∃ t ∈ m, s t ≠ 0
  · obtain ⟨t, ht, hst⟩ := hex
    refine ⟨t, ht, ?_⟩
    intro x hx
    have hy : x - (s x / s t) • t ∈ m := by
      refine m.sub_mem hx ?_
      rw [Algebra.smul_def]
      exact m.mul_mem_left _ ht
    have hsy : s (x - (s x / s t) • t) = 0 := by
      rw [hs_sub, hs_smul, div_mul_cancel₀ _ hst, sub_self]
    have h2 := hkill _ hy hsy
    have e : x = (s x / s t) • t + (x - (s x / s t) • t) := by abel
    rw [e]
    refine Ideal.add_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right h2)
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self t)
  · push_neg at hex
    refine ⟨0, m.zero_mem, ?_⟩
    intro x hx
    exact Ideal.mem_sup_right (hkill x hx (hex x hx))
