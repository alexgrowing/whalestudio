import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.SsetGroup

open MeasureTheory MeasureTheory.Measure Matrix TopologicalSpace
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace CompanionTheory.D.Upq.ModEx

section Abstract

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

theorem map_mul_right_eq (μ : Measure H) [IsHaarMeasure μ] (g : H) :
    map (· * g) μ = modularCharacterFun g • μ := by
  rw [modularCharacterFun_eq_haarScalarFactor μ g]
  exact isMulLeftInvariant_eq_smul _ μ

theorem modular_aut (α : H ≃ₜ* H) (g : H) :
    modularCharacterFun (α g) = modularCharacterFun g := by
  set μ : Measure H := haar
  set ν : Measure H := map α μ with hν
  have hαm : Measurable α := α.continuous.measurable
  have h1 : map (· * α g) ν = modularCharacterFun (α g) • ν := map_mul_right_eq ν (α g)
  have h2 : map (· * α g) ν = modularCharacterFun g • ν := by
    rw [hν, map_map (measurable_mul_const _) hαm]
    have : (fun x => x * α g) ∘ α = α ∘ (fun x => x * g) := by
      ext x; simp
    rw [this, ← map_map hαm (measurable_mul_const _), map_mul_right_eq μ g, Measure.map_smul]
  have K : PositiveCompacts H := Classical.arbitrary _
  have hpos : ν K ≠ 0 := (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
  have hfin : ν K ≠ ∞ := K.isCompact.measure_lt_top.ne
  have h3 : (modularCharacterFun (α g) • ν) K = (modularCharacterFun g • ν) K := by
    rw [← h1, h2]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h3
  exact_mod_cast (ENNReal.mul_left_inj hpos hfin).1 h3

theorem modular_bdd {V : Set H} (hV : IsCompact V) :
    ∃ M : ℝ, ∀ v ∈ V, (modularCharacterFun v : ℝ) ≤ M := by
  set μ : Measure H := haar
  have K : PositiveCompacts H := Classical.arbitrary _
  set A : Set H := closure (K : Set H) with hA
  have hAc : IsCompact A := K.isCompact.closure
  have hAm : MeasurableSet A := isClosed_closure.measurableSet
  have hpos : μ A ≠ 0 :=
    (measure_pos_of_nonempty_interior _
      (K.interior_nonempty.mono (interior_mono subset_closure))).ne'
  have hfin : μ A ≠ ∞ := hAc.measure_lt_top.ne
  have hB : IsCompact (A * V⁻¹) := hAc.mul hV.inv
  have hBfin : μ (A * V⁻¹) ≠ ∞ := hB.measure_lt_top.ne
  refine ⟨(μ (A * V⁻¹) / μ A).toReal, fun v hv => ?_⟩
  have h1 : (modularCharacterFun v : ℝ≥0∞) * μ A ≤ μ (A * V⁻¹) := by
    have h := congrArg (fun ρ : Measure H => ρ A) (map_mul_right_eq μ v)
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
    rw [← h, map_apply (measurable_mul_const _) hAm]
    refine measure_mono fun x hx => ?_
    exact ⟨x * v, hx, v⁻¹, by simpa using hv, by simp⟩
  have h2 : (modularCharacterFun v : ℝ≥0∞) ≤ μ (A * V⁻¹) / μ A :=
    (ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl hfin)).2 h1
  have h3 := ENNReal.toReal_mono (ENNReal.div_ne_top hBfin hpos) h2
  simpa using h3

theorem map_mul_right_of_modular_one (h1 : ∀ g : H, modularCharacterFun g = 1)
    (ν : Measure H) [SigmaFinite ν] [IsMulLeftInvariant ν] (g : H) : map (· * g) ν = ν := by
  have K : PositiveCompacts H := Classical.arbitrary _
  have h := haarMeasure_unique ν K
  have h2 : map (· * g) (haarMeasure K) = haarMeasure K := by
    rw [map_mul_right_eq (haarMeasure K) g, h1 g, one_smul]
  calc map (· * g) ν = map (· * g) (ν K • haarMeasure K) := by rw [← h]
    _ = ν K • haarMeasure K := by rw [Measure.map_smul, h2]
    _ = ν := h.symm

end Abstract

section Concrete

open PI PI.QuotSetU.UnitaryGroupMassFormula

variable {m : ℕ}

def MG (G : Set (Matrix (Fin m) (Fin m) ℂ)) (_hG : IsMatGroup G) : Type := {x : (Matrix (Fin m) (Fin m) ℂ) // x ∈ G}

variable {G : Set (Matrix (Fin m) (Fin m) ℂ)} {hG : IsMatGroup G}

def MG.mat (x : MG G hG) : (Matrix (Fin m) (Fin m) ℂ) := Subtype.val x

theorem MG.mem (x : MG G hG) : x.mat ∈ G := Subtype.property x

def MG.mk (hG : IsMatGroup G) (x : (Matrix (Fin m) (Fin m) ℂ)) (hx : x ∈ G) : MG G hG := Subtype.mk x hx

@[simp] theorem MG.mat_mk (x : (Matrix (Fin m) (Fin m) ℂ)) (hx : x ∈ G) : (MG.mk hG x hx).mat = x := rfl

theorem MG.ext {x y : MG G hG} (h : x.mat = y.mat) : x = y := Subtype.ext h

instance : Group (MG G hG) where
  mul a b := MG.mk hG (a.mat * b.mat) (hG.2.2.1 _ a.mem _ b.mem)
  one := MG.mk hG 1 hG.2.1
  inv a := MG.mk hG a.mat⁻¹ (hG.2.2.2 _ a.mem).1
  mul_assoc a b c := MG.ext (Matrix.mul_assoc a.mat b.mat c.mat)
  one_mul a := MG.ext (Matrix.one_mul a.mat)
  mul_one a := MG.ext (Matrix.mul_one a.mat)
  inv_mul_cancel a := MG.ext (mul_eq_one_comm.1 (hG.2.2.2 _ a.mem).2)

@[simp] theorem MG.mat_mul (a b : MG G hG) : (a * b).mat = a.mat * b.mat := rfl
@[simp] theorem MG.mat_inv (a : MG G hG) : (a⁻¹).mat = a.mat⁻¹ := rfl

instance : TopologicalSpace (MG G hG) := inferInstanceAs (TopologicalSpace {x : (Matrix (Fin m) (Fin m) ℂ) // x ∈ G})

theorem MG.isClosedEmbedding_mat : Topology.IsClosedEmbedding (MG.mat : MG G hG → (Matrix (Fin m) (Fin m) ℂ)) :=
  hG.1.isClosedEmbedding_subtypeVal

theorem MG.continuous_mat : Continuous (MG.mat : MG G hG → (Matrix (Fin m) (Fin m) ℂ)) :=
  MG.isClosedEmbedding_mat.continuous

theorem MG.continuous_iff {X : Type*} [TopologicalSpace X] {f : X → MG G hG} :
    Continuous f ↔ Continuous (fun x => (f x).mat) :=
  MG.isClosedEmbedding_mat.isInducing.continuous_iff

theorem MG.det_ne_zero (a : MG G hG) : a.mat.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (hG.2.2.2 _ a.mem).2
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

instance : IsTopologicalGroup (MG G hG) where
  continuous_mul := MG.continuous_iff.2
    ((MG.continuous_mat.comp continuous_fst).matrix_mul (MG.continuous_mat.comp continuous_snd))
  continuous_inv := by
    refine MG.continuous_iff.2 ?_
    have : (fun a : MG G hG => (a⁻¹).mat) = fun a => (a.mat.det)⁻¹ • a.mat.adjugate := by
      ext1 a
      rw [MG.mat_inv, Matrix.inv_def, Ring.inverse_eq_inv']
    rw [this]
    exact (MG.continuous_mat.matrix_det.inv₀ MG.det_ne_zero).smul
      MG.continuous_mat.matrix_adjugate

instance : LocallyCompactSpace (MG G hG) :=
  haveI : LocallyCompactSpace (Matrix (Fin m) (Fin m) ℂ) := inferInstanceAs (LocallyCompactSpace (Fin m → Fin m → ℂ))
  MG.isClosedEmbedding_mat.locallyCompactSpace

instance : SecondCountableTopology (MG G hG) :=
  haveI : SecondCountableTopology (Matrix (Fin m) (Fin m) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin m → ℂ))
  MG.isClosedEmbedding_mat.isEmbedding.secondCountableTopology

instance : MeasurableSpace (MG G hG) := borel _
instance : BorelSpace (MG G hG) := ⟨rfl⟩

def MG.toM (x : MG G hG) : MtM m := Matrix.of.symm x.mat

theorem MG.measurableEmbedding_toM : MeasurableEmbedding (MG.toM : MG G hG → MtM m) :=
  Topology.IsClosedEmbedding.measurableEmbedding (β := MtM m) (f := MG.toM)
    (MG.isClosedEmbedding_mat (hG := hG))

theorem MG.range_toM : Set.range (MG.toM : MG G hG → MtM m) = {x | Matrix.of x ∈ G} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩; exact a.mem
  · intro hx; exact ⟨MG.mk hG (Matrix.of x) hx, rfl⟩

def conjAut (hG : IsMatGroup G) (c : (Matrix (Fin m) (Fin m) ℂ)) (hc : IsUnit c) (hn : ∀ g, c * g * c⁻¹ ∈ G ↔ g ∈ G) :
    MG G hG ≃ₜ* MG G hG :=
  have h1 : c⁻¹ * c = 1 := Matrix.nonsing_inv_mul c ((Matrix.isUnit_iff_isUnit_det c).1 hc)
  have h2 : c * c⁻¹ = 1 := Matrix.mul_nonsing_inv c ((Matrix.isUnit_iff_isUnit_det c).1 hc)
  have h3 : ∀ g : (Matrix (Fin m) (Fin m) ℂ), c * (c⁻¹ * g * c) * c⁻¹ = g := fun g => by
    rw [show c * (c⁻¹ * g * c) * c⁻¹ = (c * c⁻¹) * g * (c * c⁻¹) by simp only [Matrix.mul_assoc],
      h2, Matrix.one_mul, Matrix.mul_one]
  have h4 : ∀ g : (Matrix (Fin m) (Fin m) ℂ), c⁻¹ * (c * g * c⁻¹) * c = g := fun g => by
    rw [show c⁻¹ * (c * g * c⁻¹) * c = (c⁻¹ * c) * g * (c⁻¹ * c) by simp only [Matrix.mul_assoc],
      h1, Matrix.one_mul, Matrix.mul_one]
  { toFun := fun g => MG.mk hG (c * g.mat * c⁻¹) ((hn _).2 g.mem)
    invFun := fun g => MG.mk hG (c⁻¹ * g.mat * c) ((hn _).1 (by rw [h3]; exact g.mem))
    left_inv := fun g => MG.ext (h4 g.mat)
    right_inv := fun g => MG.ext (h3 g.mat)
    map_mul' := fun a b => MG.ext (by
      change c * (a.mat * b.mat) * c⁻¹ = (c * a.mat * c⁻¹) * (c * b.mat * c⁻¹)
      rw [show (c * a.mat * c⁻¹) * (c * b.mat * c⁻¹) = c * a.mat * (c⁻¹ * c) * b.mat * c⁻¹ by
        simp only [Matrix.mul_assoc], h1]
      simp only [Matrix.mul_assoc, Matrix.one_mul])
    continuous_toFun := MG.continuous_iff.2
      ((continuous_const.matrix_mul MG.continuous_mat).matrix_mul continuous_const)
    continuous_invFun := MG.continuous_iff.2
      ((continuous_const.matrix_mul MG.continuous_mat).matrix_mul continuous_const) }

open Classical in

def modD (hG : IsMatGroup G) (x : (Matrix (Fin m) (Fin m) ℂ)) : ℝ :=
  if hx : x ∈ G then (modularCharacterFun (MG.mk hG x hx) : ℝ) else 1

theorem modD_of_mem {x : (Matrix (Fin m) (Fin m) ℂ)} (hx : x ∈ G) :
    modD hG x = (modularCharacterFun (MG.mk hG x hx) : ℝ) := dif_pos hx

theorem modProps_modD (hG : IsMatGroup G) : ModProps G (modD hG) := by
  refine ⟨fun g hg => ?_, fun a ha b hb => ?_, fun c hc hn g hg => ?_, fun V hVG hV => ?_⟩
  · rw [modD_of_mem hg]; exact_mod_cast modularCharacterFun_pos _
  · rw [modD_of_mem ha, modD_of_mem hb, modD_of_mem (hG.2.2.1 a ha b hb), ← NNReal.coe_mul,
      ← modularCharacterFun_map_mul]
    rfl
  · rw [modD_of_mem hg, modD_of_mem ((hn g).2 hg),
      ← modular_aut (conjAut hG c hc hn) (MG.mk hG g hg)]
    rfl
  · obtain ⟨M, hM⟩ := modular_bdd ((MG.isClosedEmbedding_mat (hG := hG)).isCompact_preimage hV)
    refine ⟨M, fun v hv => ?_⟩
    rw [modD_of_mem (hVG hv)]
    exact hM _ hv

theorem measurable_lmulQ (a : (Matrix (Fin m) (Fin m) ℂ)) : Measurable (lmulQ a) :=
  Continuous.measurable (α := MtM m) (γ := MtM m)
    (Continuous.matrix_mul (A := fun _ : (Matrix (Fin m) (Fin m) ℂ) => a) (B := fun x : (Matrix (Fin m) (Fin m) ℂ) => x) continuous_const
      continuous_id)

theorem measurable_rmulQ (a : (Matrix (Fin m) (Fin m) ℂ)) : Measurable (rmulQ a) :=
  Continuous.measurable (α := MtM m) (γ := MtM m)
    (Continuous.matrix_mul (A := fun x : (Matrix (Fin m) (Fin m) ℂ) => x) (B := fun _ : (Matrix (Fin m) (Fin m) ℂ) => a) continuous_id
      continuous_const)

theorem rightInv_of_modD_one (hG : IsMatGroup G) (h1 : ∀ g ∈ G, modD hG g = 1)
    (μ : Measure (MtM m)) (hμ : IsHaarOnM G μ) : IsRightInvM G μ := by
  obtain ⟨hσ, -, h0, hl⟩ := hμ
  have hι := MG.measurableEmbedding_toM (hG := hG)
  set ν : Measure (MG G hG) := μ.comap MG.toM with hν
  have hmap : ν.map MG.toM = μ := by
    rw [hν, hι.map_comap, MG.range_toM]
    exact restrict_eq_self_of_ae_mem h0
  haveI : SigmaFinite ν := SigmaFinite.of_map ν hι.measurable.aemeasurable (by rwa [hmap])
  haveI : IsMulLeftInvariant ν := ⟨fun g => by
    apply hι.map_injective
    rw [map_map hι.measurable (measurable_const_mul g)]
    have : MG.toM ∘ (fun x : MG G hG => g * x) = lmulQ g.mat ∘ MG.toM := rfl
    rw [this, ← map_map (measurable_lmulQ _) hι.measurable, hmap, hl _ g.mem]⟩
  have hΔ : ∀ g : MG G hG, modularCharacterFun g = 1 := fun g => by
    have := h1 g.mat g.mem
    rw [modD_of_mem g.mem] at this
    exact_mod_cast this
  intro s hs
  have h := map_mul_right_of_modular_one hΔ ν (MG.mk hG s hs)
  have e : rmulQ s ∘ MG.toM = MG.toM ∘ (fun x : MG G hG => x * MG.mk hG s hs) := rfl
  rw [← hmap, map_map (measurable_rmulQ _) hι.measurable, e,
    ← map_map hι.measurable (measurable_mul_const _), h]

theorem exists_modular_function : PI.QuotSetU.UnitaryGroupMassFormula.ModExists := fun _ _ hG =>
  ⟨modD hG, modProps_modD hG, rightInv_of_modD_one hG⟩

end Concrete

end CompanionTheory.D.Upq.ModEx

end
