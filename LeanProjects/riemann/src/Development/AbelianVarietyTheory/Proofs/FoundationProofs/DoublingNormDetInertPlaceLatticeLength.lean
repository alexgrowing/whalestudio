import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.GraphHeightLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableSpanSpanOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleOfValued
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrdLEqNegLog

noncomputable section

namespace GlobalTheory.InertLatLength

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice
open GlobalTheory.LFun (toCompl latAt IsFrameAt)
open GlobalTheory.LFun.InertChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}

def intMap (h : w.under (𝓞 F) = v) : intLoc F E v →+* w.adicCompletionIntegers E :=
  ((toCompl h).comp (intLoc F E v).subtype).codRestrict (w.adicCompletionIntegers E) fun y => toCompl_mem h y.2

theorem intMap_surjective (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) :
    Function.Surjective (intMap h) := by
  intro z
  obtain ⟨y, hy⟩ := (toCompl_bijective hw h).2 (z : w.adicCompletion E)
  have hy' : y ∈ intLoc F E v := (mem_intLoc_iff hw h y).2 (by rw [hy]; exact z.2)
  exact ⟨⟨y, hy'⟩, Subtype.ext hy⟩

def coord (h : w.under (𝓞 F) = v) (a : GL (Fin n) (w.adicCompletion E)) (y : Fin n → Fv F v ⊗[F] E) :
    Fin n → w.adicCompletion E :=
  (a⁻¹).1 *ᵥ (toCompl h ∘ y)

theorem mulVec_coord (h : w.under (𝓞 F) = v) (a : GL (Fin n) (w.adicCompletion E)) (y : Fin n → Fv F v ⊗[F] E) :
    a.1 *ᵥ coord h a y = toCompl h ∘ y := by
  rw [coord, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem mem_latLoc_iff_coord {L : Submodule (𝓞 E) (Fin n → E)} (hw : Formalism.UG.IsInertAt F E v w)
    (h : w.under (𝓞 F) = v) {a : GL (Fin n) (w.adicCompletion E)} (ha : IsFrameAt w L a)
    (y : Fin n → Fv F v ⊗[F] E) :
    y ∈ latLoc F L v ↔ ∀ i, coord h a y i ∈ w.adicCompletionIntegers E := by
  rw [mem_latLoc_iff hw h, ← mulVec_coord h a y]
  exact (ha _).symm

theorem coord_injective (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    (a : GL (Fin n) (w.adicCompletion E)) : Function.Injective (coord h a) := by
  intro y y' e
  have e' : toCompl h ∘ y = toCompl h ∘ y' := by rw [← mulVec_coord, ← mulVec_coord, e]
  exact funext fun i => (toCompl_bijective hw h).1 (congrFun e' i)

theorem coord_add (h : w.under (𝓞 F) = v) (a : GL (Fin n) (w.adicCompletion E)) (y y' : Fin n → Fv F v ⊗[F] E) :
    coord h a (y + y') = coord h a y + coord h a y' := by
  simp only [coord, ← Matrix.mulVec_add]
  congr 1
  funext i
  simp [map_add]

theorem coord_smul (h : w.under (𝓞 F) = v) (a : GL (Fin n) (w.adicCompletion E)) (c : Fv F v ⊗[F] E)
    (y : Fin n → Fv F v ⊗[F] E) :
    coord h a (fun i => c * y i) = toCompl h c • coord h a y := by
  simp only [coord, ← Matrix.mulVec_smul]
  congr 1
  funext i
  simp [map_mul]

theorem coord_mulVec (h : w.under (𝓞 F) = v) (a : GL (Fin n) (w.adicCompletion E)) (α : GL (Fin n) (Fv F v ⊗[F] E))
    (y : Fin n → Fv F v ⊗[F] E) :
    coord h a (α.1 *ᵥ y) = (a⁻¹ * Formalism.UG.bc (toCompl h) α * a).1 *ᵥ coord h a y := by
  rw [coord, comp_mulVec, ← mulVec_coord h a y, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Units.val_mul, Units.val_mul]

theorem exists_coord_eq (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    (a : GL (Fin n) (w.adicCompletion E)) (z : Fin n → w.adicCompletion E) : ∃ y, coord h a y = z := by
  obtain ⟨y, hy⟩ := (toCompl_bijective hw h).2.comp_left (a.1 *ᵥ z)
  refine ⟨y, ?_⟩
  rw [coord, show toCompl h ∘ y = a.1 *ᵥ z from hy, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

section Main

variable {L : Submodule (𝓞 E) (Fin n → E)} (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
  {a : GL (Fin n) (w.adicCompletion E)} (ha : IsFrameAt w L a)

def phi : latLoc F L v →ₛₗ[intMap h] (Fin n → w.adicCompletionIntegers E) where
  toFun y i := ⟨coord h a y i, (mem_latLoc_iff_coord hw h ha y).1 y.2 i⟩
  map_add' y y' := funext fun i => Subtype.ext (congrFun (coord_add h a y y') i)
  map_smul' r y := funext fun i => Subtype.ext (congrFun (coord_smul h a r.1 y.1) i)

theorem coe_phi (y : latLoc F L v) (i : Fin n) : (phi hw h ha y i : w.adicCompletion E) = coord h a y i := rfl

include hw ha in
theorem phi_surjective : Function.Surjective (phi hw h ha) := by
  intro z
  obtain ⟨y, hy⟩ := exists_coord_eq hw h a (fun i => (z i : w.adicCompletion E))
  have hm : y ∈ latLoc F L v := (mem_latLoc_iff_coord hw h ha y).2 fun i => by rw [hy]; exact (z i).2
  exact ⟨⟨y, hm⟩, funext fun i => Subtype.ext (congrFun hy i)⟩

variable {M : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E)} {α : GL (Fin n) (Fv F v ⊗[F] E)}

include hw ha in
theorem integral_entries (hM : M ≤ latLoc F L v) (hα : ∀ y, y ∈ M ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x) (i j : Fin n) :
    (a⁻¹ * Formalism.UG.bc (toCompl h) α * a).1 i j ∈ w.adicCompletionIntegers E := by
  obtain ⟨y, hy⟩ := exists_coord_eq hw h a (Pi.single j 1)
  have hm : y ∈ latLoc F L v := (mem_latLoc_iff_coord hw h ha y).2 fun k => by
    rw [hy]
    by_cases e : k = j
    · subst e; simp only [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne e]; exact zero_mem _
  have h1 := (mem_latLoc_iff_coord hw h ha _).1 (hM ((hα _).2 ⟨y, hm, rfl⟩)) i
  rw [coord_mulVec, hy, Matrix.mulVec_single_one] at h1
  exact h1

def intMat (hM : M ≤ latLoc F L v) (hα : ∀ y, y ∈ M ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x) :
    Matrix (Fin n) (Fin n) (w.adicCompletionIntegers E) :=
  Matrix.of fun i j => ⟨_, integral_entries hw h ha hM hα i j⟩

variable (hM : M ≤ latLoc F L v) (hα : ∀ y, y ∈ M ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x)

theorem coe_intMat_mulVec (z : Fin n → w.adicCompletionIntegers E) (i : Fin n) :
    ((intMat hw h ha hM hα *ᵥ z) i : w.adicCompletion E) =
      ((a⁻¹ * Formalism.UG.bc (toCompl h) α * a).1 *ᵥ fun j => (z j : w.adicCompletion E)) i := by
  have := RingHom.map_mulVec (w.adicCompletionIntegers E).subtype (intMat hw h ha hM hα) z i
  exact this

theorem submoduleOf_eq :
    M.submoduleOf (latLoc F L v) = (LinearMap.range (intMat hw h ha hM hα).mulVecLin).comap (phi hw h ha) := by
  ext y
  change y.1 ∈ M ↔ _
  rw [hα, Submodule.mem_comap, LinearMap.mem_range]
  constructor
  · rintro ⟨x, hx, e⟩
    refine ⟨phi hw h ha ⟨x, hx⟩, funext fun i => Subtype.ext ?_⟩
    rw [Matrix.mulVecLin_apply, coe_intMat_mulVec, coe_phi, e, coord_mulVec]
    rfl
  · rintro ⟨z, hz⟩
    obtain ⟨x, hx⟩ := exists_coord_eq hw h a (fun i => (z i : w.adicCompletion E))
    have hm : x ∈ latLoc F L v := (mem_latLoc_iff_coord hw h ha x).2 fun i => by rw [hx]; exact (z i).2
    refine ⟨x, hm, coord_injective hw h a (funext fun i => ?_)⟩
    rw [coord_mulVec, hx, ← coe_intMat_mulVec hw h ha hM hα, ← coe_phi hw h ha y]
    exact congrArg (fun t => ((t i : w.adicCompletionIntegers E) : w.adicCompletion E)) hz.symm

def quotMap : (latLoc F L v ⧸ M.submoduleOf (latLoc F L v)) →ₛₗ[intMap h]
    ((Fin n → w.adicCompletionIntegers E) ⧸ LinearMap.range (intMat hw h ha hM hα).mulVecLin) :=
  (M.submoduleOf (latLoc F L v)).mapQ _ (phi hw h ha) (submoduleOf_eq hw h ha hM hα).le

theorem quotMap_bijective : Function.Bijective (quotMap hw h ha hM hα) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun q hq => ?_, fun q => ?_⟩
  · induction q using Submodule.Quotient.induction_on with
    | H y =>
      rw [quotMap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
      rw [Submodule.Quotient.mk_eq_zero, submoduleOf_eq hw h ha hM hα]
      exact hq
  · induction q using Submodule.Quotient.induction_on with
    | H z =>
      obtain ⟨y, rfl⟩ := phi_surjective hw h ha z
      exact ⟨Submodule.Quotient.mk y, rfl⟩

theorem length_eq_addVal :
    Module.length (intLoc F E v) (latLoc F L v ⧸ M.submoduleOf (latLoc F L v)) =
      IsDiscreteValuationRing.addVal _ (intMat hw h ha hM hα).det := by
  haveI : RingHomSurjective (intMap h) := ⟨intMap_surjective hw h⟩
  rw [← GlobalTheory.length_quotient_range_mulVecLin_eq_addVal_det, Module.length, Module.length, WithBot.unbot_inj]
  exact Order.krullDim_eq_of_orderIso
    (Submodule.orderIsoMapComapOfBijective (quotMap hw h ha hM hα) (quotMap_bijective hw h ha hM hα))

theorem coe_det_intMat :
    ((intMat hw h ha hM hα).det : w.adicCompletion E) = toCompl h (Matrix.GeneralLinearGroup.det α).1 := by
  have h1 := RingHom.map_det (w.adicCompletionIntegers E).subtype (intMat hw h ha hM hα)
  have h2 : (w.adicCompletionIntegers E).subtype.mapMatrix (intMat hw h ha hM hα) =
      (a⁻¹ * Formalism.UG.bc (toCompl h) α * a).1 := Matrix.ext fun i j => rfl
  have h3 : Matrix.GeneralLinearGroup.det (a⁻¹ * Formalism.UG.bc (toCompl h) α * a) =
      Matrix.GeneralLinearGroup.det (Formalism.UG.bc (toCompl h) α) := by
    rw [map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
  change (w.adicCompletionIntegers E).subtype _ = _
  rw [h1, h2]
  have h4 := congrArg Units.val h3
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply] at h4
  rw [h4, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rfl

end Main

theorem ordL_eq_addVal {d : w.adicCompletionIntegers E} (hd : d ≠ 0) :
    ∃ m : ℕ, IsDiscreteValuationRing.addVal _ d = m ∧ Formalism.UG.ordL (d : w.adicCompletion E) = m := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
  have hϖ' : Valued.v ϖ = WithZero.exp (-1) := hϖ
  have hle : ϖ ∈ w.adicCompletionIntegers E := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hϖ', ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  let π : w.adicCompletionIntegers E := ⟨ϖ, hle⟩
  have hπ := GlobalTheory.DegreeOneUniformiser.irreducible_of_valued w π hϖ'
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hπ
  refine ⟨m, IsDiscreteValuationRing.addVal_def d u hπ m hu, ?_⟩
  have hc : (d : w.adicCompletion E) = ((u : w.adicCompletionIntegers E) : w.adicCompletion E) * ϖ ^ m := by
    rw [hu, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
  have hv : Valued.v (d : w.adicCompletion E) = WithZero.exp (-(m : ℤ)) := by
    rw [hc, map_mul, map_pow, hϖ', HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 u.isUnit,
      one_mul, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hne : Valued.v (d : w.adicCompletion E) ≠ 0 := by rw [hv]; exact WithZero.exp_ne_zero
  have hz : WithZero.unzero hne = Multiplicative.ofAdd (-(m : ℤ)) :=
    WithZero.coe_inj.1 (by rw [WithZero.coe_unzero, hv]; rfl)
  rw [Formalism.UG.ordL, dif_neg hne, hz]
  simp

theorem main_of_abs (habs : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 F) = v), Formalism.UG.IsInertAt F E v w → ∀ x : (Fv F v ⊗[F] E)ˣ,
    (absEv F E v x : ℝ) = (Formalism.UG.qV F v : ℝ) ^ (-(2 * Formalism.UG.ordL (toCompl h x.1)))) :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)), ∀ P : HeightOneSpectrum (𝓞 E), IsInertUnder v P → ∀ (g : GLoc σ J v) (α : GL (Fin n) (Fv F v ⊗[F] E)), (∀ y : Fin n → Fv F v ⊗[F] E, (y ∈ latLoc F L v ∧ y ∈ latMoved σ J L v g) ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x) → ∃ l : ℕ, latLength σ J L v g = l ∧ absEv F E v (Matrix.GeneralLinearGroup.det α) = ((Ideal.absNorm P.asIdeal : ℕ) : ℝ≥0) ^ (-(l : ℤ)) := by
  intro F E _ _ _ _ _ σ hσ n J hJ L _ v P hP g α hα
  have hw : Formalism.UG.IsInertAt F E v P := hP
  have h : P.under (𝓞 F) = v := (under_eq_iff hw P).2 rfl
  obtain ⟨a, ha⟩ := exists_isFrameAt hw (‹Submodule.IsLattice E L›.fg) (‹Submodule.IsLattice E L›.span_eq_top)
  have hM : latLoc F L v ⊓ latMoved σ J L v g ≤ latLoc F L v := inf_le_left
  have hα' : ∀ y, y ∈ latLoc F L v ⊓ latMoved σ J L v g ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x := fun y => hα y
  have hlen := length_eq_addVal hw h ha hM hα'
  have hdet := coe_det_intMat hw h ha hM hα'
  have hd0 : (intMat hw h ha hM hα').det ≠ 0 := by
    intro e
    rw [e, ZeroMemClass.coe_zero] at hdet
    exact ((Matrix.GeneralLinearGroup.det α).isUnit.map (toCompl h)).ne_zero hdet.symm
  obtain ⟨m, hm1, hm2⟩ := ordL_eq_addVal hd0
  refine ⟨m, hlen.trans hm1, ?_⟩
  have e1 := habs F E σ hσ v P h hw (Matrix.GeneralLinearGroup.det α)
  rw [← hdet, hm2] at e1
  have hq := absNorm_eq hσ.2.2.1 hw
  apply NNReal.eq
  rw [e1, NNReal.coe_zpow, hq, Formalism.UG.qV]
  push_cast
  rw [← zpow_natCast, ← zpow_mul]
  congr 1
  ring

theorem absEv_det_eq_of_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)), ∀ P : HeightOneSpectrum (𝓞 E), IsInertUnder v P → ∀ (g : GLoc σ J v) (α : GL (Fin n) (Fv F v ⊗[F] E)), (∀ y : Fin n → Fv F v ⊗[F] E, (y ∈ latLoc F L v ∧ y ∈ latMoved σ J L v g) ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x) → ∃ l : ℕ, latLength σ J L v g = l ∧ absEv F E v (Matrix.GeneralLinearGroup.det α) = ((Ideal.absNorm P.asIdeal : ℕ) : ℝ≥0) ^ (-(l : ℤ)) :=
  main_of_abs GlobalTheory.AbsInert.absEv_inert

end GlobalTheory.InertLatLength
