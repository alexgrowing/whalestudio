import Formalism.HermitianCurvature.HermitianCurvatureProofs.LinearFormRadicalRankOne

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.style.haveILetI false

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Dx2.Split Dx2.SplitM

variable {k j ρ : ℕ}

def splitX (x1 : Fin (2 * (1 + ρ) + k + 1) → Fin j → ℂ) :
    ((Fin j → ℂ) × (Fin (2 * ρ + k + 1) → Fin j → ℂ)) × (Fin j → ℂ) :=
  ((x1 (U.eB k 1 ρ (Sum.inl (Sum.inl 0))), fun v => x1 (U.eB k 1 ρ (Sum.inl (Sum.inr v)))),
    x1 (U.eB k 1 ρ (Sum.inr 0)))

private theorem measurePreserving_prod_map {α β γ δ : Type*} {mα : MeasureSpace α} {mβ : MeasureSpace β} {mγ : MeasureSpace γ}
    {mδ : MeasureSpace δ} {f : α → β} {g : γ → δ}
    (hf : MeasurePreserving f volume volume) (hg : MeasurePreserving g volume volume)
    [SFinite (volume : Measure α)] [SFinite (volume : Measure γ)] :
    MeasurePreserving (Prod.map f g) (volume : Measure (α × γ)) (volume : Measure (β × δ)) :=
  hf.prod hg

theorem splitX_mp : MeasurePreserving (splitX (k := k) (j := j) (ρ := ρ)) volume volume := by
  haveI a0_ : SFinite (volume : Measure (ℝ)) := inferInstance
  haveI a1_ : SFinite (volume : Measure (ℂ)) := inferInstance
  haveI a2_ : SFinite (volume : Measure (Fin j → ℂ)) := inferInstance
  haveI a3_ : SFinite (volume : Measure (Fin j → ℝ)) := inferInstance
  haveI a4_ : SFinite (volume : Measure (G.UT j → ℂ)) := inferInstance
  haveI a5_ : SFinite (volume : Measure (Fin (2 * ρ + k + 1) → ℂ)) := inferInstance
  haveI a6_ : SFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin j → ℂ)) := inferInstance
  haveI a7_ : SFinite (volume : Measure (Fin (2 * (1 + ρ) + k + 1) → Fin j → ℂ)) := inferInstance
  haveI a8_ : SFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin 1 → ℂ)) := inferInstance
  haveI a9_ : SFinite (volume : Measure (G.UT 1 → ℂ)) := inferInstance
  haveI a10_ : SFinite (volume : Measure (Fin 1 → ℝ)) := inferInstance
  haveI a11_ : SFinite (volume : Measure (Fin 1 → Fin j → ℂ)) := inferInstance
  haveI a12_ : SFinite (volume : Measure (G.UT (j + 1) → ℂ)) := inferInstance
  haveI a13_ : SFinite (volume : Measure (Fin (j + 1) → ℝ)) := inferInstance
  haveI a14_ : SFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin (j + 1) → ℂ)) := inferInstance
  haveI hP : ∀ {α β : Type} [MeasureSpace α] [MeasureSpace β] [SFinite (volume : Measure α)]
      [SFinite (volume : Measure β)], SFinite (volume : Measure (α × β)) := fun {_ _} _ _ _ _ => inferInstance
  have h0 : MeasurePreserving (fun x1 : Fin (2 * (1 + ρ) + k + 1) → Fin j → ℂ =>
      fun i : U.Ix k 1 ρ => x1 (U.eB k 1 ρ i)) volume volume := by
    have := volume_measurePreserving_piCongrLeft (fun _ : U.Ix k 1 ρ => Fin j → ℂ) (U.eB k 1 ρ).symm
    convert this using 1
    funext x1 i
    obtain ⟨i', rfl⟩ := (U.eB k 1 ρ).symm.surjective i
    first
    | simp [MeasurableEquiv.piCongrLeft_apply_apply]
    | simp [Equiv.piCongrLeft_apply_apply]
  have h1 : MeasurePreserving (fun x : U.Ix k 1 ρ → Fin j → ℂ =>
      ((fun i : Fin 1 ⊕ Fin (2 * ρ + k + 1) => x (Sum.inl i)), (fun i : Fin 1 => x (Sum.inr i)))) volume volume :=
    measurePreserving_sumPiEquivProdPi (fun _ => volume)
  have h2 : MeasurePreserving (fun x : Fin 1 ⊕ Fin (2 * ρ + k + 1) → Fin j → ℂ =>
      ((fun i : Fin 1 => x (Sum.inl i)), (fun i : Fin (2 * ρ + k + 1) => x (Sum.inr i)))) volume volume :=
    measurePreserving_sumPiEquivProdPi (fun _ => volume)
  have h3 := MeasurePreserving.comp (measurePreserving_prod_map (MeasurePreserving.prod
    (volume_preserving_funUnique (Fin 1) (Fin j → ℂ))
    (MeasurePreserving.id (volume : Measure (Fin (2 * ρ + k + 1) → Fin j → ℂ))))
    (volume_preserving_funUnique (Fin 1) (Fin j → ℂ)))
    (MeasurePreserving.comp (measurePreserving_prod_map h2 (MeasurePreserving.id (volume : Measure (Fin 1 → Fin j → ℂ))))
      (MeasurePreserving.comp h1 h0))
  exact h3

theorem cy_mp : MeasurePreserving (fun y1 : Fin (2 * ρ + k + 1) → Fin 1 → ℂ => fun v => y1 v 0) volume volume := by
  exact volume_preserving_pi fun _ => volume_preserving_funUnique (Fin 1) ℂ

theorem dy_mp : MeasurePreserving (fun q : (G.UT 1 → ℂ) × (Fin 1 → ℝ) => q.2 0) volume volume := by
  haveI : IsEmpty (G.UT 1) := ⟨fun p => absurd p.2 (by rw [Subsingleton.elim p.1.2 p.1.1]; exact lt_irrefl _)⟩
  haveI : IsProbabilityMeasure (volume : Measure (G.UT 1 → ℂ)) := by
    rw [show (volume : Measure (G.UT 1 → ℂ)) = Measure.pi (fun _ => volume) from rfl, Measure.pi_of_empty]
    infer_instance
  exact (volume_preserving_funUnique (Fin 1) ℝ).comp measurePreserving_snd

abbrev Bq (k j ρ : ℕ) := ((Fin j → ℂ) × (Fin (2 * ρ + k + 1) → ℂ)) × ℝ
abbrev Fq (k j ρ : ℕ) := ((Fin (2 * ρ + k + 1) → Fin j → ℂ) × (Fin j → ℂ)) × ((G.UT j → ℂ) × (Fin j → ℝ))

def srcQ (z : U.RC k j (1 + ρ) × U.RC k 1 ρ) : Bq k j ρ × Fq k j ρ :=
  (((cb z.1, cy z.2), dy z.2), ((cm z.1, ct z.1), z.1.2))

private theorem measurePreserving_prod_swap {α β : Type*} {mα : MeasureSpace α} {mβ : MeasureSpace β}
    [SFinite (volume : Measure α)] [SFinite (volume : Measure β)] :
    MeasurePreserving (Prod.swap : α × β → β × α) volume volume :=
  Measure.measurePreserving_swap

private theorem measurePreserving_prod_assoc {α β γ : Type*} {mα : MeasureSpace α} {mβ : MeasureSpace β} {mγ : MeasureSpace γ}
    [SFinite (volume : Measure α)] [SFinite (volume : Measure β)] [SFinite (volume : Measure γ)] :
    MeasurePreserving (fun p : (α × β) × γ => (p.1.1, (p.1.2, p.2))) volume volume :=
  measurePreserving_prodAssoc volume volume volume

private theorem measurePreserving_prod_assoc_symm {α β γ : Type*} {mα : MeasureSpace α} {mβ : MeasureSpace β} {mγ : MeasureSpace γ}
    [SFinite (volume : Measure α)] [SFinite (volume : Measure β)] [SFinite (volume : Measure γ)] :
    MeasurePreserving (fun p : α × (β × γ) => ((p.1, p.2.1), p.2.2)) volume volume :=
  MeasurePreserving.symm _ (measurePreserving_prodAssoc volume volume volume)

theorem srcQ_mp : MeasurePreserving (srcQ (k := k) (j := j) (ρ := ρ)) volume volume := by
  haveI a0_ : SFinite (volume : Measure (ℝ)) := inferInstance
  haveI a1_ : SFinite (volume : Measure (ℂ)) := inferInstance
  haveI a2_ : SFinite (volume : Measure (Fin j → ℂ)) := inferInstance
  haveI a3_ : SFinite (volume : Measure (Fin j → ℝ)) := inferInstance
  haveI a4_ : SFinite (volume : Measure (G.UT j → ℂ)) := inferInstance
  haveI a5_ : SFinite (volume : Measure (Fin (2 * ρ + k + 1) → ℂ)) := inferInstance
  haveI a6_ : SFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin j → ℂ)) := inferInstance
  haveI a7_ : SFinite (volume : Measure (Fin (2 * (1 + ρ) + k + 1) → Fin j → ℂ)) := inferInstance
  haveI a8_ : SFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin 1 → ℂ)) := inferInstance
  haveI a9_ : SFinite (volume : Measure (G.UT 1 → ℂ)) := inferInstance
  haveI a10_ : SFinite (volume : Measure (Fin 1 → ℝ)) := inferInstance
  haveI a11_ : SFinite (volume : Measure (Fin 1 → Fin j → ℂ)) := inferInstance
  haveI a12_ : SFinite (volume : Measure (G.UT (j + 1) → ℂ)) := inferInstance
  haveI a13_ : SFinite (volume : Measure (Fin (j + 1) → ℝ)) := inferInstance
  haveI a14_ : SFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin (j + 1) → ℂ)) := inferInstance
  haveI hP : ∀ {α β : Type} [MeasureSpace α] [MeasureSpace β] [SFinite (volume : Measure α)]
      [SFinite (volume : Measure β)], SFinite (volume : Measure (α × β)) := fun {_ _} _ _ _ _ => inferInstance
  have g0 := measurePreserving_prod_map (measurePreserving_prod_map (splitX_mp (k := k) (j := j) (ρ := ρ)) (MeasurePreserving.id (volume : Measure ((G.UT j → ℂ) × (Fin j → ℝ)))))
    (measurePreserving_prod_map (cy_mp (k := k) (ρ := ρ)) dy_mp)
  have g1 := MeasurePreserving.comp (measurePreserving_prod_map (measurePreserving_prod_map measurePreserving_prod_swap (MeasurePreserving.id _)) (MeasurePreserving.id _)) g0
  have g2 := MeasurePreserving.comp (measurePreserving_prod_map measurePreserving_prod_assoc (MeasurePreserving.id _)) g1
  have g3 := MeasurePreserving.comp (measurePreserving_prod_map (measurePreserving_prod_map (MeasurePreserving.id _) (measurePreserving_prod_map measurePreserving_prod_swap (MeasurePreserving.id _))) (MeasurePreserving.id _)) g2
  have g4 := MeasurePreserving.comp measurePreserving_prod_assoc g3
  have g5 := MeasurePreserving.comp (measurePreserving_prod_map (MeasurePreserving.id _) measurePreserving_prod_swap) g4
  have g6 := MeasurePreserving.comp measurePreserving_prod_assoc_symm g5
  have g7 := MeasurePreserving.comp (measurePreserving_prod_map measurePreserving_prod_assoc_symm (MeasurePreserving.id _)) g6
  exact g7

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P.PBH

open Dx2.Split Dx2.SplitM

variable {k j ρ : ℕ}

def uuQ (cy' : Fin (2 * ρ + k + 1) → ℂ) (cm' : Fin (2 * ρ + k + 1) → Fin j → ℂ) : Fin j → ℂ :=
  Matrix.vecMul (Matrix.vecMul (star cy') (Hpk k ρ)) (Matrix.of cm')

def uuQ' (cy' : Fin (2 * ρ + k + 1) → ℂ) (cm' : Fin (2 * ρ + k + 1) → Fin j → ℂ) : Fin j → ℂ :=
  ((Matrix.of cm')ᴴ * Hpk k ρ) *ᵥ cy'

def outerProductMatrix (b : Bq k j ρ) : Fin (2 * ρ + k + 1) → Fin j → ℂ := fun v a => b.1.2 v * b.1.1 a

def rrQ (b : Bq k j ρ) (cm' : Fin (2 * ρ + k + 1) → Fin j → ℂ) : Fin j → ℂ :=
  -(1 / 2 : ℂ) • uuQ b.1.2 cm' + (Complex.I * (b.2 : ℂ)) • b.1.1

def dltQ (b : Bq k j ρ) (cm' : Fin (2 * ρ + k + 1) → Fin j → ℂ) (ct' : Fin j → ℂ) : Matrix (Fin j) (Fin j) ℂ :=
  (1 / 2 : ℂ) • (Matrix.vecMulVec (star b.1.1) ct' - Matrix.vecMulVec (star ct') b.1.1) +
    (1 / 2 : ℂ) • (Matrix.vecMulVec (uuQ' b.1.2 cm') b.1.1 - (Matrix.vecMulVec (uuQ' b.1.2 cm') b.1.1)ᴴ) +
    (Complex.I * (b.2 : ℂ)) • Matrix.vecMulVec (star b.1.1) b.1.1

def psiQ (b : Bq k j ρ) (f : Fq k j ρ) : Fq k j ρ :=
  ((f.1.1 + outerProductMatrix b, f.1.2 + rrQ b f.1.1),
    (f.2.1 + fun p => dltQ b f.1.1 f.1.2 p.1.1 p.1.2, f.2.2 + fun a => (dltQ b f.1.1 f.1.2 a a).im))

def phiQ (b : Bq k j ρ) : Bq k j ρ := ((-(G.wMat j *ᵥ b.1.1), b.1.2), b.2)

def coreQ (p : Bq k j ρ × Fq k j ρ) : Bq k j ρ × Fq k j ρ := (phiQ p.1, psiQ p.1 p.2)

theorem phiQ_mp : MeasurePreserving (phiQ (k := k) (j := j) (ρ := ρ)) volume volume := by
  haveI hP : ∀ {α β : Type} [MeasureSpace α] [MeasureSpace β] [SFinite (volume : Measure α)]
      [SFinite (volume : Measure β)], SFinite (volume : Measure (α × β)) := fun {_ _} _ _ _ _ => inferInstance
  have hw : ∀ v : Fin j → ℂ, G.wMat j *ᵥ v = fun i : Fin j => v i.rev := by
    intro v; funext i; simp [G.wMat, Matrix.mulVec, dotProduct]
  have hr : MeasurePreserving (fun v : Fin j → ℂ => fun i : Fin j => v i.rev) volume volume := by
    have := volume_measurePreserving_piCongrLeft (fun _ : Fin j => ℂ) Fin.revPerm
    convert this using 1
    funext v i
    obtain ⟨i', rfl⟩ := Fin.revPerm.surjective i
    first
    | (rw [MeasurableEquiv.piCongrLeft_apply_apply]; simp)
    | (rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]; simp)
  have hn : MeasurePreserving (fun v : Fin j → ℂ => -(G.wMat j *ᵥ v)) volume volume := by
    simp_rw [hw]
    first
    | exact (Measure.measurePreserving_neg volume).comp hr
    | exact (volume_preserving_pi fun _ => Measure.measurePreserving_neg (volume : Measure ℂ)).comp hr
  exact measurePreserving_prod_map (measurePreserving_prod_map hn (MeasurePreserving.id _)) (MeasurePreserving.id _)

theorem cont_uuQ (cy' : Fin (2 * ρ + k + 1) → ℂ) :
    Continuous (fun cm' : Fin (2 * ρ + k + 1) → Fin j → ℂ => uuQ (k := k) (ρ := ρ) cy' cm') := by
  refine continuous_pi fun a => ?_
  simp only [uuQ, Matrix.vecMul, dotProduct, Matrix.of_apply]
  fun_prop

theorem cont_uuQ' (cy' : Fin (2 * ρ + k + 1) → ℂ) :
    Continuous (fun cm' : Fin (2 * ρ + k + 1) → Fin j → ℂ => uuQ' (k := k) (ρ := ρ) cy' cm') := by
  refine continuous_pi fun a => ?_
  simp only [uuQ', Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  fun_prop

theorem cont_dltQ (b : Bq k j ρ) :
    Continuous (fun q : (Fin (2 * ρ + k + 1) → Fin j → ℂ) × (Fin j → ℂ) => dltQ b q.1 q.2) := by
  refine continuous_pi fun a => continuous_pi fun c => ?_
  simp only [dltQ, uuQ', Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.vecMulVec_apply,
    Matrix.conjTranspose_apply, Pi.star_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.of_apply]
  fun_prop

theorem psiQ_mp (b : Bq k j ρ) : MeasurePreserving (psiQ b) volume volume := by
  haveI a0_ : SFinite (volume : Measure (ℝ)) := inferInstance
  haveI a1_ : SFinite (volume : Measure (ℂ)) := inferInstance
  haveI a2_ : SFinite (volume : Measure (Fin j → ℂ)) := inferInstance
  haveI a3_ : SFinite (volume : Measure (Fin j → ℝ)) := inferInstance
  haveI a4_ : SFinite (volume : Measure (G.UT j → ℂ)) := inferInstance
  haveI a5_ : SFinite (volume : Measure (Fin (2 * ρ + k + 1) → ℂ)) := inferInstance
  haveI a6_ : SFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin j → ℂ)) := inferInstance
  haveI a7_ : SFinite (volume : Measure (Fin (2 * (1 + ρ) + k + 1) → Fin j → ℂ)) := inferInstance
  haveI a8_ : SFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin 1 → ℂ)) := inferInstance
  haveI a9_ : SFinite (volume : Measure (G.UT 1 → ℂ)) := inferInstance
  haveI a10_ : SFinite (volume : Measure (Fin 1 → ℝ)) := inferInstance
  haveI a11_ : SFinite (volume : Measure (Fin 1 → Fin j → ℂ)) := inferInstance
  haveI a12_ : SFinite (volume : Measure (G.UT (j + 1) → ℂ)) := inferInstance
  haveI a13_ : SFinite (volume : Measure (Fin (j + 1) → ℝ)) := inferInstance
  haveI a14_ : SFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin (j + 1) → ℂ)) := inferInstance
  haveI hP : ∀ {α β : Type} [MeasureSpace α] [MeasureSpace β] [SFinite (volume : Measure α)]
      [SFinite (volume : Measure β)], SFinite (volume : Measure (α × β)) := fun {_ _} _ _ _ _ => inferInstance
  haveI i1 : SigmaFinite (volume : Measure (G.UT j → ℂ)) := inferInstance
  haveI i2 : SigmaFinite (volume : Measure (Fin j → ℝ)) := inferInstance
  haveI i3 : SFinite (volume : Measure ((G.UT j → ℂ) × (Fin j → ℝ))) := inferInstance
  have hu := cont_uuQ (k := k) (j := j) (ρ := ρ) b.1.2
  have h1 : MeasurePreserving (fun p : (Fin (2 * ρ + k + 1) → Fin j → ℂ) × (Fin j → ℂ) =>
      (p.1 + outerProductMatrix b, p.2 + rrQ b p.1)) volume volume := by
    refine (measurePreserving_add_right volume (outerProductMatrix b)).skew_product (μc := volume) (μd := volume) (g := fun a c => c + rrQ b a) ?_ ?_
    · have hc : Continuous fun p : (Fin (2 * ρ + k + 1) → Fin j → ℂ) × (Fin j → ℂ) => p.2 + rrQ b p.1 := by
        unfold rrQ
        fun_prop
      exact hc.measurable
    · exact Filter.Eventually.of_forall fun a => (measurePreserving_add_right volume (rrQ b a)).map_eq
  have hd : Continuous fun x : ((Fin (2 * ρ + k + 1) → Fin j → ℂ) × (Fin j → ℂ)) × ((G.UT j → ℂ) × (Fin j → ℝ)) =>
      dltQ b x.1.1 x.1.2 := (cont_dltQ b).comp continuous_fst
  have h2 := h1.skew_product (μc := volume) (μd := volume)
    (g := fun (p : (Fin (2 * ρ + k + 1) → Fin j → ℂ) × (Fin j → ℂ)) (q : (G.UT j → ℂ) × (Fin j → ℝ)) =>
      q + ((fun r : G.UT j => dltQ b p.1 p.2 r.1.1 r.1.2), (fun a => (dltQ b p.1 p.2 a a).im))) ?_ ?_
  · exact h2
  · refine Continuous.measurable ?_
    refine continuous_snd.add (Continuous.prodMk (continuous_pi fun r => ?_) (continuous_pi fun a => ?_))
    · exact (continuous_apply r.1.2).comp ((continuous_apply r.1.1).comp hd)
    · exact Complex.continuous_im.comp ((continuous_apply a).comp ((continuous_apply a).comp hd))
  · exact Filter.Eventually.of_forall fun p =>
      (measurePreserving_prod_map (measurePreserving_add_right volume (fun r : G.UT j => dltQ b p.1 p.2 r.1.1 r.1.2))
        (measurePreserving_add_right volume (fun a => (dltQ b p.1 p.2 a a).im))).map_eq

theorem cont_psiQ : Continuous (fun p : Bq k j ρ × Fq k j ρ => psiQ p.1 p.2) := by
  refine Continuous.prodMk (Continuous.prodMk ?_ ?_) (Continuous.prodMk ?_ ?_) <;>
    refine continuous_pi fun a => ?_ <;> (try refine continuous_pi fun c => ?_) <;>
    simp only [psiQ, outerProductMatrix, rrQ, dltQ, uuQ, uuQ', Pi.add_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, Pi.star_apply, smul_eq_mul,
      Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.mul_apply, Matrix.of_apply, Pi.smul_apply,
      Pi.neg_apply] <;>
    fun_prop

theorem coreQ_mp : MeasurePreserving (coreQ (k := k) (j := j) (ρ := ρ)) volume volume := by
  haveI a0_ : SFinite (volume : Measure (ℝ)) := inferInstance
  haveI a1_ : SFinite (volume : Measure (ℂ)) := inferInstance
  haveI a2_ : SFinite (volume : Measure (Fin j → ℂ)) := inferInstance
  haveI a3_ : SFinite (volume : Measure (Fin j → ℝ)) := inferInstance
  haveI a4_ : SFinite (volume : Measure (G.UT j → ℂ)) := inferInstance
  haveI a5_ : SFinite (volume : Measure (Fin (2 * ρ + k + 1) → ℂ)) := inferInstance
  haveI a6_ : SFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin j → ℂ)) := inferInstance
  haveI a7_ : SFinite (volume : Measure (Fin (2 * (1 + ρ) + k + 1) → Fin j → ℂ)) := inferInstance
  haveI a8_ : SFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin 1 → ℂ)) := inferInstance
  haveI a9_ : SFinite (volume : Measure (G.UT 1 → ℂ)) := inferInstance
  haveI a10_ : SFinite (volume : Measure (Fin 1 → ℝ)) := inferInstance
  haveI a11_ : SFinite (volume : Measure (Fin 1 → Fin j → ℂ)) := inferInstance
  haveI a12_ : SFinite (volume : Measure (G.UT (j + 1) → ℂ)) := inferInstance
  haveI a13_ : SFinite (volume : Measure (Fin (j + 1) → ℝ)) := inferInstance
  haveI a14_ : SFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin (j + 1) → ℂ)) := inferInstance
  haveI hP : ∀ {α β : Type} [MeasureSpace α] [MeasureSpace β] [SFinite (volume : Measure α)]
      [SFinite (volume : Measure β)], SFinite (volume : Measure (α × β)) := fun {_ _} _ _ _ _ => inferInstance
  haveI o1 : SecondCountableTopology (G.UT j → ℂ) := inferInstance
  haveI o2 : OpensMeasurableSpace (Fq k j ρ) := inferInstance
  haveI o3 : OpensMeasurableSpace (Bq k j ρ) := inferInstance
  haveI o4 : OpensMeasurableSpace (Bq k j ρ × Fq k j ρ) := inferInstance
  exact phiQ_mp.skew_product (μc := volume) (μd := volume) (g := psiQ) cont_psiQ.measurable
    (Filter.Eventually.of_forall fun b => (psiQ_mp b).map_eq)

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P.PBH

open Dx2.Split Dx2.SplitM

variable {k j ρ : ℕ}

def consR {α : Type*} [MeasurableSpace α] (p : (Fin j → α) × α) : Fin (j + 1) → α :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (j + 1) => α) 0).symm (p.2, p.1)

theorem consR_zero {α : Type*} [MeasurableSpace α] (p : (Fin j → α) × α) : consR p 0 = p.2 := by
  first
  | simp [consR]
  | simp [consR, MeasurableEquiv.piFinSuccAbove_symm_apply]
  | rfl

theorem consR_succ {α : Type*} [MeasurableSpace α] (p : (Fin j → α) × α) (b : Fin j) : consR p b.succ = p.1 b := by
  first
  | simp [consR]
  | simp [consR, MeasurableEquiv.piFinSuccAbove_symm_apply]
  | rfl

theorem consR_mp {α : Type*} [MeasureSpace α] [SigmaFinite (volume : Measure α)] :
    MeasurePreserving (consR (j := j) (α := α)) volume volume := by
  exact (MeasurePreserving.symm _ (measurePreserving_piFinSuccAbove (fun _ => (volume : Measure α)) 0)).comp
    Measure.measurePreserving_swap

def combF (p : (Fin (2 * ρ + k + 1) → Fin j → ℂ) × (Fin (2 * ρ + k + 1) → ℂ)) :
    Fin (2 * ρ + k + 1) → Fin (j + 1) → ℂ := fun v => consR (p.1 v, p.2 v)

theorem combF_mp : MeasurePreserving (combF (k := k) (j := j) (ρ := ρ)) volume volume := by
  exact (volume_preserving_pi fun _ => consR_mp).comp
    (MeasurePreserving.symm _ (measurePreserving_arrowProdEquivProdArrow _ _ _ (fun _ => volume) (fun _ => volume)))

def tgtQ (p : Bq k j ρ × Fq k j ρ) : U.RC k (j + 1) ρ × (Fin 1 → Fin j → ℂ) :=
  ((combF (p.2.1.1, p.1.1.2), (combU (p.2.1.2, p.2.2.1), consR (p.2.2.2, p.1.2))), fun _ => p.1.1.1)

def rearrQ (p : Bq k j ρ × Fq k j ρ) :
    (((Fin (2 * ρ + k + 1) → Fin j → ℂ) × (Fin (2 * ρ + k + 1) → ℂ)) ×
      (((Fin j → ℂ) × (G.UT j → ℂ)) × ((Fin j → ℝ) × ℝ))) × (Fin j → ℂ) :=
  (((p.2.1.1, p.1.1.2), ((p.2.1.2, p.2.2.1), (p.2.2.2, p.1.2))), p.1.1.1)

theorem rearrQ_mp : MeasurePreserving (rearrQ (k := k) (j := j) (ρ := ρ)) volume volume := by
  haveI a0_ : SFinite (volume : Measure (ℝ)) := inferInstance
  haveI a1_ : SFinite (volume : Measure (ℂ)) := inferInstance
  haveI a2_ : SFinite (volume : Measure (Fin j → ℂ)) := inferInstance
  haveI a3_ : SFinite (volume : Measure (Fin j → ℝ)) := inferInstance
  haveI a4_ : SFinite (volume : Measure (G.UT j → ℂ)) := inferInstance
  haveI a5_ : SFinite (volume : Measure (Fin (2 * ρ + k + 1) → ℂ)) := inferInstance
  haveI a6_ : SFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin j → ℂ)) := inferInstance
  haveI a7_ : SFinite (volume : Measure (Fin (2 * (1 + ρ) + k + 1) → Fin j → ℂ)) := inferInstance
  haveI a8_ : SFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin 1 → ℂ)) := inferInstance
  haveI a9_ : SFinite (volume : Measure (G.UT 1 → ℂ)) := inferInstance
  haveI a10_ : SFinite (volume : Measure (Fin 1 → ℝ)) := inferInstance
  haveI a11_ : SFinite (volume : Measure (Fin 1 → Fin j → ℂ)) := inferInstance
  haveI a12_ : SFinite (volume : Measure (G.UT (j + 1) → ℂ)) := inferInstance
  haveI a13_ : SFinite (volume : Measure (Fin (j + 1) → ℝ)) := inferInstance
  haveI a14_ : SFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin (j + 1) → ℂ)) := inferInstance
  haveI hP : ∀ {α β : Type} [MeasureSpace α] [MeasureSpace β] [SFinite (volume : Measure α)]
      [SFinite (volume : Measure β)], SFinite (volume : Measure (α × β)) := fun {_ _} _ _ _ _ => inferInstance
  have g0 := (MeasurePreserving.id (volume : Measure (Bq k j ρ × Fq k j ρ)))
  have g1 := MeasurePreserving.comp (measurePreserving_prod_map measurePreserving_prod_assoc (MeasurePreserving.id _)) g0
  have g2 := MeasurePreserving.comp (measurePreserving_prod_map measurePreserving_prod_swap (MeasurePreserving.id _)) g1
  have g3 := MeasurePreserving.comp measurePreserving_prod_swap g2
  have g4 := MeasurePreserving.comp measurePreserving_prod_assoc_symm g3
  have g5 := MeasurePreserving.comp (measurePreserving_prod_map (measurePreserving_prod_map measurePreserving_prod_assoc (MeasurePreserving.id _)) (MeasurePreserving.id _)) g4
  have g6 := MeasurePreserving.comp (measurePreserving_prod_map (measurePreserving_prod_map (measurePreserving_prod_map (MeasurePreserving.id _) measurePreserving_prod_assoc_symm) (MeasurePreserving.id _)) (MeasurePreserving.id _)) g5
  have g7 := MeasurePreserving.comp (measurePreserving_prod_map (measurePreserving_prod_map measurePreserving_prod_assoc_symm (MeasurePreserving.id _)) (MeasurePreserving.id _)) g6
  have g8 := MeasurePreserving.comp (measurePreserving_prod_map measurePreserving_prod_assoc (MeasurePreserving.id _)) g7
  have g9 := MeasurePreserving.comp (measurePreserving_prod_map (measurePreserving_prod_map (MeasurePreserving.id _) measurePreserving_prod_assoc_symm) (MeasurePreserving.id _)) g8
  have g10 := MeasurePreserving.comp (measurePreserving_prod_map (measurePreserving_prod_map (MeasurePreserving.id _) (measurePreserving_prod_map measurePreserving_prod_swap (MeasurePreserving.id _))) (MeasurePreserving.id _)) g9
  have g11 := MeasurePreserving.comp (measurePreserving_prod_map (measurePreserving_prod_map (MeasurePreserving.id _) measurePreserving_prod_assoc) (MeasurePreserving.id _)) g10
  have g12 := MeasurePreserving.comp (measurePreserving_prod_map measurePreserving_prod_assoc (MeasurePreserving.id _)) g11
  have g13 := MeasurePreserving.comp (measurePreserving_prod_map (measurePreserving_prod_map (MeasurePreserving.id _) measurePreserving_prod_assoc_symm) (MeasurePreserving.id _)) g12
  have g14 := MeasurePreserving.comp (measurePreserving_prod_map (measurePreserving_prod_map (MeasurePreserving.id _) (measurePreserving_prod_map measurePreserving_prod_swap (MeasurePreserving.id _))) (MeasurePreserving.id _)) g13
  have g15 := MeasurePreserving.comp (measurePreserving_prod_map (measurePreserving_prod_map (MeasurePreserving.id _) measurePreserving_prod_assoc) (MeasurePreserving.id _)) g14
  have g16 := MeasurePreserving.comp (measurePreserving_prod_map measurePreserving_prod_assoc_symm (MeasurePreserving.id _)) g15
  exact g16

theorem tgtQ_mp : MeasurePreserving (tgtQ (k := k) (j := j) (ρ := ρ)) volume volume := by
  haveI a0_ : SFinite (volume : Measure (ℝ)) := inferInstance
  haveI a1_ : SFinite (volume : Measure (ℂ)) := inferInstance
  haveI a2_ : SFinite (volume : Measure (Fin j → ℂ)) := inferInstance
  haveI a3_ : SFinite (volume : Measure (Fin j → ℝ)) := inferInstance
  haveI a4_ : SFinite (volume : Measure (G.UT j → ℂ)) := inferInstance
  haveI a5_ : SFinite (volume : Measure (Fin (2 * ρ + k + 1) → ℂ)) := inferInstance
  haveI a6_ : SFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin j → ℂ)) := inferInstance
  haveI a7_ : SFinite (volume : Measure (Fin (2 * (1 + ρ) + k + 1) → Fin j → ℂ)) := inferInstance
  haveI a8_ : SFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin 1 → ℂ)) := inferInstance
  haveI a9_ : SFinite (volume : Measure (G.UT 1 → ℂ)) := inferInstance
  haveI a10_ : SFinite (volume : Measure (Fin 1 → ℝ)) := inferInstance
  haveI a11_ : SFinite (volume : Measure (Fin 1 → Fin j → ℂ)) := inferInstance
  haveI a12_ : SFinite (volume : Measure (G.UT (j + 1) → ℂ)) := inferInstance
  haveI a13_ : SFinite (volume : Measure (Fin (j + 1) → ℝ)) := inferInstance
  haveI a14_ : SFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin (j + 1) → ℂ)) := inferInstance
  haveI hP : ∀ {α β : Type} [MeasureSpace α] [MeasureSpace β] [SFinite (volume : Measure α)]
      [SFinite (volume : Measure β)], SFinite (volume : Measure (α × β)) := fun {_ _} _ _ _ _ => inferInstance
  have hc : MeasurePreserving (fun x : Fin j → ℂ => fun _ : Fin 1 => x) volume volume := by
    convert MeasurePreserving.symm _ (volume_preserving_funUnique (Fin 1) (Fin j → ℂ)) using 1
    all_goals first
      | rfl
      | (funext x i; rw [Subsingleton.elim i default]; first | rfl | simp)
  exact MeasurePreserving.comp (measurePreserving_prod_map (measurePreserving_prod_map (combF_mp (k := k) (j := j) (ρ := ρ))
    (measurePreserving_prod_map combU_mp consR_mp)) hc) rearrQ_mp

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P.PBH

open Dx2.Split Dx2.SplitM

variable {k j ρ : ℕ}

theorem dltQ_eq (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) :
    dltQ (((cb x, cy y), dy y) : Bq k j ρ) (cm x) (ct x) = dlt x y := by
  rfl

theorem rrQ_eq (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) :
    ct x + rrQ (((cb x, cy y), dy y) : Bq k j ρ) (cm x) = r0 x y := by
  unfold rrQ uuQ r0
  simp only [Matrix.vecMul_vecMul, neg_smul, sub_eq_add_neg, add_assoc]
  rfl

theorem PsiL_eq (z : U.RC k j (1 + ρ) × U.RC k 1 ρ) :
    (XC z.1 z.2, aC z.1) = tgtQ (coreQ (srcQ z)) := by
  obtain ⟨x, y⟩ := z
  have key : ∀ (r : Fin j → ℂ) (u : G.UT j → ℂ) (s : Fin j ⊕ G.UT j), combU (r, u) (eZ s) = Sum.elim r u s := by
    intro r u s
    simp only [combU]
    first
    | (rw [MeasurableEquiv.piCongrLeft_apply_apply]; cases s <;> rfl)
    | (rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]; cases s <;> rfl)
  simp only [XC, aC, tgtQ, coreQ, psiQ, phiQ, srcQ, Prod.mk.injEq]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · funext v b
    refine Fin.cases ?_ (fun b' => ?_) b
    · simp only [combF, consR_zero, CX, Fin.cases_zero]
      try rfl
    · simp only [combF, consR_succ, CX, outerProductMatrix, Fin.cases_succ, Pi.add_apply]
      try rfl
  · funext q
    obtain ⟨s, rfl⟩ := (eZ (j := j)).surjective q
    rw [key]
    rcases s with b | p
    · change SX x y 0 b.succ = _
      simp only [Sum.elim_inl, rrQ_eq, SX, Fin.cases_zero, Fin.cases_succ]
    · change SX x y p.1.1.succ p.1.2.succ = _
      simp only [Sum.elim_inr, Pi.add_apply, dltQ_eq, SX, Fin.cases_succ]
      congr 1
      simp [U.skewOf, G.strictUpper, Matrix.conjTranspose_apply, p.2, not_lt_of_gt p.2,
        Matrix.diagonal_apply_ne _ (ne_of_lt p.2)]
  · funext a
    refine Fin.cases ?_ (fun a' => ?_) a
    · simp [SX, consR_zero]
    · simp [SX, consR_succ, U.skewOf, G.strictUpper, dltQ_eq]
  · funext c b
    simp [G.wMat, Matrix.mulVec, dotProduct]
    rfl

theorem PsiL_mp : MeasurePreserving (fun z : U.RC k j (1 + ρ) × U.RC k 1 ρ => (XC z.1 z.2, aC z.1)) volume volume := by
  have e : (fun z : U.RC k j (1 + ρ) × U.RC k 1 ρ => (XC z.1 z.2, aC z.1)) = tgtQ ∘ coreQ ∘ srcQ :=
    funext PsiL_eq
  rw [e]
  exact tgtQ_mp.comp (coreQ_mp.comp srcQ_mp)

end Formalism.FourierDecayAlt.P.PBH
