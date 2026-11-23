import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterEigenvectorOfCommutingRepresentat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosetsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosetsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

noncomputable section

open TensorProduct Formalism.UG

namespace GlobalTheory.OneAct

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

theorem compAt_conjAL (z : AL L) :
    compAt L v (conjAL L z) = Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom
      (v.adicCompletion (maximalRealSubfield L)) (compAt L v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem compAt_mem_tensInt {z : AL L} (hz : z ∈ ALint L) :
    compAt L v z ∈ tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L))
      (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v) := by
  have key : ALint L ≤ (tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L))
      (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v)).comap (compAt L v) := by
    rw [ALint, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · apply Subring.subset_closure
      left
      exact ⟨⟨(y : L), y, rfl⟩, by rw [GlobalTheory.InertUmax.compAt_tmul]; rfl⟩
    · apply Subring.subset_closure
      right
      exact ⟨⟨a v, ha v⟩, by rw [GlobalTheory.InertUmax.compAt_tmul]⟩
  exact key hz

theorem loc_mem_GU (Dv : InertDatum L n v w) (x : GAf L n) : Dv.loc x ∈ GU Dv.σw n := by
  set φ : AL L →+* w.adicCompletion L := (Dv.e : _ →+* _).comp (compAt L v) with hφdef
  have hφ : ∀ z, φ (conjAL L z) = Dv.σw (φ z) := fun z => by
    simp only [φ, RingHom.comp_apply, compAt_conjAL]
    exact Dv.comm _
  have hX : ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      conjT (conjAL L) ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := x.2
  have hX' := mul_eq_one_comm.mp hX
  set A : Matrix (Fin n) (Fin n) (w.adicCompletion L) :=
    ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map φ with hAdef
  have hA : cT Dv.σw A * A = 1 := by
    have : cT Dv.σw A = (conjT (conjAL L) ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))).map φ := by
      ext i j; simp [cT, conjT, A, hφ]
    rw [this, ← Matrix.map_mul, hX', Matrix.map_one _ (map_zero _) (map_one _)]
  have hloc : ((Dv.loc x : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) =
      ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) * A *
        (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) := rfl
  have hPP : cT Dv.σw ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
      cT Dv.σw (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) = 1 := by
    rw [← cT_mul, Units.mul_inv, cT_one]
  have hPP' : (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
      ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) = 1 :=
    Units.mul_inv _
  show cT Dv.σw ((Dv.loc x : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
      antiJ (w.adicCompletion L) n *
      ((Dv.loc x : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) =
      antiJ (w.adicCompletion L) n
  rw [← Dv.Panti, hloc, cT_mul, cT_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (cT Dv.σw _) (cT Dv.σw (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L))), hPP,
    Matrix.one_mul, ← Matrix.mul_assoc (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)), hPP',
    Matrix.one_mul, ← Matrix.mul_assoc (cT Dv.σw A) A, hA, Matrix.one_mul]

theorem mem_range_of_int {K : Type} [Field K] (S : Subring K) (g : GL (Fin n) K)
    (h1 : ∀ i j, (g : Matrix (Fin n) (Fin n) K) i j ∈ S)
    (h2 : ∀ i j, ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ S) :
    g ∈ (Formalism.UG.bc (n := Fin n) S.subtype).range := by
  let M : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, h1 i j⟩
  let N : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, h2 i j⟩
  have hM : M.map S.subtype = (g : Matrix (Fin n) (Fin n) K) := by ext i j; rfl
  have hN : N.map S.subtype = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by ext i j; rfl
  have inj : Function.Injective (fun A : Matrix (Fin n) (Fin n) S => A.map S.subtype) := by
    intro A B h; ext i j; exact congrFun (congrFun h i) j
  have hMN : M * N = 1 := inj (by
    simp only [Matrix.map_mul, hM, hN, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
  have hNM : N * M = 1 := inj (by
    simp only [Matrix.map_mul, hM, hN, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])
  refine ⟨⟨M, N, hMN, hNM⟩, Units.ext ?_⟩
  exact hM

theorem loc_entries_int (Dv : InertDatum L n v w) {x : GAf L n} (hx : x ∈ Umax L n) (i j : Fin n) :
    ((Dv.loc x : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈
      intL (w.adicCompletion L) := by
  have hP := GlobalTheory.InertUmax.entries_mem_of_range _ _ Dv.Pint
  have hP' := GlobalTheory.InertUmax.entries_mem_of_range _ _ (inv_mem Dv.Pint)
  have hA : ∀ k l, Dv.e (compAt L v (((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) k l)) ∈
      intL (w.adicCompletion L) := fun k l => (Dv.integ _).1 (compAt_mem_tensInt (hx k l))
  simp only [InertDatum.loc, Units.val_mul, Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _
    (Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hP' i l) (hA l k)) (hP k j)

theorem loc_mem_KU (Dv : InertDatum L n v w) {x : GAf L n} (hx : x ∈ Umax L n) :
    (⟨Dv.loc x, loc_mem_GU Dv x⟩ : GU Dv.σw n) ∈ KU Dv.σw n := by
  refine ⟨loc_mem_GU Dv x, mem_range_of_int _ _ (loc_entries_int Dv hx) ?_⟩
  have : (Dv.loc x)⁻¹ = Dv.loc x⁻¹ := by
    rw [show Dv.loc x⁻¹ = GlobalTheory.SatInd.CosetFin.locHom Dv x⁻¹ from rfl, map_inv]; rfl
  show ∀ i j, (((Dv.loc x)⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈ _
  rw [this]
  exact loc_entries_int Dv (inv_mem hx)

end GlobalTheory.OneAct

theorem GlobalTheory.OneAct.heckeFunI_unit : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (f : GAf L n → W), (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv (dosetInd ℂ (KU Dv.σw n) 1) f = f := by
  intro L _ _ _ n v w Dv U hU W _ _ f hf
  funext g
  unfold heckeFunI
  have hone : TrivOutside {v} (1 : GAf L n) := by
    intro u _
    show ((1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L u) = 1
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hdK : ∀ y : GU Dv.σw n, y ∈ (DoubleCoset.doubleCoset (1 : GU Dv.σw n) (KU Dv.σw n : Set (GU Dv.σw n))
      (KU Dv.σw n : Set (GU Dv.σw n))) ↔ y ∈ KU Dv.σw n := by
    intro y
    rw [DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      simpa using (KU Dv.σw n).mul_mem ha hb
    · intro hy
      exact ⟨y, hy, 1, (KU Dv.σw n).one_mem, by simp⟩
  rw [finsum_eq_single _ ((1 : GAf L n) : GAf L n ⧸ U)]
  · have hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = ((1 : GAf L n) : GAf L n ⧸ U) ∧ TrivOutside {v} x :=
      ⟨1, rfl, hone⟩
    rw [dif_pos hc]
    obtain ⟨hx1, hx2⟩ := hc.choose_spec
    have hxU : hc.choose ∈ U := by
      have := QuotientGroup.eq.1 hx1
      simpa using this
    have hxM : hc.choose ∈ Umax L n := (hU _ hx2).1 hxU
    have hval : Dv.hval (dosetInd ℂ (KU Dv.σw n) 1) (Dv.loc hc.choose) = 1 := by
      unfold InertDatum.hval
      rw [dif_pos (GlobalTheory.OneAct.loc_mem_GU Dv _)]
      unfold dosetInd
      rw [Set.indicator_of_mem ((hdK _).2 (GlobalTheory.OneAct.loc_mem_KU Dv hxM))]
      rfl
    rw [hval, one_smul]
    exact congrFun (hf _ hxU) g
  · intro c hc1
    split_ifs with hc
    · obtain ⟨hx1, hx2⟩ := hc.choose_spec
      have hval : Dv.hval (dosetInd ℂ (KU Dv.σw n) 1) (Dv.loc hc.choose) = 0 := by
        unfold InertDatum.hval
        split_ifs with hm
        · unfold dosetInd
          apply Set.indicator_of_notMem
          intro hmem
          have hK := (hdK _).1 hmem
          have hxM : hc.choose ∈ Umax L n :=
            GlobalTheory.T.mem_maxCompact_of_trivOutside_local_integral L n v w Dv _ hx2 (fun i j => GlobalTheory.SatInd.CosetFin.entries_int hK i j)
          apply hc1
          rw [← hx1]
          exact QuotientGroup.eq.2 (by simpa using (hU _ hx2).2 hxM)
        · rfl
      rw [hval, zero_smul]
    · rfl
