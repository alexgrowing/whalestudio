import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.BotClassMeas

open GlobalTheory.BotClassDict GlobalTheory.DefiniteClassAvg GlobalTheory.BotFormula

theorem isFrame_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) :
    Formalism.L2.DIV.IsFrame (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Formalism.L2.Col.stdLat E n) := by
  letI : StarRing E := starRingOfComm
  intro z
  rw [inv_one, Units.val_one, Matrix.one_mulVec]
  exact Formalism.L2.Col.mem_latS_std z

variable {D : D7}

theorem isFinPt_finPart (A : HSp D) (hG : A.gram = 1) (k : Formalism.L2.Theta.GA D A) :
    IsFinPt A (finPart A k) (finStd A hG k) := by
  have h1 : finHom A (realPart A k) = 1 := realPart_mem A k
  have h2 : finHom A (finPart A k) = finHom A k := by
    conv_rhs => rw [← realPart_mul_finPart A k]
    rw [map_mul, h1, one_mul]
  refine ⟨finPart_mem A k, rfl, fun i j => ?_⟩
  rw [h2, ← finAdEquiv_toAfE, ← toAfE_finStd A hG]
  rfl

theorem integral_eq_vol_mul_classSum : ∀ {D : D7} (A : HSp D), A.gram = 1 → ∀ (m : Measure (Formalism.L2.Theta.GA D A)) (fd : Set (Formalism.L2.Theta.GA D A)),
    m.IsHaarMeasure → IsFundamentalDomain (GQ A) fd m →
    ∃ v : ℂ, v ≠ 0 ∧ ∀ (n : ℕ), n = A.rank → ∀ (pt : Formalism.MainNotions.StandardLatticesGL3.GA D n → Formalism.L2.Theta.GA D A),
      (∀ x, GlobalTheory.BotFormula.IsFinPt A (pt x) x) → ∀ Φ : Formalism.L2.Theta.GA D A → ℂ,
      (∀ γ ∈ GQ A, ∀ h, Φ (γ * h) = Φ h) → (∀ k ∈ GinfC A, ∀ h, Φ (h * k) = Φ h) →
      (∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D n) (k : Formalism.L2.Theta.GA D A), x ∈ GlobalTheory.NormSum.intG D n → GlobalTheory.BotFormula.IsFinPt A k x →
        ∀ h, Φ (h * k) = Φ h) →
      ∫ g in fd, Φ g ∂m = v * ∑ᶠ x : GlobalTheory.NormSum.Cls D n (GlobalTheory.NormSum.intG D n),
        ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D n) x.out : ℂ))⁻¹ * Φ (pt x.out) := by
  intro D A hA m fd hm hfd
  have hV : ∀ φ : D.host.E →+* ℂ, (A.gram.map φ).PosDef := fun φ => by
    rw [hA, Matrix.map_one φ (map_zero φ) (map_one φ)]
    exact Matrix.PosDef.one
  let V' : HSp D := { A with sig := fun _ => (A.rank, 0) }
  have hS' : V'.SigOK := fun τ => GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef (hV τ)
  have hD' : V'.IsDefinite := fun τ => Or.inl rfl
  have hGc : IsCompact (GinfC A : Set (Formalism.L2.Theta.GA D A)) := Formalism.IndefR.Eqv.isCompact_GinfC (V := V') hS' hD'
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  have hLC := hT.1
  have hSC := hT.2.1
  have hB := hT.2.2.2.1
  have hG := hT.2.2.2.2.1
  have hC := hT.2.2.2.2.2.2
  let J : Subgroup (Formalism.L2.Theta.GA D A) :=
    (Formalism.L2.DIV.St (1 : GL (Fin A.rank) (Lev.EAf D))).comap (Lev.finE A)
  have hJ : ∀ g, g ∈ J ↔ finStd A hA g ∈ GlobalTheory.NormSum.intG D A.rank := mem_level_iff A hA (isFrame_one _)
  have hJo : IsOpen (J : Set (Formalism.L2.Theta.GA D A)) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ A 1 ∅] with κ hh
    exact hh.2.1
  have hJc : IsCompact (J : Set (Formalism.L2.Theta.GA D A)) := by
    obtain ⟨C, hCc, hCm⟩ := GlobalTheory.ParahoricCompact.exists_compact A 1
    refine (hCc.mul hGc).of_isClosed_subset (Subgroup.isClosed_of_isOpen J hJo) ?_
    intro k hk
    refine ⟨finPart A k, hCm _ (finPart_mem A k) ?_, realPart A k, realPart_mem A k, finPart_mul_realPart A k⟩
    rw [finE_finPart]
    exact hk
  have hJtop : m J ≠ ⊤ := hJc.measure_lt_top.ne
  have hJ0 : m J ≠ 0 := (hJo.measure_pos m ⟨1, J.one_mem⟩).ne'
  refine ⟨((m J).toReal : ℂ), Complex.ofReal_ne_zero.2 (ENNReal.toReal_pos hJ0 hJtop).ne', ?_⟩
  intro n hn pt hpt Φ hl hinf hlev
  subst hn
  haveI : Finite (GlobalTheory.NormSum.Cls D A.rank (GlobalTheory.NormSum.intG D A.rank)) := (GlobalTheory.NormSum.cls_finite_card_le D A.rank).1
  haveI := Fintype.ofFinite (GlobalTheory.NormSum.Cls D A.rank (GlobalTheory.NormSum.intG D A.rank))
  let z : GlobalTheory.NormSum.Cls D A.rank (GlobalTheory.NormSum.intG D A.rank) → Formalism.L2.Theta.GA D A := fun x => pt x.out
  obtain ⟨hu, hcard⟩ := transport (finStd A hA) (GQ A) J (GlobalTheory.NormSum.ratG D A.rank) (GlobalTheory.NormSum.intG D A.rank)
    hJ (fun γ hγ => finStd_mem_ratG A hA hγ) (fun δ hδ => exists_rat_lift A hA hδ)
    (fun γ hγ γ' hγ' h => finStd_injOn A hA hγ hγ' h) z (fun x => finStd_of_isFinPt A hA (hpt _))
  have hfin : ∀ l, {γ : Formalism.L2.Theta.GA D A | γ ∈ GQ A ∧ (z l)⁻¹ * γ * z l ∈ J}.Finite := fun l => by
    have him : {γ : Formalism.L2.Theta.GA D A | γ ∈ GQ A ∧ (z l)⁻¹ * γ * z l ∈ J} =
        Subtype.val '' {γ : GQ A | (z l)⁻¹ * (γ : Formalism.L2.Theta.GA D A) * z l ∈ J} := by
      ext γ
      simp only [Set.mem_setOf_eq, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
      exact ⟨fun h => ⟨h.1, h.2⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩
    rw [him]
    exact (GlobalTheory.InnerClassSum.finite_stab_of_measure m (GQ A) J hfd hJ0 hJtop (z l)).image _
  have hr : ∀ k ∈ J, ∀ h, Φ (h * k) = Φ h := fun k hk h => by
    rw [← finPart_mul_realPart A k, ← mul_assoc, hinf _ (realPart_mem A k),
      hlev _ _ ((hJ k).1 hk) (isFinPt_finPart A hA k)]
  obtain ⟨-, -, heq⟩ := GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset (Formalism.L2.Theta.GA D A) m (GQ A) J fd hfd hJo
    hJtop _ z hu hfin Φ hl hr
  rw [heq, finsum_eq_sum_of_fintype]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hcard x]
  rfl

end GlobalTheory.BotClassMeas
