import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormLinearRelationDefinedOverCoreFieldStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConjugateSectionValuesSemilinear

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjExpand

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

set_option maxHeartbeats 1000000 in

theorem read_of_isBC (M : OMDat C R i Tp tup) (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c M.lev2)
    (cc : (C.U ((i : ℕ) + 1) M.s0).Comp → ℂ) (L : ℂ) (z : G) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n m : ℕ}
    {f : Rul (C.Q.Xo ((i : ℕ) + 1)) M.c'} (hf : f ∈ sec _ M.c' a n) {as : Fin m → M.c'.F}
    {fs : Fin m → Rul (C.Q.Xo ((i : ℕ) + 1)) C.Q.c} (hfs : ∀ k, fs k ∈ sec _ C.Q.c a n) (h : IsBC M.hle f as fs)
    (g : GA D (Wc D i)) :
    cc (M.dict g).1 * L * M.mu g * rdU (unfBC M.hle (C.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z f) (M.dict g).1 (M.dict g).2 =
      ∑ k, (as k : ℂ) * (L * M.phi cc (actLev C.Q.c M.lev2 z (fs k)) g) := by
  have h1 := (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ M.hle _ _ hact).2 a n z m as fs f hf hfs h
  have h2 := congrFun (congrFun (rdU_unfBC M.hle (C.U ((i : ℕ) + 1)) (inC M.c') h1) (M.dict g).1) (M.dict g).2
  rw [Finset.sum_apply, Finset.sum_apply] at h2
  refine (congrArg (fun w => cc (M.dict g).1 * L * M.mu g * w) h2).trans ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show cc _ * L * M.mu _ * ((as k : ℂ) * _) = (as k : ℂ) * (L * (cc _ * M.mu _ * _))
  ring

end GlobalTheory.ConjExpand

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.ConjExpand.conjFun_galRul : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (hf : Fixes M.c' ta) (z : G), ∀ f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) M.c' (unfBC M.hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank, M.EquivAt (κ i) (T.cE ((i : ℕ) + 1) M.s0) → ConjFun M (κ i) τ 1 (fun g => T.cE ((i : ℕ) + 1) M.s0 (M.dict g).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * M.mu g * rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z f) (M.dict g).1 (M.dict g).2) (fun g => T.cE ((i : ℕ) + 1) M.s0 (M.dict g).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * M.mu g * rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z (galRul hf f)) (M.dict g).1 (M.dict g).2) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC hT i Tp tup M hP τ ta hta hB hf z f hfc hE
  have hact := hP.act.1
  obtain ⟨ht⟩ := id hT
  have hn : (κ i).n = (Vc D i).rank :=
    (ht.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm
  obtain ⟨m, as, fs, hfs, hBC⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ M.hle).2 _ (T.U ((i : ℕ) + 1)) _ _ f hfc
  have hsec := ((mem_cusp _ _ _ _ _ _).1 hfc).1
  have hs : ∀ k, fs k ∈ sec _ T.Q.c (wtA (κ i)) (Vc D i).rank := fun k => ((mem_cusp _ _ _ _ _ _).1 (hfs k)).1
  have hgal := GlobalTheory.GalTw.galRul_sec_val_semilinear _ _ (T.Q.Dw ((i : ℕ) + 1)) _ (T.Q.Xo ((i : ℕ) + 1)) M.c' ta hf
  have hFix : ∀ x : T.Q.c.F, ta (incF T.Q.c M.c' M.hle x) = incF T.Q.c M.c' M.hle x := by
    intro x
    apply Subtype.ext
    rw [hta]
    exact hB.core x
  have hgsec := ((hgal.1 _ _ f hsec).1)
  have hgBC := hgal.2.2 T.Q.c M.hle hFix _ _ m as fs f hsec hBC
  have hkeep : ∀ k, actLev T.Q.c M.lev2 z (fs k) ∈ T.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n := by
    intro k
    obtain ⟨y, hy, -⟩ := hP.lift.lev z
    refine (hE z y hy (fs k) ?_).1
    rw [hn]
    exact hfs k
  obtain ⟨Fk, hFk⟩ : ∃ Fk : Fin m → T.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
      ∀ k, (Fk k : T.toCore.R ((i : ℕ) + 1)) = actLev T.Q.c M.lev2 z (fs k) := ⟨fun k => ⟨_, hkeep k⟩, fun _ => rfl⟩
  have e1 := fun g => GlobalTheory.ConjExpand.read_of_isBC M hact (T.cE ((i : ℕ) + 1) M.s0) (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) z hsec hs hBC g
  have e2 := fun g => GlobalTheory.ConjExpand.read_of_isBC M hact (T.cE ((i : ℕ) + 1) M.s0) (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) z hgsec hs hgBC g
  simp only [← hFk] at e1 e2
  refine ⟨⟨m, fun k => (as k : ℂ), Fk, fun g => e1 g⟩, ?_⟩
  intro n a h hex g
  have hz : Expands M (κ i) (fun _ => 0) (Fin.append a (fun k => -(as k : ℂ))) (Fin.append h Fk) := by
    intro g
    have h0 := (e1 g).symm.trans (hex g)
    show (0 : ℂ) = _
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, neg_mul, Finset.sum_neg_distrib]
    linear_combination h0
  have hz' : (0 : ℂ) = _ := GlobalTheory.T.cuspForm_linear_relation_defined_over_core_field D G Pl0 T0 A T R F κ v₀ hC hT i Tp tup M hP τ hB.core _ _ _ hz g
  rw [Fin.sum_univ_add] at hz'
  simp only [Fin.append_left, Fin.append_right, map_neg, neg_mul, Finset.sum_neg_distrib] at hz'
  refine (e2 g).trans ?_
  simp only [one_mul, hta]
  linear_combination hz'
