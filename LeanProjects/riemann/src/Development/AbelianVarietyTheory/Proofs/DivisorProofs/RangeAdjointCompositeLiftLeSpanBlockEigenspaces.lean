import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapRangeAdjointLeBlockSum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamilySplitOperatorsEqLabelOperatorsModels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLiftStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspacesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatchedSphericalPairsCommuteCompositeLiftStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.AdjSpan

open Formalism.L2 in

theorem eigSum_le_span {K V H I : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] {σ : K →+* ℂ} {j : V →ₛₗ[σ] H}
    (hsp : Submodule.span ℂ (Set.range j) = ⊤) {op : I → Module.End K V} {U : I → Module.End ℂ H}
    (hU : ∀ i v, U i (j v) = j (op i v)) (hc : Col.PairComm op) (hs : Col.SplitOver op)
    {C : (I → K) → Prop} {CC : (I → ℂ) → Prop} (hC : ∀ x, CC (fun i => σ (x i)) → C x) :
    Col.eigSum U CC ≤ Submodule.span ℂ (j '' (Col.eigSum op C : Set V)) := by
  have hcU : Col.PairComm U := fun i i' => GlobalTheory.AdjBlock.ext_of_span hsp fun v => by
    simp only [Module.End.mul_apply, hU]
    exact congrArg j (LinearMap.congr_fun (hc i i').eq v)
  have h1 : ∀ x, Col.eigAt op x ≤ (Col.eigAt U fun i => σ (x i)).comap j := by
    intro x v hv
    rw [Submodule.mem_comap, Col.eigAt, Submodule.mem_iInf]
    intro i
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 (Col.eigAt_le op x i hv)
    refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, ?_⟩
    have : ∀ (k : ℕ) w, ((U i - σ (x i) • (1 : Module.End ℂ H)) ^ k) (j w) =
        j (((op i - x i • (1 : Module.End K V)) ^ k) w) := by
      intro k
      induction k with
      | zero => intro w; simp
      | succ k ih =>
        intro w
        rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← ih]
        simp [hU, map_smulₛₗ]
    rw [this, hk, map_zero]
  have h2 : ∀ Q : (I → K) → Prop, Submodule.span ℂ (j '' (Col.eigSum op Q : Set V)) ≤
      Col.eigSum U fun y => ∃ x, Q x ∧ y = fun i => σ (x i) := fun Q => by
    have : Col.eigSum op Q ≤ (Col.eigSum U fun y => ∃ x, Q x ∧ y = fun i => σ (x i)).comap j :=
      iSup₂_le fun x hx => (h1 x).trans (Submodule.comap_mono (Col.eigAt_le_eigSum ⟨x, hx, rfl⟩))
    rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    exact this hv
  have h3 : Submodule.span ℂ (j '' (Col.eigSum op C : Set V)) ⊔
      Submodule.span ℂ (j '' (Col.eigSum op (fun x => ¬ C x) : Set V)) = ⊤ := by
    rw [eq_top_iff, ← hsp, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    obtain ⟨a, ha, c, hc', rfl⟩ := Submodule.mem_sup.1
      ((Col.isCompl_eigSum hc hs C).sup_eq_top ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule K V)))
    rw [map_add]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨a, ha, rfl⟩) (Submodule.subset_span ⟨c, hc', rfl⟩)
  have h4 : Disjoint (Col.eigSum U fun y => CC y ∨ ∃ x, C x ∧ y = fun i => σ (x i))
      (Col.eigSum U fun y => ∃ x, ¬ C x ∧ y = fun i => σ (x i)) := by
    refine Col.disjoint_eigSum hcU ?_
    rintro y hy ⟨x, hx, rfl⟩
    rcases hy with hy | ⟨x', hx', he⟩
    · exact hx (hC x hy)
    · have : x = x' := funext fun i => σ.injective (congrFun he i)
      exact hx (this ▸ hx')
  rw [Col.eigSum_or] at h4
  intro w hw
  obtain ⟨a, ha, c, hc', rfl⟩ := Submodule.mem_sup.1 (h3 ▸ (Submodule.mem_top : w ∈ (⊤ : Submodule ℂ H)))
  have h5 : c = 0 := by
    refine (Submodule.disjoint_def.1 h4) _ ?_ (h2 _ hc')
    have : c = (a + c) - a := by abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left hw) (Submodule.mem_sup_right (h2 _ ha))
  rw [h5, add_zero]
  exact ha

theorem heckePolyOf_congr {L : Type} [Field L] (n q : ℕ) {a b : ℕ → L} (h : ∀ k, k ≤ n → a k = b k) :
    Formalism.L2.Col.heckePolyOf n q a = Formalism.L2.Col.heckePolyOf n q b := by
  unfold Formalism.L2.Col.heckePolyOf
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]

open Classical in
theorem evC_splitC {D : D7} (V : HSp D) (P : Pl D.host.E) (a : List ℤ → ℂ) (z : ℕ → ℂ) :
    GlobalTheory.Hk3.evC V P a (GlobalTheory.Hk3.splitC V.rank z) = ∑ j ∈ Finset.range (V.rank + 1),
      z j * (if IsLab V P (splitLab V.rank j) then a (splitLab V.rank j) else 0) := by
  unfold GlobalTheory.Hk3.evC GlobalTheory.Hk3.splitC
  rw [← Finsupp.sum_finset_sum_index (by simp) (by intro d x y; split_ifs <;> simp [add_mul])]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.sum_single_index (by simp)]
  split_ifs <;> simp

open Formalism.L2 in

theorem range_le_span_blockSum {K V H E Pl ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {σ : K →+* ℂ} {j : V →ₛₗ[σ] H}
    (hV : FiniteDimensional K V)
    (hsp : Submodule.span ℂ (Set.range j) = ⊤) {op : Pl × ℕ → Module.End K V} (hc : Col.PairComm op)
    (hs : Col.SplitOver op) {n m t : ℕ} (hm : m = n) {q : Pl → ℕ} {bl : List (Pl → K)}
    (hz : ∀ P k, m < k → op (P, k) = 0) (Θ : H →ₗ[ℂ] E) (W : ι → Submodule ℂ E) (hW : ⨆ c, W c = ⊤)
    (T : Pl → ℕ → Module.End ℂ H) (hT : ∀ P k, k ≤ m → ∀ v, j (op (P, k) v) = T P k (j v))
    (ev : ι → Pl → ℕ → ℂ) (g : ι → Pl → ℂ[X])
    (hg : ∀ c P, Col.heckePolyOf m (q P) (ev c P) = g c P * ((bl.map fun ν => Col.blockPoly (ν P) (q P) t).prod).map σ)
    (hev : ∀ c, ∀ w ∈ W c, ∀ P k, k ≤ m → T P k (LinearMap.adjoint Θ w) = ev c P k • LinearMap.adjoint Θ w) :
    LinearMap.range (LinearMap.adjoint Θ) ≤ Submodule.span ℂ (j '' (Col.blockSum n q t bl op : Set V)) := by
  subst hm
  let U : Pl × ℕ → Module.End ℂ H := fun i => if i.2 ≤ m then T i.1 i.2 else 0
  have hU : ∀ i v, U i (j v) = j (op i v) := by
    rintro ⟨P, k⟩ v
    by_cases hk : k ≤ m
    · simp only [U, if_pos hk]
      exact (hT P k hk v).symm
    · simp only [U, if_neg hk]
      rw [hz P k (not_le.1 hk)]
      simp
  refine le_trans ?_ (eigSum_le_span (U := U) hsp hU hc hs fun x hx => (Col.hasBlocks_map σ m q t bl x).1 hx)
  rw [LinearMap.range_eq_map, ← hW, Submodule.map_iSup]
  refine iSup_le fun c => ?_
  rintro _ ⟨w, hw, rfl⟩
  let x : Pl × ℕ → ℂ := fun i => if i.2 ≤ m then ev c i.1 i.2 else 0
  refine Col.eigAt_le_eigSum (x := x) (fun P => ?_) (Col.mem_eigAt_of_forall_apply ?_)
  · have h1 : Col.heckePolyOf m (q P) (fun k => x (P, k)) = _ :=
      (heckePolyOf_congr _ _ fun k hk => if_pos hk).trans (hg c P)
    refine Dvd.intro_left (g c P) (Eq.trans ?_ h1.symm)
    simp only [Polynomial.map_list_prod, List.map_map, Function.comp_def, Col.map_blockPoly]
  · rintro ⟨P, k⟩
    by_cases hk : k ≤ m
    · simp only [U, x, if_pos hk]
      exact hev c w hw P k hk
    · simp only [U, x, if_neg hk]
      simp

theorem range_adjoint_le_span : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A.fam.Ok s → Core R F → SchurAll R → ∀ t, LinearMap.range (LinearMap.adjoint (R.Th t)) ≤ Submodule.span ℂ (R.jX t '' ((A.fam.R t).ZH : Set (A.fam.R t).S.Forms)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hI hOk hC hS t
  classical
  have hSF : IsSF R (R.Pg.image fun PP => PP.under (𝓞 D.host.F)) := by
    intro v
    simp only [Finset.mem_image, HeightOneSpectrum.ext_iff]
    rfl
  have htop : ⨆ c, EEc R _ c = ⊤ := (GlobalTheory.T.exists_sphericalOperators_rows_normal_eigenspaces R F hC hS _ hSF).elim fun _ h => h.2.2.1
  choose hX hXo _ using (GlobalTheory.T.realization_family_normal_operators R F hC.lev hC.fam hC.models).1 t
  have hsplit := (GlobalTheory.SplitHeckeLabel.split_ops R F hC.lev hC.fam hC.models).1 t hX hXo
  have hf := GlobalTheory.AdjBlock.model_form (W := R.cX.W) (ι := Bridge.ratF D.sp.X') (ρ := R.cX.coef.ρ)
    (J := (levEnv _ R.βX (R.datXt t)).J) (χ := (levEnv _ R.βX (R.datXt t)).χ) (R.B.R t).pres (R.HX t) (hC.models.HX t)
    (hC.models.jX t)
  choose z hm hp using fun P : A.ok t => GlobalTheory.T.exists_splitPrime_heckeTransfer_compositeLift R F hI hC hS t P
  let a : (Pl D.host.E → List ℤ → ℂ) → A.ok t → ℕ → ℂ := fun c P j =>
    if IsLab (Yc D 0) (R.pl P) (splitLab (Yc D 0).rank j) then c (R.pl P) (dualLab (splitLab (Yc D 0).rank j)) else 0
  exact range_le_span_blockSum (Pl := A.ok t) (q := fun P => A.q P) (Module.Finite.of_basis (A.MtildeCSD t).basis) hf.2.1 (hOk.what₂ t).comm (hOk.what₂ t).split R.B.rankR
    (fun P => (hC.fam.degR t P).2) (R.Th t) _ htop
    (fun P k => hX (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1)) hsplit
    (fun c P k => ∑ j ∈ Finset.range ((Yc D 0).rank + 1), z P k j * a c P j) _ (fun c P => hp P (a c P))
    fun c w hw P k hk => ((GlobalTheory.T.matched_spherical_pairs_commute_composite_lift R F hC hS _ hSF t (R.pl P)
      ((GlobalTheory.GoodPrimes.good_primes R F hC.lev).2.2.2 hC.fam t P.1 P.2).1 _ _ (hm P k hk) hX hXo).2 c w hw).trans
        (congrArg (· • LinearMap.adjoint (R.Th t) w) (evC_splitC _ _ _ _))

end GlobalTheory.AdjSpan

end
