import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Statements.LocalTrivialization.LocTrivOfRetraction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Degenerations.ShortSquareFormIff
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CoeffSymmSum

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH

theorem valR_eq_valF {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    GlobalTheory.ZH.valR x U f = valF x U f := rfl

theorem FibPre.isLB_H {k : Type} [Field k] (Φ : FibPre k) (d : ℕ) : (Φ.H d).IsLB := by
  have key : ∀ (U V : Φ.E.B.left.Opens) (h : V ≤ U) (h' : Φ.D.q.left ⁻¹ᵁ V ≤ Φ.D.q.left ⁻¹ᵁ U) (u : Γ(Φ.E.B.left, U)ˣ),
      res h' (pullU Φ.D.q.left U u ^ d) = pullU Φ.D.q.left V (res h u) ^ d := by
    intro U V h h' u
    rw [map_pow]
    congr 1
    ext
    exact (congrArg (fun φ => φ.hom (u : Γ(Φ.E.B.left, U))) (Φ.D.q.left.naturality (homOfLE h).op)).symm
  refine ⟨?_, fun i => ?_, fun i j l => ?_⟩
  · show ⨆ l, Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l = ⊤
    rw [← Scheme.Hom.preimage_iSup, Φ.isLB.cover]; rfl
  · have := congrArg (fun u => pullU Φ.D.q.left _ u ^ d) (Φ.isLB.g_self i)
    simp only [map_one, one_pow] at this
    exact (key _ _ _ (Scheme.Hom.preimage_mono _ (le_inf le_rfl le_rfl)) _).trans this
  · have := congrArg (fun u => pullU Φ.D.q.left _ u ^ d) (Φ.isLB.cocycle i j l)
    simp only [map_mul, mul_pow] at this
    rw [← key _ _ _ (Scheme.Hom.preimage_mono _ inf_le_left),
      ← key _ _ _ (Scheme.Hom.preimage_mono _ (le_inf (inf_le_left.trans inf_le_right) inf_le_right)),
      ← key _ _ _ (Scheme.Hom.preimage_mono _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right))] at this
    exact this

namespace TorusFibre
variable {k : Type} [Field k]

def trivPre (E : SplitExt (Sp k)) (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (D : E.GtDatum G)
    (ha : IsAffine E.B.left) (j : E.ChartIdx) (hj : ⊤ ≤ E.chart j) : FibPre k where
  E := E
  G := G
  D := D
  N₀ := Out.Inh.trivLB _
  isLB := Out.Inh.trivLB_isLB _
  aff := fun _ => isAffineOpen_top _
  ch := fun _ => j
  le := fun _ => hj

theorem bijective_constFn {X : Scheme.{0}} (f : X ⟶ Sp k) [IsIso f] : Function.Bijective (constFn f ⊤) := by
  have h1 : Function.Bijective (f.appLE ⊤ ⊤ (fun _ _ => trivial)).hom := by
    have : f.appLE ⊤ ⊤ (fun _ _ => trivial) = f.app ⊤ := Scheme.Hom.appLE_eq_app f
    rw [this]
    exact ConcreteCategory.bijective_of_isIso (f.app ⊤)
  exact h1.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv)

theorem constFn_zero {X : Scheme.{0}} (f : X ⟶ Sp k) (U : X.Opens) : constFn f U 0 = 0 := by
  simp [constFn]

theorem exists_sec (E : SplitExt (Sp k)) (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (D : E.GtDatum G)
    (ha : IsAffine E.B.left) (j : E.ChartIdx) (hj : ⊤ ≤ E.chart j) (S : Finset E.X) :
    ∃ φ : ((trivPre E G D ha j hj).H 1).Sec, ∀ α l,
      (α ∈ S → (trivPre E G D ha j hj).wt φ α l = 1) ∧ (α ∉ S → (trivPre E G D ha j hj).wt φ α l = 0) := by
  classical
  let e := Equiv.ofBijective _ (D.coord j ⊤ (isAffineOpen_top _) hj)
  let p : AddMonoidAlgebra Γ(E.B.left, ⊤) E.X := ∑ α ∈ S, AddMonoidAlgebra.single α 1
  refine ⟨⟨fun _ => e p, fun i i' => ?_⟩, fun α l => ?_⟩
  · have : ((trivPre E G D ha j hj).H 1).g i i' = 1 := by
      show pullU _ _ 1 ^ 1 = 1
      rw [map_one, one_pow]
    rw [this, Units.val_one, _root_.one_mul]
    rfl
  · have : (trivPre E G D ha j hj).wt (d := 1) ⟨fun _ => e p, by
        intro i i'
        have : ((trivPre E G D ha j hj).H 1).g i i' = 1 := by
          show pullU _ _ 1 ^ 1 = 1
          rw [map_one, one_pow]
        rw [this, Units.val_one, _root_.one_mul]
        rfl⟩ α l = (e.symm (e p)).coeff α := rfl
    rw [this, Equiv.symm_apply_apply]
    constructor <;> intro h <;> simp [p, Finsupp.finsetSum_apply, Finsupp.single_apply, h] <;> rfl

theorem exists_good (E : SplitExt (Sp k)) (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (D : E.GtDatum G)
    [IsIso E.B.hom] (ha : IsAffine E.B.left) (j : E.ChartIdx) (hj : ⊤ ≤ E.chart j) (N : ℕ)
    (q : QuadraticMap ℤ E.X ℝ) (hq : Filter.Tendsto q Filter.cofinite Filter.atTop)
    (J : Type) [Fintype J] (c : E.X → J) (hc : Function.Surjective c)
    (hcl : ∀ α β, c α = c β ↔ ∃ m, α = β + N • m) :
    ∃ (cls : J → E.X) (F : J → ((trivPre E G D ha j hj).H 1).Sec),
      (∀ i, c (cls i) = i) ∧ (trivPre E G D ha j hj).Good N q cls F := by
  classical
  have hmin : ∀ i, ∃ α ∈ {β | c β = i}, ∀ β ∈ {β | c β = i}, q α ≤ q β := fun i =>
    Filter.Tendsto.exists_within_forall_le (hc i) hq
  choose cls hcls hle using hmin
  have hfin : ∀ i, {β | Short q N β ∧ c β = i}.Finite := by
    intro i
    have h := (hq.eventually (Filter.eventually_gt_atTop (q (cls i))))
    refine (Filter.eventually_cofinite.1 h).subset ?_
    rintro β ⟨hs, hb⟩
    obtain ⟨m, hm⟩ := (hcl (cls i) β).1 ((hcls i).trans hb.symm)
    simpa [hm] using hs m
  choose F hF using fun i => exists_sec E G D ha j hj (hfin i).toFinset
  have hiff : ∀ α i, (∃ m, α = cls i + N • m) ↔ c α = i := fun α i => by
    rw [← hcl, hcls i]
  have hsum : ∀ α, Short q N α → ∀ a : J → k, ∀ l,
      ∑ i, constFn (trivPre E G D ha j hj).E.B.hom _ (a i) * (trivPre E G D ha j hj).wt (F i) α l =
        constFn E.B.hom ⊤ (a (c α)) := by
    intro α hα a l
    rw [Finset.sum_eq_single (c α)]
    · rw [(hF (c α) α l).1 (by simpa using hα)]; exact _root_.mul_one _
    · intro i _ hi
      rw [(hF i α l).2 (by simp [hi.symm])]; exact mul_zero _
    · simp
  refine ⟨cls, F, hcls, hq, fun i m => hle i _ ((hiff _ i).1 ⟨m, rfl⟩), ?_, ?_, ?_⟩
  · rintro i β ⟨l, hl⟩
    have : β ∈ (hfin i).toFinset := by
      by_contra h
      exact hl ((hF i β l).2 h)
    have := (Set.Finite.mem_toFinset _).1 this
    exact ⟨this.1, (hiff β i).2 this.2⟩
  · intro α hα φ _
    obtain ⟨b, hb⟩ := (bijective_constFn E.B.hom).2 ((trivPre E G D ha j hj).wt φ α PUnit.unit)
    refine ⟨Pi.single (c α) b, fun i hi => (hiff α i).2 ?_, fun l => ?_⟩
    · by_contra h
      exact hi (Pi.single_eq_of_ne (Ne.symm h) _)
    · refine Eq.trans ?_ (hsum α hα _ l).symm
      rw [Pi.single_eq_same, hb]; rfl
  · intro α hα a ha' h
    have h0 : a (c α) = 0 := (bijective_constFn E.B.hom).1
      (((hsum α hα a PUnit.unit).symm.trans (h PUnit.unit)).trans (constFn_zero _ _).symm)
    funext i
    by_contra hi
    exact hi ((hiff α i).1 (ha' i hi) ▸ h0)

theorem exists_fibPre (k : Type) [Field k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    ∃ (Φ : FibPre k) (_ : Φ.E.X ≃ₗ[ℤ] X), (∀ N, ∃ π : Φ.Pol N, π.PB.g = 0) ∧
      ∀ (N : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ), Filter.Tendsto q Filter.cofinite Filter.atTop →
        ∀ (J : Type) [Fintype J] (c : Φ.E.X → J), Function.Surjective c → (∀ α β, c α = c β ↔ ∃ m, α = β + N • m) →
          ∃ (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec), (∀ i, c (cls i) = i) ∧ Φ.Good N q cls F := by
  let P := Out.Inh.zeroPolAV (Sp k)
  obtain ⟨O, h₁, h₂, h₃, D, -⟩ := GlobalTheory.UU.exists_gtDatum_prod (X := X) P.A P.isAb
  let E : SplitExt (Sp k) := SplitExt.mk P.A P.isAb X O h₁ h₂ h₃
  have := P.isAb.comm
  have : IsIso E.B.hom := by show IsIso (𝟙 (Sp k)); infer_instance
  have ha : IsAffine E.B.left := by show IsAffine (Sp k); infer_instance
  have hch : ∀ M : LB (Sp k), M.IsLB → ∃ i, ⊤ ≤ M.U i := by
    intro M hM
    have : (default : PrimeSpectrum k) ∈ ⨆ i, M.U i := by rw [hM.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact ⟨i, fun x _ => by
      have : x = (default : PrimeSpectrum k) := Subsingleton.elim (α := PrimeSpectrum k) _ _
      rw [this]; exact hi⟩
  have hiso : ∀ L M : LB (Sp k), L.IsLB → M.IsLB → LBIso L M := fun L M hL hM =>
    DVR.exists_gen_of_isLB_local (V := k) _ (LB.isLB_div hM hL)
  choose j hj using fun b => hch (E.O (E.basis b)).L (E.O (E.basis b)).isLB
  have hj' : ⊤ ≤ E.chart j := by
    intro x _
    have : (⨅ b, (E.O (E.basis b)).L.U (j b)) = ⊤ := iInf_eq_top.2 fun b => top_unique (hj b)
    show x ∈ ⨅ b, (E.O (E.basis b)).L.U (j b)
    rw [this]; trivial
  refine ⟨trivPre E _ D ha j hj', LinearEquiv.refl ℤ X, fun N => ⟨⟨P, Iso.refl _, ?_, fun _ => 1, ?_, fun α => ?_⟩, rfl⟩,
    fun N q hq J _ c hc hcl => exists_good E _ D ha j hj' N q hq J c hc hcl⟩
  · show IsMonHom (𝟙 P.A); infer_instance
  · exact hiso _ _ (Out.Inh.trivLB_isLB _) (LB.isLB_pull (LB.isLB_linComb P.isLB _ _) _)
  · exact hiso _ _ (E.O α).isLB (LB.isLB_linComb P.isLB _ _)

theorem exists_multiplicativeGroup (k : Type) [Field k] :
    ∃ (Φ : FibPre k) (q : QuadraticMap ℤ Φ.E.X ℝ) (cls : ZMod 81 → Φ.E.X) (F : ZMod 81 → (Φ.H 1).Sec) (π : Φ.Pol 81),
      Φ.Good 81 q cls F ∧ π.PB.g + Module.finrank ℤ Φ.E.X = 1 ∧ Function.Injective cls := by
  obtain ⟨Φ, e, hP, hG⟩ := exists_fibPre k ℤ
  obtain ⟨π, hπ⟩ := hP 81
  let q₀ : QuadraticMap ℤ ℤ ℝ := (Algebra.linearMap ℤ ℝ).compQuadraticMap QuadraticMap.sq
  have h₀ : Filter.Tendsto q₀ Filter.cofinite Filter.atTop := by
    have h1 : Filter.Tendsto (fun n : ℤ => n * n) Filter.cofinite Filter.atTop := by
      rw [Int.cofinite_eq, Filter.tendsto_sup]
      exact ⟨Filter.tendsto_id.atBot_mul_atBot₀ Filter.tendsto_id, Filter.tendsto_id.atTop_mul_atTop₀ Filter.tendsto_id⟩
    refine (tendsto_intCast_atTop_atTop.comp h1).congr fun n => ?_
    simp [q₀]
  obtain ⟨cls, F, hc, hg⟩ := hG 81 (q₀.comp e.toLinearMap) (h₀.comp e.injective.tendsto_cofinite) (ZMod 81)
    (fun α => (e α : ZMod 81)) (ZMod.intCast_surjective.comp e.surjective) (fun α β => by
      rw [eq_comm, ZMod.intCast_eq_intCast_iff_dvd_sub]
      constructor
      · rintro ⟨m, hm⟩
        refine ⟨e.symm m, e.injective ?_⟩
        rw [map_add, map_nsmul, e.apply_symm_apply, nsmul_eq_mul]; linarith
      · rintro ⟨m, rfl⟩
        exact ⟨e m, by rw [map_add, map_nsmul, nsmul_eq_mul]; ring⟩)
  refine ⟨Φ, _, cls, F, π, hg, ?_, fun i j h => by rw [← hc i, ← hc j, h]⟩
  rw [hπ, e.finrank_eq]; simp

end TorusFibre

theorem big_one : Big 1 81 100000 := by
  have h : (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 := by
    calc (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have h' : (2 : ℝ) ^ ((1 : ℝ) / 2 - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  refine ⟨by norm_num, ?_, ?_⟩
  · push_cast; linarith
  · simp only [Nat.factorial]; push_cast; linarith

namespace AbelianFibre
variable {k : Type} [Field k]

def affineCharts (E : SplitExt (Sp k)) (L : LB E.B.left) : LB E.B.left :=
  ⟨{p : E.B.left.Opens × L.ι × E.ChartIdx // IsAffineOpen p.1 ∧ p.1 ≤ L.U p.2.1 ∧ p.1 ≤ E.chart p.2.2},
    fun p => p.1.1, fun p q => res (inf_le_inf p.2.2.1 q.2.2.1) (L.g p.1.2.1 q.1.2.1)⟩

def affineChartsPull (E : SplitExt (Sp k)) (L : LB E.B.left) : ChartPull (affineCharts E L) L (𝟙 _) where
  idx p := p.1.2.1
  le p := p.2.2.1
  g y p q hp hq := gm_res (𝟙 _) y (inf_le_inf p.2.2.1 q.2.2.1) (show y ∈ p.1.1 ⊓ q.1.1 from ⟨hp, hq⟩) _

theorem affineCharts_isLB (E : SplitExt (Sp k)) {L : LB E.B.left} (hL : L.IsLB) : (affineCharts E L).IsLB := by
  refine ⟨top_le_iff.1 fun y _ => ?_, fun p => unit_ext fun y hy => ?_, fun p q r => unit_ext fun y hy => ?_⟩
  · obtain ⟨i, hi⟩ := exists_chart hL y
    choose j hj using fun b => exists_chart (E.O (E.basis b)).isLB y
    have hj' : y ∈ E.chart j := by
      show y ∈ ((⨅ b, (E.O (E.basis b)).L.U (j b) : E.B.left.Opens) : Set E.B.left)
      rw [TopologicalSpace.Opens.coe_iInf]
      exact Set.mem_iInter.2 hj
    obtain ⟨V, hV, hy, hle⟩ := exists_isAffineOpen_mem_and_subset (show y ∈ L.U i ⊓ E.chart j from ⟨hi, hj'⟩)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(V, i, j), hV, fun x hx => (hle hx).1, fun x hx => (hle hx).2⟩, hy⟩
  · rw [gm_res (𝟙 _) y _ hy, map_one, (affineChartsPull E L).g y p p hy hy]
    exact gm_self hL _ y (p.2.2.1 hy)
  · rw [map_mul, gm_res (𝟙 _) y _ hy, gm_res (𝟙 _) y _ hy, gm_res (𝟙 _) y _ hy,
      (affineChartsPull E L).g y p q hy.1.1 hy.1.2, (affineChartsPull E L).g y q r hy.1.2 hy.2,
      (affineChartsPull E L).g y p r hy.1.1 hy.2]
    exact gm_cocycle hL _ y (p.2.2.1 hy.1.1) (q.2.2.1 hy.1.2) (r.2.2.1 hy.2)

def ofBundle (E : SplitExt (Sp k)) (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (D : E.GtDatum G)
    {L : LB E.B.left} (hL : L.IsLB) : FibPre k where
  E := E
  G := G
  D := D
  N₀ := affineCharts E L
  isLB := affineCharts_isLB E hL
  aff p := p.2.1
  ch p := p.1.2.2
  le p := p.2.2.2

theorem ofBundle_iso (E : SplitExt (Sp k)) (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (D : E.GtDatum G)
    {L : LB E.B.left} (hL : L.IsLB) : LBIso (ofBundle E G D hL).N₀ L :=
  lbIso_of_chartPull (affineChartsPull E L) hL

theorem lbIso_of_gens {X : Scheme.{0}} {A B : LB X} (s : A.Gen) (hs : s.IsGen) (t : B.Gen) (ht : t.IsGen) :
    LBIso A B := by
  refine ⟨⟨fun p => res inf_le_left (t.s p.1) * (res inf_le_right (s.s p.2))⁻¹⟩,
    fun (p q : B.ι × A.ι) => unit_ext fun y hy => ?_⟩
  have v : ∀ p : B.ι × A.ι, y ∈ B.U p.1 ⊓ A.U p.2 → gm (𝟙 X) y (B.U p.1 ⊓ A.U p.2)
      (res inf_le_left (t.s p.1) * (res inf_le_right (s.s p.2))⁻¹) =
      gm (𝟙 X) y _ (t.s p.1) * (gm (𝟙 X) y _ (s.s p.2))⁻¹ := fun p hp => by
    rw [map_mul, map_inv, gm_res (𝟙 X) y _ hp, gm_res (𝟙 X) y _ hp]
  have e₁ := congrArg (gm (𝟙 X) y _) (hs p.2 q.2)
  have e₂ := congrArg (gm (𝟙 X) y _) (ht p.1 q.1)
  have m₁ : y ∈ A.U p.2 ⊓ A.U q.2 := ⟨hy.1.2, hy.2.2⟩
  have m₂ : y ∈ B.U p.1 ⊓ B.U q.1 := ⟨hy.1.1, hy.2.1⟩
  rw [map_mul, gm_res (𝟙 X) y _ m₁, gm_res (𝟙 X) y _ m₁] at e₁
  rw [map_mul, gm_res (𝟙 X) y _ m₂, gm_res (𝟙 X) y _ m₂] at e₂
  refine ((gm_res (𝟙 X) y _ hy _).trans (v p hy.1)).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div A B (𝟙 X) y p q hy) ((gm_res (𝟙 X) y _ hy _).trans (v q hy.2))).trans ?_)))
  rw [e₁, e₂, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

theorem exists_gen_self {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f f' : Y ⟶ X) (h : f' = f) :
    ∃ t : (LB.LinComb L (K := Fin 2) ![f', f] ![1, -1]).Gen, t.IsGen := by
  subst h
  have le : ∀ j : Fin 2 → L.ι, LB.wchart L ![f', f'] j ≤ f' ⁻¹ᵁ (L.U (j 0) ⊓ L.U (j 1)) := fun j y hy =>
    ⟨Set.mem_iInter.1 hy 0, Set.mem_iInter.1 hy 1⟩
  refine ⟨⟨fun j => res (le j) (pullU f' _ (L.g (j 0) (j 1)))⟩, fun (p q : Fin 2 → L.ι) => unit_ext fun y hy => ?_⟩
  have v : ∀ j : Fin 2 → L.ι, y ∈ LB.wchart L ![f', f'] j → gm (𝟙 Y) y (LB.wchart L ![f', f'] j)
      (res (le j) (pullU f' _ (L.g (j 0) (j 1)))) = gm f' y _ (L.g (j 0) (j 1)) := fun j hj =>
    (gm_res (𝟙 Y) y (le j) hj _).trans ((gm_pull (𝟙 Y) f' y _ (le j hj) _).trans (by rw [Category.id_comp]))
  refine ((gm_res (𝟙 Y) y _ hy _).trans (v p hy.1)).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_linComb L _ _ (𝟙 Y) y p q hy.1 hy.2) ((gm_res (𝟙 Y) y _ hy _).trans (v q hy.2))).trans ?_)))
  have e₁ := gm_cocycle hL f' y (le p hy.1).1 (le p hy.1).2 (le q hy.2).2
  have e₂ := gm_cocycle hL f' y (le p hy.1).1 (le q hy.2).1 (le q hy.2).2
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Category.id_comp, zpow_one, zpow_neg_one]
  rw [mul_right_comm, mul_inv_eq_iff_eq_mul]
  exact e₂.trans e₁.symm

theorem exists_pol (P : Out.PolAV (Sp k)) (N : ℕ) : ∃ (Φ : FibPre k) (π : Φ.Pol N), π.PB = P := by
  obtain ⟨O, h₁, h₂, h₃, D, -⟩ := GlobalTheory.UU.exists_gtDatum_prod (X := PUnit) P.A P.isAb
  let E : SplitExt (Sp k) := SplitExt.mk P.A P.isAb PUnit O h₁ h₂ h₃
  have := P.isAb.comm
  have hL : ((lbPow P.L N).pull (Iso.refl P.A).hom.left).IsLB := LB.isLB_pull (LB.isLB_linComb P.isLB _ _) _
  refine ⟨ofBundle E _ D hL, ⟨P, Iso.refl _, ?_, fun _ => 1, ofBundle_iso E _ D hL, fun α => ?_⟩, rfl⟩
  · show IsMonHom (𝟙 P.A); infer_instance
  · obtain ⟨s, hs⟩ := h₂
    obtain ⟨t, ht⟩ := exists_gen_self P.isLB (𝟙 P.A : P.A ⟶ P.A).left
      ((𝟙 P.A : P.A ⟶ P.A) * (Over.homMk P.A.hom (Category.comp_id _) ≫
        (1 : Out.baseOver (Sp k) ⟶ P.A))).left (by rw [MonObj.comp_one, _root_.mul_one])
    exact lbIso_of_gens s hs t ht

end AbelianFibre

namespace MonomialImmersion
variable (k : Type) [Field k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]

def laurent : AddMonoidAlgebra Γ(Sp k, ⊤) X ≃+* Γ((torusFib k X).G.left, ((torusFib k X).H 1).U PUnit.unit) :=
  RingEquiv.ofBijective _ ((torusFib k X).D.coord ((torusFib k X).ch PUnit.unit) _ ((torusFib k X).aff PUnit.unit)
    ((torusFib k X).le PUnit.unit))

theorem laurent_const (a : k) : laurent k X (AddMonoidAlgebra.single 0 (constFn (𝟙 (Sp k)) ⊤ a)) =
    constFn (torusFib k X).G.hom _ a := by
  refine Eq.trans ?_ (WtLin.app_constFn (torusFib k X).E.B.hom _ _ (Over.w (torusFib k X).D.q) ⊤ a)
  have key : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : Multiplicative X →* B)
      (hc : ∀ x y, Commute (f x) (g y)) (c : A),
      AddMonoidAlgebra.liftNCRingHom f g hc (AddMonoidAlgebra.single 0 c) = f c := fun f g hc c => by
    simp [AddMonoidAlgebra.liftNCRingHom]
  exact key _ _ (fun _ _ => Commute.all _ _) _

theorem closure_eq_top_iff {J : Type} (a : J → X) :
    Subring.closure (Set.range (fun c : k => (AddMonoidAlgebra.single 0 (constFn (𝟙 (Sp k)) ⊤ c) :
      AddMonoidAlgebra Γ(Sp k, ⊤) X)) ∪ Set.range fun j => AddMonoidAlgebra.single (a j) 1) = ⊤ ↔
      AddSubmonoid.closure (Set.range a) = ⊤ := by
  constructor
  · intro h
    let M := AddSubmonoid.closure (Set.range a)
    have hle : (⊤ : Subring (AddMonoidAlgebra Γ(Sp k, ⊤) X)) ≤
        (AddMonoidAlgebra.mapDomainRingHom Γ(Sp k, ⊤) M.subtype).range := by
      rw [← h, Subring.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨AddMonoidAlgebra.single 0 (constFn (𝟙 (Sp k)) ⊤ c), by simp⟩
      · exact ⟨AddMonoidAlgebra.single ⟨a j, AddSubmonoid.subset_closure ⟨j, rfl⟩⟩ 1, by simp⟩
    refine top_le_iff.1 fun α _ => ?_
    obtain ⟨y, hy⟩ := hle (Subring.mem_top (AddMonoidAlgebra.single α 1))
    by_contra hα
    have h0 : (AddMonoidAlgebra.mapDomainRingHom Γ(Sp k, ⊤) M.subtype y).coeff α = 0 :=
      Finsupp.mapDomain_notin_range _ _ (by rintro ⟨m, rfl⟩; exact hα m.2)
    rw [hy] at h0
    simp at h0
  · intro h
    set S := Subring.closure (Set.range (fun c : k => (AddMonoidAlgebra.single 0 (constFn (𝟙 (Sp k)) ⊤ c) :
      AddMonoidAlgebra Γ(Sp k, ⊤) X)) ∪ Set.range fun j => AddMonoidAlgebra.single (a j) 1) with hS
    have mono : ∀ α ∈ AddSubmonoid.closure (Set.range a), AddMonoidAlgebra.single α (1 : Γ(Sp k, ⊤)) ∈ S := by
      intro α hα
      induction hα using AddSubmonoid.closure_induction with
      | zero => exact one_mem S
      | mem _ hj =>
        obtain ⟨j, rfl⟩ := hj
        exact Subring.subset_closure (Or.inr ⟨j, rfl⟩)
      | add β β' _ _ hβ hβ' => simpa [AddMonoidAlgebra.single_mul_single] using mul_mem hβ hβ'
    refine top_le_iff.1 fun x hx => ?_
    clear hx
    induction x using AddMonoidAlgebra.induction_linear with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | single α c =>
      obtain ⟨c, rfl⟩ := (constFn_id_bijective k).2 c
      have hc : AddMonoidAlgebra.single 0 (constFn (𝟙 (Sp k)) ⊤ c) ∈ S := Subring.subset_closure (Or.inl ⟨c, rfl⟩)
      simpa [AddMonoidAlgebra.single_mul_single] using mul_mem hc (mono α (h ▸ AddSubmonoid.mem_top α))

theorem immBy_iff {J : Type} (a : J → X) (j₀ : J) (h₀ : a j₀ = 0) :
    ImmBy (torusFib k X).G.hom ((torusFib k X).H 1)
      (fun j => torusSec k X 1 (AddMonoidAlgebra.single (a j) 1)) {j₀} ↔
      AddSubmonoid.closure (Set.range a) = ⊤ := by
  let s : J → ((torusFib k X).H 1).Sec := fun j => torusSec k X 1 (AddMonoidAlgebra.single (a j) 1)
  have hs : ∀ j, (s j).f PUnit.unit = laurent k X (AddMonoidAlgebra.single (a j) 1) := fun _ => rfl
  have h1 : (s j₀).f PUnit.unit = 1 := by
    rw [hs, h₀]; exact map_one (laurent k X)
  have hW : Out.nonzeroLocus (s j₀) = ((torusFib k X).H 1).U PUnit.unit := by
    refine Eq.trans (@iSup_unique _ PUnit _ _ _) ?_
    show Scheme.basicOpen _ ((s j₀).f PUnit.unit) = _
    rw [h1]
    exact Scheme.basicOpen_of_isUnit _ isUnit_one
  have hq := (torusFib k X).D.q_affine
  have aux : ∀ W : (torusFib k X).G.left.Opens, W = ((torusFib k X).H 1).U PUnit.unit →
      ((IsAffineOpen W ∧ ∃ r : J → Γ((torusFib k X).G.left, W), (∀ j, IsRatio (s j) (s j₀) W (r j)) ∧
        Subring.closure (Set.range (constFn (torusFib k X).G.hom W) ∪ Set.range r) = ⊤) ↔
        AddSubmonoid.closure (Set.range a) = ⊤) := by
    rintro _ rfl
    have hr : ∀ j r, IsRatio (s j) (s j₀) (((torusFib k X).H 1).U PUnit.unit) r ↔ r = (s j).f PUnit.unit := by
      intro j r
      constructor
      · intro h
        have := h PUnit.unit
        rw [h1, map_one, _root_.mul_one] at this
        have e := congrArg (resG _ (le_inf le_rfl le_rfl : ((torusFib k X).H 1).U PUnit.unit ≤ _)) this
        have id : ∀ (U : (torusFib k X).G.left.Opens) (h : U ⊓ U ≤ U) (x : Γ((torusFib k X).G.left, U)),
            resG _ (le_inf le_rfl le_rfl : U ≤ U ⊓ U) (resG _ h x) = x := fun U h x => by
          rw [← CommRingCat.comp_apply, ← Functor.map_comp]
          exact congrArg (fun φ => CommRingCat.Hom.hom φ x) ((torusFib k X).G.left.presheaf.map_id _)
        rw [id, id] at e
        exact e.symm
      · rintro rfl ⟨⟩
        rw [h1, map_one, _root_.mul_one]
    have hcl : Subring.closure (Set.range (constFn (torusFib k X).G.hom (((torusFib k X).H 1).U PUnit.unit)) ∪
        Set.range fun j => (s j).f PUnit.unit) = ⊤ ↔ AddSubmonoid.closure (Set.range a) = ⊤ := by
      rw [← closure_eq_top_iff k X a]
      have e : (Set.range (constFn (torusFib k X).G.hom (((torusFib k X).H 1).U PUnit.unit)) ∪
          Set.range fun j => (s j).f PUnit.unit) = (laurent k X).toRingHom '' (Set.range (fun c : k =>
            (AddMonoidAlgebra.single 0 (constFn (𝟙 (Sp k)) ⊤ c) : AddMonoidAlgebra Γ(Sp k, ⊤) X)) ∪
              Set.range fun j => AddMonoidAlgebra.single (a j) 1) := by
        rw [Set.image_union, ← Set.range_comp, ← Set.range_comp]
        congr 2
        exact funext fun c => (laurent_const k X c).symm
      rw [e, ← RingHom.map_closure]
      constructor
      · intro h
        refine top_le_iff.1 fun x _ => ?_
        obtain ⟨y, hy, e'⟩ := h.ge (Subring.mem_top (laurent k X x))
        exact (laurent k X).injective e' ▸ hy
      · intro h
        rw [h]
        exact top_le_iff.1 fun x _ => ⟨(laurent k X).symm x, trivial, (laurent k X).apply_symm_apply x⟩
    constructor
    · rintro ⟨-, r, h₁, h₂⟩
      obtain rfl : r = fun j => (s j).f PUnit.unit := funext fun j => (hr j _).1 (h₁ j)
      exact hcl.1 h₂
    · exact fun h => ⟨((torusFib k X).aff PUnit.unit).preimage _, _, fun j => (hr j _).2 rfl, hcl.2 h⟩
  constructor
  · exact fun h => (aux _ hW).1 (h.2 j₀ rfl)
  · refine fun h => ⟨?_, ?_⟩
    · exact top_le_iff.1 (le_iSup₂_of_le j₀ rfl (hW.ge.trans' fun _ _ => trivial))
    · rintro _ rfl
      exact (aux _ hW).2 h

theorem immBy_three : ImmBy (torusFib k ℤ).G.hom ((torusFib k ℤ).H 1)
    (fun j => torusSec k ℤ 1 (AddMonoidAlgebra.single (![0, 1, -1] j) 1)) {(0 : Fin 3)} := by
  refine (immBy_iff k ℤ _ 0 rfl).2 (top_le_iff.1 fun n _ => ?_)
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simpa using nsmul_mem (AddSubmonoid.subset_closure (s := Set.range ![(0 : ℤ), 1, -1]) ⟨1, rfl⟩) m
  · simpa using nsmul_mem (AddSubmonoid.subset_closure (s := Set.range ![(0 : ℤ), 1, -1]) ⟨2, rfl⟩) m

theorem not_immBy_two : ¬ ImmBy (torusFib k ℤ).G.hom ((torusFib k ℤ).H 1)
    (fun j => torusSec k ℤ 1 (AddMonoidAlgebra.single (![0, 1] j) 1)) {(0 : Fin 2)} := by
  intro h
  have h' := (immBy_iff k ℤ _ 0 rfl).1 h
  have : AddSubmonoid.closure (Set.range ![(0 : ℤ), 1]) ≤ AddSubmonoid.nonneg ℤ := by
    rw [AddSubmonoid.closure_le]
    rintro _ ⟨j, rfl⟩
    fin_cases j <;> simp
  exact absurd (this (h'.ge (AddSubmonoid.mem_top (-1)))) (by simp)

end MonomialImmersion

theorem hilb_univ {k J : Type} [Field k] [Infinite k] [Finite J] (d : ℕ) :
    hilb (Set.univ : Set (J → k)) d = Module.finrank k (MvPolynomial.homogeneousSubmodule J k d) := by
  refine (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ ?_ _)).symm
  intro p q h
  exact MvPolynomial.funext fun v => congrFun h ⟨v, trivial⟩

theorem not_good_empty (k : Type) [Field k] (N : ℕ) :
    ¬ (torusFib k ℤ).Good N squareForm (J := Empty) Empty.elim Empty.elim := by
  intro h
  obtain ⟨a, -, ha⟩ := h.onto (0 : ℤ) (show Short squareForm N (0 : ℤ) from fun m => by
      simp only [squareForm_apply]; exact_mod_cast by positivity)
    (torusSec k ℤ 1 (AddMonoidAlgebra.single 0 1)) (by
      rintro β ⟨l, hl⟩
      by_contra hβ
      exact hl ((wt_torusSec k ℤ 1 _ β l).trans (Finsupp.single_eq_of_ne hβ)))
  have := (wt_torusSec k ℤ 1 _ (0 : ℤ) PUnit.unit).symm.trans (ha PUnit.unit)
  simp at this
  exact one_ne_zero (α := Γ(Sp k, ⊤)) this

end GlobalTheory.ZH
end
