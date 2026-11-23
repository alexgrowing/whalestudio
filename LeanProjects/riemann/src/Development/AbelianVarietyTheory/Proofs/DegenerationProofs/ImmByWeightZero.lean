import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueIsRatio
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfWeightEq
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CoeffSymmSum
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisUniqueMinAndSumsSeparated
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionBySectionsOfSpanStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClosedImmersionAbelianPartBundleStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPureWeightSectionNeZeroAt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PureSectionRatiosGenerateFunctionsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ClosedImm

section Lattice
variable {X : Type} [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (N : ℕ)

def Alone (ε : X) : Prop := ∀ v : X, v ≠ 0 → q ε < q (ε + N • v)

variable {q N}

theorem Alone.short {ε : X} (h : Alone q N ε) : Short q N ε := fun m => by
  by_cases hm : m = 0
  · simp [hm]
  · exact (h m hm).le

theorem Alone.eq {ε β m : X} (h : Alone q N ε) (hβ : Short q N β) (e : β = ε + N • m) : β = ε := by
  by_cases hm : m = 0
  · simp [e, hm]
  · have h1 := hβ (-m)
    have h2 := h m hm
    rw [e] at h1
    simp only [smul_neg, add_neg_cancel_right] at h1
    exact absurd h2 (not_lt.2 h1)

theorem pos_of_tendsto [Module.Free ℤ X] (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) {v : X}
    (hv : v ≠ 0) : 0 < q v := by
  by_contra hn
  have hfin : {x : X | ¬ 0 < q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_gt_atTop 0)
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℤ => n • v) (smul_left_injective ℤ hv)
    (fun n => ?_) hfin
  change ¬ 0 < q (n • v)
  rw [q.map_smul, zsmul_eq_mul, Int.cast_mul]
  exact not_lt.2 (mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg _) (not_lt.1 hn))

theorem alone_zero [Module.Free ℤ X] (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (hN : N ≠ 0) :
    Alone q N (0 : X) := fun v hv => by
  rw [map_zero, zero_add]
  refine pos_of_tendsto hq ?_
  rw [← natCast_zsmul]
  exact smul_ne_zero (by exact_mod_cast hN) hv

end Lattice

theorem res_const {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (e : U ≤ V) (a : R) : resG X e (constFn p V a) = constFn p U a := by
  unfold constFn
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp]
  erw [Scheme.Hom.appLE_map]

theorem const_zero {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) :
    constFn p U 0 = 0 := by
  unfold constFn
  rw [map_zero, map_zero]

theorem isRatio_lin {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) {H : LB X} {J : Type} [Fintype J]
    {s : J → H.Sec} {a : J → k} {φ t : H.Sec} (h : IsLin p s a φ) {W : X.Opens} {r : J → Γ(X, W)}
    (hr : ∀ j, IsRatio (s j) t W (r j)) : IsRatio φ t W (∑ j, constFn p W (a j) * r j) := fun l => by
  rw [h l, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, res_const, res_const, hr j l, _root_.mul_assoc]

variable {k : Type} [Field k] (Φ : FibPre k)

theorem isLB_H (d : ℕ) : (Φ.H d).IsLB := by
  have key : ∀ (U V : Φ.E.B.left.Opens) (h : V ≤ U) (h' : Φ.D.q.left ⁻¹ᵁ V ≤ Φ.D.q.left ⁻¹ᵁ U)
      (u : Γ(Φ.E.B.left, U)ˣ),
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

theorem isRatio_pull {s t : Φ.N₀.Sec} {φ ψ : (Φ.H 1).Sec}
    (hφ : ∀ l, φ.f l = (Φ.D.q.left.app (Φ.N₀.U l)).hom (s.f l))
    (hψ : ∀ l, ψ.f l = (Φ.D.q.left.app (Φ.N₀.U l)).hom (t.f l))
    {V : Φ.E.B.left.Opens} {r : Γ(Φ.E.B.left, V)} (h : IsRatio s t V r) :
    IsRatio φ ψ (Φ.D.q.left ⁻¹ᵁ V) ((Φ.D.q.left.app V).hom r) := fun l => by
  have e := congrArg (Φ.D.q.left.app (V ⊓ Φ.N₀.U l)).hom (h l)
  rw [map_mul, app_res _ _ (Φ.D.q.left.preimage_mono inf_le_right),
    app_res _ _ (Φ.D.q.left.preimage_mono inf_le_left),
    app_res _ _ (Φ.D.q.left.preimage_mono inf_le_right)] at e
  rw [hφ, hψ]
  exact e

variable {Φ} {N : ℕ} {q : QuadraticMap ℤ Φ.E.X ℝ} {J : Type} [Fintype J] {cls : J → Φ.E.X}
  {F : J → (Φ.H 1).Sec}

theorem pure_of_alone (hG : Φ.Good N q cls F) {ε : Φ.E.X} (hε : Alone q N ε) {i : J} (hi : cls i = ε) :
    Φ.Pure ε (F i) := fun β hβ => by
  obtain ⟨h1, m, hm⟩ := hG.supp i β hβ
  exact hε.eq h1 (hi ▸ hm)

theorem onto_of_alone (hG : Φ.Good N q cls F) {ε : Φ.E.X} (hε : Alone q N ε) {φ : (Φ.H 1).Sec}
    (hφ : Φ.Pure ε φ) : ∃ a : J → k, (∀ i, a i ≠ 0 → cls i = ε) ∧
      ∀ l, Φ.wt φ ε l = ∑ i, constFn Φ.E.B.hom _ (a i) * Φ.wt (F i) ε l := by
  obtain ⟨a, ha, h⟩ := hG.onto ε hε.short φ hφ
  refine ⟨a, fun i hi => ?_, h⟩
  obtain ⟨m, hm⟩ := ha i hi
  exact hε.eq (m := -m) (hG.short i) (by rw [hm]; simp)

theorem isLin_of_alone (hG : Φ.Good N q cls F) {ε : Φ.E.X} (hε : Alone q N ε) {φ : (Φ.H 1).Sec}
    (hφ : Φ.Pure ε φ) : ∃ a : J → k, IsLin Φ.G.hom F a φ := by
  obtain ⟨a, ha, h⟩ := onto_of_alone hG hε hφ
  refine ⟨a, fun l => eq_of_weight_eq Φ.D (Φ.ch l) _ (Φ.aff l) (Φ.le l) fun χ => ?_⟩
  refine Eq.trans ?_ (WtLin.weight_sum Φ F a χ l).symm
  by_cases hχ : χ = ε
  · subst hχ
    exact h l
  · have h0 : Φ.wt φ χ l = 0 := by
      by_contra hne
      exact hχ (hφ ⟨l, hne⟩)
    refine h0.trans (Finset.sum_eq_zero fun i _ => ?_).symm
    by_cases hi : a i = 0
    · rw [hi, const_zero, zero_mul]
    · have h1 : Φ.wt (F i) χ l = 0 := by
        by_contra hne
        exact hχ (pure_of_alone hG hε (ha i hi) ⟨l, hne⟩)
      rw [h1, mul_zero]

theorem immBy_weight_zero : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec) (π : Φ.Pol N), Big g N N' → Φ.Good N q cls F → π.PB.g + Module.finrank ℤ Φ.E.X = g → ImmBy Φ.G.hom (Φ.H 1) F {i | cls i = 0}) := by
  intro hL hL2 k _ _ Φ g N N' q J _ cls F π hB hG hg
  classical
  have h4 := hB.four
  have h0 : Alone q N (0 : Φ.E.X) := alone_zero hG.pos (by omega)
  obtain ⟨e, he, -⟩ := GlobalTheory.exists_basis_unique_min_and_sums_separated Φ.E.X q hG.pos _ g N N' _ rfl
    (by omega) hB.lll hB.sep
  have hp : ∀ i : {i // cls i = 0}, Φ.Pure 0 (F i.1) := fun i => pure_of_alone hG h0 i.2
  choose τ hτ₁ hτ₂ hτ₃ using fun i => (FibPre.pure_zero k Φ).2 _ (hp i)
  obtain ⟨m, t, ht⟩ := GlobalTheory.T.exists_closedImmersion_abelianPart_bundle hL hL2 k Φ N h4 π
  have := Φ.E.isAbelian.proper
  obtain ⟨hcov, hloc⟩ := GlobalTheory.T.isClosedImmersionBySections_of_span k _ Φ.E.B.hom Φ.N₀ Φ.isLB _ _ t τ ht fun n => by
    obtain ⟨φ, hφ, hφ'⟩ := (FibPre.pure_zero k Φ).1 (t n)
    obtain ⟨a, ha, h⟩ := onto_of_alone hG h0 hφ
    refine ⟨fun i => a i.1, fun l => ?_⟩
    rw [← hφ', h, ← Fintype.sum_subtype_add_sum_subtype (fun i => cls i = 0),
      Finset.sum_eq_zero (s := Finset.univ) (f := fun i : {i // ¬ cls i = 0} =>
        constFn Φ.E.B.hom _ (a i.1) * Φ.wt (F i.1) 0 l) fun i _ => by
          have : a i.1 = 0 := by_contra fun hne => i.2 (ha _ hne)
          rw [this, const_zero, zero_mul], add_zero]
    exact Finset.sum_congr rfl fun i _ => by rw [hτ₁]
  refine ⟨?_, fun i hi => ?_⟩
  · refine top_le_iff.1 fun x _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge (show Φ.D.q.left x ∈ ⊤ from trivial))
    obtain ⟨-, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i.1, TopologicalSpace.Opens.mem_iSup.2 ⟨i.2, ?_⟩⟩
    rw [hτ₃]
    exact hi
  · obtain ⟨haff, ρ, hρ, hgen⟩ := hloc ⟨i, hi⟩ trivial
    have hle := (hτ₃ ⟨i, hi⟩).ge
    have hu := fun s => SecRatio.existsUnique_isRatio (isLB_H Φ 1) s (F i) _ hle
    have := Φ.D.q_affine
    rw [hτ₃ ⟨i, hi⟩]
    choose r hr hr' using fun j => hu (F j)
    refine ⟨haff.preimage _, r, hr, ?_⟩
    refine GlobalTheory.T.pureSection_ratios_generate_functions k Φ _ e (F i) _ haff (hp ⟨i, hi⟩) hle (GlobalTheory.ZH.FibPre.exists_pure_ne_zero_at hL hL2 k Φ N h4 π) _
      (fun a => ?_) fun n φ y hφ hy => ?_
    · have ha : a ∈ Subring.closure _ := hgen.ge (Subring.mem_top a)
      refine Subring.mem_comap.1 (Subring.closure_le.2 ?_ ha)
      rintro _ (⟨c, rfl⟩ | ⟨j, rfl⟩)
      · exact Subring.subset_closure (Or.inl ⟨c, (WtLin.app_constFn _ _ _ (Over.w Φ.D.q) _ c).symm⟩)
      · exact Subring.subset_closure (Or.inr ⟨j.1,
          (hr' _ _ (isRatio_pull Φ (hτ₂ j) (hτ₂ ⟨i, hi⟩) (hρ j))).symm⟩)
    · obtain ⟨a, ha⟩ : ∃ a : J → k, IsLin Φ.G.hom F a φ :=
        hφ.elim (isLin_of_alone hG fun v hv => (he n v hv).1) (isLin_of_alone hG fun v hv => (he n v hv).2)
      rw [(hu φ).unique hy (isRatio_lin _ ha hr)]
      exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨_, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨_, rfl⟩))

end GlobalTheory.ZH.ClosedImm
end
