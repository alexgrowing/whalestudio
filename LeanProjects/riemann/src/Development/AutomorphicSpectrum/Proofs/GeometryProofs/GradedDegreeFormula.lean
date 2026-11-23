import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.LinearIndependentSumElimOfExact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GrLine

open GroundTheory.Heights₂.Heights

section Algebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem linearIndependent_snoc {F : Submodule R M}
    (hsat : ∀ (a : R) (x : M), a ≠ 0 → a • x ∈ F → x ∈ F) {n : ℕ} {f : Fin n → M}
    (hf : ∀ a, f a ∈ F) (hli : LinearIndependent R f) {s : M} (hs : s ∉ F) :
    LinearIndependent R (Fin.snoc f s : Fin (n + 1) → M) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_castSucc] at hg
  simp only [Fin.snoc_castSucc, Fin.snoc_last] at hg
  have hlast : g (Fin.last n) = 0 := by
    by_contra h0
    apply hs
    apply hsat _ _ h0
    have : g (Fin.last n) • s = -∑ a : Fin n, g a.castSucc • f a := eq_neg_of_add_eq_zero_right hg
    rw [this]
    exact F.neg_mem (F.sum_mem fun a _ => F.smul_mem _ (hf a))
  rw [hlast, zero_smul, add_zero] at hg
  have hz := Fintype.linearIndependent_iff.mp hli (fun a => g a.castSucc) hg
  intro j
  exact Fin.lastCases hlast (fun a => hz a) j

theorem card_quotient_line {F G P : Submodule R M} (hFG : F ≤ G) (hPF : P ≤ F)
    (hsat : ∀ (a : R) (x : M), a ≠ 0 → a • x ∈ F → x ∈ F) {s : M} (hs : s ∉ F)
    (T : Submodule R G) (U : Submodule R F)
    (hT : ∀ x : G, x ∈ T ↔ (x : M) ∈ P ⊔ Submodule.span R {s})
    (hU : ∀ x : F, x ∈ U ↔ (x : M) ∈ P) :
    Nat.card (G ⧸ T) =
      Nat.card (G ⧸ (F ⊔ Submodule.span R {s}).comap G.subtype) * Nat.card (F ⧸ U) := by
  set S : Submodule R G := (F ⊔ Submodule.span R {s}).comap G.subtype with hS
  have hTS : T ≤ S := fun x hx => (sup_le_sup_right hPF _) ((hT x).1 hx)
  let φ : F →ₗ[R] G ⧸ T := T.mkQ ∘ₗ Submodule.inclusion hFG
  have hker : LinearMap.ker φ = U := by
    ext x
    rw [hU]
    simp only [φ, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    rw [hT]
    change (x : M) ∈ P ⊔ Submodule.span R {s} ↔ _
    constructor
    · intro h
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
      have ha : a = 0 := by
        by_contra h0
        apply hs
        apply hsat a s h0
        have : a • s = (x : M) - y := by rw [← hyz]; abel
        rw [this]
        exact F.sub_mem x.2 (hPF hy)
      rw [ha, zero_smul, add_zero] at hyz
      rwa [← hyz]
    · exact fun h => Submodule.mem_sup_left h
  have hrange : LinearMap.range φ = S.map T.mkQ := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Submodule.inclusion hFG x, Submodule.mem_sup_left x.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨x, hx, z, hz, hxz⟩ := Submodule.mem_sup.1 (show (y : M) ∈ F ⊔ Submodule.span R {s} from hy)
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
      refine ⟨⟨x, hx⟩, ?_⟩
      simp only [φ, LinearMap.comp_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq, hT]
      have : ((Submodule.inclusion hFG ⟨x, hx⟩ - y : G) : M) = -(a • s) := by
        change x - (y : M) = _
        rw [← hxz]
        abel
      rw [this]
      exact neg_mem (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self s)))
  have hc : Nat.card (F ⧸ U) = Nat.card (S.map T.mkQ) := by
    rw [← hker, ← hrange]
    exact Nat.card_congr φ.quotKerEquivRange.toEquiv
  rw [hc, mul_comm]
  exact (Submodule.card_quotient_mul_card_quotient S T hTS).symm

end Algebra

open scoped ComplexOrder in

theorem gramDet_re_eq_norm {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    (σ : L →+* ℂ) {n : ℕ} {e : Fin n → B.carrier} (hli : LinearIndependent (𝓞 L) e) :
    GroundTheory.Heights₂.Heights.gramDet B.metric σ e = ‖B.gramDet σ e‖ := by
  have hd : B.gramDet σ e = (Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det := rfl
  have hp : 0 < (Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det :=
    (Matrix.posDef_gram_of_linearIndependent (linearIndependent_fibreVec B.metric σ hli)).det_pos
  obtain ⟨h1, h2⟩ := Complex.lt_def.mp hp
  have hz : (((Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det).re : ℂ) =
      (Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det :=
    Complex.ext (by simp) (by simpa using h2)
  rw [hd, ← hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by simpa using h1)]
  rfl

theorem grDeg_eq : ∀ (L : Type) [Field L] [NumberField L] (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (r : ℕ) (A : SatFlag B r) (i : Fin r) (f : Fin i → B.carrier) (s : B.carrier), (∀ a, f a ∈ A.F i.castSucc) → LinearIndependent (𝓞 L) f → s ∈ A.F i.succ → s ∉ A.F i.castSucc → A.grDeg i = (Module.finrank ℚ L : ℝ)⁻¹ * (Real.log (Nat.card (A.F i.succ ⧸ (A.F i.castSucc ⊔ Submodule.span (𝓞 L) {s}).comap (A.F i.succ).subtype)) - (1 / 2) * ∑ σ : L →+* ℂ, (Real.log ‖B.gramDet σ (Fin.snoc f s : Fin (i + 1) → B.carrier)‖ - Real.log ‖B.gramDet σ f‖)) := by
  intro L _ _ B r A i f s hf hli hs hs0
  have hFG : A.F i.castSucc ≤ A.F i.succ := A.mono (Fin.castSucc_lt_succ).le
  have hsat : ∀ (a : 𝓞 L) (x : B.carrier), a ≠ 0 → a • x ∈ A.F i.castSucc → x ∈ A.F i.castSucc :=
    A.sat i.castSucc
  have hsn : LinearIndependent (𝓞 L) (Fin.snoc f s : Fin (i + 1) → B.carrier) :=
    linearIndependent_snoc hsat hf hli hs0
  have hmem : ∀ a, (Fin.snoc f s : Fin (i + 1) → B.carrier) a ∈ A.F i.succ := by
    intro a
    refine Fin.lastCases ?_ (fun j => ?_) a
    · simpa using hs
    · simpa using hFG (hf j)
  let f' : Fin i → A.F i.castSucc := fun a => ⟨f a, hf a⟩
  let g' : Fin (i + 1) → A.F i.succ := fun a => ⟨(Fin.snoc f s : Fin (i + 1) → B.carrier) a, hmem a⟩
  have hf' : LinearIndependent (𝓞 L) f' := LinearIndependent.of_comp (A.F i.castSucc).subtype hli
  have hg' : LinearIndependent (𝓞 L) g' := LinearIndependent.of_comp (A.F i.succ).subtype hsn
  have hcF : Fintype.card (Fin i) = B.rank (A.F i.castSucc) := by
    rw [Fintype.card_fin, A.rank]; simp
  have hcG : Fintype.card (Fin (i + 1)) = B.rank (A.F i.succ) := by
    rw [Fintype.card_fin, A.rank]; simp
  have hP : Submodule.span (𝓞 L) (Set.range f) ≤ A.F i.castSucc :=
    Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hf a)
  have hU : ∀ x : A.F i.castSucc, x ∈ Submodule.span (𝓞 L) (Set.range f') ↔
      (x : B.carrier) ∈ Submodule.span (𝓞 L) (Set.range f) := by
    intro x
    have hm : (Submodule.span (𝓞 L) (Set.range f')).map (A.F i.castSucc).subtype =
        Submodule.span (𝓞 L) (Set.range f) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [← hm]
    constructor
    · exact fun h => ⟨x, h, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [← Subtype.ext hyx]
  have hT : ∀ x : A.F i.succ, x ∈ Submodule.span (𝓞 L) (Set.range g') ↔
      (x : B.carrier) ∈ Submodule.span (𝓞 L) (Set.range f) ⊔ Submodule.span (𝓞 L) {s} := by
    intro x
    have hm : (Submodule.span (𝓞 L) (Set.range g')).map (A.F i.succ).subtype =
        Submodule.span (𝓞 L) (Set.range f) ⊔ Submodule.span (𝓞 L) {s} := by
      rw [Submodule.map_span, ← Set.range_comp, ← Submodule.span_union]
      congr 1
      have hr : Set.range ((A.F i.succ).subtype ∘ g') =
          Set.range (Fin.snoc f s : Fin (i + 1) → B.carrier) := rfl
      rw [hr]
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        refine Fin.lastCases ?_ (fun j => ?_) a
        · right; simp
        · left; exact ⟨j, by simp⟩
      · rintro (⟨j, rfl⟩ | hy)
        · exact ⟨j.castSucc, by simp⟩
        · exact ⟨Fin.last _, by simpa using hy.symm⟩
    rw [← hm]
    constructor
    · exact fun h => ⟨x, h, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [← Subtype.ext hyx]
  have hidx := card_quotient_line hFG hP hsat hs0 _ _ hT hU
  have hfinF : Finite (A.F i.castSucc ⧸ Submodule.span (𝓞 L) (Set.range f')) :=
    finite_quotient_span hf' hcF
  have hfinG : Finite (A.F i.succ ⧸ Submodule.span (𝓞 L) (Set.range g')) :=
    finite_quotient_span hg' hcG
  have hne : (Nat.card (A.F i.succ ⧸ Submodule.span (𝓞 L) (Set.range g')) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hlog : Real.log (Nat.card (A.F i.succ ⧸ Submodule.span (𝓞 L) (Set.range g'))) =
      Real.log (Nat.card (A.F i.succ ⧸ (A.F i.castSucc ⊔ Submodule.span (𝓞 L) {s}).comap (A.F i.succ).subtype)) +
        Real.log (Nat.card (A.F i.castSucc ⧸ Submodule.span (𝓞 L) (Set.range f'))) := by
    rw [hidx] at hne ⊢
    push_cast at hne ⊢
    exact Real.log_mul (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne)
  have hgF : ∀ σ : L →+* ℂ, GroundTheory.Heights₂.Heights.gramDet B.metric σ
      (fun a => ((f' a : A.F i.castSucc) : B.carrier)) = ‖B.gramDet σ f‖ :=
    fun σ => gramDet_re_eq_norm B σ hli
  have hgG : ∀ σ : L →+* ℂ, GroundTheory.Heights₂.Heights.gramDet B.metric σ
      (fun a => ((g' a : A.F i.succ) : B.carrier)) =
        ‖B.gramDet σ (Fin.snoc f s : Fin (i + 1) → B.carrier)‖ :=
    fun σ => gramDet_re_eq_norm B σ hsn
  rw [SatFlag.grDeg, HermitianBundle.normDegree, HermitianBundle.normDegree,
    B.degree_eq_of_linearIndependent _ hf' hcF, B.degree_eq_of_linearIndependent _ hg' hcG, hlog]
  simp only [hgF, hgG, Finset.sum_sub_distrib]
  ring

end GlobalTheory.CompanionTheory.Ar.GrLine
