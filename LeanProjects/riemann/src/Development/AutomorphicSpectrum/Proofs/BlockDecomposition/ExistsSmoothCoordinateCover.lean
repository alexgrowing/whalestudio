import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.CovEx

variable {O : Type} [CommRing O] {X : Scheme.{0}}

theorem strV_basicOpen (q : X ⟶ Spec (CommRingCat.of O)) (V : X.Opens) (f : Γ(X, V)) :
    strV q (X.basicOpen f) = (algebraMap Γ(X, V) Γ(X, X.basicOpen f)).comp (strV q V) := by
  rw [RingHom.algebraMap_toAlgebra]
  simp only [strV]
  rw [← CommRingCat.hom_comp, Category.assoc, Scheme.Hom.appLE_map]

theorem coord_basicOpen (q : X ⟶ Spec (CommRingCat.of O)) {V : X.Opens} (hV : IsAffineOpen V) (f : Γ(X, V)) {d : ℕ}
    (g : MvPolynomial (Fin d) O →+* Localization.Away f)
    (hg : g.comp MvPolynomial.C = (algebraMap Γ(X, V) (Localization.Away f)).comp (strV q V)) (he : g.Etale) :
    Nonempty (Coord q (X.basicOpen f) d) := by
  have := hV.isLocalization_basicOpen f
  let e := IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f) Γ(X, X.basicOpen f)
  let G : MvPolynomial (Fin d) O →+* Γ(X, X.basicOpen f) := (e.toAlgHom.toRingHom).comp g
  have hG : (MvPolynomial.eval₂Hom (strV q (X.basicOpen f)) fun k => G (MvPolynomial.X k)) = G := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun k => by simp
    have h1 := RingHom.congr_fun hg r
    have h2 : G (MvPolynomial.C r) = e (g (MvPolynomial.C r)) := rfl
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, h2, strV_basicOpen]
    have h3 : g (MvPolynomial.C r) = algebraMap Γ(X, V) (Localization.Away f) (strV q V r) := h1
    rw [h3, AlgEquiv.commutes]
    rfl
  refine ⟨⟨hV.basicOpen f, fun k => G (MvPolynomial.X k), ?_⟩⟩
  rw [hG]
  exact RingHom.Etale.stableUnderComposition _ _ he (RingHom.Etale.of_bijective e.bijective)

theorem exists_basicOpen (Q : ∀ {R S : Type} [CommRing R] [CommRing S], (R →+* S) → Prop)
    (hQ : RingHom.RespectsIso Q) (q : X ⟶ Spec (CommRingCat.of O)) {V : X.Opens} (hV : IsAffineOpen V)
    (h : RingHom.Locally Q (q.appLE ⊤ V le_top).hom) {x : X} (hx : x ∈ V) :
    ∃ f : Γ(X, V), x ∈ X.basicOpen f ∧ Q ((algebraMap Γ(X, V) (Localization.Away f)).comp (strV q V)) := by
  obtain ⟨s, hs, hl⟩ := h
  have hc : ⨆ f : s, X.basicOpen (U := V) f.1 = V := (hV.iSup_basicOpen_eq_self_iff (s := s)).2 hs
  obtain ⟨f, hf⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc.ge hx)
  refine ⟨f.1, hf, ?_⟩
  exact hQ.2 _ (Scheme.ΓSpecIso (CommRingCat.of O)).symm.commRingCatIsoToRingEquiv (hl f.1 f.2)

theorem inter_affine (q : X ⟶ Spec (CommRingCat.of O)) [IsSeparated q] {U V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) :=
  isAffineHom_diagonal_iff.1 (inferInstance : IsAffineHom (Limits.pullback.diagonal q)) ⊤ (isAffineOpen_top _)
    _ le_top _ le_top hU hV

theorem cov_of_local (P : ℕ → Prop) (q : X ⟶ Spec (CommRingCat.of O)) [IsSeparated q] [QuasiCompact q]
    (h : ∀ x : X, ∃ (V : X.Opens) (d : ℕ), x ∈ V ∧ P d ∧ Nonempty (Coord q V d)) :
    ∃ U : Cov q, ∀ α, P (U.d α) := by
  classical
  choose V d hx hP hc using h
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X)) (fun x => (V x).2)
    fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩
  refine ⟨{ ι := t, U := fun a => V a.1, d := fun a => d a.1, c := fun a => (hc a.1).some, cover := ?_, inter := ?_ },
    fun a => hP a.1⟩
  · refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨y, hy⟩ := Set.mem_iUnion.1 (ht (Set.mem_univ x))
    obtain ⟨hy, hxy⟩ := Set.mem_iUnion.1 hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxy⟩
  · intro S hS
    induction hS using Finset.Nonempty.cons_induction with
    | singleton a => simpa using (hc a.1).some.affine
    | cons a s ha hs ih =>
      rw [Finset.cons_eq_insert, Finset.iInf_insert]
      exact inter_affine q (hc a.1).some.affine ih

theorem exists_cov : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [IsSeparated q]
    [QuasiCompact q], (Smooth q → Nonempty (Cov q)) ∧
      ∀ d, SmoothOfRelativeDimension d q → ∃ U : Cov q, ∀ α, U.d α = d := by
  intro O _ X q _ _
  refine ⟨fun hs => ?_, fun d hd => ?_⟩
  · obtain ⟨U, -⟩ := cov_of_local (fun _ => True) q fun x => by
      obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
      have h : RingHom.Locally RingHom.IsStandardSmooth (q.appLE ⊤ V le_top).hom :=
        RingHom.smooth_iff_locally_isStandardSmooth.1 (q.smooth_appLE (isAffineOpen_top _) hV le_top)
      obtain ⟨f, hf, hst⟩ := exists_basicOpen RingHom.IsStandardSmooth RingHom.isStandardSmooth_respectsIso q hV h hx
      obtain ⟨n, g, hg, he⟩ := hst.exists_etale_mvPolynomial
      exact ⟨_, n, hf, trivial, coord_basicOpen q hV f g hg he⟩
    exact ⟨U⟩
  · refine cov_of_local (fun n => n = d) q fun x => ?_
    obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
    have h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d) (q.appLE ⊤ V le_top).hom :=
      HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension d) q hd ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
    obtain ⟨f, hf, hst⟩ := exists_basicOpen (RingHom.IsStandardSmoothOfRelativeDimension d)
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso q hV h hx
    obtain ⟨g, hg, he⟩ := hst.exists_etale_mvPolynomial
    exact ⟨_, d, hf, rfl, coord_basicOpen q hV f g hg he⟩

end GlobalTheory.CompanionTheory.CovEx
