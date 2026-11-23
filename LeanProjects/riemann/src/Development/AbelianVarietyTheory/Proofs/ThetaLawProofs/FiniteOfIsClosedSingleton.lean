import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.JacNeZeroIffSpanEqMaximalIdeal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.TransvFin

theorem valT_eq_zero_of_notMem {K : Type} [Field K] {X : Scheme.{0}} (w : Sp K ⟶ X) {U : X.Opens}
    (h : ⊤ ≤ w ⁻¹ᵁ U) (f : Γ(X, U)) (p : Sp K) (hp : w p ∉ X.basicOpen f) : valT (T := K) w U f = 0 := by
  by_contra hne
  have h1 : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom ((w.appLE U ⊤ h).hom f)) := by
    have e : valT (T := K) w U f = _ := dif_pos h
    exact e ▸ Ne.isUnit hne
  have h2 : IsUnit ((w.appLE U ⊤ h).hom f) := by
    have := h1.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    rwa [Iso.hom_inv_id_apply] at this
  have h3 := (Sp K).basicOpen_of_isUnit h2
  rw [Scheme.basicOpen_appLE] at h3
  exact hp ((h3.ge (x := p) trivial).2)

theorem eq_of_specializes {X : Scheme.{0}} {J : Type} {U : X.Opens} (f : J → Γ(X, U)) {y y' : X} (h : y' ⤳ y)
    (hy : y ∈ U)
    (hf : Ideal.span (Set.range fun i => gs (𝟙 X) y U (f i)) = IsLocalRing.maximalIdeal (X.presheaf.stalk y))
    (h0 : ∀ i, y' ∉ X.basicOpen (f i)) : y' = y := by
  by_contra hne
  have hn : ¬ y ⤳ y' := fun h' => hne (h.antisymm h').eq
  rw [specializes_iff_forall_open] at hn
  push_neg at hn
  obtain ⟨V, hV, hV1, hV2⟩ := hn
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := y) (U := ⊤) trivial
  have hyW' : y' ∈ W := h.mem_open W.isOpen hyW
  obtain ⟨g, hg, hg'⟩ := hW.exists_basicOpen_le (V := ⟨V, hV⟩) ⟨y', hV1⟩ hyW'
  have hle : IsLocalRing.maximalIdeal (X.presheaf.stalk y) ≤
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y')).comap (X.presheaf.stalkSpecializes h).hom := by
    rw [← hf, Ideal.span_le]
    rintro _ ⟨i, rfl⟩ hu
    refine h0 i ((X.mem_basicOpen (f i) y' (h.mem_open U.isOpen hy)).2 ?_)
    have e : gs (𝟙 X) y U (f i) = (X.presheaf.germ U y hy).hom (f i) := gs_eq (𝟙 X) y U hy (f i)
    beta_reduce at hu
    rwa [e, TopCat.Presheaf.germ_stalkSpecializes_apply] at hu
  have hm : (X.presheaf.germ W y hyW).hom g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) :=
    fun hu => hV2 (hg ((X.mem_basicOpen g y hyW).2 hu))
  refine hle hm ?_
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  exact (X.mem_basicOpen g y' hyW').1 hg'

theorem finite_of_isClosed_singleton {T : Type} [TopologicalSpace T] [TopologicalSpace.NoetherianSpace T]
    [QuasiSober T] {Z : Set T} (hZ : IsClosed Z) (h : ∀ y ∈ Z, IsClosed ({y} : Set T)) : Z.Finite := by
  obtain ⟨S, hS, hc, hi, rfl⟩ := TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  refine hS.sUnion fun t ht => ?_
  obtain ⟨y, hy⟩ := QuasiSober.sober (hi t ht) (hc t ht)
  rw [← hy.def, (h y ⟨t, ht, hy.mem⟩).closure_eq]
  exact Set.finite_singleton y

end GlobalTheory.TransvFin

open GlobalTheory.TransvFin in

theorem GlobalTheory.KeyKa.exists_etZ_of_jac_ne_zero : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (n : ℕ) (s : Fin x.P.g → RR x n), (∀ (z : Pt x) (c : x.P.L.ι), ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c → (∀ i, valT (T := K) z.left (x.P.L.U c) ((s i).f c) = 0) → jac x s z c ≠ 0) → ∃ (d : ℕ) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), EtZ x s z ch := by
  intro K _ _ x n s hs
  have := x.P.smoothDim
  have : Smooth x.P.A.hom := SmoothOfRelativeDimension.smooth x.P.g _
  have : IsProper x.P.A.hom := x.P.isAb.proper
  have : JacobsonSpace x.P.A.left := LocallyOfFiniteType.jacobsonSpace x.P.A.hom
  have : IsLocallyNoetherian x.P.A.left := LocallyOfFiniteType.isLocallyNoetherian x.P.A.hom
  have : CompactSpace x.P.A.left := QuasiCompact.compactSpace_of_compactSpace x.P.A.hom
  have : IsNoetherian x.P.A.left := {}
  let Z : Set x.P.A.left := {y | ∀ i, y ∉ Out.nonzeroLocus (s i)}
  have hZ : IsClosed Z := by
    have e : Z = ⋂ i, (Out.nonzeroLocus (s i) : Set x.P.A.left)ᶜ := by
      ext y
      simp [Z]
    rw [e]
    exact isClosed_iInter fun i => (Out.nonzeroLocus (s i)).isOpen.isClosed_compl
  have hb : ∀ y ∈ Z, ∀ c i, y ∉ x.P.A.left.basicOpen ((s i).f c) := fun y hy c i h =>
    hy i (TopologicalSpace.Opens.mem_iSup.2 ⟨c, h⟩)
  have key : ∀ y ∈ Z, IsClosed ({y} : Set x.P.A.left) → ∃ (z : Pt x) (c : x.P.L.ι), (∀ p, z.left p = y) ∧
      ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c ∧ ∀ i, valT (T := K) z.left (x.P.L.U c) ((s i).f c) = 0 := by
    intro y hy hc
    let z : Pt x := Over.homMk (pointOfClosedPoint (K := K) x.P.A.hom y hc)
      (pointOfClosedPoint_comp (K := K) x.P.A.hom y hc)
    have hz (p) : z.left p = y := pointOfClosedPoint_apply (K := K) x.P.A.hom y hc p
    obtain ⟨c, hyc⟩ := TopologicalSpace.Opens.mem_iSup.1 (x.P.isLB.cover.ge (x := y) trivial)
    have ht : ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c := fun p _ => (congrArg (· ∈ x.P.L.U c) (hz p)).mpr hyc
    exact ⟨z, c, hz, ht, fun i => valT_eq_zero_of_notMem z.left ht _ (IsLocalRing.closedPoint K)
      fun h => hb y hy c i ((congrArg (· ∈ x.P.A.left.basicOpen ((s i).f c)) (hz _)).mp h)⟩
  have hcl : ∀ y ∈ Z, IsClosed ({y} : Set x.P.A.left) := by
    intro y' hy'
    obtain ⟨y, hy, hc⟩ := nonempty_inter_closedPoints (Z := closure ({y'} : Set x.P.A.left))
      ⟨y', subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    have hsp : y' ⤳ y := specializes_iff_mem_closure.2 hy
    obtain ⟨z, c, hz, ht, h0⟩ := key y (hsp.mem_closed hZ hy') hc
    have h1 := (jac_ne_zero_iff_span_eq_maximalIdeal K x n s z c (IsLocalRing.closedPoint K) ht h0).1 (hs z c ht h0)
    have hU : z.left (IsLocalRing.closedPoint K) ∈ x.P.L.U c := ht (x := IsLocalRing.closedPoint K) trivial
    have e := eq_of_specializes (fun i => (s i).f c) ((hz _).symm ▸ hsp) hU h1 (hb y' hy' c)
    rw [e.trans (hz _)]
    exact hc
  have hfin := finite_of_isClosed_singleton hZ hcl
  obtain ⟨d, ⟨e⟩⟩ := Finite.exists_equiv_fin Z (h := hfin)
  choose z c hz ht h0 using fun y : Z => key y y.2 (hcl y y.2)
  refine ⟨d, fun a => z (e.symm a), fun a => c (e.symm a), fun a => ht _, fun a => h0 _,
    fun a => (hs _ _ (ht _) (h0 _)).isUnit, fun a a' hne p h => hne ?_,
    fun y hy => ⟨e ⟨y, hy⟩, IsLocalRing.closedPoint K, ?_⟩⟩
  · exact e.symm.injective (Subtype.ext ((hz _ p).symm.trans (h.trans (hz _ p))))
  · exact (hz _ _).trans (congrArg Subtype.val (e.symm_apply_apply ⟨y, hy⟩))
