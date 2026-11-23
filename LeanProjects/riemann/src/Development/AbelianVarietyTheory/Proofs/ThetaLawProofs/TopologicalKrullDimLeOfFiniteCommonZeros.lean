import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOpenNonzeroLocusOfUniversallyClosed
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

open TopologicalSpace

namespace GlobalTheory.DimCut

theorem exists_ltSeries_of_anti {R α : Type*} [CommRing R] [IsNoetherianRing R] [Preorder α]
    (φ : PrimeSpectrum R → α) (hφ : ∀ a b, φ b ≤ φ a ↔ a ≤ b) (p : LTSeries α) (P : Fin (p.length + 1) → PrimeSpectrum R)
    (hP : ∀ i, φ (P i) = p i) (g : R) (hg : g ∈ (P 0).asIdeal) (hp : p.length ≠ 0) :
    ∃ (q : LTSeries α) (a : PrimeSpectrum R), q.length + 1 = p.length ∧ q.last = φ a ∧ q.last ≤ p.last ∧
      g ∈ a.asIdeal := by
  have hlt : ∀ a b, φ b < φ a ↔ a < b := fun a b => by simp only [lt_iff_le_not_ge, hφ]
  let P' : LTSeries (PrimeSpectrum R) := LTSeries.mk p.length (fun i => P i.rev) fun i j hij => by
    rw [← hlt, hP, hP]
    exact p.strictMono (Fin.rev_lt_rev.2 hij)
  have hl : P'.last = P 0 := congrArg P (Fin.rev_last _)
  have hh : P'.head = P (Fin.last _) := congrArg P (Fin.rev_zero _)
  obtain ⟨q, hq, hlen, hhead, -⟩ := PrimeSpectrum.exist_ltSeries_mem_one_of_mem_last P' (hl ▸ hg)
  have hlen' : p.length = q.length := hlen
  let q' : LTSeries α := LTSeries.mk (q.length - 1) (fun i => φ (q ⟨q.length - i, by omega⟩)) fun i j hij => by
    rw [hlt]
    refine q.strictMono ?_
    have := j.2
    have : (i : ℕ) < j := hij
    simp only [Fin.mk_lt_mk]
    omega
  have e : q'.last = φ (q 1) := by
    refine congrArg φ (congrArg q (Fin.ext ?_))
    have : 1 % (q.length + 1) = 1 := Nat.mod_eq_of_lt (by omega)
    simp only [Fin.val_last, Fin.coe_ofNat_eq_mod, this]
    change q.length - (q.length - 1) = 1
    omega
  refine ⟨q', q 1, ?_, e, ?_, hq⟩
  · change q.length - 1 + 1 = _
    omega
  · rw [e, show p.last = φ q.head by rw [← hhead, hh, hP]; rfl, hφ]
    exact q.head_le _

variable {X : Scheme.{0}}

theorem le_iff_specializes {x y : X} : x ≤ y ↔ y ⤳ x := Iff.rfl

theorem exists_ltSeries_notMem [IsLocallyNoetherian X] (p : LTSeries X) (hp : p.length ≠ 0) {D V : X.Opens}
    (g : Γ(X, V)) (hg : D ⊓ V = X.basicOpen g) (hV : p.head ∈ V) (hD : p.head ∉ D) :
    ∃ q : LTSeries X, q.length + 1 = p.length ∧ q.last ≤ p.last ∧ q.last ∉ D := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hV V.isOpen
  have hUV' : U ≤ V := hUV
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let g' : Γ(X, U) := X.presheaf.map (homOfLE hUV').op g
  have hg' : X.basicOpen g' = D ⊓ U := by
    rw [Scheme.basicOpen_res, ← hg, inf_comm D V, ← inf_assoc, inf_eq_left.2 hUV', inf_comm]
  let φ : PrimeSpectrum Γ(X, U) → X := fun a => hU.fromSpec a
  have hr : ∀ x, x ∈ U ↔ ∃ a, φ a = x := fun x => by
    change x ∈ (U : Set X) ↔ _
    rw [← hU.range_fromSpec]; rfl
  have hm : ∀ a, φ a ∈ D ↔ g' ∉ a.asIdeal := fun a => by
    have h₁ : φ a ∈ X.basicOpen g' ↔ g' ∉ a.asIdeal := by
      change a ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g' ↔ _
      rw [hU.fromSpec_preimage_basicOpen]; rfl
    rw [← h₁, hg']
    exact ⟨fun h => ⟨h, (hr _).2 ⟨a, rfl⟩⟩, fun h => h.1⟩
  have hφ : ∀ a b, φ b ≤ φ a ↔ a ≤ b := fun a b =>
    ((@Scheme.Hom.isOpenEmbedding _ _ _ hU.isOpenImmersion_fromSpec).isInducing.specializes_iff (x := a) (y := b)).trans
      (PrimeSpectrum.le_iff_specializes a b).symm
  choose P hP using fun i => (hr (p i)).1 ((le_iff_specializes.1 (p.head_le i)).mem_open U.isOpen hxU)
  obtain ⟨q, a, h₁, h₂, h₃, h₄⟩ := exists_ltSeries_of_anti φ hφ p P hP g'
    (by by_contra h; exact hD ((show φ (P 0) = p.head from hP 0) ▸ (hm _).2 h)) hp
  exact ⟨q, h₁, h₃, fun h => (hm a).1 (h₂ ▸ h) h₄⟩

theorem isClosed_singleton_of_finite {T : Type*} [TopologicalSpace T] [JacobsonSpace T] {Z : Set T}
    (hZ : IsClosed Z) (hf : Z.Finite) {z : T} (hz : z ∈ Z) : IsClosed ({z} : Set T) := by
  have : JacobsonSpace Z := .of_isClosedEmbedding hZ.isClosedEmbedding_subtypeVal
  have : Finite Z := hf
  simpa using hZ.isClosedEmbedding_subtypeVal.isClosedMap {⟨z, hz⟩} (isClosed_discrete _)

theorem finite_of_subset_isAffineOpen {K : Type} [Field K] (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    {D : X.Opens} (hD : IsAffineOpen D) {Z : Set X} (hZ : IsClosed Z) (h : Z ⊆ D) : Z.Finite := by
  let I := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨Z, hZ⟩
  have hI : Set.range I.subschemeι = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  let j := IsOpenImmersion.lift D.ι I.subschemeι (by rw [hI, Scheme.Opens.range_ι]; exact h)
  have : IsClosedImmersion (j ≫ D.ι) := by rw [IsOpenImmersion.lift_fac]; infer_instance
  have : IsClosedImmersion j := .of_comp j D.ι
  have : IsAffine D := hD
  have : IsAffine I.subscheme := isAffine_of_isAffineHom j
  have : IsFinite (I.subschemeι ≫ f) := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  have hfin := (I.subschemeι ≫ f).finite_preimage_singleton (IsLocalRing.closedPoint K)
  rw [← hI, ← Set.image_univ]
  exact (hfin.subset fun y _ => Subsingleton.elim (α := PrimeSpectrum K) _ _).image _

theorem length_le {K : Type} [Field K] (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] (r : ℕ) :
    ∀ (D : Fin r → X.Opens), (∀ i, IsAffineOpen (D i)) →
      (∀ i (y : X), ∃ (V : X.Opens) (g : Γ(X, V)), y ∈ V ∧ D i ⊓ V = X.basicOpen g) →
      ∀ W : Set X, IsClosed W → {y ∈ W | ∀ i, y ∉ D i}.Finite → ∀ p : LTSeries X, p.last ∈ W → p.length ≤ r := by
  have := LocallyOfFiniteType.jacobsonSpace f
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have nc : ∀ {x y : X}, x < y → ¬ IsClosed ({y} : Set X) := fun hxy hc =>
    hxy.ne ((le_iff_specializes.1 hxy.le).mem_closed hc rfl)
  induction r with
  | zero =>
    intro D _ _ W hW hf p hp
    by_contra h
    exact nc (p.strictMono (show (0 : Fin (p.length + 1)) < Fin.last _ from Fin.pos_iff_ne_zero.2 fun e => h (by have := congrArg Fin.val e; simp at this; omega)))
      (isClosed_singleton_of_finite hW (by simpa using hf) hp)
  | succ r ih =>
    intro D hD hg W hW hf p hp
    by_cases h0 : p.length = 0
    · omega
    have h01 : p.head < (p.tail h0).head := by
      rw [RelSeries.head_tail]
      refine p.strictMono (show (0 : Fin (p.length + 1)) < 1 from ?_)
      have : 1 % (p.length + 1) = 1 := Nat.mod_eq_of_lt (by omega)
      simp [Fin.lt_def, this]
    obtain ⟨y, hy, hyD⟩ : ∃ y, y < (p.tail h0).head ∧ y ∉ D 0 := by
      obtain ⟨y, hy, hyD⟩ := Set.not_subset.1 fun h => nc h01 (isClosed_singleton_of_finite isClosed_closure
        (finite_of_subset_isAffineOpen f (hD 0) isClosed_closure h) (subset_closure (Set.mem_singleton _)))
      have hy' : y ≤ (p.tail h0).head := le_iff_specializes.2 (specializes_iff_mem_closure.2 hy)
      by_cases h : (p.tail h0).head ≤ y
      · exact ⟨p.head, h01, fun h' => hyD ((le_iff_specializes.1 (h01.le.trans h)).mem_open (D 0).isOpen h')⟩
      · exact ⟨y, lt_of_le_not_ge hy' h, hyD⟩
    let p' : LTSeries X := (p.tail h0).cons y hy
    obtain ⟨V, g, hV, e⟩ := hg 0 y
    obtain ⟨q, h₁, h₂, h₃⟩ := exists_ltSeries_notMem p' (by simp [p']) g e (by simpa [p'] using hV)
      (by simpa [p'] using hyD)
    have hl : p'.last = p.last := by simp [p']
    have hn : p'.length = p.length := by simp [p']; omega
    have := ih (fun i => D i.succ) (fun i => hD _) (fun i => hg _) (W ∩ (D 0 : Set X)ᶜ)
      (hW.inter (D 0).isOpen.isClosed_compl) (hf.subset fun z hz => ⟨hz.1.1, Fin.cases hz.1.2 hz.2⟩) q
      ⟨(le_iff_specializes.1 (hl ▸ h₂)).mem_closed hW hp, h₃⟩
    omega

theorem topologicalKrullDim_le {W : Set X} (hW : IsClosed W) {r : ℕ}
    (h : ∀ p : LTSeries X, p.last ∈ W → p.length ≤ r) : topologicalKrullDim W ≤ r := by
  have : QuasiSober W := hW.isClosedEmbedding_subtypeVal.quasiSober
  let e : IrreducibleCloseds W → W := fun s => s.2.genericPoint
  have he : ∀ s t, (e s).1 ≤ (e t).1 ↔ s ≤ t := fun s t =>
    (subtype_specializes_iff (e t) (e s)).symm.trans
      (letI := specializationOrder W; (irreducibleSetEquivPoints (α := W)).map_rel_iff)
  refine iSup_le fun p => ?_
  have := h (p.map (fun s => (e s).1) fun s t hst => by simpa only [lt_iff_le_not_ge, he] using hst) (e p.last).2
  exact_mod_cast this

end GlobalTheory.DimCut

theorem GlobalTheory.KeyKa.topologicalKrullDim_le_of_finite_zeros : Out.Laws → ∀ (K : Type) [Field K] (x : KeyIn K) (n r : ℕ) (s : Fin r → RR x n) (W : Set x.P.A.left), 1 ≤ n → IsClosed W → W.Nonempty → {y ∈ W | ∀ i, y ∉ Out.nonzeroLocus (s i)}.Finite → topologicalKrullDim W ≤ r := by
  intro _ K _ x n r s W hn hW _ hf
  have := x.P.isAb.proper
  have hA := GlobalTheory.isAmpleLB_of_relAmple_of_isAffine x.P.A x.P.isLB x.P.ample
  refine GlobalTheory.DimCut.topologicalKrullDim_le hW
    (GlobalTheory.DimCut.length_le x.P.A.hom r (fun i => Out.nonzeroLocus (s i)) (fun i => ?_) (fun i y => ?_) W hW hf)
  · have h := hA.isAffineOpen_nonzeroLocus x.P.A.hom hn (GlobalTheory.powSecMk (L := x.P.L) n (s i).f fun a b =>
      ((s i).compat a b).trans (congrArg (· * _) (show ((x.P.L.g a b ^ (n : ℤ) : Γ(x.P.A.left, _)ˣ) :
        Γ(x.P.A.left, x.P.L.U a ⊓ x.P.L.U b)) = (x.P.L.g a b).val ^ n by simp)))
    exact (congrArg IsAffineOpen (GlobalTheory.nonzeroLocus_powSecMk (L := x.P.L) n (s i).f _)).mp h
  · obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show y ∈ ⨆ k, x.P.L.U k by rw [x.P.isLB.cover]; trivial)
    exact ⟨_, (s i).f k, hk, GlobalTheory.nonzeroLocus_inf_chart (s i) k⟩
