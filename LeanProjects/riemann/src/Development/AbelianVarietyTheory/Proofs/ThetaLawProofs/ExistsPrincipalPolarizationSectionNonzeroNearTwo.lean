import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBasisOnAny
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwoPrimeSection

open TopologicalSpace

section General

variable {X : Scheme.{0}} {L : LB X}

theorem exists_global [CompactSpace X] [QuasiSeparatedSpace X] (hL : L.IsLB) (a : Γ(X, ⊤)) {V : X.Opens}
    (hV : X.basicOpen a ≤ V) {θ : ∀ i, Γ(X, V ⊓ L.U i)} (hθ : θ ∈ secOn L V) {g : X} (hg : g ∈ X.basicOpen a)
    {i : L.ι} (hi : g ∈ X.basicOpen (θ i)) : ∃ u : L.Sec, g ∈ Out.nonzeroLocus u := by
  obtain ⟨n, t, ht⟩ := AbLaw.SecOn.exists_pow_smul_eq_restrict hL (V := ⊤) isCompact_univ
    isQuasiSeparated_univ a le_top rfl
    (AbLaw.SecOn.restrict L hV ((AbLaw.SecOn.equivFamilies _ _).symm ⟨θ, hθ⟩))
  have hi' : g ∈ V ⊓ L.U i := X.basicOpen_le _ hi
  have hm : (𝟙 X : X ⟶ X) g ∈ X.basicOpen a ⊓ L.U i := ⟨hg, hi'.2⟩
  refine ⟨AbLaw.SecOn.topEquiv _ t, (mem_nonzeroLocus _ _).2 ⟨i, hi'.2, ?_⟩⟩
  have q := congrArg (fun s => gs (𝟙 X) g _ (GlobalTheory.LB.coord s i)) ht
  have e : gs (𝟙 X) g (L.U i) ((AbLaw.SecOn.topEquiv _ t).f i) =
      gs (𝟙 X) g ⊤ a ^ n * gs (𝟙 X) g (V ⊓ L.U i) (θ i) := by
    refine (gs_res (𝟙 X) g _ hi'.2 _).trans ((gs_res (𝟙 X) g _ hm _).symm.trans (q.symm.trans
      ((gs_mul (𝟙 X) g _ hm _ _).trans (congrArg₂ (· * ·) ?_ (gs_res (𝟙 X) g _ hm _)))))
    exact (gs_res (𝟙 X) g _ hm _).trans ((LBGerm.gs_pow (𝟙 X) g _ hg _ _).trans
      (congrArg (· ^ n) (gs_res (𝟙 X) g _ hg _)))
  rw [e]
  exact (((LBGerm.isUnit_gs_iff (𝟙 X) g ⊤ trivial a).2 hg).pow n).mul
    ((LBGerm.isUnit_gs_iff (𝟙 X) g _ hi' _).2 hi)

def add (s t : L.Sec) : L.Sec :=
  ⟨fun i => s.f i + t.f i, fun i j => by rw [map_add, map_add, s.compat i j, t.compat i j, mul_add]⟩

theorem add_comm' (s t : L.Sec) : add s t = add t s := by
  unfold add
  simp only [add_comm (s.f _)]

theorem mem_nonzeroLocus_add {s t : L.Sec} {y : X} (hs : y ∈ Out.nonzeroLocus s) (ht : y ∉ Out.nonzeroLocus t) :
    y ∈ Out.nonzeroLocus (add s t) := by
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hs
  refine (mem_nonzeroLocus _ _).2 ⟨k, hk, ?_⟩
  have hn : ¬ IsUnit (gs (𝟙 X) y (L.U k) (t.f k)) := fun h => ht ((mem_nonzeroLocus _ _).2 ⟨k, hk, h⟩)
  have e : gs (𝟙 X) y (L.U k) ((add s t).f k) = gs (𝟙 X) y (L.U k) (s.f k) + gs (𝟙 X) y (L.U k) (t.f k) :=
    gs_add (𝟙 X) y _ hk _ _
  rw [e]
  by_contra h
  have h₁ := (IsLocalRing.mem_maximalIdeal _).2 h
  have h₂ := (IsLocalRing.mem_maximalIdeal _).2 hn
  have h₃ := Ideal.sub_mem _ h₁ h₂
  rw [add_sub_cancel_right] at h₃
  exact (IsLocalRing.mem_maximalIdeal _).1 h₃ u

end General

theorem exists_basicOpen_two {R : Type} [CommRing R] {U : Set (PrimeSpectrum R)} (hU : IsOpen U)
    {p q : PrimeSpectrum R} (hp : p ∈ U) (hq : q ∈ U) :
    ∃ r : R, r ∉ p.asIdeal ∧ r ∉ q.asIdeal ∧ ∀ z : PrimeSpectrum R, r ∉ z.asIdeal → z ∈ U := by
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).1 hU.isClosed_compl
  have key : ∀ z : PrimeSpectrum R, z ∈ U ↔ ¬ I ≤ z.asIdeal := fun z => by
    rw [← Set.notMem_compl_iff, hI]
    rfl
  have : ¬ (I : Set R) ⊆ p.asIdeal ∪ q.asIdeal := fun h =>
    (Ideal.subset_union.1 h).elim ((key p).1 hp) ((key q).1 hq)
  obtain ⟨r, hr, hn⟩ := Set.not_subset.1 this
  exact ⟨r, fun h => hn (Or.inl h), fun h => hn (Or.inr h), fun z hz => (key z).2 fun h => hz (h hr)⟩

theorem exists_sec_fibre (hL : Out.Laws) (hL₂ : Out.Laws2) {R : Type} [CommRing R] (Q : Out.PolAV (Sp R)) (p : Sp R) :
    ∃ th : Q.L.Sec, ∃ x : Q.A.left, Q.A.hom x = p ∧ x ∈ Out.nonzeroLocus th := by
  obtain ⟨V, hV, θ, hθ, -, nz⟩ := PushInv.pushInvertible_any hL₂.secBaseChangeAny hL.globalSectionsRank _ Q p
  obtain ⟨g, i, hg, hi⟩ := nz p hV
  obtain ⟨f, hf, hpf⟩ := (isAffineOpen_top (Sp R)).exists_basicOpen_le (V := V) ⟨p, hV⟩ trivial
  have := Q.isAb.proper
  have : CompactSpace Q.A.left := QuasiCompact.compactSpace_of_compactSpace Q.A.hom
  have : QuasiSeparatedSpace Q.A.left := quasiSeparatedSpace_of_quasiSeparated Q.A.hom
  have e := Scheme.preimage_basicOpen_top Q.A.hom f
  obtain ⟨u, hu⟩ := exists_global Q.isLB (Q.A.hom.appTop f) (e.ge.trans (Q.A.hom.preimage_mono hf)) hθ
    (g := g) (e.le (show Q.A.hom g ∈ (Sp R).basicOpen f from hg ▸ hpf)) hi
  exact ⟨u, g, hg, hu⟩

open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

theorem main : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Q : Out.PolAV (Sp R)) (p q : PrimeSpectrum R), ∃ (th : Q.L.Sec) (r : R), r ∉ p.asIdeal ∧ r ∉ q.asIdeal ∧ ∀ z : Sp R, r ∉ z.asIdeal → ∃ x : Q.A.left, Q.A.hom x = z ∧ x ∈ Out.nonzeroLocus th := by
  intro hL hL₂ R _ _ Q p q
  obtain ⟨th, hp, hq⟩ : ∃ th : Q.L.Sec, (∃ x : Q.A.left, Q.A.hom x = p ∧ x ∈ Out.nonzeroLocus th) ∧
      ∃ x : Q.A.left, Q.A.hom x = q ∧ x ∈ Out.nonzeroLocus th := by
    obtain ⟨s, x, hx, hs⟩ := exists_sec_fibre hL hL₂ Q p
    obtain ⟨t, y, hy, ht⟩ := exists_sec_fibre hL hL₂ Q q
    by_cases h₁ : y ∈ Out.nonzeroLocus s
    · exact ⟨s, ⟨x, hx, hs⟩, y, hy, h₁⟩
    by_cases h₂ : x ∈ Out.nonzeroLocus t
    · exact ⟨t, ⟨x, hx, h₂⟩, y, hy, ht⟩
    exact ⟨add s t, ⟨x, hx, mem_nonzeroLocus_add hs h₂⟩, y, hy, add_comm' t s ▸ mem_nonzeroLocus_add ht h₁⟩
  have := Q.isAb.smooth
  obtain ⟨x, hx, hx'⟩ := hp
  obtain ⟨y, hy, hy'⟩ := hq
  obtain ⟨r, h₁, h₂, h₃⟩ := exists_basicOpen_two (R := R) (p := p) (q := q)
    (Q.A.hom.isOpenMap _ (Out.nonzeroLocus th).isOpen) ⟨x, hx', hx⟩ ⟨y, hy', hy⟩
  refine ⟨th, r, h₁, h₂, fun z hz => ?_⟩
  obtain ⟨w, hw, e⟩ := h₃ z hz
  exact ⟨w, e, hw⟩

end GlobalTheory.TwoPrimeSection
