import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage

noncomputable section

namespace GlobalTheory.EtaleExactLat

section Generic

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.EtaleExact TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)

theorem exact_of_tie_lattice (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤)
    (T Yt Z : LocLat G Qp LL O) (ι : LatHom T.L Yt.L) (π : LatHom Yt.L Z.L)
    (h1 : Function.Injective ι.f) (h3 : ∀ z ∈ Z.L.T, ∃ x ∈ Yt.L.T, π.f x = z)
    (h4 : ∀ x ∈ Yt.L.T, π.f x = 0 ↔ ∃ y ∈ T.L.T, ι.f y = x) :
    Function.Injective (W.map ι) ∧ Function.Exact (W.map ι) (W.map π) ∧
      Function.Surjective (W.map π) := by
  have hι : Function.Injective (latMap ι) := fun x y hxy =>
    Subtype.ext (h1 (congrArg Subtype.val hxy))
  have hπ : Function.Surjective (latMap π) := fun y => by
    obtain ⟨x, hx, hxy⟩ := h3 y y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hex : Function.Exact (latMap ι) (latMap π) := fun x => by
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := (h4 x x.2).1 (congrArg Subtype.val hx)
      exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩
    · rintro ⟨y, rfl⟩
      exact Subtype.ext ((h4 _ (latMap ι y).2).2 ⟨y, y.2, rfl⟩)
  haveI := Z.L.free
  have hπR : Function.Surjective ((latMap π).baseChange RW) :=
    LinearMap.lTensor_surjective RW hπ
  have hexR : Function.Exact ((latMap ι).baseChange RW) ((latMap π).baseChange RW) :=
    lTensor_exact RW hex hπ
  have hιR : Function.Injective ((latMap ι).baseChange RW) := by
    obtain ⟨s, hs⟩ := (latMap π).exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hπ)
    obtain ⟨r, hr⟩ : ∃ r, r ∘ₗ latMap ι = LinearMap.id :=
      ((hex.split_tfae hι hπ).out 0 1).1 (show ∃ s, latMap π ∘ₗ s = LinearMap.id from ⟨s, hs⟩)
    refine Function.LeftInverse.injective (g := r.baseChange RW) fun x => ?_
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hr, LinearMap.baseChange_id]
    rfl
  have hsurj : Function.Surjective (W.map π) := by
    rw [← LinearMap.range_eq_top]
    refine eq_top_DD E hm Z _ ?_
    rw [span_range_map, LinearMap.range_eq_top.2 hπR]
  have hcomp : ∀ x, W.map π (W.map ι x) = 0 := fun x => by
    apply E.jD_inj
    rw [jD_map', jD_map', map_zero]
    exact hexR.apply_apply_eq_zero _
  refine ⟨fun x y hxy => E.jD_inj T (hιR ?_), fun y => ⟨fun hy => ?_, ?_⟩, hsurj⟩
  · rw [← jD_map', ← jD_map', hxy]
  · haveI := (W.DD_free Z).1
    obtain ⟨s, hs⟩ := (W.map π).exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hsurj)
    have hs' : ∀ z, W.map π (s z) = z := fun z => LinearMap.congr_fun hs z
    have htop : LinearMap.range (W.map ι) ⊔ LinearMap.range s = ⊤ := by
      refine eq_top_DD E hm Yt _ ?_
      set U := Submodule.span RW (E.jD Yt '' ((LinearMap.range (W.map ι) ⊔ LinearMap.range s :
        Submodule W.EE (W.DD Yt)) : Set (W.DD Yt))) with hU
      have hk : LinearMap.ker ((latMap π).baseChange RW) ≤ U := by
        rw [LinearMap.exact_iff.1 hexR, ← span_range_map E]
        exact Submodule.span_mono (Set.image_mono (SetLike.coe_subset_coe.2 le_sup_left))
      have hmap : U.map ((latMap π).baseChange RW) = ⊤ := by
        rw [eq_top_iff, ← E.jD_span Z, Submodule.span_le]
        rintro _ ⟨z, rfl⟩
        refine ⟨E.jD Yt (s z), Submodule.subset_span
          ⟨s z, Submodule.mem_sup_right ⟨z, rfl⟩, rfl⟩, ?_⟩
        rw [← jD_map', hs']
      have := Submodule.comap_map_eq ((latMap π).baseChange RW) U
      rw [hmap, Submodule.comap_top, sup_eq_left.2 hk] at this
      exact this.symm
    obtain ⟨_, ⟨t, rfl⟩, _, ⟨z, rfl⟩, rfl⟩ := Submodule.mem_sup.1 (htop ▸ Submodule.mem_top (x := y))
    rw [map_add, hcomp, hs', zero_add] at hy
    exact ⟨t, by rw [hy, map_zero, add_zero]⟩
  · rintro ⟨x, rfl⟩
    exact hcomp x

end Generic

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

theorem DD_exact_lattice : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (H : LocHW l P) (E : LocFon l P AI H) (K LL : FinExt l) (s : ℕ) (h : Good K s LL) (T' T T'' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (f : LatHom T'.L T.L) (g : LatHom T.L T''.L), Function.Injective f.f → (∀ z ∈ T''.L.T, ∃ x ∈ T.L.T, g.f x = z) → (∀ x ∈ T.L.T, g.f x = 0 ↔ ∃ y ∈ T'.L.T, f.f y = x) → Function.Injective ((H.W K s LL h).map f) ∧ Function.Surjective ((H.W K s LL h).map g) ∧ Function.Exact ((H.W K s LL h).map f) ((H.W K s LL h).map g) := by
  intro l _ P AI H E K LL s h T' T T'' f g hf hg hfg
  haveI := EtaleExact.finite_OL LL
  haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
  have hp : (P.PD K).p = l := P.PD_p K
  have key := exact_of_tie_lattice (E.E K s LL h).tie
    (EtaleExact.map_ne_top_of_tie (E.E K s LL h).tie
      (by rw [hp]; exact EtaleExact.isUnit_or_dvd_pow P LL)
      (by rw [hp]; exact EtaleExact.sep_RW LL)) T' T T'' f g hf hg hfg
  exact ⟨key.1, key.2.2, key.2.1⟩

end GlobalTheory.EtaleExactLat
