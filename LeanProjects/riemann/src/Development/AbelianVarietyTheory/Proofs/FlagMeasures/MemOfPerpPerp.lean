import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stdform
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovol
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical

namespace GlobalTheory.Mass.RowPerp

section General

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] in

theorem exists_smul_mem {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsLattice K Λ) (v : V) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ Λ := by
  obtain ⟨s, _, b, hbv, hsL⟩ := dualLattice_basis (R := 𝓞 K) Λ hΛ.span_eq_top
  obtain ⟨d, hd0, hd⟩ := dualLattice_denom (R := 𝓞 K) b (Submodule.span (𝓞 K) {v}) (Submodule.fg_span_singleton v)
  refine ⟨d, hd0, (Submodule.span_le.2 ?_) (hd v (Submodule.mem_span_singleton_self v))⟩
  rintro _ ⟨i, rfl⟩
  rw [hbv]; exact hsL i.2

omit [FiniteDimensional K V] in
theorem swap_mem {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {x y : V} (H : h x y ∈ (1 : Submodule (𝓞 K) K)) :
    h y x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 H
  obtain ⟨t, ht⟩ := star_algebraMap_ringOfIntegers_mem_range r
  exact Submodule.mem_one.2 ⟨t, by rw [ht, hr]; exact hs.eq x y⟩

omit [FiniteDimensional K V] [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem swap_zero {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {x y : V} (H : h x y = 0) : h y x = 0 := by
  rw [← hs.eq x y, H, map_zero]

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in

theorem mem_of_perp_perp {h : V →ₗ⋆[K] V →ₗ[K] K} (hn : h.Nondegenerate) (U : Submodule K V) (v : V)
    (H : ∀ y, (∀ u ∈ U, h u y = 0) → h v y = 0) : v ∈ U := by
  have : h v ∈ (U.map h).dualCoannihilator.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro y hy
    rw [Submodule.mem_dualCoannihilator] at hy
    exact H y fun u hu => hy _ ⟨u, hu, rfl⟩
  rw [Subspace.dualCoannihilator_dualAnnihilator_eq] at this
  obtain ⟨u, hu, e⟩ := this
  have : v - u = 0 := hn.1 _ fun y => by rw [map_sub, e, sub_self, LinearMap.zero_apply]
  rwa [sub_eq_zero.1 this]

theorem exists_sub_mem {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hn : h.Nondegenerate)
    {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsLattice K Λ) (hu : IsUnimodular h Λ) (U : Submodule K V) (v : V)
    (H : ∀ y ∈ Λ, (∀ u ∈ U, h u y = 0) → h v y ∈ (1 : Submodule (𝓞 K) K)) : ∃ l ∈ Λ, v - l ∈ U := by
  let P : Submodule K V := perp h U
  have hP : ∀ y, y ∈ P ↔ ∀ u ∈ U, h u y = 0 := fun y => by simp [P, perp, Submodule.mem_iInf]
  let φ : Λ →ₗ[𝓞 K] (V ⧸ P) := (P.mkQ.restrictScalars (𝓞 K)) ∘ₗ Λ.subtype
  have : Module.Finite (𝓞 K) Λ := Module.Finite.iff_fg.mpr hΛ.fg
  have : Module.IsTorsionFree (𝓞 K) (V ⧸ P) := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K _
  have : Module.FinitePresentation (𝓞 K) (LinearMap.range φ) := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) (LinearMap.range φ) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs'⟩ := φ.rangeRestrict.exists_rightInverse_of_surjective φ.range_rangeRestrict
  let p : Λ →ₗ[𝓞 K] Λ := LinearMap.id - s ∘ₗ φ.rangeRestrict
  have hp : ∀ y : Λ, (p y : V) ∈ P := fun y => by
    have e : φ.rangeRestrict (p y) = 0 := by
      have := LinearMap.congr_fun hs' (φ.rangeRestrict y)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
      simp only [p, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, this, sub_self]
    exact (Submodule.Quotient.mk_eq_zero P).1 (congrArg Subtype.val e)
  have hp1 : ∀ y : Λ, (y : V) ∈ P → p y = y := fun y hy => by
    have e : φ.rangeRestrict y = 0 := Subtype.ext ((Submodule.Quotient.mk_eq_zero P).2 hy)
    simp [p, e]
  let g : Λ →ₗ[𝓞 K] K := ((h v).restrictScalars (𝓞 K)) ∘ₗ Λ.subtype ∘ₗ p
  have hg : ∀ y, g y ∈ LinearMap.range (Algebra.linearMap (𝓞 K) K) := fun y =>
    Submodule.mem_one.1 (H _ (p y).2 ((hP _).1 (hp y)))
  let f := g.codRestrictOfInjective (Algebra.linearMap (𝓞 K) K) (IsFractionRing.injective (𝓞 K) K) hg
  have hf : ∀ y, algebraMap (𝓞 K) K (f y) = h v (p y) := fun y =>
    g.codRestrictOfInjective_comp_apply _ _ hg y
  obtain ⟨t, _, b, hbv, hsL⟩ := dualLattice_basis (R := 𝓞 K) Λ hΛ.span_eq_top
  obtain ⟨bs, hbs⟩ := dualLattice_dualBasis h hn b
  obtain ⟨d, hd0, hdL⟩ := dualLattice_denom (R := 𝓞 K) b Λ hΛ.fg
  obtain ⟨w, hw⟩ := dualLattice_repr h hs b bs hbs Λ (fun i => by rw [hbv]; exact hsL i.2) d hd0 hdL f
  refine ⟨w, ?_, mem_of_perp_perp hn U _ fun y hy => ?_⟩
  · rw [← hu, dualBasic_mem_dual]
    exact fun y hy => swap_mem hs (Submodule.mem_one.2 ⟨_, (hw y hy).symm⟩)
  · obtain ⟨c, hc0, hc⟩ := exists_smul_mem hΛ y
    have h1 := hw _ hc
    rw [hf, hp1 _ (by
      change c • y ∈ P
      rw [← algebraMap_smul K c y]; exact P.smul_mem _ ((hP y).2 hy))] at h1
    change h w (c • y) = h v (c • y) at h1
    rw [← algebraMap_smul K c y, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h1
    have := mul_left_cancel₀ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hc0) h1
    rw [map_sub, LinearMap.sub_apply, this, sub_self]

variable {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W]

theorem perp_lattice {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hn : h.Nondegenerate)
    {h0 : W →ₗ⋆[K] W →ₗ[K] K} (hn0 : h0.Nondegenerate) (ι : W →ₗ[K] V) (hι : ∀ x y, h (ι x) (ι y) = h0 x y)
    (X : Submodule K V) (z : V) (T : 𝓞 K) (hT : T ≠ 0) (hz : h z z = -(T : K))
    (hXX : ∀ x ∈ X, ∀ y ∈ X, h x y = 0) (hXz : ∀ x ∈ X, h x z = 0) (hXι : ∀ x ∈ X, ∀ w, h x (ι w) = 0)
    (hzι : ∀ w, h z (ι w) = 0) (hsp : ∀ v, (∀ x ∈ X, h x v = 0) → h z v = 0 → ∃ w, v - ι w ∈ X)
    {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsLattice K Λ) (hu : IsUnimodular h Λ) (hzΛ : z ∈ Λ)
    (hprim : ∀ c : K, (∃ l ∈ Λ, c • z - l ∈ X) → ∃ o : 𝓞 K, (o : K) = c)
    (L : Submodule (𝓞 K) W) (hL : ∀ w, w ∈ L ↔ ∃ l ∈ Λ, ι w - l ∈ X) :
    IsIntLat h0 L ∧ Nonempty ((↥(dual h0 L) ⧸ L.comap (dual h0 L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {T})) := by
  have inj := IsFractionRing.injective (𝓞 K) K
  have hT' : (T : K) ≠ 0 := (map_ne_zero_iff _ inj).mpr hT
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, h x y ∈ (1 : Submodule (𝓞 K) K) := fun x hx y hy => by
    rw [← hu, dualBasic_mem_dual] at hy
    exact hy x hx
  let U : Submodule K V := X ⊔ K ∙ z
  have hU : ∀ v, (∀ u ∈ U, h u v = 0) ↔ (∀ x ∈ X, h x v = 0) ∧ h z v = 0 := fun v => by
    refine ⟨fun H => ⟨fun x hx => H x (Submodule.mem_sup_left hx),
      H z (Submodule.mem_sup_right (Submodule.mem_span_singleton_self z))⟩, fun H u hu => ?_⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    simp [LinearMap.map_smulₛₗ, H.1 x hx, H.2]
  obtain ⟨g, hg⟩ := (U.mkQ ∘ₗ ι).exists_leftInverse_of_injective (by
    rw [eq_bot_iff]
    intro w hw
    have : ι w ∈ U := (Submodule.Quotient.mk_eq_zero U).1 hw
    exact hn0.1 w fun y => by rw [← hι]; exact (hU _).2 ⟨fun x hx => hXι x hx y, hzι y⟩ _ this)
  let π : V →ₗ[K] W := g ∘ₗ U.mkQ
  have hπι : ∀ w, π (ι w) = w := fun w => LinearMap.congr_fun hg w
  have hπU : ∀ u ∈ U, π u = 0 := fun u hu => by
    have : U.mkQ u = 0 := (Submodule.Quotient.mk_eq_zero U).2 hu
    simp only [π, LinearMap.comp_apply, this, map_zero]
  have hπX : ∀ x ∈ X, π x = 0 := fun x hx => hπU x (Submodule.mem_sup_left hx)
  have hπz : π z = 0 := hπU z (Submodule.mem_sup_right (Submodule.mem_span_singleton_self z))
  have hF : ∀ v, (∀ x ∈ X, h x v = 0) → v + (h z v / T) • z - ι (π v) ∈ X := fun v hv => by
    obtain ⟨w, hw⟩ := hsp (v + (h z v / T) • z) (fun x hx => by simp [hv x hx, hXz x hx])
      (by rw [map_add, map_smul, hz, smul_eq_mul]; field_simp; ring)
    have := hπX _ hw
    rw [map_sub, map_add, map_smul, hπz, smul_zero, add_zero, hπι, sub_eq_zero] at this
    rwa [this]
  have hperp : ∀ {w l}, ι w - l ∈ U → ∀ x ∈ X, h x l = 0 := fun {w l} H x hx => by
    have := swap_zero hs ((hU x).2 ⟨fun y hy => hXX y hy x hx, swap_zero hs (hXz x hx)⟩ _ H)
    rwa [map_sub, hXι x hx, zero_sub, neg_eq_zero] at this

  have hpair : ∀ y ∈ L, ∀ l ∈ Λ, (∀ x ∈ X, h x l = 0) → h0 y (π l) ∈ (1 : Submodule (𝓞 K) K) := by
    intro y hy l hl hlX
    obtain ⟨l', hl', e⟩ := (hL y).1 hy
    have e1 := swap_zero hs (hXι _ (hF l hlX) y)
    have e2 := hlX _ e
    rw [map_sub, map_add, map_smul, swap_zero hs (hzι y), smul_zero, add_zero, hι, sub_eq_zero] at e1
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at e2
    rw [← e1, e2]
    exact hint _ hl' _ hl
  have hπl : ∀ {w l}, ι w - l ∈ U → π l = w := fun {w l} H => by
    have := hπU _ H
    rw [map_sub, hπι, sub_eq_zero] at this
    exact this.symm
  refine ⟨⟨⟨?_, ?_⟩, fun x hx y hy => ?_⟩, ?_⟩
  · refine (hΛ.fg.map (π.restrictScalars (𝓞 K))).of_le fun w hw => ?_
    obtain ⟨l, hl, e⟩ := (hL w).1 hw
    exact ⟨l, hl, hπl (Submodule.mem_sup_left e)⟩
  · rw [eq_top_iff]
    intro w _
    obtain ⟨d, hd0, hd⟩ := exists_smul_mem hΛ (ι w)
    have h1 : d • w ∈ L := (hL _).2 ⟨_, hd, by
      rw [← algebraMap_smul K d w, map_smul, algebraMap_smul, sub_self]; exact X.zero_mem⟩
    have h2 := Submodule.smul_mem _ (algebraMap (𝓞 K) K d)⁻¹ (Submodule.subset_span (R := K) h1)
    rwa [← algebraMap_smul K d w, inv_smul_smul₀ ((map_ne_zero_iff _ inj).mpr hd0)] at h2
  · obtain ⟨l, hl, e⟩ := (hL y).1 hy
    rw [← hπl (Submodule.mem_sup_left e)]
    exact hpair x hx l hl (hperp (Submodule.mem_sup_left e))
  let A : Submodule (𝓞 K) V := Λ ⊓ (perp h X).restrictScalars (𝓞 K)
  have hA : ∀ y, y ∈ A ↔ y ∈ Λ ∧ ∀ x ∈ X, h x y = 0 := fun y => by simp [A, perp, Submodule.mem_iInf]
  let f1 : A →ₗ[𝓞 K] dual h0 L := ((π.restrictScalars (𝓞 K)) ∘ₗ A.subtype).codRestrict _ fun l => by
    rw [dualBasic_mem_dual]
    exact fun y hy => hpair y hy l ((hA _).1 l.2).1 ((hA _).1 l.2).2
  have s1 : Function.Surjective f1 := fun w => by
    obtain ⟨l, hl, e⟩ := exists_sub_mem hs hn hΛ hu U (ι w) fun y hy hyU => by
      obtain ⟨a, b⟩ := (hU y).1 hyU
      have e := hF y a
      rw [b, zero_div, zero_smul, add_zero] at e
      have e1 := hXι _ e w
      rw [map_sub, LinearMap.sub_apply, sub_eq_zero, hι] at e1
      refine swap_mem hs ?_
      rw [e1]
      exact (dualBasic_mem_dual h0 L w).1 w.2 _ ((hL _).2 ⟨y, hy, by simpa using X.neg_mem e⟩)
    exact ⟨⟨l, (hA _).2 ⟨hl, hperp e⟩⟩, Subtype.ext (hπl e)⟩
  let g2 : A →ₗ[𝓞 K] K := ((h z).restrictScalars (𝓞 K)) ∘ₗ A.subtype
  have hg2 : ∀ y, g2 y ∈ LinearMap.range (Algebra.linearMap (𝓞 K) K) := fun y =>
    Submodule.mem_one.1 (hint _ hzΛ _ ((hA _).1 y.2).1)
  let f2 := g2.codRestrictOfInjective (Algebra.linearMap (𝓞 K) K) inj hg2
  have hf2 : ∀ y, algebraMap (𝓞 K) K (f2 y) = h z y := fun y =>
    g2.codRestrictOfInjective_comp_apply _ _ hg2 y
  have s2 : Function.Surjective f2 := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    have hbot : (LinearMap.range f2 : Ideal (𝓞 K)) ≠ ⊥ := fun e => by
      have : f2 ⟨z, (hA _).2 ⟨hzΛ, hXz⟩⟩ = 0 := (Submodule.eq_bot_iff _).1 e _ ⟨_, rfl⟩
      have h2 := hf2 ⟨z, (hA _).2 ⟨hzΛ, hXz⟩⟩
      rw [this, map_zero, hz] at h2
      exact hT' (neg_eq_zero.1 h2.symm)
    obtain ⟨γ, hγ, hγ1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := K) hbot hne
    rw [FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 hbot)] at hγ
    obtain ⟨o, ho⟩ := hprim (star γ) (exists_sub_mem hs hn hΛ hu X _ fun y hy hyX => by
      have := hγ _ (FractionalIdeal.mem_coeIdeal_of_mem _ ⟨⟨y, (hA _).2 ⟨hy, hyX⟩⟩, rfl⟩)
      rw [hf2, FractionalIdeal.mem_one_iff] at this
      rw [LinearMap.map_smulₛₗ, starRingEnd_apply, star_star, LinearMap.smul_apply, smul_eq_mul]
      exact Submodule.mem_one.2 this)
    obtain ⟨t, ht⟩ := star_algebraMap_ringOfIntegers_mem_range o
    refine hγ1 ((FractionalIdeal.mem_one_iff _).2 ⟨t, ?_⟩)
    rw [ht]
    change star (o : K) = γ
    rw [ho, star_star]
  have hker : LinearMap.ker ((L.comap (dual h0 L).subtype).mkQ ∘ₗ f1) =
      LinearMap.ker ((Ideal.span {T}).mkQ ∘ₗ f2) := by
    ext l
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Ideal.mem_span_singleton']
    change π l ∈ L ↔ _
    obtain ⟨a, b⟩ := (hA _).1 l.2
    have e := hF l b
    rw [hL]
    constructor
    · rintro ⟨l', hl', e'⟩
      obtain ⟨o, ho⟩ := hprim (h z l / T) ⟨l' - l, Λ.sub_mem hl' a, by
        convert X.add_mem e e' using 1; abel⟩
      refine ⟨o, inj ?_⟩
      rw [hf2, map_mul]
      change (o : K) * T = _
      rw [ho, div_mul_cancel₀ _ hT']
    · rintro ⟨o, ho⟩
      have h1 : h z l / T = algebraMap (𝓞 K) K o := by
        rw [← hf2, ← ho, map_mul]
        exact mul_div_cancel_right₀ _ hT'
      rw [h1, algebraMap_smul] at e
      exact ⟨_, Λ.add_mem a (Λ.smul_mem o hzΛ), by simpa using X.neg_mem e⟩
  exact ⟨(LinearMap.quotKerEquivOfSurjective ((L.comap (dual h0 L).subtype).mkQ ∘ₗ f1)
      ((Submodule.mkQ_surjective _).comp s1)).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ hker ≪≫ₗ
    LinearMap.quotKerEquivOfSurjective ((Ideal.span {T}).mkQ ∘ₗ f2) ((Submodule.mkQ_surjective _).comp s2)⟩

end General

theorem main : ∀ (D : D7) (u : D.what₂.Word), letI := D.host.cmStar; ∀ F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → (PD (D.sp.X 0).hT ∧ Module.finrank D.host.E (D.sp.X 0).V = D.R.k) ∧ ∀ Λ : Cnt.LatV D, IsRowLat D F0 Λ → IsIntLat (D.sp.X 0).hT (Lat.L0X D Λ (lf D F0)) ∧ Nonempty ((↥(dual (D.sp.X 0).hT (Lat.L0X D Λ (lf D F0))) ⧸ (Lat.L0X D Λ (lf D F0)).comap (dual (D.sp.X 0).hT (Lat.L0X D Λ (lf D F0))).subtype) ≃ₗ[𝓞 D.host.E] (𝓞 D.host.E ⧸ Ideal.span {((Lat.Tu D u : ℕ) : 𝓞 D.host.E)})) := by
  intro D u
  letI := D.host.cmStar
  intro F0 he hz
  have hm : 0 < D.R.m := lt_of_lt_of_le (by norm_num) D.R.two_le_m
  refine ⟨⟨fun τ v hv => ?_, ?_⟩, fun Λ hΛ => ?_⟩
  · have h1 := D.sp.X_sig 0 τ
    rw [baseSpace_posDef D.R D.host.F D.sp τ] at h1
    have h2 := Formalism.UG.P.stdform_sig_pos _ h1 (fun k => τ ((D.sp.X 0).frame.repr v k)) fun e => hv (by
      apply (D.sp.X 0).frame.repr.injective
      refine Finsupp.ext fun k => ?_
      simpa using congrFun e k)
    rw [hT_expand]
    simp only [map_sum, map_mul, D.sp.cm.cmUnram.2.1 τ]
    exact h2
  · rw [(D.sp.X 0).rank_eq, D.sp.X_rank 0 (Nat.zero_le _)]
    simp [Ranks.N]
  have hT : Lat.Tu D u ≠ 0 := fun e => by
    have h1 := D.cOf_eq u
    rw [← D.sp_T, show (D.mem u).A.T = 0 from e, Nat.cast_zero, mul_zero] at h1
    exact D.sp.T_prime.ne_zero (Nat.cast_eq_zero.1 h1.symm)
  obtain ⟨-, ⟨h1, h2, h3, -, h4⟩, -⟩ := hΛ
  have hW := (Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).1
  have hs := (D.sp.Y 0).herm
  have hXp : ∀ v, (∀ x ∈ F0.X, (D.sp.Y 0).hT x v = 0) → (D.sp.Y 0).hT F0.z v = 0 →
      v ∈ Lat.orth (D.sp.Y 0) F0.Xplus := fun v a b =>
    (Formalism.MainNotions.mem_orth_iff _ _).2
      (Formalism.MainNotions.hT_zero_of_mem_Xplus F0 (fun i => a _ (Submodule.subset_span ⟨i, rfl⟩)) b)
  have hι : ∀ w, ∀ x ∈ F0.Xplus, (D.sp.Y 0).hT x (D.sp.iXY 0 w) = 0 := fun w =>
    (Formalism.MainNotions.mem_orth_iff _ _).1 (hW.le (Submodule.mem_sup_left ⟨w, rfl⟩))
  have hXX : ∀ y ∈ F0.X, ∀ x ∈ F0.Xplus, (D.sp.Y 0).hT x y = 0 := fun y hy =>
    (Formalism.MainNotions.mem_orth_iff _ _).1 (Formalism.MainNotions.X_le_orth_Xplus F0 hy)
  have hzp : F0.z ∈ F0.Xplus := Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hsub : ∀ v, (∀ x ∈ F0.X, (D.sp.Y 0).hT x v = 0) →
      (v ∈ Lat.Lsub Λ (lf D F0) ↔ ∃ l ∈ Λ, v - l ∈ F0.X) := fun v hv => by
    constructor
    · rintro ⟨a, -⟩
      obtain ⟨l, hl, x, hx, rfl⟩ := Submodule.mem_sup.1 a
      exact ⟨l, hl.1, by simpa using hx⟩
    · rintro ⟨l, hl, e⟩
      refine ⟨Submodule.mem_sup.2 ⟨l, ⟨hl, (Formalism.MainNotions.mem_orth_iff _ _).2 fun x hx => ?_⟩, v - l, e, by abel⟩,
        (Formalism.MainNotions.mem_orth_iff _ _).2 hv⟩
      have := hXX _ e x (Submodule.mem_sup_left hx)
      rwa [map_sub, hv x hx, zero_sub, neg_eq_zero] at this
  have hXz : ∀ x ∈ F0.X, (D.sp.Y 0).hT x F0.z = 0 := fun x hx => swap_zero hs (hXX x hx _ hzp)
  refine perp_lattice hs (D.sp.Y 0).nondeg (D.sp.X 0).nondeg (D.sp.iXY 0) (D.sp.iXY_isom 0 hm) F0.X F0.z _
    (Nat.cast_ne_zero.2 hT) (by rw [F0.z_norm]; simp) (fun x hx y hy => hXX y hy x (Submodule.mem_sup_left hx)) hXz
    (fun x hx w => hι w x (Submodule.mem_sup_left hx)) (fun w => hι w _ hzp) (fun v a b => ?_) h1 h2 h3.1
    (fun c hc => h4 c ((hsub _ fun x hx => by rw [map_smul, hXz x hx, smul_zero]).2 hc)) _ fun w => ?_
  · obtain ⟨_, ⟨w, rfl⟩, x, hx, rfl⟩ := Submodule.mem_sup.1 (hW.ge (hXp v a b))
    exact ⟨w, by simpa using hx⟩
  · rw [← hsub _ fun x hx => hι w x (Submodule.mem_sup_left hx)]
    exact ⟨fun a => a.1, fun a => ⟨a, hι w _ hzp⟩⟩

end GlobalTheory.Mass.RowPerp
