import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsWeightZeroSectionOfPeriodSpaceFunction

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat

noncomputable section

namespace GlobalTheory.CompSystem

open GlobalTheory.CompIdem GlobalTheory.CompFun

theorem orthogonal_of_fibres {R ι : Type} [CommRing R] [Fintype ι] (e : ι → R) (he : ∀ i, IsIdempotentElem (e i))
    (k : PrimeSpectrum R → ι) (h : ∀ i z, e i ∉ z.asIdeal ↔ k z = i) :
    (∀ i j, i ≠ j → e i * e j = 0) ∧ ∑ i, e i = 1 := by
  classical
  have ho : ∀ i j, i ≠ j → e i * e j = 0 := by
    intro i j hij
    refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem ((he i).mul (he j)) IsIdempotentElem.zero ?_
    ext z
    refine iff_of_false (fun hz => ?_) (fun hz => hz (zero_mem _))
    have hz' : e i * e j ∉ z.asIdeal := hz
    exact hij (((h i z).1 fun h1 => hz' (z.asIdeal.mul_mem_right _ h1)).symm.trans
      ((h j z).1 fun h1 => hz' (z.asIdeal.mul_mem_left _ h1)))
  refine ⟨ho, ?_⟩
  have hs : IsIdempotentElem (∑ i, e i) :=
    (OrthogonalIdempotents.mk he fun i j hij => ho i j hij).isIdempotentElem_sum
  refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem hs IsIdempotentElem.one ?_
  ext z
  refine iff_of_true (fun hz => ?_) (fun hz => z.2.ne_top ((Ideal.eq_top_iff_one _).2 hz))
  refine (h (k z) z).2 rfl ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (k z))] at hz
  refine (Ideal.add_mem_iff_left _ (sum_mem fun j hj => ?_)).1 hz
  by_contra hc
  exact (Finset.mem_erase.1 hj).1 ((h j z).1 hc).symm

theorem exists_complex_point {K : Type} [Field K] (σ : K →+* ℂ) {Y : Scheme.{0}} (s : Y ⟶ Sp K)
    [LocallyOfFiniteType s] {V : Set Y} (hV : IsOpen V) (hne : V.Nonempty) :
    ∃ p : Sp ℂ ⟶ Y, p ≫ s = spMap σ ∧ p (IsLocalRing.closedPoint ℂ) ∈ V := by
  let g := pullback.snd s (spMap σ)
  let π := pullback.fst s (spMap σ)
  have hy : Surjective (spMap σ) :=
    ⟨fun a => ⟨Classical.arbitrary _, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  have := LocallyOfFiniteType.jacobsonSpace g
  obtain ⟨z, hz⟩ := hne
  obtain ⟨w, rfl⟩ := π.surjective z
  obtain ⟨x, hx, hc'⟩ := nonempty_inter_closedPoints (Z := π ⁻¹' V) ⟨w, hz⟩
    (hV.preimage π.continuous).isLocallyClosed
  have hc : IsClosed ({x} : Set _) := hc'
  refine ⟨pointOfClosedPoint g x hc ≫ π, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
  · exact (congrArg (π · ∈ V) (pointOfClosedPoint_apply g x hc _)).mpr hx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H}
  {l : Level H} {Xo : Moduli D l} {c : Coeff l}

theorem exists_indicator_test (hA : AllTest Xo c) (U : Set (Xo.XF c)) (hU : IsClopen U) :
    ∃ χ ∈ sec Xo c 0 0, (∀ (p : TRing c.F) (y : FrPt Xo c p.R), IsIdempotentElem (χ p y) ∧
      ∀ z : PrimeSpectrum p.R, χ p y ∉ z.asIdeal ↔ basePt y z ∈ U) ∧
      ∀ (S : Type) [CommRing S] [IsReduced S] [Algebra c.F S] (y : FrPt Xo c S),
      IsIdempotentElem (evR Xo c χ y) ∧
        ∀ z : PrimeSpectrum S, evR Xo c χ y ∉ z.asIdeal ↔ basePt y z ∈ U := by
  have hex : ∀ (p : TRing c.F) (y : FrPt Xo c p.R), ∃ e : p.R, IsIdempotentElem e ∧
      ∀ z : PrimeSpectrum p.R, e ∉ z.asIdeal ↔ basePt y z ∈ U := by
    intro p y
    obtain ⟨e, he, h⟩ := PrimeSpectrum.isClopen_iff.1 (hU.preimage (basePt y).continuous)
    exact ⟨e, he, fun z => (Set.ext_iff.1 h z).symm⟩
  choose χ hi hχ using hex
  have hmap : ∀ (p : TRing c.F) (S : Type) [CommRing S] [Algebra c.F S] (φ : p.R →ₐ[c.F] S) (y : FrPt Xo c p.R)
      (w : FrPt Xo c S), w.x = spMap φ.toRingHom ≫ y.x →
      ∀ z : PrimeSpectrum S, φ (χ p y) ∉ z.asIdeal ↔ basePt w z ∈ U := by
    intro p S _ _ φ y w h z
    rw [basePt_map φ y w h]
    exact hχ p y (PrimeSpectrum.comap φ.toRingHom z)
  have hw : ∀ (p : TRing c.F) (t : Ix D → (p.R)ˣ), wchar (ex D 0 0) t = 1 := by
    intro p t
    refine Finset.prod_eq_one fun i _ => ?_
    have : ex D 0 0 i = 0 := by rcases i with _ | ⟨τ, i⟩ <;> simp [ex]
    rw [this, pow_zero]
  refine ⟨χ, ⟨fun p q φ y z h => ?_, fun p t y y' h => ?_⟩, fun p y => ⟨hi p y, hχ p y⟩, fun S _ _ _ y => ?_⟩
  · refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem (hi q z) ((hi p y).map φ) ?_
    ext w
    exact (hχ q z w).trans (hmap p q.R φ y z h.1 w).symm
  · rw [hw, _root_.one_mul]
    refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem (hi p y') (hi p y) ?_
    ext w
    have := hχ p y' w
    rw [basePt_congr y y' h.1] at this
    exact this.trans (hχ p y w).symm
  · have h := hA S y
    have e : evR Xo c χ y = h.choose_spec.choose (χ h.choose h.choose_spec.choose_spec.choose) := dif_pos h
    rw [e]
    exact ⟨(hi _ _).map _, hmap _ S _ _ y h.choose_spec.choose_spec.choose_spec.1⟩

theorem exists_index_map (σ : c.F →+* ℂ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (hcl : FnAlgClosed Xo c) :
    ∃ k : Xo.XF c → Fin F.n, (∀ i, IsClopen (k ⁻¹' {i})) ∧ ∀ (y : FrPt Xo c (CAt σ)) (i : Fin F.n) P,
      IsPeriod (F.Di i) ty P → y.x = F.u i P → k (basePt (S := CAt σ) y (IsLocalRing.closedPoint ℂ)) = i := by
  classical
  have := CompFin.quasiCompact_alt Xo
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have := c.fin
  obtain ⟨t, ht, hcont⟩ := exists_index F
  have := CompFin.isNoetherian_XF Xo c
  let s : Xo.XF c ⟶ Sp c.F := pullback.snd _ _
  let pr : Xo.XF c ⟶ Xo.X := pullback.fst _ _
  have hover : ∀ p : Sp ℂ ⟶ Xo.XF c, p ≫ s = spMap σ →
      (p ≫ pr) ≫ Xo.s = spMap (σ.comp (IntermediateField.inclusion c.le).toRingHom) := by
    intro p hp
    rw [Category.assoc, pullback.condition, ← Category.assoc, hp, CompIdem.spMap_comp]
  have hconst : ∀ p q : Sp ℂ ⟶ Xo.XF c, p ≫ s = spMap σ → q ≫ s = spMap σ →
      p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent (q (IsLocalRing.closedPoint ℂ)) →
      t (p ≫ pr) = t (q ≫ pr) := by
    refine const_on_component_of_closed σ s (fun Z x hx => ?_) (fun x => t (x ≫ pr))
      (fun m B y hB hy hh => hcont m B _ hB (fun b hb => hover _ (hy b hb)) (GlobalTheory.LocLift.isHolTo_comp_hom hh _))
    have hx' : IsIntegral c.F (A := kap Z) x := hx
    obtain ⟨k, hk⟩ := hcl Z (algebraMap (kap Z) (Om Z) x) hx'.algebraMap.isAlgebraic
    rw [IsScalarTower.algebraMap_apply c.F (kap Z) (Om Z)] at hk
    exact ⟨k, (algebraMap (kap Z) (Om Z)).injective hk⟩
  have hex : ∀ z : Xo.XF c, ∃ i : Fin F.n, ∃ p : Sp ℂ ⟶ Xo.XF c, p ≫ s = spMap σ ∧
      p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent z ∧ t (p ≫ pr) = i := by
    intro z
    obtain ⟨p, hp, hz⟩ := exists_complex_point σ s (isOpen_connectedComponent_of_noetherianSpace z)
      ⟨z, mem_connectedComponent⟩
    obtain ⟨i, P, hP, e⟩ := F.onto _ (hover p hp)
    exact ⟨i, p, hp, hz, e ▸ ht i P hP⟩
  choose k hk using hex
  have hk' : ∀ (z : Xo.XF c) (q : Sp ℂ ⟶ Xo.XF c), q ≫ s = spMap σ →
      q (IsLocalRing.closedPoint ℂ) ∈ connectedComponent z → t (q ≫ pr) = k z := by
    intro z q hq hz
    obtain ⟨p, hp, h1, h2⟩ := hk z
    rw [← h2]
    exact hconst q p hq hp (connectedComponent_eq h1 ▸ hz)
  have hkc : ∀ z w, w ∈ connectedComponent z → k w = k z := by
    intro z w h
    obtain ⟨p, hp, h1, h2⟩ := hk w
    exact Fin.ext (h2.symm.trans (hk' z p hp (connectedComponent_eq h ▸ h1)))
  refine ⟨k, fun i => ?_, fun y i P hP hy => ?_⟩
  · refine ⟨⟨isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩, isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩
    · exact ⟨connectedComponent z, fun w hw h => hz ((hkc z w hw).symm.trans h),
        isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩
    · exact ⟨connectedComponent z, fun w hw => (hkc z w hw).trans hz,
        isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩
  · let p : Sp ℂ ⟶ Xo.XF c := basePt (S := CAt σ) y
    have hp : p ≫ s = spMap σ := pullback.lift_snd _ _ _
    have hp' : t (p ≫ pr) = i := by
      have : p ≫ pr = F.u i P := (pullback.lift_fst _ _ _).trans hy
      rw [this]
      exact ht i P hP
    exact Fin.ext ((hk' _ p hp mem_connectedComponent).symm.trans hp')

theorem exists_orthogonal_idempotents : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), FnAlgClosed Xo c → ∃ χ : Fin F.n → Rul Xo c, (∀ i, χ i ∈ sec Xo c 0 0) ∧ (∀ i, χ i * χ i = χ i) ∧ (∀ i i', i ≠ i' → χ i * χ i' = 0) ∧ ∑ i, χ i = 1 ∧ ∀ (y : FrPt Xo c (CAt σ)) (i i' : Fin F.n) P, IsPeriod (F.Di i') ty P → y.x = F.u i' P → toC (evR Xo c (χ i) y) = if i' = i then 1 else 0 := by
  intro E _ _ _ H D l Xo c σ g ty F hcl
  classical
  have hA := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.allSixLaws.1.secBaseChange E H D l Xo c
  obtain ⟨k, hk, hv⟩ := exists_index_map σ F hcl
  choose χ h1 h2 h3 using fun i => exists_indicator_test hA _ (hk i)
  have ho := fun (p : TRing c.F) (y : FrPt Xo c p.R) => orthogonal_of_fibres (fun i => χ i p y)
    (fun i => (h2 i p y).1) (fun z => k (basePt y z)) fun i z => (h2 i p y).2 z
  refine ⟨χ, h1, fun i => ?_, fun i j hij => ?_, ?_, fun y i i' P hP hy => ?_⟩
  · funext p y
    exact (h2 i p y).1.eq
  · funext p y
    exact (ho p y).1 i j hij
  · funext p y
    rw [Finset.sum_apply, Finset.sum_apply]
    exact (ho p y).2
  · have : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
    obtain ⟨h4, h5⟩ := h3 i (CAt σ) y
    let v : ℂ := evR Xo c (χ i) (S := CAt σ) y
    have h6 : v ∉ (IsLocalRing.closedPoint ℂ).asIdeal ↔
        k (basePt (S := CAt σ) y (IsLocalRing.closedPoint ℂ)) = i := h5 (IsLocalRing.closedPoint ℂ)
    have h8 : v ∉ (IsLocalRing.closedPoint ℂ).asIdeal ↔ v ≠ 0 := by
      show v ∉ IsLocalRing.maximalIdeal ℂ ↔ _
      rw [IsLocalRing.notMem_maximalIdeal, isUnit_iff_ne_zero]
    rw [h8, hv y i' P hP hy] at h6
    have h9 : IsIdempotentElem v := h4
    show v = _
    split_ifs with h
    · exact (IsIdempotentElem.iff_eq_zero_or_one.1 h9).resolve_left (h6.2 h)
    · exact not_not.1 (mt h6.1 h)

end GlobalTheory.CompSystem
