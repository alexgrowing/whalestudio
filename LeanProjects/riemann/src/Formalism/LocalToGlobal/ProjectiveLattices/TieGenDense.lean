import Formalism.LocalToGlobal.ProjectiveLattices.TieRecog
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GGConn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStatementPfLA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.T0 Filter Topology

section An

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem analyticOnNhd_dom (X : Data E r) {F : Frame X.Ψ r → ℂ} (hF : DifferentiableOn ℂ F X.dom) :
    AnalyticOnNhd ℂ F X.dom := by
  let e : Frame X.Ψ r ≃L[ℂ] (Fin (Module.finrank ℂ (Frame X.Ψ r)) → ℂ) :=
    (Module.finBasis ℂ (Frame X.Ψ r)).equivFun.toContinuousLinearEquiv
  have hU : IsOpen (e.symm ⁻¹' X.dom) := (FourierCoefficientDomain.isOpen_dom X).preimage e.symm.continuous
  have hd : DifferentiableOn ℂ (F ∘ e.symm) (e.symm ⁻¹' X.dom) :=
    hF.comp e.symm.differentiableOn (fun _ h => h)
  have ha := ReciprocityTheory.AnForm.Osgood.osgood _ _ _ hU hd
  intro z hz
  have hF' : F = (F ∘ e.symm) ∘ e := by ext y; simp
  rw [hF']
  exact (ha (e z) (by simpa using hz)).comp (e.toContinuousLinearMap.analyticAt z)

theorem interior_closure_zero (X : Data E r) {F : Frame X.Ψ r → ℂ} (hF : DifferentiableOn ℂ F X.dom)
    (hne : ∃ x ∈ X.dom, F x ≠ 0) : interior (closure {x | x ∈ X.dom ∧ F x = 0}) = ∅ := by
  have hA := analyticOnNhd_dom X hF
  have hc : IsPreconnected X.dom := (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected (E := E) r X).isPreconnected
  have hO := FourierCoefficientDomain.isOpen_dom X
  by_contra hU
  obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.2 hU
  have hyc : y ∈ closure X.dom := closure_mono (fun x hx => hx.1) (interior_subset hy)
  obtain ⟨z, hzV, hzd⟩ := mem_closure_iff_nhds.1 hyc _ (isOpen_interior.mem_nhds hy)
  have hev : F =ᶠ[𝓝 z] 0 := by
    filter_upwards [isOpen_interior.mem_nhds hzV, hO.mem_nhds hzd] with w hwV hwd
    have hcont : ContinuousAt F w := (hF.differentiableAt (hO.mem_nhds hwd)).continuousAt
    by_contra hw0
    have hfr := mem_closure_iff_frequently.1 (interior_subset hwV)
    obtain ⟨v, hv0, hvZ⟩ := ((hcont.eventually_ne hw0).and_frequently hfr).exists
    exact hv0 hvZ.2
  obtain ⟨x, hx, hx0⟩ := hne
  exact hx0 (hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hzd hev hx)

end An

variable {D : D7} {T : Top D}

theorem countable_closure {A : Type} [CommRing A] {s : Set A} (hs : s.Countable) :
    (Subring.closure s : Set A).Countable := by
  have hs' : Countable s := hs.to_subtype
  haveI : Countable (MvPolynomial s ℤ) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine MvPolynomial.cardinalMk_le_max.trans ?_
    simp [Cardinal.mk_le_aleph0]
  have e : ((Subring.closure s : Subring A) : Set A) = ((Algebra.adjoin ℤ s : Subalgebra ℤ A) : Set A) := by
    rw [Algebra.adjoin_int]
    rfl
  rw [e, Algebra.adjoin_eq_range, AlgHom.coe_range]
  exact Set.countable_range _

theorem countable_Rg (h : LawsP T) {j : ℕ} (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    (Z : Comp (T.Q.Xo j) T.Q.c) : (RgR h hj hG Z : Set (AC Z)).Countable := by
  haveI : Countable T.Q.c.F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := T.Q.c.F)
  haveI : Countable (WeightFamilies.Wt D j) := by
    have hi : Function.Injective (fun w : WeightFamilies.Wt D j => (w.aP, w.aM, w.n)) := by
      rintro ⟨a1, b1, _, _, n1, _⟩ ⟨a2, b2, _, _, n2, _⟩ e
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      rfl
    exact hi.countable
  have hgen : (gensR h j).Countable := by
    have hsub : gensR h j ⊆ ⋃ u : WeightFamilies.Wt D j,
        Set.range (fun F : (recB h.toLawsCore).Cusp j u => AddMonoidAlgebra.single (wtZ (wtA u) u.n) F.1) := by
      rintro b ⟨u, F, rfl⟩
      exact Set.mem_iUnion.2 ⟨u, F, rfl⟩
    refine Set.Countable.mono hsub (Set.countable_iUnion fun u => ?_)
    haveI : Module.Finite T.Q.c.F ((recB h.toLawsCore).Cusp j u) := (recB h.toLawsCore).fdC j u
    haveI : Countable ((recB h.toLawsCore).Cusp j u) :=
      Finsupp.Countable.of_moduleFinite (R := T.Q.c.F) (M := (recB h.toLawsCore).Cusp j u)
    exact Set.countable_range _
  haveI : Countable (BcR h j) := (countable_closure hgen).to_subtype
  rw [show (RgR h hj hG Z : Set (AC Z)) = Set.range (PsiC h hj hG Z) from RingHom.coe_range _]
  exact Set.countable_range _

set_option maxHeartbeats 1600000 in

theorem mem_genRg_of (h : LawsP T) {j : ℕ} (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z))
    {κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp} (hκ : KappaTie j hG κ) (hd : DTie h j hG d)
    (Z : Comp (T.Q.Xo j) T.Q.c)
    (hbir : ∀ a : Om Z, ∃ (G : WTZ D.host.E) (f p : AC Z), f ∈ (rdData1 h hj hG d hκ hd Z).Rg ∧ p ∈ (rdData1 h hj hG d hκ hd Z).Rg ∧
      f ∈ AG Z G ∧ p ∈ AG Z G ∧ p ≠ 0 ∧ p ∈ Algebra.adjoin T.Q.c.F (Set.range fun i => d.w i Z) ∧
      a = ratio (Ω := Om Z) f p)
    {x : Frame ((T.U j T.σ₀).X (κ Z)).Ψ D.R.r} (hx : x ∈ ((T.U j T.σ₀).X (κ Z)).dom)
    (hgood : ∀ (g : AC Z) (hg : g ∈ (rdData1 h hj hG d hκ hd Z).Rg), g ≠ 0 → ∀ G ∈ (rdData1 h hj hG d hκ hd Z).WE, g ∈ AG Z G → (rdData1 h hj hG d hκ hd Z).rd ⟨g, hg⟩ x ≠ 0) :
    x ∈ genRg (rdData1 h hj hG d hκ hd Z) := by
  have hRd := tieRd1 h hj hG d hκ hd Z
  obtain ⟨uL, W, hev, hwL, hwv, hB1⟩ := id hd
  have hwL0 : ∀ i, d.w i Z ∈ AG Z d.wL := fun i => by rw [hwv i Z, hwL]; exact valC_mem _ _ _ _ _
  have rep : ∀ a : Om Z, ∃ (G : WTZ D.host.E) (f p : AC Z) (_ : f ∈ (rdData1 h hj hG d hκ hd Z).Rg) (_ : p ∈ (rdData1 h hj hG d hκ hd Z).Rg),
      f ∈ AG Z G ∧ p ∈ AG Z G ∧ p ≠ 0 ∧ G ∈ (rdData1 h hj hG d hκ hd Z).WE ∧ a = ratio (Ω := Om Z) f p := by
    intro a
    obtain ⟨G, f, p, hf, hp, hfA, hpA, hp0, hpw, ha⟩ := hbir a
    obtain ⟨r0, hr0⟩ := mem_AG.1 hpA
    have hr : r0 ≠ 0 := fun h0 => hp0 (by rw [hr0, h0, AddMonoidAlgebra.single_zero])
    obtain ⟨m, hm⟩ := adjoin_weight hwL0 hpw G (by rw [hr0]; simpa using hr)
    exact ⟨G, f, p, hf, hp, hfA, hpA, hp0, by rw [hm]; exact (rdData1 h hj hG d hκ hd Z).WE.nsmul_mem (rdData1 h hj hG d hκ hd Z).wL_mem m, ha⟩
  choose Gr fr pr hfr hpr hfAr hpAr hp0r hGEr har using rep
  have sng : ∀ {G : WTZ D.host.E} {q : AC Z}, q ∈ AG Z G → q ≠ 0 → ∃ s : Om Z, q = AddMonoidAlgebra.single G s ∧ s ≠ 0 :=
    fun {G q} hqA hq0 => by
      obtain ⟨s, hs⟩ := mem_AG.1 hqA
      exact ⟨s, hs, fun h0 => hq0 (by rw [hs, h0, AddMonoidAlgebra.single_zero])⟩
  have cons : ∀ (a : Om Z) {G' : WTZ D.host.E} (f' q : AC Z) (hf' : f' ∈ (rdData1 h hj hG d hκ hd Z).Rg) (hq : q ∈ (rdData1 h hj hG d hκ hd Z).Rg),
      f' ∈ AG Z G' → q ∈ AG Z G' → q ≠ 0 → G' ∈ (rdData1 h hj hG d hκ hd Z).WE → a = ratio (Ω := Om Z) f' q →
        (rdData1 h hj hG d hκ hd Z).rd ⟨fr a, hfr a⟩ x / (rdData1 h hj hG d hκ hd Z).rd ⟨pr a, hpr a⟩ x = (rdData1 h hj hG d hκ hd Z).rd ⟨f', hf'⟩ x / (rdData1 h hj hG d hκ hd Z).rd ⟨q, hq⟩ x := by
    intro a G' f' q hf' hq hf'A hqA hq0 hG'E ha'
    have hp1 := hgood _ (hpr a) (hp0r a) _ (hGEr a) (hpAr a)
    have hq1 := hgood _ hq hq0 _ hG'E hqA
    obtain ⟨r1, e1⟩ := mem_AG.1 (hfAr a)
    obtain ⟨r2, e2, hr2⟩ := sng (hpAr a) (hp0r a)
    obtain ⟨r3, e3⟩ := mem_AG.1 hf'A
    obtain ⟨r4, e4, hr4⟩ := sng hqA hq0
    have k1 := har a
    rw [e1, e2, ratio_single _ _ _ hr2] at k1
    rw [e3, e4, ratio_single _ _ _ hr4] at ha'
    have hx' : r1 * r4 = r3 * r2 := (div_eq_div_iff hr2 hr4).1 (k1.symm.trans ha')
    have hcross : fr a * q = f' * pr a := by
      rw [e1, e2, e3, e4, AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single,
        add_comm G' (Gr a), hx']
    have key := congrArg (fun g => (rdData1 h hj hG d hκ hd Z).rd g x)
      (show (⟨fr a, hfr a⟩ * ⟨q, hq⟩ : (rdData1 h hj hG d hκ hd Z).Rg) = ⟨f', hf'⟩ * ⟨pr a, hpr a⟩ from Subtype.ext hcross)
    simp only [map_mul, Pi.mul_apply] at key
    rw [div_eq_div_iff hp1 hq1]
    linear_combination key
  let Pf : Om Z → ℂ := fun a => (rdData1 h hj hG d hκ hd Z).rd ⟨fr a, hfr a⟩ x / (rdData1 h hj hG d hκ hd Z).rd ⟨pr a, hpr a⟩ x
  have hrat1 : ∀ {G : WTZ D.host.E} {q : AC Z}, q ∈ AG Z G → q ≠ 0 → ratio (Ω := Om Z) q q = 1 := by
    intro G q hqA hq0
    obtain ⟨s, rfl, hs⟩ := sng hqA hq0
    rw [ratio_single _ _ _ hs, div_self hs]
  have hrat0 : ∀ {G : WTZ D.host.E} {q : AC Z}, q ∈ AG Z G → q ≠ 0 → ratio (Ω := Om Z) (0 : AC Z) q = 0 := by
    intro G q hqA hq0
    obtain ⟨s, rfl, hs⟩ := sng hqA hq0
    rw [← AddMonoidAlgebra.single_zero G, ratio_single _ _ _ hs, zero_div]
  have hmulE : ∀ a b : Om Z, a * b = ratio (Ω := Om Z) (fr a * fr b) (pr a * pr b) := by
    intro a b
    obtain ⟨r1, e1⟩ := mem_AG.1 (hfAr a)
    obtain ⟨r2, e2, hr2⟩ := sng (hpAr a) (hp0r a)
    obtain ⟨r3, e3⟩ := mem_AG.1 (hfAr b)
    obtain ⟨r4, e4, hr4⟩ := sng (hpAr b) (hp0r b)
    have ka := har a
    have kb := har b
    rw [e1, e2, ratio_single _ _ _ hr2] at ka
    rw [e3, e4, ratio_single _ _ _ hr4] at kb
    rw [e1, e2, e3, e4, AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single,
      ratio_single _ _ _ (mul_ne_zero hr2 hr4), ka, kb, div_mul_div_comm]
  have haddE : ∀ a b : Om Z, a + b = ratio (Ω := Om Z) (fr a * pr b + fr b * pr a) (pr a * pr b) := by
    intro a b
    obtain ⟨r1, e1⟩ := mem_AG.1 (hfAr a)
    obtain ⟨r2, e2, hr2⟩ := sng (hpAr a) (hp0r a)
    obtain ⟨r3, e3⟩ := mem_AG.1 (hfAr b)
    obtain ⟨r4, e4, hr4⟩ := sng (hpAr b) (hp0r b)
    have ka := har a
    have kb := har b
    rw [e1, e2, ratio_single _ _ _ hr2] at ka
    rw [e3, e4, ratio_single _ _ _ hr4] at kb
    rw [e1, e2, e3, e4, AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single,
      AddMonoidAlgebra.single_mul_single, add_comm (Gr b) (Gr a), ← AddMonoidAlgebra.single_add,
      ratio_single _ _ _ (mul_ne_zero hr2 hr4), ka, kb, div_add_div _ _ hr2 hr4]
    ring
  have hAGm : ∀ a b : Om Z, pr a * pr b ∈ AG Z (Gr a + Gr b) := fun a b =>
    SetLike.mul_mem_graded (hpAr a) (hpAr b)
  have hne2 : ∀ a b : Om Z, pr a * pr b ≠ 0 := fun a b => mul_ne_zero_AG (hpAr a) (hpAr b) (hp0r a) (hp0r b)
  have hWE2 : ∀ a b : Om Z, Gr a + Gr b ∈ (rdData1 h hj hG d hκ hd Z).WE := fun a b => add_mem (hGEr a) (hGEr b)
  have hpx : ∀ a, (rdData1 h hj hG d hκ hd Z).rd ⟨pr a, hpr a⟩ x ≠ 0 := fun a => hgood _ (hpr a) (hp0r a) _ (hGEr a) (hpAr a)
  let P : Om Z →+* ℂ :=
    { toFun := Pf
      map_one' := by
        show (rdData1 h hj hG d hκ hd Z).rd ⟨fr 1, hfr 1⟩ x / (rdData1 h hj hG d hκ hd Z).rd ⟨pr 1, hpr 1⟩ x = 1
        rw [cons 1 (pr 1) (pr 1) (hpr 1) (hpr 1) (hpAr 1) (hpAr 1) (hp0r 1) (hGEr 1)
          (hrat1 (hpAr 1) (hp0r 1)).symm, div_self (hpx 1)]
      map_mul' := fun a b => by
        show (rdData1 h hj hG d hκ hd Z).rd ⟨fr (a * b), hfr _⟩ x / (rdData1 h hj hG d hκ hd Z).rd ⟨pr (a * b), hpr _⟩ x = Pf a * Pf b
        rw [cons (a * b) (fr a * fr b) (pr a * pr b) (mul_mem (hfr a) (hfr b)) (mul_mem (hpr a) (hpr b))
          (SetLike.mul_mem_graded (hfAr a) (hfAr b)) (hAGm a b) (hne2 a b) (hWE2 a b) (hmulE a b)]
        rw [show (⟨fr a * fr b, mul_mem (hfr a) (hfr b)⟩ : (rdData1 h hj hG d hκ hd Z).Rg) = ⟨fr a, hfr a⟩ * ⟨fr b, hfr b⟩ from rfl,
          show (⟨pr a * pr b, mul_mem (hpr a) (hpr b)⟩ : (rdData1 h hj hG d hκ hd Z).Rg) = ⟨pr a, hpr a⟩ * ⟨pr b, hpr b⟩ from rfl,
          map_mul, map_mul, Pi.mul_apply, Pi.mul_apply, mul_div_mul_comm]
      map_zero' := by
        show (rdData1 h hj hG d hκ hd Z).rd ⟨fr 0, hfr 0⟩ x / (rdData1 h hj hG d hκ hd Z).rd ⟨pr 0, hpr 0⟩ x = 0
        rw [cons 0 0 (pr 0) (zero_mem _) (hpr 0) (zero_mem _) (hpAr 0) (hp0r 0) (hGEr 0)
          (hrat0 (hpAr 0) (hp0r 0)).symm]
        rw [show (⟨0, zero_mem _⟩ : (rdData1 h hj hG d hκ hd Z).Rg) = 0 from rfl, map_zero, Pi.zero_apply, zero_div]
      map_add' := fun a b => by
        show (rdData1 h hj hG d hκ hd Z).rd ⟨fr (a + b), hfr _⟩ x / (rdData1 h hj hG d hκ hd Z).rd ⟨pr (a + b), hpr _⟩ x = Pf a + Pf b
        have hsA : fr a * pr b + fr b * pr a ∈ AG Z (Gr a + Gr b) := by
          refine add_mem (SetLike.mul_mem_graded (hfAr a) (hpAr b)) ?_
          rw [add_comm]; exact SetLike.mul_mem_graded (hfAr b) (hpAr a)
        have hsR : fr a * pr b + fr b * pr a ∈ (rdData1 h hj hG d hκ hd Z).Rg :=
          add_mem (mul_mem (hfr a) (hpr b)) (mul_mem (hfr b) (hpr a))
        rw [cons (a + b) _ (pr a * pr b) hsR (mul_mem (hpr a) (hpr b)) hsA (hAGm a b) (hne2 a b) (hWE2 a b)
          (haddE a b)]
        rw [show (⟨fr a * pr b + fr b * pr a, hsR⟩ : (rdData1 h hj hG d hκ hd Z).Rg) =
            ⟨fr a, hfr a⟩ * ⟨pr b, hpr b⟩ + ⟨fr b, hfr b⟩ * ⟨pr a, hpr a⟩ from rfl,
          show (⟨pr a * pr b, mul_mem (hpr a) (hpr b)⟩ : (rdData1 h hj hG d hκ hd Z).Rg) = ⟨pr a, hpr a⟩ * ⟨pr b, hpr b⟩ from rfl,
          map_add, map_mul, map_mul, map_mul, Pi.add_apply, Pi.mul_apply, Pi.mul_apply, Pi.mul_apply]
        show _ = (rdData1 h hj hG d hκ hd Z).rd ⟨fr a, hfr a⟩ x / (rdData1 h hj hG d hκ hd Z).rd ⟨pr a, hpr a⟩ x + (rdData1 h hj hG d hκ hd Z).rd ⟨fr b, hfr b⟩ x / (rdData1 h hj hG d hκ hd Z).rd ⟨pr b, hpr b⟩ x
        rw [div_add_div _ _ (hpx a) (hpx b)]
        ring }
  have hPf : ∀ a, P a = (rdData1 h hj hG d hκ hd Z).rd ⟨fr a, hfr a⟩ x / (rdData1 h hj hG d hκ hd Z).rd ⟨pr a, hpr a⟩ x := fun a => rfl

  have hwi : ∃ i, (rdData1 h hj hG d hκ hd Z).rd ⟨d.w i Z, (rdData1 h hj hG d hκ hd Z).w_mem i⟩ x ≠ 0 := by
    letI : Field (CAt T.σ₀) := inferInstanceAs (Field ℂ)
    haveI : IsAlgClosed (CAt T.σ₀) := inferInstanceAs (IsAlgClosed ℂ)
    obtain ⟨i, hi⟩ := hB1 (CAt T.σ₀) ((T.U j T.σ₀).un (κ Z) ⟨x, hx⟩)
    refine ⟨i, ?_⟩
    have hm : valC hG (wtA uL) uL.n (W i).1 Z ∈ (rdData1 h hj hG d hκ hd Z).Rg := hRd.2.2.1 uL (W i) hev
    have e1 : (⟨d.w i Z, (rdData1 h hj hG d hκ hd Z).w_mem i⟩ : (rdData1 h hj hG d hκ hd Z).Rg) = ⟨_, hm⟩ := Subtype.ext (hwv i Z)
    rw [e1, hRd.2.2.2.2.1 uL (W i) hm x hx]
    show rdU (T.U j T.σ₀) (W i).1 (κ Z) x ≠ 0
    unfold rdU
    simp only [LinearMap.coe_mk, AddHom.coe_mk, dif_pos hx]
    exact hi
  obtain ⟨i0, hi0⟩ := hwi
  have hPT : P ∈ PT (Ω := Om Z) T.σ₀ := by
    show P.comp (algebraMap T.Q.c.F (Om Z)) = T.σ₀
    ext c
    let Wc : (recB h.toLawsCore).Cusp j uL :=
      (⟨c • (W i0).1, (cutR T.C j uL).smul_mem c (W i0).2⟩ : ↥(cutR T.C j uL))
    show P (algebraMap T.Q.c.F (Om Z) c) = T.σ₀ c
    have hq0m : valC hG (wtA uL) uL.n (W i0).1 Z ∈ (rdData1 h hj hG d hκ hd Z).Rg := hRd.2.2.1 uL (W i0) hev
    have hcm : valC hG (wtA uL) uL.n Wc.1 Z ∈ (rdData1 h hj hG d hκ hd Z).Rg := hRd.2.2.1 uL Wc hev
    have e1 : (⟨d.w i0 Z, (rdData1 h hj hG d hκ hd Z).w_mem i0⟩ : (rdData1 h hj hG d hκ hd Z).Rg) = ⟨_, hq0m⟩ := Subtype.ext (hwv i0 Z)
    have hq0x : (rdData1 h hj hG d hκ hd Z).rd ⟨_, hq0m⟩ x ≠ 0 := by rw [← e1]; exact hi0
    have hev0 : evC hG Z (W i0).1 ≠ 0 := fun h0 => hq0x (by
      rw [show (⟨valC hG (wtA uL) uL.n (W i0).1 Z, hq0m⟩ : (rdData1 h hj hG d hκ hd Z).Rg) = 0 from Subtype.ext (by
        show AddMonoidAlgebra.single _ (evC hG Z (W i0).1) = 0
        rw [h0, AddMonoidAlgebra.single_zero]), map_zero]; rfl)
    have hsm : evC hG Z (Wc : T.R j) =
        algebraMap T.Q.c.F (Om Z) c * evC hG Z (W i0).1 :=
      evalAt_smul (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) c (W i0).1 _
    have hA0 : valC hG (wtA uL) uL.n (W i0).1 Z ∈ AG Z (wtZ (wtA uL) uL.n) := valC_mem _ _ _ _ _
    have hGE0 : wtZ (wtA uL) uL.n ∈ (rdData1 h hj hG d hκ hd Z).WE := by show Even ((uL.n : ℕ) : ℤ); exact_mod_cast hev
    have hr : algebraMap T.Q.c.F (Om Z) c = ratio (Ω := Om Z) (valC hG (wtA uL) uL.n Wc.1 Z)
        (valC hG (wtA uL) uL.n (W i0).1 Z) := by
      show _ = ratio (Ω := Om Z) (AddMonoidAlgebra.single _ (evC hG Z (Wc : T.R j)))
        (AddMonoidAlgebra.single _ (evC hG Z (W i0).1))
      rw [hsm, ratio_single _ _ _ hev0, mul_div_cancel_right₀ _ hev0]
    have hq0ne : valC hG (wtA uL) uL.n (W i0).1 Z ≠ 0 := fun h0 => hq0x (by
      rw [show (⟨valC hG (wtA uL) uL.n (W i0).1 Z, hq0m⟩ : (rdData1 h hj hG d hκ hd Z).Rg) = 0 from Subtype.ext h0, map_zero]; rfl)
    rw [hPf, cons _ _ _ hcm hq0m (valC_mem _ _ _ _ _) hA0 hq0ne hGE0 hr,
      hRd.2.2.2.2.1 uL Wc hcm x hx, hRd.2.2.2.2.1 uL (W i0) hq0m x hx]
    show rdU (T.U j T.σ₀) (Wc : T.R j) (κ Z) x /
      rdU (T.U j T.σ₀) (W i0).1 (κ Z) x = T.σ₀ c
    have hne0 : rdU (T.U j T.σ₀) (W i0).1 (κ Z) x ≠ 0 := by
      have := hRd.2.2.2.2.1 uL (W i0) hq0m x hx
      rw [this] at hq0x
      exact hq0x
    rw [show (Wc : T.R j) = c • ((W i0 : (recB h.toLawsCore).Cusp j uL) : T.R j)
      from rfl, map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hne0, mul_one]
  refine ⟨hx, P, hPT, fun G hGE f hf g hg hfA hgA hg0 => ?_⟩
  have hg1 := hgood g hg hg0 G hGE hgA
  rw [hPf, cons (ratio (Ω := Om Z) f g) f g hf hg hfA hgA hg0 hGE rfl, div_mul_cancel₀ _ hg1]

theorem genDenseRg (h : LawsP T) {j : ℕ} (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z))
    {κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp} (hκ : KappaTie j hG κ) (hd : DTie h j hG d)
    (Z : Comp (T.Q.Xo j) T.Q.c)
    (hbir : ∀ a : Om Z, ∃ (G : WTZ D.host.E) (f p : AC Z), f ∈ (rdData1 h hj hG d hκ hd Z).Rg ∧ p ∈ (rdData1 h hj hG d hκ hd Z).Rg ∧
      f ∈ AG Z G ∧ p ∈ AG Z G ∧ p ≠ 0 ∧ p ∈ Algebra.adjoin T.Q.c.F (Set.range fun i => d.w i Z) ∧
      a = ratio (Ω := Om Z) f p) :
    GenDenseRgSt (rdData1 h hj hG d hκ hd Z) := by
  classical
  have hRd := tieRd1 h hj hG d hκ hd Z
  let Hs : Set (AC Z) := {g | ∃ (_ : g ∈ (rdData1 h hj hG d hκ hd Z).Rg), g ≠ 0 ∧ ∃ G ∈ (rdData1 h hj hG d hκ hd Z).WE, g ∈ AG Z G}
  have hHc : Hs.Countable := (countable_Rg h hj hG Z).mono fun g hg => hg.1
  let S0 : AC Z → Set (Frame ((T.U j T.σ₀).X (κ Z)).Ψ D.R.r) := fun g =>
    if hg : g ∈ (rdData1 h hj hG d hκ hd Z).Rg then closure {x | x ∈ ((T.U j T.σ₀).X (κ Z)).dom ∧ (rdData1 h hj hG d hκ hd Z).rd ⟨g, hg⟩ x = 0} else ∅
  have hS0 : ∀ g ∈ Hs, IsClosed (S0 g) ∧ interior (S0 g) = ∅ := by
    rintro g ⟨hg, hg0, G, hGE, hgA⟩
    simp only [S0, dif_pos hg]
    refine ⟨isClosed_closure, interior_closure_zero _ (hRd.1 G hGE g hg hgA).1 ?_⟩
    by_contra hno
    push Not at hno
    exact hg0 (hRd.2.1 G g hg hgA hno)
  have hcov : ((T.U j T.σ₀).X (κ Z)).dom \ genRg (rdData1 h hj hG d hκ hd Z) ⊆ ⋃ g ∈ Hs, S0 g := by
    rintro x ⟨hx, hxg⟩
    by_contra hno
    refine hxg (mem_genRg_of h hj hG d hκ hd Z hbir hx fun g hg hg0 G hGE hgA hz => hno ?_)
    refine Set.mem_biUnion (x := g) ⟨hg, hg0, G, hGE, hgA⟩ ?_
    simp only [S0, dif_pos hg]
    exact subset_closure ⟨hx, hz⟩
  rcases Hs.eq_empty_or_nonempty with he | hne
  · refine ⟨fun _ => ∅, fun _ => ⟨isClosed_empty, interior_empty⟩, ?_⟩
    intro x hx
    have := hcov hx
    rw [he] at this
    simp at this
  · obtain ⟨f, hf⟩ := hHc.exists_eq_range hne
    refine ⟨fun n => S0 (f n), fun n => hS0 _ (by rw [hf]; exact Set.mem_range_self n), ?_⟩
    intro x hx
    obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.1 (hcov hx)
    rw [hf] at hg
    obtain ⟨n, rfl⟩ := hg
    exact Set.mem_iUnion.2 ⟨n, hxg⟩

end Formalism.L2.Pj
