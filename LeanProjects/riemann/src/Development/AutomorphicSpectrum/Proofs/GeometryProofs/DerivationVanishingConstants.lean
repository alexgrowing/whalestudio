import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OneLeftSpMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushRProdPtsResP
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExpChart

open GlobalTheory.HolHom

section Frame

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g : ℕ}

def epsIso (R : Type) [CommRing R] : epsR R ⟶ epsAt (𝟙 (Sp R)) := Over.homMk (𝟙 _) (by simp [spMap])

def epsIsoInv (R : Type) [CommRing R] : epsAt (𝟙 (Sp R)) ⟶ epsR R := Over.homMk (𝟙 _) (by simp [spMap])

def frv (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (e : Fin g → R) : epsR R ⟶ G := epsIso R ≫ M.pt e

theorem frv_left (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (e : Fin g → R) : (frv M e).left = (M.pt e).left := by
  simp [frv, epsIso]

def frvHom (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) : Multiplicative (Fin g → R) →* (epsR R ⟶ G) :=
  MonoidHom.mk' (fun e => frv M e.toAdd) fun a b => by
    show epsIso R ≫ M.pt (a.toAdd + b.toAdd) = _
    rw [M.add]
    exact MonObj.comp_mul _ _ _

theorem frv_prod (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (c : Fin g → R) :
    (List.ofFn fun i => frv M (c i • Pi.single i 1)).prod = frv M c := by
  have h := map_list_prod (frvHom M) (List.ofFn fun i => Multiplicative.ofAdd (c i • (Pi.single i 1 : Fin g → R)))
  rw [List.map_ofFn, List.prod_ofFn, ← ofAdd_sum] at h
  have e : ∑ i, c i • (Pi.single i 1 : Fin g → R) = c := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [e] at h
  exact h.symm

theorem one_over_left : (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left = η[G].left := by
  rw [Hom.one_def]
  have : (toUnit (Over.mk (𝟙 (Sp R))) : Over.mk (𝟙 (Sp R)) ⟶ 𝟙_ (Over (Sp R))) = 𝟙 _ := toUnit_unique _ _
  rw [this]
  simp

theorem isLieBasis_frv (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) :
    IsLieBasis (fun a => frv M (Pi.single a 1)) := by
  have comb : ∀ (c : Fin g → R) (w : epsR R ⟶ G),
      IsLieComb c (fun a => frv M (Pi.single a 1)) w ↔ w = frv M c := by
    intro c w
    have hs : ∀ i, (frv M (c i • Pi.single i 1)).left = spMap (epsScaleR (c i)) ≫ (frv M (Pi.single i 1)).left := by
      intro i
      rw [frv_left, frv_left, M.smul]
      rfl
    constructor
    · rintro ⟨u, hu, rfl⟩
      have : u = fun i => frv M (c i • Pi.single i 1) := by
        funext i
        apply Over.OverMorphism.ext
        rw [hu i, hs i]
      rw [this, frv_prod]
    · rintro rfl
      exact ⟨_, hs, (frv_prod M c).symm⟩
  refine ⟨fun i => ?_, fun w hw => ?_⟩
  · show spMap _ ≫ (frv M _).left = _
    rw [frv_left, ← one_over_left]
    exact M.tan _
  · obtain ⟨e, he⟩ := M.onto (epsIsoInv R ≫ w) (by
      show Spec.map _ ≫ (epsIsoInv R ≫ w).left = _
      rw [one_over_left]
      have hw' : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ w.left = η[G].left := hw
      simpa [epsIsoInv] using hw')
    have hwe : w = frv M e := by
      apply Over.OverMorphism.ext
      rw [frv_left, he]
      simp [epsIsoInv]
    refine ⟨e, (comb e w).2 hwe, fun c hc => ?_⟩
    have h2 := (comb c w).1 hc
    apply M.inj
    apply Over.OverMorphism.ext
    rw [← frv_left, ← frv_left, ← h2, hwe]

end Frame

section Jets

variable {g : ℕ}

abbrev J1 (g : ℕ) : Type := Chart.JetR ℂ (Fin g) 1

abbrev dl (c : Fin g → ℂ) : J1 g →+* DualNumber ℂ := (Chart.dualLift (R := ℂ) c : J1 g →ₐ[ℂ] DualNumber ℂ)

theorem fst_dualLift (c : Fin g → ℂ) (a : J1 g) : (Chart.dualLift c a).fst = Chart.jetAug ℂ (Fin g) 1 a :=
  AlgHom.congr_fun (Chart.fstD_comp_dualLift c) a

theorem snd_dualLift (c : Fin g → ℂ) (a : J1 g) :
    (Chart.dualLift c a).snd = ∑ j, c j * (Chart.dualLift (Pi.single j 1) a).snd := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  induction p using MvPolynomial.induction_on with
  | C r =>
    have e : ∀ c' : Fin g → ℂ, Chart.dualLift c' (Ideal.Quotient.mk _ (MvPolynomial.C r)) = algebraMap ℂ (DualNumber ℂ) r :=
      fun c' => (Chart.dualLift c').commutes r
    simp [e, TrivSqZeroExt.algebraMap_eq_inl']
  | add p q hp hq =>
    simp only [map_add, TrivSqZeroExt.snd_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p j hp =>
    have e : ∀ c' : Fin g → ℂ, (Chart.dualLift c' (Ideal.Quotient.mk _ (p * MvPolynomial.X j))).snd =
        Chart.jetAug ℂ (Fin g) 1 (Ideal.Quotient.mk _ p) * c' j := by
      intro c'
      rw [map_mul, map_mul]
      have z := Chart.dualLift_zR c' j
      rw [show (Ideal.Quotient.mk _ (MvPolynomial.X j) : J1 g) = Chart.zR 1 j from rfl, z, TrivSqZeroExt.snd_mul,
        fst_dualLift]
      simp
    simp only [e]
    simp [Pi.single_apply, mul_comm]

theorem aug_sq {a : J1 g} (h : Chart.jetAug ℂ (Fin g) 1 a = 0) : a ^ 2 = 0 := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have h1 := Chart.sub_const_mem_span_X (R := ℂ) p
  have h0 : MvPolynomial.aeval (fun _ : Fin g => (0 : ℂ)) p = 0 := h
  rw [h0, map_zero, sub_zero] at h1
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow h1 2)

theorem le_preimage_jet {X : Scheme.{0}} {ξ : Sp (J1 g) ⟶ X} {x : Sp ℂ ⟶ X}
    (h : spMap (Chart.jetAug ℂ (Fin g) 1 : J1 g →+* ℂ) ≫ ξ = x) {U : X.Opens} (hx : ⊤ ≤ x ⁻¹ᵁ U) : ⊤ ≤ ξ ⁻¹ᵁ U := by
  subst h
  intro p _
  let ρ : J1 g →+* ℂ := (Chart.jetAug ℂ (Fin g) 1 : J1 g →+* ℂ)
  have hsurj : Function.Surjective ρ := fun r => ⟨algebraMap ℂ _ r, (Chart.jetAug ℂ (Fin g) 1).commutes r⟩
  have hmax : (RingHom.ker ρ).IsMaximal := RingHom.ker_isMaximal_of_surjective ρ hsurj
  have hle : RingHom.ker ρ ≤ p.asIdeal := fun a ha =>
    p.isPrime.mem_of_pow_mem 2 (by rw [aug_sq ha]; exact zero_mem _)
  have hp : RingHom.ker ρ = p.asIdeal := hmax.eq_of_le p.isPrime.ne_top hle
  let q : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  have e : spMap ρ q = p := by
    apply PrimeSpectrum.ext
    show Ideal.comap ρ ⊥ = p.asIdeal
    rw [← hp]
    rfl
  have := hx (x := q) trivial
  show ξ p ∈ U
  rw [← e]
  exact this

variable {X : Scheme.{0}} {x : Sp ℂ ⟶ X} {V : X.Opens} {ξ : Sp (J1 g) ⟶ X}

theorem snd_val_jet (h : spMap (Chart.jetAug ℂ (Fin g) 1 : J1 g →+* ℂ) ≫ ξ = x) (hx : ⊤ ≤ x ⁻¹ᵁ V) (c : Fin g → ℂ)
    (f : Γ(X, V)) : TrivSqZeroExt.snd (valR (spMap (dl c) ≫ ξ) V f) =
      ∑ a, c a * TrivSqZeroExt.snd (valR (spMap (dl (Pi.single a 1)) ≫ ξ) V f) := by
  have hξ := le_preimage_jet h hx
  simp only [valR_spMap _ ξ V hξ]
  exact snd_dualLift c _

theorem jet_inj (h : spMap (Chart.jetAug ℂ (Fin g) 1 : J1 g →+* ℂ) ≫ ξ = x) (hV : IsAffineOpen V) (hx : ⊤ ≤ x ⁻¹ᵁ V)
    {c c' : Fin g → ℂ}
    (e : ∀ f : Γ(X, V), ∑ a, c a * TrivSqZeroExt.snd (valR (spMap (dl (Pi.single a 1)) ≫ ξ) V f) =
      ∑ a, c' a * TrivSqZeroExt.snd (valR (spMap (dl (Pi.single a 1)) ≫ ξ) V f)) :
    spMap (dl c) ≫ ξ = spMap (dl c') ≫ ξ := by
  have hξ := le_preimage_jet h hx
  have hin : ∀ b : Fin g → ℂ, ⊤ ≤ (spMap (dl b) ≫ ξ) ⁻¹ᵁ V :=
    fun b p _ => hξ (x := spMap _ p) trivial
  refine point_ext hV (hin c) (hin c') fun f => TrivSqZeroExt.ext ?_ ?_
  · simp only [valR_spMap _ ξ V hξ]
    exact (fst_dualLift c _).trans (fst_dualLift c' _).symm
  · rw [snd_val_jet h hx, snd_val_jet h hx, e f]

theorem exists_dual_pt (hV : IsAffineOpen V) (hx : ⊤ ≤ x ⁻¹ᵁ V) (D : Γ(X, V) →+ ℂ) (h1 : D 1 = 0)
    (hD : ∀ f f', D (f * f') = valAt' x V f * D f' + valAt' x V f' * D f) :
    ∃ y : Sp (DualNumber ℂ) ⟶ X, ⊤ ≤ y ⁻¹ᵁ V ∧ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ y = x ∧
      ∀ f, valR y V f = TrivSqZeroExt.inl (valAt' x V f) + TrivSqZeroExt.inr (D f) := by
  have hv : ∀ f, valAt' x V f = GlobalTheory.TangentOrigin.evalPt x V hx f := GlobalTheory.TangentOrigin.valAt'_eq_evalPt x V hx
  let χ : Γ(X, V) →+* DualNumber ℂ :=
    { toFun := fun f => TrivSqZeroExt.inl (valAt' x V f) + TrivSqZeroExt.inr (D f)
      map_one' := by
        ext <;> simp [hv, h1]
      map_mul' := fun a b => by
        ext <;> simp [hD, hv, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul]
        ring
      map_zero' := by
        ext <;> simp [hv]
      map_add' := fun a b => by
        ext <;> simp [hv] }
  obtain ⟨y, hy, he⟩ := GlobalTheory.TangentOrigin.exists_evalPt_eq hV χ
  have hval : ∀ f, valR y V f = TrivSqZeroExt.inl (valAt' x V f) + TrivSqZeroExt.inr (D f) := fun f =>
    (valR_eq y V hy f).trans (RingHom.congr_fun he f)
  refine ⟨y, hy, ?_, hval⟩
  have hin : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ y) ⁻¹ᵁ V := fun p _ => hy (x := spMap _ p) trivial
  refine point_ext hV hin hx fun f => ?_
  rw [valR_spMap _ y V hy, hval]
  simp [valAt'_eq_valR]

end Jets

section Main

open scoped CategoryTheory.Obj

theorem eta_pull {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] (φ : R →+* ℂ) :
    (η[(Over.pullback (spMap φ)).obj G]).left ≫ pullback.fst G.hom (spMap φ) =
      (1 : Over.mk (spMap φ) ⟶ G).left := by
  have h1 := congrArg (fun q => Over.Hom.left q) (map_one (pushHom (isGrpPullback_pullback G (spMap φ)) (𝟙_ _)))
  change (1 : 𝟙_ _ ⟶ (Over.pullback (spMap φ)).obj G).left ≫ pullback.fst G.hom (spMap φ) = _ at h1
  rw [Chart.one_left', Chart.one_left'] at h1
  rw [Chart.one_left']
  simpa using h1

theorem lie_der_basis : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (g : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (φ : R →+* ℂ), Smooth G.hom → ∀ (V : G.left.Opens), IsAffineOpen V → ⊤ ≤ (1 : Over.mk (spMap φ) ⟶ G).left ⁻¹ᵁ V →
  ∀ D : Γ(G.left, V) →+ ℂ, (∀ r, D (GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.cst G.hom V r) = 0) →
    (∀ f f', D (f * f') = valAt' (1 : Over.mk (spMap φ) ⟶ G).left V f * D f' + valAt' (1 : Over.mk (spMap φ) ⟶ G).left V f' * D f) →
    ∃! c : Fin g → ℂ, ∀ f, D f = ∑ a, c a * TrivSqZeroExt.snd (valR (spMap (dualMap φ) ≫ (M.pt (Pi.single a 1)).left) V f) := by
  intro R _ G _ g M φ hs V hV h1 D hc hD
  have : Smooth G.hom := hs
  let G' := (Over.pullback (spMap φ)).obj G
  let F : G'.left ⟶ G.left := pullback.fst G.hom (spMap φ)
  have hG : IsGrpPullback G' G (spMap φ) F := isGrpPullback_pullback G (spMap φ)
  have hS : Smooth G'.hom := show Smooth (pullback.snd G.hom _) from inferInstance
  let u : Fin g → (epsR R ⟶ G) := fun a => frv M (Pi.single a 1)
  have hu : IsLieBasis u := isLieBasis_frv M
  have hw : ∀ a, (spMap (Chart.dualMapR φ) ≫ (u a).left) ≫ G.hom =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap φ := fun a => by
    rw [frv_left]
    exact (tan_over M φ _).trans (by simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
  let u' : Fin g → (epsR ℂ ⟶ G') := fun a => Over.homMk (pullback.lift _ _ (hw a)) (pullback.lift_snd _ _ _)
  have hu' : IsLieBasis u' := Chart.frameLieBC G hu φ hG fun i => pullback.lift_fst _ _ _
  obtain ⟨x, hx, hxv⟩ := Chart.chart_of_basis hu'
  let ξ : Sp (J1 g) ⟶ G.left := (x 1).left ≫ F
  have hη : (η[G']).left ≫ F = (1 : Over.mk (spMap φ) ⟶ G).left := eta_pull G φ
  have hleft : ∀ c : Fin g → ℂ, (Chart.spMap (Chart.dualLift c) ≫ x 1).left ≫ F = spMap (dl c) ≫ ξ := by
    intro c
    rw [Over.comp_left, Chart.spMap_left, Category.assoc]
    rfl
  have hξ : spMap (Chart.jetAug ℂ (Fin g) 1 : J1 g →+* ℂ) ≫ ξ = (1 : Over.mk (spMap φ) ⟶ G).left := by
    have h := congrArg (fun q => q.left) (Chart.spMap_jetAug_alt hx 1)
    simp only [Over.comp_left, Chart.spMap_left, Chart.one_left'] at h
    rw [← hη, ← Category.assoc, show spMap (Chart.jetAug ℂ (Fin g) 1 : J1 g →+* ℂ) ≫ (x 1).left = _ from h]
    simp
  have ht : ∀ a, spMap (dualMap φ) ≫ (M.pt (Pi.single a 1)).left = spMap (dl (Pi.single a 1)) ≫ ξ := by
    intro a
    rw [← hleft, ← hxv a, ← frv_left]
    exact (pullback.lift_fst _ _ (hw a)).symm
  simp only [ht]
  obtain ⟨y, hy, hyf, hyv⟩ := exists_dual_pt hV h1 D (by simpa using hc 1) hD
  have hyo : y ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap φ := by
    have e := GlobalTheory.TangentOrigin.eq_spMap_of_evalPt (y ≫ G.hom) ((algebraMap ℂ (DualNumber ℂ)).comp φ) (fun a => by
      rw [← GlobalTheory.TangentOrigin.evalPt_constFn G.hom y V hy a]
      have h := hyv (cst G.hom V a)
      rw [valR_eq y V hy, val_cst V _ h1 a, hc a] at h
      refine h.trans ?_
      simp [TrivSqZeroExt.algebraMap_eq_inl'])
    rw [e]
    simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let w : epsR ℂ ⟶ G' := Over.homMk (pullback.lift y _ hyo) (pullback.lift_snd _ _ _)
  have hwt : Chart.IsTan w := by
    apply (Chart.isTan_iff w).2
    show spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ w.left = (η[G']).left
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc]
      refine ((congrArg _ (pullback.lift_fst _ _ hyo)).trans hyf).trans hη.symm
    · rw [Category.assoc]
      refine (congrArg _ (pullback.lift_snd _ _ hyo)).trans ?_
      have e := Over.w (η[G'])
      refine Eq.trans ?_ e.symm
      simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨c, hcw, -⟩ := Chart.exists_coord hx w hwt
  have hyc : y = spMap (dl c) ≫ ξ := by
    rw [← hleft, ← hcw]
    exact (pullback.lift_fst _ _ hyo).symm
  refine ⟨c, fun f => ?_, fun c' hc' => ?_⟩
  · rw [← snd_val_jet hξ h1, ← hyc, hyv]
    simp
  · have e1 := jet_inj hξ hV h1 (c := c) (c' := c') fun f => by
      rw [← hc' f, ← snd_val_jet hξ h1, ← hyc, hyv]
      simp
    have e2 : Chart.spMap (Chart.dualLift c) ≫ x 1 = Chart.spMap (Chart.dualLift c') ≫ x 1 := by
      refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
      exact (hleft c).trans (e1.trans (hleft c').symm)
    exact ((Chart.exists_coord hx _ (Chart.isTan_dualLift hx c)).unique rfl e2).symm

end Main

end GlobalTheory.CompanionTheory.Ar.Flat.ExpChart
