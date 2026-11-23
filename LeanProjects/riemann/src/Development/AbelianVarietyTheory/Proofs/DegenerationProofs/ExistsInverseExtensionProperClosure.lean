import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteOfIsClosedOfFiniteInterClosedPoints

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.InvExt

theorem inv_left_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (ι[G']).left ≫ φ = φ ≫ (ι[G]).left := by
  have e := congrArg (fun z => z.left) (map_inv (pushHom h G') (𝟙 G'))
  have e₁ : (𝟙 G' : G' ⟶ G')⁻¹ = ι[G'] := by rw [Hom.inv_def, Category.id_comp]
  rw [e₁] at e
  refine e.trans ?_
  show (𝟙 G'.left ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem isDominant_gPt (p : ℕ) [Fact p.Prime] : IsDominant (gPt p) := by
  refine ⟨?_⟩
  exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (OO p).subtype).mpr (by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp Subtype.val_injective]; exact bot_le)

theorem exists_common {X : Scheme.{0}} {k k' : Type} [Field k] [Field k'] (u : Sp k ⟶ X)
    (u' : Sp k' ⟶ X) (x : Sp k) (x' : Sp k') (h : u x = u' x') :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (v : Sp K ⟶ Sp k) (v' : Sp K ⟶ Sp k'),
      v ≫ u = v' ≫ u' := by
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback x x' h
  let F := (pullback u u').residueField z
  let w : Sp (AlgebraicClosure F) ⟶ pullback u u' :=
    spMap (algebraMap F (AlgebraicClosure F)) ≫ (pullback u u').fromSpecResidueField z
  exact ⟨AlgebraicClosure F, inferInstance, inferInstance, w ≫ pullback.fst _ _,
    w ≫ pullback.snd _ _, by simp [pullback.condition]⟩

variable (C : Core)

theorem isOpenImmersion_a : IsOpenImmersion C.a := by
  have : IsOpenImmersion (C.a ≫ C.G.ι) := MorphismProperty.of_isPullback C.cart.flip inferInstance
  exact IsOpenImmersion.of_comp C.a C.G.ι

variable {C}

theorem generic_inv {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)
    (c : Sp (OO p) ⟶ τ.H.left) (hc : c ≫ τ.H.hom = spMap τ.j) (a₀ : Sp (PadicAlgCl p) ⟶ C.A.left)
    (ha : a₀ ≫ C.a = gPt p ≫ c ≫ τ.f) :
    gPt p ≫ c ≫ (ι[τ.H]).left ≫ τ.f = a₀ ≫ (ι[C.A]).left ≫ C.a := by
  have := isOpenImmersion_a C
  have hinj : Function.Injective ((OO p).subtype.comp τ.j) := Subtype.val_injective.comp τ.j_inj
  let k : FractionRing τ.V →+* PadicAlgCl p := IsFractionRing.lift hinj
  have hk : spMap k ≫ Out.jK τ.V = gPt p ≫ spMap τ.j := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    simp [k]
  let l : Sp (PadicAlgCl p) ⟶ pullback τ.H.hom (Out.jK τ.V) :=
    pullback.lift (gPt p ≫ c) (spMap k) (by rw [Category.assoc, hc, hk])
  have hl : l ≫ pullback.fst _ _ = gPt p ≫ c := pullback.lift_fst _ _ _
  have h1 : l ≫ τ.φ = a₀ := by
    rw [← cancel_mono C.a, Category.assoc, τ.φ_f, reassoc_of% hl, ha]
  have h2 := inv_left_comp τ.φ_cart
  have h3 := inv_left_comp (isGrpPullback_pullback τ.H (Out.jK τ.V))
  have h4 : (ι[(Over.pullback (Out.jK τ.V)).obj τ.H]).left ≫ τ.φ ≫ C.a =
      τ.φ ≫ (ι[C.A]).left ≫ C.a := by
    rw [← Category.assoc, ← Category.assoc]; exact congrArg (· ≫ C.a) h2
  have h5 : (ι[(Over.pullback (Out.jK τ.V)).obj τ.H]).left ≫ pullback.fst τ.H.hom (Out.jK τ.V) ≫ τ.f =
      pullback.fst τ.H.hom (Out.jK τ.V) ≫ (ι[τ.H]).left ≫ τ.f := by
    rw [← Category.assoc, ← Category.assoc]; exact congrArg (· ≫ τ.f) h3
  rw [← h1, Category.assoc, ← h4, τ.φ_f]
  erw [h5]
  rw [reassoc_of% hl]

theorem range_residue {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)
    {K : Type} [Field K] (v : Sp K ⟶ Sp (kb p)) :
    Set.range (v ≫ rPt p ≫ spMap τ.j) = {IsLocalRing.closedPoint τ.V} := by
  have := τ.j_loc
  have h : ∀ x : Sp K, (v ≫ rPt p ≫ spMap τ.j) x = IsLocalRing.closedPoint τ.V := by
    intro x
    have hx : v x = IsLocalRing.closedPoint (kb p) := Subsingleton.elim (α := PrimeSpectrum (kb p)) _ _
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hx]
    exact (congrArg (spMap τ.j) (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))).trans
      (IsLocalRing.comap_closedPoint τ.j)
  ext x
  exact ⟨fun ⟨z, hz⟩ => hz ▸ h z, fun hx => ⟨IsLocalRing.closedPoint K, (h _).trans hx.symm⟩⟩

theorem rPt_apply (p : ℕ) [Fact p.Prime] (x : Sp (kb p)) : rPt p x = cPt p := by
  have hx : x = IsLocalRing.closedPoint (kb p) := Subsingleton.elim (α := PrimeSpectrum (kb p)) _ _
  rw [hx]
  exact IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p))

theorem exists_common_residue {X : Scheme.{0}} {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (α : Sp (OO p) ⟶ X) (β : Sp (OO q) ⟶ X) (h : α (cPt p) = β (cPt q)) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (v : Sp K ⟶ Sp (kb p)) (v' : Sp K ⟶ Sp (kb q)),
      v ≫ rPt p ≫ α = v' ≫ rPt q ≫ β := by
  obtain ⟨x⟩ : Nonempty (Sp (kb p)) := inferInstance
  obtain ⟨x'⟩ : Nonempty (Sp (kb q)) := inferInstance
  refine exists_common _ _ x x' ?_
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, rPt_apply, rPt_apply, h]

theorem natCast_kb (p : ℕ) [hp : Fact p.Prime] : (p : kb p) = 0 := by
  rw [← map_natCast (IsLocalRing.residue (OO p)), IsLocalRing.residue_eq_zero_iff,
    Valuation.mem_maximalIdeal_iff]
  change Valued.v (p : PadicAlgCl p) < 1
  rw [PadicAlgCl.valuation_p, one_div]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

theorem prime_eq {X : Scheme.{0}} {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (α : Sp (OO p) ⟶ X) (β : Sp (OO q) ⟶ X) (h : α (cPt p) = β (cPt q)) : p = q := by
  obtain ⟨K, _, _, v, v', -⟩ := exists_common_residue α β h
  have h1 : (p : K) = 0 := by
    rw [← map_natCast (Spec.preimage v).hom]
    exact (congrArg _ (natCast_kb p)).trans (map_zero _)
  have h2 : (q : K) = 0 := by
    rw [← map_natCast (Spec.preimage v').hom]
    exact (congrArg _ (natCast_kb q)).trans (map_zero _)
  have := (CharP.charP_iff_prime_eq_zero hp.out).mpr h1
  have := (CharP.charP_iff_prime_eq_zero hq.out).mpr h2
  exact CharP.eq K ‹CharP K p› ‹CharP K q›

theorem special_inv (hF : C.FibLaw) {p : ℕ} [Fact p.Prime] {y y' : Sp (OO p) ⟶ C.Z}
    (τ : C.Test y) (τ' : C.Test y')
    (c : Sp (OO p) ⟶ τ.H.left) (hc : c ≫ τ.H.hom = spMap τ.j)
    (c' : Sp (OO p) ⟶ τ'.H.left) (hc' : c' ≫ τ'.H.hom = spMap τ'.j)
    (h : (c ≫ τ.f) (cPt p) = (c' ≫ τ'.f) (cPt p)) :
    (c ≫ (ι[τ.H]).left ≫ τ.f) (cPt p) = (c' ≫ (ι[τ'.H]).left ≫ τ'.f) (cPt p) := by
  obtain ⟨K, _, _, v, v', hv⟩ := exists_common_residue _ _ h
  let d : Over.mk (v ≫ rPt p ≫ spMap τ.j) ⟶ τ.H := Over.homMk (v ≫ rPt p ≫ c) (by simp [hc])
  let d' : Over.mk (v' ≫ rPt p ≫ spMap τ'.j) ⟶ τ'.H := Over.homMk (v' ≫ rPt p ≫ c') (by simp [hc'])
  have hd : d.left ≫ τ.f = d'.left ≫ τ'.f := by simpa [d, d'] using hv
  have hr : (v ≫ rPt p ≫ spMap τ.j) ≫ τ.y₀ = (v' ≫ rPt p ≫ spMap τ'.j) ≫ τ'.y₀ := by
    have := congrArg (· ≫ C.GG.hom) hv
    simp only [Category.assoc, τ.f_over, τ'.f_over, reassoc_of% hc, reassoc_of% hc'] at this
    simpa using this
  have e := (hF p y y' τ τ' K _ _ (range_residue τ v) (range_residue τ' v') hr d d d' d' hd hd).2
  have e' : v ≫ rPt p ≫ c ≫ (ι[τ.H]).left ≫ τ.f = v' ≫ rPt p ≫ c' ≫ (ι[τ'.H]).left ≫ τ'.f := by
    simpa [Hom.inv_def, d, d'] using e
  obtain ⟨x⟩ : Nonempty (Sp K) := inferInstance
  have := congrArg (fun g => g x) e'
  simp only [Scheme.Hom.comp_apply, rPt_apply] at this
  simpa only [Scheme.Hom.comp_apply] using this

theorem exists_test (hT : C.HasTests) {p : ℕ} [Fact p.Prime] (α : Sp (OO p) ⟶ C.G.toScheme)
    (a₀ : Sp (PadicAlgCl p) ⟶ C.A.left) (b : Sp (OO p) ⟶ C.P.left) (ha : a₀ ≫ C.a = gPt p ≫ α)
    (hb : gPt p ≫ b = a₀ ≫ (ι[C.A]).left ≫ C.a ≫ C.G.ι) (hb' : b ≫ C.P.hom = α ≫ C.GG.hom) :
    ∃ (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y) (c : Sp (OO p) ⟶ τ.H.left),
      c ≫ τ.H.hom = spMap τ.j ∧ c ≫ τ.f = α ∧ b = (c ≫ (ι[τ.H]).left ≫ τ.f) ≫ C.G.ι := by
  have hw : C.a ≫ C.GG.hom = C.A.hom ≫ C.U.ι := by simpa using C.cart.w
  have hcl : C.Cl (α ≫ C.GG.hom) := by
    rintro _ ⟨x, rfl⟩
    rw [← reassoc_of% ha, hw, ← Category.assoc, Scheme.Hom.comp_apply]
    exact Subtype.property _
  obtain ⟨τ⟩ := hT p _ hcl
  obtain ⟨c, hc, hcf⟩ := τ.lift α rfl
  refine ⟨_, τ, c, hc, hcf, ?_⟩
  have := C.proper
  have := isDominant_gPt p
  refine ext_of_isDominant_of_isSeparated C.P.hom ?_ (gPt p) ?_
  · have h1 : τ.f ≫ C.G.ι ≫ C.P.hom = τ.H.hom ≫ τ.y₀ := τ.f_over
    simp only [Category.assoc]
    rw [hb', h1, Over.w_assoc, reassoc_of% hc, τ.fac]
  · rw [hb, ← Category.assoc (gPt p), generic_inv τ c hc a₀ (by rw [hcf, ha])]
    simp only [Category.assoc]

end GlobalTheory.InvExt

namespace GlobalTheory

open InvExt in

theorem exists_inv_extension : ∀ C : Core, C.HasTests → SmoothOfRelativeDimension C.g C.GG.hom → C.TestCart → C.FibLaw → ∃ i : C.GG ⟶ C.GG, C.a ≫ i.left = (ι[C.A]).left ≫ C.a := by
  intro C hT hS _ hF
  have := isOpenImmersion_a C
  have := C.flat
  have := C.lft
  have := C.qc
  have := C.proper
  have : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  have : IsLocallyNoetherian C.P.left := LocallyOfFiniteType.isLocallyNoetherian (C.P.hom ≫ C.π)
  have : QuasiCompact C.GG.hom := inferInstanceAs (QuasiCompact (C.G.ι ≫ C.P.hom))
  obtain ⟨z, hz⟩ := C.ne
  have : Nonempty C.G.toScheme := ⟨C.e z⟩
  have hI : IsIntegral C.G.toScheme := isIntegral_of_isOpenImmersion C.G.ι
  have hw : C.a ≫ C.GG.hom = C.A.hom ≫ C.U.ι := by simpa using C.cart.w
  let e := C.a.isoOpensRange
  have he : e.inv ≫ C.a = C.a.opensRange.ι := C.a.isoOpensRange_inv_comp
  have he' : e.hom ≫ C.a.opensRange.ι = C.a := C.a.isoOpensRange_hom_ι
  obtain ⟨Φ, ⟨h1, h2⟩, -⟩ := @existsUnique_extension_of_finite_specializations C.G.toScheme hI
    (C.GG.hom ≫ C.π) inferInstance inferInstance inferInstance
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth C.GG.hom C.normal)
    C.Z C.P.left C.GG.hom C.P.hom _ C.G C.a.opensRange
    (e.inv ≫ (ι[C.A]).left ≫ C.a ≫ C.G.ι) ⟨_, eSec C.A (⟨z, hz⟩ : C.U), rfl⟩
    (by
      have h : C.a ≫ C.G.ι ≫ C.P.hom = C.A.hom ≫ C.U.ι := hw
      simp only [Category.assoc]
      rw [h, Over.w_assoc, ← hw, reassoc_of% he])
    (by
      intro σ _
      let F : Set C.P.left := {w | ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ C.Z)
        (τ : C.Test y) (c : Sp (OO p) ⟶ τ.H.left), c ≫ τ.H.hom = spMap τ.j ∧
          (c ≫ τ.f) (cPt p) = σ ∧ w = C.G.ι ((c ≫ (ι[τ.H]).left ≫ τ.f) (cPt p))}
      refine ⟨F, Set.Subsingleton.finite ?_, ?_, ?_⟩
      · rintro _ ⟨p, _, y, τ, c, hc, hσ, rfl⟩ _ ⟨q, _, y', τ', c', hc', hσ', rfl⟩
        obtain rfl := prime_eq _ _ (hσ.trans hσ'.symm)
        rw [special_inv hF τ τ' c hc c' hc' (hσ.trans hσ'.symm)]
      · rintro _ ⟨p, _, y, τ, c, hc, hσ, rfl⟩
        exact Subtype.property _
      · intro p _ α a₀ b hσ ha hb hb'
        obtain ⟨y, τ, c, hc, hcf, rfl⟩ := exists_test hT α (a₀ ≫ e.inv) b
          (by rw [Category.assoc, he, ha]) (by rw [hb, Category.assoc]) hb'
        exact ⟨p, _, y, τ, c, hc, hcf ▸ hσ, Scheme.Hom.comp_apply _ _ _⟩)
  refine ⟨Over.homMk Φ h2, ?_⟩
  rw [← cancel_mono C.G.ι]
  change (C.a ≫ Φ) ≫ C.G.ι = _
  rw [Category.assoc, Category.assoc]
  conv_lhs => rw [← he', Category.assoc, h1, e.hom_inv_id_assoc]

end GlobalTheory
