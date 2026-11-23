import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.JetGlue
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet

attribute [local instance] Over.cartesianMonoidalCategory

section BC

variable {S T : Type} [CommRing S] [CommRing T] (f : S →+* T)

def bcJ (κ : Type) (m : ℕ) : Jet S κ m →+* Jet T κ m :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (MvPolynomial.map f)) (fun P hP => by
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    have h1 : orig S κ ≤ (orig T κ).comap (MvPolynomial.map f) := by
      unfold orig
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap, map_X]
      exact Ideal.subset_span ⟨j, rfl⟩
    exact ((Ideal.pow_right_mono h1 _).trans (Ideal.le_comap_pow _ _)) hP)

theorem base_change_jet_variable {κ : Type} (m : ℕ) (j : κ) : bcJ f κ m (zz m j) = zz m j := by
  unfold zz
  show Ideal.Quotient.mk _ (MvPolynomial.map f (X j)) = _
  rw [MvPolynomial.map_X]

theorem bcJ_C {κ : Type} (m : ℕ) (s : S) :
    bcJ f κ m (algebraMap S (Jet S κ m) s) = algebraMap T (Jet T κ m) (f s) := by
  show Ideal.Quotient.mk _ (MvPolynomial.map f (C s)) = Ideal.Quotient.mk _ (C (f s))
  rw [MvPolynomial.map_C]

theorem bcJ_comp (κ : Type) (m : ℕ) :
    (bcJ f κ m).comp (algebraMap S (Jet S κ m)) = (algebraMap T (Jet T κ m)).comp f := RingHom.ext fun s => bcJ_C f (κ := κ) m s

theorem nat_ring {κ : Type} {m : ℕ} {B B' : Type} [CommRing B] [Algebra S B] [CommRing B'] [Algebra T B']
    (ψ : Jet S κ m →ₐ[S] B) (ψ' : Jet T κ m →ₐ[T] B') (bB : B →+* B')
    (hB : ∀ s, bB (algebraMap S B s) = algebraMap T B' (f s)) (h : ∀ j, ψ' (zz m j) = bB (ψ (zz m j))) :
    (ψ' : Jet T κ m →+* B').comp (bcJ f κ m) = bB.comp (ψ : Jet S κ m →+* B) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro s
    have e1 : (Ideal.Quotient.mk (orig S κ ^ (m + 1)) (C s)) = algebraMap S (Jet S κ m) s := rfl
    simp only [RingHom.comp_apply, AlgHom.coe_toRingHom, e1, bcJ_C, AlgHom.commutes, hB]
  · intro j
    have e2 : (Ideal.Quotient.mk (orig S κ ^ (m + 1)) (X j)) = zz m j := rfl
    simp only [RingHom.comp_apply, AlgHom.coe_toRingHom, e2, base_change_jet_variable, h]

variable {X : Scheme.{0}} (x0 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp S ⟶ X)

abbrev x0T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp T ⟶ X := Spec.map (CommRingCat.ofHom f) ≫ x0

def bcO {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra T A'] (bA : A →+* A')
    (hA : bA.comp (algebraMap S A) = (algebraMap T A').comp f) : overAt (x0T f x0) A' ⟶ overAt x0 A :=
  Over.homMk (Spec.map (CommRingCat.ofHom bA)) (by
    dsimp
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hA])

theorem bcO_left {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra T A'] (bA : A →+* A')
    (hA : bA.comp (algebraMap S A) = (algebraMap T A').comp f) :
    (bcO f x0 bA hA).left = Spec.map (CommRingCat.ofHom bA) := rfl

theorem nat_over {A A' B B' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra T A'] [CommRing B]
    [Algebra S B] [CommRing B'] [Algebra T B'] (bA : A →+* A') (hA : bA.comp (algebraMap S A) = (algebraMap T A').comp f)
    (bB : B →+* B') (hB : bB.comp (algebraMap S B) = (algebraMap T B').comp f)
    (ψ : A →ₐ[S] B) (ψ' : A' →ₐ[T] B') (e : (ψ' : A' →+* B').comp bA = bB.comp (ψ : A →+* B)) :
    homAt (x0T f x0) ψ' ≫ bcO f x0 bA hA = bcO f x0 bB hB ≫ homAt x0 ψ := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, bcO_left, homAt, Over.homMk_left, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]

end BC

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField

section Transfer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) (x0 : Sp S ⟶ Xo.X) {d : ℕ}

def xT (x : ∀ m, overAt x0 (Jet S (Fin 1 × Fin d) m) ⟶ Xo.univ.t.G) (m : ℕ) :
    overAt (x0T f x0) (Jet T (Fin 1 × Fin d) m) ⟶ Xo.univ.t.G :=
  bcO f x0 (bcJ f (Fin 1 × Fin d) m) (bcJ_comp f _ m) ≫ x m

private theorem jetSubstP_apply_mk {R : Type} [CommRing R] {κ κ' : Type} (m : ℕ)
    (φ : κ → MvPolynomial κ' R) (p : MvPolynomial κ R) :
    jetSubstP m φ (Ideal.Quotient.mk (orig R κ ^ (m + 1)) p) =
      Ideal.Quotient.mk _ (aeval (fun i => φ i - C (MvPolynomial.constantCoeff (φ i))) p) := by
  rfl

private theorem bcJ_mk_lemma_2 {S' T' : Type} [CommRing S'] [CommRing T'] (g : S' →+* T') (κ : Type) (m : ℕ)
    (p : MvPolynomial κ S') :
    bcJ g κ m (Ideal.Quotient.mk (orig S' κ ^ (m + 1)) p) = Ideal.Quotient.mk _ (MvPolynomial.map g p) := by
  rfl

private theorem jetCopy_mk_lemma_3 {R : Type} [CommRing R] (d' : ℕ) {n : ℕ} (m : ℕ) (i : Fin n)
    (p : MvPolynomial (Fin 1 × Fin d') R) :
    jetCopy d' m i (Ideal.Quotient.mk (orig R (Fin 1 × Fin d') ^ (m + 1)) p) =
      Ideal.Quotient.mk _ (aeval (fun q : Fin 1 × Fin d' => (X (i, q.2) : MvPolynomial (Fin n × Fin d') R)) p) := by
  rfl

theorem isExpHomR_bc {x : ∀ m, overAt x0 (Jet S (Fin 1 × Fin d) m) ⟶ Xo.univ.t.G} (hx : IsExpHomR x0 d x) :
    IsExpHomR (x0T f x0) d (xT f x0 x) := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨fun m => ?_, fun m => ?_⟩
  · have e := nat_ring f (ψ := (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m))
      (ψ' := (jetTrunc : Jet T (Fin 1 × Fin d) (m + 1) →ₐ[T] Jet T (Fin 1 × Fin d) m))
      (bB := bcJ f _ m) (fun s => bcJ_C f m s) (fun j => (base_change_jet_variable f m j).symm)
    have k := nat_over f x0 (bcJ f _ (m + 1)) (bcJ_comp f _ (m + 1)) (bcJ f _ m) (bcJ_comp f _ m) _ _ e
    unfold xT
    rw [← Category.assoc, k, Category.assoc, h1 m]
  · have eS := nat_ring f
      (ψ := (jetSubstP m fun p : Fin 1 × Fin d => X ((0 : Fin 2), p.2) + X ((1 : Fin 2), p.2) :
        Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin 2 × Fin d) m))
      (ψ' := (jetSubstP m fun p : Fin 1 × Fin d => X ((0 : Fin 2), p.2) + X ((1 : Fin 2), p.2) :
        Jet T (Fin 1 × Fin d) m →ₐ[T] Jet T (Fin 2 × Fin d) m))
      (bB := bcJ f _ m) (fun s => bcJ_C f m s) (fun j => by
        rw [show zz m j = Ideal.Quotient.mk (orig S (Fin 1 × Fin d) ^ (m + 1)) (X j) from rfl,
          show zz m j = Ideal.Quotient.mk (orig T (Fin 1 × Fin d) ^ (m + 1)) (X j) from rfl,
          jetSubstP_apply_mk, jetSubstP_apply_mk, bcJ_mk_lemma_2]
        simp)
    have eC : ∀ i : Fin 2, _ := fun i => nat_ring f
      (ψ := (jetCopy d m i : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin 2 × Fin d) m))
      (ψ' := (jetCopy d m i : Jet T (Fin 1 × Fin d) m →ₐ[T] Jet T (Fin 2 × Fin d) m))
      (bB := bcJ f _ m) (fun s => bcJ_C f m s) (fun j => by
        rw [show zz m j = Ideal.Quotient.mk (orig S (Fin 1 × Fin d) ^ (m + 1)) (X j) from rfl,
          show zz m j = Ideal.Quotient.mk (orig T (Fin 1 × Fin d) ^ (m + 1)) (X j) from rfl,
          jetCopy_mk_lemma_3, jetCopy_mk_lemma_3, bcJ_mk_lemma_2]
        simp)
    have kS := nat_over f x0 (bcJ f _ m) (bcJ_comp f _ m) (bcJ f _ m) (bcJ_comp f _ m) _ _ eS
    have k0 := nat_over f x0 (bcJ f _ m) (bcJ_comp f _ m) (bcJ f _ m) (bcJ_comp f _ m) _ _ (eC 0)
    have k1 := nat_over f x0 (bcJ f _ m) (bcJ_comp f _ m) (bcJ f _ m) (bcJ_comp f _ m) _ _ (eC 1)
    unfold xT
    simp only [← Category.assoc, kS, k0, k1]
    simp only [Category.assoc, h2 m]
    first
    | exact Hom.comp_mul _ _ _
    | exact MonObj.comp_mul _ _ _
    | exact CategoryTheory.Hom.comp_mul _ _ _
    | simp only [Hom.comp_mul]
    | simp only [MonObj.comp_mul]

theorem dual_comp : (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f).comp (algebraMap S (DualNumber S)) =
    (algebraMap T (DualNumber T)).comp f := RingHom.ext fun s => by
  ext <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem sameTan_bc {x x' : ∀ m, overAt x0 (Jet S (Fin 1 × Fin d) m) ⟶ Xo.univ.t.G} (ht : SameTanR x0 d x x') :
    SameTanR (x0T f x0) d (xT f x0 x) (xT f x0 x') := by
  intro j
  have e := nat_ring f
    (ψ := (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S))
    (ψ' := (jetTan ((0 : Fin 1), j) : Jet T (Fin 1 × Fin d) (0 + 1) →ₐ[T] DualNumber T))
    (bB := ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) (fun s => RingHom.congr_fun (dual_comp f) s) (fun q => by
      show aeval _ (X q) = ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f (aeval _ (X q))
      simp only [aeval_X]
      split_ifs <;> ext <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR])
  have k := nat_over f x0 (bcJ f _ 1) (bcJ_comp f _ 1) (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) (dual_comp f) _ _ e
  unfold xT
  simp only [← Category.assoc, k]
  simp only [Category.assoc, ht j]

end Transfer

theorem theta {S : Type} [CommRing S] (p : Ideal S) [p.IsPrime] (κ : Type) (m : ℕ) :
    ∃ θ : Jet (Localization.AtPrime p) κ m →+* ReciprocityTheory.ChartRestriction.G.TB.JetLoc S κ m p,
      θ.comp (bcJ (algebraMap S (Localization.AtPrime p)) κ m) =
        algebraMap (ReciprocityTheory.ChartRestriction.G.TB.JetRing S κ m) (ReciprocityTheory.ChartRestriction.G.TB.JetLoc S κ m p) := by
  classical
  have hu : ∀ y : p.primeCompl, IsUnit (((algebraMap (ReciprocityTheory.ChartRestriction.G.TB.JetRing S κ m)
      (ReciprocityTheory.ChartRestriction.G.TB.JetLoc S κ m p)).comp (algebraMap S (ReciprocityTheory.ChartRestriction.G.TB.JetRing S κ m))) y) :=
    fun y => IsLocalization.map_units (ReciprocityTheory.ChartRestriction.G.TB.JetLoc S κ m p)
      (⟨algebraMap S (ReciprocityTheory.ChartRestriction.G.TB.JetRing S κ m) y, by
        first
        | exact Algebra.mem_algebraMapSubmonoid_of_mem y
        | exact Submonoid.mem_map_of_mem _ y.2⟩ :
        Algebra.algebraMapSubmonoid (ReciprocityTheory.ChartRestriction.G.TB.JetRing S κ m) p.primeCompl)
  let g : Localization.AtPrime p →+* ReciprocityTheory.ChartRestriction.G.TB.JetLoc S κ m p :=
    IsLocalization.lift (M := p.primeCompl) hu
  let F : MvPolynomial κ (Localization.AtPrime p) →+* ReciprocityTheory.ChartRestriction.G.TB.JetLoc S κ m p :=
    MvPolynomial.eval₂Hom g fun j => algebraMap (ReciprocityTheory.ChartRestriction.G.TB.JetRing S κ m)
      (ReciprocityTheory.ChartRestriction.G.TB.JetLoc S κ m p)
      (Ideal.Quotient.mk (Ideal.span (Set.range (X : κ → MvPolynomial κ S)) ^ (m + 1)) (X j))
  have hF : ∀ a ∈ orig (Localization.AtPrime p) κ ^ (m + 1), F a = 0 := by
    intro a ha
    have h1 : F a ∈ Ideal.map F (orig (Localization.AtPrime p) κ ^ (m + 1)) := Ideal.mem_map_of_mem _ ha
    rw [map_orig_pow] at h1
    have h3 : Ideal.span (Set.range fun i => F (X i)) =
        Ideal.map (algebraMap (ReciprocityTheory.ChartRestriction.G.TB.JetRing S κ m) (ReciprocityTheory.ChartRestriction.G.TB.JetLoc S κ m p))
          (Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range (X : κ → MvPolynomial κ S)) ^ (m + 1)))
            (Ideal.span (Set.range (X : κ → MvPolynomial κ S)))) := by
      rw [Ideal.map_map, Ideal.map_span, ← Set.range_comp]
      congr 1
      congr 1
      funext i
      simp [F]
    rw [h3, ← Ideal.map_pow, ← Ideal.map_pow, Ideal.map_quotient_self, Ideal.map_bot] at h1
    exact (Submodule.mem_bot _).1 h1
  refine ⟨Ideal.Quotient.lift _ F hF, ?_⟩
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro s
    show F (MvPolynomial.map (algebraMap S (Localization.AtPrime p)) (C s)) = _
    rw [MvPolynomial.map_C]
    simp only [F, MvPolynomial.eval₂Hom_C]
    exact IsLocalization.lift_eq hu s
  · intro j
    show F (MvPolynomial.map (algebraMap S (Localization.AtPrime p)) (X j)) = _
    rw [MvPolynomial.map_X]
    simp only [F, MvPolynomial.eval₂Hom_X']
    rfl

theorem expUniqRaw : ExpUniqRawSt := by
  intro E _ _ _ H Dw l Xo S _ _ x0 d x x' hx hx' ht
  funext m
  apply Over.OverMorphism.ext
  refine ReciprocityTheory.ChartRestriction.G.TB.JGPf.jetGlue S (Fin 1 × Fin d) m Xo.univ.t.G.left (x m).left (x' m).left ?_
  intro p _
  obtain ⟨θ, hθ⟩ := theta p (Fin 1 × Fin d) m
  have hloc := ExpUniqBC.expUniqLoc E H Dw l Xo (Localization.AtPrime p)
    (x0T (algebraMap S (Localization.AtPrime p)) x0) d _ _ (isExpHomR_bc (algebraMap S (Localization.AtPrime p)) x0 hx)
    (isExpHomR_bc (algebraMap S (Localization.AtPrime p)) x0 hx') (sameTan_bc (algebraMap S (Localization.AtPrime p)) x0 ht)
  have hm := congrArg (fun g => (g m).left) hloc
  simp only [xT, Over.comp_left, bcO_left] at hm
  have key : Spec.map (CommRingCat.ofHom (algebraMap (ReciprocityTheory.ChartRestriction.G.TB.JetRing S (Fin 1 × Fin d) m)
      (ReciprocityTheory.ChartRestriction.G.TB.JetLoc S (Fin 1 × Fin d) m p))) =
      Spec.map (CommRingCat.ofHom θ) ≫
        Spec.map (CommRingCat.ofHom (bcJ (algebraMap S (Localization.AtPrime p)) (Fin 1 × Fin d) m)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) hθ.symm
  have e1 := (congrArg (fun t => t ≫ (x m).left) key).trans (Category.assoc _ _ _)
  have e2 := (congrArg (fun t => t ≫ (x' m).left) key).trans (Category.assoc _ _ _)
  exact e1.trans ((congrArg (fun t => Spec.map (CommRingCat.ofHom θ) ≫ t) hm).trans e2.symm)

theorem expUniq : ExpUniqSt := by
  intro E _ _ _ H Dw l Xo c S _ _ _ y d x x' hx hx' ht
  exact expUniqRaw E H Dw l Xo S y.x d x x' hx hx' ht

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
