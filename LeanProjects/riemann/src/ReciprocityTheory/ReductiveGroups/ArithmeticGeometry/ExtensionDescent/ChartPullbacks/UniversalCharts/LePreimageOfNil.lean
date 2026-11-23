import Mathlib

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

variable {R₀ : Type} [CommRing R₀]

abbrev sp (P : Type) [CommRing P] [Algebra R₀ P] : Over (Spec (CommRingCat.of R₀)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R₀ P)))

def spMap {P P' : Type} [CommRing P] [Algebra R₀ P] [CommRing P'] [Algebra R₀ P'] (g : P →ₐ[R₀] P') :
    sp (R₀ := R₀) P' ⟶ sp P :=
  Over.homMk (Spec.map (CommRingCat.ofHom g.toRingHom)) (by
    simp only [sp, Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact g.comp_algebraMap)

theorem spMap_left {P P' : Type} [CommRing P] [Algebra R₀ P] [CommRing P'] [Algebra R₀ P'] (g : P →ₐ[R₀] P') :
    (spMap g).left = Spec.map (CommRingCat.ofHom g.toRingHom) := rfl

theorem spMap_comp {P P' P'' : Type} [CommRing P] [Algebra R₀ P] [CommRing P'] [Algebra R₀ P']
    [CommRing P''] [Algebra R₀ P''] (g : P →ₐ[R₀] P') (g' : P' →ₐ[R₀] P'') :
    spMap g' ≫ spMap g = spMap (R₀ := R₀) (g'.comp g) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, spMap_left, spMap_left, spMap_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

section Chart

variable (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G]

structure Chart where
  U : G.left.Opens
  hU : IsAffineOpen U
  he : ⊤ ≤ (η[G]).left ⁻¹ᵁ U

variable {G}

def alg0 (C : Chart G) : R₀ →+* Γ(G.left, C.U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv ≫ G.hom.appLE ⊤ C.U le_top).hom

instance (C : Chart G) : Algebra R₀ Γ(G.left, C.U) := (alg0 C).toAlgebra

theorem fromSpec_over (C : Chart G) :
    C.hU.fromSpec ≫ G.hom = Spec.map (CommRingCat.ofHom (alg0 C)) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec G.hom (isAffineOpen_top _) C.hU le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

def pt (C : Chart G) {P : Type} [CommRing P] [Algebra R₀ P] (h : Γ(G.left, C.U) →ₐ[R₀] P) : sp P ⟶ G :=
  Over.homMk (Spec.map (CommRingCat.ofHom h.toRingHom) ≫ C.hU.fromSpec) (by
    simp only [sp, Over.mk_hom]
    rw [Category.assoc, fromSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact h.comp_algebraMap)

theorem pt_left (C : Chart G) {P : Type} [CommRing P] [Algebra R₀ P] (h : Γ(G.left, C.U) →ₐ[R₀] P) :
    (pt C h).left = Spec.map (CommRingCat.ofHom h.toRingHom) ≫ C.hU.fromSpec := rfl

theorem spMap_pt (C : Chart G) {P P' : Type} [CommRing P] [Algebra R₀ P] [CommRing P'] [Algebra R₀ P']
    (g : P →ₐ[R₀] P') (h : Γ(G.left, C.U) →ₐ[R₀] P) : spMap g ≫ pt C h = pt C (g.comp h) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, spMap_left, pt_left, pt_left, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem pt_injective (C : Chart G) {P : Type} [CommRing P] [Algebra R₀ P] {h h' : Γ(G.left, C.U) →ₐ[R₀] P}
    (H : pt C h = pt C h') : h = h' := by
  have h1 : (pt C h).left = (pt C h').left := by rw [H]
  rw [pt_left, pt_left] at h1
  have h2 := (cancel_mono C.hU.fromSpec).mp h1
  have h3 := Spec.map_injective h2
  apply AlgHom.ext
  intro a
  exact congrArg (fun f => f.hom a) h3

theorem chart_eq (C : Chart G) {P : Type} [CommRing P] (x : Spec (CommRingCat.of P) ⟶ G.left)
    (hx : ⊤ ≤ x ⁻¹ᵁ C.U) :
    Spec.map (x.appLE C.U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of P)).hom) ≫ C.hU.fromSpec = x := by
  rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec x C.hU (isAffineOpen_top _) hx,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.id_comp]

theorem exists_pt (C : Chart G) {P : Type} [CommRing P] [Algebra R₀ P] (x : sp P ⟶ G)
    (hx : ⊤ ≤ x.left ⁻¹ᵁ C.U) : ∃ h : Γ(G.left, C.U) →ₐ[R₀] P, x = pt C h := by
  have hx' : Spec.map (x.left.appLE C.U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of P)).hom) ≫ C.hU.fromSpec =
      x.left := chart_eq C x.left hx
  have hc : (x.left.appLE C.U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of P)).hom).hom.comp (alg0 C) =
      algebraMap R₀ P := by
    have e : Spec.map (CommRingCat.ofHom ((x.left.appLE C.U ⊤ hx ≫
        (Scheme.ΓSpecIso (CommRingCat.of P)).hom).hom.comp (alg0 C))) =
        Spec.map (CommRingCat.ofHom (algebraMap R₀ P)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, ← fromSpec_over, ← Category.assoc, hx']
      exact Over.w x
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  refine ⟨{ (x.left.appLE C.U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of P)).hom).hom with
    commutes' := fun r => RingHom.congr_fun hc r }, ?_⟩
  apply Over.OverMorphism.ext
  rw [pt_left]
  exact hx'.symm

theorem le_preimage_of_nil (C : Chart G) {P P₀ : Type} [CommRing P] [Algebra R₀ P] [CommRing P₀]
    [Algebra R₀ P₀] (q : P →ₐ[R₀] P₀) (hq : Function.Surjective q)
    (hn : ∀ a ∈ RingHom.ker q, IsNilpotent a) (x : sp P ⟶ G) (h₀ : Γ(G.left, C.U) →ₐ[R₀] P₀)
    (hx : spMap q ≫ x = pt C h₀) : ⊤ ≤ x.left ⁻¹ᵁ C.U := by
  intro p _
  have hker : RingHom.ker q.toRingHom ≤ PrimeSpectrum.asIdeal p := by
    intro a ha
    obtain ⟨k, hk⟩ := hn a ha
    exact (PrimeSpectrum.isPrime p).mem_of_pow_mem k (by rw [hk]; exact Ideal.zero_mem _)
  haveI := PrimeSpectrum.isPrime p
  let p₀ : PrimeSpectrum P₀ :=
    ⟨(PrimeSpectrum.asIdeal p).map q.toRingHom, Ideal.map_isPrime_of_surjective hq hker⟩
  have hp₀ : (Spec.map (CommRingCat.ofHom q.toRingHom)).base p₀ = p := by
    apply PrimeSpectrum.ext
    show Ideal.comap q.toRingHom (Ideal.map q.toRingHom (PrimeSpectrum.asIdeal p)) = PrimeSpectrum.asIdeal p
    exact (Ideal.comap_map_of_surjective' q.toRingHom hq _).trans (sup_eq_left.mpr hker)
  have e : Spec.map (CommRingCat.ofHom q.toRingHom) ≫ x.left =
      Spec.map (CommRingCat.ofHom h₀.toRingHom) ≫ C.hU.fromSpec := by
    rw [← spMap_left, ← Over.comp_left, hx, pt_left]
  have hmem : C.hU.fromSpec.base ((Spec.map (CommRingCat.ofHom h₀.toRingHom)).base p₀) ∈ C.U := by
    rw [← SetLike.mem_coe, ← C.hU.range_fromSpec]
    exact Set.mem_range_self _
  have h3 : (Spec.map (CommRingCat.ofHom q.toRingHom) ≫ x.left).base p₀ =
      (Spec.map (CommRingCat.ofHom h₀.toRingHom) ≫ C.hU.fromSpec).base p₀ := by
    rw [e]
  have h2 : x.left.base ((Spec.map (CommRingCat.ofHom q.toRingHom)).base p₀) ∈ C.U := by
    have h4 : x.left.base ((Spec.map (CommRingCat.ofHom q.toRingHom)).base p₀) =
        C.hU.fromSpec.base ((Spec.map (CommRingCat.ofHom h₀.toRingHom)).base p₀) := h3
    rw [h4]
    exact hmem
  rw [← hp₀]
  exact h2

end Chart

section ChartB

theorem exists_chart [IsLocalRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] :
    Nonempty (Chart G) := by
  obtain ⟨U, hU, hmem, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := (η[G]).left.base (IsLocalRing.closedPoint R₀)) (U := ⊤) (by trivial)
  refine ⟨⟨U, hU, ?_⟩⟩
  intro y _
  exact (IsLocalRing.specializes_closedPoint (R := R₀) y).mem_open ((η[G]).left ⁻¹ᵁ U).isOpen hmem

variable {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G]

def epsHom (C : Chart G) : Γ(G.left, C.U) ⟶ CommRingCat.of R₀ :=
  Scheme.Hom.appLE (η[G]).left C.U ⊤ C.he ≫ (Scheme.ΓSpecIso (CommRingCat.of R₀)).hom

theorem epsHom_spec (C : Chart G) : Spec.map (epsHom C) ≫ C.hU.fromSpec = (η[G]).left := chart_eq C (η[G]).left C.he

theorem epsHom_comp (C : Chart G) : (epsHom C).hom.comp (alg0 C) = RingHom.id R₀ := by
  have e : Spec.map (CommRingCat.ofHom ((epsHom C).hom.comp (alg0 C))) =
      Spec.map (CommRingCat.ofHom (RingHom.id R₀)) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, ← fromSpec_over, ← Category.assoc,
      epsHom_spec, CommRingCat.ofHom_id, Spec.map_id]
    first
    | exact Over.w (η[G])
    | simpa using Over.w (η[G])
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

def eps (C : Chart G) : Γ(G.left, C.U) →ₐ[R₀] R₀ :=
  { (epsHom C).hom with commutes' := fun r => RingHom.congr_fun (epsHom_comp C) r }

theorem eps_apply (C : Chart G) (a : Γ(G.left, C.U)) : eps C a = (epsHom C).hom a := rfl

theorem pt_eps (C : Chart G) (P : Type) [CommRing P] [Algebra R₀ P] :
    pt C ((Algebra.ofId R₀ P).comp (eps C)) = (1 : sp P ⟶ G) := by
  apply Over.OverMorphism.ext
  rw [pt_left]
  have e : CommRingCat.ofHom ((Algebra.ofId R₀ P).comp (eps C)).toRingHom =
      epsHom C ≫ CommRingCat.ofHom (algebraMap R₀ P) := rfl
  rw [e, Spec.map_comp, Category.assoc, epsHom_spec]
  first
  | rfl
  | (rw [MonObj.Hom.one_def]; rfl)
  | simp [MonObj.Hom.one_def]

end ChartB

section Smooth

variable {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G] (C : Chart G)

theorem chart_smooth [Smooth G.hom] : Algebra.Smooth R₀ Γ(G.left, C.U) := by
  have h1 : Smooth (C.hU.fromSpec ≫ G.hom) := inferInstance
  rw [fromSpec_over] at h1
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp h1

end Smooth

end ReciprocityTheory.ChartRestriction.G.Chart
