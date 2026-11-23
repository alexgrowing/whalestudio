import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtSmul

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchC

open GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

theorem germ_closedPoint {Y : Scheme.{0}} {R : CommRingCat.{0}} [IsLocalRing R] (f : Spec R ⟶ Y) (U : Y.Opens)
    (hU : f (IsLocalRing.closedPoint R) ∈ U) :
    Y.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo f =
      f.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem f hU).ge ≫ (Scheme.ΓSpecIso R).hom := by
  rw [Scheme.germ_stalkClosedPointTo]
  simp [Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]

theorem point_of_ringHom {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {F : Type} [Field F]
    (g : Γ(X, U) →+* F) :
    ∃ h : centre (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec : Sp F ⟶ X) ∈ U, ∀ t : Γ(X, U),
      (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec : Sp F ⟶ X)).hom
        (X.presheaf.germ U _ h t) = g t := by
  have h0 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have hc : centre (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec : Sp F ⟶ X) ∈ U :=
    h0 (Set.mem_univ (Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint F)))
  refine ⟨hc, fun t => ?_⟩
  have h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec : Sp F ⟶ X) ⁻¹ᵁ U :=
    fun z _ => h0 (Set.mem_univ (Spec.map (CommRingCat.ofHom g) z))
  have h1 : hU.fromSpec.appLE U ⊤ h0 = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact Category.comp_id _
  have h2 : (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec : Sp F ⟶ X).appLE U ⊤ h' =
      hU.fromSpec.appLE U ⊤ h0 ≫ (Spec.map (CommRingCat.ofHom g)).appTop :=
    (Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom g)) hU.fromSpec U ⊤ ⊤ h0 le_rfl).symm
  have h3 : X.presheaf.germ U _ hc ≫ Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec : Sp F ⟶ X) =
      (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec : Sp F ⟶ X).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (.of F)).hom :=
    germ_closedPoint (R := .of F) _ U hc
  have h4 : X.presheaf.germ U _ hc ≫ Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec : Sp F ⟶ X) =
      CommRingCat.ofHom g := by
    rw [h3, h2, h1, Category.assoc, Scheme.ΓSpecIso_naturality]
    exact Iso.inv_hom_id_assoc (Scheme.ΓSpecIso Γ(X, U)) _
  exact congrArg (fun q => q.hom t) h4

theorem germ_fraction {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {p : X} (hp : p ∈ U)
    (s : X.presheaf.stalk p) : ∃ t₁ t₂ : Γ(X, U), IsUnit (X.presheaf.germ U p hp t₂) ∧
      s * X.presheaf.germ U p hp t₂ = X.presheaf.germ U p hp t₁ := by
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨p, hp⟩ : U)
  haveI := hU.isLocalization_stalk (⟨p, hp⟩ : U)
  obtain ⟨⟨t₁, t₂⟩, h⟩ := IsLocalization.surj (hU.primeIdealOf (⟨p, hp⟩ : U)).asIdeal.primeCompl s
  exact ⟨t₁, t₂, IsLocalization.map_units _ t₂, h⟩

section Values

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem genMap_germ (U : X.Opens) {p : X} (h : genPt ξ ⤳ p) (hp : p ∈ U) (t : Γ(X, U)) :
    genMap ξ ⟨p, h⟩ (X.presheaf.germ U p hp t) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) (h.mem_open U.2 hp) t) := by
  have e := TopCat.Presheaf.germ_stalkSpecializes X.presheaf (U := U) (y := p) (x := genPt ξ) hp h
  have e2 : (X.presheaf.stalkSpecializes h).hom (X.presheaf.germ U p hp t) = X.presheaf.germ U (genPt ξ) (h.mem_open U.2 hp) t :=
    ConcreteCategory.congr_hom e t
  exact congrArg (fun u => (Scheme.stalkClosedPointTo ξ).hom u) e2

variable {F : Type} [Field F] {z : Sp F ⟶ X}

theorem val_of_fractions {U : X.Opens} (hU : IsAffineOpen U) (hz : centre z ∈ U) (hgen : genPt ξ ⤳ centre z)
    (g : Γ(X, U) →+* F) (hg : ∀ t, (Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U _ hz t) = g t)
    {a : Ω} {b : F} (ha : a ∈ regAt ξ ⟨centre z, hgen⟩)
    (hb : ∀ t₁ t₂ : Γ(X, U), a * genMap ξ ⟨centre z, hgen⟩ (X.presheaf.germ U _ hz t₂) =
      genMap ξ ⟨centre z, hgen⟩ (X.presheaf.germ U _ hz t₁) → b * g t₂ = g t₁) : ValAt ξ z a b := by
  obtain ⟨s, hs⟩ := ha
  obtain ⟨t₁, t₂, hu, hst⟩ := germ_fraction hU hz s
  refine ⟨hgen, s, hs, ?_⟩
  have e2 := congrArg (genMap ξ ⟨centre z, hgen⟩) hst
  rw [map_mul, hs] at e2
  have key : ∀ St : X.presheaf.stalk (centre z) →+* F, (∀ t, St (X.presheaf.germ U _ hz t) = g t) → St s = b := by
    intro St hSt
    have e1 : St s * g t₂ = g t₁ := by
      have := congrArg St hst
      rwa [map_mul, hSt, hSt] at this
    have hne : g t₂ ≠ 0 := by
      have := hu.map St
      rw [hSt] at this
      exact this.ne_zero
    exact mul_right_cancel₀ hne (e1.trans (hb t₁ t₂ e2).symm)
  exact key _ hg

theorem val_int (hz : genPt ξ ⤳ centre z) (n : ℤ) : ValAt ξ z (n : Ω) (n : F) :=
  ⟨hz, (n : X.presheaf.stalk (centre z)), map_intCast _ n, map_intCast _ n⟩

theorem val_prod (hz : genPt ξ ⤳ centre z) {τ : Type} (s : Finset τ) (a : τ → Ω) (r : τ → F)
    (h : ∀ i ∈ s, ValAt ξ z (a i) (r i)) : ValAt ξ z (∏ i ∈ s, a i) (∏ i ∈ s, r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using val_one hz
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact val_mul (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem val_aeval (hz : genPt ξ ⤳ centre z) {κ : Type} (a : κ → Ω) (r : κ → F)
    (h : ∀ i, ValAt ξ z (a i) (r i)) (P : MvPolynomial κ ℤ) :
    ValAt ξ z (MvPolynomial.aeval a P) (MvPolynomial.aeval r P) := by
  induction P using MvPolynomial.induction_on with
  | C n => simpa using val_int hz n
  | add p q hp hq => simpa [map_add] using val_add hp hq
  | mul_X p i hp => simpa using val_mul hp (h i)

end Values

theorem ringHom_of_relations {Ω : Type} [Field Ω] {κ : Type} (r : κ → Ω) (ρ : κ → ℂ)
    (h : ∀ P : MvPolynomial κ ℤ, MvPolynomial.aeval r P = 0 → MvPolynomial.aeval ρ P = 0) :
    ∃ φ : Algebra.adjoin ℤ (Set.range r) →+* ℂ, ∀ j (hj : r j ∈ Algebra.adjoin ℤ (Set.range r)),
      φ ⟨r j, hj⟩ = ρ j := by
  have hm : ∀ P : MvPolynomial κ ℤ, MvPolynomial.aeval r P ∈ Algebra.adjoin ℤ (Set.range r) := by
    intro P
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact ⟨P, rfl⟩
  let f : MvPolynomial κ ℤ →+* Algebra.adjoin ℤ (Set.range r) :=
    (MvPolynomial.aeval r : MvPolynomial κ ℤ →ₐ[ℤ] Ω).toRingHom.codRestrict _ hm
  have hf : Function.Surjective f := by
    rintro ⟨a, ha⟩
    rw [Algebra.adjoin_range_eq_range_aeval] at ha
    obtain ⟨P, rfl⟩ := ha
    exact ⟨P, Subtype.ext rfl⟩
  let g : MvPolynomial κ ℤ →+* ℂ := (MvPolynomial.aeval ρ : MvPolynomial κ ℤ →ₐ[ℤ] ℂ).toRingHom
  have hk : RingHom.ker f ≤ RingHom.ker g := by
    intro P hP
    refine h P ?_
    exact congrArg Subtype.val (show f P = 0 from hP)
  refine ⟨f.liftOfRightInverse _ (Function.rightInverse_surjInv hf) ⟨g, hk⟩, fun j hj => ?_⟩
  have e : f (MvPolynomial.X j) = ⟨r j, hj⟩ := Subtype.ext (MvPolynomial.aeval_X r j)
  rw [← e, RingHom.liftOfRightInverse_comp_apply]
  exact MvPolynomial.aeval_X ρ j

section Coords

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω}

def segreRatio (c c' : (k : K) → J k) (v : (Σ k, J k) → ℂ) : ℂ := ∏ k, v ⟨k, c' k⟩ / v ⟨k, c k⟩

theorem val_segre {z : Sp ℂ ⟶ X} {v : (Σ k, J k) → ℂ} (hz : genPt ξ ⤳ centre z) (hv : CoordsAt ξ y z v)
    (c : (k : K) → J k) (hc : ∀ k, v ⟨k, c k⟩ ≠ 0) (c' : (k : K) → J k) :
    ValAt ξ z ((∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) (segreRatio c c' v) := by
  rw [← Finset.prod_div_distrib]
  refine val_prod hz _ _ _ fun k _ => ?_
  obtain ⟨-, h2⟩ := hv.2 k (c k) (isUnit_iff_ne_zero.2 (hc k))
  obtain ⟨r, hr, hr'⟩ := h2 (c' k)
  have : v ⟨k, c' k⟩ / v ⟨k, c k⟩ = r := by
    rw [hr', mul_div_cancel_right₀ _ (hc k)]
  rw [this]
  exact hr

theorem relation_limit (hall : ∀ q : X, genPt ξ ⤳ q) (hξ : IsCptGen ξ) (c : (k : K) → J k)
    {w : (Σ k, J k) → ℂ} (hw : w ∈ closure {w' : (Σ k, J k) → ℂ | ∃ z : Sp ℂ ⟶ X, CoordsAt ξ y z w'})
    (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (P : MvPolynomial ((k : K) → J k) ℤ)
    (hP : MvPolynomial.aeval (fun c' : (k : K) → J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) P = 0) :
    MvPolynomial.aeval (fun c' => segreRatio c c' w) P = 0 := by
  by_contra hne
  have hρ : ∀ c', ContinuousAt (fun v : (Σ k, J k) → ℂ => segreRatio c c' v) w := fun c' =>
    tendsto_finset_prod _ fun k _ =>
      ContinuousAt.div (continuous_apply _).continuousAt (continuous_apply _).continuousAt (hc k)
  have hcont : ContinuousAt (fun v : (Σ k, J k) → ℂ => MvPolynomial.aeval (fun c' => segreRatio c c' v) P) w := by
    have e : (fun v : (Σ k, J k) → ℂ => MvPolynomial.aeval (fun c' => segreRatio c c' v) P) =
        fun v => MvPolynomial.eval (fun c' => segreRatio c c' v) (MvPolynomial.map (algebraMap ℤ ℂ) P) := by
      funext v
      rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]
    rw [e]
    exact ContinuousAt.comp (f := fun v : (Σ k, J k) → ℂ => fun c' => segreRatio c c' v)
      (g := fun u => MvPolynomial.eval u (MvPolynomial.map (algebraMap ℤ ℂ) P))
      (MvPolynomial.continuous_eval _).continuousAt (continuousAt_pi.2 hρ)
  have h1 := hcont.eventually_ne hne
  have h2 : ∀ᶠ v : (Σ k, J k) → ℂ in 𝓝 w, ∀ k, v ⟨k, c k⟩ ≠ 0 :=
    eventually_all.2 fun k => (continuous_apply _).continuousAt.eventually_ne (hc k)
  obtain ⟨v, ⟨hv1, hv2⟩, z, hz⟩ := mem_closure_iff_nhds.1 hw _ (inter_mem h1 h2)
  have hv := val_aeval (hall (centre z)) _ _ (val_segre (hall (centre z)) hz c hv2) P
  rw [hP] at hv
  exact hv1 (val_unique hξ hv (val_zero (hall (centre z))))

theorem coords_of_values (hξ : IsCptGen ξ) {z : Sp ℂ ⟶ X} {w : (Σ k, J k) → ℂ} (c : (k : K) → J k)
    (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (hy : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hv : ∀ c' : (k : K) → J k, ValAt ξ z ((∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) (segreRatio c c' w)) :
    CoordsAt ξ y z w := by
  classical
  have V : ∀ k i, ValAt ξ z (y ⟨k, i⟩ / y ⟨k, c k⟩) (w ⟨k, i⟩ / w ⟨k, c k⟩) := by
    intro k i
    have h := hv (Function.update c k i)
    rw [← Finset.prod_div_distrib] at h
    unfold segreRatio at h
    have e1 : ∏ k', y ⟨k', Function.update c k i k'⟩ / y ⟨k', c k'⟩ = y ⟨k, i⟩ / y ⟨k, c k⟩ := by
      rw [Finset.prod_eq_single k]
      · simp
      · intro b _ hb
        rw [Function.update_of_ne hb, div_self (hy b)]
      · simp
    have e2 : ∏ k', w ⟨k', Function.update c k i k'⟩ / w ⟨k', c k'⟩ = w ⟨k, i⟩ / w ⟨k, c k⟩ := by
      rw [Finset.prod_eq_single k]
      · simp
      · intro b _ hb
        rw [Function.update_of_ne hb, div_self (hc b)]
      · simp
    rwa [e1, e2] at h
  refine ⟨fun k => ⟨c k, isUnit_iff_ne_zero.2 (hc k)⟩, fun k c₁ hu => ?_⟩
  have h1 : w ⟨k, c₁⟩ ≠ 0 := hu.ne_zero
  have hq : w ⟨k, c₁⟩ / w ⟨k, c k⟩ ≠ 0 := div_ne_zero h1 (hc k)
  have hy1 : y ⟨k, c₁⟩ ≠ 0 := by
    have h := val_ne_zero hξ (r := Units.mk0 _ hq) (V k c₁)
    exact (div_ne_zero_iff.1 h).1
  have hk := hy k
  have hck := hc k
  refine ⟨hy1, fun i => ⟨w ⟨k, i⟩ / w ⟨k, c₁⟩, ?_, by field_simp⟩⟩
  have h := val_mul (V k i) (val_inv₀ hq (V k c₁))
  convert h using 1 <;> field_simp

end Coords

theorem closed_coords (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (hall : ∀ q : X, genPt ξ ⤳ q)
    (tie : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    (w : (Σ k, J k) → ℂ) (hw : w ∈ closure {w' : (Σ k, J k) → ℂ | ∃ z : Sp ℂ ⟶ X, CoordsAt ξ y z w'})
    (hne : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) : ∃ z : Sp ℂ ⟶ X, CoordsAt ξ y z w := by
  choose c hc using hne
  have hξ := tie.gen

  have h2 : ∀ᶠ v : (Σ k, J k) → ℂ in 𝓝 w, ∀ k, v ⟨k, c k⟩ ≠ 0 :=
    eventually_all.2 fun k => (continuous_apply _).continuousAt.eventually_ne (hc k)
  obtain ⟨v, hv, z₀, hz₀⟩ := mem_closure_iff_nhds.1 hw _ h2
  have hch₀ := in_chart (hall (centre z₀)) hz₀ hv
  have hx : (∏ k, y ⟨k, c k⟩) ≠ 0 := hch₀.1
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hx) k (Finset.mem_univ k)
  obtain ⟨U, hU, hmem⟩ := tie.affine c hx
  have hp₀ : centre z₀ ∈ U := (hmem _).2 ⟨hall _, hch₀⟩
  set r : ((k : K) → J k) → Ω := fun c' => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩ with hr

  obtain ⟨φ, hφ⟩ := ringHom_of_relations r (fun c' => segreRatio c c' w)
    (fun P hP => relation_limit hall hξ c hw hc P hP)

  let e : Γ(X, U) →+* Ω := (genMap ξ ⟨centre z₀, hall _⟩).comp (X.presheaf.germ U _ hp₀).hom
  have he : ∀ {p : X} (hp : p ∈ U) (t : Γ(X, U)), genMap ξ ⟨p, hall p⟩ (X.presheaf.germ U p hp t) = e t := by
    intro p hp t
    show _ = genMap ξ ⟨centre z₀, hall _⟩ (X.presheaf.germ U _ hp₀ t)
    rw [genMap_germ U (hall p) hp t, genMap_germ U (hall _) hp₀ t]
  have hA : ∀ t, e t ∈ Algebra.adjoin ℤ (Set.range r) := fun t =>
    (tie.ring c hx (e t)).2 fun p hp => ⟨X.presheaf.germ U p.1 ((hmem p.1).2 ⟨p.2, hp⟩) t, he _ t⟩
  let e' : Γ(X, U) →+* Algebra.adjoin ℤ (Set.range r) := e.codRestrict _ hA
  let g : Γ(X, U) →+* ℂ := φ.comp e'
  obtain ⟨hcz, hgerm⟩ := point_of_ringHom hU g
  set z : Sp ℂ ⟶ X := Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec with hz
  obtain ⟨hgz, hchz⟩ := (hmem _).1 hcz

  have hval : ∀ a (ha : a ∈ Algebra.adjoin ℤ (Set.range r)), ValAt ξ z a (φ ⟨a, ha⟩) := by
    intro a ha
    refine val_of_fractions hU hcz hgz g hgerm ((tie.ring c hx a).1 ha _ hchz) fun t₁ t₂ h => ?_
    rw [he hcz, he hcz] at h
    have : (⟨a, ha⟩ : Algebra.adjoin ℤ (Set.range r)) * e' t₂ = e' t₁ := Subtype.ext h
    have := congrArg φ this
    rwa [map_mul] at this
  refine ⟨z, coords_of_values hξ c hc hy fun c' => ?_⟩
  have hj : r c' ∈ Algebra.adjoin ℤ (Set.range r) := Algebra.subset_adjoin ⟨c', rfl⟩
  have := hval _ hj
  rwa [hφ c' hj] at this

theorem closed_coords' : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    ∀ w : (Σ k, J k) → ℂ, w ∈ closure {w' : (Σ k, J k) → ℂ | ∃ z : Sp ℂ ⟶ X, CoordsAt ξ y z w'} →
      (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → ∃ z : Sp ℂ ⟶ X, CoordsAt ξ y z w :=
  fun X Ω _ ξ K _ J _ y hall tie w hw hne => closed_coords X Ω ξ K J y hall tie w hw hne

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchC
