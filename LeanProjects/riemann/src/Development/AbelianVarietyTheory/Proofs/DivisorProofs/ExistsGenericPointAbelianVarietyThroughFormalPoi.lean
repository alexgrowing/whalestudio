import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOpSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceOfSmoothOfGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValRConstHom
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifGenPoint

theorem valR_constFn {A B : Type} [CommRing A] [CommRing B] {X : Scheme.{0}} (p : X ⟶ Sp B) (x : Sp A ⟶ X)
    (χ : B →+* A) (hx : x ≫ p = spMap χ) (a : B) : valR x ⊤ (constFn p ⊤ a) = χ a := by
  have h : ⊤ ≤ x ⁻¹ᵁ (⊤ : X.Opens) := fun _ _ => trivial
  unfold constFn
  refine (GlobalTheory.ZH.CrdMove.valR_appLE x p ⊤ ⊤ _ h _).trans ?_
  rw [hx]
  have h' : ⊤ ≤ (spMap χ) ⁻¹ᵁ (⊤ : (Sp B).Opens) := fun _ _ => trivial
  rw [GlobalTheory.ZH.CrdCalc.valR_eq _ _ h']
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom χ)
  have := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom a)) n
  refine Eq.trans ?_ (this.trans (congrArg χ ((Scheme.ΓSpecIso (CommRingCat.of B)).inv_hom_id_apply a)))
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

end GlobalTheory.UnifGenPoint

open GlobalTheory.UnifGenPoint in

theorem GlobalTheory.UnifGenPoint.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∃ (ψ : FractionRing R →+* FractionRing Ω) (ξ : Sp (FractionRing Ω) ⟶ P.A.A.left), (∀ r, ψ (algebraMap R (FractionRing R) r) = algebraMap Ω (FractionRing Ω) (φ r)) ∧ ξ ≫ P.A.A.hom = spMap ψ ∧ ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = spMap (algebraMap Ω (FractionRing Ω)) ≫ x' ∧ ∀ O (f : Γ(P.A.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0 := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam _ _ _ n v' D Ω _ _ _ φ x' δ dd' _ hx _ _ _ hinj g _ δL _

  have hφ : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun r hr => ?_
    have h1 : valR x' ⊤ (constFn t.G.hom ⊤ r) = 0 := (valR_constFn t.G.hom x' φ hx r).trans hr
    have h2 := hinj ⊤ (constFn t.G.hom ⊤ r) (fun _ _ => trivial) h1
    have h3 := valR_constFn t.G.hom (eSec t.G) (RingHom.id R) (by
      rw [eSec, Over.w]; simp [spMap]) r
    rw [h2, GlobalTheory.ZH.CrdCalc.valR_eq (eSec t.G) ⊤ (fun _ _ => trivial), map_zero] at h3
    exact h3.symm

  set L := FractionRing Ω
  have hinjL : Function.Injective ((algebraMap Ω L).comp φ) :=
    (IsFractionRing.injective Ω L).comp hφ
  let ψ : FractionRing R →+* L := IsFractionRing.lift (K := FractionRing R) hinjL
  have hψ : ∀ r, ψ (algebraMap R (FractionRing R) r) = algebraMap Ω L (φ r) := fun r => by
    simp [ψ, IsFractionRing.lift_algebraMap]
  let u : Sp L ⟶ t.G.left := spMap (algebraMap Ω L) ≫ x'
  have hu : u ≫ t.G.hom = spMap ψ ≫ jK R := by
    simp only [u, Category.assoc, hx, spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun r => (hψ r).symm
  let ξ₀ : Sp L ⟶ pullback t.G.hom (jK R) := pullback.lift u (spMap ψ) hu
  let ξ : Sp L ⟶ P.A.A.left := ξ₀ ≫ P.U.gen.hom.left
  have n₁ : P.U.gen.hom.left ≫ P.U.gen.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, P.U.gen.hom_inv_id, Over.id_left]
  have hξ1 : ξ ≫ P.A.A.hom = spMap ψ := by
    simp only [ξ, Category.assoc, Over.w]
    exact pullback.lift_snd _ _ _
  have hξ2 : ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = u := by
    simp only [ξ, Category.assoc]
    rw [← Category.assoc P.U.gen.hom.left, n₁, Category.id_comp]
    exact pullback.lift_fst _ _ _
  refine ⟨ψ, ξ, hψ, hξ1, hξ2, ?_⟩

  haveI : Smooth t.G.hom := t.semi.smooth
  haveI : GeometricallyConnected t.G.hom := t.semi.geomConnected
  haveI : IrreducibleSpace t.G.left :=
    GlobalTheory.irreducibleSpace_of_smooth_of_geometricallyConnected_domain R t.G inferInstance inferInstance
      ⟨x' (IsLocalRing.closedPoint Ω)⟩
  set q := u (IsLocalRing.closedPoint L) with hq
  have hqg : q = genericPoint t.G.left := by
    have h1 : q ⤳ genericPoint t.G.left := by
      refine specializes_iff_forall_open.2 fun s hs hgs => ?_
      obtain ⟨V, hVa, hpV, -⟩ := exists_isAffineOpen_mem_and_subset
        (U := ⊤) (x := x' (IsLocalRing.closedPoint Ω)) trivial
      have hV : ⊤ ≤ x' ⁻¹ᵁ V := (GlobalTheory.ZH.CrdCalc.top_le_iff x' V).2 hpV
      have hgV : genericPoint t.G.left ∈ V :=
        ((genericPoint_spec t.G.left).mem_open_set_iff V.isOpen).2 ⟨_, trivial, hpV⟩
      let W : t.G.left.Opens := V ⊓ ⟨s, hs⟩
      obtain ⟨b, hbW, hgb⟩ := hVa.exists_basicOpen_le (V := W) ⟨genericPoint t.G.left, hgV, hgs⟩ hgV
      have hb : b ≠ 0 := by
        rintro rfl
        rw [Scheme.basicOpen_zero] at hgb
        exact hgb
      have hv : valR x' V b ≠ 0 := fun h => hb (hinj V b hV h)
      obtain ⟨hV', hval⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (algebraMap Ω L) x' V hV
      have hu : IsUnit (valR u V b) := by
        rw [hval]
        exact (Ne.isUnit ((map_ne_zero_iff _ (IsFractionRing.injective Ω L)).2 hv))
      have := ((GlobalTheory.ZH.CrdCalc.isUnit_valR_iff u V hV' b).1 hu) (Set.mem_univ (IsLocalRing.closedPoint L))
      exact (hbW this).2
    exact (h1.antisymm (genericPoint_specializes q)).eq

  haveI : Smooth P.A.A.hom := P.A.isAb.smooth
  haveI : GeometricallyConnected P.A.A.hom := P.A.isAb.geomConnected
  haveI : IrreducibleSpace P.A.A.left :=
    GlobalTheory.irreducibleSpace_of_smooth_of_geometricallyConnected_domain (FractionRing R) P.A.A inferInstance
      inferInstance ⟨ξ (IsLocalRing.closedPoint L)⟩
  haveI : IsIntegral P.A.A.left := GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace P.A.A.hom
  set y := ξ (IsLocalRing.closedPoint L) with hy
  let mm : P.A.A.left ⟶ t.G.left := P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)
  haveI : IsIso P.U.gen.inv.left := ⟨⟨P.U.gen.hom.left, by
    rw [← Over.comp_left, P.U.gen.inv_hom_id, Over.id_left], n₁⟩⟩
  haveI : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  haveI : IsPreimmersion (pullback.fst t.G.hom (jK R)) := MorphismProperty.of_isPullback (IsPullback.of_hasPullback t.G.hom (jK R)).flip inferInstance
  haveI : IsPreimmersion mm := inferInstance
  have hmy : mm y = q := by
    rw [hq, ← hξ2]
    rfl
  have hyg : y = genericPoint P.A.A.left := by
    apply (Scheme.Hom.isEmbedding mm).injective
    have h1 : mm (genericPoint P.A.A.left) ⤳ mm y :=
      (genericPoint_specializes y).map (Scheme.Hom.continuous mm)
    rw [hmy, hqg] at h1 ⊢
    exact ((genericPoint_specializes _).antisymm h1).eq
  intro O f hO hf
  by_contra hne
  have hne' : P.A.A.left.basicOpen f ≠ ⊥ := fun h => hne ((basicOpen_eq_bot_iff f).1 h)
  have hgen : genericPoint P.A.A.left ∈ P.A.A.left.basicOpen f := by
    refine ((genericPoint_spec P.A.A.left).mem_open_set_iff (P.A.A.left.basicOpen f).isOpen).2 ?_
    obtain ⟨z, hz⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne'
    exact ⟨z, trivial, hz⟩
  have hu : IsUnit (valR ξ O f) :=
    (GlobalTheory.ZH.CrdCalc.isUnit_valR_iff ξ O hO f).2
      ((GlobalTheory.ZH.CrdCalc.top_le_iff ξ _).2 (by rw [← hy, hyg]; exact hgen))
  exact hu.ne_zero hf
