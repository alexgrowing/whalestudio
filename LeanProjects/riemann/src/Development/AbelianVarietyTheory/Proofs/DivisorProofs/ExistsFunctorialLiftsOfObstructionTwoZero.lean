import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearLiftOfProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulEqZeroOfMemMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDefectCoboundaryOfObstructionClassZeroStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Obs

theorem exists_isFun_of_isOb2_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → Module.Projective R₀ (GlobForm s₀) → ∀ L : Pre I π (OAff s₀), (∀ w, L.IsOb2 α w 0) → ∃ L' : Pre I π (OAff s₀), L'.IsFun := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ hpar hproj L hob

  obtain ⟨θ, -, -, hθ, -⟩ := hob 0

  let Wm : Submodule R (∀ (T T' : AffOp X₀) (_ : T ⟶ T'), L.B T') :=
    { carrier := {g | ∀ T T' a, g T T' a ∈ I.map (algebraMap R (L.B T'))}
      add_mem' := fun hx hy T T' a ↦ Ideal.add_mem _ (hx T T' a) (hy T T' a)
      zero_mem' := fun T T' a ↦ Ideal.zero_mem _
      smul_mem' := fun r g hg T T' a ↦ by
        show r • g T T' a ∈ _
        rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ (hg T T' a) }
  let q : (∀ (T T' : AffOp X₀) (_ : T ⟶ T'), L.B T') →ₗ[R]
      (∀ (T T' T'' : AffOp X₀) (_ : T ⟶ T') (_ : T' ⟶ T''), L.B T'') :=
    { toFun := fun g T T' T'' a b ↦ L.ρ b (g T T' a) - g T T'' (a ≫ b) + g T' T'' b
      map_add' := fun g g' ↦ by
        funext T T' T'' a b
        simp only [Pi.add_apply, map_add]; abel
      map_smul' := fun r g ↦ by
        funext T T' T'' a b
        simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_sub, smul_add] }
  let v : GlobForm s₀ →+ (∀ (T T' T'' : AffOp X₀) (_ : T ⟶ T') (_ : T' ⟶ T''), L.B T'') :=
    { toFun := fun w T T' T'' a b ↦ θ T T' T'' a b (w.1 T)
      map_zero' := by funext T T' T'' a b; simp
      map_add' := fun w w' ↦ by funext T T' T'' a b; simp }
  have hv : ∀ (r : R) (w : GlobForm s₀), v (π r • w) = r • v w := by
    intro r w
    funext T T' T'' a b
    show θ T T' T'' a b (π r • w.1 T) = r • θ T T' T'' a b (w.1 T)
    have e : π r • w.1 T = L.p T (algebraMap R (L.B T) r) • w.1 T := by
      rw [SemiHom.map_algebraMap (L.semi T), algebraMap_smul]
    rw [e, (hθ T T' T'' a b).smul, AlgHom.commutes, ← Algebra.smul_def]
  have hW : ∀ (r : R), π r = 0 → ∀ m ∈ Wm, r • m = 0 := by
    intro r hr m hm
    have hrI : r ∈ I := hk ▸ RingHom.mem_ker.2 hr
    funext T T' a
    show r • m T T' a = 0
    rw [Algebra.smul_def]
    exact mul_eq_zero_of_mem_map hI (Ideal.mem_map_of_mem _ hrI) (hm T T' a)
  have hex : ∀ w : GlobForm s₀, ∃ m ∈ Wm, q m = v w := by
    intro w
    obtain ⟨g, hg, hgθ⟩ := GlobalTheory.T.exists_defect_coboundary_of_obstructionClass_zero R R₀ I hI π hπ hk R₁ α _ (OAff s₀) L w θ hθ (hob w)
    refine ⟨g, hg, ?_⟩
    funext T T' T'' a b
    exact (hgθ T T' T'' a b).symm
  obtain ⟨u, hus, huW, huq⟩ := exists_semilinear_lift_of_projective R R₀ π hπ (GlobForm s₀) hproj _ _ Wm hW q v hv hex

  have hext : ∀ (T T' : AffOp X₀) (a : T ⟶ T'), ∃! ξ : Ω[Sec s₀ T.unop.1⁄R₀] →+ L.B T',
      (∀ b w, ξ (L.p T b • w) = L.ρ a b * ξ w) ∧ (∀ w, ξ w ∈ I.map (algebraMap R (L.B T'))) ∧
        ∀ w : GlobForm s₀, ξ (w.1 T) = u w T T' a := fun T T' a ↦
    exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar T _ _ (L.p T) (L.semi T) (L.surj T) (L.ker T) (L.ρ a)
      ((Pi.evalAddMonoidHom (fun _ ↦ L.B T') a).comp ((Pi.evalAddMonoidHom _ T').comp ((Pi.evalAddMonoidHom _ T).comp u)))
      (fun r w ↦ by
        show u (π r • w) T T' a = r • u w T T' a
        rw [hus]; rfl) (fun w ↦ huW w T T' a)
  choose ξ hξ huniq using hext
  have hβ : ∀ (T T' : AffOp X₀) (a : T ⟶ T'), ∃ β : L.B T →ₐ[R] L.B T', IsTheta I (L.p T) (L.ρ a) β (ξ T T' a) :=
    fun T T' a ↦ (theta_classify R R₀ _ _ _ I hI π hπ (L.p T) (L.semi T) (L.surj T) (L.ker T) (L.ρ a)).2
      (ξ T T' a) (hξ T T' a).1 (hξ T T' a).2.1
  choose ρ' hρ' using hβ
  have hρ'e : ∀ (T T' : AffOp X₀) (a : T ⟶ T') x, ρ' T T' a x = L.ρ a x - ξ T T' a (D R₀ _ (L.p T x)) := by
    intro T T' a x
    rw [(hρ' T T' a).der]; abel
  have hp0 : ∀ (T T' : AffOp X₀) (a : T ⟶ T') y, L.p T' (ξ T T' a y) = 0 :=
    fun T T' a y ↦ (L.ker T' _).2 ((hξ T T' a).2.1 y)
  have hnat : ∀ (T T' : AffOp X₀) (a : T ⟶ T') x, L.p T' (ρ' T T' a x) = mp (OAff s₀) a (L.p T x) := by
    intro T T' a x
    rw [hρ'e, map_sub, hp0, sub_zero, L.nat]
  let L' : Pre I π (OAff s₀) :=
    { B := L.B, p := L.p, semi := L.semi, surj := L.surj, ker := L.ker, smooth := L.smooth
      ρ := fun {T T'} a ↦ ρ' T T' a
      nat := fun {T T'} a x ↦ hnat T T' a x }
  refine ⟨L', ?_⟩

  have hcomp : ∀ (T T' T'' : AffOp X₀) (a : T ⟶ T') (b : T' ⟶ T'') (y : Ω[Sec s₀ T.unop.1⁄R₀]),
      ξ T T'' (a ≫ b) y = L.ρ b (ξ T T' a y) + ξ T' T'' b (p1 (OAff s₀) a y) - θ T T' T'' a b y := by
    intro T T' T'' a b
    let ψ : Ω[Sec s₀ T.unop.1⁄R₀] →+ L.B T'' :=
      AddMonoidHom.mk' (fun y ↦ L.ρ b (ξ T T' a y) + ξ T' T'' b (p1 (OAff s₀) a y) - θ T T' T'' a b y)
        (fun y z ↦ by simp only [map_add]; abel)
    have hψm : ∀ y, ψ y ∈ I.map (algebraMap R (L.B T'')) := fun y ↦
      Ideal.sub_mem _ (Ideal.add_mem _ (algHom_mem_map I (L.ρ b) ((hξ T T' a).2.1 y)) ((hξ T' T'' b).2.1 _))
        ((hθ T T' T'' a b).mem y)
    have e : ψ = ξ T T'' (a ≫ b) := by
      refine huniq T T'' (a ≫ b) ψ ⟨fun c y ↦ ?_, hψm, fun w ↦ ?_⟩
      · have h1 : ψ (L.p T c • y) = L.ρ b (L.ρ a c) * ψ y := by
          show L.ρ b (ξ T T' a (L.p T c • y)) + ξ T' T'' b (p1 (OAff s₀) a (L.p T c • y)) -
              θ T T' T'' a b (L.p T c • y) = L.ρ b (L.ρ a c) * (L.ρ b (ξ T T' a y) + ξ T' T'' b (p1 (OAff s₀) a y) - θ T T' T'' a b y)
          rw [(hξ T T' a).1, oneFormsMapOfFunctorMorphism_smul, ← L.nat, (hξ T' T'' b).1, (hθ T T' T'' a b).smul, map_mul]
          simp only [AlgHom.comp_apply]; ring
        have h2 : L.ρ b (L.ρ a c) = L.ρ (a ≫ b) c + θ T T' T'' a b (D R₀ _ (L.p T c)) := by
          rw [(hθ T T' T'' a b).der]; simp
        rw [h1, h2, add_mul, mul_eq_zero_of_mem_map hI ((hθ T T' T'' a b).mem _) (hψm y), add_zero]
      · show L.ρ b (ξ T T' a (w.1 T)) + ξ T' T'' b (p1 (OAff s₀) a (w.1 T)) - θ T T' T'' a b (w.1 T) = u w T T'' (a ≫ b)
        rw [← w.2 a, (hξ T T' a).2.2, (hξ T' T'' b).2.2]
        have := congrFun (congrFun (congrFun (congrFun (congrFun (huq w) T) T') T'') a) b
        change L.ρ b (u w T T' a) - u w T T'' (a ≫ b) + u w T' T'' b = θ T T' T'' a b (w.1 T) at this
        rw [← this]; abel
    intro y
    rw [← e]; rfl
  intro T T' T'' a b x
  change ρ' T T'' (a ≫ b) x = ρ' T' T'' b (ρ' T T' a x)
  have hD : D R₀ _ (L.p T' (ρ' T T' a x)) = p1 (OAff s₀) a (D R₀ _ (L.p T x)) := by
    rw [hnat, p1_D]
  rw [hρ'e T' T'' b, hD, hρ'e T T' a, map_sub, hρ'e, hcomp]
  have h2 : L.ρ b (L.ρ a x) = L.ρ (a ≫ b) x + θ T T' T'' a b (D R₀ _ (L.p T x)) := by
    rw [(hθ T T' T'' a b).der]; simp
  rw [h2]; abel

end GlobalTheory.Obs
