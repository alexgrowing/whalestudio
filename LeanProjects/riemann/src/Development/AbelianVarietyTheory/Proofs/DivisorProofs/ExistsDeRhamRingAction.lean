import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPullHomExtAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOnAff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasicoherentHomFromAffine

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.AbDatum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDatum.DRAct

section Pull

variable {R : Type} [CommRing R] {I : Ideal R} {S : Scheme.{0}} (κ : DividedPowers I) (t : S ⟶ Sp R)
  {A : Over S} [GrpObj A]

theorem primPull_of_eq_id (f : A ⟶ A) [IsMonHom f] (h : f = 𝟙 A) (c : prim κ t A) : primPull κ t f c = c := by
  subst h
  exact Subtype.ext (IsMor.pullCohomologyOne_id _ c.1)

theorem primPull_of_eq_comp (f g k : A ⟶ A) [IsMonHom f] [IsMonHom g] [IsMonHom k] (h : k = f ≫ g)
    (c : prim κ t A) : primPull κ t k c = primPull κ t f (primPull κ t g c) := by
  subst h
  exact (GrpMor.pull_pull _ _ _ (fun _ ↦ rfl) rfl c).symm

theorem primPull_of_eq_mul (f g k : A ⟶ A) [IsMonHom f] [IsMonHom g] [IsMonHom k] (h : k = f * g)
    (c : prim κ t A) : primPull κ t k c = primPull κ t f c + primPull κ t g c := by
  subst h
  exact Subtype.ext (c.2 A f g)

end Pull

variable {O : Type} [CommRing O] {T : Scheme.{0}} {A : Over T} [GrpObj A] (i : OAct O A)

theorem actPull_one {V : T.Opens} (hV : IsAffineOpen V) (c : primDR (onAff A hV)) : actPull i 1 hV c = c :=
  haveI := i.hom
  primPull_of_eq_id _ _ _ (by rw [i.one, CategoryTheory.Functor.map_id]) c

theorem actPull_mul (x y : O) {V : T.Opens} (hV : IsAffineOpen V) (c : primDR (onAff A hV)) :
    actPull i (x * y) hV c = actPull i x hV (actPull i y hV c) :=
  haveI := i.hom
  primPull_of_eq_comp _ _ _ _ _ (by rw [i.mul, CategoryTheory.Functor.map_comp]) c

theorem actPull_add (x y : O) {V : T.Opens} (hV : IsAffineOpen V) (c : primDR (onAff A hV)) :
    actPull i (x + y) hV c = actPull i x hV c + actPull i y hV c :=
  haveI := i.hom
  primPull_of_eq_mul _ _ _ _ _ (by rw [i.add]; exact CategoryTheory.Functor.map_mul _ _ _) c

theorem transition_comm (f : A ⟶ A) {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    {b : Sp Γ(T, V') ⟶ Sp Γ(T, V)} {φ : (onAff A hV').left ⟶ (onAff A hV).left}
    (w : φ ≫ (onAff A hV).hom = (onAff A hV').hom ≫ b)
    (hφ : φ ≫ pullback.fst A.hom hV.fromSpec = pullback.fst A.hom hV'.fromSpec) :
    φ ≫ ((Over.pullback hV.fromSpec).map f).left = ((Over.pullback hV'.fromSpec).map f).left ≫ φ := by
  have k {W : T.Opens} (hW : IsAffineOpen W) :
      ((Over.pullback hW.fromSpec).map f).left ≫ pullback.fst A.hom hW.fromSpec =
        pullback.fst A.hom hW.fromSpec ≫ f.left := pullback.lift_fst _ _ _
  refine pullback.hom_ext ?_ ?_
  · refine (Category.assoc _ _ _).trans ((congrArg (φ ≫ ·) (k hV)).trans ?_)
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f.left) hφ).trans ?_)
    refine (k hV').symm.trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
    exact congrArg (_ ≫ ·) hφ.symm
  · refine (Category.assoc _ _ _).trans
      ((congrArg (φ ≫ ·) (Over.w ((Over.pullback hV.fromSpec).map f))).trans (w.trans ?_))
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_ (congrArg (_ ≫ ·) w.symm)
    refine Eq.trans ?_ (Category.assoc _ _ _)
    exact congrArg (· ≫ b) (Over.w ((Over.pullback hV'.fromSpec).map f)).symm

variable {H : T.Modules} (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV))

theorem actPull_res (he : IsDRIso A H e) (x : O) {V V' : T.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') (h : V' ≤ V) (s : Γ(H, V)) :
    (e V' hV').symm (actPull i x hV' (e V' hV' (Twist.resM H h s))) =
      Twist.resM H h ((e V hV).symm (actPull i x hV (e V hV s))) := by
  letI := resAlg h
  haveI := i.hom x
  obtain ⟨φ, hφ, hφ'⟩ := DeRhamSheaf.VB.exists_transition A hV hV' h
  have a := he V V' hV hV' h φ hφ hφ'
  refine (e V' hV').symm_apply_eq.2 (Eq.trans ?_ (a _).symm)
  refine (congrArg (actPull i x hV') (a s)).trans ?_
  refine Eq.trans ?_
    (congrArg (GlobalTheory.Published.AbelianDeRham.bcMor hφ).pull ((e V hV).apply_symm_apply _).symm)
  have m := homMor (dp0 Γ(T, V)) (𝟙 _) (A := onAff A hV) (B := onAff A hV)
    ((Over.pullback hV.fromSpec).map (i.act x))
  have m' := homMor (dp0 Γ(T, V')) (𝟙 _) (A := onAff A hV') (B := onAff A hV')
    ((Over.pullback hV'.fromSpec).map (i.act x))
  have k := m.comp (GlobalTheory.Published.AbelianDeRham.bcMor hφ)
  exact (GrpMor.pull_pull (GlobalTheory.Published.AbelianDeRham.bcMor hφ) m' k (fun _ ↦ rfl)
    (transition_comm (i.act x) hV hV' hφ.1.w hφ').symm _).trans
    (GrpMor.pull_pull m (GlobalTheory.Published.AbelianDeRham.bcMor hφ) k (fun _ ↦ rfl) rfl _).symm

theorem exists_hom (he : IsDRIso A H e) (x : O) :
    ∃ u : H ⟶ H, ∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      e V hV (u.app V s) = actPull i x hV (e V hV s) := by
  obtain ⟨u, hu⟩ := GlobalTheory.hom_of_affine_compatible T H H
    (fun V hV ↦ (e V hV).symm.toLinearMap ∘ₗ actPull i x hV ∘ₗ (e V hV).toLinearMap)
    fun V V' hV hV' h s ↦ actPull_res i e he x hV hV' h s
  exact ⟨u, fun V hV s ↦ (congrArg (e V hV) (LinearMap.congr_fun (hu V hV) s)).trans
    ((e V hV).apply_symm_apply _)⟩

end GlobalTheory.AbDatum.DRAct

open GlobalTheory.AbDatum.DRAct in

theorem GlobalTheory.AbDatum.exists_isDRAct : ∀ (O : Type) [CommRing O] (T : Scheme.{0}) (A : Over T) [GrpObj A],
    IsAbelianScheme A → ∀ (i : OAct O A) (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)), IsDRIso A H e →
    ∃ ρ : O →+* End H, IsDRAct e i ρ := by
  intro O _ T A _ _ i H e he
  choose u hu using exists_hom i e he
  have h1 : u 1 = 𝟙 H := hom_ext_affine fun V hV s ↦
    (e V hV).injective ((hu 1 V hV s).trans (actPull_one i hV (e V hV s)))
  have h2 (x y : O) : u (x * y) = u y ≫ u x := hom_ext_affine fun V hV s ↦ by
    change (u (x * y)).app V s = (u x).app V ((u y).app V s)
    apply (e V hV).injective
    rw [hu, hu, hu, actPull_mul]
  have h3 (x y : O) : u (x + y) = u x + u y := hom_ext_affine fun V hV s ↦ by
    change (u (x + y)).app V s = (u x).app V s + (u y).app V s
    apply (e V hV).injective
    rw [map_add, hu, hu, hu, actPull_add]
  exact ⟨RingHom.mk' { toFun x := (u x : End H), map_one' := h1, map_mul' := h2 } h3, hu⟩
