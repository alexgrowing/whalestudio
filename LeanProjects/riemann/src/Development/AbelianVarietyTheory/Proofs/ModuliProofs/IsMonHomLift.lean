import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.SharpPull

section
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A C : Over S} {A' C' : Over S'}
  [GrpObj A] [GrpObj C] [GrpObj A'] [GrpObj C'] {φ : A'.left ⟶ A.left} {ψ : C'.left ⟶ C.left}

theorem push_inj (h : IsGrpPullback A' A f φ) {T : Over S'} {x y : T ⟶ A'}
    (e : pushHom h T x = pushHom h T y) : x = y :=
  Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))

theorem push_left (h : IsGrpPullback A' A f φ) {T : Over S'} (x : T ⟶ A') :
    (pushHom h T x).left = x.left ≫ φ := rfl

theorem push_surj (h : IsGrpPullback A' A f φ) {T : Over S'} (y : Over.mk (T.hom ≫ f) ⟶ A) :
    ∃ x : T ⟶ A', pushHom h T x = y :=
  ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem push_comp (h : IsGrpPullback A' A f φ) (h' : IsGrpPullback C' C f ψ) {p : A ⟶ C} {p' : A' ⟶ C'}
    (e : p'.left ≫ ψ = φ ≫ p.left) {T : Over S'} (x : T ⟶ A') :
    pushHom h' T (x ≫ p') = pushHom h T x ≫ p :=
  Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, e, Category.assoc])

theorem exists_lift (h : IsGrpPullback A' A f φ) (h' : IsGrpPullback C' C f ψ) (p : A ⟶ C) :
    ∃ p' : A' ⟶ C', p'.left ≫ ψ = φ ≫ p.left :=
  ⟨Over.homMk (h'.1.lift (φ ≫ p.left) A'.hom (by rw [Category.assoc, Over.w, h.1.w])) (h'.1.lift_snd _ _ _),
    h'.1.lift_fst _ _ _⟩

theorem isMonHom_lift (h : IsGrpPullback A' A f φ) (h' : IsGrpPullback C' C f ψ) {p : A ⟶ C} [IsMonHom p]
    {p' : A' ⟶ C'} (e : p'.left ≫ ψ = φ ≫ p.left) : IsMonHom p' := by
  have h1 : (1 : 𝟙_ (Over S') ⟶ A') ≫ p' = 1 := by
    apply push_inj h'
    rw [push_comp h h' e, map_one, map_one, MonObj.one_comp]
  have h2 : (fst A' A' * snd A' A') ≫ p' = (fst A' A' ≫ p') * (snd A' A' ≫ p') := by
    apply push_inj h'
    rw [push_comp h h' e, map_mul, map_mul, MonObj.mul_comp, push_comp h h' e, push_comp h h' e]
  constructor
  · simpa [Hom.one_def] using h1
  · rw [Hom.mul_def, Hom.mul_def] at h2
    have e1 : lift (fst A' A' ≫ p') (snd A' A' ≫ p') = p' ⊗ₘ p' := by ext <;> simp
    simpa [e1] using h2
end

theorem sharp_pull : ∀ (h g k : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (o : Type) [CommRing o] (b : TBase o k) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s) (t' : TObj g k J b s') (c : SiegPre h k (b.ζ : o) s), f ≫ s = s' → TMap t' t f → c.Principal → IsSharp W a bas t c → ∃ c' : SiegPre h k (b.ζ : o) s', c'.Principal ∧ IsSharp W a bas t' c' := by
  intro h g k W J a bas o _ b S S' s s' f t t' c hf ⟨φ, hφ, hL, hpt, hact⟩ hc ⟨pr, hmon, huniv, hiso, hmat, hlev⟩
  obtain ⟨⟨c', hpb⟩, hprin⟩ := GlobalTheory.T.siegelObject_pullback_exists_and_principal h k o (b.ζ : o) S S' s s' f c hf
  refine ⟨c', hprin c' hpb hc, ?_⟩
  obtain ⟨ψ, ψ₂, hψ, hsq, ⟨w, hw⟩, hlv⟩ := hpb
  choose pr' hpr using fun u => exists_lift hφ hψ (pr u)
  refine ⟨pr', fun u => ?_, fun T y => ?_, ?_, fun j u => ?_, fun i u => ?_⟩
  · have := hmon u
    exact isMonHom_lift hφ hψ (hpr u)
  · obtain ⟨x₀, hx₀, hu⟩ := huniv (Over.mk (T.hom ≫ f)) (fun u => pushHom hψ T (y u))
    obtain ⟨x, rfl⟩ := push_surj hφ x₀
    refine ⟨x, fun u => push_inj hψ ?_, fun x' hx' => push_inj hφ (hu _ fun u => ?_)⟩
    · rw [push_comp hφ hψ (hpr u), hx₀ u]
    · rw [← push_comp hφ hψ (hpr u), hx' u]
  · have hc : ∀ uv : Fin 8 × Fin 8, (lift (pr' uv.1) (pr' uv.2)).left ≫ ψ₂ = φ ≫ (lift (pr uv.1) (pr uv.2)).left := by
      intro uv
      apply pullback.hom_ext
      · show (_ ≫ ψ₂) ≫ (fst c.A c.A).left = (φ ≫ _) ≫ (fst c.A c.A).left
        rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, hpr, Category.assoc,
          ← Over.comp_left, lift_fst]
      · show (_ ≫ ψ₂) ≫ (snd c.A c.A).left = (φ ≫ _) ≫ (snd c.A c.A).left
        rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, hpr, Category.assoc,
          ← Over.comp_left, lift_snd]
    have H₁ := iso_linComb ((isGen_iff w).1 hw)
      (fun uv : Fin 8 × Fin 8 => (lift (pr' uv.1) (pr' uv.2)).left) (fun uv => W uv.1 uv.2)
    have H₂ : LBIso (t.L.pull φ) (LB.LinComb c.P
        (fun uv : Fin 8 × Fin 8 => (lift (pr' uv.1) (pr' uv.2)).left ≫ ψ₂) (fun uv => W uv.1 uv.2)) :=
      LBIso.chartPull (chartPullPull t.L φ φ rfl) (chartPullSame c.P _ _ _ φ hc) hiso
    exact LBIso.trans t'.isLB (DVR.linComb_isLB _ c.isLB _ _) (DVR.linComb_isLB _ c'.isLB _ _)
      (LBIso.trans t'.isLB (DVR.linComb_isLB _ t.isLB _ _) (DVR.linComb_isLB _ c.isLB _ _) hL H₂) H₁.symm
  · apply push_inj hψ
    have e : ∀ v, pushHom hψ t'.A (pr' v) = preHom (pushHom hφ t'.A (𝟙 _)) (pr v) := fun v =>
      (congrArg _ (Category.id_comp _).symm).trans (push_comp hφ hψ (hpr v) (𝟙 _))
    have e₂ : pushHom hφ t'.A (t'.act j) = pushHom hφ t'.A (𝟙 _) ≫ t.act j :=
      (congrArg _ (Category.id_comp _).symm).trans (push_comp hφ hφ (hact j) (𝟙 _))
    rw [push_comp hφ hψ (hpr u), e₂, Category.assoc, hmat j u]
    refine (map_list_prod (preHom (pushHom hφ t'.A (𝟙 _))) _).trans (Eq.trans ?_ (map_list_prod _ _).symm)
    rw [List.map_ofFn, List.map_ofFn]
    congr 2
    funext v
    simp only [Function.comp, map_zpow, e]
  · apply hψ.1.hom_ext
    · rw [hlv, ← hlev i u, Over.comp_left, Over.comp_left, Category.assoc, hpr, ← Category.assoc, hpt, Category.assoc]
    · rw [Over.w, Over.w]; rfl

end GlobalTheory.SharpPull
end
