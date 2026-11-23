import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def AbelianDieudonne : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p],
    ∃ (M : ∀ (A : Over (Sp k)) [GrpObj A], ModuleCat.{0} (WittVector p k))
      (map : ∀ {A B : Over (Sp k)} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f],
        M A →ₗ[WittVector p k] M B)
      (F : ∀ (A : Over (Sp k)) [GrpObj A],
        M A →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] M A)
      (V : ∀ (A : Over (Sp k)) [GrpObj A],
        M A →ₛₗ[((WittVector.frobeniusEquiv p k).symm : WittVector p k →+* WittVector p k)] M A)
      (red : ∀ (A : Over (Sp k)) [GrpObj A],
        M A →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] HdR A),
      (∀ (A : Over (Sp k)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
        SmoothOfRelativeDimension g A.hom →
        Module.Free (WittVector p k) (M A) ∧ Module.Finite (WittVector p k) (M A) ∧
        Module.finrank (WittVector p k) (M A) = 2 * g ∧
        (∀ m, F A (V A m) = p • m) ∧ (∀ m, V A (F A m) = p • m) ∧
        Function.Surjective (red A) ∧ (∀ m, red A m = 0 ↔ ∃ n, m = p • n) ∧
        (∀ h, h ∈ Fil A ↔ ∃ m, h = red A (V A m)) ∧
        map (𝟙 A) = LinearMap.id) ∧
      (∀ (A B : Over (Sp k)) [GrpObj A] [GrpObj B], IsAbelianScheme A → IsAbelianScheme B →
        (∀ (f : A ⟶ B) [IsMonHom f] (m : M A),
          map f (F A m) = F B (map f m) ∧ map f (V A m) = V B (map f m) ∧
          red B (map f m) = push (dp0 k) (𝟙 _) f (red A m)) ∧
        ∀ (f g : A ⟶ B) [IsMonHom f] [IsMonHom g] [IsMonHom (f * g)],
          map (f * g) = map f + map g) ∧
      ∀ (A B C : Over (Sp k)) [GrpObj A] [GrpObj B] [GrpObj C], IsAbelianScheme A →
        IsAbelianScheme B → IsAbelianScheme C →
        ∀ (f : A ⟶ B) (g : B ⟶ C) [IsMonHom f] [IsMonHom g], map (f ≫ g) = map g ∘ₗ map f

namespace AbelianDieudonne

theorem exists_action (H : AbelianDieudonne) (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p]
    [PerfectRing k p] {A : Over (Sp k)} [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) {O : Type} [CommRing O] (a : OAct O A) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module (WittVector p k) M)
      (ρ : O →+* Module.End (WittVector p k) M)
      (F : M →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] M)
      (red : M →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] HdR A),
      Module.Free (WittVector p k) M ∧ Module.Finite (WittVector p k) M ∧
      Module.finrank (WittVector p k) M = 2 * g ∧ Function.Injective F ∧
      (∀ x m, ρ x (F m) = F (ρ x m)) ∧ Function.Surjective red ∧
      (∀ m, red m = 0 ↔ ∃ n, m = p • n) ∧
      ∀ x m, red (ρ x m) = act (dp0 k) (𝟙 _) a x (red m) := by
  obtain ⟨M, map, F, V, red, h1, h2, h3⟩ := H p k
  obtain ⟨hfree, hfin, hrk, -, hVF, hs, hk, -, hid⟩ := h1 A g hA hg
  obtain ⟨hnat, hadd⟩ := h2 A A hA hA
  have hc : ∀ {f f' : A ⟶ A} [IsMonHom f] [IsMonHom f'], f = f' → map f = map f' := by
    intro f f' _ _ e; subst e; rfl
  have := a.hom
  let ρ : O →+* Module.End (WittVector p k) (M A) := RingHom.mk'
    { toFun x := map (a.act x)
      map_one' := (hc a.one).trans hid
      map_mul' x y := (hc ((congrArg a.act (mul_comm x y)).trans (a.mul y x))).trans
        (h3 A A A hA hA hA _ _) }
    fun x y ↦ by
      have : IsMonHom (a.act x * a.act y) := a.add x y ▸ a.hom _
      exact (hc (a.add x y)).trans (hadd _ _)
  refine ⟨M A, inferInstance, inferInstance, ρ, F A, red A, hfree, hfin, hrk, ?_,
    fun x m ↦ (hnat _ m).1, hs, hk, fun x m ↦ (hnat _ m).2.2⟩
  refine (injective_iff_map_eq_zero _).2 fun m hm ↦ ?_
  have e := hVF m
  rw [hm, map_zero, ← Nat.cast_smul_eq_nsmul (WittVector p k)] at e
  exact (smul_eq_zero.1 e.symm).resolve_left (WittVector.p_nonzero p k)

end AbelianDieudonne

end GlobalTheory.Published
