import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThListTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaConstantListOfFibrePullbackFieldExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantUniqueAndLinearInSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.GalConj
open GlobalTheory.UMin.GalTh

theorem coe_mul {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] (τ₁ τ₂ : K ≃ₐ[Ω] K) :
    ((τ₁ * τ₂ : K ≃ₐ[Ω] K) : K →+* K) = (τ₁ : K →+* K).comp (τ₂ : K →+* K) := RingHom.ext fun _ => rfl

theorem coe_one {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] :
    ((1 : K ≃ₐ[Ω] K) : K →+* K) = RingHom.id K := RingHom.ext fun _ => rfl

theorem comp_alg {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] (τ : K ≃ₐ[Ω] K) :
    (τ : K →+* K).comp (algebraMap Ω K) = algebraMap Ω K := RingHom.ext fun r => τ.commutes r

theorem thList_conj : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (Ω K : Type) [Field Ω] [Field K] [IsAlgClosed K] [Algebra Ω K] (x : Sp Ω ⟶ S) (θ : SecAt G L x) (pt : Fin N → (Over.mk (spMap (algebraMap Ω K) ≫ x) ⟶ G)) (c : Fin N → K), Odd m → (m : K) ≠ 0 → PolFib G L g (spMap (algebraMap Ω K) ≫ x) → ThList G L ρ m (spMap (algebraMap Ω K) ≫ x) (SecAt.pull G L θ (algebraMap Ω K)) pt c → ∃ φ : (K ≃ₐ[Ω] K) →* Equiv.Perm (Fin N), ∀ (τ : K ≃ₐ[Ω] K) (a : Fin N), spMap (τ : K →+* K) ≫ (pt a).left = (pt (φ τ a)).left ∧ τ (c a) = c (φ τ a) := by
  intro S G _ _ L ρ hL hρ g m N Ω K _ _ _ _ x θ pt c hm hmK hpol hK
  classical
  have hfix : ∀ τ : K ≃ₐ[Ω] K, spMap (τ : K →+* K) ≫ (Over.mk (spMap (algebraMap Ω K) ≫ x)).hom = (Over.mk (spMap (algebraMap Ω K) ≫ x)).hom := fun τ => by
    show spMap (τ : K →+* K) ≫ spMap (algebraMap Ω K) ≫ x = spMap (algebraMap Ω K) ≫ x
    rw [← Category.assoc, ← GalTh.sp_comp, comp_alg]
  let u : (K ≃ₐ[Ω] K) → (Over.mk (spMap (algebraMap Ω K) ≫ x) ⟶ Over.mk (spMap (algebraMap Ω K) ≫ x)) := fun τ => Over.homMk (spMap (τ : K →+* K)) (hfix τ)
  have hul : ∀ τ, (u τ).left = spMap (τ : K →+* K) := fun τ => Over.homMk_left _ _
  have hu1 : u 1 = 𝟙 _ := Over.OverMorphism.ext (by rw [hul, coe_one, GalTh.sp_id]; rfl)
  have humul : ∀ τ₁ τ₂, u (τ₁ * τ₂) = u τ₁ ≫ u τ₂ := fun τ₁ τ₂ =>
    Over.OverMorphism.ext (by rw [Over.comp_left, hul, hul, hul, coe_mul, GalTh.sp_comp])
  have htor : ∀ τ a, (u τ ≫ pt a) ^ (m ^ 2) = 1 := fun τ a => by
    rw [← MonObj.comp_pow, (hK.2.1 a).1, MonObj.comp_one]
  choose f hf using fun τ a => thList_exh hK (u τ ≫ pt a) (htor τ a)
  have hf1 : ∀ a, f 1 a = a := fun a => hK.1 (by rw [← hf, hu1, Category.id_comp])
  have hfmul : ∀ τ₁ τ₂ a, f (τ₁ * τ₂) a = f τ₁ (f τ₂ a) := fun τ₁ τ₂ a => hK.1 (by
    rw [← hf, ← hf, ← hf, humul, Category.assoc])
  let P : (K ≃ₐ[Ω] K) → Equiv.Perm (Fin N) := fun τ =>
    { toFun := f τ, invFun := f τ⁻¹
      left_inv := fun a => by rw [← hfmul, inv_mul_cancel, hf1]
      right_inv := fun a => by rw [← hfmul, mul_inv_cancel, hf1] }
  let φ : (K ≃ₐ[Ω] K) →* Equiv.Perm (Fin N) :=
    { toFun := P
      map_one' := Equiv.ext fun a => hf1 a
      map_mul' := fun τ₁ τ₂ => Equiv.ext fun a => hfmul τ₁ τ₂ a }
  have hφ : ∀ τ a, φ τ a = f τ a := fun _ _ => rfl
  have hleft : ∀ (τ : K ≃ₐ[Ω] K) a, spMap (τ : K →+* K) ≫ (pt a).left = (pt (f τ a)).left := fun τ a => by
    rw [← hf, Over.comp_left, hul]
  refine ⟨φ, fun τ a => ⟨by rw [hφ]; exact hleft τ a, ?_⟩⟩
  rw [hφ]
  obtain ⟨pt', hpt', h'⟩ := GlobalTheory.UMin.ThPull.thList_pull S G L ρ hL hρ m N K K (τ : K →+* K) (spMap (algebraMap Ω K) ≫ x)
    (SecAt.pull G L θ (algebraMap Ω K)) pt c hK
  obtain ⟨pt₃, hpt₃, h₃⟩ := thList_comp m (algebraMap Ω K) (τ : K →+* K) (algebraMap Ω K) (comp_alg τ) x θ pt' _ h'
  have e3 : pt₃ a = pt (f τ a) := Over.OverMorphism.ext (by rw [hpt₃, hpt', hleft])
  have q := h₃.2.1 a
  rw [e3] at q
  have hθ : SecM.ofSec G (SecAt.pull G L θ (algebraMap Ω K)) =
      @id Γ((Over.mk (spMap (algebraMap Ω K) ≫ x)).left, ⊤) (GlobalTheory.ZH.fn (1 : K)) • SecM.ofSec G (SecAt.pull G L θ (algebraMap Ω K)) := by
    rw [id, show GlobalTheory.ZH.fn (1 : K) = 1 from map_one _, one_smul]
  have r := (GlobalTheory.UMin.thG_smul_iff S G L ρ hL hρ g m K (spMap (algebraMap Ω K) ≫ x) _ _ (pt (f τ a)) 1 (c (f τ a)) (τ (c a)) hm hmK hpol hθ
    (hK.2.1 (f τ a))).1 q
  rw [r, _root_.one_mul]

end GlobalTheory.UMin.GalConj
end
