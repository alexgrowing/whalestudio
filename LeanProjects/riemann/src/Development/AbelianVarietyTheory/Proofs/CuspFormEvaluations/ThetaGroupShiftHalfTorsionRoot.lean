import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalSymLiftExistsUniqueGlobalStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTranslationSectionsUniversalObject
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalSymLiftMulOddStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace RootShift

open ThetaAct CommPairing

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S}

theorem exists_lin_iff (hL : L.IsLB) (θ : ThetaGrp A L k T) :
    ∃ f : SecM A L k T →ₗ[Γ(T.left, ⊤)] SecM A L k T, ∀ s s', IsActOf A L k θ s s' ↔
      f (SecM.ofSec A s) = SecM.ofSec A s' := by
  obtain ⟨f, hf⟩ := exists_lin hL θ
  refine ⟨f, fun s s' => ?_⟩
  rw [isActOf_iff hL]
  exact ⟨fun H => sv_ext hL fun y J hJ => (hf _ _ _ _ _ hJ).trans (H y J hJ).symm,
    fun H y J hJ => H ▸ hf _ _ _ _ _ hJ⟩

theorem exists_isActOf (hL : L.IsLB) (θ : ThetaGrp A L k T) (s : LB.Sec (LPow A L k T)) :
    ∃ s', IsActOf A L k θ s s' := by
  obtain ⟨f, hf⟩ := exists_lin_iff hL θ
  exact ⟨SecM.toSec A (f (SecM.ofSec A s)), (hf _ _).2 rfl⟩

theorem act_smul (hL : L.IsLB) (θ : ThetaGrp A L k T) (c : Γ(T.left, ⊤))
    {a b a' b' : LB.Sec (LPow A L k T)} (h : ∀ j, b.f j = liftFun A _ c * a.f j)
    (ha : IsActOf A L k θ a a') (hb : IsActOf A L k θ b b') :
    ∀ j, b'.f j = liftFun A _ c * a'.f j := by
  obtain ⟨f, hf⟩ := exists_lin_iff hL θ
  have e : SecM.ofSec A b = c • SecM.ofSec A a := Subtype.ext (funext h)
  have e' : SecM.ofSec A b' = c • SecM.ofSec A a' := by
    rw [← (hf _ _).1 ha, ← (hf _ _).1 hb, e, map_smul]
  exact fun j => congrFun (congrArg Subtype.val e') j

theorem liftFun_one (W : (T ⊗ A).left.Opens) : liftFun A W (1 : Γ(T.left, ⊤)) = 1 := by
  unfold liftFun
  rw [map_one, map_one]

theorem toΓ_bijective (B : Type) [CommRing B] : Function.Bijective (toΓ B) :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).symm.commRingCatIsoToRingEquiv.bijective

end RootShift

open RootShift in

theorem isUUOver_shift : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (B : Type) [CommRing B] (x0 : Sp B ⟶ Xo.X) (N : ℕ), Odd N → ∀ (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 (ptO Xo x0))) (t u z : ptO Xo x0 ⟶ Xo.univ.t.G) (e : Γ((ptO Xo x0).left, ⊤)ˣ), t ^ (N ^ 2) = 1 → u ^ (N ^ 2) = 1 → z ^ (N ^ 2) = 1 → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) t u 1 → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) u z e → ∀ F F', IsUUOver Xo.univ.t.G Xo.univ.t.PP N s z (t * u) F → IsUUOver Xo.univ.t.G Xo.univ.t.PP N s (u * z) t F' → ∃ r : B, (toΓ B r) ^ 2 = (e : Γ((ptO Xo x0).left, ⊤)) ∧ r ^ (N ^ 2) = 1 ∧ ∀ j, F.f j = liftFun Xo.univ.t.G _ (T := ptO Xo x0) (toΓ B r) * F'.f j := by
  intro hLaw E _ _ _ H Dw l Xo B _ x0 N hN s t u z e ht hu hz wtu wuz F F' hF hF'
  have hL := Xo.univ.t.PP.isLB
  have htu : (t * u) ^ (N ^ 2) = 1 := by rw [mul_pow, ht, hu, _root_.one_mul]
  obtain ⟨α₀, α, s₁, s₂, Uuz, Ut, g₀, n₀, cα, tw, hUuz, a₁, hUt, a₂⟩ := hF'
  obtain ⟨Uz, Utu, hUz, hUtu⟩ : ∃ Uz Utu,
      SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) z Uz ∧
      SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) (t * u) Utu := by
    obtain ⟨-, -, -, -, Uz, Utu, -, -, -, -, h₁, -, h₂, -⟩ := hF
    exact ⟨Uz, Utu, h₁, h₂⟩
  obtain ⟨⟨Uu, hUu⟩, -⟩ := GlobalTheory.T.universal_symLift_exists_unique_global hLaw E H Dw l Xo N hN _ u hu
  obtain ⟨p, hp⟩ := exists_isActOf hL Uz s₁
  obtain ⟨q, hq⟩ := exists_isActOf hL Uu p
  obtain ⟨w, hw⟩ := exists_isActOf hL Ut q
  obtain ⟨G, hG⟩ := exists_isActOf hL Utu p
  obtain rfl : G = F :=
    ((exists_isVtOver_and_existsUnique_isUUOver hLaw E H Dw l Xo N hN _ s).2 z (t * u) hz htu).unique
      ⟨α₀, α, s₁, p, Uz, Utu, g₀, n₀, cα, tw, hUz, hp, hUtu, hG⟩ hF
  obtain ⟨r₀, r₀2, r₀N, h₀⟩ := GlobalTheory.T.universal_symLift_mul_odd hLaw E H Dw l Xo N hN _ t u Ut Uu Utu 1 hUt hUu hUtu wtu
  obtain ⟨r, r2, rN, h₁⟩ := GlobalTheory.T.universal_symLift_mul_odd hLaw E H Dw l Xo N hN _ u z Uu Uz Uuz e hUu hUz hUuz wuz
  obtain rfl : r₀ = 1 := by
    obtain ⟨m, hm⟩ : Odd (N ^ 2) := hN.pow
    rwa [hm, pow_succ, pow_mul, r₀2, one_pow, _root_.one_mul] at r₀N
  obtain ⟨ρ, hρ⟩ := (toΓ_bijective B).2 (r : Γ((ptO Xo x0).left, ⊤))
  refine ⟨ρ, ?_, (toΓ_bijective B).1 ?_, fun j => ?_⟩
  · rw [hρ]
    exact congrArg Units.val r2
  · rw [map_pow, map_one, hρ]
    exact congrArg Units.val rN
  · have e₀ := h₀ p q w G hq hw hG j
    rw [Units.val_one, liftFun_one, _root_.one_mul] at e₀
    rw [hρ, ← e₀]
    exact act_smul hL Ut _ (h₁ s₁ p q s₂ hp hq a₁) a₂ hw j

end GlobalTheory
