import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.AdjPairing

theorem weilIs_adj_eq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → ∀ α β : A ⟶ A, IsMonHom α → IsMonHom β → LBIso (P.pull (lift (fst A A ≫ α) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ β)).left) → ∀ (n : ℤ) (T : Over S) (a b : T ⟶ A) (c c' : Γ(T.left, ⊤)ˣ), Out.WeilIs (G2 A) P n (lift (a ≫ α) 1) (lift 1 b) c → Out.WeilIs (G2 A) P n (lift a 1) (lift 1 (b ≫ β)) c' → c = c' := by
  intro S A _ _ P hA hP α β hα hβ hiso n T a b c c' h h'
  let ψ₁ : G2 A ⟶ G2 A := lift (fst A A ≫ α) (snd A A)
  let ψ₂ : G2 A ⟶ G2 A := lift (fst A A) (snd A A ≫ β)
  haveI : IsMonHom ψ₁ := inferInstanceAs (IsMonHom (lift (fst A A ≫ α) (snd A A)))
  haveI : IsMonHom ψ₂ := inferInstanceAs (IsMonHom (lift (fst A A) (snd A A ≫ β)))
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hL : (P.pull ψ₁.left).IsLB := pull_isLB hP _
  have hx₁ : lift a 1 ≫ ψ₁ = lift (a ≫ α) 1 := by ext <;> simp [ψ₁]
  have hy₁ : lift 1 b ≫ ψ₁ = lift 1 b := by ext <;> simp [ψ₁]
  have hx₂ : lift a 1 ≫ ψ₂ = lift a 1 := by ext <;> simp [ψ₂]
  have hy₂ : lift 1 b ≫ ψ₂ = lift 1 (b ≫ β) := by ext <;> simp [ψ₂]
  have hw₁ : LBIso (lbPow (P.pull ψ₁.left) 1) (P.pull ψ₁.left) := lbIso_lbPow_one hL
  have hw₂ : LBIso (lbPow (P.pull ψ₁.left) 1) (P.pull ψ₂.left) :=
    LBIso.trans (isLB_lbPow hL 1) hL (pull_isLB hP _) (lbIso_lbPow_one hL) hiso
  have h1 := WeilIsogeny.weilIs_pull_hom (d := 1) (x := lift a 1) (y := lift 1 b)
    globalFns_holds hAA hL hP ψ₁ hw₁ (by rw [hx₁, hy₁]; exact h)
  have h2 := WeilIsogeny.weilIs_pull_hom (d := 1) (x := lift a 1) (y := lift 1 b)
    globalFns_holds hAA hL hP ψ₂ hw₂ (by rw [hx₂, hy₂]; exact h')
  rw [Nat.cast_one, _root_.mul_one] at h1 h2
  exact CommutatorPairing.weilIs_unique globalFns_holds hAA hL h1 h2

end GlobalTheory.AdjPairing
