import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.XiMulNu
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
import ReciprocityTheory.DualLattices.AinfFacts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineThetaEqZeroIffFontaineXiElementDvd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends

set_option autoImplicit false

noncomputable section

open CategoryTheory WittVector Ideal

namespace GlobalTheory.Published

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

structure CycPerfd (p : ℕ) [Fact p.Prime] : Type 1 where
  R : Type
  [ring : CommRing R]
  [nonunit : Fact ¬IsUnit (p : R)]
  [complete : IsAdicComplete (span {(p : R)}) R]
  reg : IsSMulRegular R (p : R)
  ε : PreTilt R p
  zeta_zero : zeta ε 0 = 1
  surj : Function.Surjective (fontaineTheta R p)
  ker_eq : RingHom.ker (fontaineTheta R p) = span {xi ε}

attribute [instance] CycPerfd.ring CycPerfd.nonunit CycPerfd.complete

def CycPerfd.Over {p : ℕ} [Fact p.Prime] (S S' : CycPerfd p) [Algebra S.R S'.R] (α : Ainf p S.R →+* Ainf p S'.R) : Prop :=
  (∀ a, fontaineTheta S'.R p (α a) = algebraMap S.R S'.R (fontaineTheta S.R p a)) ∧
    (∀ a, α (frobenius a) = frobenius (α a)) ∧ α (teichmuller p S.ε) = teichmuller p S'.ε

def CycPerfd.ofIntegers (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((_root_.frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) : CycPerfd p where
  R := O
  reg := fun a b h => sub_eq_zero.1 (ReciprocityTheory.PGsh.Ainf.torsion_free p O hv 1 _ (by
    have h' : (p : O) * a = (p : O) * b := h
    rw [pow_one, sub_mul, mul_comm a, mul_comm b, h', sub_self]))
  ε := ε
  zeta_zero := (zeta_succ_pow ε 0).symm.trans hε.pow_eq_one
  surj := ReciprocityTheory.PGsh.Ainf.theta_surj p O hv
  ker_eq := ReciprocityTheory.PGsh.Ainf.ker_theta p O hv ε hε

open scoped Formalism.Per in

theorem CycPerfd.nonempty (p : ℕ) [Fact p.Prime] : ∃ S : CycPerfd p, IsPrimitiveRoot (zeta S.ε 1) p := by
  obtain ⟨e, he⟩ := GlobalTheory.MemLoc.Model.exists_isEps p
  exact ⟨CycPerfd.ofIntegers p (Formalism.Per.OC p) (PadicComplexInt.integers p) e he.isPrimitiveRoot_untilt,
    he.isPrimitiveRoot_untilt⟩

theorem CycPerfd.over_refl {p : ℕ} [Fact p.Prime] (S : CycPerfd p) : S.Over S (RingHom.id _) :=
  ⟨fun _ => rfl, fun _ => rfl, rfl⟩

def PrismaticDieudonnePerfd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
  ∃ (M : ∀ S : CycPerfd p, PDivGroup p S.R → ModuleCat.{0} (Ainf p S.R))
    (map : ∀ (S : CycPerfd p) (G H : PDivGroup p S.R), (G ⟶ H) →+ (M S H →ₗ[Ainf p S.R] M S G))
    (φ : ∀ (S : CycPerfd p) (G : PDivGroup p S.R), M S G →ₛₗ[(frobenius : Ainf p S.R →+* Ainf p S.R)] M S G)
    (lie : ∀ (S : CycPerfd p) (G : PDivGroup p S.R), M S G →ₛₗ[fontaineTheta S.R p] G.dual.Lie)
    (du : ∀ (S : CycPerfd p) (G : PDivGroup p S.R), M S G.dual ≃ₗ[Ainf p S.R] Module.Dual (Ainf p S.R) (M S G))
    (l : ∀ S : CycPerfd p, M S (PDivGroup.mu p S.R)) (e : ∀ S : CycPerfd p, M S (const p S.R)),
    (∀ (S : CycPerfd p) (G : PDivGroup p S.R), Module.Projective (Ainf p S.R) (M S G) ∧ Module.Finite (Ainf p S.R) (M S G) ∧
      (∀ q, Module.rankAtStalk (R := Ainf p S.R) (M S G) q = G.height) ∧
      (∀ m, ∃ n, φ S G n = frobenius (xi S.ε) • m) ∧
      Module.Projective S.R G.dual.Lie ∧ Module.Finite S.R G.dual.Lie ∧ Function.Surjective (lie S G) ∧
      (∀ m, lie S G m = 0 ↔ ∃ n, φ S G m = frobenius (xi S.ε) • n) ∧
      map S G G (𝟙 G) = LinearMap.id) ∧
    (∀ (S : CycPerfd p) (G H K : PDivGroup p S.R) (f : G ⟶ H) (g : H ⟶ K),
      map S G K (f ≫ g) = map S G H f ∘ₗ map S H K g) ∧
    (∀ (S : CycPerfd p) (G H : PDivGroup p S.R) (f : G ⟶ H) (m : M S H),
      map S G H f (φ S H m) = φ S G (map S G H f m) ∧
      lie S G (map S G H f m) = lieMap H.dual G.dual (dualHom G H f) (lie S H m) ∧
      ∀ x : M S G.dual, du S H (map S H.dual G.dual (dualHom G H f) x) m = du S G x (map S G H f m)) ∧
    (∀ S : CycPerfd p, Function.Bijective (LinearMap.toSpanSingleton (Ainf p S.R) _ (l S)) ∧
      Function.Bijective (LinearMap.toSpanSingleton (Ainf p S.R) _ (e S)) ∧
      φ S _ (l S) = frobenius (xi S.ε) • l S ∧ φ S _ (e S) = e S ∧
      map S _ _ (epsHom (zeta S.ε) S.zeta_zero (zeta_succ_pow S.ε)) (l S) = Sandwich.mu S.ε • e S ∧
      du S (PDivGroup.mu p S.R) (e S) (l S) = 1) ∧
    ∀ (S S' : CycPerfd p) [Algebra S.R S'.R] (α : Ainf p S.R →+* Ainf p S'.R), S.Over S' α →
      ∃ bc : ∀ G : PDivGroup p S.R, M S G →ₛₗ[α] M S' (G.baseChange S'.R),
        (∀ G, Submodule.span (Ainf p S'.R) (Set.range (bc G)) = ⊤ ∧ ∀ m, bc G (φ S G m) = φ S' _ (bc G m)) ∧
        (∀ (G H : PDivGroup p S.R) (f : G ⟶ H) (m : M S H),
          bc G (map S G H f m) = map S' _ _ (baseChangeMap S'.R f) (bc H m)) ∧
        ∀ j : PDivGroup.mu p S'.R ⟶ (PDivGroup.mu p S.R).baseChange S'.R,
          (∀ n, j.app n (1 ⊗ₜ AddMonoidAlgebra.single 1 1) = AddMonoidAlgebra.single 1 1) →
            map S' _ _ j (bc _ (l S)) = l S'

end GlobalTheory.Published
