import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaSuccPow

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PDiv GlobalTheory.PDivGroup WithConv
open GlobalTheory.DeRham (spOver spOver_comp)

open GlobalTheory GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Closed

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Closed

theorem tatePt_tau_surjective : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {t : SAB H (Sp k)} {p : ℕ} [Fact p.Prime] {GG : PDivGroup p k} (tw : GG.TorsionTower t.G) (I : GeomTate Dw t), ∀ (n : ℕ) (K : Type) [Field K] [Algebra k K] (φ : GG.A n →ₐ[k] K), ∃ x : Dw.La, tatePt (tau tw I x) n K = φ := by
  intro E _ _ _ H Dw k _ _ _ t p _ GG tw I n K _ _ φ

  have hm : ∀ a, φ a ∈ (Algebra.ofId k K).range := fun a => by
    have hi : IsIntegral k (φ a) := (Algebra.IsIntegral.isIntegral a).map φ
    exact minpoly.mem_range_of_degree_eq_one k (φ a)
      (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hi))
  have hinj : Function.Injective (Algebra.ofId k K) := (algebraMap k K).injective
  let e := AlgEquiv.ofInjective _ hinj
  let ψ : GG.A n →ₐ[k] k := (e.symm : (Algebra.ofId k K).range →ₐ[k] k).comp (φ.codRestrict _ hm)
  have hψ : (Algebra.ofId k K).comp ψ = φ :=
    AlgHom.ext fun a => congrArg Subtype.val (e.apply_symm_apply ⟨φ a, hm a⟩)

  have hp : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  have hz : (selfIso.inv ≫ spOver ψ ≫ tw.y n) ^ p ^ n = 1 := by
    rw [← MonObj.comp_pow, (tw.exists_iff n _).1 ⟨ψ, rfl⟩, MonObj.comp_one]
  obtain ⟨x, hx⟩ := (I.onto (p ^ n) hp _).1 hz
  refine ⟨x, ?_⟩
  have hl : latPt tw I n x = ψ := by
    refine tw.inj n k _ _ ?_
    rw [latPt_y, hx, Iso.hom_inv_id_assoc]
  show (Algebra.ofId k K).comp ((tau tw I x).pt n) = φ
  rw [tau_pt, hl, hψ]

end GlobalTheory.GroupBplus.Closed
