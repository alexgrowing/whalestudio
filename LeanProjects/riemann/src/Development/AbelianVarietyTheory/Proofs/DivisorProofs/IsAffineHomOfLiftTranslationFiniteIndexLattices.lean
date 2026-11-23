import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteOfIsClosedOfFiniteInterClosedPoints
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.RiemannFormBijectiveOfWeilNondeg

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftAffine

section
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem sub_mem_of_ex_eq {z w : Fin g → ℂ} (h : u.ex z = u.ex w) : z - w ∈ u.Λ := by
  have e := u.ex_add (z - w) w
  rw [sub_add_cancel, h] at e
  exact (u.ker _).1 (mul_eq_right.1 e.symm)

theorem ex_eq_of_sub_mem {z w : Fin g → ℂ} (h : z - w ∈ u.Λ) : u.ex z = u.ex w := by
  have e := u.ex_add (z - w) w
  rw [sub_add_cancel, (u.ker _).2 h, _root_.one_mul] at e
  exact e

theorem exists_ex_apply_eq [LocallyOfFiniteType A.hom] (x : A.left) (hx : IsClosed ({x} : Set A.left)) :
    ∃ z, (u.ex z).left (IsLocalRing.closedPoint ℂ) = x := by
  obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk (U := 𝟙_ (Over (Sp ℂ))) (V := A) (pointOfClosedPoint A.hom x hx)
    ((pointOfClosedPoint_comp A.hom x hx).trans rfl))
  exact ⟨z, by rw [hz]; exact pointOfClosedPoint_apply A.hom x hx _⟩

end

theorem isAffineHom_of_lift : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (B : Over (Sp ℂ)) [GrpObj B], IsAbelianScheme B →
    ∀ (L : LB A.left) (L' : LB B.left) (u : HolUnif A L g) (u' : HolUnif B L' g) (a : Fin g → ℂ) (N : ℕ),
    0 < N → u.Λ ≤ u'.Λ → (∀ x ∈ u'.Λ, N • x ∈ u.Λ) →
    ∀ ψ : A.left ⟶ B.left, ψ ≫ B.hom = A.hom → (∀ z, (u.ex z).left ≫ ψ = (u'.ex (z + a)).left) → IsAffineHom ψ := by
  intro g A _ hA B _ hB L L' u u' a N hN hle hN' ψ hψ hex
  have := hA.proper
  have := hB.proper
  have : IsProper (ψ ≫ B.hom) := by rw [hψ]; infer_instance
  have : IsProper ψ := IsProper.of_comp ψ B.hom
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  haveI := u'.discrete
  haveI := holUnif_isZLattice u'
  haveI : Module.Finite ℤ u'.Λ := ZLattice.module_finite ℝ u'.Λ
  let K : Submodule ℤ u'.Λ := u.Λ.comap u'.Λ.subtype
  have hQ : Finite (u'.Λ ⧸ K) := by
    refine Module.finite_of_fg_torsion _ fun q => ?_
    induction q using Submodule.Quotient.induction_on with
    | H l =>
      refine ⟨⟨(N : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hN.ne')⟩, ?_⟩
      change ((N : ℤ) • Submodule.Quotient.mk l : u'.Λ ⧸ K) = 0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      change ((((N : ℤ) • l : u'.Λ)) : Fin g → ℂ) ∈ u.Λ
      rw [Submodule.coe_smul, natCast_zsmul]
      exact hN' _ l.2
  have hLQF : LocallyQuasiFinite ψ := by
    refine GlobalTheory.locallyQuasiFinite_of_finite_fibres_closedPoints ψ fun y hy => ?_
    have hcl : IsClosed ({ψ y} : Set B.left) := by simpa using ψ.isClosedMap _ hy
    refine GlobalTheory.finite_of_isClosed_of_finite_inter_closedPoints (hcl.preimage ψ.continuous) ?_
    obtain ⟨z₀, rfl⟩ := exists_ex_apply_eq u y hy
    let r := Function.surjInv (Submodule.Quotient.mk_surjective K)
    have hr : ∀ q, Submodule.Quotient.mk (r q) = q := Function.surjInv_eq (Submodule.Quotient.mk_surjective K)
    refine (Set.finite_range fun q : u'.Λ ⧸ K =>
      (u.ex (z₀ + ((r q : u'.Λ) : Fin g → ℂ))).left (IsLocalRing.closedPoint ℂ)).subset ?_
    rintro x ⟨hx, hxc⟩
    obtain ⟨z, rfl⟩ := exists_ex_apply_eq u x hxc
    have hx' : ((u.ex z).left ≫ ψ) (IsLocalRing.closedPoint ℂ) =
        ((u.ex z₀).left ≫ ψ) (IsLocalRing.closedPoint ℂ) := by
      first | exact hx | simpa using hx | (simp only [Scheme.Hom.comp_apply]; exact hx)
    rw [hex, hex] at hx'
    have e1 : u'.ex (z + a) = u'.ex (z₀ + a) :=
      Over.OverMorphism.ext (ext_of_apply_closedPoint_eq B.hom (Over.w _) (Over.w _) hx')
    have hl : z - z₀ ∈ u'.Λ := by
      simpa [add_sub_add_right_eq_sub] using sub_mem_of_ex_eq u' e1
    refine ⟨Submodule.Quotient.mk ⟨z - z₀, hl⟩, ?_⟩
    have h2 : (r (Submodule.Quotient.mk ⟨z - z₀, hl⟩) - ⟨z - z₀, hl⟩ : u'.Λ) ∈ K :=
      (Submodule.Quotient.eq K).1 (hr _)
    have h3 : ((r (Submodule.Quotient.mk ⟨z - z₀, hl⟩) : u'.Λ) : Fin g → ℂ) - (z - z₀) ∈ u.Λ := h2
    dsimp only
    rw [ex_eq_of_sub_mem u (z := z₀ + _) (w := z) (by convert h3 using 1; abel)]
  have : IsFinite ψ := .of_isProper_of_locallyQuasiFinite _
  infer_instance

end GlobalTheory.LiftAffine
