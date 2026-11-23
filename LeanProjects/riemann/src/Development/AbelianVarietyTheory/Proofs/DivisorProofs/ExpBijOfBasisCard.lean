import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsFunctional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HasBasisOfBasis

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnif

theorem expBij_of_basis_card : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ), AdmBase R I → 1 ≤ k → ∀ (Λ : Type) [Fintype Λ] (b : Module.Basis Λ (FractionRing R) (Fam D.toPre (FractionRing R) k)) (σ : Λ → U.SecK k), Fintype.card Λ = k ^ A.g → (∀ l, U.Expands k (σ l) (b l)) → U.ExpBij k := by
  intro R _ _ I D A G _ _ U k hR hk Λ _ b σ hcard hσ
  classical
  obtain ⟨β, -, hβ⟩ := GlobalTheory.GenericSectionBasis.exists_secK_basis
    GlobalTheory.abelianSchemeLaws_all.1.secBaseChange R I D A G U k hk
  choose C hC using fun l => (hβ (σ l)).exists
  have hCc : ∀ l, GlobalTheory.UnifPowAdm.IsComb (pullback.snd G.hom (jK R)) (σ l) (C l) β := fun l jj => hC l jj
  let Φ : (Λ → FractionRing R) →ₗ[FractionRing R] (Fin (k ^ A.g) → FractionRing R) :=
    { toFun := fun c a => ∑ l, c l * C l a
      map_add' := fun c d => by funext a; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        funext a
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _ }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    obtain ⟨s, hs⟩ := GlobalTheory.UnifPowAdm.exists_isComb (pullback.snd G.hom (jK R)) c σ
    have h1 := hs.trans hCc
    have hz : ∀ a, ∑ l, c l * C l a = 0 := fun a => congrFun hc a
    have h0 : ∀ jj, s.f jj = 0 := fun jj => by
      rw [h1 jj]
      simp [hz]
    have hE := GlobalTheory.UnifPowAdm.expands_comb U k hσ hs
    have h2 := GlobalTheory.ExpZero.main R I D A G U k hR s _ h0 hE
    exact funext fun l => Fintype.linearIndependent_iff.1 b.linearIndependent c h2 l
  have hsurj : Function.Surjective Φ := by
    rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    simp [hcard]
  refine GlobalTheory.UnifPowAdm.expBij_of_basis U k hR b σ hσ fun s => ?_
  obtain ⟨d, hd, -⟩ := hβ s
  obtain ⟨c, rfl⟩ := hsurj d
  obtain ⟨s', hs'⟩ := GlobalTheory.UnifPowAdm.exists_isComb (pullback.snd G.hom (jK R)) c σ
  have e : s' = s := (hs'.trans hCc).unique fun jj => hd jj
  exact ⟨c, e ▸ hs'⟩

end GlobalTheory.ProdUnif
