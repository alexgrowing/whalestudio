import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecScalOneVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEquivPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportSymmetricLiftsThetaGroupTraitStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem trait_transport : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∀ w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W))), w₀.IsGen → ∀ lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A), (∀ (p : QkPt D.toPre (Kb R) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), QkExt em.toRingHom p p₁ → p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g → (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α) → ∀ E' : Fam T.D'.toPre F (C.n ^ j) → SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j), Eqv T.D'.toPre T.A F (C.n ^ j) lab' E' → ∃ (lab : QkPt D.toPre F (C.n ^ j) → (TFK (R := R) F ⟶ C.A.A)) (E : Fam D.toPre F (C.n ^ j) → SecK C.A.L (snd (TFK (R := R) F) C.A.A).left (C.n ^ j)) (Φ : Fam D.toPre F (C.n ^ j) → Fam T.D'.toPre F (C.n ^ j)), LabExt em (C.lab j) lab ∧ Eqv D.toPre C.A F (C.n ^ j) lab E ∧ (∀ (s : Fam D.toPre F (C.n ^ j)) (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)), F₀.Over s → (∀ f' : ∀ x, T.D'.toPre.SecB (C.n ^ j) x, (∀ x, PullB T.hD x (F₀.f (T.hD.xe x)) (f' x)) → ∀ x, GeneratorPullback.SecScal T.D'.toPre.P.L (DegPre.famφ T.D'.toPre F x) (DegPre.famε (C.n ^ j)) ((Φ s).s x) (T.D'.toPre.famφB x) (DegPre.famε (C.n ^ j)) (f' x) (DegPre.prB T.D'.toPre F).left 1)) ∧ ∀ (s : Fam D.toPre F (C.n ^ j)) (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval (E s) p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval (E' (Φ s)) q z Jt := by
  intro R _ _ _ hR D C j wA hwA W _ _ _ T F _ _ _ _ em hc f hf hfst hα w₀ hw₀ lab' hlab' E' hE'
  obtain ⟨Φ, hΦb, hΦa, hΦs, hΦP, hΦp, hΦf⟩ := GlobalTheory.FamPull.fam_transport R D W T.φ T.D' T.hD F hc (C.n ^ j)
  obtain ⟨lab, hLE, hon, hlr⟩ := GlobalTheory.Mum.Trait.exists_lab_push R hR D C j W T F em hc f hf hfst hα lab' hlab' hE'.onto
  obtain ⟨Tr, hTb, hTa, hTs, hTv⟩ := GlobalTheory.Mum.SecMove.exists_trait_transport R hR D C j wA hwA W T F hc f hf hfst hα w₀ hw₀
  have hC2 := GlobalTheory.T.transport_symmetric_lifts_theta_group_trait R hR D C j wA hwA W T F hc f hf hfst hα w₀ hw₀
  refine ⟨lab, fun s => Tr (E' (Φ s)), Φ, hLE, ⟨?_, ?_, ?_, hon, ?_, ?_, ?_⟩, hΦP, fun s => hTv (E' (Φ s))⟩
  · exact hTb.comp (hE'.bij.comp hΦb)
  · intro s s' s'' h i
    exact hTa _ _ _ (hE'.add _ _ _ (hΦa s s' s'' h)) i
  · intro c s s' h i
    exact hTs c _ _ (hE'.smul c _ _ (hΦs c s s' h)) i
  · intro p
    obtain ⟨p', hy, hg⟩ := hΦp p
    exact (hΦf p p' hy hg).1 (hE'.frame p')
  · intro p
    obtain ⟨p', hy, hg⟩ := hΦp p
    exact (hC2 _ _ (hlr p p' hy hg) ((hE'.onto _).2 ⟨p', rfl⟩)).1 (hE'.lift p')
  · intro p w θ s s' hw hθ hr
    obtain ⟨p', hy, hg⟩ := hΦp p
    obtain ⟨w', hw', hr'⟩ := (hΦf p p' hy hg).2 w hw
    obtain ⟨θ', hθ', hact⟩ := (hC2 _ _ (hlr p p' hy hg) ((hE'.onto _).2 ⟨p', rfl⟩)).2 θ hθ
    exact hact _ _ _ _ (hTv _) (hTv _) (hE'.act p' w' θ' _ _ hw' hθ' (hr' s s' hr))

end GlobalTheory.Mum
