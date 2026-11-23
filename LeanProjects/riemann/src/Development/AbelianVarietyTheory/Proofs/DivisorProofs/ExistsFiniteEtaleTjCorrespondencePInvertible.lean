import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackTer
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeTjIsogeniesRepresentableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsTypeTjPIsogenyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeTjCorrespondenceTargetFiniteEtalStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem exists_tjCorr_finiteEtale : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∃ T : TjCorr M.toRepFam r w j c, IsFinite T.s ∧ Etale T.s ∧ Surjective T.s ∧ IsFinite T.t ∧ Etale T.t ∧ ∀ (S : Scheme.{0}) (x : S ⟶ M.X) (o₁ o₁' : Obj b N (x ≫ M.s)) (m : ObjMap o₁ M.univ x) (ψ₁ : o₁.A ⟶ o₁'.A), IsUnit ((p : ℕ) : Γ(S, ⊤)) → IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : S ⟶ T.Y, y ≫ T.s = x ∧ ∃ (m₀ : ObjMap o₁ T.o y) (m₁ : ObjMap o₁' T.o' y), m₀.φ ≫ T.ψ.left = ψ₁.left ≫ m₁.φ := by
  intro p _ D R _ _ b N hN hNp hp r w j c hw hu hj hc hm M
  haveI : LocallyOfFiniteType M.s := by
    haveI : Smooth M.s := M.smooth.smooth
    infer_instance
  haveI : IsLocallyNoetherian M.X := LocallyOfFiniteType.isLocallyNoetherian M.s
  obtain ⟨Y, o₀, m₀, o', ψ, hfin, het, hisog, htj, huniv⟩ :=
    GlobalTheory.T.harrisTaylor_typeTj_isogenies_representable p D R b N hN hNp hp r w j c hw hu hj hc hm M.X M.s M.univ
  obtain ⟨t, ⟨ht, ⟨mt⟩⟩, -⟩ := M.rep Y.left (Y.hom ≫ M.s) o'
  obtain ⟨h3, h4⟩ := GlobalTheory.T.harrisTaylor_typeTj_correspondence_target_finite_etale p D R b N hN hNp hp r w j c hw hu hj hc hm M Y.left Y.hom t ht.symm o₀ o' m₀ mt ψ
    hisog htj hfin het huniv
  have hsurj : Surjective Y.hom := by
    refine ⟨fun x => ?_⟩
    obtain ⟨k, _, _, a, ha⟩ := GlobalTheory.FinEt.exists_algClosed_point M.X x
    obtain ⟨o₁, ⟨m⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N M.X (Sp k) M.s a M.univ
    obtain ⟨o₁', ψ₁, h1, h2⟩ := GlobalTheory.T.harrisTaylor_exists_typeTj_pIsogeny p D R b N hN hNp hp r w j c hw hu hj hc hm k (a ≫ M.s) o₁
    obtain ⟨y, ⟨hy, -⟩, -⟩ := huniv (Sp k) a o₁ o₁' m ψ₁ h1 h2
    have hx : x ∈ Set.range a.base := by rw [ha]; rfl
    obtain ⟨z', rfl⟩ := hx
    exact ⟨y.base z', by rw [← hy]; rfl⟩
  let T : TjCorr M.toRepFam r w j c :=
    { Y := Y.left, s := Y.hom, t := t, st := ht.symm, o := o₀, o' := o', ms := m₀, mt := mt, ψ := ψ,
      isog := hisog, tj := htj, wPrime := hw.isPrime, uLe := hu,
      pReg := fun U f hf => pReg_of_isUnit (Y.hom ≫ M.s) hp U f hf, sFin := hfin, tFin := h3, sSurj := hsurj }
  exact ⟨T, hfin, het, hsurj, h3, h4, fun S x o₁ o₁' m ψ₁ _ h1 h2 => huniv S x o₁ o₁' m ψ₁ h1 h2⟩

end GlobalTheory.UPel.HT.ES
