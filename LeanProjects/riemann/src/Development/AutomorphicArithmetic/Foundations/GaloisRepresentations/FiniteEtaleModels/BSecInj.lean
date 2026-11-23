import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.SecInjG
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSecInj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

open private half_ker from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSecInj

theorem UpperTheory.Gal.FiniteEtaleModels.secInjG_of :
    UpperTheory.Gal.crystallineComparison.Mod.PulledEx → UpperTheory.Gal.crystallineComparison.Mod.PulledRead → UpperTheory.Gal.crystallineComparison.Mod.PullKer → UpperTheory.Gal.crystallineComparison.Mod.KerFromU → UpperTheory.Gal.crystallineComparison.Mod.IsoOfKer → SecInjG := by
  intro hPE hPR hPK hKU hIK p _ D R _ b N hN hNp hm r w j e hw hu hj he M T K _ _ _ x y y' hy hy' hK
  have hpK0 : IsUnit ((p : ℕ) : K) := by
    refine IsUnit.mk0 _ ?_
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpK : IsUnit ((p : ℕ) : Γ(Sp K, ⊤)) := by
    have := hpK0.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    simpa using this
  obtain ⟨o₁, ⟨m₁⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N M.X (Sp K) M.s x M.univ
  obtain ⟨P⟩ := hPE p D R b N hN hNp M r w j (p ^ e) T (Sp K) x (x ≫ M.s) rfl o₁ m₁ y hy
  obtain ⟨P'⟩ := hPE p D R b N hN hNp M r w j (p ^ e) T (Sp K) x (x ≫ M.s) rfl o₁ m₁ y' hy'
  have hc : ∃ e', p ^ e = p ^ e' ∧ (0 < j → 0 < e') := ⟨e, rfl, he⟩
  have k1 := half_ker hPR hPK hN hNp hm hw hu hj hc T hpK x y y' hy hy' (fun g hg h => (hK g hg).1 h) m₁ P P'
  have k2 := half_ker hPR hPK hN hNp hm hw hu hj hc T hpK x y' y hy' hy (fun g hg h => (hK g hg).2 h) m₁ P' P
  have hker : ∀ (U : Over (Sp K)) (g : U ⟶ o₁.A), g ≫ P.ψ = 1 ↔ g ≫ P'.ψ = 1 := by
    intro U g
    constructor
    · exact hKU p D R b N r w hw.ne_top hu K (x ≫ M.s) (p ^ e) o₁ P.o' P'.o' P.ψ P'.ψ P.isog P'.isog
        (fun U g => ⟨k1 U g, k2 U g⟩) U g
    · exact hKU p D R b N r w hw.ne_top hu K (x ≫ M.s) (p ^ e) o₁ P'.o' P.o' P'.ψ P.ψ P'.isog P.isog
        (fun U g => ⟨k2 U g, k1 U g⟩) U g
  obtain ⟨m, hm'⟩ := hIK p D R b N K (x ≫ M.s) (p ^ e) o₁ P.o' P'.o' P.ψ P'.ψ P.isog P'.isog hker
  obtain ⟨m'', hm''⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m P'.m'
  have hU := T.univ (Sp K) x o₁ P.o' m₁ P.ψ hpK P.isog P.tj
  have fix : ∀ (f : Sp K ⟶ T.Y) (_ : f = y') (n : GlobalTheory.UPel.HT.ObjMap P.o' T.o' f),
      ∃ n' : GlobalTheory.UPel.HT.ObjMap P.o' T.o' y', n'.φ = n.φ := by
    rintro f rfl n
    exact ⟨n, rfl⟩
  obtain ⟨n', hn'⟩ := fix _ (Category.id_comp y') m''
  refine hU.unique ⟨hy, P.m₀, P.m', P.sq⟩ ⟨hy', P'.m₀, n', ?_⟩
  rw [hn', hm'', ← Category.assoc, hm', P'.sq]
