import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalPointTorusExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalPointTorusExtensionAddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalPointZeroAndPeriodStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem exists_qkPt_tautPt : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → (∀ i, s i ≠ 0) → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (a : Fin T.r → ℤ), ∃ p : QkPt D F n, p.y = e.symm a ∧ TautPt T ω s ε n D e β ββ w F a p.g := by
  intro o W _ _ _ T I _ ε n V _ _ D ω s e β ββ w hB hF hs F _ _ a
  have hex := fun b => GlobalTheory.T.exists_tautological_point_torus_extension T ε n V D ω s e β ββ w hB hF hs F b
  let f : (Fin T.r → ℤ) → GtPtF D F := fun b => Classical.choose (hex b)
  have hf : ∀ b, TautPt T ω s ε n D e β ββ w F b (f b) := fun b => Classical.choose_spec (hex b)
  have hadd := GlobalTheory.T.tautological_point_torus_extension_add T ε n V D ω s e β ββ w hB hF F
  have hzi := GlobalTheory.T.tautologicalPoint_zero_and_period T ε n V D ω s e β ββ w hB hF F
  refine ⟨⟨e.symm a, f a, ⟨f (((n : ℕ) : ℤ) • a), ?_, ?_⟩⟩, rfl, hf a⟩
  · refine ⟨fun i => f (((i : ℕ) : ℤ) • a), ?_, ?_, rfl⟩
    · apply (hzi _).1
      have h0 : (((0 : Fin (n + 1)) : ℕ) : ℤ) • a = 0 := by simp
      dsimp only
      rw [h0]
      exact hf 0
    · intro i
      have h1 : ((i.succ : ℕ) : ℤ) • a = ((i.castSucc : ℕ) : ℤ) • a + a := by
        simp [add_smul]
      have h3 := hf (((i.succ : ℕ) : ℤ) • a)
      rw [h1] at h3
      have := hadd _ _ _ _ _ (hf (((i.castSucc : ℕ) : ℤ) • a)) (hf a) h3
      simpa only [h1] using this
  · apply (hzi _).2
    rw [e.apply_symm_apply]
    exact hf _

end GlobalTheory.TInj
