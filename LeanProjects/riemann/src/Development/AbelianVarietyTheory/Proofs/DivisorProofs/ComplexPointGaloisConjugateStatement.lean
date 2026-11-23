import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointGaloisConjugate
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_point_galois_conjugate : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (𝔠 : FracId (FR E)) (φ : I → E →+* ℂ)
    (L L' : Set E) (T : CxPt 𝔠 φ L) (R : Type) [CommRing R] (σ : R →+* ℂ) (X₀ : Obj (FR E) 𝔠 (Sp R)) (δ₀ : X₀.DetGen)
    (N : I → Module.End R (HdR X₀.A)), T.IsOver σ X₀ δ₀ N →
    ∀ (g : ℂ ≃+* ℂ) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left)
      (U' : Unif (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) L' 0 X') (κ : ℂ),
      X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p → κ ≠ 0 → U'.e = T.U.e → U'.c = T.U.c →
      (∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : epsR ℂ ⟶ T.X.A) (v' : epsR ℂ ⟶ X'.A),
        v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → T.U.u.IsDiff w v →
          U'.u.IsDiff (fun j ↦ κ * g (w j)) v') →
      (∀ (a : E) (α : T.X.A ⟶ T.X.A) [IsMonHom α] (α' : X'.A ⟶ X'.A) [IsMonHom α'], α'.left ≫ p = p ≫ α.left →
        (∀ w, U'.u.ex (fun j ↦ g (φ (U'.e j) a) * w j) = U'.u.ex w ≫ α') →
          ∀ w, T.U.u.ex (fun j ↦ φ (T.U.e j) a * w j) = T.U.u.ex w ≫ α) →
      ∃ T' : CxPt 𝔠 (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) L', T'.IsOver ((g : ℂ →+* ℂ).comp σ) X₀ δ₀ N ∧
        T'.C * κ ^ Fintype.card I = g T.C ∧
        ∀ i, T'.U.h i = U'.h i ∧ T'.s i * T'.w i ^ 2 = κ ^ 2 * g (T.s i * T.w i ^ 2) := by
  first | exact @GlobalTheory.ConjTransport.exists_conj_point | exact GlobalTheory.ConjTransport.exists_conj_point | (intros; apply GlobalTheory.ConjTransport.exists_conj_point <;> assumption)
