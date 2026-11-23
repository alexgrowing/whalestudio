import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTransportCmPeriodsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodTransportGaloisConjugateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTransportCmConjugationStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ConjCMPoint

theorem conj_unif : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)),
        ∃ (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left)
          (U' : Unif (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) (lattice c (y * (upIdele K E t)⁻¹)) 0 X'),
          X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p ∧ U'.e = T.U.e ∧ U'.c = T.U.c ∧
          (∀ i, g ((T.U.h i : ℂ) * (Real.sqrt d : ℝ)) = ((modF t : ℝ) : ℂ) * ((U'.h i : ℂ) * (Real.sqrt d : ℝ))) ∧
          (∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : epsR ℂ ⟶ T.X.A) (v' : epsR ℂ ⟶ X'.A),
            v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → T.U.u.IsDiff w v →
              U'.u.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v') ∧
          (∀ (a : E) (α : T.X.A ⟶ T.X.A) [IsMonHom α] (α' : X'.A ⟶ X'.A) [IsMonHom α'], α'.left ≫ p = p ≫ α.left →
            (∀ w, U'.u.ex (fun j ↦ g (φ (U'.e j) a) * w j) = U'.u.ex w ≫ α') →
              ∀ w, T.U.u.ex (fun j ↦ φ (T.U.e j) a * w j) = T.U.u.ex w ≫ α) := by
  intro hPC hDR hDC K _ _ d δ io hK hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E _ _ _ _ I _ φ hcm hφ c y hc 𝔠 T
  obtain ⟨X', p, hp⟩ := (GlobalTheory.RealMult.Obj.pullback_facts (F := FR E) (𝔠 := 𝔠)).1 T.X (spMap (g : ℂ →+* ℂ))
  obtain ⟨u', hlat, htan, htor⟩ := GlobalTheory.T.torsion_transport_cm_periods hPC hDR hDC K d δ io hK hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E I φ hcm hφ c y hc 𝔠 T X' p hp
  obtain ⟨u'', h', hex, ⟨χ, hah⟩, hh⟩ :=
    GlobalTheory.T.torsion_transport_cm_conjugation hPC hDR hDC K d δ io hK hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E I φ hcm hφ c y hc 𝔠 T X' p hp u' hlat htan htor
  have htan'' : ∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : epsR ℂ ⟶ T.X.A) (v' : epsR ℂ ⟶ X'.A),
      v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → T.U.u.IsDiff w v →
        u''.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v' := by
    intro w v v' h1 h2
    have h3 := htan w v v' h1 h2
    unfold HolUnif.IsDiff at h3 ⊢
    rw [hex]
    exact h3
  have hB := GlobalTheory.T.period_transport_galois_conjugate T.X.A X'.A (T.X.diag T.U.c) (X'.diag T.U.c) _ T.U.u u'' g p hp.grp Ω₀ Ω₁ hT.1 hT.2.1 htan''
  let U' : Unif (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) (lattice c (y * (upIdele K E t)⁻¹)) 0 X' :=
    { e := T.U.e, c := T.U.c, pos := T.U.pos, u := u''
      lat := fun w ↦ by rw [← hlat w, ← u''.ker, ← u'.ker, hex]
      act := fun a w ↦ by
        haveI := T.X.rm.hom a
        haveI := X'.rm.hom a
        exact (hB (fun j ↦ φ (T.U.e j) ((a : FR E) : E)) (T.X.rm.act a) (X'.rm.act a) (hp.act a)).1 (T.U.act a) w
      h := h'
      ah := ⟨χ, hah⟩ }
  refine ⟨X', p, U', hp, rfl, rfl, hh, htan'', ?_⟩
  intro a α _ α' _ hαα' H w
  exact (hB (fun j ↦ φ (T.U.e j) a) α α' hαα').2 H w

end GlobalTheory.ConjCMPoint
