import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EqOfForallAlgClosed
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DatEqOfPhiHat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCuspOfThetaSum

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.ThetaSumDescent

theorem exists_cusp_thetaSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), 1 ≤ r → (∀ σ, GoodEmb c σ → IsUnf (U σ)) → l.A = 1 → ∀ [StarRing (𝓞 E)] (a : (E →+* ℂ) × ℕ → ℕ) (n N : ℕ) (dδ : DeltaDat Xo c n) (La : GenLat E n) (T : Type) [Fintype T] (cs : T → Rul dδ.Xo₂ dδ.c₂) (e : ℕ) (w : T → (Fin n → LevQ Dw dδ.l₂) → c.F) (P : T → MvPolynomial (LtN Dw n) c.F), Dom a n → LastPos Dw a → dδ.IsLev → dδ.l₂.A = 1 → IsNab dδ.Xo₂ dδ.c₂ dδ.nab₂ → La.Unimod → La.TrivAt dδ.l₂.M → La.LevOK N dδ.l₂.M → 0 < e → (∀ t, cs t ∈ sec dδ.Xo₂ dδ.c₂ 0 0 ∧ cs t ^ (e + 1) = cs t) → (∀ t, P t ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → SumInv dδ cs w P → ∃ f ∈ cusp Xo c U a n, (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra dδ.c₂.F k], (∀ x : c.F, algebraMap dδ.c₂.F k (dδ.eF x) = algebraMap c.F k x) → ∀ (y : FrPt Xo c k) (y₂ : FrPt dδ.Xo₂ dδ.c₂ k), FrOver dδ y₂ y → ∃ v : T → k, (∀ t, thLaValAt dδ.Xo₂ dδ.c₂ dδ.nab₂ (fun q => dδ.eF (w t q)) La N (MvPolynomial.map (dδ.eF : c.F →+* dδ.c₂.F) (P t)) y₂ (v t)) ∧ evR Xo c f y = ∑ t, evR dδ.Xo₂ dδ.c₂ (cs t) y₂ * v t) ∧ ∀ f' ∈ sec Xo c a n, (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra dδ.c₂.F k], (∀ x : c.F, algebraMap dδ.c₂.F k (dδ.eF x) = algebraMap c.F k x) → ∀ (y : FrPt Xo c k) (y₂ : FrPt dδ.Xo₂ dδ.c₂ k), FrOver dδ y₂ y → ∃ v : T → k, (∀ t, thLaValAt dδ.Xo₂ dδ.c₂ dδ.nab₂ (fun q => dδ.eF (w t q)) La N (MvPolynomial.map (dδ.eF : c.F →+* dδ.c₂.F) (P t)) y₂ (v t)) ∧ evR Xo c f' y = ∑ t, evR dδ.Xo₂ dδ.c₂ (cs t) y₂ * v t) → f' = f := by
  intro E _ _ _ H Dw l Xo c r U hr hU hA _ a n N d La T _ cs e w P hD hL hlev hA₂ hnab hun hT hO he hcs hP hinv
  obtain ⟨f, hf, hval⟩ := exists_sec_thetaSum d hlev hnab La N hun hT hO a cs w P (fun t => (hcs t).1) hP hinv
  refine ⟨f, ?_, hval, fun f' hf' hval' => ?_⟩
  · rw [← Formalism.L2.PjFree.cusp_ofPj]
    exact mem_cusp_of_thetaSum d (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) hr
      (fun σ hσ => (Formalism.L2.PjFree.isUnf_ofPj (U σ)).2 (hU σ hσ)) hA hlev hA₂ hnab La N hun hT hO a hD hL cs e he w P hcs hP
      f hf hval
  · refine GlobalTheory.ClassSumUnique.sec_eq_of_geometric hf' hf fun k _ _ _ y => ?_
    letI : Algebra d.c₂.F k := ((algebraMap c.F k).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
    have hk : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a := fun a => by
      show algebraMap c.F k (d.eF.symm (d.eF a)) = _
      rw [AlgEquiv.symm_apply_apply]
    obtain ⟨y₂, hy⟩ := hlev.2.2.2.2.2.2.1 k hk y
    obtain ⟨v, hv, e₁⟩ := hval k hk y y₂ hy
    obtain ⟨v', hv', e₂⟩ := hval' k hk y y₂ hy
    rw [e₁, e₂]
    unfold thLaValAt at hv hv'
    exact sum_values_eq d.nab₂ hnab La N hun hT hO a _
      (fun t => (GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a _ (hP t)) _ _ 1 y₂ _ _ _ _ hv hv' fun _ _ => rfl

section Shift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} {A : Type} [AddCommGroup A]

def ShiftTie (d : DeltaDat Xo c n) (cs : A → Rul d.Xo₂ d.c₂) (κ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) → A) : Prop :=
  ∀ (k : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) (s : Sim Dw) (ρ : d.Xo₂.X ≅ d.Xo₂.X), s.InGam l d.l₂ → d.Xo₂.LevAut s ρ →
    (∀ x : Dw.La, (Submodule.Quotient.mk (s.f d.l₂.M x) : LaI Xo c d) = k (Submodule.Quotient.mk x)) →
    ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra d.c₂.F K] (y y' : FrPt d.Xo₂ d.c₂ K), y'.x = y.x ≫ ρ.hom →
      ∀ a, evR d.Xo₂ d.c₂ (cs (a + κ k)) y' = evR d.Xo₂ d.c₂ (cs a) y

def ShiftEq (d : DeltaDat Xo c n) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ)
    (κ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) → A) (φ : A → (Fin n → LevQc Dw d.l₂) → c.F) : Prop :=
  ∀ (k : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) (σq : LevQ Dw d.l₂ ≃ₗ[𝓞 E] LevQ Dw d.l₂)
    (σc : LevQc Dw d.l₂ ≃ₗ[𝓞 E] LevQc Dw d.l₂),
    (∀ x y : Dw.La, σq (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
      x - y ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ∧ k (Submodule.Quotient.mk x) = Submodule.Quotient.mk y) →
    (∀ (x : LevQc Dw d.l₂) (q : LevQ Dw d.l₂), (d.l₂.M : ℤ) ∣
      Dw.EF (qRep (σc x)) (cSep d.l₂ • levRep (σq q)) - Dw.EF (qRep x) (cSep d.l₂ • levRep q)) →
    ∀ a x, φ a (fun b => σc.symm (x b)) = (((ψ k)⁻¹ : c.Fˣ) : c.F) * φ (a + κ k) x

end Shift

section Marks

open ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Member
open scoped TensorProduct

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} {A : Type} [AddCommGroup A] [DecidableEq A]

end Marks

end GlobalTheory.ThetaSumDescent
