import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniversalFrameRingSubalgebraEqTopStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniversalFrameTestRingStatement

noncomputable section

namespace GlobalTheory.HolEval

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

section Ring

variable {K : Type} [Field K] {σ : K →+* ℂ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {A : Type} [CommRing A] [Algebra K A]

theorem toC_mul (x y : CAt σ) : toC (x * y) = toC x * toC y := rfl
theorem toC_add (x y : CAt σ) : toC (x + y) = toC x + toC y := rfl
theorem toC_one : toC (1 : CAt σ) = 1 := rfl

def holSub (B : Set V) (k : V → (A →ₐ[K] CAt σ)) : Subalgebra K A where
  carrier := {t | DifferentiableOn ℂ (fun b => toC (k b t)) B}
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq, map_mul, toC_mul] at *
    exact hx.mul hy
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq, map_add, toC_add] at *
    exact hx.add hy
  algebraMap_mem' := fun r => by
    simp only [Set.mem_setOf_eq, AlgHom.commutes]
    exact differentiableOn_const _

theorem mem_holSub {B : Set V} {k : V → (A →ₐ[K] CAt σ)} {t : A} :
    t ∈ holSub B k ↔ DifferentiableOn ℂ (fun b => toC (k b t)) B := Iff.rfl

theorem inv_mem_holSub {B : Set V} {k : V → (A →ₐ[K] CAt σ)} {d x : A} (hx : x ∈ holSub B k)
    (h : d * x = 1) : d ∈ holSub B k := by
  rw [mem_holSub] at hx ⊢
  have key : ∀ b, toC (k b d) * toC (k b x) = 1 := fun b => by
    rw [← toC_mul, ← map_mul, h, map_one, toC_one]
  have hne : ∀ b, toC (k b x) ≠ 0 := fun b hb => by
    have h1 := key b
    rw [hb, mul_zero] at h1
    exact zero_ne_one h1
  have heq : (fun b => toC (k b d)) = fun b => (toC (k b x))⁻¹ :=
    funext fun b => eq_inv_of_mul_eq_one_left (key b)
  rw [heq]
  exact hx.inv fun b _ => hne b

theorem det_mem {n : ℕ} (A' : Subalgebra K A) (X : Matrix (Fin n) (Fin n) A) (h : ∀ i j, X i j ∈ A') :
    X.det ∈ A' := by
  rw [Matrix.det_apply]
  refine sum_mem fun e _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem fun i _ => h _ _) _

private theorem evR_eq_of_frMap {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (hS : Out.SecBaseChangeSt) {w : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c w n)
    {S : Type} [CommRing S] [Algebra c.F S] (q : TRing c.F) (κ : q.R →ₐ[c.F] S) (u : FrPt Xo c q.R)
    (x : FrPt Xo c S) (h : FrMap κ u x) : evR Xo c f x = κ (f q u) := by
  have hW := (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS E H Dw l Xo c).2.2.1
  unfold sec secW at hf
  obtain ⟨hn, -⟩ := hf
  unfold evR evalAt
  split_ifs with hT
  · exact hW f hn S _ q _ κ _ u x hT.choose_spec.choose_spec.choose_spec h
  · exact absurd ⟨q, κ, u, h⟩ hT

end Ring

theorem differentiableOn_evR : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (B : Set V) (p : TRing c.F) (y₀ : FrPt Xo c p.R) (ψ : V → (p.R →ₐ[c.F] CAt σ)) (z y : V → FrPt Xo c (CAt σ)) (G : V → (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ))) (a : V → CAt σ), (∀ b ∈ B, FrMap (ψ b) y₀ (z b) ∧ FrChg (G b) (a b) (z b) (y b)) → (∀ t, DifferentiableOn ℂ (fun b => toC (ψ b t)) B) → (∀ τ i j, DifferentiableOn ℂ (fun b => toC (G b τ i j)) B) → DifferentiableOn ℂ (fun b => toC (a b)) B → ∀ w n, ∀ f ∈ sec Xo c w n, DifferentiableOn ℂ (fun b => toC (evR Xo c f (y b))) B := by
  intro hS E _ _ _ H Dw l Xo c σ V _ _ B p y₀ ψ z y G a hzy hψ hG ha w n f hf
  obtain ⟨A, π, X, s, u, hU⟩ := GlobalTheory.T.exists_universalFrame_testRing hS E H Dw l Xo c p y₀
  obtain ⟨hFR, u₀, hπ, hch⟩ := hU
  have hk : ∀ b ∈ B, ∃ kk : A.R →ₐ[c.F] CAt σ,
      kk.comp π = ψ b ∧ (∀ τ, (X τ).map kk = G b τ) ∧ kk (s : A.R) = a b := by
    intro b hb
    obtain ⟨-, hc⟩ := hzy b hb
    obtain ⟨hex, huniq⟩ := GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) (z b) (y b)
    obtain ⟨g, a', hdet, hc'⟩ := hex hc.1
    obtain ⟨hg, ha'⟩ := huniq _ _ _ _ hc hc'
    obtain ⟨kk, ⟨h1, h2, h3⟩, -⟩ := hFR.2 (CAt σ) (ψ b) g a' hdet
    exact ⟨kk, h1, fun τ => (h2 τ).trans (congrFun hg τ).symm, h3.trans ha'.symm⟩
  rcases B.eq_empty_or_nonempty with hB | ⟨b₀, hb₀⟩
  · rw [hB]
    exact differentiableOn_empty
  have : Nonempty (A.R →ₐ[c.F] CAt σ) := ⟨(hk b₀ hb₀).choose⟩
  choose! kk hkk using hk
  have hX : ∀ τ i j, X τ i j ∈ holSub B kk := by
    intro τ i j
    rw [mem_holSub]
    refine (hG τ i j).congr fun b hb => ?_
    show toC (kk b (X τ i j)) = toC (G b τ i j)
    rw [← (hkk b hb).2.1 τ]
    rfl
  have hs : (s : A.R) ∈ holSub B kk := by
    rw [mem_holSub]
    refine ha.congr fun b hb => ?_
    show toC (kk b (s : A.R)) = toC (a b)
    rw [(hkk b hb).2.2]
  have hA' := GlobalTheory.T.universalFrameRing_subalgebra_eq_top c.F (E →+* ℂ) (fun τ => Dw.mult τ) p.R A.R π X s hFR (holSub B kk)
    (fun t => by
      rw [mem_holSub]
      refine (hψ t).congr fun b hb => ?_
      show toC (kk b (π t)) = toC (ψ b t)
      rw [← (hkk b hb).1]
      rfl)
    hX hs (inv_mem_holSub hs (Units.inv_mul s))
    (fun τ => by
      obtain ⟨v, hv⟩ := hFR.1 τ
      refine ⟨((v⁻¹ : (A.R)ˣ) : A.R), inv_mem_holSub (det_mem _ (X τ) (hX τ)) ?_, ?_⟩ <;>
        · rw [← hv]
          exact Units.inv_mul v)
  have he : f A u ∈ holSub B kk := by
    rw [hA']
    exact Algebra.mem_top
  rw [mem_holSub] at he
  refine he.congr fun b hb => ?_
  show toC (evR Xo c f (y b)) = toC (kk b (f A u))
  congr 1
  apply evR_eq_of_frMap hS hf A (kk b) u (y b)
  obtain ⟨hm, hc⟩ := hzy b hb
  have hb1 : FrMap (kk b) u₀ (z b) :=
    ((GlobalTheory.framedPoint_baseChange_laws E H Dw l Xo c).2.1 p.R A.R (CAt σ) π (kk b) y₀ u₀ (z b) hπ).2
      (by rw [(hkk b hb).1]; exact hm)
  apply (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c A.R (CAt σ) (kk b) u₀ u (z b) (y b) X s hch hb1).2
  have e1 : (fun τ => (X τ).map (kk b)) = G b := funext (hkk b hb).2.1
  rw [e1, (hkk b hb).2.2]
  exact hc

end GlobalTheory.HolEval
