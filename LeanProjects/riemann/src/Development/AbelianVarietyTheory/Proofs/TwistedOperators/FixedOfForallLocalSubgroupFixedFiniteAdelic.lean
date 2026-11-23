import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralMulRightOfCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelFamOfNotMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryClosureLocalComponentsOpen
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

noncomputable section

namespace GlobalTheory.TrIdem

theorem fixed_of_forall_finLoc_mem : ∀ (D : D7) (V : HSp D) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → ∀ (K' : ∀ v, Subgroup (GLoc D.sp.cm.sig V.gram v)), (∀ v, K' v ≤ Kv V v) → ∀ x : W, (∀ v, ∀ k ∈ K' v, σ (locFin V v k) x = x) → ∀ g : GfC V, (∀ v, finLoc V v g ∈ K' v) → σ g x = x := by
  intro D V W _ _ σ hσ K' hK' x hx g hg
  have fl_self : ∀ a (y : GLoc D.sp.cm.sig V.gram a), finLoc V a (locFin V a y) = y :=
    fun a y => proj_emb_self _ _ a y
  have fl_ne : ∀ v a, v ≠ a → ∀ (y : GLoc D.sp.cm.sig V.gram a), finLoc V v (locFin V a y) = 1 :=
    fun v a h y => proj_emb_ne _ _ h y
  let St : Subgroup (GfC V) :=
    { carrier := {k | σ k x = x}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have e : σ a⁻¹ (σ a x) = x := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rwa [ha] at e }
  have hSt : IsOpen (St : Set (GfC V)) := hσ x
  let U : Subgroup (GA D V) := St.comap (toFin V)
  have hU : IsOpen (U : Set (GA D V)) := hSt.preimage (continuous_toFin V)
  obtain ⟨S, hS⟩ := GlobalTheory.PlaceGen.exists_levelOff_le D.sp.cm.sig V.gram (frameLat V) U hU
  have key : ∀ k : GfC V, (∀ v ∈ S, finLoc V v k = 1) → (∀ v, v ∉ S → finLoc V v k ∈ Kv V v) → σ k x = x := by
    intro k h1 h2
    have hk : (k : GA D V) ∈ levelOff D.sp.cm.sig V.gram (frameLat V) S := mem_levelOff.2 ⟨k.2, h1, h2⟩
    have h := hS hk
    have e : toFin V (k : GA D V) = k := toFin_coe k
    change σ (toFin V (k : GA D V)) x = x at h
    rwa [e] at h
  have step : ∀ T : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ k : GfC V, (∀ v, finLoc V v k ∈ K' v) →
      (∀ v ∈ S, v ∉ T → finLoc V v k = 1) → σ k x = x := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro k hk h1
      exact key k (fun v hv => h1 v hv (Finset.notMem_empty v)) (fun v _ => hK' v (hk v))
    | insert a T ha ih =>
      intro k hk h1
      set k' := locFin V a (finLoc V a k)⁻¹ * k with hk'
      have hfix : σ k' x = x := by
        refine ih k' (fun v => ?_) (fun v hv hvT => ?_)
        · by_cases h : v = a
          · subst h
            simp [k', map_mul, fl_self]
          · simp only [k', map_mul, fl_ne v a h, one_mul]
            exact hk v
        · by_cases h : v = a
          · subst h
            simp [k', map_mul, fl_self]
          · simp only [k', map_mul, fl_ne v a h, one_mul]
            exact h1 v hv (by simp [h, hvT])
      have hkk : k = locFin V a (finLoc V a k) * k' := by
        simp [k', ← mul_assoc, ← map_mul]
      rw [hkk, map_mul, Module.End.mul_apply, hfix]
      exact hx a _ (hk a)
  exact step S g hg (fun v hv hvS => absurd hv hvS)

end GlobalTheory.TrIdem
