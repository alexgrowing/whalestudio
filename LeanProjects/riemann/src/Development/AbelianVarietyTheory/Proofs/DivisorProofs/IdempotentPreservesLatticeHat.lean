import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.LatLoc

theorem loc_transfer {R : Type} [CommRing R] {n : ℕ} {S : Subring R} (H₀ H₁ : Submodule S (Fin n → R)) (N : ℕ)
    (u : S) (ε : R) (hu : (u : R) * N = ε) (hε : ε * ε = ε) (h : ∀ y ∈ H₀, (N : R) • y ∈ H₁) (z : Fin n → R)
    (hz : (fun a => ε * z a) ∈ H₀) : (fun a => ε * z a) ∈ H₁ := by
  have h1 := H₁.smul_mem u (h _ hz)
  convert h1 using 1
  funext a
  show ε * z a = (u : R) * ((N : R) * (ε * z a))
  rw [← mul_assoc, hu, ← mul_assoc, hε]

set_option maxHeartbeats 800000 in

theorem lamHat_loc : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (PP : Pl D.host.E) (e : Formalism.L2.Theta.AE D), IsBaseFrame V β Λ N → ((N : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → Formalism.L2.NTheta.IsIdemAt e PP → ∀ y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, (y ∈ Formalism.L2.NTheta.LamHat V → (fun a => finPart D e * y a) ∈ Formalism.L2.NTheta.LamHat V) ∧ ((fun a => finPart D e * y a) ∈ Formalism.L2.NTheta.LamHat V ↔ ∀ i, (β⁻¹).val.mulVec (fun a => swapAE D (finPart D e * y a)) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) := by
  intro D V β Λ N PP e hB hN he y
  obtain ⟨hfr, -, -, h01, h10⟩ := hB
  have hee : e * e = e := he.1.1
  have key : ∀ z, z ∈ Formalism.L2.NTheta.LamHat V ↔
      (fun i => swapAE D (z i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.LevSplit.L0sub V) :=
    fun z => GlobalTheory.LevSplit.latHat_iff (GlobalTheory.LevSplit.L0sub V) z
  have hint : ∀ x : 𝓞 D.host.E, x ∉ PP.asIdeal → ∃ u : Formalism.L2.Herm.intAf D.host.F D.host.E,
      (u : EAf D) * GlobalTheory.LevSplit.finSw D (incA D (x : D.host.E)) = GlobalTheory.LevSplit.finSw D e := by
    intro x hx
    have x0 : x ≠ 0 := fun h0 => hx (h0 ▸ PP.asIdeal.zero_mem)
    have hm := GlobalTheory.LevSplit.swapAE_int (not_not.1 fun hn => hx ((he.2 x x0).2 hn))
    refine ⟨⟨_, hm⟩, ?_⟩
    show GlobalTheory.LevSplit.finSw D (e * incA D ((x : D.host.E)⁻¹)) * _ = _
    have : (x : D.host.E) ≠ 0 := by simpa using x0
    rw [← map_mul, mul_assoc, ← map_mul, inv_mul_cancel₀ this, map_one, mul_one]
  obtain ⟨u, hu⟩ := hint N hN
  have hu' : (u : EAf D) * (N : EAf D) = GlobalTheory.LevSplit.finSw D e := by
    rw [← hu]
    congr 1
  obtain ⟨φ, hφ⟩ := hint 1 (fun h => PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h))
  have hφ' : (φ : EAf D) = GlobalTheory.LevSplit.finSw D e := by
    rw [← hφ]
    simp
  have hε : GlobalTheory.LevSplit.finSw D e * GlobalTheory.LevSplit.finSw D e = GlobalTheory.LevSplit.finSw D e := by
    rw [← map_mul, hee]
  have hsw : (fun a => swapAE D (finPart D e * y a)) = fun a => GlobalTheory.LevSplit.finSw D e * swapAE D (y a) :=
    funext fun a => map_mul _ _ _
  have a01 := GlobalTheory.LevSplit.hatL_smul (F := D.host.F) (GlobalTheory.LevSplit.L0sub V) Λ N h01
  have a10 := GlobalTheory.LevSplit.hatL_smul (F := D.host.F) Λ (GlobalTheory.LevSplit.L0sub V) N h10
  constructor
  · intro hy
    refine (key _).2 ?_
    rw [hsw, ← hφ']
    exact Submodule.smul_mem _ φ ((key y).1 hy)
  · refine (key _).trans (Iff.trans ?_ (hfr _))
    rw [hsw]
    exact ⟨loc_transfer _ _ N u _ hu' hε a01 _, loc_transfer _ _ N u _ hu' hε a10 _⟩

end GlobalTheory.LatLoc
