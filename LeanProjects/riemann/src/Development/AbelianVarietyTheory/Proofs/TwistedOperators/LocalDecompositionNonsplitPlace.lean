import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabilizerInertPlace
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.InertIwasawaLoc

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.LFun GlobalTheory.InertIwasawaIso

theorem exists_loc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {c : 𝓞 E} (hc : (c : E) + σ c = 1) {n r : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsLattice E L]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w)
    (hv : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.UnramAt F E v) (hL : IsSelfDualAt σ J L v) {e : Matrix (Fin n) (Fin r) E}
    {p : Matrix (Fin r) (Fin n) E} (hp : p * e = 1) (he : Formalism.UG.cT (σ : E →+* E) e * J * e = 0) (y : GLoc σ J v) :
    ∃ q k : GLoc σ J v, k ∈ stabLoc σ J L v ∧ y = q * k ∧ ∃ β : GL (Fin r) (Fv F v ⊗[F] E),
      (HA.mat (Fv F v) σ J q).1 * e.map (inclR (Fv F v)) = e.map (inclR (Fv F v)) * β.1 := by
  have h := (InertChart.under_eq_iff hw w).2 rfl
  obtain ⟨a, ha⟩ := Frames.exists_isLatticeFrame (F := F) L
  have hN := GlobalTheory.UnramSelfDual.exists_norm v hσ (GlobalTheory.UnramConjUnit.exists_sub_conj_unit _ _ _ hσ v hv)
  have hO : ∀ z, z ∈ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v ↔ z ∈ intLoc F E v := GlobalTheory.StabOrbit.mem_OEv_iff v
  simp only [hO] at hN
  let ι : E →+* Fv F v ⊗[F] E := inclR (Fv F v)
  obtain ⟨k, h1, h2, h3⟩ := exists_stab (intLoc F E v) (w.adicCompletionIntegers E)
    (InertChart.complEquiv hw h) (InertChart.mem_intLoc_iff hw h)
    (σ := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) (fun _ => sigR_mem_intLoc σ) (sigR_invol (InertChart.conj_conj hσ))
    (τ := ι c) (tmul_mem_intLoc (one_mem _) c)
    (by change ι c + ι (σ c) = 1
        rw [← map_add, hc, map_one]) hN
    (J := JR (Fv F v) J) (by ext i j; exact congrArg ι (hJ.1 i j))
    ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_det_JR hJ.2)) (Λ := latLoc F L v)
    (fun y => Submodule.ext_iff.1 hL y) (ha v) (X := e.map ι) (P := p.map ι)
    (by rw [← Matrix.map_mul, hp, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_map (σ : E →+* E) _ ι (fun _ => rfl), show JR (Fv F v) J = J.map ι from rfl,
          ← Matrix.map_mul, ← Matrix.map_mul, he, Matrix.map_zero _ (map_zero _)])
    (g := matHom _ σ J y) y.2
  let κ : GLoc σ J v := ⟨k, h1⟩
  exact ⟨y * κ⁻¹, κ, h2, (inv_mul_cancel_right y κ).symm, h3⟩

end GlobalTheory.InertIwasawaLoc

namespace GlobalTheory.InertIwasawaLoc

open scoped Matrix TensorProduct

theorem eq_mul_stab_of_not_split : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (a : GL (Fin V.rank) (TensorProduct D.host.F (AF D.host.F) D.host.E)), Φ.IsGood D.sp.cm L a → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → ∀ (g : GLoc D.sp.cm.sig V.gram v), ∃ q k : GLoc D.sp.cm.sig V.gram v, k ∈ stabLoc D.sp.cm.sig V.gram L v ∧ g = q * k ∧ ∃ β : GL (Fin (wittIndex V)) (TensorProduct D.host.F (Fv D.host.F v) D.host.E), (HA.mat (F := D.host.F) (Fv D.host.F v) D.sp.cm.sig V.gram q).1 * (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) = (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) * β.1 := by
  intro D V Φ L a hG v hv g
  haveI := hG.1
  have := v.isMaximal
  obtain ⟨P, hP, hPv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
  let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨P, hP.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩
  have h : w.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hPv.over.symm
  have hi := GlobalTheory.LPositivity.split_or_inert D w
  rw [h] at hi
  obtain ⟨c, hc⟩ := D.host.exists_trace_one
  rw [← show D.sp.cm.sig (c : D.host.E) = D.host.conj c from D.host.φ₀.injective
    (((isCMExt_host D).2.2.2 _ _).trans (Formalism.HC.HostAx.conjE_apply _ _ _).symm)] at hc
  have key : ∀ (x y : Fin (wittIndex V) → V.V) (j i : Fin (wittIndex V)),
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (Matrix.of fun z k => V.frame.repr (x k) z) * V.gram *
        Matrix.of fun z k => V.frame.repr (y k) z) j i = V.hD (y i) (x j) := by
    intro x y j i
    have := GlobalTheory.AutFunCompare.hT_col D.sp.cm V (Matrix.of fun z k => V.frame.repr (x k) z) j (y i)
    have e : GlobalTheory.AutFunCompare.vecOf V ((Matrix.of fun z k => V.frame.repr (x k) z)ᵀ j) = x j :=
      V.frame.equivFun.symm_apply_apply (x j)
    rw [e] at this
    change _ = V.hT (x j) (y i)
    rw [this]; rfl
  obtain ⟨q, k, hk, hg, β, hβ⟩ := exists_loc (isCMExt_host D) (c := c) hc (GlobalTheory.Doubling.isHermND_gram V)
    (hi.resolve_left hv)
    ((GlobalTheory.SelfDualLatticeCompare.unram_iff ..).2 fun u hu =>
      haveI := u.isPrime
      GlobalTheory.FinPl.TamePlaces.extUnramAt D v u.asIdeal hu)
    (hG.2.1 v) (e := Matrix.of fun z k => V.frame.repr (Φ.e k) z)
    (p := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (Matrix.of fun z k => V.frame.repr (Φ.f k) z) * V.gram)
    (by ext j i; rw [key, Φ.ef, Matrix.one_apply]; simp only [eq_comm])
    (by ext j i; rw [key, Φ.ee]; rfl) g
  exact ⟨q, k, hk, hg, β, hβ⟩

end GlobalTheory.InertIwasawaLoc

end
