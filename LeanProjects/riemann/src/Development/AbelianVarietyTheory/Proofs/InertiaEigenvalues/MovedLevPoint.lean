import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepLatticeStabilizerVacuumEqDetCharSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicMatrixMemLatticeOfColumns
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCHLat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.NakayamaChar
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000

namespace GlobalTheory.SingleDatum.MovedLevel

theorem cSep_mem {D : D7} {H : Geo.Tor.Host D.host.E} (l : Geo.Tor.Level H) :
    cSep l ∈ Mfr l ∧ cSep l - 1 ∈ l.Mb := by
  have hex : ∃ c, c ∈ Mfr l ∧ c - 1 ∈ l.Mb := by
    have : (1 : 𝓞 D.host.E) ∈ l.Mb ⊔ Mfr l := by rw [show l.Mb ⊔ Mfr l = ⊤ from l.coprime]; trivial
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 this
    exact ⟨y, hy, by rw [← hxy, sub_add_cancel_right]; exact neg_mem hx⟩
  unfold cSep; rw [dif_pos hex]; exact hex.choose_spec

theorem finVec_div {D : D7} (W : HSp D) (v : Fin W.rank → D.host.E) (c : D.host.E) :
    finVec W (fun x => v x / c) = ((1 : Af D.host.F) ⊗ₜ[D.host.F] c⁻¹) • finVec W v := by
  funext i
  change (1 : Af D.host.F) ⊗ₜ[D.host.F] (v i / c) = ((1 : Af D.host.F) ⊗ₜ[D.host.F] c⁻¹) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] v i)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, div_eq_inv_mul]

theorem finVec_sub {D : D7} (W : HSp D) (v v' : Fin W.rank → D.host.E) :
    finVec W (v - v') = finVec W v - finVec W v' :=
  funext fun i => TensorProduct.tmul_sub _ _ _

theorem finVec_nsmul {D : D7} (W : HSp D) (n : ℕ) (v : Fin W.rank → D.host.E) :
    finVec W (n • v) = n • finVec W v :=
  funext fun i => by
    change (1 : Af D.host.F) ⊗ₜ[D.host.F] (n • v i) = n • ((1 : Af D.host.F) ⊗ₜ[D.host.F] v i)
    exact TensorProduct.tmul_smul n _ _

theorem inv_smul_nsmul {D : D7} (W : HSp D) (n : ℕ) (hn : (n : D.host.E) ≠ 0)
    (x : Fin W.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    ((1 : Af D.host.F) ⊗ₜ[D.host.F] (n : D.host.E)⁻¹) • (n • x) = x := by
  rw [← Nat.cast_smul_eq_nsmul (Af D.host.F ⊗[D.host.F] D.host.E), smul_smul,
    ← map_natCast (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Af D.host.F ⊗[D.host.F] D.host.E) n,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hn,
    ← Algebra.TensorProduct.one_def, one_smul]

theorem moved_levPoint : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (V W : HSp D) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), V.gram = 1 → (ΛV : Set (Fin V.rank → D.host.E)) = L0c D V → (ΛW : Set (Fin W.rank → D.host.E)) = L0c D W → IsSelfDualC V ΛV → IsSelfDualC W ΛW → (ΛV : Set (Fin V.rank → D.host.E)) = (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) → ∀ (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)), GlobalTheory.Member.IotaOK Dw W ι → ∀ (l₂ : Geo.Tor.Level H) (e : AE D), IsHalfIdem l₂ e → ∀ (u : GA D W) (g : Dw.La →ₗ[𝓞 D.host.E] Dw.La) (σq : LevQ Dw l₂ ≃ LevQ Dw l₂), Induces W l₂ ι u g → (∀ a : Dw.La, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk (g a)) → ∀ q : Fin V.rank → LevQ Dw l₂, ∃ c ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True), IsHalf e c ∧ actO V W 1 u (levPoint V W l₂ ι e q) = levPoint V W l₂ ι e (fun b => σq (q b)) + c := by
  intro D H Dw V W ΛV ΛW hV a1 a2 a3 a4 a5 ι hι l₂ e he u g σq hind hσ q
  obtain ⟨P, hIS, -⟩ := he
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self hIS
  have i1 : finPart D e ∈ intAE D := by
    have := GlobalTheory.AdTh.MovedDatum.idem_div_mem hIS 1 fun PP _ => PP.isPrime.one_notMem
    rwa [show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, inv_one, RingHom.map_one, mul_one] at this
  obtain ⟨-, -, -, -, -, m6⟩ := GlobalTheory.MovedLat.moved_lattices D V W ΛV ΛW a1 a2 a3 a4 1 1
  have hM0 : (l₂.M : D.host.E) ≠ 0 := by
    have : l₂.M ≠ 0 := by have := l₂.three_le; omega
    exact_mod_cast this
  let ρ : (Fin V.rank → LevQ Dw l₂) → Matrix (Fin W.rank) (Fin V.rank) D.host.E := fun q' =>
    Matrix.of fun a b => ι (cSep l₂ • levRep (q' b)) a / (l₂.M : D.host.E)
  have hlev : ∀ q', levPoint V W l₂ ι e q' = e • GlobalTheory.LatVac.finTens 1 (ρ q') := by
    intro q'
    refine GlobalTheory.AdTh.LatOf.eq_of_parts ?_ ?_ <;> ext a b
    · change infPart D (e * _) = infPart D (e * _)
      rw [RingHom.map_mul, RingHom.map_mul, GlobalTheory.PlaceDatum.infPart_idemSum hIS, zero_mul, zero_mul]
    · change finPart D (e * _) = finPart D (e * _)
      rw [RingHom.map_mul, RingHom.map_mul]; rfl
  have hact : ∀ x, actO V W 1 u x = Formalism.L2.Theta.mt W u * x := by
    intro x; rw [actO, inv_one, GlobalTheory.AdelicLatMove.mt_one, Matrix.mul_one]
  set Y : WO V W := Formalism.L2.Theta.mt W u * GlobalTheory.LatVac.finTens 1 (ρ q) -
    GlobalTheory.LatVac.finTens 1 (ρ fun b => σq (q b)) with hYdef
  have hinf : Y.map (infPart D) = 0 := by
    have h1 := GlobalTheory.AdTh.MovedDatum.infPart_moved V W u (ρ q)
    have h2 := GlobalTheory.AdTh.MovedDatum.infPart_finTens (D := D) (ρ fun b => σq (q b))
    ext a b
    have h1' := congrFun (congrFun h1 a) b
    have h2' := congrFun (congrFun h2 a) b
    simp only [Matrix.map_apply, Matrix.zero_apply] at h1' h2'
    simp only [hYdef, Matrix.map_apply, Matrix.sub_apply, Matrix.zero_apply, map_sub, h1', h2', sub_zero]
  have hcols : ∀ b, (fun a => finPart D (Y a b)) ∈ latGHat W 1 := by
    intro b
    have hcol : (fun a => finPart D (Y a b)) = (finHom W u).1 *ᵥ finVec W (fun a => ρ q a b) -
        finVec W (fun a => ρ (fun b => σq (q b)) a b) := by
      rw [← GlobalTheory.AdTh.MovedDatum.finPart_moved V W u (ρ q) b]
      funext a
      simp only [hYdef, Matrix.sub_apply, map_sub, Pi.sub_apply]
      rfl
    rw [hcol]
    set a := cSep l₂ • levRep (q b) with ha_def
    have hc := cSep_mem (D := D) l₂
    have ha : a ∈ Mfr l₂ • (⊤ : Submodule (𝓞 D.host.E) Dw.La) :=
      Submodule.smul_mem_smul hc.1 Submodule.mem_top
    obtain ⟨w, hw, hw'⟩ := hind.2.2 a ha
    have hqa : (Submodule.Quotient.mk a : LevQ Dw l₂) = q b := by
      have hr : (Submodule.Quotient.mk (levRep (q b)) : LevQ Dw l₂) = q b :=
        Classical.choose_spec (Submodule.Quotient.mk_surjective _ (q b))
      rw [← hr]
      refine (Submodule.Quotient.eq _).2 ?_
      have : a - levRep (q b) = (cSep l₂ - 1) • levRep (q b) := by rw [ha_def, sub_smul, one_smul]
      rw [this]
      exact Submodule.smul_mem_smul hc.2 Submodule.mem_top
    have hmk : (Submodule.Quotient.mk (g a) : LevQ Dw l₂) = σq (q b) := by rw [← hσ, hqa]
    have hga : g a ∈ Mfr l₂ • (⊤ : Submodule (𝓞 D.host.E) Dw.La) := by
      rw [ha_def, map_smul]; exact Submodule.smul_mem_smul hc.1 Submodule.mem_top
    obtain ⟨z, hz⟩ := GlobalTheory.AdTh.MovedDatum.sub_sep_mem l₂ (σq (q b)) (g a) hga hmk
    have hι' : ι (cSep l₂ • levRep (σq (q b))) = ι (g a) - l₂.M • ι z := by
      rw [← map_nsmul, ← hz, map_sub, sub_sub_cancel]
    have e1 : (fun x => ρ q x b) = fun x => ι a x / (l₂.M : D.host.E) := rfl
    have e2 : (fun x => ρ (fun b => σq (q b)) x b) = fun x => ι (cSep l₂ • levRep (σq (q b))) x / (l₂.M : D.host.E) := rfl
    rw [e1, e2, finVec_div, finVec_div, hι', finVec_sub, finVec_nsmul, Matrix.mulVec_smul, ← smul_sub,
      sub_sub_eq_add_sub, add_sub_right_comm, hw', ← smul_add, inv_smul_nsmul W _ hM0]
    refine add_mem hw (GlobalTheory.AdTh.MovedDatum.finVec_mem W 1 _ ?_)
    exact (GlobalTheory.Member.IotaOK.emb hι).2 ▸ LinearMap.mem_range_self ι z
  have hY : Y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True := by
    have := GlobalTheory.T.finite_adelic_matrix_mem_lattice_of_columns D V W hV 1 Y hinf hcols
    rwa [show fin W 1 = 1 from map_one _, m6, ← a5] at this
  refine ⟨e • Y, GlobalTheory.LatticeStable.smul_mem_latO D V W _ _ _ e i1 Y hY, ?_, ?_⟩
  · intro i j
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hee]
  · rw [hlev, hlev, hact, Matrix.mul_smul, ← smul_add, add_sub_cancel]

end GlobalTheory.SingleDatum.MovedLevel
