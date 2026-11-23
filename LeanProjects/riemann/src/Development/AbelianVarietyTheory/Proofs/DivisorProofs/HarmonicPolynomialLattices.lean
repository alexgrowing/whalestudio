import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLatticeBaseChangeSpanProof
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockMinorProductEqSignDualWeylExtremalVector
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicValueSpaceMapEqDualWeylModuleFunctio
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolynomialEqZeroOfFunction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicLatticeFgAndSpansValueSpace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapVVSymmMapVV
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain
open NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links (PolF labLL)
open Formalism.L2.Host (embLL0)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmallSpan

variable {D : D7} {m n : ℕ}

open GlobalTheory.ExportSeries.Onto in

theorem exists_harm (w : Weight D n) (B : GLR D n) (hw : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m) (F : VV ℂ w.lam) :
    ∃ P ∈ harm m w B, harmFn m w B P = coefFn (RingHom.id ℂ) w.lam (F : Pol ℂ D.what₂.Tau n) := by
  obtain ⟨s, hs⟩ := GlobalTheory.ExportSeries.DeltaExtremal.harmFn_delta D m n w B hw hm
  have hs0 : ((s : ℤ) : ℂ) ≠ 0 := by exact_mod_cast s.ne_zero
  have key : ∀ u : GLR D n, harmFn m w B (fockGL m w B u (w.delta m)) =
      ((s : ℤ) : ℂ) • coefLin w.lam (actP w.lam (invTrK (u * B)) (ten fun τ => extremal ℂ n (w.lam τ))) := fun u => by
    funext x
    rw [harmFn_fockGL, hs, Pi.smul_apply, smul_eq_mul]
    congr 1
    change _ = coefFn _ _ _ _
    rw [coefFn_actP, _root_.mul_inv_rev, mul_assoc]
  have hle : (VV ℂ w.lam).map (coefLin w.lam) ≤ (harm m w B).map (harmFn m w B) := by
    rw [GlobalTheory.OrbitSpan.VV_eq_span_orbit, harm, Submodule.map_span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    have h2 := key (invTrK g * B⁻¹)
    rw [inv_mul_cancel_right, invTrK_invTrK] at h2
    refine (Submodule.smul_mem_iff _ hs0).1 ?_
    beta_reduce
    rw [← h2]
    exact Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩
  exact hle (Submodule.mem_map_of_mem F.2)

open GlobalTheory.ExportSeries.HarmLattice in

theorem harmLat_le_span {K₀ K : Type} [Field K₀] [NumberField K₀] [Field K] [NumberField K] (f : K₀ →+* K) (σ : K →+* ℂ)
    (emb : D.what₂.Tau → (D.host.E →+* K₀)) (O O' : Subring ℂ) (hO' : ∀ a : 𝓞 K, σ a ∈ O') (w : Weight D n) (B : GLR D n)
    (hw : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m) {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hM : Submodule.IsLattice D.host.E M) {P : PolF D m n} (hP : P ∈ harmLat σ (fun τ => f.comp (emb τ)) O' m w B M) :
    P ∈ Submodule.span O' (harmLat (σ.comp f) emb O m w B M : Set (PolF D m n)) := by
  set N := Submodule.span O' (harmLat (σ.comp f) emb O m w B M : Set (PolF D m n))
  have hN : N ≤ (harm m w B).restrictScalars O' := Submodule.span_le.2 fun Q hQ => hQ.1
  have hle : coefLatFn σ (fun τ => f.comp (emb τ)) O' w.lam M ≤ N.map ((harmFn m w B).restrictScalars O') := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨F, hF, rfl⟩
    have hF' := GlobalTheory.NabBC.nabBaseChange _ _ _ _ n f emb w.lam M hM hF
    rw [coefFn_eq, SetLike.mem_coe]
    clear hF
    induction hF' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, e⟩ := hy
      obtain ⟨Q, hQ, eQ⟩ := exists_harm w B hw hm (GlobalTheory.CoefModel.mapVV (σ.comp f) w.lam x)
      have e1 : harmFn m w B Q = coefFn (σ.comp f) w.lam (x : Pol K₀ D.what₂.Tau n) := eQ.trans (coefFn_eq _ _ x).symm
      refine ⟨Q, Submodule.subset_span ⟨hQ, ?_⟩, ?_⟩
      · exact Submodule.subset_span ⟨x, hx, e1⟩
      · refine eQ.trans (congrArg (cf w.lam) (Subtype.ext ?_))
        change MvPolynomial.map (σ.comp f) x.1 = MvPolynomial.map σ y.1
        rw [e, MvPolynomial.map_map]
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add _ _ _ _ h1 h2 => rw [map_add, map_add]; exact add_mem h1 h2
    | smul a F _ h1 =>
      rw [← algebraMap_smul K a F, LinearMap.map_smulₛₗ, map_smul]
      exact Submodule.smul_mem _ (⟨σ a, hO' a⟩ : O') h1
  obtain ⟨Q, hQ, e⟩ := hle hP.2
  have h0 : P - Q = 0 := GlobalTheory.ExportSeries.HarmInj.harm_inj D m n w B hw hm _ (sub_mem hP.1 (hN hQ)) (by
    rw [map_sub, sub_eq_zero]
    exact e.symm)
  rw [sub_eq_zero.1 h0]
  exact hQ

theorem isLattice_latAt {S T : HSp D} {B : Base S T} (hF : B.F.Good) (h : Bridge.Gf S) :
    Submodule.IsLattice D.host.E (B.latAt h) :=
  Formalism.UG.P.global_lattice_isLattice_holds _ _ _ _ (Module.Finite.iff_fg.2 hF.sdS.1.fg) hF.sdS.1.span_eq_top _

theorem smallSt : GlobalTheory.BigOn.Exp.TupLe.SmallSt := by
  intro D _ _ _ _ _ _ _ _ _ p j _ _ B hB _ O O' _ hO' h P hP
  exact harmLat_le_span D.LL0.val.toRingHom D.what₂.embLL (labLL0 D) O O' hO'.int B.w B.F.BS hB.wt
    (GlobalTheory.CoefLatConj.pq_le hB) (isLattice_latAt hB.frame _) hP

end GlobalTheory.SmallSpan

end
