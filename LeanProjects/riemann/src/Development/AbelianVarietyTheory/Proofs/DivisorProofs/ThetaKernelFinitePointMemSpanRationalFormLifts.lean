import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesFourth
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPresExtMemExtBijIsom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaLevelVPCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelTensorValues

open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KernelSpanCore

open GlobalTheory.KernelSpan

set_option maxHeartbeats 1000000 in

theorem kernel_mem_span_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ h ∈ GfC (Vc D i), ∀ (w : (R.cV i).W) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (fun g : GA D (Wc D i) => thetaKO (R.ωP i t) h g (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) w))) ∈ Submodule.span ℂ (Set.range fun x₀ : A.fam.amb.FL i t => (R.thF i t (jVx R i t x₀) (fun ρ => u ρ) : GA D (Wc D i) → ℂ)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i t hV h hh w u
  refine (hR.thP.thF i t).elim fun thP hPF => ?_
  refine (GlobalTheory.SplitReps.exists_bad R t one_pos).elim fun bad hbad => ?_
  refine (GlobalTheory.SplitReps.exists_split_system R i t le_rfl (by simp) hbad.1
    (fun k _ hk => GlobalTheory.SplitReps.fin_mem_levJ R i (hR.lev.βV i) t hbad.2.2 k hk) one_pos).elim fun m hm =>
    hm.elim fun ys hys => ?_
  have hfin : ∀ k ∈ GfC (Vc D i), ∀ hk : fin (Vc D i) k ∈ levJ R i t, ∀ P, R.ωP i t (k, 1) (R.ptP i t P) =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • R.ptP i t P := fun k hk hk' =>
    GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) hR.models.inf
      (hR.thP.ωP i t) _ _ _ _ _ (hR.thP.pt_theta i t) k hk 1 (one_mem _) _
      (GlobalTheory.AdTh.LevelLawCore.omega_level_vP_core D G Pl0 T0 A Ks R F hR i t k hV hk hk')
  have key := exists_integral (hR.thP.ωP i t) (D.sp.V_sig _) (hR.models.vpos i) (R.cV i) (hR.models.cV i) (R.βV i)
    (R.datVt i t) (fun _ => Iff.rfl)
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i t) ∘ₗ R.ioP i (PiTensorProduct.tprod ℂ u)) (fun w => hR.thP.pt_theta i t _)
    (fun a ha w => (hR.thP.ioP i t).1 a ha _ w) (fun k hk hk' w => hfin k hk hk' _)
    (hR.models.νV i t) (Fin m) ys hys.2.1 hys.2.2 (fun k => (hys.1 k).1) hh w
  refine key.elim fun f hf => hf.2.elim fun a ha => ?_
  have hr := (hR.models.HV i t).2.1
  have hf' : f ∈ LinearMap.range (R.HV i t).e := hr.ge hf.1
  refine hf'.elim fun y hy => ?_
  have h0 : (R.B.L i t).pres.ExtBij := (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.L i t).pres).2.1
  have he : ∀ x, (R.HV i t).e (jVx R i t x) = (R.B.L i t).pres.extL x := hR.models.jV i t
  have hsp : Submodule.span ℂ (Set.range (jVx R i t)) = ⊤ :=
    span_eq_top_of_model (R.HV i t).e (hR.models.HV i t).1 (jVx R i t) _ he (h0.2.trans hr.symm)
  let T : (R.HV i t).H →ₗ[ℂ] (GA D (Wc D i) → ℂ) :=
    { toFun := fun y => R.thF i t y (fun ρ => u ρ)
      map_add' := fun y y' => by rw [map_add]; rfl
      map_smul' := fun c y => by rw [map_smul]; rfl }
  refine mem_span_of_linear (jVx R i t) hsp T y a ha.1 _ (funext fun g => ?_)
  have h1 := congrFun (hPF.2 y u) g
  have h2 := hPF.1.eq ((R.extV i t).rangeRestrict y) (PiTensorProduct.tprod ℂ u) g
  have h3 := ha.2 g
  rw [← hy] at h3
  exact h1.trans (h2.trans (Eq.trans rfl h3))

end GlobalTheory.KernelSpanCore
