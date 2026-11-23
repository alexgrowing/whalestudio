import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignThird
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TranslateSumVacuumMovedByAdelicPairStatement
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

namespace GlobalTheory.SingleDatum.ShortSum
open GlobalTheory.AdTh.ShortSeries

set_option maxHeartbeats 1000000 in

theorem thetaKO_transSum_eq_short_series : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW s f₀ → ∀ (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)), LatEmb W ι → (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (l₂ : Geo.Tor.Level H) (e : AE D), IsHalfIdem l₂ e → ∀ (r g q0 : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (hq : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x₀ : Frame X.Ψ r) (vr : Harm.Var X.Ψ q0 X.p0 (Fin V.rank) ≃ FVar D W.rank V.rank) (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsMod W hr X → IsSympl X bas → IsONFr X x₀ → IsInvOf W hr X x₀ s → IsBasOf W hr X hq x₀ BW → IsVarOf V W X q0 vr → ∀ (bad N : ℕ) (h : GA D V) (k : GA D W) (Λ : GenLat D.host.E V.rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) (e' : AE D) (Ps : Finset (Formalism.L2.DIV.Pl D.host.E)) (y : (AE D)ˣ), l₂.M ∣ bad → IsIdemSum e' Ps → (∀ PP ∈ Ps, ((bad : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → h ∈ GfC V → SuppAt e' V h → IsDetAt e' V h y → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat V (finPt V h)) → Λ.TrivAt l₂.M → Λ.LevOK N l₂.M → MarkAd l₂ W hr ι k mk → ∀ Y : (Fin V.rank → LevQ Dw l₂) → Matrix (Fin V.rank) (Fin r) D.host.E, IsRoots l₂ (latR hr (latG W k)) mk N Y → ∀ (v : TF V.rank g) (a : ℂ), IsVac X bas (H.w0 : D.host.E) (tens (stdL D.host.E V.rank) (latR hr (latG W k))) v → Reads θ V W hr X bas idx (om (1, k) f₀) (a • v) (frMove θ W hr X k x₀) → ∀ (w : (Fin V.rank → LevQ Dw l₂) → ℂ) (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin V.rank)) (d : ℕ), P.IsHomogeneous d → thetaKO om h k (pureTensorO ψ θ V W (fun _ => 1) s (fun _ => 1) BW (transSum ψ V W l₂ ι e f₀ w) (MvPolynomial.rename vr P)) = (-1) ^ d * ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ)⁻¹ ^ d * a * (((χW y : Circle) : ℂ)⁻¹ * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E V.rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ r) : ℂ)) * ((Nat.card (Fin V.rank → LevQ Dw l₂) : ℂ))⁻¹ * thP X hq bas idx (gphi X bas (H.w0 : D.host.E) Λ.La (latR hr (latG W k)) v w Y) P (frMove θ W hr X k x₀) := by
  intro D H Dw ψ θ V W χV χW om ΛV ΛW s f₀ hVP ι hι hrt l₂ e he r g q0 hr X hq bas idx x₀ vr BW hM hS hx hinv hbas hvr
    bad N h k Λ mk e' Ps y hbad he' hPs hh hsupp hdet hΛ htriv hlev hmk Y hY v a hv hR w P d hd
  choose p hp using fun q => exists_finOf V W hr (Y q)
  obtain ⟨hthP, hdat⟩ := GlobalTheory.T.translateSum_vacuum_moved_by_adelicPair D H Dw ψ θ V W χV χW om ΛV ΛW s f₀ hVP
    ι hι l₂ e he r hr bad N h k Λ mk hbad ⟨hh, e', Ps, he', hPs, hsupp⟩ hΛ htriv hlev hmk Y (fun q => (p q).1)
    (fun q => (p q).2) hY hp w
  obtain ⟨hP, -, hV0, hW0, hVs, hWs, hVstd, -, hvac⟩ := hVP
  have hψ := hP.weil.std
  haveI := finite_levQ Dw l₂
  letI : Fintype (Fin V.rank → LevQ Dw l₂) := Fintype.ofFinite _
  obtain ⟨hhs, hks, -, hlat, hV1, -⟩ := GlobalTheory.MovedLat.moved_lattices D _ _ _ _ hV0 hW0 hVs hWs h k
  obtain ⟨-, -, hmv, -⟩ := GlobalTheory.MovedLat.moved_lattices D _ _ _ _ hV0 hW0 hVs hWs 1 k
  rw [show fin V 1 = 1 from map_one _, hV1] at hmv
  have hx' := isONFr_move hψ hP.inf hP.std hP.even hr X bas idx hM hS hx k
  have hvac' := GlobalTheory.WeilVacMove.isVacO_om D _ _ _ _ _ _ _ hP.weil hP.inf (fun _ => 1) (fun _ => 1) _
    (fun τ => compAt θ τ (Formalism.L2.Theta.mt _ k) * s τ * compAt θ τ (Formalism.L2.Theta.mt _ k⁻¹))
    _ _ _ _ 1 k (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.mul_assoc, GlobalTheory.WeilVacMove.compAt_mt_inv_mul, Matrix.mul_one]) hmv _ hvac
  have hL : ∀ L₀ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E),
      L₀ = Submodule.span (𝓞 D.host.E)
        {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ Bridge.hLat W (fin W k), w = a • v} →
      latR hr (latG W k) = latR hr L₀ := fun L₀ h₀ => by rw [h₀, hlat]
  have hcl := GlobalTheory.T.weilRepresentation_split_support_projects_vacuum D _ _ _ _ _ _ _ hP _ g hr X bas idx hM hS H hrt _ _ Λ.La _ hV0 hVs hks hVstd hL _ _ hx'
    (isInvOf_move hr X hinv k) _ hvac' _ hR e' Ps h y he' hsupp hdet hΛ
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul, projA_smul, smul_smul] at hcl
  obtain ⟨-, hsd, huni, hfg⟩ := LatOf.isLatOf_tens D _ _ _ _ _ g hr X bas idx hψ hP.inf hP.std hP.even hM hS
    _ _ Λ.La _ hhs hks hΛ hL
  obtain ⟨hth, hsum⟩ := reads_sum hψ hP.inf hP.std hP.even hr X bas idx hM hS hx'
    (hP.weil.om_pres (h, k) _ hvac.2.theta) hcl w (fun q => (p q).1) (fun q => (p q).2) (fun q => (hp q).2)
    Finset.univ
  rw [finsum_eq_sum_of_fintype] at hdat
  have hrd := (reads_linear_injective D _ _ _ _ _ g hr X bas idx hψ hP.inf hP.std hP.even hM hS _ hx'
    _ _ _ _ hsum hsum).1 ((Nat.card (Fin V.rank → LevQ Dw l₂) : ℂ))⁻¹ 0
  rw [zero_smul, zero_smul, add_zero, add_zero, ← hdat] at hrd
  simp only [heisG_smul, (hp _).1] at hrd
  simp only [smul_comm (w _)] at hrd
  rw [← Finset.smul_sum, smul_smul, ← finsum_eq_sum_of_fintype] at hrd
  rw [kernel_of_reads hP hr X bas idx hM hS hq hx hinv hbas hvr hh k hthP hrd P d hd,
    theta_smul₂ idx hS hP.even hq hx'.mem_dom _ _ hrd.1]
  have hpar := Parity.thP_gphi_neg _ _ g _ X bas idx hS hP.even q0 hq (H.w0 : D.host.E) H.w0.isIntegral_coe (cmHost_idempotent_trace_eq_one H)
    _ hsd v hv Λ huni hfg _ w Y P d hd _ hx'.mem_dom
  unfold gphi at hpar ⊢
  rw [hpar]
  push_cast
  ring
end GlobalTheory.SingleDatum.ShortSum
