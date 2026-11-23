import Formalism.LocalToGlobal.InertKernelTheory.TranslatesOfInertKernelAtPlace
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FirstKernelLawGlobal
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.K1RepresentativesLTOfDictionary

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.KerInert.KGLt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert.KG

variable {p : ℕ} [Fact p.Prime]

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in

theorem first_kernel_small_of_frame (D : D7) (h5 : 5 ≤ p) (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (g : GL3Theta.G1 p) (hLT : LTIso g)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)
    (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)
    (hAt : GL3Theta.At D cc δ g) (hIn : GL3Theta.InertK D p) (hM : GL3Theta.ModelOverW g.lam g.abelian₂ g.C)
    (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : TaylorLogMetric.IsChi D χ) (hLam : g.abelian₂ = B.tor.abelian₂)
    (hAdm : Formalism.L2.KerInert.RepLt.AdmGLt X hfin D fd) (hCl : Formalism.L2.KerInert.RepRec.ClAway p cl)
    (hXi : Formalism.L2.KerInert.RepRec.XiAway X D Ξ₀) (hSc : Formalism.L2.KerInert.RepLt.ScalGLt X hfin fd χ muT g.lam)
    (hρ : Formalism.L2.KerInert.RepFrame.LamPosG X E D pos g.lam ρ) (hMI : Formalism.L2.KerInert.RepFrame.MInv X fd.frM)
    (hL : Formalism.L2.KerInert.RepLt.FrameLatMapLt X fd.frM hfin D (fun j La _ => fd.kerN j La)
        (fun j _ La' => fd.kerN (j + 1) La') ρ) :
    Formalism.L2.KerInert.RepLt.FirstKernelLawLocalPowerSeries X E hfin (beLT hLT) pos (FrecG E.toCEmb pos fd B χ g.lam SS cl Ξ₀ muT (ltC g hLT)) := by

  let large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E) :=
    fun j La _ => fd.kerN j La
  let Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E) :=
    fun j _ La' => fd.kerN (j + 1) La'
  let Ξ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ :=
    fun j La La' => movD (Ξ₀ j La La') (fd.trG j La) (fd.trG (j + 1) La')
  let G : ∀ j, X.Lt j → X.Lt (j + 1) → TaylorLogMetric.VC D ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ :=
    fun j La La' => kerTh B χ SS cl (large₂ j La La') (Lg' j La La') (Ξ j La La')
  let F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p] :=
    fun j La La' => ((p : ℂ_[p]) ^ expG X j La La') •
      TaylorLogMetric.pSer D g.lam (fun z => scalG fd χ muT j La La' * G j La La' z)
  let Fr : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p] :=
    fun j La La' => Formalism.L2.KerInert.Rep.sclY (ltC g hLT) (F j La La')
  let S := fun j (La : X.Lt j) (La' : X.Lt (j + 1)) => Formalism.L2.KerInert.RepFrame.subGen X E pos fd.frM j La La'
  have hFam : FrecG E.toCEmb pos fd B χ g.lam SS cl Ξ₀ muT (ltC g hLT) =
      fun j La La' => Formalism.MainNotions.FormalGroupSystem.linSub (S j La La') (Fr j La La') := by
    funext j La La'
    have hS : S j La La' = subBG E.toCEmb pos fd j La La' :=
      funext fun x => funext fun y => (subBG_eq E pos fd j La La' x y).symm
    rw [hS]
    exact linSub_scl _ _ _

  have hB : BeProp p (beLT hLT) := Formalism.L2.KerInert.beProp_ofA Formalism.L2.KerInert.inert_facts_first_hold D cc δ p g hLT hAt h5 hIn hM
  have hComb0 : Formalism.L2.KerInert.RepLt.CombAtLt X hfin D large₂ Lg'
      (fun j La La' => TaylorLogMetric.pSer D g.lam (G j La La')) B.tor (B.eNat χ) g.lam :=
    Formalism.L2.KerInert.RepLt.combAtLt_of_dataRec X hfin D B χ SS cl g.lam hcc hδ
      (Formalism.L2.KerInert.AlgTP.algT_of B hcc hδ hχ) large₂ Lg' Ξ
      (Formalism.L2.KerInert.RepRec.dataRec_movD X D cl Ξ₀ (fun j La _ => fd.trG j La) (fun j _ La' => fd.trG (j + 1) La')
        ((Formalism.L2.KerInert.RepRec.dataRec_iff X D cl Ξ₀).2 ⟨hCl, hXi⟩)) hAdm
  have hComb : Formalism.L2.KerInert.RepLt.CombAtLt X hfin D large₂ Lg' F B.tor (B.eNat χ) g.lam :=
    Formalism.L2.KerInert.RepLt.combAtLt_scalar X hfin D large₂ Lg' B.tor (B.eNat χ) g.lam G
      (fun j La La' => scalG fd χ muT j La La') (fun j La La' => expG X j La La') hComb0 hSc
  have hOnb : Formalism.L2.KerInert.RepLt.OnbExLt X hfin D large₂ Lg' :=
    Formalism.L2.KerInert.RepLt.onbExLt_of X hfin D large₂ Lg'
      (Formalism.L2.KerInert.orthBasisExists_of Formalism.L2.KerInert.global_orthonormal_basis_four Formalism.L2.KerInert.weakApprox_of_approx_and_separation) h5 hIn hAdm
  have hTr : Formalism.L2.KerInert.RepLt.LamTraceLt X hfin D large₂ Lg' g.lam :=
    Formalism.L2.KerInert.RepLt.lamTraceLt_of X hfin D large₂ Lg' g.lam
      (Formalism.L2.KerInert.RepLt.rankTieLt_of X hfin D large₂ Lg' hAdm)
      (Formalism.L2.KerInert.RepFrame.colTie_of X hfin D large₂ Lg' (Formalism.L2.KerInert.RepFrame.trace_tau_sum D) g.lam)
  have hFH : Formalism.L2.KerInert.RepLt.FrameHypLt X E hfin D pos large₂ Lg' Fr S g.lam 1 :=
    Formalism.L2.KerInert.RepLt.frameHypLt_of_lat X E hfin D pos large₂ Lg' fd.frM g.lam ρ hOnb hTr hρ
      (Formalism.L2.KerInert.RepFrob.frobTw_of X E h5) hMI (twInt_all X E) hL Fr
  rw [hFam]
  exact Formalism.L2.KerInert.RepLt.K1_representatives_LT_of_dictionary Formalism.L2.KerInert.Rep.curve_dictionary Formalism.L2.KerInert.kernels_integral_inert D h5 X E
    hfin hLT cc δ hAt hIn hM B hcc hδ χ hχ hIn hLam pos large₂ Lg' F Fr
    (fun j La La' => by simp only [Fr]; rw [ltC_eq]) S hB hComb hFH

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in

theorem first_kernel_small_of_frame_twist (D : D7) (h5 : 5 ≤ p) (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (g : GL3Theta.G1 p) (hLT : LTIso g)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)
    (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)
    (hAt : GL3Theta.At D cc δ g) (hIn : GL3Theta.InertK D p) (hM : GL3Theta.ModelOverW g.lam g.abelian₂ g.C)
    (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : TaylorLogMetric.IsChi D χ) (hLam : g.abelian₂ = B.tor.abelian₂)
    (hAdm : Formalism.L2.KerInert.RepLt.AdmGLt X hfin D fd) (hCl : Formalism.L2.KerInert.RepRec.ClAway p cl)
    (hXi : XiAwayLt X hfin D Ξ₀) (hSc : Formalism.L2.KerInert.RepLt.ScalGLt X hfin fd χ muT g.lam)
    (hρ : Formalism.L2.KerInert.RepFrame.LamPosG X E D pos g.lam ρ) (hMI : Formalism.L2.KerInert.RepFrame.MInv X fd.frM)
    (hL : Formalism.L2.KerInert.RepLt.FrameLatMapLt X fd.frM hfin D (fun j La _ => fd.kerN j La)
        (fun j _ La' => fd.kerN (j + 1) La') ρ) :
    Formalism.L2.KerInert.RepLt.FirstKernelLawLocalPowerSeries X E hfin (beLT hLT) pos (FrecG E.toCEmb pos fd B χ g.lam SS cl Ξ₀ muT (ltC g hLT)) := by
  classical
  let Ξ₁ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ :=
    fun j La La' => if j < X.mm ∧ La ∈ repOf X.Lv hfin j ∧ (X.Pj (j + 1)).IsLatTup La'.2 then Ξ₀ j La La' else fun _ => 0
  have hXi1 : Formalism.L2.KerInert.RepRec.XiAway X D Ξ₁ := by
    obtain ⟨S₀, hp, hS⟩ := hXi
    refine ⟨S₀, hp, fun j La La' y => ?_⟩
    by_cases h : j < X.mm ∧ La ∈ repOf X.Lv hfin j ∧ (X.Pj (j + 1)).IsLatTup La'.2
    · simp only [Ξ₁, if_pos h]
      exact hS j h.1 La h.2.1 La' h.2.2 y
    · simp only [Ξ₁, if_neg h]
      exact IntOff.zero
  have hK := first_kernel_small_of_frame D h5 X E hfin g hLT pos fd cc δ B χ SS cl Ξ₁ muT ρ hAt hIn hM hcc hδ hχ hLam
    hAdm hCl hXi1 hSc hρ hMI hL
  intro j hj L0 h0 La' hLa' φ
  have hEq : thFOf X pos (FrecG E.toCEmb pos fd B χ g.lam SS cl Ξ₁ muT (ltC g hLT)) j L0 La' =
      thFOf X pos (FrecG E.toCEmb pos fd B χ g.lam SS cl Ξ₀ muT (ltC g hLT)) j L0 La' := by
    simp only [thFOf, FrecG, Ξ₁, if_pos (And.intro hj (And.intro h0 hLa'))]
  have := hK j hj L0 h0 La' hLa' φ
  rwa [hEq] at this

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in

theorem first_kernel_law_global_small : TranslatesOfInertKernelAtPlace := by
  intro D p _ h5 X _ E hfin hst g hLT pos fd cc δ B χ lam SS cl Ξ₀ muT ρ hAt hIn hM hcc hδ hχ hlam hLam hAdm hCl hXi hSc
    hρ hMI hL
  subst hlam
  have hK := first_kernel_small_of_frame_twist D h5 X E hfin g hLT pos fd cc δ B χ SS cl Ξ₀ muT ρ hAt hIn hM hcc hδ hχ hLam hAdm hCl hXi hSc
    hρ hMI hL
  have h2b := (Formalism.L2.PairingIndexBounds.PowerSeriesNecessity.adm_two_pendant_iff_representative D X E hfin hst hLT pos _).2 hK
  exact ⟨Formalism.L2.KerInert.admissible_second_of_variant D X E hfin hst hLT pos _ h2b, h2b,
    Formalism.L2.KerInert.admissible_third_of_second_eleventh D X E hfin hst hLT pos _ h2b
      (Formalism.L2.KerInert.admissible_eleventh_inert D cc δ p g hLT hAt h5 hIn hM X _ rfl)⟩

end Formalism.L2.KerInert.KGLt
