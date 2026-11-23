import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerOpsComm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpanSectionsAllAffinesOfCoverStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelOperatorsEventuallyGenerateStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CokernelSequenceOperatorSequenceStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.UV

theorem serre_one {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X)
    (hH : GlobalTheory.IsAmpleLB H) (F : X.Modules) (hF : IsCoherent F) :
    ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ q, 0 < q → Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ F H n) q) := by
  letI := algebraOfOver X A
  haveI : GlobalTheory.QCoh.IsFiniteQC F := ⟨hF.1, hF.2⟩
  exact Filter.eventually_atTop.1 (GlobalTheory.IsAmpleLB.eventually_subsingleton_coh_twistZ (R := A)
    (f := X ↘ Spec (.of A)) (fun _ => rfl) F hH)

theorem kerOpSeq (hG : GradedNoeth) {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] {k : ℕ} {M : ℕ → X.Modules}
    {T : Fin (k + 1) → ∀ e, M e ⟶ M (e + 1)} {d : ℕ} (hM : OpSeq (k + 1) M T d) :
    ∃ d₁ : ℕ, OpSeq k (kerSeq M T) (kerOps hM.comm) d₁ := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  choose D hD using fun U : X.affineOpens => GlobalTheory.T.kernel_operators_eventually_generate hG hM U
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens => ((U : X.Opens) : Set X)) (fun U => U.1.isOpen) (fun x _ => by
      have hx : x ∈ (⊤ : X.Opens) := trivial
      rw [← iSup_affineOpens_eq_top X] at hx
      obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact Set.mem_iUnion.2 ⟨U, hU⟩)
  have hcoh : ∀ e, IsCoherent (kerSeq M T e) := fun e => by
    haveI := (hM.coherent (e + 1)).1
    exact isCoherent_kernel _ (hM.coherent e)
  refine ⟨t.sup D, ⟨hcoh, kerOps_comm hM.comm, fun e he => ?_⟩⟩
  refine GlobalTheory.T.span_sections_all_affines_of_cover (fun i => (hcoh e).1) (hcoh (e + 1)).1 _ (fun x => ?_)
  obtain ⟨U, hUt, hxU⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact ⟨U, hxU, hD U e ((Finset.le_sup hUt).trans he)⟩

theorem vanish_of_ker_cok {X : Scheme.{0}} (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (hH : H.IsLB)
    {M : ℕ → X.Modules} (τ : ∀ e, M e ⟶ M (e + 1)) (n : ℤ)
    (h0 : ∀ q, 0 < q → Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (M 0) H n) q))
    (hK : ∀ e q, 0 < q → Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (kernel (τ e)) H n) q))
    (hC : ∀ e q, 0 < q → Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (cokernel (τ e)) H n) q)) :
    ∀ e q, 0 < q → Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (M e) H n) q) := by
  intro e
  induction e with
  | zero => exact h0
  | succ e ih =>
    intro q hq
    have hL := GlobalTheory.Twist.isLB_lbZPow hH n
    let f := τ e
    let S₁ : ShortComplex X.Modules := ShortComplex.mk (kernel.ι f) (Abelian.factorThruImage f) (by
      rw [← cancel_mono (Abelian.image.ι f)]; simp)
    have hS₁ : S₁.ShortExact := by
      refine { exact := ?_ }
      exact ShortComplex.exact_of_f_is_kernel _
        (isKernelOfComp (Abelian.image.ι f) f (kernelIsKernel f) _ (Abelian.image.fac f))
    let S₂ : ShortComplex X.Modules := ShortComplex.mk (Abelian.image.ι f) (cokernel.π f) (by
      simp [Abelian.image.ι])
    have hS₂ : S₂.ShortExact := by
      refine { exact := ?_ }
      exact ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel (cokernel.π f))
    have h₁ := GlobalTheory.Twist.shortExact_map hL hS₁
    have h₂ := GlobalTheory.Twist.shortExact_map hL hS₂
    have hIm := GlobalTheory.cohOn.subsingleton₃ h₁ ⊤ q (ih q hq) (hK e (q + 1) (by omega))
    exact GlobalTheory.cohOn.subsingleton₂ h₂ ⊤ q hIm (hC e q hq)

theorem coh_twistZ_of_sections {X : Scheme.{0}} (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (hH : H.IsLB)
    (F : X.Modules) [F.IsQuasicoherent] (h : ∀ U : X.affineOpens, Subsingleton Γ(F, U)) (n : ℤ) (q : ℕ) :
    Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ F H n) q) := by
  have hz : IsZero F := (GlobalTheory.QCoh.isZero_iff_forall_affine).2 fun U hU => h ⟨U, hU⟩
  have hz' : IsZero (GlobalTheory.twistZ F H n) := (GlobalTheory.twistFunctor (GlobalTheory.lbZPow H n)).map_isZero hz
  exact GlobalTheory.cohOn.subsingleton_of_isZero hz' ⊤ q

theorem uniformVanishing (hG : GradedNoeth) : UniformVanishing := by
  intro A _ _ X _ _ H hH k
  induction k with
  | zero =>
    intro M T d hM
    have hz : ∀ e, d < e → ∀ (n : ℤ) q, Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (M e) H n) q) := by
      intro e he n q
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
      haveI := (hM.coherent (e' + 1)).1
      refine coh_twistZ_of_sections H hH.isLB _ (fun U => ?_) n q
      have := hM.gen e' (by omega) U
      simp only [Set.iUnion_of_empty, Submodule.span_empty] at this
      refine ⟨fun a b => ?_⟩
      have ha : a ∈ (⊥ : Submodule Γ(X, U) _) := this ▸ Submodule.mem_top
      have hb : b ∈ (⊥ : Submodule Γ(X, U) _) := this ▸ Submodule.mem_top
      rw [Submodule.mem_bot] at ha hb
      rw [ha, hb]
    choose N hN using fun e => serre_one (A := A) H hH (M e) (hM.coherent e)
    obtain ⟨B, hB⟩ := Finite.exists_le (fun i : Fin (d + 1) => N i)
    refine ⟨B, fun n hn e q hq => ?_⟩
    by_cases he : e ≤ d
    · exact hN e n ((hB ⟨e, by omega⟩).trans hn) q hq
    · exact hz e (by omega) n q
  | succ k ih =>
    intro M T d hM
    obtain ⟨d₁, hK⟩ := kerOpSeq hG (A := A) hM
    obtain ⟨a, ha⟩ := ih _ _ _ hK
    obtain ⟨b, hb⟩ := ih _ _ _ (GlobalTheory.T.cokernel_sequence_operator_sequence hM)
    obtain ⟨c, hc⟩ := serre_one (A := A) H hH (M 0) (hM.coherent 0)
    refine ⟨max a (max b c), fun n hn => ?_⟩
    exact vanish_of_ker_cok H hH.isLB (T (Fin.last k)) n
      (hc n (by omega)) (fun e q hq => ha n (by omega) e q hq) (fun e q hq => hb n (by omega) e q hq)

end GlobalTheory.CompanionTheory.GE.UV
