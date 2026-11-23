import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOperatorFixThetaDatumAwaySplitPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOrientedFiniteFixesFockPolynomialVecto
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FockVectorsChainIsVacuumOffThetaLevels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorFockVacuum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepVectorExistsNonzeroVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockSph

variable {D : D7}

section Fock

variable {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
  {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}

variable (ψ θ sS sT) in

def Killed (n : ℕ) (g : WO S T → ℂ) : Prop :=
  ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ), l.length = n →
    l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) g = 0

variable (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
include hψ hθ

theorem foldr_theta (l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ)) {g : WO S T → ℂ}
    (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) g) := by
  induction l with
  | nil => exact hg
  | cons p l ih => exact GlobalTheory.FockIndep.annih_theta hψ hθ _ _ _ ih

theorem foldr_add (l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ)) {g g' : WO S T → ℂ}
    (hg : IsThetaFunO ψ S T g) (hg' : IsThetaFunO ψ S T g') :
    l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) (g + g') =
      l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) g +
        l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) g' := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact GlobalTheory.FockIndep.annih_add hψ hθ _ _ _ (foldr_theta hψ hθ l hg) (foldr_theta hψ hθ l hg')

theorem foldr_smul (l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ)) (a : ℂ) {g : WO S T → ℂ}
    (hg : IsThetaFunO ψ S T g) :
    l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) (a • g) =
      a • l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) g := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact GlobalTheory.FockIndep.annih_smul hψ hθ _ _ _ _ (foldr_theta hψ hθ l hg)

theorem foldr_of_eq_zero (l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ)) {g : WO S T → ℂ}
    (hg : IsThetaFunO ψ S T g) (h0 : g = 0) :
    l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) g = 0 := by
  have e : g = (0 : ℂ) • g := by rw [zero_smul, h0]
  rw [e, foldr_smul hψ hθ l 0 hg, zero_smul]

theorem killed_succ {n : ℕ} {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) (h : Killed ψ θ sS sT n g) :
    Killed ψ θ sS sT (n + 1) g := by
  intro l hl
  obtain ⟨p, l', rfl⟩ : ∃ p l', l = p :: l' := by
    cases l with
    | nil => simp at hl
    | cons p l' => exact ⟨p, l', rfl⟩
  simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
  rw [List.foldr_cons]
  exact foldr_of_eq_zero hψ hθ [p] (foldr_theta hψ hθ l' hg) (h l' hl)

theorem killed_mono {n m : ℕ} (hnm : n ≤ m) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) (h : Killed ψ θ sS sT n g) :
    Killed ψ θ sS sT m g := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact killed_succ hψ hθ hg ih

variable (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
include hS hT

theorem killed_aPlus (n : ℕ) : ∀ {g : WO S T → ℂ}, IsThetaFunO ψ S T g → Killed ψ θ sS sT n g →
    ∀ (τ' : D.what₂.Tau) (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ),
      Killed ψ θ sS sT (n + 1) (aPlus (heisO ψ S T) θ τ' (cplxO (sS τ') (sT τ')) z' g) := by
  induction n with
  | zero =>
    intro g hg h τ' z' l _
    have hg0 : g = 0 := h [] rfl
    have ha := GlobalTheory.FockIndep.aPlus_theta hψ hθ τ' (cplxO (sS τ') (sT τ')) z' hg
    refine foldr_of_eq_zero hψ hθ l ha ?_
    have e : g = (0 : ℂ) • g := by rw [zero_smul, hg0]
    rw [e, GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ _ hg, zero_smul]
  | succ n ih =>
    intro g hg h τ' z' l hl
    rcases List.eq_nil_or_concat l with h0 | ⟨l', q, rfl⟩
    · rw [h0, List.length_nil] at hl; omega
    · replace hl : l'.length = n + 1 := by simpa using hl
      rw [List.concat_eq_append, List.foldr_append, List.foldr_cons, List.foldr_nil,
        GlobalTheory.FockIndep.annih_aPlus hψ hθ q.1 q.2 hS hT τ' z' hg]
      have hq := GlobalTheory.FockIndep.annih_theta hψ hθ q.1 (cplxO (sS q.1) (sT q.1)) q.2 hg
      have hk : Killed ψ θ sS sT n (annih (heisO ψ S T) θ q.1 (cplxO (sS q.1) (sT q.1)) q.2 g) := by
        intro l'' hl''
        have := h (l'' ++ [q]) (by simp [hl''])
        rwa [List.foldr_append, List.foldr_cons, List.foldr_nil] at this
      rw [foldr_add hψ hθ l' (GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ hq) (GlobalTheory.OrientedHeis.theta_smul _ hg),
        ih hq hk τ' z' l' hl, foldr_smul hψ hθ l' _ hg, h l' hl, smul_zero, zero_add]

theorem isFockVec_pureTensorO (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hv : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec ψ θ S T sS sT (pureTensorO ψ θ S T sS sT BS BT f φ) := by
  have key : IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f φ) ∧
      ∃ N, Killed ψ θ sS sT N (pureTensorO ψ θ S T sS sT BS BT f φ) := by
    refine GlobalTheory.FockIndep.pure_mem (P := fun g => IsThetaFunO ψ S T g ∧ ∃ N, Killed ψ θ sS sT N g)
      (fun g g' ⟨hg, N, hN⟩ ⟨hg', N', hN'⟩ => ⟨GlobalTheory.OrientedHeis.theta_add hg hg', max N N', fun l hl => ?_⟩)
      (fun a g ⟨hg, N, hN⟩ => ⟨GlobalTheory.OrientedHeis.theta_smul a hg, N, fun l hl => ?_⟩)
      (fun i g ⟨hg, N, hN⟩ => ⟨GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ hg, N + 1, killed_aPlus hψ hθ hS hT N hg hN _ _⟩)
      ⟨hf, 1, fun l hl => ?_⟩ φ
    · rw [foldr_add hψ hθ l hg hg', killed_mono hψ hθ (le_max_left N N') hg hN l hl,
        killed_mono hψ hθ (le_max_right N N') hg' hN' l hl, add_zero]
    · rw [foldr_smul hψ hθ l a hg, hN l hl, smul_zero]
    · obtain ⟨p, rfl⟩ := List.length_eq_one_iff.1 hl
      exact hv p.1 p.2
  obtain ⟨h1, N, h2⟩ := key
  exact ⟨h1, N, h2⟩

end Fock

section Sph

variable {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}

theorem placeIdem_smul_of {P : HeightOneSpectrum (𝓞 D.host.F) → Prop} {w : HeightOneSpectrum (𝓞 D.host.F)}
    {ε : AF D.host.F} (hε : IsPlaceIdem D w ε) (hw : ¬ P w) {u : WO S T} (hu : u ∈ latO S T LS LT P) :
    algebraMap (AF D.host.F) (AE D) ε • u = 0 := by
  obtain ⟨β, rfl, -, h0⟩ := hε
  induction hu using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hx
    have hβα : β * α = 0 := by
      refine RestrictedProduct.ext _ _ fun y => ?_
      change evalV D.host.F y (β * α) = evalV D.host.F y 0
      rw [map_mul, map_zero]
      by_cases hy : y = w
      · rw [hy, hP w hw, mul_zero]
      · rw [h0 y hy, zero_mul]
    have hp : pairA D.host.F 0 β * pairA D.host.F 0 α = 0 := Prod.ext (mul_zero _) hβα
    ext i j
    change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (_ ⊗ₜ _) = (0 : AE D)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hp, TensorProduct.zero_tmul]
  | zero => rw [smul_zero]
  | add x x' _ _ h h' => rw [smul_add, h, h', add_zero]
  | neg x _ h => rw [smul_neg, h, neg_zero]

theorem idemSum_mul_of {P : HeightOneSpectrum (𝓞 D.host.F) → Prop} {e : AE D} {Pset : Finset (Pl D.host.E)}
    (he : IsIdemSum e Pset) (hv : ∀ PP ∈ Pset, ¬ P (PP.under (𝓞 D.host.F))) {u : WO S T}
    (hu : u ∈ latO S T LS LT P) (a : Fin T.rank) (b : Fin S.rank) :
    e * u a b = 0 ∧ cA D e * u a b = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have key : ∀ PP ∈ Pset, es PP * u a b = 0 ∧ cA D (es PP) * u a b = 0 := by
    intro PP hPP
    obtain ⟨⟨a1, a2, w, ε, hε, a3⟩, -⟩ := hes PP hPP
    have hw : ¬ P w := by
      rw [← GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ PP w ε (hes PP hPP) hε a3]
      exact hv PP hPP
    have h0 := congrFun (congrFun (placeIdem_smul_of hε hw hu) a) b
    rw [Matrix.smul_apply, smul_eq_mul, ← a3, Matrix.zero_apply] at h0
    have c1 : cA D (es PP) * cA D (es PP) = cA D (es PP) := by rw [← map_mul, a1]
    have c2 : cA D (es PP) * es PP = 0 := by rw [mul_comm, a2]
    refine ⟨?_, ?_⟩
    · linear_combination es PP * h0 - u a b * a1 - u a b * a2
    · linear_combination cA D (es PP) * h0 - u a b * c1 - u a b * c2
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_mul]; exact Finset.sum_eq_zero fun PP hPP => (key PP hPP).1
  · rw [map_sum, Finset.sum_mul]; exact Finset.sum_eq_zero fun PP hPP => (key PP hPP).2

theorem isLatVac_pureTensorO_off {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ)
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    {f₀ Φ f : WO S T → ℂ} (hvac : IsVacO ψ θ S T sS sT LS LT f₀) {e : AE D} {Pset : Finset (Pl D.host.E)}
    (he : IsIdemSum e Pset) (hth : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T LS LT fun _ => True) 1 f₀ Φ f)
    (Sf : Finset (HeightOneSpectrum (𝓞 D.host.F))) (hP : ∀ PP ∈ Pset, PP.under (𝓞 D.host.F) ∈ Sf)
    (hpt : ∀ φ, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f φ)) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    IsLatVac (heisO ψ S T) (latO S T LS LT fun v => v ∉ Sf) (pureTensorO ψ θ S T sS sT BS BT f φ) := by
  have hle : latO S T LS LT (fun v => v ∉ Sf) ≤ latO S T LS LT fun _ => True :=
    GlobalTheory.PlaceTensor.latO_mono fun _ _ => trivial
  have hlat := hvac.2.lat
  have fix : ∀ u ∈ latO S T LS LT (fun v => v ∉ Sf), heisO ψ S T u f₀ = f₀ →
      heisO ψ S T u (pureTensorO ψ θ S T sS sT BS BT f φ) = pureTensorO ψ θ S T sS sT BS BT f φ := fun u hu h0 =>
    GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hθ sS sT BS BT f hpt u
      (GlobalTheory.VacGood.infPart_latO (hle hu))
      (GlobalTheory.Hk3.heisO_fix_thetaAt_off ψ S T e _ 1 f₀ Φ f hth u
        (idemSum_mul_of he (fun PP h hn => hn (hP PP h)) hu) h0) φ
  exact ⟨fun u hu => fix (2 • u) (AddSubgroup.nsmul_mem _ hu 2) (hlat.1 u (hle hu)),
    fun e' he' u hu hh => fix u hu (hlat.2 e' he' u (hle hu) hh)⟩

end Sph

end GlobalTheory.FockSph

open GlobalTheory.FockSph in

theorem GlobalTheory.ChainOnto.fock_sph : ∀ D : D7, ForStep D fun c k s s' p => (∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (p.pt φ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff c.ψ s.V s'.V s.Λ s'.Λ c.S (p.pt φ)) ∧ GlobalTheory.LFun.UnrOff (c.chS (k + 1)) (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) ∧ GlobalTheory.LFun.UnrOff (c.chT (k + 1)) (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := by
  classical
  intro D _ c hc k hk s s' hs hs' p hp
  obtain ⟨ξ, f₀, hvec⟩ := hp.vec
  obtain ⟨hfθ, -, hfv, hpt⟩ := (GlobalTheory.T.thetaChainStep_vector_exists_nonzero_vacuum D c hc ⟨k, hk⟩ s s' hs hs').2 ξ f₀ p.f hvec
  obtain ⟨hvac, e, he, hth⟩ := hvec
  have hψ : IsStdChar D c.ψ (-1) := hc.std
  have hθ : IsInfFam c.θ := hc.inf
  refine ⟨fun φ => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact isFockVec_pureTensorO hψ hθ (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s.M τ)
      (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s'.M τ) (onb s.M) (onb s'.M) hfθ hfv φ
  · refine isLatVac_pureTensorO_off hθ (onb s.M) (onb s'.M) hvac he hth c.S (fun PP hPP => ?_) hpt φ
    obtain ⟨hr, ξ', hL⟩ := hs.lev
    rw [Finset.union_empty, hL] at hPP
    exact Finset.mem_image_of_mem _ hPP
  · intro w hw
    have hμ : GlobalTheory.LFun.UnrAt (c.μ (k + 1)) w := hc.unr ⟨k, hk⟩ w hw
    have hη : GlobalTheory.LFun.UnrAt c.η⁻¹ w := (GlobalTheory.LFun.unrAt_of_unramEverywhere hc.chars.2.1 w).inv
    have hμη : GlobalTheory.LFun.UnrAt (c.μ (k + 1) * c.η⁻¹) w := hμ.mul hη
    unfold Com.chS Lift.chrStep
    split_ifs <;> assumption
  · intro w hw
    have hμ : GlobalTheory.LFun.UnrAt (c.μ (k + 1)) w := hc.unr ⟨k, hk⟩ w hw
    have hη : GlobalTheory.LFun.UnrAt c.η⁻¹ w := (GlobalTheory.LFun.unrAt_of_unramEverywhere hc.chars.2.1 w).inv
    have hμη : GlobalTheory.LFun.UnrAt (c.μ (k + 1) * c.η⁻¹) w := hμ.mul hη
    unfold Com.chT Lift.chrStep
    split_ifs <;> assumption

end
