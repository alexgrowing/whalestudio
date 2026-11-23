import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSign
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharSymplecticHalfPeriodLatticeEqOne
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentHalfMemCompletedHomLatticeIffLocal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemPerOInfHalfAO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomAtIffLocPPerO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjPNotMemOfIdemSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExpTraceEqBrk
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NoConjOfIdemSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BrkSumRepsOrth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardRepsEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.DatumFour

theorem nsmul_mem_perO_of_halfB {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    {SS : Finset (HeightOneSpectrum (𝓞 E))} {M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)} {c : ℕ} (hc : 0 < c)
    {y : Formalism.L2.Col.HomE E a b} (hy : y ∈ halfBO SS M c) : c • y ∈ M := by
  have h := Formalism.L2.Ker.mem_of_forall_locP M fun Q => GlobalTheory.AdForm.HalfPairing.smul_mem_locP hc hy Q
  rwa [Nat.cast_smul_eq_nsmul] at h

theorem xi_add_halfB {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    {SS : Finset (HeightOneSpectrum (𝓞 E))} {N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)} {N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)}
    {M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)} {c : ℕ} (hc : 0 < c) (Ξ : Formalism.L2.Col.HomE E a b → ℂ)
    (hΞ2 : ∀ x, ∀ y ∈ Formalism.L2.Col.homAt SS N N', Ξ (x + (c : E) • y) = Ξ x)
    (hH : ∀ z, (∀ P ∈ SS, z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M) → z ∈ Formalism.L2.Col.homAt SS N N')
    {β : Formalism.L2.Col.HomE E a b} (hβ : β ∈ halfBO SS M c) (x : Formalism.L2.Col.HomE E a b) : Ξ (x + β) = Ξ x := by
  have hcE : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have h1 : (c : E)⁻¹ • β ∈ Formalism.L2.Col.homAt SS N N' := by
    refine hH _ fun P hP => ?_
    have h2 := (Formalism.L2.Ker.mem_twO M c _ β).1 hβ P
    have h3 : expS SS P = 1 := by unfold expS; rw [if_pos hP]
    rwa [h3, zpow_one] at h2
  have h4 := hΞ2 x _ h1
  rwa [smul_smul, mul_inv_cancel₀ hcE, one_smul] at h4

noncomputable def eXm {D : D7} (S T : HSp D) (e : AE D) (x : Formalism.L2.Col.HomE D.host.E S.rank T.rank) : WO S T :=
  (LinearMap.toMatrix' x).map fun r => e * incA D r

theorem nsmul_toMatrix_mem_latRat {D : D7} {S T : HSp D} (hcc : D.host.ccK = ⊤) {N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (dS : IsSelfDualC S N) (k c : ℕ) {y : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hy : c • y ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') :
    (k * c) • LinearMap.toMatrix' y ∈ GlobalTheory.LatVac.latRat S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) := by
  have h1 := GlobalTheory.AdForm.HalfPairing.toMatrix_mem_latRat hcc dS hy
  rw [map_nsmul] at h1
  rw [mul_smul]
  exact nsmul_mem h1 k

theorem char_brk {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {δ : ℂ} {sc : ℝ} (hP : StdPair θ S T δ sc ψ)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT) {e : AE D} (he0 : infPart D e = 0) {k : ℕ} {t u : WO S T}
    (ht : IsHalf e t) (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
    {M : Matrix (Fin T.rank) (Fin S.rank) D.host.E} (htM : t = GlobalTheory.LatVac.finTens 1 M + k • u)
    (y' : Formalism.L2.Col.HomE D.host.E S.rank T.rank)
    (hY : k • LinearMap.toMatrix' y' ∈ GlobalTheory.LatVac.latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))) :
    ψ (symplO S T t (eXm S T (cA D e) y')) = brk (HV sc) (embH (tauE D) δ y') (embH (tauE D) δ (Matrix.toLin' M)) := by
  have hht : IsHalf (cA D (cA D e)) t := by rw [GlobalTheory.LatVac.cA_cA]; exact ht
  have h4 := GlobalTheory.DatumFourier.char_eq hP.std dS dT (GlobalTheory.PlaceVec.infPart_cA he0) hht hu htM hY
  have h6 := GlobalTheory.TraceBrk.exp_trace_eq_brk D ψ θ S T δ sc hP M (LinearMap.toMatrix' y')
  rw [Matrix.toLin'_toMatrix'] at h6
  exact h4.trans h6

theorem fin_sum {V : Type} [AddCommGroup V] [Module ℂ V] (H : Formalism.L2.Th1.H.Sesq V) {A B Λ : AddSubgroup V} {SA SB : Finset V}
    (f g : V → ℂ) {v : V} (hv : v ∈ Λ ⊓ A) (hRA : Formalism.L2.Th1.H.IsReps B (Λ ⊓ A) SA)
    (horth : ∀ w ∈ Λ ⊓ A, ∑ y ∈ SB, brk H y w = if w ∈ B then (SB.card : ℂ) else 0)
    (hcard : SA.card = SB.card) (hne : SB.card ≠ 0) (hg : ∀ y ∈ SB, g y = brk H y v) :
    ∃ s0 ∈ SA, v - s0 ∈ B ∧
      ∑ y ∈ SB, (((SA.card : ℂ))⁻¹ * ∑ s ∈ SA, f s * (brk H y s)⁻¹) * g y = f s0 := by
  obtain ⟨s0, hs0, hvs0⟩ := hRA.2.2 v hv
  refine ⟨s0, hs0, hvs0, ?_⟩
  have h1 : ∑ y ∈ SB, (((SA.card : ℂ))⁻¹ * ∑ s ∈ SA, f s * (brk H y s)⁻¹) * g y
      = ((SA.card : ℂ))⁻¹ * ∑ s ∈ SA, f s * ∑ y ∈ SB, brk H y (v - s) := by
    rw [Finset.sum_congr rfl fun y hy => by rw [hg y hy]]
    simp only [Formalism.L2.Ker.brk_sub_right, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun y _ => by ring
  rw [h1, Finset.sum_congr rfl fun s hs => by rw [horth (v - s) (sub_mem hv (hRA.1 s hs))]]
  rw [Finset.sum_eq_single s0 (fun s hs hne' => by
      rw [if_neg (fun h => hne' (hRA.2.1 s hs s0 hs0 (by
        have h2 : s - s0 = (v - s0) - (v - s) := by abel
        rw [h2]; exact sub_mem hvs0 h))), mul_zero]) (fun h => absurd hs0 h), if_pos hvs0, hcard]
  have : (SB.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hne
  field_simp

theorem onV_embH {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] [Nonempty ι] {a b : ℕ}
    (emb : ι → E →+* ℂ) {δ : ℂ} (hδ : δ ≠ 0) (Ξ : Formalism.L2.Col.HomE E a b → ℂ) (z : Formalism.L2.Col.HomE E a b) :
    onV emb δ Ξ (embH emb δ z) = Ξ z := by
  have h : ∃ x, embH emb δ x = embH emb δ z := ⟨z, rfl⟩
  unfold onV
  rw [dif_pos h]
  exact congrArg Ξ (Formalism.L2.Ker.embH_inj emb hδ h.choose_spec)

theorem mem_BC {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ}
    {emb : ι → E →+* ℂ} {δ : ℂ} {AA0 : Submodule (𝓞 E) E} {SS : Finset (HeightOneSpectrum (𝓞 E))}
    {N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)} {N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)} {c : ℕ} {w : VV ι a b}
    (h : w ∈ BC emb δ AA0 SS N N' c) : ∃ β ∈ halfBO SS (perO AA0 N N') c, embH emb δ β = w :=
  AddSubgroup.mem_map.1 h

theorem embH_sub_eq {E : Type} [Field E] [NumberField E] {ι : Type} {a b : ℕ} (emb : ι → E →+* ℂ) (δ : ℂ)
    (m p β : Formalism.L2.Col.HomE E a b) (x0 s0 : VV ι a b) (hp : embH emb δ p = x0)
    (hβ : embH emb δ β = embH emb δ m - s0) : s0 - x0 = embH emb δ (m - p - β) := by
  rw [map_sub, map_sub, hp, hβ]; abel

theorem xi_sub_halfB {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    {SS : Finset (HeightOneSpectrum (𝓞 E))} {N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)} {N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)}
    {M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)} {c : ℕ} (hc : 0 < c) (Ξ : Formalism.L2.Col.HomE E a b → ℂ)
    (hΞ2 : ∀ x, ∀ y ∈ Formalism.L2.Col.homAt SS N N', Ξ (x + (c : E) • y) = Ξ x)
    (hH : ∀ z, (∀ P ∈ SS, z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M) → z ∈ Formalism.L2.Col.homAt SS N N')
    {β : Formalism.L2.Col.HomE E a b} (hβ : β ∈ halfBO SS M c) (x : Formalism.L2.Col.HomE E a b) : Ξ (x - β) = Ξ x := by
  have h1 := xi_add_halfB hc Ξ hΞ2 hH hβ (x - β)
  rw [sub_add_cancel] at h1
  exact h1.symm

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem four_expand : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → (∃ ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), IsSelfDualC S ΛS ∧ (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N) → (∃ ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E), IsSelfDualC T ΛT ∧ (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N') → ∀ (Φ : WO S T → ℂ) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), IsSBHalf e (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) Φ → (∀ γ, Φ (γ.map fun r => e * incA D r) = Ξ (toHom S T hS hT γ)) → (∀ x, Ξ x ≠ 0 → (c : D.host.E) • x ∈ Formalism.L2.Col.homAt SS N N') → (∀ x, ∀ y ∈ Formalism.L2.Col.homAt SS N N', Ξ (x + (c : D.host.E) • y) = Ξ x) → ∀ (SX SA SB : Finset (VV D.what₂.Tau a b)), Formalism.L2.Th1.H.IsReps (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) SX → Formalism.L2.Th1.H.IsReps (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) ((LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') ⊓ (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c)) SA → Formalism.L2.Th1.H.IsReps (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) SB → ∀ (px py : VV D.what₂.Tau a b → Formalism.L2.Col.HomE D.host.E a b), (∀ x ∈ SX, px x ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c ∧ embH (tauE D) δ (px x) = x) → (∀ y ∈ SB, py y ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c ∧ embH (tauE D) δ (py y) = y) → ∀ t, Φ t = ∑ x ∈ SX, ∑ y ∈ SB, (((SA.card : ℂ))⁻¹ * ∑ s ∈ SA, onV (tauE D) δ Ξ (s - x) * (brk (HV sc) y s)⁻¹) * (ψ (symplO S T (t + ((LinearMap.toMatrix' (px x)).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => e * incA D r) (((LinearMap.toMatrix' (py y)).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => cA D e * incA D r)) * halfInd e (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) (t + ((LinearMap.toMatrix' (px x)).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => e * incA D r)) := by
  intro D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa ⟨ΛS, dS, eS⟩ ⟨ΛT, dT, eT⟩ Φ Ξ hSB hΦ hΞ1 hΞ2 SX SA SB hRX hRA hRB px py hpx hpy
  subst hS hT
  obtain rfl : ΛS = N := SetLike.coe_injective eS
  obtain rfl : ΛT = N' := SetLike.coe_injective eT
  rw [← eS, ← eT] at hSB
  rw [← eS, ← eT]
  haveI : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛ
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hE
  have he0 : infPart D e = 0 := GlobalTheory.PlaceVec.idemSum_infPart hE
  have hecA : e * cA D e = 0 := hE.2
  have heI : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hee])
  have hcAcA : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have hcI : finPart D (cA D e) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hcAcA])
  have hΛe : ∀ w ∈ Λ, e • w ∈ Λ := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ e heI
  have hΛc : ∀ w ∈ Λ, cA D e • w ∈ Λ := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ (cA D e) hcI
  have hhe : ∀ w : WO S T, IsHalf e (e • w) := fun w i j => by
    rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hee]
  have heX : ∀ x, IsHalf e (eXm S T e x) := fun x i j => by
    simp only [eXm, Matrix.map_apply, ← mul_assoc, hee]
  have heX_add : ∀ x y, eXm S T e (x + y) = eXm S T e x + eXm S T e y := fun x y => by
    ext i j; simp only [eXm, map_add, Matrix.map_apply, Matrix.add_apply, RingHom.map_add, mul_add]
  have heX_sub : ∀ x y, eXm S T e (x - y) = eXm S T e x - eXm S T e y := fun x y => by
    ext i j; simp only [eXm, map_sub, Matrix.map_apply, Matrix.sub_apply, RingHom.map_sub, mul_sub]
  have heF : ∀ M : Matrix (Fin T.rank) (Fin S.rank) D.host.E, e • GlobalTheory.LatVac.finTens 1 M = eXm S T e (Matrix.toLin' M) := fun M => by
    ext i j
    simp only [eXm, LinearMap.toMatrix'_toLin', Matrix.smul_apply, smul_eq_mul, Matrix.map_apply]
    refine GlobalTheory.SplitScalar.adele_ext (by simp only [RingHom.map_mul, he0, zero_mul]) ?_
    have h6 : finPart D (GlobalTheory.LatVac.finTens 1 M i j) = finPart D (incA D (M i j)) := rfl
    rw [RingHom.map_mul, RingHom.map_mul, h6]
  have hkeX : ∀ K : ℕ, ∀ M : Matrix (Fin T.rank) (Fin S.rank) D.host.E, K • eXm S T e (Matrix.toLin' ((K : D.host.E)⁻¹ • M)) = (if K = 0 then 0 else eXm S T e (Matrix.toLin' M)) := by
    intro K M
    split_ifs with hK
    · rw [hK, zero_smul]
    ext i j
    simp only [eXm, LinearMap.toMatrix'_toLin', Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, nsmul_eq_mul]
    rw [← mul_assoc, mul_comm (K : AE D) e, mul_assoc, show (K : AE D) = incA D (K : D.host.E) by simp, ← map_mul,
      ← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hK), one_mul]
  have hKinj : ∀ K : ℕ, 0 < K → ∀ w₁ w₂ : WO S T, K • w₁ = K • w₂ → w₁ = w₂ := by
    intro K hK w₁ w₂ h
    have hu : IsUnit (K : AE D) := by
      have h1 : (K : AE D) = incA D (K : D.host.E) := by simp
      rw [h1]
      exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hK.ne')).map _
    ext i j
    have h3 := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply, nsmul_eq_mul] at h3
    exact hu.mul_left_cancel h3
  have hΦ' : ∀ x, Φ (eXm S T e x) = Ξ x := fun x => by
    rw [eXm, hΦ]
    congr 1
    unfold toHom
    rw [show ((LinearMap.toMatrix' x).reindex (finCongr rfl) (finCongr rfl)) = LinearMap.toMatrix' x from by
      ext i j; simp [Matrix.reindex_apply], Matrix.toLin'_toMatrix']
  obtain ⟨hsup, k, hk, hinv, hsupp⟩ := hSB
  have hSplit := GlobalTheory.HalfSplit.splitHyp_halves D ψ θ S T δ sc hP e SS hE ΛS ΛT c hc hcP h2 hLa dS dT
  intro t
  show Φ t = ∑ x ∈ SX, ∑ y ∈ SB, (((SA.card : ℂ))⁻¹ * ∑ s ∈ SA, onV (tauE D) δ Ξ (s - x) * (brk (HV sc) y s)⁻¹) *
    (ψ (symplO S T (t + eXm S T e (px x)) (eXm S T (cA D e) (py y))) * halfInd e Λ (t + eXm S T e (px x)))
  have hRHS0 : ∀ x ∈ SX, t + eXm S T e (px x) ∉ Λ ∨ ¬ IsHalf e (t + eXm S T e (px x)) → ∑ y ∈ SB, (((SA.card : ℂ))⁻¹ * ∑ s ∈ SA, onV (tauE D) δ Ξ (s - x) * (brk (HV sc) y s)⁻¹) *
      (ψ (symplO S T (t + eXm S T e (px x)) (eXm S T (cA D e) (py y))) * halfInd e Λ (t + eXm S T e (px x))) = 0 := by
    intro x _ h
    have h0 : halfInd e Λ (t + eXm S T e (px x)) = 0 := by
      unfold halfInd
      rw [if_neg]
      rintro ⟨h1, h3⟩
      rcases h with h | h
      exacts [h h1, h h3]
    simp [h0]
  by_cases ht : IsHalf e t
  swap
  ·
    have hΦ0 : Φ t = 0 := by
      by_contra h0
      exact ht (hsup t h0)
    rw [hΦ0]
    refine (Finset.sum_eq_zero fun x hx => hRHS0 x hx (Or.inr fun h3 => ht fun i j => ?_)).symm
    have h4 := h3 i j
    have h5 := heX (px x) i j
    simp only [Matrix.add_apply, mul_add] at h4
    rw [h5] at h4
    exact add_right_cancel h4
  have hsn : ∀ (a : AE D) (n : ℕ) (w : WO S T), a • (n • w) = n • (a • w) := fun a n w => by
    ext i j; simp only [Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]; ring
  have hns3 : ∀ (p q r : ℕ) (w : WO S T), (p * q * r) • w = p • (q • (r • w)) := fun p q r w => by
    ext i j; simp only [Matrix.smul_apply, nsmul_eq_mul]; push_cast; ring
  have hns2 : ∀ (p q : ℕ) (w : WO S T), (p * q) • w = p • (q • w) := fun p q w => by
    ext i j; simp only [Matrix.smul_apply, nsmul_eq_mul]; push_cast; ring
  have hhs : ∀ (n : ℕ) (w : WO S T), IsHalf e w → IsHalf e (n • w) := fun n w hw i j => by
    rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hw i j]
  have hEX : Φ t ≠ 0 → ∃ x0 ∈ SX, t + eXm S T e (px x0) ∈ Λ := by
    intro h0
    obtain ⟨M, hM, u, hu, htM⟩ := GlobalTheory.DatumFourier.approx_mod (Nat.mul_pos (Nat.mul_pos hk hk) hc) (hsupp t h0)
    have hteq : t = eXm S T e (Matrix.toLin' ((k : D.host.E)⁻¹ • M)) + k • (c • (e • u)) := by
      apply hKinj k hk
      have h1 : k • t = e • (k • t) := by
        ext i j
        rw [Matrix.smul_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, mul_left_comm, ht i j]
      rw [h1, htM, smul_add, heF, smul_add, hkeX k M, if_neg hk.ne', hsn, hns3]
    have hΦg : Φ t = Ξ (Matrix.toLin' ((k : D.host.E)⁻¹ • M)) := by
      rw [hteq, hinv _ (nsmul_mem (hΛe u hu) c) (hhs c _ (hhe u)), hΦ']
    have hg1 := hΞ1 _ (hΦg ▸ h0)
    have hg2 := (GlobalTheory.HomAtPer.homAt_iff_locP_perO D S T SS h2 ΛS ΛT dS dT _).1 hg1
    obtain ⟨x0, hx0, hloc⟩ := GlobalTheory.PerLift.exists_rep_add_mem D ψ θ S T δ sc hP e SS hE ΛS ΛT dS dT c hc SX hRX px hpx _ hg2
    refine ⟨x0, hx0, ?_⟩
    have h3 := (GlobalTheory.AdForm.HalfLat.half_mem_latO_iff D S T hP.cc e SS hE ΛS ΛT dS dT _).2 hloc
    have h4 : t + eXm S T e (px x0) = eXm S T e (Matrix.toLin' ((k : D.host.E)⁻¹ • M) + px x0) + k • (c • (e • u)) := by
      conv_lhs => rw [hteq]
      rw [heX_add]; abel
    rw [h4]
    exact add_mem h3 (nsmul_mem (nsmul_mem (hΛe u hu) c) k)
  have hUQ : ∀ x ∈ SX, ∀ x0 ∈ SX, t + eXm S T e (px x) ∈ Λ → t + eXm S T e (px x0) ∈ Λ → x = x0 := by
    intro x hx x0 hx0 h1 h3
    have h4 : eXm S T e (px x - px x0) ∈ Λ := by
      have h5 : eXm S T e (px x - px x0) = (t + eXm S T e (px x)) - (t + eXm S T e (px x0)) := by rw [heX_sub]; abel
      rw [h5]; exact sub_mem h1 h3
    have hloc := (GlobalTheory.AdForm.HalfLat.half_mem_latO_iff D S T hP.cc e SS hE ΛS ΛT dS dT _).1 h4
    have hA : px x - px x0 ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) ΛS ΛT) c :=
      sub_mem (hpx x hx).1 (hpx x0 hx0).1
    have hmem : px x - px x0 ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) ΛS ΛT := by
      apply Formalism.L2.Ker.mem_of_forall_locP
      intro Q
      by_cases hQ : Q ∈ SS
      · exact hloc Q hQ
      · have h6 := (Formalism.L2.Ker.mem_twO _ c _ _).1 hA Q
        unfold expS at h6
        rw [if_neg hQ] at h6
        split_ifs at h6 with hQ'
        · have hcE : (c : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
          have h7 := Formalism.L2.Ker.nat_smul_mem _ c h6
          rwa [neg_neg, zpow_one, smul_smul, mul_inv_cancel₀ hcE, one_smul] at h7
        · simpa using h6
    have h8 : x - x0 ∈ LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) ΛS ΛT :=
      ⟨px x - px x0, hmem, by rw [map_sub, (hpx x hx).2, (hpx x0 hx0).2]⟩
    exact hRX.2.1 x hx x0 hx0 h8
  by_cases hex : ∃ x0 ∈ SX, t + eXm S T e (px x0) ∈ Λ
  swap
  · have hΦ0 : Φ t = 0 := by
      by_contra h0
      exact hex (hEX h0)
    rw [hΦ0]
    exact (Finset.sum_eq_zero fun x hx => hRHS0 x hx (Or.inl fun h => hex ⟨x, hx, h⟩)).symm
  obtain ⟨x0, hx0, hu0⟩ := hex
  rw [Finset.sum_eq_single x0 (fun x hx hne => hRHS0 x hx (Or.inl fun h => hne (hUQ x hx x0 hx0 h hu0)))
    (fun h => absurd hx0 h)]
  have huh : IsHalf e (t + eXm S T e (px x0)) := fun i j => by
    rw [Matrix.add_apply, mul_add, ht i j, heX _ i j]
  have hI : halfInd e Λ (t + eXm S T e (px x0)) = 1 := by
    unfold halfInd
    rw [if_pos ⟨hu0, huh⟩]
  simp only [hI, mul_one]
  obtain ⟨M, hM, u', hu', huM⟩ := GlobalTheory.DatumFourier.approx_mod (Nat.mul_pos hk hc) hu0
  have hueq : t + eXm S T e (px x0) = eXm S T e (Matrix.toLin' M) + k • (c • (e • u')) := by
    have h1 : t + eXm S T e (px x0) = e • (t + eXm S T e (px x0)) := by
      ext i j
      rw [Matrix.smul_apply, smul_eq_mul, huh i j]
    rw [h1, huM, smul_add, heF, hsn, hns2]
  have hΦt : Φ t = Ξ (Matrix.toLin' M - px x0) := by
    have h1 : t = eXm S T e (Matrix.toLin' M - px x0) + k • (c • (e • u')) := by
      rw [heX_sub, sub_add_eq_add_sub, ← hueq]; abel
    rw [h1, hinv _ (nsmul_mem (hΛe u' hu') c) (hhs c _ (hhe u')), hΦ']
  have hcAu : cA D e • (t + eXm S T e (px x0)) = 0 := by
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, ← huh i j, ← mul_assoc, mul_comm (cA D e) e, hecA, zero_mul]
  have hmA := GlobalTheory.HalfAConj.mem_perO_inf_halfAO D S T hP.cc e SS hE ΛS ΛT dS dT c hc M hM ⟨-(k • (cA D e • u')), neg_mem (nsmul_mem (hΛc u' hu') k), by
      have h1 := congrArg (fun w => cA D e • w) huM
      simp only [hcAu, smul_add] at h1
      rw [eq_neg_of_add_eq_zero_left h1.symm, hsn, mul_comm k c, hns2, smul_neg]⟩
  have hv : embH (tauE D) δ (Matrix.toLin' M) ∈ LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) ΛS ΛT ⊓
      AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS ΛS ΛT c :=
    ⟨⟨_, hmA.1, rfl⟩, ⟨_, hmA.2, rfl⟩⟩
  have hY : ∀ y ∈ SB, ψ (symplO S T (t + eXm S T e (px x0)) (eXm S T (cA D e) (py y))) = brk (HV sc) y (embH (tauE D) δ (Matrix.toLin' M)) := by
    intro y hy
    have hcy : c • py y ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) ΛS ΛT :=
      nsmul_mem_perO_of_halfB hc (hpy y hy).1
    have hKY : (k * c) • LinearMap.toMatrix' (py y) ∈
        GlobalTheory.LatVac.latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) := by
      exact nsmul_toMatrix_mem_latRat hP.cc dS k c hcy
    exact (char_brk hP dS dT he0 huh hu' huM (py y) hKY).trans (by rw [(hpy y hy).2])
  have hcard := GlobalTheory.RepsCard.card_reps_eq _ _ _ _ _ _ hSplit SA SB hRA hRB
  obtain ⟨y0, hy0, -⟩ := hRB.2.2 0 (zero_mem _)
  have hSBne : SB.card ≠ 0 := (Finset.card_pos.2 ⟨y0, hy0⟩).ne'
  obtain ⟨s0, hs0, hvs0, hsum⟩ := fin_sum (HV sc) (fun s => onV (tauE D) δ Ξ (s - x0))
    (fun y => ψ (symplO S T (t + eXm S T e (px x0)) (eXm S T (cA D e) (py y)))) hv hRA
    (fun w hw => GlobalTheory.brk_sum_reps_orth _ _ _ _ _ _ hSplit SB hRB w hw) hcard hSBne hY
  refine hΦt.trans (Eq.trans ?_ hsum.symm)
  beta_reduce
  refine (mem_BC hvs0).elim fun β hβ => ?_
  have hβ' := hβ.1
  have hβe := hβ.2
  have hs0e := embH_sub_eq (tauE D) δ (Matrix.toLin' M) (px x0) β x0 s0 (hpx x0 hx0).2 hβe
  have hXi := xi_sub_halfB hc Ξ hΞ2 (fun z hz => (GlobalTheory.HomAtPer.homAt_iff_locP_perO D S T SS h2 ΛS ΛT dS dT z).2 hz) hβ' (Matrix.toLin' M - px x0)
  rw [hs0e, onV_embH (tauE D) hP.ne, hXi]

end GlobalTheory.AdForm.DatumFour
