import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationSplitSupportProjectsVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthonormalFrameReadingEqConjugateDatumThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPureTensorAtOriginEqThetaSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThPBilinearHeis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HxTranslateExponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaReadingLinearInjectiveAtOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenMapTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCHLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinTensAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyDerivCompNeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevel
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.ShortSeries

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem heisG_smul (y : Matrix (Fin n) (Fin r) E) (c : ℂ) (φ : TF n g) :
    heisG X bas y (c • φ) = c • heisG X bas y φ := by
  funext x
  simp only [heisG, heisS, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem projA_smul (w : E) (A : AddSubgroup (Matrix (Fin n) (Fin r) E)) (a : ℂ) (φ : TF n g) :
    projA X bas w A (a • φ) = a • projA X bas w A φ := by
  by_cases ha : a = 0
  · subst ha
    have h0 : ∀ y : Matrix (Fin n) (Fin r) E, heisG X bas y (0 : TF n g) = 0 := fun y => by
      have := heisG_smul (X := X) (bas := bas) y 0 (0 : TF n g)
      rwa [zero_smul, zero_smul] at this
    rw [zero_smul, zero_smul, projA, finsum_mem_eq_zero_of_forall_eq_zero, smul_zero]
    rintro _ ⟨y, -, rfl⟩
    simp only [h0, smul_zero]
  have hi : Function.Injective fun ψ : TF n g => a • ψ := smul_right_injective _ ha
  have e : (fun y => epsW X w y • heisG X bas y (a • φ)) '' A =
      (fun ψ : TF n g => a • ψ) '' ((fun y => epsW X w y • heisG X bas y φ) '' A) := by
    rw [Set.image_image]
    congr 1
    funext y
    rw [heisG_smul, smul_comm]
  unfold projA
  rw [e, Set.ncard_image_of_injective _ hi, finsum_mem_image hi.injOn, smul_comm a]
  congr 1
  rw [smul_finsum]
  simp only [smul_finsum]

theorem theta_smul₂ (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n) {q0 : ℕ} (hq : X.p0 + q0 = r)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (c : ℂ) (φ : TF n g) (h : GlobalTheory.SW.IsSB (c • φ))
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) : thP X hq bas idx (c • φ) P x = c * thP X hq bas idx φ P x := by
  have key : ∀ (a : ℂ) (ψ : TF n g), GlobalTheory.SW.IsSB ψ → thP X hq bas idx (a • ψ) P x = a * thP X hq bas idx ψ P x := by
    intro a ψ hψ
    have := (theta_bilinear_heisenberg E r g n X bas idx hs hn q0 hq x hx ψ hψ P).1 ψ hψ a 0
    rwa [zero_smul, add_zero, zero_mul, add_zero] at this
  by_cases hc : c = 0
  · have := key 0 _ h
    rw [zero_smul] at this
    rw [hc, zero_smul, this, zero_mul, zero_mul]
  · refine key c φ ?_
    have := (isSB_algebra_haar_linear ℚ _ _ _ _ h h).2.1 c⁻¹
    rwa [inv_smul_smul₀ hc] at this

theorem finite_levQ {H : Geo.Tor.Host E} (Dw : Datum H) (l : Geo.Tor.Level H) : Finite (LevQ Dw l) := by
  have hM : l.Mb ≠ ⊥ := by
    intro h
    have h₁ := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h₁
    have h₂ : l.M = 0 := by exact_mod_cast h₁
    have := l.three_le
    omega
  have := l.Mb.finiteQuotientOfFreeOfNeBot hM
  have := Dw.fin
  exact Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem cmHost_idempotent_trace_eq_one (H : Geo.Tor.Host E) : (H.w0 : E) + cc (H.w0 : E) = 1 := by
  rw [cc, ← H.bar_eq]
  exact_mod_cast congrArg (fun t : 𝓞 E => (t : E)) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one H)

end Classical

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {r g : ℕ}

theorem isInvOf_move (hr : W.rank = r) (X : Data D.host.E r) {x : Frame X.Ψ r}
    {s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ} (hs : IsInvOf W hr X x s) (k : GA D W) :
    IsInvOf W hr X (frMove θ W hr X k x)
      fun τ => compAt θ τ (Formalism.L2.Theta.mt W k) * s τ * compAt θ τ (Formalism.L2.Theta.mt W k⁻¹) := by
  subst hr
  intro ρ τ hτ
  have h := hs ρ τ hτ
  have e : mat (frMove θ W rfl X k x) τ = compAt θ ρ (Formalism.L2.Theta.mt W k) * mat x τ := by
    rw [← RealCoord.realM_tauE, ← hτ]
    rfl
  change s ρ * mat x τ = _ at h
  change (compAt θ ρ (Formalism.L2.Theta.mt W k) * s ρ * compAt θ ρ (Formalism.L2.Theta.mt W k⁻¹)) * _ = _
  rw [e, Matrix.mul_assoc, ← Matrix.mul_assoc (compAt θ ρ (Formalism.L2.Theta.mt W k⁻¹)),
    GlobalTheory.WeilVacMove.compAt_mt_inv_mul, Matrix.one_mul, Matrix.mul_assoc, h, Matrix.mul_neg, Matrix.mul_assoc]

theorem isBasOf_move (hr : W.rank = r) (X : Data D.host.E r) {q0 : ℕ} (hq : X.p0 + q0 = r) {x : Frame X.Ψ r}
    {B : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ} (hB : IsBasOf W hr X hq x B) (k : GA D W) :
    IsBasOf W hr X hq (frMove θ W hr X k x) fun τ => compAt θ τ (Formalism.L2.Theta.mt W k) * B τ := by
  subst hr
  intro ρ τ hτ j i a hi
  have e : mat (frMove θ W rfl X k x) τ = compAt θ ρ (Formalism.L2.Theta.mt W k) * mat x τ := by
    rw [← RealCoord.realM_tauE, ← hτ]
    rfl
  refine Eq.trans ?_ (congrFun (congrFun e a) (rowIdx hq j)).symm
  simp only [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun b _ => congrArg _ (hB ρ τ hτ j i b hi)

theorem isONFr_move (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hV : V.gram = 1) (he : Even V.rank) (hr : W.rank = r)
    (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hM : IsMod W hr X)
    (hS : IsSympl X bas) {x : Frame X.Ψ r} (hx : IsONFr X x) (k : GA D W) : IsONFr X (frMove θ W hr X k x) := by
  subst hr
  obtain ⟨X', m, hq', hq, bas', idx', hs, -, -, -, -, -, -, hfr⟩ :=
    GlobalTheory.T.orthonormal_frame_reading_eq_conjugate_datum_theta D ψ θ V W g X bas idx hψ hθ he hV hM hS
  obtain ⟨⟨B, hB⟩, hBx⟩ := hfr x hx
  obtain ⟨-, -, -, -, -, -, -, hmv, -⟩ := hBx B hB
  exact (hmv k).1

theorem reads_sum (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hV : V.gram = 1) (he : Even V.rank) (hr : W.rank = r)
    (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hM : IsMod W hr X)
    (hS : IsSympl X bas) {x : Frame X.Ψ r} (hx : IsONFr X x) {f : WO V W → ℂ} {φ : TF V.rank g}
    (hf : IsThetaFunO ψ V W f) (hR : Reads θ V W hr X bas idx f φ x) {Q : Type} (c : Q → ℂ)
    (γ : Q → Matrix (Fin W.rank) (Fin V.rank) D.host.E) (u : Q → WO V W) (hu : ∀ q, IsFinOf V W (γ q) (u q))
    (s : Finset Q) :
    IsThetaFunO ψ V W (∑ q ∈ s, c q • heisO ψ V W (u q) f) ∧
      Reads θ V W hr X bas idx (∑ q ∈ s, c q • heisO ψ V W (u q) f)
        (∑ q ∈ s, c q • heisG X bas (-(colsR hr (γ q))) φ) x := by
  have hlin := reads_linear_injective D ψ θ V W r g hr X bas idx hψ hθ hV he hM hS x hx
  induction s using Finset.induction_on with
  | empty =>
    have := (hlin _ _ _ _ hR hR).1 0 0
    simp only [zero_smul, add_zero] at this
    exact ⟨GlobalTheory.OrientedHeis.theta_zero, this⟩
  | insert q s hq ih =>
    rw [Finset.sum_insert hq, Finset.sum_insert hq]
    have h1 := reads_heisO_finOf D ψ θ V W r g hr X bas idx hψ hθ hV he hM hS x hx f φ hf hR _ _ (hu q)
    have := (hlin _ _ _ _ h1 ih.2).1 (c q) 1
    rw [one_smul, one_smul] at this
    exact ⟨GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf (hu q).1)) ih.1, this⟩

theorem kernel_of_reads {χV χW : (AE D)ˣ →* Circle} {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    (hP : IsPair ψ θ V W χV χW om) (hr : W.rank = r)
    (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hM : IsMod W hr X)
    (hS : IsSympl X bas) {q0 : ℕ} (hq : X.p0 + q0 = r) {x : Frame X.Ψ r} (hx : IsONFr X x)
    {s B : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ} (hs : IsInvOf W hr X x s) (hB : IsBasOf W hr X hq x B)
    {vr : Harm.Var X.Ψ q0 X.p0 (Fin V.rank) ≃ FVar D W.rank V.rank} (hvr : IsVarOf V W X q0 vr)
    {h : GA D V} (hh : h ∈ GfC V) (k : GA D W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) {φ : TF V.rank g}
    (hR : Reads θ V W hr X bas idx (om (h, k) f) φ (frMove θ W hr X k x))
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin V.rank)) (d : ℕ) (hd : P.IsHomogeneous d) :
    thetaKO om h k (pureTensorO ψ θ V W (fun _ => 1) s (fun _ => 1) B f (MvPolynomial.rename vr P)) =
      ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ)⁻¹ ^ d * thP X hq bas idx φ P (frMove θ W hr X k x) := by
  have h1 := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ V W χV χW om hP.weil hP.inf (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) s (fun τ => compAt θ τ (Formalism.L2.Theta.mt W k) * s τ * compAt θ τ (Formalism.L2.Theta.mt W k⁻¹)) B
    (fun τ => compAt θ τ (Formalism.L2.Theta.mt W k) * B τ) h k
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.mul_assoc, GlobalTheory.WeilVacMove.compAt_mt_inv_mul, Matrix.mul_one])
    (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ V hh, Matrix.mul_one]) (fun _ => rfl) f hf
    (MvPolynomial.rename vr P)).2
  rw [thetaKO, h1]
  exact GlobalTheory.T.fock_pure_tensor_at_origin_eq_theta_series D ψ θ V W r g hr X bas idx hP.weil.std hP.inf hP.std hP.even hM hS q0 hq _ _ _ vr
    (isONFr_move hP.weil.std hP.inf hP.std hP.even hr X bas idx hM hS hx k) (isInvOf_move hr X hs k)
    (isBasOf_move hr X hq hB k) hvr _ φ (hP.weil.om_pres _ _ hf) hR P d hd

theorem exists_finOf (V W : HSp D) (hr : W.rank = r) (y : Matrix (Fin V.rank) (Fin r) D.host.E) :
    ∃ p : Matrix (Fin W.rank) (Fin V.rank) D.host.E × WO V W, colsR hr p.1 = y ∧ IsFinOf V W p.1 p.2 := by
  subst hr
  exact ⟨(yᵀ, GlobalTheory.LatVac.finTens 1 yᵀ), rfl, (GlobalTheory.VacSign.isFinOf_iff _ _).2 rfl⟩

set_option maxHeartbeats 1000000 in

theorem thetaKO_eq_short_series : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (g q0 : ℕ) (X : Data D.host.E D.R.r) (hq : X.p0 + q0 = D.R.r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r) (x₀ : Frame X.Ψ D.R.r) (vr : Harm.Var X.Ψ q0 X.p0 (Fin (Vc D i).rank) ≃ FVar D (Wc D i).rank (Vc D i).rank), IsMod (Wc D i) (rank_Wc i) X → IsSympl X bas → IsONFr X x₀ → IsInvOf (Wc D i) (rank_Wc i) X x₀ (cart (R.MW i (sg0 D A))) → IsBasOf (Wc D i) (rank_Wc i) X hq x₀ (onb (R.MW i (sg0 D A))) → IsVarOf (Vc D i) (Wc D i) X q0 vr → ∀ (bad N : ℕ) (h : GA D (Vc D i)) (k : GA D (Wc D i)) (Λ : GenLat D.host.E (Vc D i).rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)) (e : AE D) (Ps : Finset (Formalism.L2.DIV.Pl D.host.E)) (y : (AE D)ˣ), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((bad : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → h ∈ GfC (Vc D i) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h y → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → Λ.TrivAt l₂.M → Λ.LevOK N l₂.M → MarkAd l₂ (Wc D i) (rank_Wc i) ι k mk → ∀ Y : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E, IsRoots l₂ (latR (rank_Wc i) (latG (Wc D i) k)) mk N Y → ∀ (v : TF (Vc D i).rank g) (a : ℂ), IsVac X bas (H.w0 : D.host.E) (tens (stdL D.host.E (Vc D i).rank) (latR (rank_Wc i) (latG (Wc D i) k))) v → Reads R.θ (Vc D i) (Wc D i) (rank_Wc i) X bas idx (R.ωP i t (1, k) (R.vacP i)) (a • v) (frMove R.θ (Wc D i) (rank_Wc i) X k x₀) → ∀ (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin (Vc D i).rank)) (d : ℕ), P.IsHomogeneous d → thetaKO (R.ωP i t) h k (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) (R.vP i t) (MvPolynomial.rename vr P)) = ((δ : ℤ) : ℂ) ^ d * (-1) ^ d * ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ)⁻¹ ^ d * a * ((((Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 y : Circle) : ℂ)⁻¹ * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) * ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ * thP X hq bas idx (gphi X bas (H.w0 : D.host.E) Λ.La (latR (rank_Wc i) (latG (Wc D i) k)) v (hatC l₂ φ) Y) P (frMove R.θ (Wc D i) (rank_Wc i) X k x₀) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i hstd H Dw ι hι hiso
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.lattice_isometry_sign_second D G Pl0 T0 A Ks R F hC i hstd H Dw ι hι hiso
  refine ⟨δ, ?_⟩
  intro t l₂ φ hφ hl hrt g q0 X hq bas idx x₀ vr hM hS hx hinv hbas hvr bad N h k Λ mk e Ps y hbad he hPs hh hsupp hdet
    hΛ htriv hlev hmk Y hY v a hv hR P d hd
  obtain ⟨hP, -, hV0, hW0, hVs, hWs, hVstd⟩ := RecPair.isPair_record D G Pl0 T0 A Ks R F hC i t hstd
  have hψ := hP.weil.std
  have hvac : IsVacO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.vacP i) :=
    (hC.thP.vP i t).1
  choose p hp using fun q => exists_finOf (Vc D i) (Wc D i) (rank_Wc i) ((δ : ℤ) • Y q)
  have hdat := hδ t l₂ φ hφ hl bad N h k Λ mk hbad ⟨hh, e, Ps, he, hPs, hsupp⟩ hΛ htriv hlev hmk Y (fun q => (p q).1)
    (fun q => (p q).2) hY hp
  haveI := finite_levQ Dw l₂
  letI : Fintype (Fin (Vc D i).rank → LevQ Dw l₂) := Fintype.ofFinite _
  obtain ⟨hhs, hks, -, hlat, hV1, -⟩ := GlobalTheory.MovedLat.moved_lattices D _ _ _ _ hV0 hW0 hVs hWs h k
  obtain ⟨-, -, hmv, -⟩ := GlobalTheory.MovedLat.moved_lattices D _ _ _ _ hV0 hW0 hVs hWs 1 k
  rw [show fin (Vc D i) 1 = 1 from map_one _, hV1] at hmv
  have hx' := isONFr_move hψ hP.inf hP.std hP.even (rank_Wc i) X bas idx hM hS hx k
  have hvac' := GlobalTheory.WeilVacMove.isVacO_om D _ _ _ _ _ _ _ hP.weil hP.inf (fun _ => 1) (fun _ => 1) _
    (fun τ => compAt R.θ τ (Formalism.L2.Theta.mt _ k) * cart (R.MW i (sg0 D A)) τ * compAt R.θ τ (Formalism.L2.Theta.mt _ k⁻¹))
    _ _ _ _ 1 k (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.mul_assoc, GlobalTheory.WeilVacMove.compAt_mt_inv_mul, Matrix.mul_one]) hmv _ hvac
  have hL : ∀ L₀ : Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E),
      L₀ = Submodule.span (𝓞 D.host.E)
        {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ Bridge.hLat (Wc D i) (fin (Wc D i) k), w = a • v} →
      latR (rank_Wc i) (latG (Wc D i) k) = latR (rank_Wc i) L₀ := fun L₀ h₀ => by rw [h₀, hlat]
  have hcl := GlobalTheory.T.weilRepresentation_split_support_projects_vacuum D _ _ _ _ _ _ _ hP _ g (rank_Wc i) X bas idx hM hS H hrt _ _ Λ.La _ hV0 hVs hks hVstd hL _ _ hx'
    (isInvOf_move (rank_Wc i) X hinv k) _ hvac' _ hR e Ps h y he hsupp hdet hΛ
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul, projA_smul, smul_smul] at hcl
  obtain ⟨-, hsd, huni, hfg⟩ := LatOf.isLatOf_tens D _ _ _ _ _ g (rank_Wc i) X bas idx hψ hP.inf hP.std hP.even hM hS
    _ _ Λ.La _ hhs hks hΛ hL
  obtain ⟨hth, hsum⟩ := reads_sum hψ hP.inf hP.std hP.even (rank_Wc i) X bas idx hM hS hx'
    (hP.weil.om_pres (h, k) _ hvac.2.theta) hcl (hatC l₂ φ) (fun q => (p q).1) (fun q => (p q).2) (fun q => (hp q).2)
    Finset.univ
  rw [finsum_eq_sum_of_fintype] at hdat
  have hthP : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have h1 := hP.weil.om_pres (h, k)⁻¹ _ (hdat ▸ GlobalTheory.OrientedHeis.theta_smul _ hth :
      IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.ωP i t (h, k) (R.vP i t)))
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h1
  have hrd := (reads_linear_injective D _ _ _ _ _ g (rank_Wc i) X bas idx hψ hP.inf hP.std hP.even hM hS _ hx'
    _ _ _ _ hsum hsum).1 ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ 0
  rw [zero_smul, zero_smul, add_zero, add_zero, ← hdat] at hrd
  simp only [heisG_smul, (hp _).1] at hrd
  simp only [smul_comm (hatC l₂ φ _)] at hrd
  rw [← Finset.smul_sum, smul_smul, ← finsum_eq_sum_of_fintype] at hrd
  rw [kernel_of_reads hP (rank_Wc i) X bas idx hM hS hq hx hinv hbas hvr hh k hthP hrd P d hd,
    theta_smul₂ idx hS hP.even hq hx'.mem_dom _ _ hrd.1]
  have hpar := Parity.thP_gphi_neg _ _ g _ X bas idx hS hP.even q0 hq (H.w0 : D.host.E) H.w0.isIntegral_coe (cmHost_idempotent_trace_eq_one H)
    _ hsd v hv Λ huni hfg _ (hatC l₂ φ) Y P d hd _ hx'.mem_dom
  unfold gphi at hpar ⊢
  rcases Int.units_eq_one_or δ with rfl | rfl
  · simp only [Units.val_one, one_smul]
    rw [hpar]
    push_cast
    ring
  · simp only [Units.val_neg, Units.val_one, neg_smul, one_smul, neg_neg, Int.cast_neg, Int.cast_one, ← mul_pow]
    rw [neg_mul_neg, one_mul, one_mul]
    ring

end GlobalTheory.AdTh.ShortSeries
