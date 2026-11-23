import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PureEqPureA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzHeisLine
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopology
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.SchurTranslationsCharacters
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WeilRepresentationQuadraticDatum
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.BoundMulTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.WeilBound.ThetaLifts.SchwartzMoments.SchwartzDqTendsto
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CompanionTheory.Ar.RT.Inj

open scoped SchwartzMap LineDeriv

noncomputable section

namespace PositivityTheory.ThKOwn.KPol

open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.RT

section Line
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def hl (a : V) (L : V →L[ℝ] ℝ) (t : ℝ) (f : V → ℂ) (x : V) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * (L a / 2) : ℝ) : ℂ)) * f (x + t • a)

def dop (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  ∂_{a} f + (-(2 * Real.pi * Complex.I)) • SchwartzMap.smulLeftCLM ℂ L f

theorem dop_apply (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    dop a L f x = fderiv ℝ f x a + (-(2 * Real.pi * Complex.I) * (L x : ℂ)) * f x := by
  have hT := L.hasTemperateGrowth
  simp only [dop, SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hT,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  simp only [Complex.real_smul, smul_eq_mul]
  ring

theorem dop_add (a b : V) (L M : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) :
    dop (a + b) (L + M) f = dop a L f + dop b M f := by
  ext x
  simp only [SchwartzMap.add_apply, dop_apply, map_add, ContinuousLinearMap.add_apply]
  push_cast
  ring

theorem dop_subsingleton [Subsingleton V] (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) : dop a L f = 0 := by
  ext x
  have ha : a = 0 := Subsingleton.elim _ _
  have hx : x = 0 := Subsingleton.elim _ _
  simp [dop_apply, ha, hx]

theorem hasDerivAt_hl (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    HasDerivAt (fun t : ℝ => hl a L t f x) (dop a L f x) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => t * L x + t ^ 2 * (L a / 2)) (L x) 0 := by
    have a1 : HasDerivAt (fun t : ℝ => t * L x) (L x) 0 := by simpa using (hasDerivAt_id (0 : ℝ)).mul_const (L x)
    have a2 : HasDerivAt (fun t : ℝ => t ^ 2 * (L a / 2)) 0 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (L a / 2)
    simpa using a1.fun_add a2
  have h2 : HasDerivAt (fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * (L a / 2) : ℝ) : ℂ)))
      (-(2 * Real.pi * Complex.I) * (L x : ℂ)) 0 := by
    have := ((h1.ofReal_comp).const_mul (-(2 * Real.pi * Complex.I))).cexp
    simpa using this
  have h3 : HasDerivAt (fun t : ℝ => x + t • a) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add x
  have h4 : HasDerivAt (fun t : ℝ => f (x + t • a)) (fderiv ℝ f x a) 0 := by
    have hf : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • a) := by
      simpa using f.hasFDerivAt x
    exact hf.comp_hasDerivAt (0 : ℝ) h3
  refine (h2.fun_mul h4).congr_deriv ?_
  rw [dop_apply]
  simp
  ring

end Line

variable {F : Type} [Field F] [NumberField F]

section Points
variable {κ : Type} [Fintype κ]

def pt (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i)

theorem evI_pt (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    (fun i => evI F (pt x y i)) = x := by
  funext i
  simp [evI, pt]

theorem pureA_pt (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    pureA F f g (pt x y) = f x * g y := by
  simp [pureA, pt]

def rOf (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) : (κ → AF F) → ℂ := fun x => g fun i => (x i).2

theorem tens_rOf (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    tens (evI F) f (rOf g) = pureA F f g := rfl

theorem snd_eq_zero {z : κ → AF F} (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  let u : AF F := (0, 1)
  have h0 : evI F u = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h : u * z i = 0 := congrFun (hz u h0) i
  have h' : (1 : Af F) * (z i).2 = 0 := congrArg Prod.snd h
  simpa using h'

theorem rOf_add (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (x z : κ → AF F) (hz : At (evI F) z) :
    rOf g (x + z) = rOf g x := by
  have : (fun i => (x + z) i |>.2) = fun i => (x i).2 := by
    funext i
    show (x i).2 + (z i).2 = _
    rw [snd_eq_zero hz, add_zero]
  simp only [rOf, this]

theorem slice_sb {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (x : κ → mixedEmbedding.mixedSpace F) :
    (fun y => Φ (pt x y)) ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    have : (fun y => pureA F f g (pt x y)) = f x • g := by
      funext y
      simp [pureA_pt]
    rw [this]
    exact Submodule.smul_mem _ _ hg
  | zero => exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
  | smul c Φ _ h => exact Submodule.smul_mem _ c h

theorem slice_schwartz {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    ∃ h : SInf F κ, ∀ x, Φ (pt x y) = h x := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact ⟨g y • f, fun x => by simp [pureA_pt, mul_comm]⟩
  | zero => exact ⟨0, fun _ => rfl⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨h₁, e₁⟩ := h1
    obtain ⟨h₂, e₂⟩ := h2
    exact ⟨h₁ + h₂, fun x => by simp [e₁, e₂]⟩
  | smul c Φ _ h =>
    obtain ⟨h₁, e₁⟩ := h
    exact ⟨c • h₁, fun x => by simp [e₁]⟩

theorem exists_sb_one : ∃ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), g 0 = 1 := by
  obtain ⟨-, -, -, hc, ho, -⟩ := GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology F
  have hcl : IsClosed (GlobalTheory.CompanionTheory.SW.Core.Oh F) := hc.isClosed
  let S : Set (κ → FiniteAdeleRing (𝓞 F) F) := Set.pi Set.univ fun _ => GlobalTheory.CompanionTheory.SW.Core.Oh F
  have hS : IsClopen S := ⟨isClosed_set_pi fun _ _ => hcl, isOpen_set_pi Set.finite_univ fun _ _ => ho⟩
  have hSc : IsCompact S := isCompact_univ_pi fun _ => hc
  have h0 : (0 : κ → FiniteAdeleRing (𝓞 F) F) ∈ S := fun i _ v => by
    show (0 : _) ∈ _
    exact zero_mem _
  refine ⟨S.indicator 1, ⟨?_, HasCompactSupport.intro hSc fun x hx => Set.indicator_of_notMem hx _⟩, by simp [h0]⟩
  have h1 : IsLocallyConstant (⇑(LocallyConstant.charFn ℂ hS)) := (LocallyConstant.charFn ℂ hS).isLocallyConstant
  rwa [LocallyConstant.coe_charFn] at h1

end Points

section Coord
variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def aOf (M : Model σ X W) (u : Matrix (Fin n) (Fin d) (AE F E)) : Fin n × Fin d → mixedEmbedding.mixedSpace F :=
  fun i => evI F ((M.co.e u).1 i)

def lOf (M : Model σ X W) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  GlobalTheory.CompanionTheory.AgreeO.Sys.HeisD.linForm fun i => evI F ((M.co.e u).2 i)

end Coord

section Coord2
open GlobalTheory.CompanionTheory.AgreeO.Sys.HeisD
variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem aOf_add (M : Model σ X W) (u v : Matrix (Fin n) (Fin d) (AE F E)) :
    aOf M (u + v) = aOf M u + aOf M v := by
  funext i
  simp [aOf, map_add, evI_add]

theorem lOf_add (M : Model σ X W) (u v : Matrix (Fin n) (Fin d) (AE F E)) :
    lOf M (u + v) = lOf M u + lOf M v := by
  ext y
  simp only [lOf, ContinuousLinearMap.add_apply, linForm_apply, ← map_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [map_add, evI_add, mul_add]

theorem evI_half_trace (S : mixedEmbedding.mixedSpace F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F ⅟(2 : AF F) * S) =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) S / 2 := by
  have h1 : evI F ⅟(2 : AF F) + evI F ⅟(2 : AF F) = 1 := by
    rw [← evI_add, invOf_two_add_invOf_two]
    exact map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h2 : S = evI F ⅟(2 : AF F) * S + evI F ⅟(2 : AF F) * S := by
    rw [← add_mul, h1, one_mul]
  have h3 := congrArg (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)) h2
  rw [map_add] at h3
  linarith

open scoped Classical in
theorem heisLine_tens (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) (f : SInf F (Fin n × Fin d))
    {r : (Fin n × Fin d → AF F) → ℂ} (hr : ∀ x z, At (evI F) z → r (x + z) = r x) (t : ℝ) :
    M.heisLine ψ u t (tens (evI F) f r) = tens (evI F) (hl (aOf M u) (lOf M u) t f) r := by
  have hab : ∀ s, evI F s = 0 → s • M.co.e u = 0 := fun s hs => by
    rw [← map_smul, hu s hs, map_zero]
  have ha : At (evI F) (M.co.e u).1 := fun s hs => congrArg Prod.fst (hab s hs)
  have hb : At (evI F) (M.co.e u).2 := fun s hs => congrArg Prod.snd (hab s hs)
  have hat : At (evI F) (realAd F t • (M.co.e u).1) := fun s hs => by
    rw [smul_comm, ha s hs, smul_zero]
  funext x
  show schr ψ (M.co.e (realAd F t • u)) _ x = _
  rw [map_smul]
  show schr ψ (realAd F t • (M.co.e u).1, realAd F t • (M.co.e u).2) _ x = _
  have e : (fun i => evI F ((x + realAd F t • (M.co.e u).1) i)) =
      (fun i => evI F (x i)) + t • fun i => evI F ((M.co.e u).1 i) := by
    funext i
    simp [evI_add, evI_mul, evI_realAd, Algebra.smul_def]
  simp only [schr, tens]
  rw [phase_line ψ hψ _ _ x hb t, e, hr x _ hat, evI_half_trace]
  simp only [hl, aOf, lOf, linForm_apply, mul_assoc]
  rfl

end Coord2

section Core
variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

theorem act_one (k : UA σ W.J) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    actAB (cA σ) ((1 : UA σ Y.J), k) u = u * (mat k).transpose := by
  simp [actAB, mat]

theorem at_mul {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) (N : Matrix (Fin d) (Fin d) (AE F E)) :
    At (evI F) (u * N) := fun s hs => by rw [← Matrix.smul_mul, hu s hs, Matrix.zero_mul]

open scoped Classical in
theorem actsD_dop (M : Model σ Y W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) (f : SInf F (Fin n × Fin d)) :
    ActsD (evI F) (M.heisLine ψ u) f (dop (aOf M u) (lOf M u) f) := by
  intro r hr x
  have e : (fun t => M.heisLine ψ u t (tens (evI F) f r) x) =
      fun t => hl (aOf M u) (lOf M u) t f (fun i => evI F (x i)) * r x := by
    funext t
    rw [heisLine_tens M hψ hu f hr.1 t]
    rfl
  rw [e]
  exact (hasDerivAt_hl _ _ f _).mul_const (r x)

open scoped Classical in
theorem actsD_unique (M : Model σ Y W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) {f f₁ : SInf F (Fin n × Fin d)}
    (h : ActsD (evI F) (M.heisLine ψ u) f f₁) : f₁ = dop (aOf M u) (lOf M u) f := by
  obtain ⟨g, hg, h0⟩ := exists_sb_one (F := F) (κ := Fin n × Fin d)
  ext x
  have hr : Rest (evI F) f (rOf g) := ⟨fun x z hz => rOf_add g x z hz, Submodule.subset_span ⟨f, g, hg, rfl⟩⟩
  have h1 := h _ hr (pt x 0)
  have h2 := actsD_dop M hψ hu f _ hr (pt x 0)
  have := h1.unique h2
  simpa [tens_rOf, pureA_pt, h0] using this

open scoped Classical in
theorem pureA_inj {κ : Type} [Fintype κ] {f₁ f₂ : SInf F κ} {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (h0 : g 0 = 1)
    (h : pureA F f₁ g = pureA F f₂ g) : f₁ = f₂ := by
  ext x
  have := congrFun h (pt x 0)
  simpa [pureA_pt, h0] using this

variable {M : Model σ Y W} {ψ : AddChar (AF F) ℂ} {om : Rep σ Y W} {k : UA σ W.J}

open scoped Classical in

def Impl (om : Rep σ Y W) (k : UA σ W.J) (A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)) : Prop :=
  ∀ f : SInf F (Fin n × Fin d), ∀ g ∈ SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F), om (1, k) (pureA F f g) = pureA F (A f) g

open scoped Classical in
theorem exists_impl (hl : ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      ∀ g ∈ SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F), om (1, k) (pureA F f g) = pureA F f₁ g) :
    ∃ A, Impl om k A := by
  choose A₀ hA₀ using hl
  obtain ⟨g, hg, h0⟩ := exists_sb_one (F := F) (κ := Fin n × Fin d)
  refine ⟨{ toFun := A₀, map_add' := fun f₁ f₂ => ?_, map_smul' := fun c f => ?_ }, hA₀⟩
  · refine pureA_inj h0 ?_
    have e : ∀ (p q : SInf F (Fin n × Fin d)), pureA F (⇑(p + q)) g = pureA F p g + pureA F q g := fun p q => by
      funext x
      simp [pureA, add_mul]
    rw [← hA₀ _ g hg, e, e, map_add, hA₀ _ g hg, hA₀ _ g hg]
  · refine pureA_inj h0 ?_
    have e : ∀ (p : SInf F (Fin n × Fin d)), pureA F (⇑(c • p)) g = c • pureA F p g := fun p => by
      funext x
      simp [pureA, mul_assoc]
    simp only [RingHom.id_apply]
    rw [← hA₀ _ g hg, e, e, map_smul, hA₀ _ g hg]

open scoped Classical in
theorem polynomial_functional_eval_continuous (hs : IsSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om)
    {A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)} (hA : Impl om k A) (x : Fin n × Fin d → mixedEmbedding.mixedSpace F) :
    ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f, A f x = T f := by
  obtain ⟨g, hg, h0⟩ := exists_sb_one (F := F) (κ := Fin n × Fin d)
  let l : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj (pt x 0)
  have hl : l ∈ (adeleClass F).adm (Fin n × Fin d) := fun g' _ =>
    ⟨g' 0 • (BoundedContinuousFunction.evalCLM ℂ x ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ _), fun f => by
      simp [l, pureA_pt, mul_comm]⟩
  obtain ⟨T, hT⟩ := hs.adm (1, k) l hl g hg
  refine ⟨T, fun f => ?_⟩
  rw [← hT f]
  show _ = om (1, k) (pureA F f g) (pt x 0)
  rw [hA f g hg, pureA_pt, h0, mul_one]

end Core

section LineProof
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def chirp (c : ℝ) (q : V → ℝ) (x : V) : ℂ := Complex.exp (Complex.I * ((-(2 * Real.pi) * c * q x : ℝ) : ℂ))

theorem chirp_tg (c : ℝ) {q : V → ℝ} (hq : q.HasTemperateGrowth) : (chirp c q).HasTemperateGrowth := by
  have h1 : (fun x => -(2 * Real.pi) * c * q x).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const _).mul hq
  exact GlobalTheory.CompanionTheory.OM.SchDiff.temperate_exp.comp h1

theorem chirp_mul (q : V → ℝ) (x y : V) :
    chirp 1 q y * chirp (-1) q x =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((q y - q x : ℝ) : ℂ)) := by
  rw [chirp, chirp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem chirp_one (q : V → ℝ) (x : V) : chirp (-1) q x * chirp 1 q x = 1 := by
  rw [mul_comm, chirp_mul]
  simp

theorem hl_schwartz (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) (t : ℝ) : ∃ G : 𝓢(V, ℂ), ∀ x, G x = hl a L t f x := by
  have hq : (fun x => t * L x + t ^ 2 * (L a / 2)).HasTemperateGrowth :=
    ((Function.HasTemperateGrowth.const t).mul L.hasTemperateGrowth).add (Function.HasTemperateGrowth.const _)
  refine ⟨SchwartzMap.smulLeftCLM ℂ (chirp 1 fun x => t * L x + t ^ 2 * (L a / 2))
    (SchwartzMap.compSubConstCLM ℂ (-(t • a)) f), fun x => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply (chirp_tg 1 hq), SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, hl, chirp]
  simp only [smul_eq_mul]
  congr 2
  push_cast
  ring

theorem hl_line_deriv (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) :
    ∃ G : ℝ → 𝓢(V, ℂ), (∀ t x, G t x = hl a L t f x) ∧
      (a ≠ 0 → ∀ T : 𝓢(V, ℂ) →L[ℂ] ℂ, HasDerivAt (fun t => T (G t)) (T (dop a L f)) 0) := by
  choose G hG using hl_schwartz a L f
  refine ⟨G, hG, fun ha T => ?_⟩
  have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.2 ha
  obtain ⟨g₀, -, hg₀⟩ := exists_dual_vector ℝ a hna
  set lam : V →L[ℝ] ℝ := ‖a‖⁻¹ • g₀ with hlam
  have hla : lam a = 1 := by
    simp only [hlam, ContinuousLinearMap.smul_apply, hg₀, smul_eq_mul]
    simpa using inv_mul_cancel₀ hna
  set q : V → ℝ := fun x => lam x * L x + (-(L a / 2)) * (lam x * lam x) with hq
  have hqt : q.HasTemperateGrowth :=
    (lam.hasTemperateGrowth.mul L.hasTemperateGrowth).add
      ((Function.HasTemperateGrowth.const _).mul (lam.hasTemperateGrowth.mul lam.hasTemperateGrowth))
  have hdiff : ∀ (x : V) (t : ℝ), q (x + t • a) - q x = t * L x + t ^ 2 * (L a / 2) := fun x t => by
    simp only [hq, map_add, map_smul, hla, smul_eq_mul]
    ring
  have t1 := chirp_tg 1 hqt
  have t2 := chirp_tg (-1) hqt
  set P := SchwartzMap.smulLeftCLM ℂ (chirp 1 q) with hP
  set Pi := SchwartzMap.smulLeftCLM ℂ (chirp (-1) q) with hPi
  set g : 𝓢(V, ℂ) := P f with hg
  have hGe : ∀ t, G t = Pi (SchwartzMap.compSubConstCLM ℂ (-(t • a)) g) := fun t => by
    ext x
    rw [hG, hPi, SchwartzMap.smulLeftCLM_apply_apply t2, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, hg, hP,
      SchwartzMap.smulLeftCLM_apply_apply t1, hl, ← hdiff]
    simp only [smul_eq_mul]
    rw [← mul_assoc, mul_comm (chirp (-1) q x), chirp_mul]
  have hf : Pi g = f := by
    ext x
    rw [hPi, SchwartzMap.smulLeftCLM_apply_apply t2, hg, hP, SchwartzMap.smulLeftCLM_apply_apply t1]
    simp only [smul_eq_mul]
    rw [← mul_assoc, chirp_one, one_mul]
  have hG0 : G 0 = f := by
    ext x
    rw [hG]
    simp [hl]
  have hder : ∀ T₁ : 𝓢(V, ℂ) →L[ℂ] ℂ, HasDerivAt (fun t => T₁ (G t)) (T₁ (Pi (∂_{a} g))) 0 := fun T₁ => by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have h := PositivityTheory.ThKOwn.schwartz_dq_tendsto g a
    have h2 := (((T₁.comp Pi).restrictScalars ℝ).continuous.tendsto _).comp h
    refine h2.congr fun t => ?_
    simp only [Function.comp, map_smul, map_sub, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.comp_apply,
      zero_add, hG0, hGe, hf]
  have hid : Pi (∂_{a} g) = dop a L f := by
    ext x
    have h1 := hder (BoundedContinuousFunction.evalCLM ℂ x ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ V ℂ)
    have e : (fun t => (BoundedContinuousFunction.evalCLM ℂ x ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ V ℂ) (G t)) =
        fun t => hl a L t f x := by
      funext t
      exact hG t x
    rw [e] at h1
    exact h1.unique (hasDerivAt_hl a L f x)
  rw [← hid]
  exact hder T
end LineProof

section Inter
variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}
variable {M : Model σ Y W} {ψ : AddChar (AF F) ℂ} {om : Rep σ Y W} {k : UA σ W.J}

open scoped Classical in
theorem line_hl (hψ : IsStd ψ) (hs : IsSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om)
    {A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)} (hA : Impl om k A)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) (f G : SInf F (Fin n × Fin d)) (t : ℝ)
    (hG : ∀ x, G x = hl (aOf M u) (lOf M u) t f x) (x : Fin n × Fin d → mixedEmbedding.mixedSpace F) :
    A G x = hl (aOf M (u * (mat k).transpose)) (lOf M (u * (mat k).transpose)) t (A f) x := by
  obtain ⟨g, hg, h0⟩ := exists_sb_one (F := F) (κ := Fin n × Fin d)
  have hr : ∀ x z, At (evI F) z → rOf g (x + z) = rOf g x := fun x z hz => rOf_add g x z hz
  have hΦ : pureA F f g ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, g, hg, rfl⟩
  have e1 : M.heisLine ψ u t (pureA F f g) = pureA F G g := by
    rw [← tens_rOf, heisLine_tens M hψ hu f hr t, tens_rOf]
    congr 1
    funext x
    exact (hG x).symm
  have e2 : om (1, k) (M.heisLine ψ u t (pureA F f g)) =
      M.heisLine ψ (u * (mat k).transpose) t (om (1, k) (pureA F f g)) := by
    have := hs.impl (1, k) (realAd F t • u) _ hΦ
    rw [act_one, Matrix.smul_mul] at this
    exact this
  rw [e1, hA G g hg, hA f g hg, ← tens_rOf, ← tens_rOf, heisLine_tens M hψ (at_mul hu _) (A f) hr t] at e2
  have := congrFun e2 (pt x 0)
  simpa [tens_rOf, pureA_pt, h0] using this

open scoped Classical in
theorem inter_of_ne (hψ : IsStd ψ) (hs : IsSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om)
    {A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)} (hA : Impl om k A)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) (ha : aOf M u ≠ 0) (f : SInf F (Fin n × Fin d)) :
    A (dop (aOf M u) (lOf M u) f) = dop (aOf M (u * (mat k).transpose)) (lOf M (u * (mat k).transpose)) (A f) := by
  obtain ⟨G, hG, hD⟩ := hl_line_deriv (aOf M u) (lOf M u) f
  ext x
  obtain ⟨T, hT⟩ := polynomial_functional_eval_continuous hs hA x
  have h1 := hD ha T
  have e : (fun t => T (G t)) = fun t => hl (aOf M (u * (mat k).transpose)) (lOf M (u * (mat k).transpose)) t (A f) x := by
    funext t
    rw [← hT]
    exact line_hl hψ hs hA hu f (G t) t (hG t) x
  rw [e] at h1
  rw [hT]
  exact h1.unique (hasDerivAt_hl _ _ (A f) x)

open scoped Classical in
theorem exists_at (M : Model σ Y W) (ξ : Fin n × Fin d → mixedEmbedding.mixedSpace F) :
    ∃ v : Matrix (Fin n) (Fin d) (AE F E), At (evI F) v ∧ aOf M v = ξ := by
  refine ⟨M.co.e.symm (pt ξ 0, 0), fun s hs => ?_, ?_⟩
  · have h1 : s.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hs
    rw [← map_smul, LinearEquiv.map_eq_zero_iff]
    refine Prod.ext ?_ (by simp)
    funext i
    refine Prod.ext ?_ ?_
    · show s.1 * _ = 0
      rw [h1, zero_mul]
    · show s.2 * 0 = 0
      rw [mul_zero]
  · have : M.co.e (M.co.e.symm (pt ξ 0, 0)) = (pt ξ 0, 0) := LinearEquiv.apply_symm_apply _ _
    show (fun i => evI F ((M.co.e (M.co.e.symm (pt ξ 0, 0))).1 i)) = ξ
    rw [this]
    exact evI_pt ξ 0

open scoped Classical in
theorem inter (hψ : IsStd ψ) (hs : IsSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om)
    {A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)} (hA : Impl om k A)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) (f : SInf F (Fin n × Fin d)) :
    A (dop (aOf M u) (lOf M u) f) = dop (aOf M (u * (mat k).transpose)) (lOf M (u * (mat k).transpose)) (A f) := by
  by_cases ha : aOf M u = 0
  · rcases subsingleton_or_nontrivial (Fin n × Fin d → mixedEmbedding.mixedSpace F) with hV | hV
    · rw [dop_subsingleton, dop_subsingleton, map_zero]
    · obtain ⟨ξ, hξ⟩ := exists_ne (0 : Fin n × Fin d → mixedEmbedding.mixedSpace F)
      obtain ⟨v, hv, rfl⟩ := exists_at M ξ
      have huv : At (evI F) (u + v) := fun s hs => by rw [smul_add, hu s hs, hv s hs, add_zero]
      have h1 := inter_of_ne hψ hs hA huv (by rw [aOf_add, ha, zero_add]; exact hξ) f
      have h2 := inter_of_ne hψ hs hA hv hξ f
      rw [aOf_add, lOf_add, dop_add, map_add, Matrix.add_mul, aOf_add, lOf_add, dop_add, h2] at h1
      exact add_right_cancel h1
  · exact inter_of_ne hψ hs hA hu ha f

open scoped Classical in
theorem acts_unique {A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)} (hA : Impl om k A) {f f₁ : SInf F (Fin n × Fin d)}
    (h : Acts (evI F) (om (1, k)) f f₁) : f₁ = A f := by
  obtain ⟨g, hg, h0⟩ := exists_sb_one (F := F) (κ := Fin n × Fin d)
  have hr : Rest (evI F) f (rOf g) := ⟨fun x z hz => rOf_add g x z hz, Submodule.subset_span ⟨f, g, hg, rfl⟩⟩
  have h1 := h _ hr
  rw [tens_rOf, tens_rOf, hA f g hg] at h1
  exact (pureA_inj h0 h1).symm

end Inter

section Keep
variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}
variable {M : Model σ Y W} {ψ : AddChar (AF F) ℂ} {om : Rep σ Y W} {k : UA σ W.J}

theorem mat_inv_mul (k : UA σ W.J) : mat k⁻¹ * mat k = 1 := by
  show ((k⁻¹ : UA σ W.J).1.1) * k.1.1 = 1
  simp

theorem mat_mul_inv (k : UA σ W.J) : mat k * mat k⁻¹ = 1 := by
  show k.1.1 * ((k⁻¹ : UA σ W.J).1.1) = 1
  simp

open scoped Classical in
theorem gauss_impl (hψ : IsStd ψ) (hs : IsSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om)
    {τ : ∀ w : InfinitePlace F, EmbOver E w} (hk : k ∈ KInf σ W τ)
    {A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)} (hA : Impl om k A)
    {f₀ : SInf F (Fin n × Fin d)} (h₀ : M.IsGauss ψ τ f₀) : M.IsGauss ψ τ (A f₀) := by
  obtain ⟨ε, hε⟩ := h₀
  refine ⟨ε, fun u u' hu hu' hrel f f' hf hf' => ?_⟩
  set N := (mat k⁻¹).transpose with hN
  have hNk : N * (mat k).transpose = 1 := by
    rw [hN, ← Matrix.transpose_mul, mat_mul_inv, Matrix.transpose_one]
  have e1 : u * N * (mat k).transpose = u := by rw [Matrix.mul_assoc, hNk, Matrix.mul_one]
  have e2 : u' * N * (mat k).transpose = u' := by rw [Matrix.mul_assoc, hNk, Matrix.mul_one]
  have hf1 := actsD_unique M hψ hu hf
  have hf2 := actsD_unique M hψ hu' hf'
  have i1 := inter hψ hs hA (at_mul hu N) f₀
  have i2 := inter hψ hs hA (at_mul hu' N) f₀
  rw [e1, ← hf1] at i1
  rw [e2, ← hf2] at i2
  have hcomm : ∀ w, Commute ((mat k⁻¹).map (piInf (τ w))) (W.θ w) := fun w => by
    have hc : Commute ((mat k).map (piInf (τ w))) (W.θ w) := hk.2 w
    have h1 : (mat k⁻¹).map (piInf (τ w)) * (mat k).map (piInf (τ w)) = 1 := by
      rw [← Matrix.map_mul, mat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : (mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w)) = 1 := by
      rw [← Matrix.map_mul, mat_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    show _ * _ = _ * _
    calc (mat k⁻¹).map (piInf (τ w)) * W.θ w
        = (mat k⁻¹).map (piInf (τ w)) * W.θ w * ((mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w))) := by
          rw [h2, Matrix.mul_one]
      _ = (mat k⁻¹).map (piInf (τ w)) * (W.θ w * (mat k).map (piInf (τ w))) * (mat k⁻¹).map (piInf (τ w)) := by
          simp only [Matrix.mul_assoc]
      _ = (mat k⁻¹).map (piInf (τ w)) * ((mat k).map (piInf (τ w)) * W.θ w) * (mat k⁻¹).map (piInf (τ w)) := by
          rw [hc.eq]
      _ = W.θ w * (mat k⁻¹).map (piInf (τ w)) := by
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hrel' : ∀ w, (u' * N).map (piInf (τ w)) =
      (((ε w : ℤ) : ℂ) * Complex.I) • (Y.θ w * (u * N).map (piInf (τ w)) * (W.θ w).transpose) := fun w => by
    have hN' : N.map (piInf (τ w)) = ((mat k⁻¹).map (piInf (τ w))).transpose := by
      rw [hN, Matrix.transpose_map]
    have hc : (W.θ w).transpose * N.map (piInf (τ w)) = N.map (piInf (τ w)) * (W.θ w).transpose := by
      rw [hN', ← Matrix.transpose_mul, ← Matrix.transpose_mul, (hcomm w).eq]
    rw [Matrix.map_mul, Matrix.map_mul, hrel w, Matrix.smul_mul]
    simp only [Matrix.mul_assoc, hc]
  have hg := hε (u * N) (u' * N) (at_mul hu N) (at_mul hu' N) hrel' _ _
    (actsD_dop M hψ (at_mul hu N) f₀) (actsD_dop M hψ (at_mul hu' N) f₀)
  rw [← i1, ← i2, hg, map_smul]

end Keep

section Loc
open GlobalTheory.CompanionTheory.SW.Core

variable {κ : Type} [Fintype κ]

def fstAd : AF F →ₐ[F] Ainf F := AlgHom.fst F (Ainf F) (Af F)

def iot (p : κ → Af F) : κ → AF F := fun i => pairA F 0 (p i)

theorem dot_iot (x : κ → AF F) (q : κ → Af F) :
    x ⬝ᵥ iot q = pairA F 0 ((fun i => sndA F (x i)) ⬝ᵥ q) := by
  have h1 : fstAd (x ⬝ᵥ iot q) = 0 := by
    simp only [dotProduct, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    show (x i).1 * 0 = 0
    rw [mul_zero]
  have h2 : sndA F (x ⬝ᵥ iot q) = (fun i => sndA F (x i)) ⬝ᵥ q := by
    simp only [dotProduct, map_sum]
    rfl
  exact Prod.ext h1 h2

theorem dot_zero' (x : κ → AF F) : x ⬝ᵥ iot (0 : κ → Af F) = 0 := by
  rw [dot_iot, dotProduct_zero]
  rfl

theorem iot_neg (p : κ → Af F) (x : κ → AF F) : x ⬝ᵥ iot (-p) = pairA F 0 (-((fun i => sndA F (x i)) ⬝ᵥ p)) := by
  rw [dot_iot, dotProduct_neg]

theorem pt_add_iot (x : κ → mixedEmbedding.mixedSpace F) (y p : κ → Af F) :
    pt x y + iot p = pt x (y + p) := by
  funext i
  refine Prod.ext ?_ rfl
  show _ + (0 : Ainf F) = _
  rw [add_zero]
  rfl

theorem pt_eta (X : κ → AF F) : X = pt (fun i => evI F (X i)) fun i => (X i).2 := by
  funext i
  refine Prod.ext ?_ rfl
  show (X i).1 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (InfiniteAdeleRing.ringEquiv_mixedSpace F (X i).1)
  rw [RingEquiv.symm_apply_apply]

def psF (ψ : AddChar (AF F) ℂ) : AddChar (Af F) ℂ where
  toFun x := ψ (pairA F 0 (-x))
  map_zero_eq_one' := by
    rw [neg_zero]
    exact AddChar.map_zero_eq_one ψ
  map_add_eq_mul' a b := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    exact Prod.ext (add_zero (0 : Ainf F)).symm (neg_add a b)

theorem psF_apply (ψ : AddChar (AF F) ℂ) (x : Af F) : psF ψ x = ψ (pairA F 0 (-x)) := rfl

theorem psF_std {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) : IsStdChar F (psF ψ) := by
  refine ⟨hψ.1.comp (continuous_const.prodMk continuous_neg), fun b => ?_⟩
  have h1 := hψ.2.1 b
  have e : pairA F 0 (-algebraMap F (Af F) b) =
      pairA F (algebraMap F (Ainf F) b) 0 + -algebraMap F (AF F) b := by
    refine Prod.ext ?_ ?_
    · show (0 : Ainf F) = algebraMap F (Ainf F) b + -algebraMap F (Ainf F) b
      rw [add_neg_cancel]
    · show -algebraMap F (Af F) b = 0 + -algebraMap F (Af F) b
      rw [zero_add]
  have hz : At (evI F) (pairA F (algebraMap F (Ainf F) b) 0) := fun u hu => by
    have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
    show (u.1 * algebraMap F (Ainf F) b, u.2 * 0) = ((0 : Ainf F), (0 : Af F))
    rw [h1, zero_mul, mul_zero]
  rw [psF_apply, e, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, h1, inv_one, mul_one, hψ.2.2 _ hz]
  have : evI F (pairA F (algebraMap F (Ainf F) b) 0) = mixedEmbedding F b := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (Ainf F) b) = _
    ext <;> simp
  rw [this, GlobalTheory.LatVacArith.trace_mixedEmbedding]
  simp

theorem exists_nadual {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (κ : Type) [Fintype κ] [DecidableEq κ] :
    ∃ (_ : MeasurableSpace (κ → Af F)) (μ : Measure (κ → Af F)),
      NADual (κ → Af F) (fun x y => psF ψ (x ⬝ᵥ y)) μ := by
  letI : MeasurableSpace (A F) := borel _
  haveI : BorelSpace (A F) := ⟨rfl⟩
  obtain ⟨hlc, hsc, ht2, hc, ho, -⟩ := GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology F
  have hne : (interior (Oh F)).Nonempty := by
    rw [ho.interior_eq]
    exact ⟨0, fun v => zero_mem _⟩
  let K : TopologicalSpace.PositiveCompacts (A F) := ⟨⟨Oh F, hc⟩, hne⟩
  have hlf : (Measure.addHaarMeasure K) (Oh F) = 1 := Measure.addHaarMeasure_self
  have hQ := SelfDual.naQuad F (Measure.addHaarMeasure K) inferInstance hlf (psF ψ) (psF_std hψ) κ
    (1 : Matrix κ κ F) (Matrix.isSymm_one) (by simp)
  have h5 := hQ.2.2.2.2.2
  have e : chiB (psF ψ) (Bf (1 : Matrix κ κ F)) = fun x y => psF ψ (x ⬝ᵥ y) := by
    funext x y
    simp [chiB, Bf, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [e] at h5
  exact ⟨_, _, h5⟩

end Loc

section Loc2
variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}
variable {M : Model σ Y W} {ψ : AddChar (AF F) ℂ} {om : Rep σ Y W} {k : UA σ W.J}

theorem act_fix (M : Model σ Y W) (hk : k ∈ UAt σ W (evI F)) (p q : Fin n × Fin d → Af F) :
    M.co.e.symm (iot p, iot q) * (mat k).transpose = M.co.e.symm (iot p, iot q) := by
  set w := M.co.e.symm (iot p, iot q) with hwd
  have h0 : evI F (pairA F 0 1) = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have hi : ∀ p : Fin n × Fin d → Af F, pairA F 0 1 • iot p = iot p := fun p => by
    funext i
    exact Prod.ext (mul_zero (0 : Ainf F)) (one_mul (p i))
  have hw : pairA F 0 1 • w = w := by
    apply M.co.e.injective
    rw [map_smul, hwd, LinearEquiv.apply_symm_apply]
    exact Prod.ext (hi p) (hi q)
  have hK : pairA F 0 1 • (mat k - 1) = 0 := hk _ h0
  have hK' : pairA F 0 1 • mat k = pairA F 0 1 • (1 : Matrix (Fin d) (Fin d) (AE F E)) := by
    rw [smul_sub] at hK
    exact sub_eq_zero.1 hK
  calc w * (mat k).transpose = (pairA F 0 1 • w) * (mat k).transpose := by rw [hw]
    _ = w * (pairA F 0 1 • (mat k).transpose) := by rw [Matrix.smul_mul, Matrix.mul_smul]
    _ = w * (pairA F 0 1 • mat k).transpose := by rw [Matrix.transpose_smul]
    _ = w := by
      rw [hK', Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_smul, Matrix.mul_one, hw]

theorem comm_rho (hs : IsSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om) (hk : k ∈ UAt σ W (evI F))
    (p q : Fin n × Fin d → Af F) {Φ : (Fin n × Fin d → AF F) → ℂ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    om (1, k) (M.co.rho ψ (M.co.e.symm (iot p, iot q)) Φ) = M.co.rho ψ (M.co.e.symm (iot p, iot q)) (om (1, k) Φ) := by
  have := hs.impl (1, k) (M.co.e.symm (iot p, iot q)) Φ hΦ
  rw [act_one, act_fix M hk] at this
  exact this

theorem rho_iot (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (p q : Fin n × Fin d → Af F) (Φ : (Fin n × Fin d → AF F) → ℂ)
    (x : Fin n × Fin d → AF F) :
    M.co.rho ψ (M.co.e.symm (iot p, iot q)) Φ x =
      ψ (x ⬝ᵥ iot q + ⅟(2 : AF F) * (iot p ⬝ᵥ iot q)) * Φ (x + iot p) := by
  show schr ψ (M.co.e (M.co.e.symm (iot p, iot q))) Φ x = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem iot_zero' : iot (0 : Fin n × Fin d → Af F) = 0 := rfl

theorem rho_char (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (y : Fin n × Fin d → Af F) (Φ : (Fin n × Fin d → AF F) → ℂ)
    (X : Fin n × Fin d → AF F) :
    M.co.rho ψ (M.co.e.symm (iot 0, iot (-y))) Φ X = psF ψ ((fun i => (X i).2) ⬝ᵥ y) * Φ X := by
  rw [rho_iot, iot_zero', add_zero, zero_dotProduct, mul_zero, add_zero, iot_neg]
  rfl

theorem rho_tr (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (p : Fin n × Fin d → Af F) (Φ : (Fin n × Fin d → AF F) → ℂ)
    (X : Fin n × Fin d → AF F) :
    M.co.rho ψ (M.co.e.symm (iot p, iot 0)) Φ X = Φ (X + iot p) := by
  rw [rho_iot, dot_zero', dot_zero', mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]

theorem evI_iot (X : Fin n × Fin d → AF F) (p : Fin n × Fin d → Af F) :
    (fun i => evI F ((X + iot p) i)) = fun i => evI F (X i) := by
  funext i
  have : evI F (iot p i) = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  rw [Pi.add_apply, GlobalTheory.CompanionTheory.AgreeO.Sys.HeisD.evI_add, this, add_zero]

open scoped Classical in
theorem exists_arch_operator (hψ : IsStd ψ)
    (hs : IsSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om) (hk : k ∈ UAt σ W (evI F)) (f : SInf F (Fin n × Fin d)) :
    ∃ f₁ : SInf F (Fin n × Fin d), ∀ g ∈ SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F), om (1, k) (pureA F f g) = pureA F f₁ g := by
  obtain ⟨mK, μ, hD⟩ := exists_nadual hψ (Fin n × Fin d)
  have hpure : ∀ g, GlobalTheory.CompanionTheory.SW.Core.SB g → pureA F f g ∈ schA F (Fin n × Fin d) := fun g hg =>
    Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hC : ∀ g, GlobalTheory.CompanionTheory.SW.Core.SB g → om (1, k) (pureA F f g) ∈ schA F (Fin n × Fin d) := fun g hg =>
    hs.pres (1, k) _ (hpure g hg)
  have hsch : ∀ ξ : Fin n × Fin d → mixedEmbedding.mixedSpace F, ∃ c : ℂ, ∀ g, GlobalTheory.CompanionTheory.SW.Core.SB g →
      (fun y => om (1, k) (pureA F f g) (pt ξ y)) = c • g := fun ξ => by
    refine GlobalTheory.CompanionTheory.SW.SchurChar.schur_translations_characters (Fin n × Fin d → Af F) _ μ hD
      (fun g y => om (1, k) (pureA F f g) (pt ξ y)) (fun φ hφ => slice_sb (hC φ hφ) ξ) ?_ ?_ ?_ ?_
    · intro φ φ' _ _
      have e : pureA F f (φ + φ') = pureA F f φ + pureA F f φ' := by
        funext x
        simp [pureA, mul_add]
      funext y
      simp only [e, map_add, Pi.add_apply]
    · intro c φ _
      have e : pureA F f (c • φ) = c • pureA F f φ := by
        funext x
        simp only [pureA, Pi.smul_apply, smul_eq_mul]
        ring
      funext y
      simp only [e, map_smul, Pi.smul_apply]
    · intro y φ hφ
      have e : pureA F f (fun u => psF ψ (u ⬝ᵥ y) * φ u) = M.co.rho ψ (M.co.e.symm (iot 0, iot (-y))) (pureA F f φ) := by
        funext X
        rw [rho_char]
        simp only [pureA]
        ring
      funext u
      rw [e, comm_rho hs hk _ _ (hpure φ hφ), rho_char]
      rfl
    · intro x φ hφ
      have e : pureA F f (fun u => φ (u + x)) = M.co.rho ψ (M.co.e.symm (iot x, iot 0)) (pureA F f φ) := by
        funext X
        rw [rho_tr]
        show _ = f (fun i => evI F ((X + iot x) i)) * _
        rw [evI_iot]
        rfl
      funext u
      rw [e, comm_rho hs hk _ _ (hpure φ hφ), rho_tr, pt_add_iot]
  choose c hc using hsch
  obtain ⟨g₀, hg₀, h0⟩ := exists_sb_one (F := F) (κ := Fin n × Fin d)
  obtain ⟨h, hh⟩ := slice_schwartz (hC g₀ hg₀) 0
  refine ⟨h, fun g hg => ?_⟩
  have e1 : ∀ ξ, c ξ = h ξ := fun ξ => by
    have h1 := congrFun (hc ξ g₀ hg₀) 0
    simp only [Pi.smul_apply, smul_eq_mul, h0, mul_one] at h1
    rw [← h1, hh]
  funext X
  have h2 := congrFun (hc (fun i => evI F (X i)) g hg) fun i => (X i).2
  simp only [Pi.smul_apply, smul_eq_mul, e1, ← pt_eta] at h2
  exact h2

end Loc2

end PositivityTheory.ThKOwn.KPol
