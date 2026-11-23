import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsLocalTwistTrivializationStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsTriangularRegularFrameChangeStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DetFacGMatEqOne
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptBasesLinearIndependentSpan
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsChartOfLineBundle

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.AdFrame

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

section Pure

theorem values_adapted {Ω Φ : Type} [Field Ω] [Field Φ] (i : Ω →+* Φ) (R : Subring Φ) {n r : ℕ}
    (A : Matrix (Fin n) (Fin r) Ω) (T : Matrix (Fin r) (Fin r) Ω) (C₀ : Matrix (Fin r) (Fin n) Ω) (z : Ω)
    (u U Rm Rm' : Matrix (Fin r) (Fin r) Φ) (F : Matrix (Fin n) (Fin r) Φ)
    (hF : F = A.map i * u) (hu : u * U = T.map i * Rm) (hRm : ∀ a b, Rm a b ∈ R) (hRm' : ∀ a b, Rm' a b ∈ R)
    (hR : Rm * Rm' = 1) (hB : ∀ a b, i ((A * T) a b / z) ∈ R) (hC₀ : ∀ a b, i (C₀ a b) ∈ R)
    (hinv : ∀ a b, ∑ k, C₀ a k * ((A * T) k b / z) = if a = b then 1 else 0) :
    ∃ C : Matrix (Fin r) (Fin n) Φ, (∀ a b, (F * U) a b / i z ∈ R) ∧ (∀ a b, C a b ∈ R) ∧
      ∀ a b, ∑ k, C a k * ((F * U) k b / i z) = if a = b then 1 else 0 := by
  set B : Matrix (Fin n) (Fin r) Ω := Matrix.of fun a b => (A * T) a b / z with hBdef
  have hFU : F * U = (A * T).map i * Rm := by
    rw [hF, Matrix.mul_assoc, hu, ← Matrix.mul_assoc, Matrix.map_mul]
  have hval : ∀ a b, (F * U) a b / i z = (B.map i * Rm) a b := by
    intro a b
    rw [hFU, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.map_apply, hBdef, Matrix.of_apply, map_div₀]
    ring
  have hCB : C₀ * B = 1 := by
    ext a b
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact hinv a b
  have hRm2 : Rm' * Rm = 1 := mul_eq_one_comm.1 hR
  refine ⟨Rm' * C₀.map i, fun a b => ?_, fun a b => ?_, fun a b => ?_⟩
  · rw [hval, Matrix.mul_apply]
    exact sum_mem fun k _ => mul_mem (hB a k) (hRm k b)
  · rw [Matrix.mul_apply]
    exact sum_mem fun k _ => mul_mem (hRm' a k) (hC₀ k b)
  · have h1 : (Rm' * C₀.map i) * (B.map i * Rm) = 1 := by
      have h2 : C₀.map i * B.map i = 1 := by
        rw [← Matrix.map_mul, hCB]
        exact Matrix.map_one _ (map_zero i) (map_one i)
      calc (Rm' * C₀.map i) * (B.map i * Rm) = Rm' * (C₀.map i * B.map i) * Rm := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h2, Matrix.mul_one, hRm2]
    have h3 := congrFun (congrFun h1 a) b
    rw [Matrix.mul_apply, Matrix.one_apply] at h3
    simpa only [hval] using h3

theorem colFrame_semi {Ω Φ E F : Type} [Field Ω] [Field Φ] [AddCommGroup E] [Module Ω E] [AddCommGroup F] [Module Φ F]
    {i : Ω →+* Φ} {j : E →+ F} (hj : ∀ (a : Ω) (e : E), j (a • e) = i a • j e) {r : ℕ} (e : Fin r → E)
    (T : Matrix (Fin r) (Fin r) Ω) :
    (fun k => j (colFrame e T k)) = colFrame (fun a => j (e a)) (T.map i) := by
  funext k
  simp only [colFrame, map_sum, hj, Matrix.map_apply]

theorem isFrameAt_of_map {X : Scheme.{0}} {Ω E E' : Type} [Field Ω] [AddCommGroup E] [Module Ω E] [AddCommGroup E']
    [Module Ω E'] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (L : Lat ξ E) (f : E →ₗ[Ω] E') (hf : Function.Injective f) {r : ℕ}
    (b : Fin r → E) (p : Cpt ξ) (h : (L.map f).IsFrameAt (fun k => f (b k)) p) : L.IsFrameAt b p := by
  refine ⟨LinearIndependent.of_comp f h.1, ?_⟩
  have h2 : (L p).map (f.restrictScalars (regAt ξ p)) =
      (Submodule.span (regAt ξ p) (Set.range b)).map (f.restrictScalars (regAt ξ p)) := by
    have : (Set.range fun k => f (b k)) = (f.restrictScalars (regAt ξ p)) '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [Submodule.map_span, ← this]
    exact h.2
  exact Submodule.map_injective_of_injective (f := f.restrictScalars (regAt ξ p)) hf h2

end Pure

section Main

theorem adapted_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∀ (𝔐' : HodgeCpt Y S (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (Fl : 𝔐'.Flag), HodgeOver 𝔐' 𝔐 pr (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) j → (∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) → ColFlags 𝔐 bW bO j Fl → ∀ (τ : CMType H) (p' : Cpt 𝔐'.ξ) (hp : genPt 𝔐.ξ ⤳ pr p'.1) (c₁ : ∀ k, J₀ k), InChart 𝔐.ξ (seg x₀) c₁ ⟨pr p'.1, hp⟩ → ∃ (U : Matrix (Fin (rk (CMType H) D.p D.q (.inl τ))) (Fin (rk (CMType H) D.p D.q (.inl τ))) (GenField Ω (rk (CMType H) D.p D.q))) (C : Matrix (Fin (rk (CMType H) D.p D.q (.inl τ))) (Fin (n (.inl τ))) (GenField Ω (rk (CMType H) D.p D.q))), U.BlockTriangular id ∧ (∀ a b, (fMat (aOf 𝔐 bW bO φ) (.inl τ) * U) a b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inl τ)) ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, C a b ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, ∑ k, C a k * ((fMat (aOf 𝔐 bW bO φ) (.inl τ) * U) k b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inl τ))) = if a = b then 1 else 0) ∧ ∀ l, ((𝔐'.V (.inl τ)).gr (Fl.b (.inl τ)) l).IsGenAt p' (U l l) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ hF 𝔐' pr j Fl hO hV hC τ p' hp c₁ hch
  obtain ⟨T, C₀, -, hfr, hreg, hC₀r, hinv⟩ := GlobalTheory.T.exists_local_twist_trivialization 𝔐.X Ω 𝔐.ξ (EE 𝔐) ((k : K₀) → J₀ k) (seg x₀)
    (LL 𝔐 (.inl τ)) (m (.inl τ)) (rk (CMType H) D.p D.q (.inl τ)) (n (.inl τ)) (VV 𝔐 (.inl τ)) (φ (.inl τ))
    (cc 𝔐 bW bO (.inl τ)) (hF.2.2.1 _) (hF.1 _) (hF.2.1 _).1 (hF.2.1 _).2 ⟨pr p'.1, hp⟩ c₁ hch
  let e : Fin (rk (CMType H) D.p D.q (.inl τ)) → 𝔐.Li := fun a => (bW τ a : 𝔐.Li)
  have hfrV : (𝔐.V (.inl τ)).IsFrameAt (colFrame e T) ⟨pr p'.1, hp⟩ := by
    refine isFrameAt_of_map _ (inW 𝔐) (GenBases.inW_injective 𝔐) _ _ ?_
    have h : (fun k => inW 𝔐 (colFrame e T k)) = colFrame (cc 𝔐 bW bO (.inl τ)) T := by
      funext k
      simp only [colFrame, map_sum, map_smul]
      rfl
    rw [h]
    exact hfr
  have hE := hO.2.2.2.1
  have hpull := FlagPull.pull_isFrameAt hO.1 hE p' hp hfrV
  rw [← hV (.inl τ), colFrame_semi hE.1] at hpull
  have he : LinearIndependent Ω e :=
    (bW τ).linearIndependent.map' (𝔐.Vgen (.inl τ)).subtype (Submodule.ker_subtype _)
  have hw := hE.2 _ e he
  have hb : Fl.b (.inl τ) = colFrame (fun a => j (e a)) (genU Ω (rk (CMType H) D.p D.q) (.inl τ)) := by
    funext k
    rw [hC.1 τ k, DetG.wBlock_gMat]
    rfl
  have hflag := Fl.sub (.inl τ)
  rw [hb] at hflag
  obtain ⟨U, Rm, Rm', hU, hRm, hRm', hR, hu, hgen⟩ := GlobalTheory.T.exists_triangular_regular_frame_change 𝔐'.X _ 𝔐'.ξ 𝔐'.Li (𝔐'.V (.inl τ))
    (rk (CMType H) D.p D.q (.inl τ)) (fun a => j (e a)) _ (genU Ω (rk (CMType H) D.p D.q) (.inl τ)) p' hw
    (by rw [DetG.det_genU]; exact isUnit_one) hpull hflag
  obtain ⟨C, h1, h2, h3⟩ := values_adapted (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) (regAt 𝔐'.ξ p')
    (aOf 𝔐 bW bO φ (.inl τ)) T C₀ (seg x₀ c₁ ^ m (.inl τ)) _ U Rm Rm' (fMat (aOf 𝔐 bW bO φ) (.inl τ)) rfl hu hRm hRm' hR
    (fun a b => LatModel.dominates_regAt hO.1 p' hp (hreg a b))
    (fun a b => LatModel.dominates_regAt hO.1 p' hp (hC₀r a b)) hinv
  refine ⟨U, C, hU, h1, h2, h3, fun l => ?_⟩
  rw [hb]
  exact hgen l

end Main

end GlobalTheory.CompanionTheory.Ar.PB.FMX.AdFrame
