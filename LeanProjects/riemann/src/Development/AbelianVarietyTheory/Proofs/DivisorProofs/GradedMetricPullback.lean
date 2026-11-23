import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnRegularFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlag

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.MixDens GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Published
open scoped Classical

namespace GlobalTheory.OrthFilt

open GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.HermFrame Matrix

theorem form_pull_eq_zero {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ}
    (π : Y ⟶ X) (w : π ≫ p = q) {L A B : X.Modules} {g a b : ℕ} (h : Met p σ L g) (hA : IsVB A a) (hB : IsVB B b)
    (u : A ⟶ L) (v : B ⟶ L)
    (H : ∀ (V : X.Opens) (s : Γ(A, V)) (t : Γ(B, V)), ∀ y ∈ ptsIn p σ V, h.form (u.app V s) (v.app V t) y = 0)
    (V : Y.Opens) (s : Γ((Scheme.Modules.pullback π).obj A, V)) (t : Γ((Scheme.Modules.pullback π).obj B, V))
    (z : CxPts q σ) (hz : z ∈ ptsIn q σ V) :
    (h.pull π w).form (((Scheme.Modules.pullback π).map u).app V s) (((Scheme.Modules.pullback π).map v).app V t) z = 0 := by
  have h₀ := h.isVB.mem_pick (PtsOver.map π w _ z)
  have h₁ := hA.mem_pick (PtsOver.map π w _ z)
  have h₂ := hB.mem_pick (PtsOver.map π w _ z)
  generalize h.isVB.pick (PtsOver.map π w _ z) = c₀ at h₀
  generalize hA.pick (PtsOver.map π w _ z) = c₁ at h₁
  generalize hB.pick (PtsOver.map π w _ z) = c₂ at h₂
  rw [(h.pull π w).form_eq (c₀.pull h.isVB π) h₀ _ _ hz, Chart.crd_app _ (c₁.pull hA π) _ s hz h₁,
    Chart.crd_app _ (c₂.pull hB π) _ t hz h₂, HermFrame.form_mulVec, (h.pull_G π w c₀ h₀)]
  have e₁ (i : Fin a) : (c₀.pull h.isVB π).crd q σ
      (((Scheme.Modules.pullback π).map u).app (c₁.pull hA π).U ((c₁.pull hA π).e i)) z =
      c₀.crd p σ (u.app (c₁.U ⊓ c₂.U) (Twist.resM A inf_le_left (c₁.e i))) (PtsOver.map π w _ z) := by
    rw [Twist.app_resM, c₀.crd_resM _ _ (mem_ptsIn_inf.2 ⟨h₁, h₂⟩), ← c₀.crd_pull h.isVB π w _ le_rfl h₁ h₀,
      ← QCoh.pullback_map_app_pullbackSections]
    rfl
  have e₂ (i : Fin b) : (c₀.pull h.isVB π).crd q σ
      (((Scheme.Modules.pullback π).map v).app (c₂.pull hB π).U ((c₂.pull hB π).e i)) z =
      c₀.crd p σ (v.app (c₁.U ⊓ c₂.U) (Twist.resM B inf_le_right (c₂.e i))) (PtsOver.map π w _ z) := by
    rw [Twist.app_resM, c₀.crd_resM _ _ (mem_ptsIn_inf.2 ⟨h₁, h₂⟩), ← c₀.crd_pull h.isVB π w _ le_rfl h₂ h₀,
      ← QCoh.pullback_map_app_pullbackSections]
    rfl
  simp only [e₁, e₂]
  have key (M : Matrix (Fin g) (Fin a) ℂ) (N : Matrix (Fin g) (Fin b) ℂ) (K : Matrix (Fin g) (Fin g) ℂ)
      (e : ∀ i j, HermFrame.form K (fun l => M l i) (fun l => N l j) = 0) : Mᵀ * K * Nᴴᵀ = 0 := by
    ext i j
    have := HermFrame.form_mulVec K M N (Pi.single i 1) (Pi.single j 1)
    rw [mulVec_single_one, mulVec_single_one] at this
    have e' := (this.symm.trans (e i j))
    simpa [← Pi.single_star] using e'
  rw [key, zero_mulVec, dotProduct_zero]
  intro i j
  have hW := mem_ptsIn_inf.2 ⟨h₁, h₂⟩
  exact (h.form_eq c₀ h₀ _ _ hW).symm.trans (H _ _ _ _ hW)

theorem OrthEmb.pull {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (π : Y ⟶ X)
    (w : π ≫ p = q) {ι : Type} {L : X.Modules} {g : ℕ} {hL : VMetric p L g} {E : ι → X.Modules} {r : ι → ℕ}
    {h : ∀ a, VMetric p (E a) (r a)} {T : ∀ a, E a ⟶ L} (H : OrthEmb hL h T) :
    OrthEmb (hL.pull π w) (fun a => (h a).pull π w) fun a => (Scheme.Modules.pullback π).map (T a) := by
  refine ⟨fun a σ V s t z hz => ?_, fun a b hab σ V s t z hz =>
    form_pull_eq_zero π w (hL.met σ) (h a).isVB (h b).isVB _ _ (H.2 a b hab σ) V s t z hz⟩
  have hc := ((h a).met σ).isVB.mem_pick (PtsOver.map π w _ z)
  refine form_app_of_gram (Chart.pull _ ((h a).met σ).isVB π) hc ?_ s t hz
  refine Eq.trans ?_ (((h a).met σ).pull_G π w _ hc).symm
  ext i j
  rw [← ((h a).met σ).form_frame _ hc, ← H.1 a σ _ _ _ _ hc, ← (hL.met σ).form_pull π w _ _ le_rfl hc,
    ← QCoh.pullback_map_app_pullbackSections, ← QCoh.pullback_map_app_pullbackSections]
  rfl

theorem isGraded_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (π : Y ⟶ X) (w : π ≫ p = q) (ι : Type) (L : X.Modules) (g : ℕ) (hL : VMetric p L g) (E E' : ι → X.Modules) (r : ι → ℕ) (h : ∀ a, VMetric p (E a) (r a)) (u : ∀ a, E a ⟶ E' a) (m : ℕ) (o : ι ≃ Fin m), (∀ a, IsVB (E' a) (r a)) → IsGraded hL o h u → IsGraded (E' := fun a => (Scheme.Modules.pullback π).obj (E' a)) (hL.pull π w) o (fun a => (h a).pull π w) fun a => (Scheme.Modules.pullback π).map (u a) := by
  intro k _ X Y p q π w ι L g hL E E' r h u m o hE' ⟨F, j, s, κ, t, z, hj, h0, hl, hs, hS, ht, hO⟩
  refine ⟨fun i => (Scheme.Modules.pullback π).obj (F i), fun i => (Scheme.Modules.pullback π).map (j i),
    fun i => (Scheme.Modules.pullback π).map (s i), fun a => (Scheme.Modules.pullback π).map (κ a),
    fun a => (Scheme.Modules.pullback π).map (t a),
    fun a => ((ShortComplex.mk _ _ (z a)).map (Scheme.Modules.pullback π)).zero, fun i => ?_,
    (Scheme.Modules.pullback π).map_isZero h0, inferInstance, fun i => ?_, fun a => ?_, fun a => ?_, ?_⟩
  · obtain ⟨h₁, n, h₂⟩ := hj i
    exact ⟨SubPull.isSubbundle_pullback X Y π _ _ _ n h₂ h₁, n, h₂.pullback π⟩
  · rw [← Functor.map_comp, hs]
  · obtain ⟨-, n, h₁⟩ := hj (o a).castSucc
    obtain ⟨-, n', h₂⟩ := hj (o a).succ
    have := (hS a).epi_g
    haveI : (ShortComplex.mk _ _ (z a)).X₁.IsQuasicoherent := h₁.isQuasicoherent
    haveI : (ShortComplex.mk _ _ (z a)).X₂.IsQuasicoherent := h₂.isQuasicoherent
    exact ShortComplex.ShortExact.mk' (S := (ShortComplex.mk _ _ (z a)).map (Scheme.Modules.pullback π))
      (QCoh.exact_map_pullback π (hS a).exact).1
      (FlagPull.mono_pullback_map_f π _ (hS a) (hE' a)) (QCoh.exact_map_pullback π (hS a).exact).2
  · rw [← Functor.map_comp, ht]
  · simpa only [Functor.map_comp] using hO.pull π w

end GlobalTheory.OrthFilt

end
