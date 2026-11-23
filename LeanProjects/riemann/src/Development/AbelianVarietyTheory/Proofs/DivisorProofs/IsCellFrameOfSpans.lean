import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CokernelSubbundleIsVB
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCell

theorem form_pullCol {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B)
    (w : π ≫ q = p) {σ : k →+* ℂ} {E : B.Modules} {m : ℕ} (h : Met q σ E m) (cE : Chart E m) {W : Y.Opens}
    (hW : W ≤ π ⁻¹ᵁ cE.U) (M : Matrix (Fin m) (Fin m) Γ(Y, W)) {y : CxPts p σ} (hy : y ∈ ptsIn p σ W)
    (j l : Fin m) :
    (h.pull π w).form (pullCol π cE.e hW M j) (pullCol π cE.e hW M l) y =
      chg (Matrix.of fun a b => ev p σ W (M a b) y) (h.G cE (PtsOver.map π w (spMap σ) y)) j l := by
  have hc : y ∈ ptsIn p σ (π ⁻¹ᵁ cE.U) := mem_ptsIn.2 (hW (mem_ptsIn.1 hy))
  have hc' : PtsOver.map π w (spMap σ) y ∈ ptsIn q σ cE.U := hc
  have key (b : Fin m) : (cE.pull h.isVB π).crd p σ (pullCol π cE.e hW M b) y =
      fun a => ev p σ W (M a b) y := by
    funext a
    simp only [pullCol, Chart.crd_sum, Chart.crd_smul, cE.crd_pull h.isVB π w _ hW hy hc, cE.crd_frame hc',
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [(h.pull π w).form_eq (cE.pull h.isVB π) hc _ _ hy, h.pull_G π w cE hc', key, key, chg_apply]
  rfl

theorem Spans.exists_adaptedChart {X : Scheme.{0}} {F : X.Modules} {m : ℕ} {fl : Vert.Flag F m} {U : X.Opens}
    {v : Fin m → Γ(F, U)} (H : Spans fl U v) (i : Fin m) :
    ∃ (s : Fin i → Γ(fl.F i.castSucc, U)) (t : Fin 1 → Γ(fl.F i.succ, U)), IsFrame s ∧
      IsFrame (fun j => (fl.π i).app U (t j)) ∧
      ∀ j, (fl.ι i.succ).app U (Sum.elim (fun l => (fl.step i).app U (s l)) t j) = v (emb i j) := by
  obtain ⟨s, hs, es⟩ := H i.castSucc
  obtain ⟨s', hs', es'⟩ := H i.succ
  have e₁ (j : Fin i) : (fl.ι i.succ).app U ((fl.step i).app U (s j)) = v (Fin.castLE i.isLt.le j) := by
    refine Eq.trans ?_ (es j)
    rw [← fl.step_ι i]
    rfl
  refine ⟨s, fun j => s' (Fin.natAdd i j), hs,
    isFrame_cokernel_π (l := i) (m := 1) (fl.step i) hs' hs fun j => ?_, ?_⟩
  · exact QCoh.injective_app_of_mono (fl.ι i.succ) U ((e₁ j).trans (es' (Fin.castAdd 1 j)).symm)
  · rintro (j | j)
    · exact e₁ j
    · refine (es' _).trans (congrArg v (Fin.ext ?_))
      obtain rfl : j = 0 := Subsingleton.elim _ _
      rfl

theorem isCellFrame_of_spans : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (r : ι → ℕ) (d : ℕ) (e : Fin (d + 1) ≃ Option (Σ a, Low (r a))) (σ : k →+* ℂ) (a : ι) (E : B.Modules) (h : VMetric q E (r a)) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) (r a)) (cE : Chart E (r a)) (c' : AlgChart p σ (d + 1)) (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ cE.U) (n : Low (r a) → Γ(Y, W)), GlobalTheory.FlagCell.Spans fl W (GlobalTheory.FlagCell.pullCol π cE.e hW (GlobalTheory.FlagCell.uniR n)) → c'.e.source ⊆ ptsIn p σ W → (∀ y ∈ c'.e.source, ∀ s, fib e (c'.e y) a s = ev p σ W (n s) y) → IsCellFrame e π w c' a h fl cE := by
  intro k _ B Y q p π w ι _ r d e σ a E h fl cE c' W hW n H hs hn i
  obtain ⟨s, t, h₁, h₂, h₃⟩ := H.exists_adaptedChart i
  refine ⟨⟨W, s, t, h₁, h₂⟩, fun y hy => ⟨hs hy, ?_⟩⟩
  have hM : uni (fib e (c'.e y) a) = Matrix.of fun j l => ev p σ W (uniR n j l) y := by
    ext j l
    rw [← uniR_eq_uni, of_apply, uniR_apply, uniR_apply, ev_eq (hs hy)]
    split_ifs
    · rw [hn y hy, ev_eq (hs hy)]
    · exact (map_one _).symm
    · exact (map_zero _).symm
  ext j l
  rw [submatrix_apply, hM, ← form_pullCol π w (h.met σ) cE hW (uniR n) (hs hy), ← h₃, ← h₃]
  exact Met.form_restrict _ (fl.isSubbundle i.succ) (fl.isVB i.succ) _ _ (hs hy)

end GlobalTheory.FlagCell
