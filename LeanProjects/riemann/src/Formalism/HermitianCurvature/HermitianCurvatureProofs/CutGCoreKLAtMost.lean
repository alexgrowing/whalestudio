import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTKLineCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ProductIntervalFrames
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieBracketMultiplication
import Lemmata.GeneralBFactSecondAltForm.Imports

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLAM

section LinAlg

theorem prod_act {W ι : Type*} [AddCommGroup W] [Module ℂ W] (F : ι → W →ₗ[ℂ] W) (c : ι → ℂ) {w : W}
    (hw : ∀ τ, F τ w = c τ • w) (l : List ι) : (l.map F).prod w = (l.map c).prod • w := by
  induction l with
  | nil => simp
  | cons τ l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, map_smul, hw τ, smul_smul, List.map_cons,
      List.prod_cons, mul_comm]

def projL {W ι : Type*} [AddCommGroup W] [Module ℂ W] (C : ℂ → W →ₗ[ℂ] W) (x : ι → ℂ → ℂ) (Y : ι → ℂ)
    (l : List ι) : W →ₗ[ℂ] W :=
  (l.map fun τ => C (Y τ) - x τ (Y τ) • (1 : W →ₗ[ℂ] W)).prod

theorem projL_eig {W ι : Type*} [AddCommGroup W] [Module ℂ W] (C : ℂ → W →ₗ[ℂ] W) (x : ι → ℂ → ℂ) (Y : ι → ℂ)
    (l : List ι) (μ : ℂ → ℂ) {w : W} (hw : ∀ Y', C Y' w = μ Y' • w) :
    projL C x Y l w = (l.map fun τ => μ (Y τ) - x τ (Y τ)).prod • w := by
  unfold projL
  refine prod_act _ _ (fun τ => ?_) l
  rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hw, sub_smul]

theorem eig_zero {W ι : Type*} [AddCommGroup W] [Module ℂ W] [Fintype ι] (S : ι → Submodule ℂ W)
    (hS : ⨆ τ, S τ = ⊤) (C : ℂ → W →ₗ[ℂ] W) (x : ι → ℂ → ℂ) (hC : ∀ τ Y, ∀ w ∈ S τ, C Y w = x τ Y • w)
    (μ : ℂ → ℂ) (hsep : ∀ τ, ∃ Y, x τ Y ≠ μ Y) {u : W} (hu : ∀ Y, C Y u = μ Y • u) : u = 0 := by
  classical
  choose Y hY using hsep
  set l := (Finset.univ : Finset ι).toList with hl
  have hzero : ∀ w, projL C x Y l w = 0 := by
    intro w
    have hw : w ∈ ⨆ τ, S τ := by rw [hS]; trivial
    induction hw using Submodule.iSup_induction' with
    | mem τ' w hw =>
      rw [projL_eig C x Y l (x τ') (fun Y' => hC τ' Y' w hw)]
      have : (l.map fun τ => x τ' (Y τ) - x τ (Y τ)).prod = 0 := by
        apply List.prod_eq_zero
        rw [List.mem_map]
        exact ⟨τ', by simp [hl], by simp⟩
      rw [this, zero_smul]
    | zero => exact map_zero _
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  have h1 := projL_eig C x Y l μ hu
  rw [hzero] at h1
  have hp : (l.map fun τ => μ (Y τ) - x τ (Y τ)).prod ≠ 0 := by
    apply List.prod_ne_zero
    rw [List.mem_map]
    rintro ⟨τ, -, h0⟩
    exact hY τ (sub_eq_zero.1 h0).symm
  exact (smul_eq_zero.1 h1.symm).resolve_left hp

theorem eig_mem {W ι : Type*} [AddCommGroup W] [Module ℂ W] [Fintype ι] [DecidableEq ι] (S : ι → Submodule ℂ W)
    (hS : ⨆ τ, S τ = ⊤) (C : ℂ → W →ₗ[ℂ] W) (x : ι → ℂ → ℂ) (hC : ∀ τ Y, ∀ w ∈ S τ, C Y w = x τ Y • w)
    (σ : ι) (hsep : ∀ τ, τ ≠ σ → ∃ Y, x τ Y ≠ x σ Y) {u : W} (hu : ∀ Y, C Y u = x σ Y • u) : u ∈ S σ := by
  have hsep' : ∀ τ : {τ // τ ≠ σ}, ∃ Y, x τ.1 Y ≠ x σ Y := fun τ => hsep τ.1 τ.2
  choose Y hY using hsep'
  let Yf : ι → ℂ := fun τ => if h : τ = σ then 0 else Y ⟨τ, h⟩
  set l := ((Finset.univ : Finset ι).erase σ).toList with hl
  have hmem : ∀ w, projL C x Yf l w ∈ S σ := by
    intro w
    have hw : w ∈ ⨆ τ, S τ := by rw [hS]; trivial
    induction hw using Submodule.iSup_induction' with
    | mem τ' w hw =>
      rw [projL_eig C x Yf l (x τ') (fun Y' => hC τ' Y' w hw)]
      by_cases hτ : τ' = σ
      · subst hτ
        exact Submodule.smul_mem _ _ hw
      · have : (l.map fun τ => x τ' (Yf τ) - x τ (Yf τ)).prod = 0 := by
          apply List.prod_eq_zero
          rw [List.mem_map]
          exact ⟨τ', by simp [hl, hτ], by simp⟩
        rw [this, zero_smul]
        exact Submodule.zero_mem _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  have h1 := projL_eig C x Yf l (x σ) hu
  have hp : (l.map fun τ => x σ (Yf τ) - x τ (Yf τ)).prod ≠ 0 := by
    apply List.prod_ne_zero
    rw [List.mem_map]
    rintro ⟨τ, hτl, h0⟩
    have hτ : τ ≠ σ := by
      have := (Finset.mem_toList.1 hτl)
      exact (Finset.mem_erase.1 this).1
    have hYf : Yf τ = Y ⟨τ, hτ⟩ := by simp [Yf, hτ]
    rw [hYf] at h0
    exact hY ⟨τ, hτ⟩ (sub_eq_zero.1 h0).symm
  have h2 : u = ((l.map fun τ => x σ (Yf τ) - x τ (Yf τ)).prod)⁻¹ • projL C x Yf l u := by
    rw [h1, smul_smul, inv_mul_cancel₀ hp, one_smul]
  rw [h2]
  exact Submodule.smul_mem _ _ (hmem u)

theorem schur_core {Wq Wp : Type*} [AddCommGroup Wq] [Module ℂ Wq] [FiniteDimensional ℂ Wq]
    [AddCommGroup Wp] [Module ℂ Wp] [FiniteDimensional ℂ Wp]
    (S' : Submodule ℂ Wq) (S : Submodule ℂ Wp) (Gq : Set (Module.End ℂ Wq)) (Gp : Set (Module.End ℂ Wp))
    (hirr' : ∀ K : Submodule ℂ Wq, K ≤ S' → (∀ A ∈ Gq, ∀ v ∈ K, A v ∈ K) → K = ⊥ ∨ K = S')
    (hirr : ∀ K : Submodule ℂ Wp, K ≤ S → (∀ B ∈ Gp, ∀ w ∈ K, B w ∈ K) → K = ⊥ ∨ K = S)
    (hst : ∀ A ∈ Gq, ∀ v ∈ S', A v ∈ S')
    (E Z : Wq →ₗ[ℂ] Wp) (hES : ∀ v ∈ S', E v ∈ S) (hZS : ∀ v ∈ S', Z v ∈ S)
    (hq : ∀ A ∈ Gq, ∃ B : Module.End ℂ Wp, E ∘ₗ A = B ∘ₗ E ∧ Z ∘ₗ A = B ∘ₗ Z)
    (hp : ∀ B ∈ Gp, ∃ A ∈ Gq, E ∘ₗ A = B ∘ₗ E)
    (hne : ∃ v ∈ S', E v ≠ 0) :
    ∃ c : ℂ, ∀ v ∈ S', Z v = c • E v := by
  first | exact Bl.general_b_fact_second_alt_form.goal1 .. | (apply Bl.general_b_fact_second_alt_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_alt_form.goal1 <;> assumption)

end LinAlg

section Geo

open Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx8

variable {k r : ℕ}

theorem inv_mul_uh {g : Q.Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ * g = 1 :=
  Matrix.nonsing_inv_mul _ (WeylGroupFacts.isUnit_of_uh hg)

theorem mul_inv_uh {g : Q.Mx k r} (hg : g ∈ UH (Hpk k r)) : g * g⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh hg)

theorem geom_fr {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r))
    (hne : Q.GGl k r z z' g ≠ 0) {m : ℕ} {Fr : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hFr : Q.IsFrameOf k r [g⁻¹ *ᵥ z, z'] Fr) :
    ∃ (e' f : Fin (2 * r + k + 1) → ℂ) (s c s₂ c₂ : ℂ), s ≠ 0 ∧ s₂ ≠ 0 ∧
      e' = s • (g⁻¹ *ᵥ z + c • z') ∧ f = s₂ • (z' + c₂ • (g⁻¹ *ᵥ z)) ∧
      (inWb k r e' ∧ herm (Hpk k r) e' z' = 0 ∧ herm (Hpk k r) e' e' = 1) ∧
      (inWb k r (g *ᵥ f) ∧ herm (Hpk k r) (g *ᵥ f) z = 0 ∧ herm (Hpk k r) (g *ᵥ f) (g *ᵥ f) = 1) ∧
      Q.IsFrameOf k r [z', e'] Fr ∧ Q.IsFrameOf k r [z, g *ᵥ f] (fun a => g *ᵥ Fr a) := by
  have hpos := GGl_pos hz hz' hT hT' hg hne
  set y := g⁻¹ *ᵥ z with hy
  have hgy : g *ᵥ y = z := inv_mulVec_uh hg.1 z
  have hginv : g⁻¹ ∈ Q.Glev k r (Fin.last r) := by
    refine ⟨WeylGroupFacts.uh_inv hg.1, fun a ha => ⟨?_, ?_⟩⟩
    · conv_lhs => rw [← (hg.2 a ha).1]
      rw [Matrix.mulVec_mulVec, inv_mul_uh hg.1, Matrix.one_mulVec]
    · conv_lhs => rw [← (hg.2 a ha).2]
      rw [Matrix.mulVec_mulVec, inv_mul_uh hg.1, Matrix.one_mulVec]
  have hyW : inWb k r y := inWb_mulVec hginv hz
  have hyy : herm (Hpk k r) y y = -((Tz k r z : ℝ) : ℂ) := by
    rw [← herm_self', ← hgy, herm_UH hg.1]
  have hζ : herm (Hpk k r) z' y = Q.zetaL k r z z' (Fin.last r) g := by
    unfold Q.zetaL
    rw [fvec_last, fvec_last, ← hgy, herm_UH hg.1]
  have hG1 : 0 < Complex.normSq (herm (Hpk k r) z' y) - Tz k r z' * Tz k r z := by
    rw [hζ, mul_comm]; exact hpos
  have hG2 : 0 < Complex.normSq (herm (Hpk k r) y z') - Tz k r z * Tz k r z' := by
    rw [← herm_conj, hζ]
    have : Complex.normSq (star (Q.zetaL k r z z' (Fin.last r) g)) =
        Complex.normSq (Q.zetaL k r z z' (Fin.last r) g) := Complex.normSq_conj _
    rw [this]; exact hpos
  obtain ⟨e', s, c, hs, he', he'W, he'z, he'e⟩ := orth_unit hyW hz' hT' hyy (herm_self' z') hG2
  obtain ⟨f, s₂, c₂, hs₂, hf, hfW, hfy, hff⟩ := orth_unit hz' hyW hT (herm_self' z') hyy hG1
  have hBz : ∀ a, herm (Hpk k r) (Fr a) z' = 0 := fun a => hFr.2.2 a z' (by simp)
  have hBy : ∀ a, herm (Hpk k r) (Fr a) y = 0 := fun a => hFr.2.2 a y (by simp)
  have hBe : ∀ a, herm (Hpk k r) (Fr a) e' = 0 := by
    intro a
    rw [he', herm_smul_right', herm_add_right', herm_smul_right', hBz, hBy]; simp
  have hBf : ∀ a, herm (Hpk k r) (Fr a) f = 0 := by
    intro a
    rw [hf, herm_smul_right', herm_add_right', herm_smul_right', hBz, hBy]; simp
  refine ⟨e', f, s, c, s₂, c₂, hs, hs₂, he', hf, ⟨he'W, he'z, he'e⟩, ⟨inWb_mulVec hg hfW, ?_, ?_⟩, ⟨hFr.1, hFr.2.1, ?_⟩,
    ⟨fun a => inWb_mulVec hg (hFr.1 a), ?_, ?_⟩⟩
  · rw [← hgy, herm_UH hg.1, hfy]
  · rw [herm_UH hg.1, hff]
  · intro a v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hBz a
    · exact hBe a
  · intro a b
    rw [herm_UH hg.1]; exact hFr.2.1 a b
  · intro a v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · conv_lhs => rw [← hgy]
      rw [herm_UH hg.1]; exact hBy a
    · rw [herm_UH hg.1]; exact hBf a

theorem conj_uw {z z' : Fin (2 * r + k + 1) → ℂ} {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r))
    {h' : Q.Mx k r} (hh' : h' ∈ UWset k r z') (hy : h' *ᵥ (g⁻¹ *ᵥ z) = g⁻¹ *ᵥ z) :
    g * h' * g⁻¹ ∈ UWset k r z := by
  have hginv : g⁻¹ * g = 1 := inv_mul_uh hg.1
  have hgi : g⁻¹ ∈ UH (Hpk k r) := WeylGroupFacts.uh_inv hg.1
  refine ⟨WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul hg.1 hh'.1) hgi, fun c => ?_, ?_⟩
  · have hc := hg.2 c (by simp)
    have i1 : g⁻¹ *ᵥ bvec (eI k r c) = bvec (eI k r c) := by
      conv_lhs => rw [← hc.1]
      rw [Matrix.mulVec_mulVec, hginv, Matrix.one_mulVec]
    have i2 : g⁻¹ *ᵥ bvec (esI k r c) = bvec (esI k r c) := by
      conv_lhs => rw [← hc.2]
      rw [Matrix.mulVec_mulVec, hginv, Matrix.one_mulVec]
    constructor
    · rw [← Matrix.mulVec_mulVec, i1, ← Matrix.mulVec_mulVec, (hh'.2.1 c).1, hc.1]
    · rw [← Matrix.mulVec_mulVec, i2, ← Matrix.mulVec_mulVec, (hh'.2.1 c).2, hc.2]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hy, inv_mulVec_uh hg.1]

end Geo

section Fib

open Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx8

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]

theorem fib_intertwine {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} (hrep : IsCRepOn (UWset k r z) π) {g : Q.Mx k r}
    (hg : g ∈ Q.Glev k r (Fin.last r)) {X : Wq →L[ℂ] Wp} (hX : X ∈ FibAt k r z z' π π' g)
    {h' : Q.Mx k r} (hh' : h' ∈ UWset k r z') (hy : h' *ᵥ (g⁻¹ *ᵥ z) = g⁻¹ *ᵥ z) (v : Wq) :
    X (π' h' v) = π (g * h' * g⁻¹) (X v) := by
  have hh'i : h'⁻¹ ∈ UWset k r z' := LieBracketMultiplication.uw_inv hh'
  have hyi : h'⁻¹ *ᵥ (g⁻¹ *ᵥ z) = g⁻¹ *ᵥ z := by
    conv_lhs => rw [← hy]
    rw [Matrix.mulVec_mulVec, inv_mul_uh hh'.1, Matrix.one_mulVec]
  have hh : g * h'⁻¹ * g⁻¹ ∈ UWset k r z := conj_uw hg hh'i hyi
  have hc : g * h' * g⁻¹ ∈ UWset k r z := conj_uw hg hh' hy
  have hgg : g * h'⁻¹ * g⁻¹ * g * h' = g := by
    rw [Matrix.mul_assoc (g * h'⁻¹) g⁻¹ g, inv_mul_uh hg.1, Matrix.mul_one, Matrix.mul_assoc, inv_mul_uh hh'.1,
      Matrix.mul_one]
  have hfib := hX _ hh h' hh' hgg
  have hone : g * h' * g⁻¹ * (g * h'⁻¹ * g⁻¹) = 1 := by
    rw [show g * h' * g⁻¹ * (g * h'⁻¹ * g⁻¹) = g * h' * (g⁻¹ * g) * h'⁻¹ * g⁻¹ by
      simp only [Matrix.mul_assoc], inv_mul_uh hg.1, Matrix.mul_one, Matrix.mul_assoc g h' h'⁻¹, mul_inv_uh hh'.1,
      Matrix.mul_one, mul_inv_uh hg.1]
  have hπ1 : (π (g * h' * g⁻¹)).comp (π (g * h'⁻¹ * g⁻¹)) = 1 := by
    rw [← hrep.2 _ hc _ hh, hone, hrep.1]
  calc X (π' h' v) = (π (g * h' * g⁻¹)).comp (π (g * h'⁻¹ * g⁻¹)) (X (π' h' v)) := by rw [hπ1]; rfl
    _ = π (g * h' * g⁻¹) ((π (g * h'⁻¹ * g⁻¹)).comp (X.comp (π' h')) v) := rfl
    _ = π (g * h' * g⁻¹) (X v) := by rw [hfib]

end Fib

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLAM

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

open Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx8

theorem lie_weight_at_most_holds : KLAtMost := by
  classical
  intro Wp Wq _ _ _ _ _ _ P z z' π π' hPl hk g hg hGG Fr hFr ρ E Z hEf hZf hEe hZe hEn
  obtain ⟨hOK, hz, hz', hTz, hTz', hπ, hπ'⟩ := id hPl
  obtain ⟨-, hrep, hcont, -, -, -⟩ := id hπ
  obtain ⟨-, hrep', hcont', -, -, -⟩ := id hπ'
  have hT : 0 < Tz P.k P.r z := by rw [hTz]; exact hOK.T_pos
  have hT' : 0 < Tz P.k P.r z' := by rw [hTz']; exact hOK.T'_pos
  obtain ⟨e', f, s, c, s₂, c₂, hs, hs₂, he', hf, ⟨he1, he2, he3⟩, ⟨hf1, hf2, hf3⟩, hFe, hFf⟩ :=
    KLAM.geom_fr hz hz' hT hT' hg hGG hFr
  have hBr : Q.Branching := qr_branching_of branching_compact
  obtain ⟨S', hInt', hirr', hcap'⟩ := hBr Wq (P1 P) (first_projection_preserves_ok hOK) rfl z' e' π' hz' hT' hπ' he1 he2 he3
  obtain ⟨S, hInt, hirr, hcap⟩ := hBr Wp (P2 P) (second_projection_preserves_ok hOK) rfl z (g *ᵥ f) π hz hT hπ hf1 hf2 hf3
  have hgl' := (frame_general_linear Wq P.k P.r (P.k - 1) z' π' Fr ⟨hrep', hcont'⟩ (frame_sub hFr (by simp))).2
  have hgl := (frame_general_linear Wp P.k P.r (P.k - 1) z π (fun a => g *ᵥ Fr a) ⟨hrep, hcont⟩
    (frame_sub hFf (by simp))).2

  have hC' : ∀ (σ : M.Ty (P1 P)) (Y : ℂ), ∀ v ∈ S' σ,
      qdet (Qr.EB π' Fr) (Y + ((P.k : ℂ) - 2) / 2) v = M.xC (P1 P) σ Y • v := by
    intro σ Y v hv
    rw [← hgl']
    have := hcap' Fr hFe σ (Y + ((P.k : ℂ) - 2) / 2) v hv
    rw [show Y + ((P.k : ℂ) - 2) / 2 - (((P1 P).k : ℂ) - 2) / 2 = Y from add_sub_cancel_right _ _] at this
    exact this
  have hC : ∀ (τ : M.Ty (P2 P)) (Y : ℂ), ∀ w ∈ S τ,
      qdet (Qr.EB π (fun a => g *ᵥ Fr a)) (Y + ((P.k : ℂ) - 2) / 2) w = M.xC (P2 P) τ Y • w := by
    intro τ Y w hw
    rw [← hgl]
    have := hcap (fun a => g *ᵥ Fr a) hFf τ (Y + ((P.k : ℂ) - 2) / 2) w hw
    rw [show Y + ((P.k : ℂ) - 2) / 2 - (((P2 P).k : ℂ) - 2) / 2 = Y from add_sub_cancel_right _ _] at this
    exact this

  have hCX : ∀ X ∈ FibAt P.k P.r z z' π π' g, ∀ (Y : ℂ) (v : Wq),
      X (qdet (Qr.EB π' Fr) (Y + ((P.k : ℂ) - 2) / 2) v) =
        qdet (Qr.EB π (fun a => g *ᵥ Fr a)) (Y + ((P.k : ℂ) - 2) / 2) (X v) := by
    intro X hX Y v
    rw [← hgl', ← hgl]
    exact capRep_intertwine hFr hrep' hcont' hg.1 X
      (fun h' hh' hy v => KLAM.fib_intertwine hrep hg hX hh' hy v) _ v

  obtain ⟨Y1, hY1⟩ := Formalism.FourierDecayAlt.P5.Kfp.sep_real (first_projection_preserves_ok hOK)
  obtain ⟨Y2, hY2⟩ := Formalism.FourierDecayAlt.P5.Kfp.sep_real (second_projection_preserves_ok hOK)
  have sep1 : ∀ σ σ' : M.Ty (P1 P), σ ≠ σ' → ∃ Y, M.xC (P1 P) σ Y ≠ M.xC (P1 P) σ' Y :=
    fun σ σ' h => ⟨(Y1 : ℂ), fun h0 => h (hY1 h0)⟩
  have sep2 : ∀ τ τ' : M.Ty (P2 P), τ ≠ τ' → ∃ Y, M.xC (P2 P) τ Y ≠ M.xC (P2 P) τ' Y :=
    fun τ τ' h => ⟨(Y2 : ℂ), fun h0 => h (hY2 h0)⟩

  have hkill : ∀ X : Wq →L[ℂ] Wp, CapEig P π' Fr ρ X → ∀ σ : M.Ty (P1 P),
      (∃ Y, M.xC (P1 P) σ Y ≠ M.xC P ρ Y) → ∀ v ∈ S' σ, X v = 0 := by
    intro X hX σ ⟨Y, hY⟩ v hv
    have h1 := hX Y v
    rw [hC' σ Y v hv, map_smul] at h1
    have h2 : (M.xC (P1 P) σ Y - M.xC P ρ Y) • X v = 0 := by rw [sub_smul, h1, sub_self]
    exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hY)
  have htop' : ⨆ σ, S' σ = ⊤ := hInt'.submodule_iSup_eq_top
  have htop : ⨆ τ, S τ = ⊤ := hInt.submodule_iSup_eq_top

  obtain ⟨σ0, v0, hv0, hEv0⟩ : ∃ σ0, ∃ v ∈ S' σ0, E v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hEn
    ext v
    have hv : v ∈ ⨆ σ, S' σ := by rw [htop']; trivial
    induction hv using Submodule.iSup_induction' with
    | mem σ w hw => simpa using hcon σ w hw
    | zero => simp
    | add a b _ _ ha hb => simp only [map_add, ContinuousLinearMap.zero_apply] at ha hb ⊢; rw [ha, hb, add_zero]
  have hx0 : ∀ Y, M.xC (P1 P) σ0 Y = M.xC P ρ Y := by
    by_contra h
    push Not at h
    exact hEv0 (hkill E hEe σ0 h v0 hv0)

  have hstab : ∀ σ : M.Ty (P1 P), ∀ h0 ∈ UWset P.k P.r z', h0 *ᵥ e' = e' → ∀ v ∈ S' σ, π' h0 v ∈ S' σ := by
    intro σ h0 hh0 he0 v hv
    have hFe2 : Q.IsFrameOf P.k P.r [e', z'] Fr := frame_sub hFe (by simp)
    have hF0 : Q.IsFrameOf P.k P.r [z', e'] (fun a => h0 *ᵥ Fr a) := by
      refine ⟨fun a => inWb_mulVec (uw_glev (Fin.last P.r) hh0) (hFe.1 a), fun a b => ?_, fun a w hw => ?_⟩
      · rw [herm_UH hh0.1]; exact hFe.2.1 a b
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · rw [← hh0.2.2, herm_UH hh0.1]; exact hFe.2.2 a _ (by simp)
        · rw [← he0, herm_UH hh0.1]; exact hFe.2.2 a _ (by simp)
    have hgl0 := (frame_general_linear Wq P.k P.r (P.k - 1) z' π' (fun a => h0 *ᵥ Fr a) ⟨hrep', hcont'⟩
      (frame_sub hF0 (by simp))).2
    have hmov : ∀ (w : ℂ) (x : Wq), π' h0 (capRep P.k P.r π' Fr w x) =
        capRep P.k P.r π' (fun a => h0 *ᵥ Fr a) w (π' h0 x) := by
      intro w x
      refine capRep_intertwine hFe2 hrep' hcont' hh0.1 (π' h0) (fun h' hh' _ u => ?_) w x
      have hc : h0 * h' * h0⁻¹ ∈ UWset P.k P.r z' := LieBracketMultiplication.uw_mul (LieBracketMultiplication.uw_mul hh0 hh') (LieBracketMultiplication.uw_inv hh0)
      have e1 : h0 * h' * h0⁻¹ * h0 = h0 * h' := by
        rw [Matrix.mul_assoc, KLAM.inv_mul_uh hh0.1, Matrix.mul_one]
      have := hrep'.2 _ hc _ hh0
      rw [e1, hrep'.2 _ hh0 _ hh'] at this
      have e2 := congrArg (fun L : Wq →L[ℂ] Wq => L u) this
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at e2
      exact e2
    refine KLAM.eig_mem S' htop' (fun Y => qdet (Qr.EB π' (fun a => h0 *ᵥ Fr a)) (Y + ((P.k : ℂ) - 2) / 2))
      (fun τ => M.xC (P1 P) τ) (fun τ Y w hw => ?_) σ (fun τ h => sep1 τ σ h) (fun Y => ?_)
    · rw [← hgl0]
      have := hcap' (fun a => h0 *ᵥ Fr a) hF0 τ (Y + ((P.k : ℂ) - 2) / 2) w hw
      rw [show Y + ((P.k : ℂ) - 2) / 2 - (((P1 P).k : ℂ) - 2) / 2 = Y from add_sub_cancel_right _ _] at this
      exact this
    · show qdet (Qr.EB π' (fun a => h0 *ᵥ Fr a)) (Y + ((P.k : ℂ) - 2) / 2) (π' h0 v) = _
      rw [← hgl0, ← hmov, hgl', hC' σ Y v hv, map_smul]

  have heigE : ∀ X ∈ FibAt P.k P.r z z' π π' g, ∀ v ∈ S' σ0, ∀ Y,
      qdet (Qr.EB π (fun a => g *ᵥ Fr a)) (Y + ((P.k : ℂ) - 2) / 2) (X v) = M.xC (P1 P) σ0 Y • X v := by
    intro X hX v hv Y
    rw [← hCX X hX, hC' σ0 Y v hv, map_smul]
  obtain ⟨τ0, hτ0⟩ : ∃ τ0 : M.Ty (P2 P), ∀ Y, M.xC (P2 P) τ0 Y = M.xC (P1 P) σ0 Y := by
    by_contra h
    push Not at h
    exact hEv0 (KLAM.eig_zero S htop
      (fun Y => qdet (Qr.EB π (fun a => g *ᵥ Fr a)) (Y + ((P.k : ℂ) - 2) / 2)) (fun τ => M.xC (P2 P) τ)
      (fun τ Y w hw => hC τ Y w hw) (M.xC (P1 P) σ0) h (heigE E hEf v0 hv0))
  have hmemS : ∀ X ∈ FibAt P.k P.r z z' π π' g, ∀ v ∈ S' σ0, X v ∈ S τ0 := by
    intro X hX v hv
    refine KLAM.eig_mem S htop (fun Y => qdet (Qr.EB π (fun a => g *ᵥ Fr a)) (Y + ((P.k : ℂ) - 2) / 2))
      (fun τ => M.xC (P2 P) τ) (fun τ Y w hw => hC τ Y w hw) τ0 (fun τ h => sep2 τ τ0 h) (fun Y => ?_)
    show _ = M.xC (P2 P) τ0 Y • X v
    rw [hτ0 Y]
    exact heigE X hX v hv Y

  have hfix_y : ∀ h' : Q.Mx P.k P.r, h' *ᵥ z' = z' → h' *ᵥ e' = e' → h' *ᵥ (g⁻¹ *ᵥ z) = g⁻¹ *ᵥ z := by
    intro h' hz'h he'h
    have h1 : h' *ᵥ e' = s • (h' *ᵥ (g⁻¹ *ᵥ z) + c • z') := by
      rw [he', Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, hz'h]
    rw [he'h, he'] at h1
    have h2 := smul_right_injective _ hs h1
    exact (add_right_cancel h2).symm

  obtain ⟨c0, hc0⟩ := KLAM.schur_core (S' σ0) (S τ0)
    ((fun h => (π' h : Wq →ₗ[ℂ] Wq)) '' {h | h ∈ UWset P.k P.r z' ∧ h *ᵥ e' = e'})
    ((fun h => (π h : Wp →ₗ[ℂ] Wp)) '' {h | h ∈ UWset P.k P.r z ∧ h *ᵥ (g *ᵥ f) = g *ᵥ f})
    (fun K hK hst => (hirr' σ0).2 K hK (fun h hh he v hv => hst _ ⟨h, ⟨hh, he⟩, rfl⟩ v hv))
    (fun K hK hst => (hirr τ0).2 K hK (fun h hh he v hv => hst _ ⟨h, ⟨hh, he⟩, rfl⟩ v hv))
    (fun A hA v hv => by
      obtain ⟨h, ⟨hh, he⟩, rfl⟩ := hA
      exact hstab σ0 h hh he v hv)
    (E : Wq →ₗ[ℂ] Wp) (Z : Wq →ₗ[ℂ] Wp) (fun v hv => hmemS E hEf v hv) (fun v hv => hmemS Z hZf v hv)
    (fun A hA => by
      obtain ⟨h, ⟨hh, he⟩, rfl⟩ := hA
      have hy := hfix_y h hh.2.2 he
      refine ⟨(π (g * h * g⁻¹) : Wp →ₗ[ℂ] Wp), ?_, ?_⟩
      · ext v
        exact KLAM.fib_intertwine hrep hg hEf hh hy v
      · ext v
        exact KLAM.fib_intertwine hrep hg hZf hh hy v)
    (fun B hB => by
      obtain ⟨h, ⟨hh, he⟩, rfl⟩ := hB
      set h' := g⁻¹ * h * g with hh'def
      have hgi : g⁻¹ ∈ UH (Hpk P.k P.r) := WeylGroupFacts.uh_inv hg.1
      have hyy : h' *ᵥ (g⁻¹ *ᵥ z) = g⁻¹ *ᵥ z := by
        rw [hh'def, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, inv_mulVec_uh hg.1, hh.2.2]
      have hff : h' *ᵥ f = f := by
        rw [hh'def, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, he, Matrix.mulVec_mulVec, KLAM.inv_mul_uh hg.1,
          Matrix.one_mulVec]
      have hz'f : z' = s₂⁻¹ • f - c₂ • (g⁻¹ *ᵥ z) := by
        rw [hf, smul_smul, inv_mul_cancel₀ hs₂, one_smul, add_sub_cancel_right]
      have hzz : h' *ᵥ z' = z' := by
        conv_lhs => rw [hz'f]
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hff, hyy, ← hz'f]
      have hee : h' *ᵥ e' = e' := by
        rw [he', Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, hyy, hzz]
      have hgl' : g⁻¹ ∈ Q.Glev P.k P.r (Fin.last P.r) := ⟨hgi, fun a ha => ⟨by
          conv_lhs => rw [← (hg.2 a ha).1]
          rw [Matrix.mulVec_mulVec, KLAM.inv_mul_uh hg.1, Matrix.one_mulVec], by
          conv_lhs => rw [← (hg.2 a ha).2]
          rw [Matrix.mulVec_mulVec, KLAM.inv_mul_uh hg.1, Matrix.one_mulVec]⟩⟩
      have hlev := glev_mul (glev_mul hgl' (uw_glev (Fin.last P.r) hh)) hg
      have hmem : h' ∈ UWset P.k P.r z' := ⟨hlev.1, fun a => hlev.2 a (by simp), hzz⟩
      refine ⟨(π' h' : Wq →ₗ[ℂ] Wq), ⟨h', ⟨hmem, hee⟩, rfl⟩, ?_⟩
      have hconj : g * h' * g⁻¹ = h := by
        rw [hh'def, show g * (g⁻¹ * h * g) * g⁻¹ = (g * g⁻¹) * h * (g * g⁻¹) by simp only [Matrix.mul_assoc],
          KLAM.mul_inv_uh hg.1, Matrix.one_mul, Matrix.mul_one]
      ext v
      have := KLAM.fib_intertwine hrep hg hEf hmem hyy v
      rw [hconj] at this
      exact this)
    ⟨v0, hv0, hEv0⟩

  refine ⟨c0, ?_⟩
  ext v
  have hv : v ∈ ⨆ σ, S' σ := by rw [htop']; trivial
  induction hv using Submodule.iSup_induction' with
  | mem σ w hw =>
    by_cases hσ : σ = σ0
    · subst hσ
      exact hc0 w hw
    · have hd : ∃ Y, M.xC (P1 P) σ Y ≠ M.xC P ρ Y := by
        obtain ⟨Y, hY⟩ := sep1 σ σ0 hσ
        exact ⟨Y, by rw [← hx0 Y]; exact hY⟩
      rw [ContinuousLinearMap.smul_apply, hkill Z hZe σ hd w hw, hkill E hEe σ hd w hw, smul_zero]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
