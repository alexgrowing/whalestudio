import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.Incl

open NumberField IsDedekindDomain MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns

theorem subst_expAlong {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : LogFGL v d)
    {κ : Type} [Fintype κ] {ι : κ → Type} [∀ b, Fintype (ι b)] (u : ∀ b, ι b → Fin d → C)
    (A : κ → Matrix (Fin d) (Fin d) C) (t : κ → C) (hA : ∀ b a, (A b).mulVec (u b a) = t b • u b a) (i : Fin d) :
    subst (expAlong (fun _ : κ => G) u)
        (expPt G (∑ b, mv (A b) (lgPt G fun e => (X ⟨b, e⟩ : MvPowerSeries (Σ _ : κ, Fin d) C))) i) =
      subst (fun e : Fin d => ∑ ℓ : (Σ b, ι b), (t ℓ.1 * u ℓ.1 ℓ.2 e) • (X ℓ : MvPowerSeries (Σ b, ι b) C))
        (expOf G i) := by
  have hu : ∀ (b : κ) (e : Fin d),
      constantCoeff (∑ a, u b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C)) = 0 := fun b e => by simp
  have hE : ∀ (b : κ), (fun e : Fin d => expAlong (fun _ : κ => G) u ⟨b, e⟩) =
      expPt G (fun e => ∑ a, u b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C)) := fun b => rfl
  have hs : HasSubst (expAlong (fun _ : κ => G) u) :=
    hasSubst_of_constantCoeff_zero fun q => cc_expPt G (hu q.1) q.2
  have hX : ∀ (b : κ) (e : Fin d), constantCoeff (X ⟨b, e⟩ : MvPowerSeries (Σ _ : κ, Fin d) C) = 0 := by simp
  rw [subst_expPt G hs (fun e => by
    rw [Finset.sum_apply, map_sum]
    exact Finset.sum_eq_zero fun b _ => cc_mv _ (cc_lgPt G (hX b)) e)]
  unfold expPt
  congr 1
  funext e
  rw [Finset.sum_apply, ← coe_substAlgHom hs, map_sum, coe_substAlgHom, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [subst_mv hs]
  have h1 : (fun e' => subst (expAlong (fun _ : κ => G) u)
      (lgPt G (fun e => (X ⟨b, e⟩ : MvPowerSeries (Σ _ : κ, Fin d) C)) e')) =
      fun e => ∑ a, u b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C) := by
    funext e'
    rw [subst_lgPt G hs (hX b)]
    simp only [subst_X hs]
    rw [hE b, lgPt_expPt G (hu b)]
  rw [h1]
  simp only [mv, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  exact congrFun (hA b a) e

theorem isotropic_blocks {O : Type} [CommRing O] [StarRing O] (I : Ideal O) {φ : Type} {r m : φ → ℕ} {n : ℕ}
    (blk : (Σ f : φ, Fin (m f)) ↪ Fin n) (ε : φ → O) (x : ∀ f, Fin (r f) → Fin n → O)
    (h0 : ∀ f b j, j ∉ Set.range (fun j => blk ⟨f, j⟩) → x f b j = 0)
    (hiso : ∀ f b b', ∑ j, x f b j * star (x f b' j) ∈ I) (b b' : Σ f, Fin (r f)) :
    ∑ j, star (ε b.1 * x b.1 b.2 j) * (ε b'.1 * x b'.1 b'.2 j) ∈ I := by
  obtain ⟨f, β⟩ := b
  obtain ⟨f', β'⟩ := b'
  by_cases hf : f = f'
  · subst hf
    have e : ∑ j, star (ε f * x f β j) * (ε f * x f β' j) =
        (star (ε f) * ε f) * ∑ j, x f β' j * star (x f β j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [star_mul]; ring
    rw [e]
    exact I.mul_mem_left _ (hiso f β' β)
  · refine Ideal.sum_mem _ fun j _ => ?_
    by_cases h1 : j ∈ Set.range (fun j => blk ⟨f, j⟩)
    · by_cases h2 : j ∈ Set.range (fun j => blk ⟨f', j⟩)
      · obtain ⟨j1, h1⟩ := h1
        obtain ⟨j2, h2⟩ := h2
        exact absurd (congrArg Sigma.fst (blk.injective (h1.trans h2.symm))) hf
      · simp [h0 f' β' j h2]
    · simp [h0 f β j h1]

theorem inclSt_of_lim (hAct : LimActSt) (hPt : LimPtSt) (hFr : LimFrameSt) : InclSt := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y Ch p _ Y cx n B hB
  obtain ⟨blk, hblk⟩ := hB
  choose x hx0 hxB hxiso using fun (f : {f : Lt1 Dw // cx f ≠ 0}) (N : ℕ) => (hblk f).2.2 N
  choose ε hε using fun τ : E →+* ℂ => hAct E H Dw l Xo c hstar T io y Ch p Y τ
  choose A hAapp hAlie using fun (b : Col cx) (j : Fin n) =>
    hε b.1.1.1 (B b.1.1 b.2 j) (fun N => x b.1 N b.2 j) (fun N => hxB b.1 N b.2 j)
  letI := io.toAlgebra
  letI : Algebra T.Fr Y.C := Y.ιF.toAlgebra
  have hw : ∀ b : Col cx, IntLog (fglOf (isIntFB_chart Ch Y)) (lgPt (fgl Ch Y)
      fun e => (X ⟨b, e⟩ : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) Y.C)) :=
    fun b => intLog_lgPt_X (fgl Ch Y) (fun e => (⟨b, e⟩ : Σ _ : Col cx, Fin (chD Ch.ch)))
  have hint := fun j : Fin n => hPt Y.C (vX_vp Y) _ T.Fr (𝓞 E) Ch.ch.B (isIntFB_chart Ch Y) _ (Col cx) _ hw
    (fun b => A b j) (fun N b => ε b.1.1.1 N * x b.1 N b.2 j) (fun N b => hAapp b j N)
  refine ⟨fun q => expPt (fgl Ch Y) (∑ b, mv (A b q.1) (lgPt (fgl Ch Y) fun e => X ⟨b, e⟩)) q.2,
    fun q => cc_expPt _ (hint q.1).1 q.2, fun q => (hint q.1).2 q.2, fun q => ?_, ?_⟩
  · exact subst_expAlong (fgl Ch Y) (fun b : Col cx => frame Ch Y b.1.1) (fun b => A b q.1)
      (fun b => jX Y (B b.1.1 b.2 q.1)) (fun b a => hAlie b q.1 _) q.2
  · exact hFr Y.C (vX_vp Y) p (vX_vp_p Y) _ T.Fr (𝓞 E) Ch.ch.B (isIntFB_chart Ch Y) _ (gauge_chart Ch Y) _ (Col cx) _
      hw H.w0 n A (fun N b j => ε b.1.1.1 N * x b.1 N b.2 j) (fun N b j => hAapp b j N)
      (fun N => isotropic_blocks _ blk (fun f => ε f.1.1 N) (fun f => x f N) (fun f => hx0 f N)
        (fun f b b' => by simpa only [hstar] using hxiso f N b b'))

end GlobalTheory.IsoTriv.Incl
