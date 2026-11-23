import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.StandardLatticeGoodPlace
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.PowSqEqOneOfKilledBy

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.ClsValTest

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem latsOK_std (l : Geo.Tor.Level H) (n : ℕ) (Cl : Type) :
    LatsOK l.M (fun _ : Cl => (⟨stdLat E n⟩ : GenLat E n)) (fun _ => l.M) := fun _ =>
  ⟨GlobalTheory.Survey.StandardLatticeGoodPlace.unimod_std H n, GlobalTheory.Survey.StandardLatticeGoodPlace.trivAt_std n _, l.odd, dvd_rfl, by
    simp only [GenLat.Ln, inf_idem]; exact Submodule.smul_le_right⟩

theorem not_latsOK_even {M : ℕ} (hM : Even M) {Cl : Type} (k : Cl) (La : Cl → GenLat E n) (Nc : Cl → ℕ) :
    ¬ LatsOK M La Nc := fun h => by
  obtain ⟨-, -, ho, hd, -⟩ := h k
  exact (Nat.not_even_iff_odd.2 ho) (hM.trans_dvd hd)

theorem zCard_ne_zero (Dw : Datum H) {M : ℕ} {Cl : Type} {La : Cl → GenLat E n} {Nc : Cl → ℕ} (h : LatsOK M La Nc)
    (k : Cl) : (La k).zCard (Nc k) (Dw.p + Dw.q) ≠ 0 :=
  (GlobalTheory.RootsSplitTest.zCard_pos Dw (La k) (Nc k) M (h k).1 (h k).2.2).ne'

theorem clsSum_std (σ : c.F →+* ℂ) (X : Data E (Dw.p + Dw.q)) (hr : X.p0 + q0 = Dw.p + Dw.q)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ)
    (idx : Fin g ≃ X.Ψ × Fin (Dw.p + Dw.q)) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)) (l₂ : Geo.Tor.Level H)
    (w : (Fin n → LevQ Dw l₂) → c.F) (P : MvPolynomial (LtN Dw n) c.F) (L : Lt E (Dw.p + Dw.q)) (v : TF n g)
    (Y : (Fin n → LevQ Dw l₂) → Matrix (Fin n) (Fin (Dw.p + Dw.q)) E) (x : Frame X.Ψ (Dw.p + Dw.q)) :
    clsSum σ X hr bas idx eL (fun _ : Unit => w) (fun _ => ⟨stdLat E n⟩) (fun _ => l₂.M) (fun _ => 1) 1 (fun _ => 1)
      (fun _ => P) L v (fun _ => Y) x =
    ((Nat.card (Fin n → LevQ Dw l₂) : ℂ))⁻¹ *
      thP X hr bas idx (gphi X bas (H.w0 : E) (stdLat E n) L v (fun q => σ (w q)) Y)
        (MvPolynomial.rename eL (MvPolynomial.map σ P)) x := by
  have hz := zCard_ne_zero Dw (latsOK_std l₂ n Unit) ()
  have hm : (⟨stdLat E n⟩ : GenLat E n).mIdx l₂.M (Dw.p + Dw.q) =
      (⟨stdLat E n⟩ : GenLat E n).zCard l₂.M (Dw.p + Dw.q) := by
    have e : (⟨stdLat E n⟩ : GenLat E n).Ln = stdLat E n := inf_idem _
    rw [GenLat.mIdx, GenLat.zCard, e]
  have hz' : (((⟨stdLat E n⟩ : GenLat E n).zCard l₂.M (Dw.p + Dw.q) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hz
  simp only [clsSum, Finset.univ_unique, Finset.sum_singleton, hm, map_mul, map_inv₀, map_natCast, map_one]
  congr 1
  push_cast
  field_simp

def oneSim (D : Datum H) : Sim D where
  f _ := LinearMap.id
  ν _ := 1
  tower n _ _ _ a := ⟨0, by simp⟩
  inv n _ := ⟨LinearMap.id, fun a => ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩⟩
  mult n _ a b := by simp

theorem oneSim_inGam (l l₂ : Geo.Tor.Level H) : (oneSim Dw).InGam l l₂ :=
  ⟨by simp [oneSim], fun a => by simp [oneSim], fun a => ⟨0, by simp [oneSim]⟩⟩

theorem datEq_lin (d : DeltaDat Xo c n) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ)
    {w w' : (Fin n → LevQ Dw d.l₂) → c.F} (h : DatEq d ψ w) (h' : DatEq d ψ w') (t : c.F) :
    DatEq d ψ (w + t • w') := by
  intro s hs kI σq h1 h2 q
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h s hs kI σq h1 h2 q, h' s hs kI σq h1 h2 q]
  ring

theorem datEq_char (d : DeltaDat Xo c n) {ψ ψ' : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ}
    {w : (Fin n → LevQ Dw d.l₂) → c.F} (h : DatEq d ψ w) (h' : DatEq d ψ' w) (hw : w ≠ 0)
    (s : Sim Dw) (hs : s.InGam l d.l₂) (kI : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) (σq : LevQ Dw d.l₂ ≃ LevQ Dw d.l₂)
    (h1 : ∀ a : Dw.La, (Submodule.Quotient.mk (s.f d.l₂.M a) : LaI Xo c d) = kI (Submodule.Quotient.mk a))
    (h2 : ∀ a : Dw.La, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk (s.f d.l₂.M a)) : ψ kI = ψ' kI := by
  obtain ⟨q, hq⟩ := Function.ne_iff.1 hw
  have e := (h s hs kI σq h1 h2 q).symm.trans (h' s hs kI σq h1 h2 q)
  exact inv_injective (Units.ext (mul_right_cancel₀ hq e))

theorem exists_datEq (d : DeltaDat Xo c n) (hI : d.l₂.Mb ≤ d.I) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ)
    (x₀ : Fin n → LaI Xo c d) (hx : Submodule.span (𝓞 E) (Set.range x₀) = ⊤) :
    ∃ w : (Fin n → LevQ Dw d.l₂) → c.F, DatEq d ψ w ∧
      ∀ (k : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) (a : Fin n → Dw.La),
        (∀ b, (Submodule.Quotient.mk (a b) : LaI Xo c d) = k (x₀ b)) →
        w (fun b => Submodule.Quotient.mk (a b)) = (ψ k : c.Fˣ) := by
  let π : LevQ Dw d.l₂ →ₗ[𝓞 E] LaI Xo c d :=
    Submodule.factor (Submodule.smul_mono_left hI)
  have hπ : ∀ a : Dw.La, π (Submodule.Quotient.mk a) = Submodule.Quotient.mk a := fun a => rfl
  have uniq : ∀ k k' : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d, (∀ b, k (x₀ b) = k' (x₀ b)) → k = k' := by
    intro k k' h
    apply LinearEquiv.toLinearMap_injective
    exact LinearMap.ext_on_range hx h
  let w : (Fin n → LevQ Dw d.l₂) → c.F := fun q =>
    if h : ∃ k : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d, ∀ b, π (q b) = k (x₀ b) then (ψ h.choose : c.Fˣ) else 0
  have hw : ∀ q (k : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d), (∀ b, π (q b) = k (x₀ b)) → w q = (ψ k : c.Fˣ) := by
    intro q k hk
    have h : ∃ k : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d, ∀ b, π (q b) = k (x₀ b) := ⟨k, hk⟩
    have : h.choose = k := uniq _ _ fun b => (h.choose_spec b).symm.trans (hk b)
    simp only [w, dif_pos h, this]
  refine ⟨w, ?_, fun k a ha => hw _ k fun b => (hπ _).trans (ha b)⟩
  intro s _ kI σq h1 h2 q
  have hc : ∀ u, π (σq u) = kI (π u) := by
    intro u
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    rw [h2, hπ, hπ, h1]
  have hc' : ∀ u, π u = kI (π (σq.symm u)) := fun u => by rw [← hc, Equiv.apply_symm_apply]
  by_cases h : ∃ k : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d, ∀ b, π (q b) = k (x₀ b)
  · obtain ⟨k, hk⟩ := h
    rw [hw q k hk, hw _ (kI⁻¹ * k) (fun b => ?_), map_mul, map_inv, Units.val_mul]
    apply kI.injective
    rw [← hc', hk]
    change _ = (kI * (kI⁻¹ * k)) (x₀ b)
    rw [mul_inv_cancel_left]
  · have h' : ¬ ∃ k : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d, ∀ b, π (σq.symm (q b)) = k (x₀ b) := by
      rintro ⟨k, hk⟩
      exact h ⟨kI * k, fun b => by rw [hc', hk]; rfl⟩
    simp only [w, dif_neg h, dif_neg h', mul_zero]

theorem cvIs_unique (d : DeltaDat Xo c n) [Algebra d.c₂.F ℂ] {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}
    {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {L : Lt E r} {cv cv' : (Dw.La →ₗ[𝓞 E] (Fin r → E)) → ℂ}
    (h : CvIs d X bas idx e L cv) (h' : CvIs d X bas idx e L cv') {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    {y₂ : FrPt d.Xo₂ d.c₂ ℂ} (A : AnFib X bas idx e x L y₂) {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)}
    (hm : IsMark d.l₂ L mk) (hA : A.Marked mk) : cv mk = cv' mk :=
  (h x hx y₂ A mk hm hA).symm.trans (h' x hx y₂ A mk hm hA)

theorem cvIs_const (d : DeltaDat Xo c n) [Algebra d.c₂.F ℂ] (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ)
    (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (L : Lt E r) (t : ℂ)
    (h : ∀ y₂ : FrPt d.Xo₂ d.c₂ ℂ, evR d.Xo₂ d.c₂ d.cδ y₂ = t) : CvIs d X bas idx e L fun _ => t :=
  fun _ _ y₂ _ _ _ _ => h y₂

end

end GlobalTheory.ClsValTest
