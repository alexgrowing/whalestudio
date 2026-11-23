import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsVanBdOfMemExtVanZ
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OffZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
import Development.WeilBound.CoreStatements.ProjectiveValuations.NV

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS
open GlobalTheory.CompanionTheory.Ar.HolExt

noncomputable section

namespace DifferentiableLines

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ}

def chr (e : Ix D → ℤ) (t : Ix D → (CAt σ)ˣ) : ℂ := by
  classical exact toC (∏ ix, t ix ^ e ix).val

theorem chr_ne_zero (e : Ix D → ℤ) (t : Ix D → (CAt σ)ˣ) : chr e t ≠ 0 := by
  classical
  exact Units.ne_zero (M₀ := ℂ) (∏ ix, t ix ^ e ix : (CAt σ)ˣ)

theorem chr_mul (e : Ix D → ℤ) (t t' : Ix D → (CAt σ)ˣ) : chr e (t * t') = chr e t * chr e t' := by
  classical
  have : (∏ ix, (t * t') ix ^ e ix) = (∏ ix, t ix ^ e ix) * ∏ ix, t' ix ^ e ix := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun ix _ => mul_zpow _ _ _
  exact congrArg (fun u : (CAt σ)ˣ => toC u.val) this

theorem chr_add (e e' : Ix D → ℤ) (t : Ix D → (CAt σ)ˣ) : chr (e + e') t = chr e t * chr e' t := by
  classical
  have : (∏ ix, t ix ^ (e + e') ix) = (∏ ix, t ix ^ e ix) * ∏ ix, t ix ^ e' ix := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun ix _ => zpow_add _ _ _
  exact congrArg (fun u : (CAt σ)ˣ => toC u.val) this

theorem chr_zero (t : Ix D → (CAt σ)ˣ) : chr 0 t = 1 := by
  classical
  have : (∏ ix, t ix ^ (0 : Ix D → ℤ) ix) = 1 := Finset.prod_eq_one fun ix _ => zpow_zero _
  exact congrArg (fun u : (CAt σ)ˣ => toC u.val) this

theorem ex_add_int (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) : (fun i => (ex D (a + a') (n + n') i : ℤ)) =
    (fun i => (ex D a n i : ℤ)) + fun i => (ex D a' n' i : ℤ) := by
  funext i
  rw [ex_add]
  simp

theorem dom_add {a a' : (E →+* ℂ) × ℕ → ℕ} {n n' : ℕ} (h : Dom a n) (h' : Dom a' n') : Dom (a + a') (n + n') :=
  ⟨fun τ _ _ hij => Nat.add_le_add (h.1 τ hij) (h'.1 τ hij), h.2.add h'.2⟩

theorem laU_add' (V : Unf Xo c σ r) (a a' : (E →+* ℂ) × ℕ → ℕ) {n n' : ℕ} (hn : Even n) (hn' : Even n') (k : V.Comp) :
    laU V (a + a') (n + n') k = laU V a n k + laU V a' n' k := by
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨m', rfl⟩ := hn'
  funext τ j
  have h1 : (m + m) / 2 = m := by omega
  have h2 : (m' + m') / 2 = m' := by omega
  have h3 : (m + m + (m' + m')) / 2 = m + m' := by omega
  simp only [laU, Pi.add_apply, h1, h2, h3]
  split_ifs <;> push_cast <;> ring

theorem evR_frBor {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) {t : Ix D → (CAt σ)ˣ}
    {y y' : FrPt Xo c (CAt σ)} (h : FrBor t y y') :
    toC (evR Xo c f y') = chr (fun i => (ex D a n i : ℤ)) t * toC (evR Xo c f y) := by
  classical
  have hL := (GlobalTheory.Reg.evLaws_genFr_atlas E H D l Xo c).1
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  have e : evR Xo c f y' = wchar (ex D a n) t * evR Xo c f y :=
    hL.wt a n f hf (CAt σ) t _ _ (hL.test _ _) (hL.test _ _) h
  have e' : (wchar (ex D a n) t : CAt σ) = (∏ ix, t ix ^ (ex D a n ix : ℤ)).val := by
    simp only [wchar, zpow_natCast, Units.coe_prod, Units.val_pow_eq_pow_val]
  rw [e, e']
  rfl

theorem rdU_eq (V : Unf Xo c σ r) (f : Rul Xo c) (k : V.Comp) (x : (V.X k).dom) :
    rdU V f k x.1 = toC (evR Xo c f (V.un k x)) := dif_pos x.2

theorem sec_frBor {V : Unf Xo c σ r} (hU : IsUnf V) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hD : Dom a n)
    (hN : NV Xo c σ a n) {k : V.Comp} {P : Frame (V.X k).Ψ r → ℂ} (hP : (V.X k).IsSec (laU V a n k) P)
    {x x' : (V.X k).dom} {t : Ix D → (CAt σ)ˣ} (ht : FrBor t (V.un k x) (V.un k x')) :
    P x'.1 = chr (fun i => (ex D a n i : ℤ)) t * P x.1 := by
  obtain ⟨γ, hγ, b, hb, hx⟩ := (hU.2.2.2.1 k k x x').1 ⟨t, ht⟩
  have hx' : x'.1 = rmul (lact γ x.1) b := eq_of_heq (Sigma.mk.inj hx).2
  have hd := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_lact (V.X k) hγ x.2
  have key : ∀ la Q, (V.X k).IsSec la Q → Q x'.1 = (bchar la b * (V.X k).χ la γ) * Q x.1 := fun la Q hQ => by
    rw [hx', hQ.2.1 _ hd b hb, hQ.2.2 γ hγ _ x.2, mul_assoc]
  obtain ⟨a', n', hD', g, hg, f, hf, hg0, hf0⟩ := hN (V.un k x)
  have e₁ := key _ _ (hU.2.2.2.2.1 a' n' hD' g hg k)
  have e₂ := key _ _ (hU.2.2.2.2.1 _ _ (dom_add hD hD') f hf k)
  rw [rdU_eq, rdU_eq, evR_frBor hg ht] at e₁
  rw [rdU_eq, rdU_eq, evR_frBor hf ht, ex_add_int, chr_add, laU_add' V a a' hD.2 hD'.2, (V.X k).χ_add _ _ γ hγ] at e₂
  have a₁ := mul_right_cancel₀ (show toC (evR Xo c g (V.un k x)) ≠ 0 from hg0) e₁
  have a₂ := mul_right_cancel₀ (show toC (evR Xo c f (V.un k x)) ≠ 0 from hf0) e₂
  have hdiag : ∀ τ i, b τ i i ≠ 0 := fun τ i => by
    have hdet := (hb τ).1
    rw [Matrix.det_of_upperTriangular (M := mat b τ) (fun a c hac => (hb τ).2 a c hac)] at hdet
    exact Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ _)
  have hadd : bchar (laU V a n k + laU V a' n' k) b = bchar (laU V a n k) b * bchar (laU V a' n' k) b := by
    simp only [bchar, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.add_apply, Pi.add_apply, zpow_add₀ (hdiag τ i)]
  rw [key _ _ hP]
  congr 1
  refine mul_right_cancel₀ (chr_ne_zero (fun i => (ex D a' n' i : ℤ)) t) ?_
  rw [a₂, hadd, a₁]
  ring

theorem exists_chart_frBor (T : TorFlag Xo c) (y : FrPt Xo c (CAt σ)) (i : T.X.F.J) {z : Sp (CAt σ) ⟶ T.X.YY}
    (e : T.X.ptY y = z) (hz : ⊤ ≤ z ⁻¹ᵁ T.X.F.U i) :
    ∃ (Q : FrPt Xo c (CAt σ)) (t : Ix D → (CAt σ)ˣ), T.X.F.ChartFr i z hz Q ∧ FrBor t Q y := by
  subst e
  have hl := T.X.lies_ptY y
  obtain ⟨Q, hQ⟩ := T.X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd y) hl.1 i hz
  obtain ⟨t, ht⟩ := hQ.exists_frBor hl
  exact ⟨Q, t, hQ, ht⟩

end DifferentiableLines
