import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.RootFrame

section Flags

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {lv : Level H} {Xo : Moduli Dw lv} {c : Coeff lv} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {ε : F ≃+* c.F} (C : GlobalTheory.ShFam.FlagCpt Z ε)

open Classical in
private theorem symLog_eq' {b : ℕ → Bool} {l : ℕ} (hl : l.Prime) (hb : b l = true) (σ : E →+* ℂ) (i : Fin (Dw.mult σ))
    (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (y : AlgPt C.Y) (h : resP v = l) :
    symLog C b (.inl (σ, i)) v e y = stepLog Z.t (C.π ≫ GlobalTheory.Toroidal.genι Z) (fun y => (fr C y).v σ) l i v e y +
      (if σ (H.rt : E) = H.rt0 then vDiff E l else 0) * Real.log (e.w l) := by
  obtain rfl := h
  rw [mixLog_eq (b := b) (by simp [hb])]
  have hl' : Real.log (resP v) ≠ 0 := (Real.log_pos (by exact_mod_cast hl.one_lt)).ne'
  simp only [symLog, mixLog, lnStep, dif_pos hl, dif_pos i.2, hb, true_and]
  split_ifs
  · field_simp
    ring
  · simp

private theorem single_spec (b : ℕ → Bool) (R : Option ℝ) (σ : E →+* ℂ) (k : Fin (Dw.mult σ)) (n : ℤ)
    {w : Pad.Sym E →₀ ℤ} (hw : w = Finsupp.single (b, R, .inl (σ, (k : ℕ))) n) :
    (∀ y : C.Y.X, UnitAt y (((dg C y σ k ^ n) * (eqn (divOf C (expo Dw w)) y)⁻¹ : C.Y.Fnˣ) : C.Y.Fn)) ∧
    ∀ v e y, lgOf C w v e y = Real.log (e.w (TrueGeo.valAt y.1
      (((dg C (below y.1) σ k ^ n) * (eqn (divOf C (expo Dw w)) (below y.1))⁻¹ : C.Y.Fnˣ) : C.Y.Fn))) +
      n * symLog C b (.inl (σ, k)) v e y := by
  obtain ⟨k, hk⟩ := k
  have hP (y : C.Y.X) : ∏ x : Pad.Letter Dw, dg C y x.1 x.2 ^ expo Dw w x = dg C y σ ⟨k, hk⟩ ^ n := by
    rw [Finset.prod_eq_single ⟨σ, ⟨k, hk⟩⟩ (fun x _ hx => by
      rw [hw, expo_single, if_neg (by simpa [letterOf, hk] using hx.symm), zpow_zero]) (by simp), hw, expo_single,
      if_pos (by simp [letterOf, hk])]
  refine ⟨fun y => ?_, fun v e y => ?_⟩
  · have h₁ : (divOf C (expo Dw w)).IsEqn y (∏ x : Pad.Letter Dw, dg C y x.1 x.2 ^ expo Dw w x) :=
      isEqn_sum _ y fun x => ((fr_spec C y).2 x.1 x.2).zsmul _
    rw [hP] at h₁
    simpa [div_eq_mul_inv] using (Base.isEqn_eqn _ y).iff_unitAt.1 h₁
  · rw [lgOf_eq_lgCopy, lgCopy_eq, hP]
    congr 1
    rw [hw]
    exact Finsupp.sum_single_index (h := fun (a : Pad.Sym E) (n : ℤ) => (n : ℝ) * symLog C a.1 a.2.2 v e y) (by simp)

end Flags

theorem UpperTheory.flag_component_eigen_coordinates :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (F : Type) [Field F] [NumberField F] (ε : F ≃+* c.F) (C : FlagCpt Z ε) (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 → ∀ (a : ℕ → Bool) (R : Option ℝ) (p : ℕ), p.Prime → a p = true → (∀ i : Fin (Dw.mult τ), (∀ x, UnitAt x (genAt (divOf C (expo Dw (rootSym Dw a R τ i))) x * (dg C x τ i : C.Y.Fn))) ∧ ∀ v e y, resP v = p → lgOf C (rootSym Dw a R τ i) v e y = Real.log (e.w (TrueGeo.valAt y.1 (genAt (divOf C (expo Dw (rootSym Dw a R τ i))) (below y.1) * (dg C (below y.1) τ i : C.Y.Fn)))) + stepLog Z.t (C.π ≫ genι Z) (fun y => (fr C y).v τ) p i v e y + vDiff E p * Real.log (e.w (p : AlgebraicClosure F))) ∧ ∀ i : Fin (Dw.mult (conjEmb τ)), (∀ x, UnitAt x ((genAt (divOf C (expo Dw (rootSym Dw a R τ (Dw.p + Dw.q - 1 - i)))) x)⁻¹ * (dg C x (conjEmb τ) i : C.Y.Fn))) ∧ ∀ v e y, resP v = p → -lgOf C (rootSym Dw a R τ (Dw.p + Dw.q - 1 - i)) v e y = Real.log (e.w (TrueGeo.valAt y.1 ((genAt (divOf C (expo Dw (rootSym Dw a R τ (Dw.p + Dw.q - 1 - i)))) (below y.1))⁻¹ * (dg C (below y.1) (conjEmb τ) i : C.Y.Fn)))) + stepLog Z.t (C.π ≫ genι Z) (fun y => (fr C y).v (conjEmb τ)) p i v e y + 0 * Real.log (e.w (p : AlgebraicClosure F)) := by
  intro E _ _ _ H Dw l Xo c Z F _ _ ε C τ hτ a R p hp ha
  have hc : ¬ conjEmb τ (H.rt : E) = H.rt0 := GlobalTheory.AllWt.conj_not_mem ⟨τ, hτ⟩
  have m₁ : Dw.mult τ = Dw.p := by simp [Datum.mult, hτ]
  have m₂ : Dw.mult (conjEmb τ) = Dw.q := by simp [Datum.mult, hc]
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have hi : (i : ℕ) < Dw.p := m₁ ▸ i.2
    obtain ⟨h₁, h₂⟩ := single_spec C a R τ i 1 (w := rootSym Dw a R τ i) (if_pos hi)
    have e₀ (x : C.Y.X) : genAt (divOf C (expo Dw (rootSym Dw a R τ i))) x * (dg C x τ i : C.Y.Fn) =
        (((dg C x τ i ^ (1 : ℤ)) * (eqn (divOf C (expo Dw (rootSym Dw a R τ i))) x)⁻¹ : C.Y.Fnˣ) : C.Y.Fn) := by
      rw [zpow_one, Units.val_mul, mul_comm]
    refine ⟨fun x => e₀ x ▸ h₁ x, fun v e y hv => ?_⟩
    rw [e₀, h₂, symLog_eq' C hp ha τ i v e y hv, if_pos hτ]
    push_cast
    ring
  · have hi : (i : ℕ) < Dw.q := m₂ ▸ i.2
    have hw : rootSym Dw a R τ (Dw.p + Dw.q - 1 - i) = Finsupp.single (a, R, .inl (conjEmb τ, (i : ℕ))) (-1) := by
      rw [rootSym, if_neg (by omega), show Dw.p + Dw.q - 1 - (Dw.p + Dw.q - 1 - i) = i by omega]
    obtain ⟨h₁, h₂⟩ := single_spec C a R (conjEmb τ) i (-1) hw
    have e₀ (x : C.Y.X) : (genAt (divOf C (expo Dw (rootSym Dw a R τ (Dw.p + Dw.q - 1 - i)))) x)⁻¹ *
        (dg C x (conjEmb τ) i : C.Y.Fn) =
        (((dg C x (conjEmb τ) i ^ (-1 : ℤ)) *
          (eqn (divOf C (expo Dw (rootSym Dw a R τ (Dw.p + Dw.q - 1 - i)))) x)⁻¹ : C.Y.Fnˣ) : C.Y.Fn)⁻¹ := by
      rw [zpow_neg_one, Units.val_mul, mul_inv, mul_comm, Units.val_inv_eq_inv_val (dg C x (conjEmb τ) i), inv_inv]
    refine ⟨fun x => e₀ x ▸ (h₁ x).inv, fun v e y hv => ?_⟩
    rw [e₀, h₂, symLog_eq' C hp ha (conjEmb τ) i v e y hv, if_neg hc, GlobalTheory.LineNorm.Neg.valAt_inv (h₁ _), map_inv₀,
      Real.log_inv]
    push_cast
    ring
