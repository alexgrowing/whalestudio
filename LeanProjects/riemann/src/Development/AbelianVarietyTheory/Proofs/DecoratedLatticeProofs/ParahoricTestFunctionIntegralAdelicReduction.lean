import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RescOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FunObj.Comparison₂ (IsRed Compat IsIx)

namespace GlobalTheory.QTw.LocFn

section Red

variable {S F K : Type} [CommRing S] [CommRing F] [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {φ : S →+* F} {ψ : S →+* K}

theorem parPhi_eq_of_equiv (h : IsRed φ ψ) {R : Type} [Fintype R] [DecidableEq R] {r t j j' a b : ℕ} (f : Fin r ≃ R)
    {ea : Ix R (Fin t) j ≃ Fin a} {eb : Ix R (Fin t) j' ≃ Fin b}
    (ha : IsIx ((Equiv.sumCongr f (Equiv.refl (Fin j × Fin t))).trans ea))
    (hb : IsIx ((Equiv.sumCongr f (Equiv.refl (Fin j' × Fin t))).trans eb))
    {c : Fˣ →* ℂˣ} {δ : Kˣ →* ℂˣ} (hc : Compat φ ψ c δ⁻¹) (N : Matrix (Fin b) (Fin a) S) :
    parPhi δ ((N.map ψ).submatrix eb ea) =
      if H : LowZero r (N.map φ) ∧ IsUnit (topL r (N.map φ)).det then (c H.2.unit : ℂ) else 0 := by
  have e1 : (topL r (N.map φ)).det = ((N.submatrix eb ea).toBlocks₁₁.map φ).det := by
    rw [GlobalTheory.FunObj.Comparison₂.topL_r ha hb, ← det_submatrix_equiv_self f]
    rfl
  have e2 : LowZero r (N.map φ) ↔ MaxM ((N.map ψ).submatrix eb ea).toBlocks₂₁ :=
    (GlobalTheory.FunObj.Comparison₂.lowZero_r h ha hb N).trans
      ⟨fun H i l => by
        obtain ⟨l, rfl⟩ := f.surjective l
        exact H i l, fun H i l => H i (f l)⟩
  split_ifs with H
  · obtain ⟨g, hg, e⟩ := (h.isUnit_det_iff _).1 (e1 ▸ H.2)
    rw [parPhi_of_mem (x := (N.map ψ).submatrix eb ea) _ hg e (e2.1 H.1) (fun _ _ => h.int _) (fun _ _ => h.int _),
      hc.det (k := Matrix.GeneralLinearGroup.det g) _ (H.2.unit_spec.trans e1) (congrArg Matrix.det e),
      MonoidHom.inv_apply]
  · by_contra h0
    obtain ⟨h1, h2, -⟩ := (parPhi_ne_zero_iff _).1 h0
    exact H ⟨e2.2 h2, e1 ▸ (h.isUnit_det_iff _).2 h1⟩

theorem tame_congr {δ : Kˣ →* ℂˣ} (hδ : IsTame δ) {x y : Kˣ} (hx : valuation K (x : K) = 1)
    (h : valuation K ((x : K) - y) < 1) : δ y = δ x := by
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul]
  refine hδ _ ?_
  rwa [Units.val_mul, Units.val_inv_eq_inv_val, ← mul_inv_cancel₀ x.ne_zero, ← sub_mul, map_mul, map_inv₀, hx, inv_one,
    mul_one, Valuation.map_sub_swap]

end Red

theorem isIx_of_isOrd {κ l r t j a : ℕ} (h : κ + l = r) {e : Ix (Fin κ ⊕ Fin l) (Fin t) j ≃ Fin a}
    (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e) :
    IsIx ((Equiv.sumCongr (finSumFinEquiv.trans (finCongr h)).symm (Equiv.refl (Fin j × Fin t))).trans e) := by
  refine ⟨?_, fun i => ?_, fun c s => ?_⟩
  · simpa [h] using (Fintype.card_congr e).symm
  · obtain ⟨i, rfl⟩ := (finSumFinEquiv.trans (finCongr h)).surjective i
    rw [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.symm_apply_apply, he]
    rcases i with i | i <;> rfl
  · refine (he (.inr (c, s))).trans ?_
    change κ + l + c.val * t + s.val = _
    rw [h, mul_comm]; omega

theorem parPhi_component : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E) (π' : EAf D →+* k), (∀ a, π' (toEAf D a) = q.pr a) → GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) → ∀ (δ : kˣ →* ℂˣ), IsTame δ → ∀ (ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), (∀ (z : 𝓞 D.host.E) (x : kˣ) (u : (Formalism.L2.DIV.kP PP)ˣ), (x : k) = (ofSplit q).pr (z : D.host.E) → (u : Formalism.L2.DIV.kP PP) = Ideal.Quotient.mk PP.asIdeal z → δ x = (ξ u)⁻¹) → ∀ (κ l r t j j' a b : ℕ), r = κ + l → ∀ (ea : Ix (Fin κ ⊕ Fin l) (Fin t) j ≃ Fin a) (eb : Ix (Fin κ ⊕ Fin l) (Fin t) j' ≃ Fin b), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos ea → GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos eb → ∀ N : Matrix (Fin b) (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E), parPhi δ ((N.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)).submatrix eb ea) = if H : LowZero r (N.map (Formalism.L2.DIV.resS D.host.F PP)) ∧ IsUnit (topL r (N.map (Formalism.L2.DIV.resS D.host.F PP))).det then ((ξ H.2.unit : ℂˣ) : ℂ) else 0 := by
  intro D k _ _ _ _ q PP π' hπ hred δ hδ ξ hξ κ l r t j j' a b hr ea eb ha hb N
  refine parPhi_eq_of_equiv hred _ (isIx_of_isOrd hr.symm ha) (isIx_of_isOrd hr.symm hb) (fun s u x hu hx => ?_) N
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (u : Formalism.L2.DIV.kP PP)
  have h1 : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E z) =
      (ofSplit q).pr (z : D.host.E) := hπ (incA D (z : D.host.E))
  have h2 : valuation k ((x : k) - (ofSplit q).pr (z : D.host.E)) < 1 := by
    rw [hx, ← h1, ← RingHom.map_sub, ← hred.ker, RingHom.map_sub, Formalism.L2.DIV.resS_oToS, sub_eq_zero]
    exact (hz.trans hu).symm
  have h3 : valuation k (x : k) = 1 := by
    rw [hx]; exact (hred.isUnit_iff s).1 (hu ▸ u.isUnit)
  have h4 : (ofSplit q).pr (z : D.host.E) ≠ 0 := fun h => by
    rw [h, sub_zero, h3] at h2
    exact lt_irrefl _ h2
  rw [MonoidHom.inv_apply, ← tame_congr hδ (y := Units.mk0 _ h4) h3 h2, hξ z (Units.mk0 _ h4) u rfl hz.symm, inv_inv]

end GlobalTheory.QTw.LocFn

end
