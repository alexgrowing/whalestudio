import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Framed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSBesUnscaledDual

noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam Matrix ValuativeRel IsLocalRing GlobalTheory.LocMod

namespace GlobalTheory.MiTop

section Frame

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
  {ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ} {A : Formalism.BasicNotions.TH.HSp D}

theorem besVec_ne_zero (B : SBes X h u ψ A) : B.d.i₀ *ᵥ vecB B.o B.ζ ≠ 0 := fun h0 => by
  apply B.line.2
  have e : B.L.gram *ᵥ B.ζ = (B.o.iBᴴ * (B.d.i₀ᴴ * (D.sp.Y 0).gram)) *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ) := by
    rw [← B.o.isoB, ← B.d.iso]
    simp only [vecB, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e, h0]; simp

theorem besScale_unique (B : SBes X h u ψ A) {μ μ' : D.host.E}
    (h₁ : ∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = μ * X.ιE (X.zR u (Fin.cast (rank_eq X h) k)))
    (h₂ : ∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = μ' * X.ιE (X.zR u (Fin.cast (rank_eq X h) k))) : μ = μ' := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 (besVec_ne_zero B)
  have hz : X.ιE (X.zR u (Fin.cast (rank_eq X h) k)) ≠ 0 := fun h0 => hk (by rw [h₁, h0, mul_zero]; rfl)
  exact mul_right_cancel₀ hz ((h₁ k).symm.trans (h₂ k))

theorem Framed.lines {B : SBes X h u ψ A} (hB : Framed B) (a : Fin D.R.rS) :
    ∃ s s' : D.host.E, (∀ k, B.d.e k a = s * X.ιE (X.eR a (Fin.cast (rank_eq X h) k))) ∧
      ∀ k, B.d.e' k a = s' * X.ιE (X.fR a (Fin.cast (rank_eq X h) k)) := by
  obtain ⟨μ, lam, -, -, -, he, he'⟩ := hB
  exact ⟨_, _, fun k => he k a, fun k => he' k a⟩

theorem Framed.e'_eq {A' : Formalism.BasicNotions.TH.HSp D} {u' : D.what₂.Word} {B : SBes X h u ψ A} {B' : SBes X h u' ψ A'}
    (hB : Framed B) (hB' : Framed B') (e : B'.d.e = B.d.e) : B'.d.e' = B.d.e' := by
  obtain ⟨μ, lam, -, -, -, he, he'⟩ := hB
  obtain ⟨μ', lam', -, -, -, ge, ge'⟩ := hB'
  ext k a
  have hne : ∃ r, B.d.e r a ≠ 0 := by
    by_contra hc
    push Not at hc
    have := congrFun (congrFun B.d.e'e a) a
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
    simp [hc] at this
  obtain ⟨r, hr⟩ := hne
  have hz : X.ιE (X.eR a (Fin.cast (rank_eq X h) r)) ≠ 0 := fun h0 => hr (by rw [he, h0, mul_zero])
  have hs := mul_right_cancel₀ hz ((ge r a).symm.trans ((congrFun (congrFun e r) a).trans (he r a)))
  rw [ge', he', hs]

theorem Framed.shear_eq_zero {B B' : SBes X h u ψ A} (hB : Framed B) (hB' : Framed B')
    {c : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E} (e : B'.d.e = B.d.e) (e' : B'.d.e' = B.d.e' + B.d.e * c) : c = 0 := by
  have e1 : B.d.e * c = 0 := by simpa [hB.e'_eq hB' e] using e'
  have := congrArg (fun x => B.d.e'ᴴ * (D.sp.Y 0).gram * x) e1
  simpa only [← Matrix.mul_assoc, B.d.e'e, Matrix.one_mul, Matrix.mul_zero] using this

theorem exists_framed_adapted (F₀ : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F₀) (hE : IdE X)
    (hψ : IsStdChar D ψ (-1)) (μ : D.host.E) (hμ : μ ≠ 0) (vA : Vol (D.sp.X 0)) :
    ∃ B : SBes X h u ψ (D.sp.X 0), Framed B ∧ B.Adapted tr.wt ∧
      ∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = μ * X.ιE (X.zR u (Fin.cast (rank_eq X h) k)) := by
  obtain ⟨lam, hl, H⟩ := exists_sBes_scaled_dual D X h u ψ F₀ tr hE hψ
  obtain ⟨B, ha, -, hz, he, he'⟩ := H μ vA hμ
  exact ⟨B, ⟨μ, lam, hμ, hl, hz, he, he'⟩, ha, hz⟩

end Frame

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u)
  (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))

def InPlace : Prop := Placed f B ∧ Framed B

variable {f B}

theorem Placed.adapted (h : Placed f B) : B.Adapted (W.S.tr u).wt := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb⟩ := h
  exact hb.adapted

theorem Placed.levTrace (h : Placed f B) : LevTrace f B := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb⟩ := h
  exact hb.trace

theorem InPlace.common (h : InPlace f B) :
    ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (ι : Type)
      (v : VCom f.c) (o : TDat f.c k ι) (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg),
      f.c.Is ∧ v.Is ∧ VTie f v ∧ ShapeOff v o ∧ GPin G ∧ GRead f G pl ∧ BotTie f B v o G ∧
      ∃ μ lam s : D.host.E, μ ≠ 0 ∧ μ * lam = -D.host.xi0 ^ (D.R.m / 2) ∧
        (s = (W.S.X.B.g : D.host.E) ∨ s = -(W.S.X.B.g : D.host.E)) ∧
        (∀ j hj, v.τ j hj *ᵥ o.ζ₀ = lam • (f.c.bes j 0 hj).ζ) ∧
        (∀ r, (B.d.i₀ *ᵥ vecB B.o B.ζ) r = μ * W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))) ∧
        (∀ r (a : Fin D.R.rS), B.d.e r a =
          μ * s ^ (D.R.rS - (a : ℕ)) * W.S.X.ιE (W.S.X.eR a (Fin.cast (rank_eq W.S.X W.Q.instEq) r))) ∧
        ∀ r (a : Fin D.R.rS), B.d.e' r a =
          (star (μ * s ^ (D.R.rS - (a : ℕ))))⁻¹ * W.S.X.ιE (W.S.X.fR a (Fin.cast (rank_eq W.S.X W.Q.instEq) r)) := by
  obtain ⟨⟨k, i1, i2, i3, i4, ι, v, o, n, G, pl, h1, h2, h3, h4, h5, h6, hb⟩, μ, s, hμ, hs, hz, he, he'⟩ := h
  obtain ⟨μ', lam, n1, n2, n3⟩ := hb.norm
  obtain rfl : μ = μ' := besScale_unique B hz n2
  exact ⟨k, i1, i2, i3, i4, ι, v, o, n, G, pl, h1, h2, h3, h4, h5, h6, hb, μ, lam, s, hμ, n1, hs, n3, hz, he, he'⟩

variable (f B)

theorem shift_tOf (a₀ a : GA D (D.sp.X 0)) :
    (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * tOf f B a₀ a =
      embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from f.g.b 0) := by
  unfold tOf
  rw [mul_assoc, mul_inv_cancel_left]

theorem tOf_eq_iff (a₀ a : GA D (D.sp.X 0)) (t : GA D (D.sp.Y 0)) :
    tOf f B a₀ a = t ↔ embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from f.g.b 0) =
      (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * t := by
  rw [← shift_tOf, mul_right_inj]

example : tOf f B 1 1 = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * (show GA D (D.sp.Y 0) from f.g.b 0) := by
  unfold tOf
  rw [mul_one, map_one, mul_one]

example (d : BotDat W u) {z : GA D (D.sp.Y 0)} (hp : d.Pin z) (hb : (show GA D (D.sp.Y 0) from f.g.b 0) = d.b) :
    tOf f d.B d.a₀ d.a = z * (show GA D (D.sp.Y 0) from W.Q.tS) * d.k := by
  rw [tOf_eq_iff, hb]; exact hp.eq

example (f' : FamCh W u) (B' : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (c : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (hc : c ≠ 0) (e : B'.d.e = B.d.e) (e' : B'.d.e' = B.d.e' + B.d.e * c) (h : InPlace f B) : ¬ InPlace f' B' :=
  fun h' => hc (h.2.shear_eq_zero h'.2 e e')

end GlobalTheory.MiTop

end
