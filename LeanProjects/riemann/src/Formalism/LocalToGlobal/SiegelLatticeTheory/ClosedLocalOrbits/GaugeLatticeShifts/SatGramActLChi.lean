import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActLStmt
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiNCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictK

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.NormCut Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.SatGramActL

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ChiNBiAll : Prop := ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), ChiNBi X

namespace ChiLeft

theorem kBB_mem {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Λ ∈ Y.what₂ u) (hΛ' : Λ' ∈ Y.what₂ u')
    (p : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') : kBB Y u u' Λ Λ' p.1.1 ∈ X.B.I.Kset := by
  obtain ⟨hRL, -, hmap, -⟩ := p.2
  have hRL' : RatLink X p.1.1 p.1.2 := hRL
  have hmap' : Formalism.HermitianLatticesTheory.gmap p.1.2 Λ' = Λ := hmap
  have hb0 := (Y.cs u).base_lam Λ hΛ
  have hb1 := (Y.cs u').base_lam Λ' hΛ'
  have key : (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ *
      (p.1.1.2 * (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u')) ∈ X.B.I.Kset := by
    refine LatDictK.dict_K X _ _ {y | y ∈ Λ} (fun y => ?_) (fun y => ?_)
    · show y ∈ Λ ↔ _
      conv_lhs => rw [← hb0]
      exact (Y.cs u).lat_eq _ y
    · show y ∈ Λ ↔ _
      have e1 : y ∈ Λ ↔ p.1.2.symm y ∈ Λ' := by
        constructor
        · intro hy
          rw [← hmap'] at hy
          obtain ⟨z, hz, hzy⟩ := hy
          have : p.1.2.symm y = z := by rw [← hzy]; simp
          rw [this]; exact hz
        · intro h
          rw [← hmap']
          exact ⟨p.1.2.symm y, h, by simp⟩
      have hlat : ∀ w, w ∈ Λ' ↔ X.B.I.fmat (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u')⁻¹ *ᵥ
          incl X.B.I (X.crd w) ∈ X.B.I.Lf := fun w => by
        have := (Y.cs u').lat_eq ((Y.cs u').base Λ') w
        rw [hb1] at this
        exact this
      rw [e1, hlat, show (p.1.1.2 * (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u'))⁻¹ =
          (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u')⁻¹ * p.1.1.2⁻¹ from _root_.mul_inv_rev _ _,
        LatDictK.fmatK_mul, ← Matrix.mulVec_mulVec, LatDictK.ratLink_incl_inv X hRL']
  have e : kBB Y u u' Λ Λ' p.1.1 = (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ *
      (p.1.1.2 * (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u')) := by
    simp only [kBB, kOf, mul_assoc]
  rw [e]
  exact key

theorem kB_inv_fix {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {w : D.what₂.Word}
    {rs : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (c : ColSys X w rs) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (γ : Gam X w) (hk : kB c Λ γ ∈ X.B.I.Kset) :
    ∀ a, CongG X (X.B.I.fmat (kB c Λ γ)⁻¹ *ᵥ X.f0 a) (X.f0 a) := by
  have e : (((iotaF X w γ * c.h (c.base Λ) : Hfin X w) : X.B.I.Gf) * X.xu w)⁻¹ *
      ((c.h (c.base Λ) : X.B.I.Gf) * X.xu w) = (kB c Λ γ)⁻¹ := by
    unfold kB
    push_cast
    group
  have hK : (((iotaF X w γ * c.h (c.base Λ) : Hfin X w) : X.B.I.Gf) * X.xu w)⁻¹ *
      ((c.h (c.base Λ) : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset := by
    rw [e]; exact mem_Kset_inv X hk
  have h := (column_fixed_holds X w (iotaF X w γ * c.h (c.base Λ)) (c.h (c.base Λ)) hK).1
  rw [e] at h
  exact h

theorem one_fix {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (w : D.what₂.Word) (h1 : (1 : X.B.I.Gf) ∈ X.B.I.Kset) :
    ∀ a, CongG X (X.B.I.fmat (1 : X.B.I.Gf) *ᵥ nxt X.e0 X.z0 a) (nxt X.e0 X.z0 a) := by
  have hK : (((1 : Hfin X w) : X.B.I.Gf) * X.xu w)⁻¹ * (((1 : Hfin X w) : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset := by
    rw [inv_mul_cancel]; exact h1
  have h := (column_fixed_holds X w 1 1 hK).2
  simpa only [inv_mul_cancel] using h

end ChiLeft

theorem chiNLeft_holds (hB : ChiNBiAll) : ChiNLeft := by
  intro D X Y u u' Λ Λ' hΛ hΛ' γ hk p
  have hκ := ChiLeft.kBB_mem Y u u' hΛ hΛ' p
  have h1 : (1 : X.B.I.Gf) ∈ X.B.I.Kset := by
    have h := mem_Kset_mul X hk (mem_Kset_inv X hk)
    rwa [mul_inv_cancel] at h
  have h := hB D X (kBB Y u u' Λ Λ' p.1.1) (kB (Y.cs u) Λ γ) 1 hκ hk h1
    (ChiLeft.kB_inv_fix (Y.cs u) Λ γ hk) (ChiLeft.one_fix u h1)
  rwa [mul_one] at h

end Formalism.L2.SG.Pf.SatGramActL
