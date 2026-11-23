import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUniformisationIsComplexUniformisation
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

theorem kch_eq_one_of_wchar {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {S : Type} [CommRing S] (t : Ix Dw → Sˣ)
    (h : wchar (Formalism.L2.Pj.ex Dw (fun _ => 1) 0) t = wchar (Formalism.L2.Pj.ex Dw (fun _ => 0) 2) t) : kch t = 1 := by
  rw [kch_eq, mul_inv_eq_one]
  apply Units.ext
  simp only [wchar, Fintype.prod_option, Formalism.L2.Pj.ex, pow_zero, pow_one, one_mul, Finset.prod_const_one,
    mul_one] at h
  rw [Units.coe_prod, Units.val_pow_eq_pow_val]
  exact h

theorem rootVal_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)), Formalism.L2.PjFree.GoodEmb c σ → ModelBase M → NegXi M → FramesOK e F M un → ∀ (y : FrPt Xo c (CAt σ)) (v v' : ℂ), RootVal (unfOf e F M un) y v → RootVal (unfOf e F M un) y v' → v = v' := by
  intro E _ _ _ H Dw l Xo c σ g e F r M un hσ hM hN hun y v v' hv hv'
  obtain ⟨k, x, t, ht, rfl⟩ := hv
  obtain ⟨k', x', t', ht', rfl⟩ := hv'
  obtain ⟨-, hmul, hinv, huniq⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)
  have h0 : FrBor (t * t'⁻¹) (un k x) (un k' x') := hmul _ _ _ _ _ ht (hinv _ _ _ ht')
  obtain ⟨γ, hγ, b, hb, heq⟩ := (fibre_unfOf e F M un hun hM
    (GlobalTheory.FibreFlag.fibTri E H Dw l Xo c σ g e F r M hσ hM hN) k k' x x').1 ⟨_, h0⟩
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 heq
  have h3 : x'.1 = rmul (lact γ x.1) b := eq_of_heq h2
  have hxg : lact γ x.1 ∈ (M.X k').dom := (hM.domStab k' x.1 x.2).2 γ hγ
  obtain ⟨t1, ht1, hw1⟩ := hun.2.2.1 k' γ hγ x hxg
  have hxb : rmul (⟨lact γ x.1, hxg⟩ : (M.X k').dom).1 b ∈ (M.X k').dom := by
    have hx2 := x'.2
    rw [h3] at hx2
    exact hx2
  obtain ⟨t2, ht2, hw2⟩ := hun.2.1 k' ⟨lact γ x.1, hxg⟩ b hb hxb
  have hx' : (⟨rmul (lact γ x.1) b, hxb⟩ : (M.X k').dom) = x' := Subtype.ext h3.symm
  rw [hx'] at ht2
  have h12 : t * t'⁻¹ = t1 * t2 := huniq _ _ _ _ h0 (hmul _ _ _ _ _ ht1 ht2)
  have d1 : Formalism.L2.Pj.Dom (fun _ : (E →+* ℂ) × ℕ => 1) 0 := ⟨fun _ => antitone_const, by decide⟩
  have d2 : Formalism.L2.Pj.Dom (fun _ : (E →+* ℂ) × ℕ => 0) 2 := ⟨fun _ => antitone_const, by decide⟩
  have k1 : kch t1 = 1 := kch_eq_one_of_wchar t1 ((hw1 _ _ d1).trans (hw1 _ _ d2).symm)
  have hla : Formalism.L2.PjFree.laU (unfOf e F M un) (fun _ => 1) 0 k' =
      Formalism.L2.PjFree.laU (unfOf e F M un) (fun _ => 0) 2 k' := by
    funext τ j
    simp only [Formalism.L2.PjFree.laU]
    split_ifs <;> simp
  have k2 : kch t2 = 1 :=
    kch_eq_one_of_wchar t2 ((hw2 _ _ d1).trans ((congrArg (fun la => bchar la b) hla).trans (hw2 _ _ d2).symm))
  have hk := congrArg kch h12
  rw [kch_mul, kch_mul, kch_inv, k1, k2, one_mul, mul_inv_eq_one] at hk
  rw [hk]

end GlobalTheory.KeyFourth
