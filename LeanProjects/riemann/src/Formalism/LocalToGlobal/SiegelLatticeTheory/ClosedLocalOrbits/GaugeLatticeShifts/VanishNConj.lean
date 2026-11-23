import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictK
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut

namespace Formalism.L2.SG.Pf.VanishNConj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

theorem chiN_mul {x y : X.B.I.Gf} (hx : x ∈ X.K2) (hy : y ∈ X.K2) :
    chiN X (x * y) = chiN X x * chiN X y := by
  obtain ⟨hfe, hfz, -, -⟩ := reference_frame_congruences X
  have hf0 : ∀ a, X.f0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).2
  have hg := modulus_g_ne_zero X
  unfold chiN
  refine unitaryCongruence.psi_mul_of_Z X.B.I X.B.g X.psiEf_add X.psiEf_int hg ?_
  have h : (∑ a, hA X.B.I (X.f0 a) (X.B.I.fmat (x * y) *ᵥ nxt X.e0 X.z0 a)) -
      (∑ a, hA X.B.I (X.f0 a) (X.B.I.fmat x *ᵥ nxt X.e0 X.z0 a)) -
      (∑ a, hA X.B.I (X.f0 a) (X.B.I.fmat y *ᵥ nxt X.e0 X.z0 a)) =
      ∑ a, (hA X.B.I (X.f0 a) (X.B.I.fmat (x * y) *ᵥ nxt X.e0 X.z0 a) -
        hA X.B.I (X.f0 a) (X.B.I.fmat x *ᵥ nxt X.e0 X.z0 a) -
        hA X.B.I (X.f0 a) (X.B.I.fmat y *ᵥ nxt X.e0 X.z0 a)) := by
    simp only [Finset.sum_sub_distrib]
  rw [h]
  exact unitaryCongruence.Z_sum X.B.I X.B.g _ _ fun a _ =>
    unitaryCongruence.term_Z X.B.I X.B.g _ _ (unitaryCongruence.nxt_Z X.B.I X.B.g X.e0 X.f0 X.z0 hfe hfz a)
      (unitaryCongruence.Me_Q X.B.I X.B.g X.e0 X.f0 hf0 hfe a
        (unitaryCongruence.e_step X.B.I X.B.g X.e0 X.z0 X.bw hx.1 hx.2 a _
          (unitaryCongruence.nxt_cong X.B.I X.B.g X.e0 X.z0 X.bw hy.2 a)))

theorem chiL_conj {u : D.what₂.Word} {n : X.B.I.Gf} (hn : n ∈ X.NfinU u) (hnK : n ∈ X.B.I.Kset) :
    chiL X ((X.xu u)⁻¹ * n * X.xu u) = 1 := by
  unfold chiL
  exact unitaryCongruence.psi_Z X.B.I X.B.g X.psiEf_add X.psiEf_int (modulus_g_ne_zero X)
    (unitaryCongruence.Z_sum X.B.I X.B.g _ _ fun i _ => Z_bw hn hnK i)

theorem chiN_conj {u : D.what₂.Word} {n : X.B.I.Gf} (hn : n ∈ X.NfinU u) (hnK : n ∈ X.B.I.Kset) :
    chiN X ((X.xu u)⁻¹ * n * X.xu u) = X.chi2 ((X.xu u)⁻¹ * n * X.xu u) := by
  rw [level_char_eq_mul, chiL_conj X hn hnK, mul_one]

theorem kappa_Kset {Λ : Submodule (𝓞 D.host.E) (VS D).V} (a : X.B.I.Gf)
    (hlat : ∀ y : (VS D).V, y ∈ Λ ↔ X.B.I.fmat a⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf)
    {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hmap : Formalism.HermitianLatticesTheory.gmap n Λ = Λ) {x : X.B.I.GA}
    (hx : RatLink X x n) : a⁻¹ * x.2 * a ∈ X.B.I.Kset := by
  have key : a⁻¹ * (x.2 * a) ∈ X.B.I.Kset := by
    refine LatDictK.dict_K X _ _ {y | y ∈ Λ} (fun y => hlat y) (fun y => ?_)
    show y ∈ Λ ↔ _
    have e1 : y ∈ Λ ↔ n.symm y ∈ Λ := by
      conv_lhs => rw [← hmap]
      constructor
      · rintro ⟨z, hz, hzy⟩
        have : n.symm y = z := by rw [← hzy]; simp
        rw [this]; exact hz
      · intro h
        exact ⟨n.symm y, h, by simp⟩
    rw [e1, hlat, show (x.2 * a)⁻¹ = a⁻¹ * x.2⁻¹ from _root_.mul_inv_rev _ _,
      LatDictK.fmatK_mul, ← mulVec_mulVec, LatDictK.ratLink_incl_inv X hx]
  rwa [mul_assoc]

theorem core (u : D.what₂.Word) (hNK : UnipotentConjugateInLevel X u) (h : Hfin X u) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hlat : ∀ y : (VS D).V, y ∈ Λ ↔
      X.B.I.fmat ((h : X.B.I.Gf) * X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf)
    {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NLam Λ (lf D (X.Fu u)))
    (hx : RatLink X x n) :
    ((h : X.B.I.Gf) * X.xu u)⁻¹ * x.2 * ((h : X.B.I.Gf) * X.xu u) ∈ X.K2 ∧
    X.chi2 (((h : X.B.I.Gf) * X.xu u)⁻¹ * x.2 * ((h : X.B.I.Gf) * X.xu u)) = X.psiFinU u x.2 ∧
    ∀ k ∈ X.K2,
      chiN X (((h : X.B.I.Gf) * X.xu u)⁻¹ * x.2 * ((h : X.B.I.Gf) * X.xu u) * k) =
          X.psiFinU u x.2 * chiN X k ∧
      chiN X (k * (((h : X.B.I.Gf) * X.xu u)⁻¹ * x.2 * ((h : X.B.I.Gf) * X.xu u))) =
          chiN X k * X.psiFinU u x.2 := by
  have hxN : x.2 ∈ X.NfinU u := nLamNfin_holds D X u Λ x n hx hn
  have hc := nfinConj_holds X u h⁻¹ x.2 hxN
  have ec : ((h⁻¹ : Hfin X u) : X.B.I.Gf) * x.2 * ((h⁻¹ : Hfin X u) : X.B.I.Gf)⁻¹ =
      (h : X.B.I.Gf)⁻¹ * x.2 * (h : X.B.I.Gf) := by
    rw [Subgroup.coe_inv, inv_inv]
  rw [ec] at hc
  have hκK := kappa_Kset X ((h : X.B.I.Gf) * X.xu u) hlat hn.1.2 hx
  have eκ : ((h : X.B.I.Gf) * X.xu u)⁻¹ * x.2 * ((h : X.B.I.Gf) * X.xu u) =
      (X.xu u)⁻¹ * ((h : X.B.I.Gf)⁻¹ * x.2 * (h : X.B.I.Gf)) * X.xu u := by group
  have en : (h : X.B.I.Gf)⁻¹ * x.2 * (h : X.B.I.Gf) =
      X.xu u * (((h : X.B.I.Gf) * X.xu u)⁻¹ * x.2 * ((h : X.B.I.Gf) * X.xu u)) * (X.xu u)⁻¹ := by group
  have hnK : (h : X.B.I.Gf)⁻¹ * x.2 * (h : X.B.I.Gf) ∈ X.B.I.Kset := by
    rw [en]
    exact unitaryCongruence.K_mul X.B.I (unitaryCongruence.K_mul X.B.I (X.xu_K u) hκK) (unitaryCongruence.K_inv X.B.I (X.xu_K u))
  obtain ⟨hK2, hchi⟩ := hNK _ hc.1 hnK
  rw [hc.2] at hchi
  have hN : chiN X (((h : X.B.I.Gf) * X.xu u)⁻¹ * x.2 * ((h : X.B.I.Gf) * X.xu u)) = X.psiFinU u x.2 := by
    rw [eκ, chiN_conj X hc.1 hnK, hchi]
  rw [eκ] at hN ⊢
  refine ⟨hK2, hchi, fun k hk => ⟨?_, ?_⟩⟩
  · rw [chiN_mul X hK2 hk, hN]
  · rw [chiN_mul X hk hK2, hN]

end Formalism.L2.SG.Pf.VanishNConj

namespace Formalism.L2.SG.Pf

theorem nilradical_conj_level_of_mem (hN : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), UnipotentConjugateInLevel X u) :
    Formalism.L2.SG.TermOp.Vanish.NilradicalConjLevel := by
  intro D X Y u ρ x n hn hx
  exact VanishNConj.core X u (hN D X u) ((Y.cs u).h ρ) ((Y.cs u).lat_eq ρ) hn hx

theorem nilradical_conj_level_of_psi (hP : ∀ (D : D7) (X : HidaSetting D), PsiDd X) :
    Formalism.L2.SG.TermOp.Vanish.NilradicalConjLevel :=
  nilradical_conj_level_of_mem fun D X _ => unipotent_in_level_of_psi (hP D X)

end Formalism.L2.SG.Pf
