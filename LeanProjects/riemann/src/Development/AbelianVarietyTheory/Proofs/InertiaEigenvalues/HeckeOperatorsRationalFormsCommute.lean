import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorBaseChangeForms
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw Formalism.IndefR.NX
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HkKs

theorem comm_of_conj {K F V : Type} [Field K] [AddCommGroup F] [Module K F] [AddCommGroup V] [Module K V]
    (e : F ≃ₗ[K] V) (A B : Module.End K F) (A' B' : Module.End K V) (a c : K) (ha : a ≠ 0) (hc : c ≠ 0)
    (hA : ∀ x, e (A x) = a • A' (e x)) (hB : ∀ x, e (B x) = c • B' (e x)) (h : A * B = B * A) :
    A' * B' = B' * A' := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  have h1 : e (A (B x)) = (a * c) • A' (B' (e x)) := by
    rw [hA, hB, map_smul, smul_smul]
  have h2 : e (B (A x)) = (a * c) • B' (A' (e x)) := by
    rw [hB, hA, map_smul, smul_smul, mul_comm c a]
  have h3 : e (A (B x)) = e (B (A x)) := by
    rw [← Module.End.mul_apply, h, Module.End.mul_apply]
  rw [h1, h2] at h3
  have h4 := congrArg (fun z => (a * c)⁻¹ • z) h3
  simp only [inv_smul_smul₀ (mul_ne_zero ha hc)] at h4
  simpa using h4

theorem baseChange_inj {Ks K M : Type} [Field Ks] [Field K] [Algebra Ks K] [AddCommGroup M] [Module Ks M]
    {f g : Module.End Ks M}
    (h : Module.End.baseChangeHom Ks K M f = Module.End.baseChangeHom Ks K M g) : f = g := by
  have hinj : Function.Injective fun y : M => ((1 : K) ⊗ₜ[Ks] y : K ⊗[Ks] M) := by
    have h0 := Module.Flat.rTensor_preserves_injective_linearMap (M := M) (Algebra.linearMap Ks K)
      (algebraMap Ks K).injective
    intro y y' hy
    apply (TensorProduct.lid Ks M).symm.injective
    apply h0
    simpa using hy
  ext x
  apply hinj
  exact LinearMap.congr_fun h ((1 : K) ⊗ₜ[Ks] x)

end GlobalTheory.HkKs

namespace GlobalTheory.HkKs

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem opK_comm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks)
    (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS Rl cG S) (H : NExpRealH Rl cG S Y), CommG D → HkComm D →
    ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (b : Bool) k P k' P', HkIdx i k P → HkIdx i k' P' →
      GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) *
                   GlobalTheory.GoodSS.opK S j (H.hL j k' P') (fun x hx => H.hs j h1 h2 k' P' x hx) =
        GlobalTheory.GoodSS.opK S j (H.hL j k' P') (fun x hx => H.hs j h1 h2 k' P' x hx) *
          GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) ∧
      ∀ g : S.G, GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) * rhoKG S j (Y.rho j h1 h2) g =
        rhoKG S j (Y.rho j h1 h2) g * GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG S Y H hCG hHk i hi j h1 h2 b k P k' P' hP hP'
  have hj : j ∈ Finset.Icc 1 D.R.m := Finset.mem_Icc.2 ⟨h1, h2⟩
  have hc : ∀ k P, H.cHk i b k P ≠ 0 := fun k P => by
    rw [H.cHk_pow]; exact pow_ne_zero _ (H.cHk_unit i b P).ne_zero
  have hkE : ∀ k P, HkIdx i k P → ∀ x, Y.eF i j b h1 h2 (D.nexp.hkF i j b k P x) =
      H.cHk i b k P • hkFR S i j b (H.hL j) (H.hs j h1 h2) k P (Y.eF i j b h1 h2 x) := by
    intro k P hP x
    exact H.hkEq i j b h1 h2 k P x hP.2.2.2 hP.2.2.1 hP.2.1
  constructor
  · have hcm := comm_of_conj (Y.eF i j b h1 h2) (D.nexp.hkF i j b k P) (D.nexp.hkF i j b k' P') _ _ _ _
      (hc k P) (hc k' P') (hkE k P hP) (hkE k' P' hP') (hHk i hi j hj b k P k' P' hP hP').eq
    apply baseChange_inj (K := KB S i b)
    rw [map_mul, map_mul]
    exact hcm
  · intro g
    have hne : (show FractionRing (D.ntw.O i) from (readLL0 S i b (chiL S j (Y.chi j h1 h2) (S.eG.symm (S.eG g))))⁻¹) ≠ 0 := by
      refine inv_ne_zero ((_root_.map_ne_zero _).2 fun h0 => ?_)
      exact Units.ne_zero _ (congrArg Subtype.val h0)
    have hA : ∀ x, Y.eF i j b h1 h2 (D.nexp.actG i j b (S.eG g) x) =
        (show FractionRing (D.ntw.O i) from (readLL0 S i b (chiL S j (Y.chi j h1 h2) (S.eG.symm (S.eG g))))⁻¹) •
          (show Module.End (FractionRing (D.ntw.O i)) (Fm S i j b) from
            Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (rhoKG S j (Y.rho j h1 h2) (S.eG.symm (S.eG g))))
            (Y.eF i j b h1 h2 x) := by
      intro x
      rw [Y.act]
      rfl
    have hCG' : (D.nexp.actG i j b (S.eG g)).toLinearMap * D.nexp.hkF i j b k P =
        D.nexp.hkF i j b k P * (D.nexp.actG i j b (S.eG g)).toLinearMap := hCG i hi b j hj (S.eG g) k P hP
    have hcm := comm_of_conj (Y.eF i j b h1 h2) _ _ _ _ _ _ hne (hc k P) hA (hkE k P hP) hCG'
    rw [MulEquiv.symm_apply_apply] at hcm
    symm
    apply baseChange_inj (K := KB S i b)
    rw [map_mul, map_mul]
    exact hcm

end GlobalTheory.HkKs
