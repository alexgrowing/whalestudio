import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.SpecOfF
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNormHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ContinuousInvT
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TyFact
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupport
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.MemFn
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.MemComm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.FrameTh
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.FacCont
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.SplitC
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.SepConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.AdmCusp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfAdm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfIdem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PConvRing
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAvgK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfCen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSetupBasic

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp cj lev GLw)
open UpperTheory.Gal.LocalSmoothExtension UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl
open Formalism.UG (Hecke conv)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Spc

private theorem conv_add_r {X : Type} [Group X] {K : Subgroup X} (hK : Formalism.UG.IsCommensurated K) {e : X → ℂ}
    (he : e ∈ Hecke ℂ K) (f f' : X → ℂ) : conv K e (f + f') = conv K e f + conv K e f' := by
  have hs := Formalism.UG.P.finite_support_cosets hK ((Formalism.UG.P.mem_hecke_iff ℂ K e).1 he).2
  funext x
  have hsub : ∀ (φ : X → ℂ), (Function.support fun q : X ⧸ K => e q.out * φ (q.out⁻¹ * x)).Finite := fun φ =>
    hs.subset fun q hq => left_ne_zero_of_mul hq
  simp only [conv, Pi.add_apply, mul_add]
  exact finsum_add_distrib (hsub f) (hsub f')

private theorem conv_smul_r {X : Type} [Group X] (K : Subgroup X) (e : X → ℂ) (c : ℂ) (f : X → ℂ) :
    conv K e (c • f) = c • conv K e f := by
  funext x
  simp only [conv, Pi.smul_apply, smul_eq_mul]
  refine (finsum_congr fun q => mul_left_comm _ _ _).trans ?_
  simpa only [smul_eq_mul] using (smul_finsum c fun q : X ⧸ K => e q.out * f (q.out⁻¹ * x)).symm

private theorem span_fix {X : Type} [Group X] {K : Subgroup X} (hK : Formalism.UG.IsCommensurated K) {e : X → ℂ}
    (he : e ∈ Hecke ℂ K) (s : Set (X → ℂ)) (hs : ∀ f ∈ s, conv K e f = f) :
    ∀ f ∈ Submodule.span ℂ s, conv K e f = f := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf => exact hs f hf
  | zero => funext x; simp [conv]
  | add f f' _ _ h h' => rw [conv_add_r hK he, h, h']
  | smul c f _ h => rw [conv_smul_r, h]

end UpperTheory.Gal.Spc

theorem UpperTheory.Gal.Spc.specData :
    UpperTheory.Gal.Int.Geo.Pl.WtOf → UpperTheory.Gal.Spc.SpecData := by
  intro hWt E _ _ _ A n p _ S F x U w₀ Up V hodd hSc hGen hOff hq r W hAux N hrN hStab L hw Ty hTy hEx J g θ hseen
  obtain ⟨⟨Lv, hLv⟩, ⟨Kw, hKwo, hKwc, hKwF⟩, hJo, hJc, hker, hcusp⟩ :=
    UpperTheory.Gal.Spc.tyTop E A n p S F x U w₀ Up V hodd hSc hGen hOff hq r W hAux N hrN hStab L hw Ty hTy
  obtain ⟨u, hu, u', hu', heu, hue, hinv, hcomm, hX⟩ :=
    UpperTheory.Gal.Spc.auxFn E A n p S F x U w₀ Up V hodd hSc hGen hOff hq r W hAux N hrN hStab L hw Ty hTy
  have hmem := UpperTheory.Gal.Spc.memFn E A n p S F x U w₀ Up V hodd hSc hGen hOff hq r W hAux N hrN hStab L hw Ty hTy
  have hmc := UpperTheory.Gal.Spc.memComm E A n p S F x U w₀ Up V hodd hSc hGen hOff hq r W hAux N hrN hStab L hw Ty hTy
  obtain ⟨thQ, hthQ, hEig⟩ :=
    UpperTheory.Gal.Spc.eigEx E A n p S F x U w₀ Up V hodd hSc hGen hOff hq r W hAux N hrN hStab L hw Ty hTy
  have hLK : Lv.K.toSubgroup = Ty.K₀ := hLv.trans hTy.K₀_eq.symm
  have hid : TfIdem := pTfIdem pTfAdm (pTfCen pAvgK pTfAdm)
  have hAdm1 : Ty.admitted (Ty.tf 1) := (pTfAdm _ _ Ty 1 (map_one _)).1
  have he : Ty.tf 1 ∈ Hecke ℂ Ty.K₀ := hAdm1.1
  have hψ : ∀ j, (g j).fn ∈ Hecke ℂ Ty.K₀ := fun j => (hmem (g j) (θ j) (hseen j)).1
  have hring := pConvRing _ Ty.K₀ Ty.cms
  have hoff : ∀ f ∈ Off2 W L Ty, conv Ty.K₀ (Ty.tf 1) f = f := by
    refine UpperTheory.Gal.Spc.span_fix Ty.cms he _ ?_
    rintro f ⟨h, hh, -, rfl⟩
    exact (hid _ _ Ty h hh).2.2
  have hrel : Rel (conv Ty.K₀) (fun j => (g j).fn) (Ty.tf 1) u u' :=
    { idem := (hid _ _ Ty 1 (map_one _)).2.1
      eT := fun j => hoff _ (hmc (g j) (g j) (θ j) (θ j) (hseen j) (hseen j)).1
      eu := by rw [hue, heu]
      TT := fun j j' => (hmc (g j) (g j') (θ j) (θ j') (hseen j) (hseen j')).2
      uT := fun j => by
        show conv Ty.K₀ u (conv Ty.K₀ (g j).fn (Ty.tf 1)) = conv Ty.K₀ (g j).fn (conv Ty.K₀ u (Ty.tf 1))
        rw [hcomm _ (hmc (g j) (g j) (θ j) (θ j) (hseen j) (hseen j)).1, hue,
          (hring _ (hψ j) _ he).2 u hu, heu]
      inv := by rw [hue]; exact hinv }
  obtain ⟨w₁, hw₁⟩ := hAux.nonempty
  obtain ⟨P₁, hP₁⟩ := hEx.1 w₁.1 w₁.2.2
  obtain ⟨P, hP⟩ := hEx.1 w₀ hw.2
  have hfac₀ : ∀ y, Ty.L.pr (F.j y) = comp w₀ y := by
    intro y
    rw [hTy.L_eq]
    exact (hTy.fac ⟨w₀, hw⟩).1 y
  have hcont : Continuous Ty.L.pr := by
    rw [hTy.L_eq]
    exact UpperTheory.Gal.Spc.facCont E A n p S F ⟨w₀, hw⟩ _ (hTy.fac ⟨w₀, hw⟩)
  have hat : ∀ y, P.at y = (Ty.L.pr y : Matrix (Fin n) (Fin n) (w₀.adicCompletion E)) := by
    intro y
    obtain ⟨y', rfl⟩ := F.surj y
    rw [hP, hfac₀]
  letI : MeasurableSpace (w₀.adicCompletion E) := borel _
  haveI : BorelSpace (w₀.adicCompletion E) := ⟨rfl⟩
  obtain ⟨τ, hτ, hτ2, Sp, hSp⟩ := UpperTheory.Gal.Spc.splitC p S.G Lv (w₀.adicCompletion E) P Ty.L hcont hat Kw hKwo hKwc
    (by rw [hLK]; exact hKwF)
  have hCe : Sp.Cusp (Ty.tf 1) := by
    intro h
    have h0 := UpperTheory.Gal.Spc.cuspIrr_kFinite_rep_eq_centralCuspForm S.G.GAf (w₀.adicCompletion E) n Ty hJo hJc hker hcusp (Ty.tf 1) hAdm1 h.1 h.2
    have h1 : (fun y => Ty.tf 1 (Sp.e.symm (y, h))) = fun y => Ty.tf 1 (Ty.L.loc y * h.1) :=
      funext fun y => by rw [hSp]; rfl
    rw [h1]
    exact h0
  have hA : ∀ m : ℕ, 1 ≤ m → ∃ A' : Set S.G.GAf,
      (∀ y ∈ A', (P₁.at y).charpoly.Separable ∧ GlobalTheory.LKCx.RegAf S.G y) ∧
      (∀ j a, (g j).fn a ≠ 0 → ∀ y ∈ A', a * y ∈ A') ∧
      ∀ y, powFn Lv.K.toSubgroup u (Ty.tf 1) m y ≠ 0 → y ∈ A' := by
    intro m hm
    obtain ⟨X, hX1, hX2⟩ := hX m hm
    refine ⟨{y | ∀ w ∈ W, (L w).pr y ∈ X w}, ?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨y', rfl⟩ := F.surj y
      have hsep : ∀ w ∈ W, (comp w.1 y').val.charpoly.Separable := fun w hw' => by
        have h := (hX1 w hw' _ (hy w hw')).1
        rwa [(hTy.fac w).1] at h
      refine ⟨?_, hEx.2 r hAux.prime hAux.ne y' ?_⟩
      · rw [hP₁]
        exact hsep w₁ hw₁
      · intro v hv
        obtain ⟨w, hwW, rfl | rfl⟩ := hAux.half.all v hv
        · exact hsep w hwW
        · exact UpperTheory.Gal.Spc.sepConj E n y' w.1 (hsep w hwW)
    · intro j a ha y hy w hw'
      rw [map_mul]
      exact (hX1 w hw' _ (hy w hw')).2 _ ((hmem (g j) (θ j) (hseen j)).2.1 a ha w hw')
    · intro y hy
      rw [hLK] at hy
      exact (hX2 y hy).2
  have hso : UpperTheory.Gal.Spc.SpecOfF := UpperTheory.Gal.Spc.specOfF
  unfold UpperTheory.Gal.Spc.SpecOfF UpperTheory.Gal.Spc.ForPlaces at hso
  have hso' := @hso p _ S.G (pSetupBasic E A n p S).1 Lv (w₀.adicCompletion E) _ _ _ _ _ _ _ P Ty.L.pr.ker _ τ hτ hτ2 Sp
    (w₁.1.adicCompletion E) _ _ P₁ (UpperTheory.Gal.G1.FinCls_holds E A n p S)
  have key := hso'
    S.D S.L V.lam (Module.Dual ℂ V.W.Sp) ((UpperTheory.Gal.CertificateRingHomMap.xi V.W V.jz).comp thQ) (hWt E A n p S x U w₀ Up V thQ hthQ)
    J (fun j => (g j).fn) θ (Ty.tf 1) u u' (by rw [hLK]; exact hψ) (by rw [hLK]; exact he) (by rw [hLK]; exact hu)
    (by rw [hLK]; exact hu') (by rw [hLK]; exact hrel) hCe hA
    (by rw [hLK]; exact hEig J g θ hseen)
  obtain ⟨m, hm, hspec⟩ := key
  have hW := (UpperTheory.Gal.Spc.words p S.G Lv J (fun j => (g j).fn) (Ty.tf 1) u u' (by rw [hLK]; exact hψ)
    (by rw [hLK]; exact he) (by rw [hLK]; exact hu) (by rw [hLK]; exact hrel) m).1
  obtain ⟨X, -, hX2⟩ := hX m hm
  rw [hLv] at hspec hW
  refine ⟨_, ⟨hW, fun y hy => ?_⟩, hspec⟩
  rw [← hTy.K₀_eq] at hy
  exact (hX2 y hy).1
