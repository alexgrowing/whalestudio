import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

theorem formsExport_eq : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd) (hE : IsEmpty D.nd.Loc)
    (hfg : ∀ i j b, (BsupT D T S i j b).FG) (hst : HkStab D T S In) (sd : SigData D T) (rho : RhoFam D T)
    (hrho : ∀ i σ b, Continuous fun g =>
      ((rho i σ b g : GL (Fin D.R.r) (T.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (T.O0 i))) (he : EIdem D)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (wt : WtData D T)
    (i : (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).Tw) (j : ℕ) (b : Bool) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
    ∃ e : (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Fm i j b ≃ₗ[FractionRing ((T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i)]
        Fm ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b,
      (∀ x, x ∈ (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Bsup i j b ↔
        e x ∈ Bsup ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b) ∧
      (∀ g x, e ((mkEx D T S In hE hfg hst sd rho hrho he Pq wt).actG i j b g x) =
        actG ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b
          (In.rho j h1 h2) (In.chi j h1 h2) g (e x)) ∧
      ∀ k P x, e ((mkEx D T S In hE hfg hst sd rho hrho he Pq wt).hkF i j b k P x) =
        algebraMap ((T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i)
            (FractionRing ((T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i)) (cHkT D T i b P : T.O i) ^ k •
          GlobalTheory.HeightCounting.hkF D ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b
            (In.hL j) (In.hs j h1 h2) k P (e x) := by
  intro D S In T hE hfg hst sd rho hrho he Pq wt i j b h1 h2
  let i' : T.Tw := i
  have hW : WKr D S j = (S.A j).WK := WKr_of D S h1 h2
  let e : (KT D T i' b ⊗[S.Ks] ↥(WKr D S j)) ≃ₗ[KT D T i' b] (KT D T i' b ⊗[S.Ks] ↥(S.A j).WK) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (KT D T i' b) (KT D T i' b)) (LinearEquiv.ofEq _ _ hW)
  have he1 : ∀ (a : KT D T i' b) (w : ↥(WKr D S j)), e (a ⊗ₜ[S.Ks] w) = a ⊗ₜ[S.Ks] (LinearEquiv.ofEq _ _ hW w) :=
    fun a w => rfl
  have hbc : ∀ (f : Module.End S.Ks ↥(WKr D S j)) (f' : Module.End S.Ks ↥(S.A j).WK),
      (∀ w, ((f w : ↥(WKr D S j)) : S.WL j) = (f' (LinearEquiv.ofEq _ _ hW w) : S.WL j)) →
      ∀ y, e (Module.End.baseChangeHom S.Ks (KT D T i' b) _ f y) = Module.End.baseChangeHom S.Ks (KT D T i' b) _ f' (e y) := by
    intro f f' hf y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a w =>
      show a ⊗ₜ[S.Ks] (LinearEquiv.ofEq _ _ hW (f w)) = a ⊗ₜ[S.Ks] (f' (LinearEquiv.ofEq _ _ hW w))
      exact congrArg (a ⊗ₜ[S.Ks] ·) (Subtype.ext (hf w))
    | add y z hy hz => rw [map_add, map_add, hy, hz, map_add, map_add]
  have hc : ∀ g', cR D S In.chi j g' = chiL S j (In.chi j h1 h2) g' := fun g' => dif_pos ⟨h1, h2⟩
  have hsm : ∀ (r : T.O i') (y : KT D T i' b ⊗[S.Ks] ↥(WKr D S j)),
      e ((show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) r) • y) =
        (show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) r) • e y := fun r y => e.map_smul _ y
  have hsm' : ∀ (r : T.O i') (y : KT D T i' b ⊗[S.Ks] ↥(S.A j).WK),
      e.symm ((show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) r) • y) =
        (show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) r) • e.symm y := fun r y => e.symm.map_smul _ y
  refine ⟨e, ?_, ?_, ?_⟩
  · let eO : (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Fm i j b →ₗ[(T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i] Fm ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b :=
      { toFun := fun y => e y, map_add' := fun y z => e.map_add y z, map_smul' := fun r y => hsm r y }
    let eO' : Fm ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b →ₗ[(T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i] (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Fm i j b :=
      { toFun := fun y => e.symm y, map_add' := fun y z => e.symm.map_add y z, map_smul' := fun r y => hsm' r y }
    have hle1 : (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Bsup i j b ≤ (Bsup ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b).comap eO := by
      show BsupT D T S i' j b ≤ _
      refine Submodule.span_le.mpr ?_
      rintro y ⟨w, hw, rfl⟩
      exact (Submodule.subset_span ⟨LinearEquiv.ofEq _ _ hW w, hw, rfl⟩ : _ ∈ Bsup ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b)
    have hle2 : Bsup ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b ≤ ((mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Bsup i j b).comap eO' := by
      refine Submodule.span_le.mpr ?_
      rintro y ⟨w, hw, rfl⟩
      exact (Submodule.subset_span ⟨(LinearEquiv.ofEq _ _ hW).symm w, hw, rfl⟩ : _ ∈ BsupT D T S i' j b)
    intro x
    refine ⟨fun hx => hle1 hx, fun hx => ?_⟩
    have h := hle2 hx
    rw [Submodule.mem_comap] at h
    change e.symm (e x) ∈ _ at h
    exact Eq.mp (congrArg (fun (z : (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Fm i j b) => z ∈ (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Bsup i j b) (e.symm_apply_apply x)) h
  · intro g x
    change e ((actEndT D T S In.rho In.chi i' j b (S.eG.symm g)) x) =
      (actEnd ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b (In.rho j h1 h2) (In.chi j h1 h2) (S.eG.symm g)) (e x)
    change e ((readK D T i' b (cR D S In.chi j (S.eG.symm g)))⁻¹ •
        Module.End.baseChangeHom S.Ks (KT D T i' b) ↥(WKr D S j) (rhoR D S In.rho j (S.eG.symm g)) x) =
      (readK D T i' b (chiL S j (In.chi j h1 h2) (S.eG.symm g)))⁻¹ •
        Module.End.baseChangeHom S.Ks (KT D T i' b) ↥(S.A j).WK (rhoKG S j (In.rho j h1 h2) (S.eG.symm g)) (e x)
    rw [LinearEquiv.map_smul, hbc _ (rhoKG S j (In.rho j h1 h2) (S.eG.symm g)) (fun w => rfl) x, hc]
  · intro k P x
    change e ((show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) (cHkT D T i' b P : T.O i')) ^ k •
        Module.End.baseChangeHom S.Ks (KT D T i' b) ↥(WKr D S j) (hLr D S In j k P) x) =
      (show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) (cHkT D T i' b P : T.O i')) ^ k •
        Module.End.baseChangeHom S.Ks (KT D T i' b) ↥(S.A j).WK
          (((In.hL j k P).restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK)
            fun x hx => In.hs j h1 h2 k P x hx) (e x)
    rw [LinearEquiv.map_smul, hbc _ _ ?_ x]
    intro w
    rw [hLr, dif_pos ⟨h1, h2⟩]
    rfl

end GlobalTheory.HeightCounting.FormsStep
