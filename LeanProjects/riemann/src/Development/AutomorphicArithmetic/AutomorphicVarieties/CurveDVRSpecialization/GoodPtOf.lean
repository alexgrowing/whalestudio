import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransferAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PointLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IrrOfConn
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CharpolyFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.InjTest

set_option linter.overlappingInstances false

open IsLocalRing Matrix UpperTheory.V UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Pr

section

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
  {F : Frame l (ResidueField O)} {n : ℕ} {G : W.GFrame l} {r : W.Resid G O n} (K : TwLink F r)
  {A A' : Type} [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A']

private theorem tw_map (f : A →ₐ[O] A') (ρ : NRep F n A) :
    (W.GDet.ofRep (K.tw ρ)).map (f : A →+* A') = W.GDet.ofRep (K.tw (ρ.map (f : A →+* A'))) := by
  rw [(CA.d_gmap (W.GDet.ofRep (K.tw ρ))).2.2.2]
  congr 1
  ext g i j
  simp [TwLink.tw, TwLink.κA]

private theorem twψ_map (f : A →ₐ[O] A') (ρ : NRep F n A) (v : G.Vl) (i : Fin n) :
    W.pushCh (f : A →+* A') (K.twψ ρ v i) = K.twψ (ρ.map (f : A →+* A')) v i := by
  ext g
  simp [TwLink.twψ, TwLink.κA]

private theorem maps_comp (B : W.UniversalOrdinaryDeterminantRing r) (φ : B.B →ₐ[O] A) (f : A →ₐ[O] A') (ρ : NRep F n A)
    (h : B.u.Maps (φ : B.B →+* A) (W.GDet.ofRep (K.tw ρ)) (K.twψ ρ)) :
    B.u.Maps ((f.comp φ : B.B →ₐ[O] A') : B.B →+* A') (W.GDet.ofRep (K.tw (ρ.map (f : A →+* A'))))
      (K.twψ (ρ.map (f : A →+* A'))) := by
  refine ⟨?_, fun v i => ?_⟩
  · rw [← tw_map, ← h.1, (CA.d_gmap B.u.D).2.1]
    rfl
  · rw [← twψ_map, ← h.2]
    rfl

private theorem maps_of_inj (B : W.UniversalOrdinaryDeterminantRing r) (φ : B.B →ₐ[O] A) (f : A →ₐ[O] A') (hf : Function.Injective f)
    (ρ : NRep F n A)
    (h : B.u.Maps ((f.comp φ : B.B →ₐ[O] A') : B.B →+* A') (W.GDet.ofRep (K.tw (ρ.map (f : A →+* A'))))
      (K.twψ (ρ.map (f : A →+* A')))) :
    B.u.Maps (φ : B.B →+* A) (W.GDet.ofRep (K.tw ρ)) (K.twψ ρ) := by
  have hc : ((f.comp φ : B.B →ₐ[O] A') : B.B →+* A') = (f : A →+* A').comp (φ : B.B →+* A) := rfl
  have hinj : Function.Injective (f : A →+* A') := hf
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun v i => ?_⟩
  · refine (UpperTheory.V.AlgebraTools.Det.injTest (X := Unit) (fun _ => A') (fun _ => (f : A →+* A'))
      (fun a ha => hinj (by rw [ha (), map_zero]))).1 _ _ (fun _ => ?_)
    rw [(UpperTheory.V.CA.d_gmap B.u.D).2.1, ← hc, h1, tw_map]
  · ext g
    have := congrArg (fun χ => ((χ g : A'ˣ) : A')) (h2 v i)
    simp only [hc, ← twψ_map] at this
    exact hinj this

end

theorem UpperTheory.V.Pr.goodPtOf :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (n : ℕ) (T : UpperTheory.V.Pr.Setup F n), T.GoodPtOf := by
  intro l _ O _ _ _ _ _ F n T Φ hΦ J hJ A _ _ _ ρ hρ K' _ j hj hirr
  have hcl : CA.IsCL O A :=
    { noeth := PrincipalIdealRing.isNoetherianRing
      complete := inferInstance
      isLocalHom := inferInstance
      res_fin := Module.Finite.of_finite }
  obtain ⟨ξ, hξ, -⟩ := point_loc T.ok T.n23 T.S A hcl (ResidueField.map (algebraMap O A)) (fun _ => rfl) ρ
    hρ.cont hρ.bar
  have hTI : T.S.u.TI (RingHom.ker (j.comp (ξ : T.S.A →+* A))) := by
    refine (types T.ok T.n23 T.S K' (j.comp (ξ : T.S.A →+* A))).1.1 ?_
    rw [← NRep.map_map, hξ]
    exact hirr
  have hle := hJ _ (RingHom.ker_isPrime _) hTI
  refine ⟨ξ.comp (T.S.inc.comp Φ), fun x hx => ?_, ?_⟩
  · have h1 := hle (Ideal.mem_map_of_mem _ hx)
    exact hj (Eq.trans h1 (map_zero j).symm)
  · have hu : T.S.u.map (T.S.A.val : T.S.A →+* T.S.R) = T.S.ρ := by
      refine NRep.ext ?_ ?_
      · ext g i j
        rfl
      · funext v i
        ext g
        rfl
    have hc : T.S.A.val.comp (T.S.inc.comp Φ) = T.S.B.val.comp Φ := AlgHom.ext fun _ => rfl
    have h2 := maps_comp T.K T.B (T.S.inc.comp Φ) ξ T.S.u
      (maps_of_inj T.K T.B (T.S.inc.comp Φ) T.S.A.val Subtype.val_injective T.S.u (by rw [hu, hc]; exact hΦ))
    rwa [hξ] at h2
