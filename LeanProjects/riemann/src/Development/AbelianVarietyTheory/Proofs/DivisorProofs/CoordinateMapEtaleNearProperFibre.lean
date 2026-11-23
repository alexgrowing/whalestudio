import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNearPointOfEtaleOnFibreSmooth
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FibEt

@[reassoc]
theorem map_fst' {X Y Z X' Y' Z' : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (f' : X' ⟶ Z') (g' : Y' ⟶ Z') (i₁ : X ⟶ X')
    (i₂ : Y ⟶ Y') (i₃ : Z ⟶ Z') (h1 : f ≫ i₃ = i₁ ≫ f') (h2 : g ≫ i₃ = i₂ ≫ g') :
    pullback.map f g f' g' i₁ i₂ i₃ h1 h2 ≫ pullback.fst f' g' = pullback.fst f g ≫ i₁ :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem map_snd' {X Y Z X' Y' Z' : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (f' : X' ⟶ Z') (g' : Y' ⟶ Z') (i₁ : X ⟶ X')
    (i₂ : Y ⟶ Y') (i₃ : Z ⟶ Z') (h1 : f ≫ i₃ = i₁ ≫ f') (h2 : g ≫ i₃ = i₂ ≫ g') :
    pullback.map f g f' g' i₁ i₂ i₃ h1 h2 ≫ pullback.snd f' g' = pullback.snd f g ≫ i₂ :=
  pullback.lift_snd _ _ _

end GlobalTheory.Mum.FibEt

namespace GlobalTheory.Mum.FibEt

theorem exists_residue_factor {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (π : S ⟶ Sp R) (s : S)
    (hs : π s = closedPoint R) :
    ∃ κ : ResidueField R →+* S.residueField s, S.fromSpecResidueField s ≫ π = spMap (κ.comp (residue R)) := by
  let φ := Spec.preimage (S.fromSpecResidueField s ≫ π)
  have hφ : Spec.map φ = S.fromSpecResidueField s ≫ π := Spec.map_preimage _
  have hpt : ∀ t : Spec (S.residueField s), (Spec.map φ) t = closedPoint R := by
    intro t
    rw [hφ, Scheme.Hom.comp_apply]
    have : S.fromSpecResidueField s t = s := by
      have := Set.mem_range_self (f := ⇑(S.fromSpecResidueField s)) t
      rwa [Scheme.range_fromSpecResidueField] at this
    rw [this, hs]
  have hker : ∀ r ∈ maximalIdeal R, φ.hom r = 0 := by
    intro r hr
    let t : Spec (S.residueField s) := closedPoint (S.residueField s)
    have h1 : (PrimeSpectrum.comap φ.hom t) = closedPoint R := hpt t
    have h2 : r ∈ (PrimeSpectrum.comap φ.hom t).asIdeal := by rw [h1]; exact hr
    simpa [t, closedPoint] using h2
  refine ⟨Ideal.Quotient.lift (maximalIdeal R) φ.hom hker, ?_⟩
  rw [← hφ]
  rfl

end GlobalTheory.Mum.FibEt

namespace GlobalTheory.Mum.FibEt

theorem smooth_affineSpace_sp (R : Type) [CommRing R] (g : ℕ) : Smooth (𝔸(Fin g; Sp R) ↘ Sp R) := by
  have e : (𝔸(Fin g; Sp R) ↘ Sp R) = (AffineSpace.isoOfIsAffine (Fin g) (Sp R)).hom ≫
      Spec.map (CommRingCat.ofHom MvPolynomial.C) ≫ (Sp R).isoSpec.inv := by
    rw [← AffineSpace.isoOfIsAffine_inv_over (n := Fin g) (S := Sp R), Iso.hom_inv_id_assoc]
  rw [e]
  haveI : Algebra.Smooth Γ(Sp R, ⊤) (MvPolynomial (Fin g) Γ(Sp R, ⊤)) := ⟨inferInstance, inferInstance⟩
  have : Smooth (Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := Γ(Sp R, ⊤)) (σ := Fin g)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr inferInstance
  infer_instance

end GlobalTheory.Mum.FibEt

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Mum.fibre_etale_near : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (E : Emb M.π G') (P' : Scheme.{0}) (b : P' ⟶ PSpace R E.N) (X : E.H.toScheme.Opens) (a : X.toScheme ⟶ P'), a ≫ b = X.ι ≫ E.f → ∀ (x : P') (y : E.Y.left), E.j y = b x → (b ≫ PSpace.str R E.N) x = closedPoint R → ∀ (W0 : (PSpace R E.N).Opens) (g : ℕ) (τ0 : W0.toScheme ⟶ 𝔸(Fin g; Sp R)) (O : E.Y.left.Opens) (e : O.toScheme ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) (spMap (residue R))), y ∈ O → (O : Set E.Y.left) ⊆ E.j ⁻¹' W0 → τ0 ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = W0.ι ≫ PSpace.str R E.N → Etale e → e ≫ pullback.snd _ _ = O.ι ≫ E.Y.hom → (∀ (T : Scheme.{0}) (t : T ⟶ O.toScheme) (w : T ⟶ W0.toScheme), w ≫ W0.ι = t ≫ O.ι ≫ E.j → t ≫ e ≫ pullback.fst _ _ = w ≫ τ0) → ∀ (c : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) M.π), c ≫ pullback.fst _ _ = (a ∣_ (b ⁻¹ᵁ W0)) ≫ (b ∣_ W0) ≫ τ0 → c ≫ pullback.snd _ _ = (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom → ∀ z : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme, ((a ⁻¹ᵁ (b ⁻¹ᵁ W0)).ι ≫ a) z = x → ∃ U : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme.Opens, z ∈ U ∧ Etale (U.ι ≫ c) := by
  intro R _ _ _ hR M G' _ _ hG E P' b X a hab x y hyb hx0 W0 g τ0 O e hyO hOW hτ0 he he2 he3 c hc1 hc2 z hz
  haveI : Smooth G'.hom := hG.smooth
  haveI : Smooth (𝔸(Fin g; Sp R) ↘ Sp R) := FibEt.smooth_affineSpace_sp R g
  haveI : Etale e := he
  let iV : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme ⟶ G'.left := (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).ι ≫ X.ι ≫ E.H.ι
  let p : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme ⟶ M.S := iV ≫ G'.hom
  have hh : c ≫ pullback.snd (𝔸(Fin g; Sp R) ↘ Sp R) M.π = p := by
    rw [hc2]; simp only [p, iV, Category.assoc]
  have hp : Smooth p := by dsimp only [p, iV]; infer_instance
  have key : a ≫ b ≫ PSpace.str R E.N = X.ι ≫ E.H.ι ≫ G'.hom ≫ M.π := by rw [reassoc_of% hab, E.f_over]
  have hs : M.π (p z) = closedPoint R := by
    have h1 := congrArg (fun f : X.toScheme ⟶ Sp R => f ((a ⁻¹ᵁ (b ⁻¹ᵁ W0)).ι z)) key
    simp only [Scheme.Hom.comp_apply] at h1 hz ⊢
    simp only [p, iV, Scheme.Hom.comp_apply]
    rw [← h1, hz]
    simpa [Scheme.Hom.comp_apply] using hx0
  obtain ⟨κ, hκ⟩ := FibEt.exists_residue_factor M.π (p z) hs
  obtain ⟨Ω', _, io, eG, l, -, hl1, hl2⟩ := E.fib (M.S.residueField (p z)) (M.S.fromSpecResidueField (p z)) κ hκ

  let Vs := (a ⁻¹ᵁ (b ⁻¹ᵁ W0))
  let x' : Sp Ω' ⟶ M.S := spMap io ≫ M.S.fromSpecResidueField (p z)
  let k' : Sp Ω' ⟶ Sp (ResidueField R) := spMap (io.comp κ)
  have hxk : x' ≫ M.π = k' ≫ spMap (residue R) := by
    simp only [x', k', Category.assoc, hκ, ← Spec.map_comp]; rfl
  have hpt : x' (closedPoint Ω') = p z := by
    simp only [x', Scheme.Hom.comp_apply]
    have := Set.mem_range_self (f := ⇑(M.S.fromSpecResidueField (p z))) ((spMap io) (closedPoint Ω'))
    rwa [Scheme.range_fromSpecResidueField] at this
  obtain ⟨w, hw1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := x') z (closedPoint Ω') hpt.symm
  let mG : pullback p x' ⟶ pullback G'.hom x' :=
    pullback.map p x' G'.hom x' iV (𝟙 _) (𝟙 _) (by simp [p]) (by simp)
  let gm : pullback p x' ⟶ pullback E.Y.hom k' := mG ≫ eG.hom.left
  have hgms : gm ≫ pullback.snd E.Y.hom k' = pullback.snd p x' := by
    have hA : eG.hom.left ≫ pullback.snd E.Y.hom k' = pullback.snd G'.hom x' := Over.w eG.hom
    simp only [gm, Category.assoc, hA, mG, FibEt.map_snd', Category.comp_id]
  have E1 : mG ≫ l = pullback.fst p x' ≫ Vs.ι ≫ X.ι := by
    rw [← cancel_mono E.H.ι, Category.assoc, hl1]
    exact FibEt.map_fst' _ _ _ _ _ _ _ _ _
  have E2 : gm ≫ pullback.fst E.Y.hom k' ≫ E.j = pullback.fst p x' ≫ Vs.ι ≫ a ≫ b := by
    simp only [gm, Category.assoc]
    erw [← hl2]
    rw [reassoc_of% E1, hab]
  have hgmw : (gm ≫ pullback.fst E.Y.hom k') w = y := by
    haveI : IsImmersion E.j := E.imm
    apply E.j.isEmbedding.injective
    have h := congrArg (fun f : pullback p x' ⟶ PSpace R E.N => f w) E2
    simp only [Scheme.Hom.comp_apply] at h hz ⊢
    rw [h, hw1, hz, hyb]
  let Wo : (pullback p x').Opens := (gm ≫ pullback.fst E.Y.hom k') ⁻¹ᵁ O
  have hwW : w ∈ Wo := by
    show (gm ≫ pullback.fst E.Y.hom k') w ∈ O
    rw [hgmw]; exact hyO

  let A := 𝔸(Fin g; Sp R) ↘ Sp R
  let Oy := pullback (O.ι ≫ E.Y.hom) k'
  let eΩ : Oy ⟶ pullback (pullback.snd A (spMap (residue R))) k' :=
    pullback.map (O.ι ≫ E.Y.hom) k' (pullback.snd A (spMap (residue R))) k' e (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, he2]) (by simp)
  haveI : MorphismProperty.IsStableUnderComposition @Etale := MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have heΩ : Etale eΩ :=
    MorphismProperty.pullback_map (P := @Etale) (f := O.ι ≫ E.Y.hom) (g := k') (f' := pullback.snd A (spMap (residue R)))
      (g' := k') (i₁ := e) (i₂ := 𝟙 _) he inferInstance he2.symm (by simp)
  let θ : pullback (pullback.snd A (spMap (residue R))) k' ⟶ pullback (pullback.snd A M.π) x' :=
    (pullbackLeftPullbackSndIso A (spMap (residue R)) k').hom ≫ (pullback.congrHom rfl hxk.symm).hom ≫
      (pullbackLeftPullbackSndIso A M.π x').inv
  have hθ1 : θ ≫ pullback.fst (pullback.snd A M.π) x' ≫ pullback.fst A M.π =
      pullback.fst (pullback.snd A (spMap (residue R))) k' ≫ pullback.fst A (spMap (residue R)) := by
    simp only [θ, Category.assoc, pullbackLeftPullbackSndIso_inv_fst, pullback.congrHom_hom, FibEt.map_fst',
      Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
  have hθ2 : θ ≫ pullback.fst (pullback.snd A M.π) x' ≫ pullback.snd A M.π =
      pullback.snd (pullback.snd A (spMap (residue R))) k' ≫ x' := by
    simp only [θ, Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd, pullback.congrHom_hom, FibEt.map_snd'_assoc,
      Category.id_comp]
    simp
  have hθ3 : θ ≫ pullback.snd (pullback.snd A M.π) x' = pullback.snd (pullback.snd A (spMap (residue R))) k' := by
    simp only [θ, Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd, pullback.congrHom_hom, FibEt.map_snd',
      Category.comp_id]
    simp

  let ψ : Wo.toScheme ⟶ Oy :=
    pullback.lift ((gm ≫ pullback.fst E.Y.hom k') ∣_ O) (Wo.ι ≫ gm ≫ pullback.snd E.Y.hom k') (by
      rw [← Category.assoc, morphismRestrict_ι]
      simp only [Category.assoc, pullback.condition]
      rfl)
  have hψ1 : ψ ≫ pullback.fst (O.ι ≫ E.Y.hom) k' = (gm ≫ pullback.fst E.Y.hom k') ∣_ O := pullback.lift_fst _ _ _
  have hψ2 : ψ ≫ pullback.snd (O.ι ≫ E.Y.hom) k' = Wo.ι ≫ gm ≫ pullback.snd E.Y.hom k' := pullback.lift_snd _ _ _
  let jO : Oy ⟶ pullback E.Y.hom k' :=
    pullback.map (O.ι ≫ E.Y.hom) k' E.Y.hom k' O.ι (𝟙 _) (𝟙 _) (by simp) (by simp)
  haveI : IsOpenImmersion jO :=
    MorphismProperty.pullback_map (P := @IsOpenImmersion) (f := O.ι ≫ E.Y.hom) (g := k') (f' := E.Y.hom) (g' := k')
      (i₁ := O.ι) (i₂ := 𝟙 _) inferInstance inferInstance rfl (by simp)
  haveI : IsOpenImmersion mG :=
    MorphismProperty.pullback_map (P := @IsOpenImmersion) (f := p) (g := x') (f' := G'.hom) (g' := x')
      (i₁ := iV) (i₂ := 𝟙 _) (by dsimp only [iV]; infer_instance) inferInstance rfl (by simp)
  haveI : IsIso eG.hom.left := by
    show IsIso ((Over.forget _).map eG.hom); infer_instance
  have hψj : ψ ≫ jO = Wo.ι ≫ gm := by
    apply pullback.hom_ext
    · dsimp only [jO]
      rw [Category.assoc, FibEt.map_fst', reassoc_of% hψ1, morphismRestrict_ι]
      simp only [Category.assoc]
      rfl
    · dsimp only [jO]
      rw [Category.assoc, FibEt.map_snd', Category.comp_id, hψ2]
      simp only [Category.assoc]
  haveI : IsOpenImmersion (ψ ≫ jO) := by rw [hψj]; dsimp only [gm]; infer_instance
  haveI : IsOpenImmersion ψ := IsOpenImmersion.of_comp ψ jO
  have hEq : Wo.ι ≫ pullback.map p x' (pullback.snd A M.π) x' c (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hh]) (by simp) = ψ ≫ eΩ ≫ θ := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · have hcond : (Wo.ι ≫ pullback.fst p x' ≫ (a ∣_ (b ⁻¹ᵁ W0)) ≫ (b ∣_ W0)) ≫ W0.ι =
            ((gm ≫ pullback.fst E.Y.hom k') ∣_ O) ≫ O.ι ≫ E.j := by
          simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc]
          rw [E2]
        simp only [Category.assoc]
        rw [hθ1, FibEt.map_fst'_assoc, hc1]
        dsimp only [eΩ]
        rw [FibEt.map_fst'_assoc, reassoc_of% hψ1, he3 _ _ _ hcond]
        simp only [Category.assoc]
      · simp only [Category.assoc]
        rw [hθ2, FibEt.map_fst'_assoc, hh]
        dsimp only [eΩ]
        rw [FibEt.map_snd'_assoc, Category.id_comp, reassoc_of% hψ2]
        rw [reassoc_of% hgms, pullback.condition]
    · simp only [Category.assoc]
      rw [hθ3, FibEt.map_snd', Category.comp_id]
      dsimp only [eΩ]
      rw [FibEt.map_snd', Category.comp_id, hψ2, hgms]
  have hEt : Etale (Wo.ι ≫ pullback.map p x' (pullback.snd A M.π) x' c (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hh]) (by simp)) := by
    rw [hEq]; infer_instance
  obtain ⟨U, hU, hUe⟩ := GlobalTheory.Mum.etale_near_of_etale_fibre M.S Vs.toScheme _ p (pullback.snd A M.π) c hh hp inferInstance Ω' x' Wo w hwW hEt
  exact ⟨U, hw1 ▸ hU, hUe⟩
