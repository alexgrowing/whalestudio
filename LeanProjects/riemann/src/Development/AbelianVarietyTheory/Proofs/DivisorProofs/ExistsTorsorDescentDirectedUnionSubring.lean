import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenFibMapCompAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsorModelFilteredColimitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtalePolynomialModelOfDirectedUnionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DirectedSystemEtaleBaseChangePolynomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreLocalizationDirectedUnionSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreLocalizationDirectedUnionKernelStatement

open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.TorsorUnionDescent

theorem exists_stage_torsor : ∀ (T : Type) [CommRing T] [IsDomain T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (𝒜 : ι → Subring T), Monotone 𝒜 → (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (q : ℕ), 0 < q →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
      [Algebra.Etale (Polynomial T) E] (Q : Ideal E) [Q.IsPrime]
      (D₁ : Type) [CommRing D₁] [Algebra (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁]
      (act₁ : Multiplicative (ZMod q) →* (D₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)] D₁)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁ q act₁ →
    ∃ (i : ι) (EA : Type) (_ : CommRing EA) (_ : Algebra (Polynomial (𝒜 i)) EA) (_ : Algebra (𝒜 i) EA)
      (_ : IsScalarTower (𝒜 i) (Polynomial (𝒜 i)) EA) (_ : Algebra.Etale (Polynomial (𝒜 i)) EA) (e : EA →+* E),
      e.comp (algebraMap (Polynomial (𝒜 i)) EA) =
        (algebraMap (Polynomial T) E).comp (Polynomial.mapRingHom (𝒜 i).subtype) ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e)) →+*
          GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)),
        β.comp (algebraMap (Localization.AtPrime (Q.comap e))
            (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e)))) =
          (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))).comp
            (Localization.localRingHom (Q.comap e) Q e rfl) ∧
      ∃ (D : Type) (_ : CommRing D) (_ : Algebra (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))) D)
        (actA : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))] D)),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))) D q actA ∧
        ∀ (C : Type) [CommRing C] (ψ : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →+* C) (σ : D →+* C),
          σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))) D) = ψ.comp β →
          ∃ σ₁ : D₁ →+* C, σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁) = ψ := by
  intro T _ _ ι _ _ _ 𝒜 hA hU q hq E _ _ _ _ _ Q _ D₁ _ _ act₁ htor
  obtain ⟨i₀, E₀, _, _, hE₀, ⟨iso₀⟩⟩ := GlobalTheory.T.exists_etale_polynomial_descent_of_directed_union T ι 𝒜 hA hU E

  let ι' := {k : ι // i₀ ≤ k}
  haveI : IsDirected ι' (· ≤ ·) := ⟨fun a b => by
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨c, a.2.trans hac⟩, hac, hbc⟩⟩
  haveI : Nonempty ι' := ⟨⟨i₀, le_rfl⟩⟩
  let 𝒜' : ι' → Subring T := fun k => 𝒜 k.1
  have hA' : Monotone 𝒜' := fun a b hab => hA hab
  have hU' : ∀ x : T, ∃ k : ι', x ∈ 𝒜' k := fun x => by
    obtain ⟨j, hj⟩ := hU x
    obtain ⟨c, hjc, hic⟩ := directed_of (· ≤ ·) j i₀
    exact ⟨⟨c, hic⟩, hA hjc hj⟩
  obtain ⟨Ek, _, _, _, _, _, e, h, he, hh, heh, hid, hcomp, hinj, hsurj⟩ :=
    GlobalTheory.T.directedSystem_etale_baseChange_polynomial T ι' 𝒜' hA' hU' ⟨i₀, le_rfl⟩ (fun k => k.2) E E₀ ⟨iso₀⟩
  have he' : ∀ k (a : 𝒜' k), e k (algebraMap (𝒜' k) (Ek k) a) = algebraMap T E a := by
    intro k a
    have := congrArg (fun φ => φ (Polynomial.C a)) (he k)
    simpa [IsScalarTower.algebraMap_apply (𝒜' k) (Polynomial (𝒜' k)) (Ek k),
      IsScalarTower.algebraMap_apply T (Polynomial T) E] using this
  have hnz : ∀ (S S' : Subring T) (φ : S →+* S'), (∀ a, (φ a : T) = a) →
      ∀ a ∈ nonZeroDivisors S, φ a ∈ nonZeroDivisors S' := by
    intro S S' φ hφ a ha
    refine mem_nonZeroDivisors_of_ne_zero (fun h0 => nonZeroDivisors.ne_zero ha (Subtype.ext ?_))
    have := congrArg Subtype.val h0
    rw [hφ] at this
    exact this
  have hnzT : ∀ (S : Subring T), ∀ a ∈ nonZeroDivisors S, S.subtype a ∈ nonZeroDivisors T := by
    intro S a ha
    exact mem_nonZeroDivisors_of_ne_zero (fun h0 => nonZeroDivisors.ne_zero ha (Subtype.ext h0))
  let g : ∀ k : ι', GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k))) →+*
      GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) := fun k =>
    GlobalTheory.GenFibMap.genFibMap (𝒜' k).subtype (e k) (he' k) (hnzT _) (Q.comap (e k)) Q rfl
  have hQ : ∀ k l (hkl : k ≤ l), Q.comap (e k) = (Q.comap (e l)).comap (h k l hkl) := by
    intro k l hkl
    rw [Ideal.comap_comap]
    congr 1
    ext y
    exact (heh k l hkl y).symm
  let f : ∀ k l : ι', k ≤ l → GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k))) →+*
      GlobalTheory.LocAcyc.GenFib (𝒜' l) (Localization.AtPrime (Q.comap (e l))) := fun k l hkl =>
    GlobalTheory.GenFibMap.genFibMap (Subring.inclusion (hA' hkl)) (h k l hkl) (hh k l hkl)
      (hnz _ _ _ (fun _ => rfl)) (Q.comap (e k)) (Q.comap (e l)) (hQ k l hkl)
  have hgc : ∀ k (y : Ek k), g k (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))
          (algebraMap E (Localization.AtPrime Q) (e k y)) := fun k y =>
    GlobalTheory.GenFibMap.genFibMap_apply _ _ _ _ _ _ _ y
  have hfc : ∀ k l (hkl : k ≤ l) (y : Ek k), f k l hkl (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime (Q.comap (e l)))
          (GlobalTheory.LocAcyc.GenFib (𝒜' l) (Localization.AtPrime (Q.comap (e l))))
          (algebraMap (Ek l) (Localization.AtPrime (Q.comap (e l))) (h k l hkl y)) := fun k l hkl y =>
    GlobalTheory.GenFibMap.genFibMap_apply _ _ _ _ _ _ _ y
  obtain ⟨k, Di, _, _, acti, htori, ⟨iso₂⟩⟩ := GlobalTheory.T.exists_torsor_model_filtered_colimit ι'
    (fun k => GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k)))) f
    (fun k hkk => GlobalTheory.GenFibMap.genFibMap_id _ _ _ _ _ _ (hid k hkk))
    (fun k l m hkl hlm => GlobalTheory.GenFibMap.genFibMap_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (hcomp k l m hkl hlm (hkl.trans hlm)))
    (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) g
    (fun k l hkl => GlobalTheory.GenFibMap.genFibMap_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (fun y => (heh k l hkl y).symm))
    (GlobalTheory.T.genericFibreLocalization_directedUnion_surjective T ι' 𝒜' hA' hU' E Q Ek e h he' heh hsurj g hgc)
    (GlobalTheory.T.genericFibreLocalization_directedUnion_kernel T ι' 𝒜' hA' hU' E Q Ek e h he' hh heh hinj hsurj g hgc f hfc)
    q hq D₁ act₁ htor
  refine ⟨k.1, Ek k, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, e k, he k,
    g k, GlobalTheory.GenFibMap.genFibMap_comp_algebraMap _ _ _ _ _ _ _, Di, inferInstance, inferInstance, acti, htori, ?_⟩
  intro C _ ψ σ hσ
  letI : Algebra (GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k))))
      (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) := (g k).toAlgebra
  letI : Algebra (GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k)))) C :=
    (ψ.comp (g k)).toAlgebra
  let ψa : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →ₐ[GlobalTheory.LocAcyc.GenFib (𝒜' k)
      (Localization.AtPrime (Q.comap (e k)))] C := { ψ with commutes' := fun r => rfl }
  let σa : Di →ₐ[GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k)))] C :=
    { σ with commutes' := fun r => (congrArg (fun φ => φ r) hσ : _) }
  refine ⟨(Algebra.TensorProduct.lift ψa σa (fun _ _ => Commute.all _ _)).toRingHom.comp
    iso₂.symm.toAlgHom.toRingHom, ?_⟩
  ext b
  simp [ψa]

end GlobalTheory.TorsorUnionDescent
