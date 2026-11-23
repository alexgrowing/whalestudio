import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Thick

section Sheaf

variable {Y Z : Scheme.{0}} (π : Y ⟶ Z) {n : ℕ}

theorem app_res {U V : Z.Opens} (h : U ≤ V) (a : Γ(Z, V)) :
    (Y.presheaf.map (homOfLE (π.preimage_mono h)).op).hom ((π.app V).hom a) =
      (π.app U).hom ((Z.presheaf.map (homOfLE h).op).hom a) :=
  (congrArg (fun q => q.hom a) (π.naturality (homOfLE h).op)).symm

theorem res_res {U V W : Z.Opens} (h : U ≤ V) (h' : V ≤ W) (a : Γ(Z, W)) :
    (Z.presheaf.map (homOfLE h).op).hom ((Z.presheaf.map (homOfLE h').op).hom a) =
      (Z.presheaf.map (homOfLE (h.trans h')).op).hom a := by
  have := Z.presheaf.map_comp (homOfLE h').op (homOfLE h).op
  exact (congrArg (fun q => q.hom a) this).symm

theorem le_iSup_aff (U : Z.Opens) : U ≤ ⨆ V : {V : Z.Opens // IsAffineOpen V ∧ V ≤ U}, V.1 := by
  intro x hx
  obtain ⟨V, hV, hxV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens hx
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV, hVU⟩, hxV⟩

theorem ext_aff {U : Z.Opens} (s t : Γ(Z, U))
    (h : ∀ V : Z.Opens, IsAffineOpen V → ∀ hV : V ≤ U,
      (Z.presheaf.map (homOfLE hV).op).hom s = (Z.presheaf.map (homOfLE hV).op).hom t) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq' Z.sheaf (fun V : {V : Z.Opens // IsAffineOpen V ∧ V ≤ U} => V.1) U
    (fun V => homOfLE V.2.2) (le_iSup_aff U) s t (fun V => h V.1 V.2.1 V.2.2)

theorem sections_of_affine (e : ∀ U : Z.Opens, Fin n → Γ(Y, π ⁻¹ᵁ U))
    (he : ∀ (U V : Z.Opens) (h : U ≤ V) (i : Fin n),
      (Y.presheaf.map (homOfLE (π.preimage_mono h)).op).hom (e V i) = e U i)
    (haff : ∀ U : Z.Opens, IsAffineOpen U → ∀ f : Γ(Y, π ⁻¹ᵁ U),
      ∃! c : Fin n → Γ(Z, U), f = ∑ i, (π.app U).hom (c i) * e U i)
    (W : Z.Opens) (f : Γ(Y, π ⁻¹ᵁ W)) :
    ∃! c : Fin n → Γ(Z, W), f = ∑ i, (π.app W).hom (c i) * e W i := by
  have res : ∀ (U V : Z.Opens) (h : U ≤ V) (g : Γ(Y, π ⁻¹ᵁ V)) (c : Fin n → Γ(Z, V)),
      g = ∑ i, (π.app V).hom (c i) * e V i →
      (Y.presheaf.map (homOfLE (π.preimage_mono h)).op).hom g =
        ∑ i, (π.app U).hom ((Z.presheaf.map (homOfLE h).op).hom (c i)) * e U i := by
    intro U V h g c hg
    rw [hg, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, app_res π h, he U V h]
  have uniq : ∀ (V : Z.Opens) (g : Γ(Y, π ⁻¹ᵁ V)) (c c' : Fin n → Γ(Z, V)),
      g = ∑ i, (π.app V).hom (c i) * e V i → g = ∑ i, (π.app V).hom (c' i) * e V i → c = c' := by
    intro V g c c' h h'
    funext i
    refine ext_aff _ _ fun U hU hUV => ?_
    exact congrFun ((haff U hU _).unique (res U V hUV g c h) (res U V hUV g c' h')) i
  let Ix := {V : Z.Opens // IsAffineOpen V ∧ V ≤ W}
  have ex : ∀ a : Ix, ∃ c : Fin n → Γ(Z, a.1),
      (Y.presheaf.map (homOfLE (π.preimage_mono a.2.2)).op).hom f =
        ∑ i, (π.app a.1).hom (c i) * e a.1 i := fun a => (haff a.1 a.2.1 _).exists
  choose cf hcf using ex
  have compat : ∀ (a b : Ix) (j : Fin n) (U : Z.Opens), IsAffineOpen U → ∀ (ha : U ≤ a.1) (hb : U ≤ b.1),
      (Z.presheaf.map (homOfLE ha).op).hom (cf a j) = (Z.presheaf.map (homOfLE hb).op).hom (cf b j) := by
    intro a b j U hU ha hb
    have h1 := res U a.1 ha _ _ (hcf a)
    have h2 := res U b.1 hb _ _ (hcf b)
    rw [res_res] at h1 h2
    exact congrFun ((haff U hU _).unique h1 h2) j
  have glue : ∀ j : Fin n, ∃ s : Γ(Z, W), ∀ a : Ix, (Z.presheaf.map (homOfLE a.2.2).op).hom s = cf a j := by
    intro j
    obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' Z.sheaf (fun a : Ix => a.1) W (fun a => homOfLE a.2.2)
      (le_iSup_aff W) (fun a => cf a j) (by
        intro a b
        refine ext_aff _ _ fun U hU hUV => ?_
        have ha : U ≤ a.1 := hUV.trans inf_le_left
        have hb : U ≤ b.1 := hUV.trans inf_le_right
        refine (res_res hUV inf_le_left _).trans (Eq.trans ?_ (res_res hUV inf_le_right _).symm)
        exact compat a b j U hU ha hb)
    exact ⟨s, hs⟩
  choose s hs using glue
  refine ⟨s, ?_, fun c hc => ?_⟩
  · refine TopCat.Sheaf.eq_of_locally_eq' Y.sheaf (fun a : Ix => π ⁻¹ᵁ a.1) (π ⁻¹ᵁ W)
      (fun a => homOfLE (π.preimage_mono a.2.2)) ?_ _ _ fun a => ?_
    · intro y hy
      obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (le_iSup_aff W hy)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, ha⟩
    · refine (hcf a).trans (Eq.trans ?_ (res a.1 W a.2.2 _ s rfl).symm)
      exact Finset.sum_congr rfl fun i _ => by rw [hs i a]
  · exact uniq W f c s hc (by
      refine TopCat.Sheaf.eq_of_locally_eq' Y.sheaf (fun a : Ix => π ⁻¹ᵁ a.1) (π ⁻¹ᵁ W)
        (fun a => homOfLE (π.preimage_mono a.2.2)) ?_ _ _ fun a => ?_
      · intro y hy
        obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (le_iSup_aff W hy)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, ha⟩
      · refine (hcf a).trans (Eq.trans ?_ (res a.1 W a.2.2 _ s rfl).symm)
        exact Finset.sum_congr rfl fun i _ => by rw [hs i a])

end Sheaf

section Basis

open Polynomial in
theorem jet_basis (k : Type) [Field k] (m : ℕ) :
    ∃ b : Module.Basis (Fin (m + 1)) k (Jet k Unit m),
      ∀ i : Fin (m + 1), b i = (Ideal.Quotient.mk (orig k Unit ^ (m + 1)) (MvPolynomial.X ())) ^ (i : ℕ) := by
  let φ : MvPolynomial Unit k ≃ₐ[k] k[X] := MvPolynomial.pUnitAlgEquiv k
  have hX : φ (MvPolynomial.X ()) = X := by simp [φ]
  have hI : Ideal.span {(X : k[X]) ^ (m + 1)} = (orig k Unit ^ (m + 1)).map (φ : MvPolynomial Unit k →+* k[X]) := by
    rw [Ideal.map_pow, orig, Ideal.map_span, ← Ideal.span_singleton_pow]
    congr 2
    ext p
    simp [hX]
    exact eq_comm
  let E : Jet k Unit m ≃ₐ[k] AdjoinRoot ((X : k[X]) ^ (m + 1)) := Ideal.quotientEquivAlg _ _ φ hI
  let pb := AdjoinRoot.powerBasis' (monic_X_pow (R := k) (m + 1))
  have hd : pb.dim = m + 1 := by simp [pb]
  refine ⟨(pb.basis.map E.symm.toLinearEquiv).reindex (finCongr hd), fun i => ?_⟩
  have hE : E (Ideal.Quotient.mk _ (MvPolynomial.X ())) = AdjoinRoot.root _ := by
    have h : E (Ideal.Quotient.mk _ (MvPolynomial.X ())) = Ideal.Quotient.mk _ (φ (MvPolynomial.X ())) := rfl
    rw [h, hX]
    rfl
  simp [pb]
  rw [← hE, AlgEquiv.symm_apply_apply]

end Basis

section Affine

variable {k A J : Type} [CommRing k] [CommRing A] [CommRing J] [Algebra k A] [Algebra k J]
  {I : Type} [Fintype I] (b : Module.Basis I k J)

open TensorProduct in
theorem spec_case {Y : Scheme.{0}} (p : Y ⟶ Sp A) (q : Y ⟶ Sp J)
    (sq : IsPullback p q (spMap (algebraMap k A)) (spMap (algebraMap k J))) (f : Γ(Y, ⊤)) :
    ∃! c : I → A, f = ∑ i, p.appTop.hom (toΓ A (c i)) * q.appTop.hom (toΓ J (b i)) := by
  classical
  let e : Y ≅ Sp (A ⊗[k] J) := sq.isoPullback ≪≫ pullbackSpecIso k A J
  have ep : e.hom ≫ spMap (Algebra.TensorProduct.includeLeftRingHom) = p := by
    simp [e]
  have eq' : e.hom ≫ spMap ((Algebra.TensorProduct.includeRight : J →ₐ[k] A ⊗[k] J) : J →+* A ⊗[k] J) = q := by
    simp [e]
  let Φ : A ⊗[k] J →+* Γ(Y, ⊤) := e.hom.appTop.hom.comp (toΓ _)
  haveI : IsIso e.hom.appTop := inferInstanceAs (IsIso (e.hom.app ⊤))
  have hΦ : Function.Bijective Φ :=
    (ConcreteCategory.bijective_of_isIso e.hom.appTop).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (A ⊗[k] J))).inv)
  have hl : ∀ a, p.appTop.hom (toΓ A a) = Φ (a ⊗ₜ 1) := by
    intro a
    rw [← ep, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, spMap_toΓ]
    rfl
  have hr : ∀ j, q.appTop.hom (toΓ J j) = Φ (1 ⊗ₜ j) := by
    intro a
    rw [← eq', Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, spMap_toΓ]
    rfl
  let B := Algebra.TensorProduct.basis A b
  have key : ∀ c : I → A, ∑ i, p.appTop.hom (toΓ A (c i)) * q.appTop.hom (toΓ J (b i)) = Φ (∑ i, c i • B i) := by
    intro c
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hl, hr, ← map_mul, Algebra.TensorProduct.basis_apply]
    simp [B, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
  obtain ⟨w, rfl⟩ := hΦ.2 f
  refine ⟨fun i => B.repr w i, ?_, fun c hc => ?_⟩
  · show Φ w = ∑ i, p.appTop.hom (toΓ A (B.repr w i)) * q.appTop.hom (toΓ J (b i))
    rw [key, B.sum_repr]
  · have hc' : Φ w = _ := hc
    rw [key] at hc'
    have h := hΦ.1 hc'
    funext i
    rw [h]
    exact (congrFun (B.repr_sum_self c) i).symm

end Affine

section AffineBase

variable {k J : Type} [CommRing k] [CommRing J] [Algebra k J]
  {I : Type} [Fintype I] (b : Module.Basis I k J)

theorem affine_case {U Y : Scheme.{0}} [IsAffine U] (p : Y ⟶ U) (q : Y ⟶ Sp J) (u : U ⟶ Sp k)
    (sq : IsPullback p q u (spMap (algebraMap k J))) (f : Γ(Y, ⊤)) :
    ∃! c : I → Γ(U, ⊤), f = ∑ i, p.appTop.hom (c i) * q.appTop.hom (toΓ J (b i)) := by
  let A : Type := Γ(U, ⊤)
  let g : k →+* A := (Spec.preimage (U.isoSpec.inv ≫ u)).hom
  letI : Algebra k A := g.toAlgebra
  have hg : spMap (algebraMap k A) = U.isoSpec.inv ≫ u := Spec.map_preimage _
  have sq' : IsPullback (p ≫ U.isoSpec.hom) q (spMap (algebraMap k A)) (spMap (algebraMap k J)) := by
    rw [hg]
    exact IsPullback.of_iso sq (Iso.refl _) U.isoSpec (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  let ψ : A →+* Γ(U, ⊤) := U.isoSpec.hom.appTop.hom.comp (toΓ A)
  haveI : IsIso U.isoSpec.hom.appTop := inferInstanceAs (IsIso (U.isoSpec.hom.app ⊤))
  have hψ : Function.Bijective ψ :=
    (ConcreteCategory.bijective_of_isIso U.isoSpec.hom.appTop).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv)
  have hp : ∀ a : A, (p ≫ U.isoSpec.hom).appTop.hom (toΓ A a) = p.appTop.hom (ψ a) := by
    intro a
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    rfl
  obtain ⟨c, hc, hu⟩ := spec_case b _ q sq' f
  refine ⟨fun i => ψ (c i), ?_, fun c' hc' => ?_⟩
  · refine Eq.trans hc (Finset.sum_congr rfl fun i _ => ?_)
    rw [hp]
  · choose d hd using fun i => hψ.2 (c' i)
    have : d = c := hu d (by
      refine Eq.trans hc' (Finset.sum_congr rfl fun i _ => ?_)
      rw [hp, hd])
    funext i
    rw [← hd i, this]

end AffineBase

section Restrict

theorem top_res {Y : Scheme.{0}} (V : Y.Opens) (s : Γ(Y, ⊤)) :
    V.topIso.hom.hom (V.ι.appTop.hom s) = (Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom s := by
  have h : V.ι.appTop ≫ V.topIso.hom = Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op :=
    (Y.presheaf.map_comp (homOfLE (x := V.ι ''ᵁ ⊤) le_top).op (eqToHom V.ι_image_top.symm).op).symm.trans
      (congrArg _ (Subsingleton.elim _ _))
  exact congrArg (fun q => q.hom s) h

theorem restrict_appTop {Y Z : Scheme.{0}} (f : Y ⟶ Z) (U : Z.Opens) (a : Γ(U.toScheme, ⊤)) :
    (f ⁻¹ᵁ U).topIso.hom.hom ((f ∣_ U).appTop.hom a) = (f.app U).hom (U.topIso.hom.hom a) := by
  have h0 : (f.app (U.ι ''ᵁ ⊤) ≫ Y.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op) ≫
      Y.presheaf.map (eqToHom (f ⁻¹ᵁ U).ι_image_top.symm).op =
      Z.presheaf.map (eqToHom U.ι_image_top.symm).op ≫ f.app U := by
    rw [f.naturality (eqToHom U.ι_image_top.symm).op, Category.assoc]
    exact congrArg (f.app _ ≫ ·) ((Y.presheaf.map_comp (eqToHom (image_morphismRestrict_preimage f U ⊤)).op
      (eqToHom (f ⁻¹ᵁ U).ι_image_top.symm).op).symm.trans (congrArg _ (Subsingleton.elim _ _)))
  have h : (f ∣_ U).appTop ≫ (f ⁻¹ᵁ U).topIso.hom = U.topIso.hom ≫ f.app U := by
    rw [morphismRestrict_appTop]
    exact h0
  exact congrArg (fun q => q.hom a) h

end Restrict

section Main

variable {X0 : Scheme.{0}} (G : Over X0) {k : Type} [Field k] (x : Sp k ⟶ X0) (m : ℕ)

theorem prZ_isPullback : IsPullback (prZ G x m) (fst (Tm x m) G).left (pullback.snd G.hom x)
    (spMap (algebraMap k (Jet k Unit m))) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst G.hom x) (v₁₃ := G.hom) (h₂₂ := x) ?_ (prZ_snd G x m)
    (IsPullback.of_hasPullback G.hom x)
  rw [prZ_fst]
  exact (IsPullback.of_hasPullback (Tm x m).hom G.hom).flip

theorem prZ_affine (U : (pullback G.hom x).Opens) (hU : IsAffineOpen U) (f : Γ(Ym G x m, prZ G x m ⁻¹ᵁ U)) :
    ∃! c : Fin (m + 1) → Γ(pullback G.hom x, U),
      f = ∑ i, ((prZ G x m).app U).hom (c i) * dltOn G x m _ ^ (i : ℕ) := by
  obtain ⟨b, hb⟩ := jet_basis k m
  haveI : IsAffine U.toScheme := hU
  have sq := (isPullback_morphismRestrict (prZ G x m) U).paste_vert (prZ_isPullback G x m)
  have letterRowOperator : ∀ y, (prZ G x m ⁻¹ᵁ U).topIso.hom.hom ((prZ G x m ⁻¹ᵁ U).topIso.inv.hom y) = y := fun y =>
    congrArg (fun q => q.hom y) (prZ G x m ⁻¹ᵁ U).topIso.inv_hom_id
  have TV2 : ∀ y, (prZ G x m ⁻¹ᵁ U).topIso.inv.hom ((prZ G x m ⁻¹ᵁ U).topIso.hom.hom y) = y := fun y =>
    congrArg (fun q => q.hom y) (prZ G x m ⁻¹ᵁ U).topIso.hom_inv_id
  have TU1 : ∀ y, U.topIso.hom.hom (U.topIso.inv.hom y) = y := fun y =>
    congrArg (fun q => q.hom y) U.topIso.inv_hom_id
  have fm : ∀ i : Fin (m + 1), (prZ G x m ⁻¹ᵁ U).topIso.hom.hom
      (((prZ G x m ⁻¹ᵁ U).ι ≫ (fst (Tm x m) G).left).appTop.hom (toΓ _ (b i))) =
        dltOn G x m _ ^ (i : ℕ) := by
    intro i
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, hb, map_pow, map_pow, map_pow, map_pow,
      top_res]
    rfl
  have key : ∀ c : Fin (m + 1) → Γ(U.toScheme, ⊤), (prZ G x m ⁻¹ᵁ U).topIso.hom.hom
      (∑ i, ((prZ G x m) ∣_ U).appTop.hom (c i) *
        ((prZ G x m ⁻¹ᵁ U).ι ≫ (fst (Tm x m) G).left).appTop.hom (toΓ _ (b i))) =
      ∑ i, ((prZ G x m).app U).hom (U.topIso.hom.hom (c i)) * dltOn G x m _ ^ (i : ℕ) := by
    intro c
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, restrict_appTop, fm]
  obtain ⟨c, hc, hu⟩ := affine_case b _ _ _ sq ((prZ G x m ⁻¹ᵁ U).topIso.inv.hom f)
  refine ⟨fun i => U.topIso.hom.hom (c i), ?_, fun c' hc' => ?_⟩
  · have := congrArg (prZ G x m ⁻¹ᵁ U).topIso.hom.hom hc
    rw [letterRowOperator, key] at this
    exact this
  · have h : (fun i => U.topIso.inv.hom (c' i)) = c := hu _ (by
      have h2 := key fun i => U.topIso.inv.hom (c' i)
      simp only [TU1] at h2
      rw [← hc'] at h2
      exact (congrArg _ h2.symm).trans (TV2 _))
    funext i
    rw [← h, TU1]

theorem sections_thick : ∀ (X0 : Scheme.{0}) (G : Over X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (m : ℕ)
    (W : (pullback G.hom x).Opens) (f : Γ(Ym G x m, prZ G x m ⁻¹ᵁ W)),
    ∃! c : Fin (m + 1) → Γ(pullback G.hom x, W),
      f = ∑ i, ((prZ G x m).app W).hom (c i) * dltOn G x m _ ^ (i : ℕ) := by
  intro X0 G k _ x m W f
  refine sections_of_affine (prZ G x m) (fun U i => dltOn G x m _ ^ (i : ℕ)) ?_
    (fun U hU f => prZ_affine G x m U hU f) W f
  intro U V h i
  rw [map_pow, dltOn, res_res]
  rfl

end Main

end GlobalTheory.CompanionTheory.Ar.Coc.Thick
