import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Principalise

theorem memIdealOfLocally {W : Scheme.{0}} (I : W.IdealSheafData) (A : W.affineOpens) (b : Γ(W, A.1))
    (h : ∀ y ∈ A.1, ∃ (B : W.affineOpens) (e : B.1 ≤ A.1), y ∈ B.1 ∧ resG W e b ∈ I.ideal B) :
    b ∈ I.ideal A := by
  have hk : ∀ B : W.affineOpens, I.ideal B = RingHom.ker (I.subschemeι.app B.1).hom := fun B => by
    rw [← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]
  rw [hk, RingHom.mem_ker]
  refine GlobalTheory.Cartier.ext_germ fun z hz => ?_
  obtain ⟨B, e, hzB, this⟩ := h _ hz
  rw [hk, RingHom.mem_ker, GlobalTheory.Cartier.app_resG] at this
  rw [← GlobalTheory.Cartier.germ_resG (I.subschemeι.preimage_mono e) z hzB, this, map_zero, map_zero]

theorem comapIdealTopLe {X W : Scheme.{0}} [IsAffine W] (J : X.IdealSheafData) (g : W ⟶ X)
    (U : X.affineOpens) (h : ⊤ ≤ g ⁻¹ᵁ U.1) :
    (J.comap g).ideal ⟨⊤, isAffineOpen_top W⟩ ≤ Ideal.map (g.appLE U.1 ⊤ h).hom (J.ideal U) := by
  have key : J.comap g ≤ Scheme.IdealSheafData.ofIdealTop (Ideal.map (g.appLE U.1 ⊤ h).hom (J.ideal U)) := by
    refine (GlobalTheory.Cartier.comap_le_iff _ _ _).2 fun U' a ha B hB => memIdealOfLocally _ _ _ fun y hy => ?_
    obtain ⟨t, htle, hyt⟩ := U.2.exists_basicOpen_le (V := U'.1 ⊓ U.1) ⟨g y, hB hy, h trivial⟩ (h trivial)
    obtain ⟨_, ⟨B', hB'a, rfl⟩, hyB', hB'le⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ B.1 ⊓ g ⁻¹ᵁ X.basicOpen t from ⟨hy, hyt⟩) (B.1 ⊓ g ⁻¹ᵁ X.basicOpen t).isOpen
    refine ⟨⟨B', hB'a⟩, fun x hx => (hB'le hx).1, hyB', ?_⟩
    have hDU' : X.basicOpen t ≤ U'.1 := htle.trans inf_le_left
    have h1 : resG X hDU' a ∈ J.ideal (X.affineBasicOpen t) :=
      J.ideal_le_comap_ideal (U := X.affineBasicOpen t) (V := U') hDU' ha
    rw [← J.map_ideal_basicOpen U t] at h1
    have hB'D : B' ≤ g ⁻¹ᵁ X.basicOpen t := fun x hx => (hB'le hx).2
    have e : resG W (fun x hx => (hB'le hx).1 : B' ≤ B.1) (resG W hB ((g.app U'.1).hom a)) =
        (g.appLE (X.basicOpen t) B' hB'D).hom (resG X hDU' a) := by
      show _ = resG W hB'D ((g.app (X.basicOpen t)).hom (resG X hDU' a))
      rw [GlobalTheory.Cartier.app_resG, GlobalTheory.Cartier.resG_resG, GlobalTheory.Cartier.resG_resG]
    rw [e, Scheme.IdealSheafData.ofIdealTop_ideal]
    have h2 := Ideal.mem_map_of_mem (g.appLE (X.basicOpen t) B' hB'D).hom h1
    rw [Ideal.map_map, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE] at h2
    rw [Ideal.map_map, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
    exact h2
  have := key ⟨⊤, isAffineOpen_top W⟩
  rw [Scheme.IdealSheafData.ofIdealTop_ideal] at this
  refine this.trans (le_of_eq ?_)
  convert Ideal.map_id _
  rw [show homOfLE (le_top : (⊤ : W.Opens) ≤ ⊤) = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

theorem comapIdealAffine : ∀ {X W : Scheme.{0}} (J : X.IdealSheafData) (g : W ⟶ X) (U : X.affineOpens) (A : W.affineOpens) (h : A.1 ≤ g ⁻¹ᵁ U.1), (J.comap g).ideal A = Ideal.map (g.appLE U.1 A.1 h).hom (J.ideal U) := by
  intro X W J g U A h
  apply le_antisymm
  · intro x hx
    have : IsAffine A.1.toScheme := A.2
    have hA : ⊤ ≤ A.1.ι ⁻¹ᵁ A.1 := A.1.ι_preimage_self.ge
    have h1 := (GlobalTheory.Cartier.comap_le_iff (J.comap g) A.1.ι _).1 le_rfl A x hx ⟨⊤, isAffineOpen_top _⟩ hA
    rw [← Scheme.IdealSheafData.comap_comp] at h1
    have h2 := comapIdealTopLe J (A.1.ι ≫ g) U (hA.trans (A.1.ι.preimage_mono h)) h1
    have hb : Function.Bijective (A.1.ι.appLE A.1 ⊤ hA).hom := ConcreteCategory.bijective_of_isIso _
    rw [← Ideal.comap_map_of_bijective _ hb (I := Ideal.map (g.appLE U.1 A.1 h).hom (J.ideal U)),
      Ideal.mem_comap, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
    exact h2
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact (GlobalTheory.Cartier.comap_le_iff J g _).1 le_rfl U a ha A h

theorem kerIdealAffine : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (U : X.Opens) (hU : IsAffineOpen U) (I : Ideal Γ(X, U)), ∃ J : X.IdealSheafData, J.ideal ⟨U, hU⟩ = I ∧ ∀ N : ℕ, (N : Γ(X, U)) ∈ I → ∀ V : X.affineOpens, (N : Γ(X, V.1)) ∈ J.ideal V := by
  intro X _ U hU I
  have hR : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let q : Γ(X, U) →+* Γ(X, U) ⧸ I := Ideal.Quotient.mk I
  let f : Spec (CommRingCat.of (Γ(X, U) ⧸ I)) ⟶ X := Spec.map (CommRingCat.ofHom q) ≫ hU.fromSpec
  haveI : QuasiCompact f := quasiCompact_of_noetherianSpace_source f
  have hz : ⊤ ≤ f ⁻¹ᵁ U := fun _ _ => hU.range_fromSpec.subset ⟨_, rfl⟩
  have hfs : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have hzapp : f.appLE U ⊤ hz = hU.fromSpec.appLE U ⊤ hfs ≫ (Spec.map (CommRingCat.ofHom q)).appTop := by
    rw [Scheme.Hom.comp_appLE]
    rfl
  have m2 : f.appLE U ⊤ hz = (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec.map (CommRingCat.ofHom q)).appTop := by
    rw [hzapp]
    congr 1
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    convert Category.comp_id _
    exact (Spec Γ(X, U)).presheaf.map_id _
  have m3 : (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec.map (CommRingCat.ofHom q)).appTop =
      CommRingCat.ofHom q ≫ (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I))).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom q)).symm
  have k1 : ∀ b, (f.appLE U ⊤ hz).hom b = (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I))).inv.hom (q b) := by
    intro b
    rw [m2, m3]
    rfl
  refine ⟨f.ker, ?_, ?_⟩
  · ext a
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
    constructor
    · intro ha
      have h1 : (f.appLE U ⊤ hz).hom a = 0 := by
        show resG _ hz ((f.app U).hom a) = 0
        rw [ha, map_zero]
      rw [k1] at h1
      have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I))).hom.hom h1
      rw [Iso.inv_hom_id_apply, map_zero] at h2
      exact Ideal.Quotient.eq_zero_iff_mem.1 h2
    · intro ha
      have h1 : (f.appLE U ⊤ hz).hom a = 0 := by
        rw [k1, show q a = 0 from Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
      refine GlobalTheory.Cartier.ext_germ fun x hx => ?_
      rw [map_zero, ← GlobalTheory.Cartier.germ_resG hz x trivial]
      exact (congrArg _ h1).trans (map_zero _)
  · intro N hN V
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker, map_natCast]
    have h0 : (N : Γ(X, U) ⧸ I) = 0 := by
      rw [← map_natCast q, Ideal.Quotient.eq_zero_iff_mem]; exact hN
    have h1 : (N : Γ(Spec (CommRingCat.of (Γ(X, U) ⧸ I)), ⊤)) = 0 := by
      rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I))).inv.hom, h0, map_zero]
    rw [← map_natCast (resG _ (le_top : f ⁻¹ᵁ V.1 ≤ ⊤)), h1, map_zero]

theorem exists_dvd_of_span_mul_eq {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] {m : ℕ}
    (A : Fin m → R) (I' : Ideal R) {f : R} (h : Ideal.span (Set.range A) * I' = Ideal.span {f})
    (hf : f ∈ nonZeroDivisors R) : ∃ k, ∃ s ∉ P, ∀ k', A k ∣ s * A k' := by
  have hfm : f ∈ Ideal.span (Set.range A) * I' := h ▸ Ideal.mem_span_singleton_self f
  have key : ∀ x ∈ Ideal.span (Set.range A) * I', ∃ c : Fin m → R, (∀ k, c k ∈ I') ∧ x = ∑ k, A k * c k := by
    intro x hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun x y ⟨c, hc, hx⟩ ⟨d, hd, hy⟩ => ?_)
    · obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 ha
      refine ⟨fun k => d k * b, fun k => I'.mul_mem_left _ hb, ?_⟩
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by simp only [smul_eq_mul]; ring
    · refine ⟨c + d, fun k => I'.add_mem (hc k) (hd k), ?_⟩
      simp only [hx, hy, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  obtain ⟨c, hc, hfc⟩ := key f hfm
  have hAc : ∀ k k', ∃ t, A k' * c k = f * t := fun k k' => by
    have : A k' * c k ∈ Ideal.span {f} :=
      h ▸ Ideal.mul_mem_mul (Ideal.subset_span ⟨k', rfl⟩) (hc k)
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨t, by rw [← ht, mul_comm]⟩
  choose t ht using hAc
  have hsum : ∑ k, t k k = 1 := by
    refine (mul_cancel_left_mem_nonZeroDivisors hf).1 ?_
    rw [Finset.mul_sum, _root_.mul_one]
    conv_rhs => rw [hfc]
    exact Finset.sum_congr rfl fun k _ => (ht k k).symm
  obtain ⟨k, hk⟩ : ∃ k, t k k ∉ P := by
    by_contra hcon
    push_neg at hcon
    exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2
      (hsum ▸ Ideal.sum_mem _ fun k _ => hcon k))
  refine ⟨k, t k k, hk, fun k' => ⟨t k k', ?_⟩⟩
  refine (mul_cancel_left_mem_nonZeroDivisors hf).1 ?_
  calc f * (t k k * A k') = (f * t k k) * A k' := by ring
    _ = A k * c k * A k' := by rw [ht]
    _ = A k * (A k' * c k) := by ring
    _ = f * (A k * t k k') := by rw [ht]; ring

theorem exists_idealSheaf_principalises : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (p n : ℕ) (U : Fin n → X.Opens) (m : Fin n → ℕ) (A : ∀ j, Fin (m j) → Γ(X, U j)), (∀ j, IsAffineOpen (U j)) → (∀ j, (p : Γ(X, U j)) ∈ (Ideal.span (Set.range (A j))).radical) → ∃ J : X.IdealSheafData, (∀ x ∈ J.support, x ∉ X.basicOpen (p : Γ(X, ⊤))) ∧ ∀ (W W' : Scheme.{0}) (b : W ⟶ X) (ν : W' ⟶ W), ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap b) → ∀ (w : W') (j : Fin n), (ν ≫ b) w ∈ U j → ∃ (V : W'.Opens) (hV : V ≤ (ν ≫ b) ⁻¹ᵁ U j), w ∈ V ∧ IsAffineOpen V ∧ ∃ k, ∀ k', ((ν ≫ b).appLE (U j) V hV).hom (A j k) ∣ ((ν ≫ b).appLE (U j) V hV).hom (A j k') := by
  intro X _ p n U m A hU hp
  choose J hJU hJp using fun j => kerIdealAffine X (U j) (hU j) (Ideal.span (Set.range (A j)))
  choose N hN using fun j => hp j
  have hmem : ∀ (V : X.affineOpens) (s : Finset (Fin n)),
      ((p ^ (∑ j ∈ s, N j) : ℕ) : Γ(X, V.1)) ∈ (∏ j ∈ s, J j).ideal V := by
    intro V s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
        pow_add, Nat.cast_mul]
      refine Ideal.mul_mem_mul (hJp j _ ?_ V) ih
      rw [Nat.cast_pow]
      exact hN j
  refine ⟨∏ j, J j, fun x hx hxp => ?_, ?_⟩
  · obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have h1 := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hxV).1 hx
    rw [Scheme.mem_zeroLocus_iff] at h1
    refine h1 _ (hmem ⟨V, hV⟩ Finset.univ) ?_
    have e : ((p ^ (∑ j, N j) : ℕ) : Γ(X, V)) =
        (X.presheaf.map (homOfLE le_top).op).hom ((p : Γ(X, ⊤)) ^ (∑ j, N j)) := by
      simp
    rw [e, Scheme.basicOpen_res]
    refine ⟨hxV, ?_⟩
    have htop : x ∈ (⊤ : X.Opens) := trivial
    show x ∈ X.basicOpen _
    rw [Scheme.mem_basicOpen _ _ _ htop, map_pow]
    exact ((Scheme.mem_basicOpen _ _ _ htop).1 hxp).pow _
  · intro W W' b ν hE w j hw
    have hw0 : b (ν w) ∈ U j := hw
    obtain ⟨V₁, f, hw₁, hf, hV₁⟩ := hE (ν w)
    obtain ⟨g, hgle, hwg⟩ := V₁.2.exists_basicOpen_le (V := V₁.1 ⊓ b ⁻¹ᵁ U j) ⟨ν w, hw₁, hw0⟩ hw₁
    have hDU : (W.affineBasicOpen g).1 ≤ b ⁻¹ᵁ U j := hgle.trans inf_le_right
    have hDV : (W.affineBasicOpen g).1 ≤ V₁.1 := W.basicOpen_le g
    have hfD : (W.presheaf.map (homOfLE hDV).op).hom f ∈ nonZeroDivisors Γ(W, (W.affineBasicOpen g).1) :=
      (GlobalTheory.Cartier.isRegularFn_iff_of_isAffineOpen (W.affineBasicOpen g).2).1
        (((GlobalTheory.Cartier.isRegularFn_iff_of_isAffineOpen V₁.2).2 hf).resG hDV)
    have hI1 := ((∏ i, J i).comap b).map_ideal_basicOpen V₁ g
    rw [hV₁, Ideal.map_span, Set.image_singleton] at hI1
    have hI2 := comapIdealAffine (∏ i, J i) b ⟨U j, hU j⟩ (W.affineBasicOpen g) hDU
    rw [← Finset.mul_prod_erase Finset.univ J (Finset.mem_univ j), Scheme.IdealSheafData.ideal_mul,
      Pi.mul_apply, Ideal.map_mul, hJU, Ideal.map_span, ← Set.range_comp] at hI2
    rw [← Finset.mul_prod_erase Finset.univ J (Finset.mem_univ j)] at hI1
    have hwD : ν w ∈ (W.affineBasicOpen g).1 := hwg
    obtain ⟨k, s, hsP, hdiv⟩ := exists_dvd_of_span_mul_eq
      (Ideal.comap (W.presheaf.germ (W.affineBasicOpen g).1 (ν w) hwD).hom (IsLocalRing.maximalIdeal _)) _ _
      (hI2.symm.trans hI1.symm) hfD
    have hsu : ν w ∈ W.basicOpen s := by
      rw [Scheme.mem_basicOpen _ _ _ hwD]
      by_contra hc
      exact hsP ((IsLocalRing.mem_maximalIdeal _).2 hc)
    have hED : W.basicOpen s ≤ (W.affineBasicOpen g).1 := W.basicOpen_le s
    obtain ⟨_, ⟨V, hVa, rfl⟩, hwV, hVE⟩ := W'.isBasis_affineOpens.exists_subset_of_mem_open
      (show w ∈ ν ⁻¹ᵁ W.basicOpen s from hsu) (ν ⁻¹ᵁ W.basicOpen s).isOpen
    have hVE' : V ≤ ν ⁻¹ᵁ W.basicOpen s := hVE
    have hV : V ≤ (ν ≫ b) ⁻¹ᵁ U j := fun x hx => hDU (hED (hVE' hx))
    refine ⟨V, hV, hwV, hVa, k, fun k' => ?_⟩
    have key : (b.appLE (U j) _ hDU ≫ W.presheaf.map (homOfLE hED).op) ≫ ν.appLE _ V hVE' =
        (ν ≫ b).appLE (U j) V hV := by
      rw [Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE]
    have hu := W.toRingedSpace.isUnit_res_basicOpen s
    have h1 := map_dvd (W.presheaf.map (homOfLE hED).op).hom (hdiv k')
    rw [map_mul] at h1
    have h2 := hu.dvd_mul_left.1 h1
    have h3 := map_dvd (ν.appLE _ V hVE').hom h2
    rw [← key]
    simpa using h3

end GlobalTheory.Principalise
