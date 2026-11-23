import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover

noncomputable section

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz.G

section alg
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

private theorem alg_core {D : ℕ} (u : Fin D → B)
    (h : (MvPolynomial.aeval u : MvPolynomial (Fin D) R →ₐ[R] B).toRingHom.Etale) :
    ∃ t : B ⊗[R] B, Algebra.TensorProduct.lmul' R t = 1 ∧
      ∀ x : B ⊗[R] B, Algebra.TensorProduct.lmul' R x = 0 →
        t * x ∈ Ideal.span (Set.range fun k => (1 : B) ⊗ₜ[R] u k - u k ⊗ₜ[R] (1 : B)) := by
  let P := MvPolynomial (Fin D) R
  letI : Algebra P B := (MvPolynomial.aeval u : P →ₐ[R] B).toRingHom.toAlgebra
  haveI : Algebra.Etale P B := h
  have hP : ∀ p : P, algebraMap P B p = MvPolynomial.aeval u p := fun _ => rfl
  let J : Ideal (B ⊗[R] B) := Ideal.span (Set.range fun k => (1 : B) ⊗ₜ[R] u k - u k ⊗ₜ[R] (1 : B))
  have hJ : ∀ k, (1 : B) ⊗ₜ[R] u k - u k ⊗ₜ[R] (1 : B) ∈ J := fun k => Ideal.subset_span ⟨k, rfl⟩
  let iL : B →+* (B ⊗[R] B) ⧸ J :=
    (Ideal.Quotient.mk J).comp (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B) (B := B)).toRingHom
  let iR : B →+* (B ⊗[R] B) ⧸ J :=
    (Ideal.Quotient.mk J).comp (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := B)).toRingHom
  have hLR : iR.comp (algebraMap P B) = iL.comp (algebraMap P B) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)
    · have e : algebraMap P B (MvPolynomial.C r) = algebraMap R B r := by simp [hP]
      simp only [RingHom.comp_apply, e]
      show Ideal.Quotient.mk J ((1 : B) ⊗ₜ[R] algebraMap R B r) = Ideal.Quotient.mk J (algebraMap R B r ⊗ₜ[R] (1 : B))
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    · have e : algebraMap P B (MvPolynomial.X k) = u k := by simp [hP]
      simp only [RingHom.comp_apply, e]
      exact Ideal.Quotient.eq.2 (hJ k)
  letI : Algebra P ((B ⊗[R] B) ⧸ J) := (iL.comp (algebraMap P B)).toAlgebra
  let aL : B →ₐ[P] (B ⊗[R] B) ⧸ J := { iL with commutes' := fun _ => rfl }
  let aR : B →ₐ[P] (B ⊗[R] B) ⧸ J :=
    { iR with commutes' := fun p => congrArg (fun f : P →+* _ => f p) hLR }
  let ρ : B ⊗[P] B →ₐ[P] (B ⊗[R] B) ⧸ J := Algebra.TensorProduct.productMap aL aR
  have hρ : ∀ x y : B, ρ (x ⊗ₜ[P] y) = Ideal.Quotient.mk J (x ⊗ₜ[R] y) := by
    intro x y
    show aL x * aR y = _
    show Ideal.Quotient.mk J _ * Ideal.Quotient.mk J _ = _
    rw [← map_mul]
    simp
  let mulQ : (B ⊗[R] B) ⧸ J →+* B := Ideal.Quotient.lift J (Algebra.TensorProduct.lmul' R (S := B)).toRingHom (by
    intro a ha
    have : J ≤ RingHom.ker (Algebra.TensorProduct.lmul' R (S := B)).toRingHom := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      simp [RingHom.mem_ker]
    exact this ha)
  have hm : ∀ y : B ⊗[P] B, mulQ (ρ y) = Algebra.TensorProduct.lmul' P y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => rw [hρ]; simp [mulQ]
    | add x y hx hy => simp only [map_add, hx, hy]
  obtain ⟨t', ht0, ht1⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := P) (S := B)).1 inferInstance
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (ρ t')
  refine ⟨t, ?_, fun x hx => ?_⟩
  · have := hm t'
    rw [← ht, ht1] at this
    simpa [mulQ] using this
  · have hxI : x ∈ KaehlerDifferential.ideal R B := hx
    rw [← KaehlerDifferential.span_range_eq_ideal] at hxI
    clear hx
    induction hxI using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
      have := congrArg ρ (ht0 s)
      rw [map_mul, map_sub, hρ, hρ, map_zero, ← ht, ← map_sub, ← map_mul, mul_comm] at this
      exact this
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact J.add_mem hx hy
    | smul a x _ hx => rw [smul_eq_mul, mul_left_comm]; exact J.mul_mem_left a hx

private theorem alg2 {T : Type} [CommRing T] [Algebra R T] (a b : B →ₐ[R] T)
    (hφ : Function.Bijective (Algebra.TensorProduct.productMap a b)) (m : T →ₐ[R] B)
    (ma : ∀ x, m (a x) = x) (mb : ∀ x, m (b x) = x) {D : ℕ} (u : Fin D → B)
    (h : (MvPolynomial.aeval u : MvPolynomial (Fin D) R →ₐ[R] B).toRingHom.Etale) :
    ∃ t : T, m t = 1 ∧ ∀ x, m x = 0 → t * x ∈ Ideal.span (Set.range fun k => b (u k) - a (u k)) := by
  obtain ⟨t, ht1, ht2⟩ := alg_core (R := R) u h
  have hm : ∀ y : B ⊗[R] B, m (Algebra.TensorProduct.productMap a b y) = Algebra.TensorProduct.lmul' R y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [ma, mb]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨Algebra.TensorProduct.productMap a b t, by rw [hm, ht1], fun x hx => ?_⟩
  obtain ⟨y, rfl⟩ := hφ.2 x
  rw [hm] at hx
  have := Ideal.mem_map_of_mem (Algebra.TensorProduct.productMap a b).toRingHom (ht2 y hx)
  rw [Ideal.map_span, ← Set.range_comp] at this
  have e : ((Algebra.TensorProduct.productMap a b).toRingHom ∘ fun k => (1 : B) ⊗ₜ[R] u k - u k ⊗ₜ[R] (1 : B)) =
      fun k => b (u k) - a (u k) := by
    funext k
    simp
  rw [e] at this
  simpa using this
end alg

section geo
variable {R : Type} [CommRing R]

private theorem secMap_comp {X Y Y' : Sch R} (f : Y ⟶ X) (g : Y' ⟶ Y) {U : X.left.Opens} {V : Y.left.Opens}
    {V' : Y'.left.Opens} (h : V ≤ f.left ⁻¹ᵁ U) (h' : V' ≤ g.left ⁻¹ᵁ V) (h'' : V' ≤ (g ≫ f).left ⁻¹ᵁ U)
    (x : Sec X U) : secMap g h' (secMap f h x) = secMap (g ≫ f) h'' x :=
  congrArg (fun φ => φ.hom x) (Scheme.Hom.appLE_comp_appLE g.left f.left U V V' h h')

private theorem secMap_self {X : Sch R} (f : X ⟶ X) (hf : f = 𝟙 X) {U : X.left.Opens}
    (h : U ≤ f.left ⁻¹ᵁ U) (x : Sec X U) : secMap f h x = x := by
  subst hf
  show (Scheme.Hom.appLE (𝟙 X.left) U U h).hom x = x
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
  exact congrArg (fun φ => φ.hom x) (X.left.presheaf.map_id (Opposite.op U))

private theorem secRes_apply (X : Sch R) {U V : X.left.Opens} (h : V ≤ U) (x : Sec X U) :
    secRes X h x = (X.left.presheaf.map (homOfLE h).op).hom x := by
  show (Scheme.Hom.appLE (𝟙 X.left) U V h).hom x = _
  simp [Scheme.Hom.appLE]
  rfl

private theorem secRes_secMap {X Y : Sch R} (f : Y ⟶ X) {U : X.left.Opens} {V V' : Y.left.Opens}
    (h : V ≤ f.left ⁻¹ᵁ U) (h' : V' ≤ V) (h'' : V' ≤ f.left ⁻¹ᵁ U) (x : Sec X U) :
    secRes Y h' (secMap f h x) = secMap f h'' x := by
  rw [secRes_apply]
  exact congrArg (fun φ => φ.hom x) (Scheme.Hom.appLE_map f.left h (homOfLE h').op)

private theorem ker_pre {X Y : Sch R} (f : Y ⟶ X) {U : X.left.Opens} {V : Y.left.Opens}
    (e : f.left ⁻¹ᵁ U = V) (h : V ≤ f.left ⁻¹ᵁ U) :
    RingHom.ker (secMap f (le_refl (f.left ⁻¹ᵁ U))).toRingHom = RingHom.ker (secMap f h).toRingHom := by
  subst e
  rfl

private theorem diagonal_comp_fst (Z : Sch R) : dg Z ≫ p1 Z = 𝟙 Z :=
  Over.OverMorphism.ext (pullback.diagonal_fst Z.hom)

private theorem diagonal_comp_snd (Z : Sch R) : dg Z ≫ p2 Z = 𝟙 Z :=
  Over.OverMorphism.ext (pullback.diagonal_snd Z.hom)

private theorem pre_dg (Z : Sch R) (U : Z.left.Opens) :
    (dg Z).left ⁻¹ᵁ ((p1 Z).left ⁻¹ᵁ U ⊓ (p2 Z).left ⁻¹ᵁ U) = U := by
  have e1 : (dg Z).left ⁻¹ᵁ ((p1 Z).left ⁻¹ᵁ U) = U := by
    have h : (dg Z).left ≫ (p1 Z).left = 𝟙 _ := congrArg (fun f => f.left) (diagonal_comp_fst Z)
    rw [← Scheme.Hom.comp_preimage, h]
    rfl
  have e2 : (dg Z).left ⁻¹ᵁ ((p2 Z).left ⁻¹ᵁ U) = U := by
    have h : (dg Z).left ≫ (p2 Z).left = 𝟙 _ := congrArg (fun f => f.left) (diagonal_comp_snd Z)
    rw [← Scheme.Hom.comp_preimage, h]
    rfl
  show (dg Z).left ⁻¹ᵁ ((p1 Z).left ⁻¹ᵁ U) ⊓ (dg Z).left ⁻¹ᵁ ((p2 Z).left ⁻¹ᵁ U) = U
  rw [e1, e2, inf_idem]

private theorem ker_res (Z : Sch R) [IsSeparated Z.hom] {N N' : (XX Z).left.Opens} (hN : IsAffineOpen N)
    (hN' : IsAffineOpen N') (h : N' ≤ N) :
    RingHom.ker (secMap (dg Z) (le_refl ((dg Z).left ⁻¹ᵁ N'))).toRingHom =
      (RingHom.ker (secMap (dg Z) (le_refl ((dg Z).left ⁻¹ᵁ N))).toRingHom).map (secRes (XX Z) h).toRingHom := by
  haveI : IsClosedImmersion (dg Z).left := inferInstanceAs (IsClosedImmersion (pullback.diagonal Z.hom))
  have e := (dg Z).left.ker.map_ideal (U := ⟨N', hN'⟩) (V := ⟨N, hN⟩) h
  rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply] at e
  have r : (secRes (XX Z) h).toRingHom = ((XX Z).left.presheaf.map (homOfLE h).op).hom :=
    RingHom.ext fun x => secRes_apply (XX Z) h x
  have k : ∀ M : (XX Z).left.Opens, (secMap (dg Z) (le_refl ((dg Z).left ⁻¹ᵁ M))).toRingHom = ((dg Z).left.app M).hom := by
    intro M
    rw [Scheme.Hom.app_eq_appLE]
    rfl
  rw [r, k, k]
  exact e.symm

private theorem factorization_through_pullback {A C T : CommRingCat.{0}} {Y X : Scheme.{0}} (j : Spec A ⟶ Y) (ψ : Spec C ⟶ X) {pr : X ⟶ Y}
    {ι : Spec T ⟶ X} {incl : A ⟶ C} {f : C ⟶ T} {g : A ⟶ T} (e : ψ ≫ pr = Spec.map incl ≫ j)
    (a : incl ≫ f = g) (s : Spec.map g ≫ j = ι ≫ pr) : (Spec.map f ≫ ψ) ≫ pr = ι ≫ pr := by
  rw [Category.assoc, e, ← Category.assoc, ← Spec.map_comp, a, s]

private theorem commGroup_inv_eq_conj_twist_identity {T C : CommRingCat.{0}} {X : Scheme.{0}} (ι : Spec T ⟶ X) (ψ : Spec C ⟶ X)
    [IsOpenImmersion ι] [IsOpenImmersion ψ] (h : Set.range ι = Set.range ψ) (f : C ⟶ T)
    (hf : Spec.map f ≫ ψ = ι) : Function.Bijective f.hom := by
  have hi : Spec.map f = (IsOpenImmersion.isoOfRangeEq ι ψ h).hom := by
    rw [← cancel_mono ψ, hf, IsOpenImmersion.isoOfRangeEq_hom_fac]
  have hi' : IsIso (Spec.map f) := hi ▸ inferInstance
  exact isIso_SpecMap_iff.1 hi'

private theorem sq_main (Z : Sch R) (U : Z.left.Opens) (hU : IsAffineOpen U) :
    IsAffineOpen ((p1 Z).left ⁻¹ᵁ U ⊓ (p2 Z).left ⁻¹ᵁ U) ∧
    Function.Bijective (Algebra.TensorProduct.productMap
      (secMap (p1 Z) (inf_le_left : (p1 Z).left ⁻¹ᵁ U ⊓ (p2 Z).left ⁻¹ᵁ U ≤ _))
      (secMap (p2 Z) (inf_le_right : (p1 Z).left ⁻¹ᵁ U ⊓ (p2 Z).left ⁻¹ᵁ U ≤ _))) := by
  let W := (p1 Z).left ⁻¹ᵁ U ⊓ (p2 Z).left ⁻¹ᵁ U
  have hW1 : W ≤ (p1 Z).left ⁻¹ᵁ U := inf_le_left
  have hW2 : W ≤ (p2 Z).left ⁻¹ᵁ U := inf_le_right
  let B := Sec Z U
  let j : Spec (CommRingCat.of B) ⟶ Z.left := hU.fromSpec
  haveI : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  have hj : Spec.map (CommRingCat.ofHom (algebraMap R B)) = j ≫ Z.hom := by
    have := IsAffineOpen.SpecMap_appLE_fromSpec Z.hom (isAffineOpen_top _) hU (le_top : U ≤ Z.hom ⁻¹ᵁ ⊤)
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at this
    exact this
  let ψ₀ := pullback.map (Spec.map (CommRingCat.ofHom (algebraMap R B))) (Spec.map (CommRingCat.ofHom (algebraMap R B)))
    Z.hom Z.hom j j (𝟙 _) (by rw [Category.comp_id, hj]) (by rw [Category.comp_id, hj])
  haveI : IsOpenImmersion ψ₀ := MorphismProperty.pullback_map (P := IsOpenImmersion) inferInstance inferInstance hj hj
  let ψ : Spec (CommRingCat.of (B ⊗[R] B)) ⟶ (XX Z).left := (pullbackSpecIso R B B).inv ≫ ψ₀
  haveI : IsOpenImmersion ψ := inferInstanceAs (IsOpenImmersion ((pullbackSpecIso R B B).inv ≫ ψ₀))
  have hr : Set.range ψ = (W : Set (XX Z).left) := by
    have h1 : Set.range ψ = Set.range ψ₀ := by
      show Set.range ((pullbackSpecIso R B B).inv ≫ ψ₀) = _
      rw [Scheme.Hom.comp_base, TopCat.coe_comp]
      exact Function.Surjective.range_comp (Scheme.Hom.surjective _) _
    rw [h1, Scheme.Pullback.range_map]
    show _ = (pullback.fst Z.hom Z.hom) ⁻¹' (U : Set Z.left) ∩ (pullback.snd Z.hom Z.hom) ⁻¹' (U : Set Z.left)
    rw [show Set.range j = (U : Set Z.left) from hU.range_fromSpec]
  have hWa : IsAffineOpen W := by
    have : ψ.opensRange = W := TopologicalSpace.Opens.ext hr
    rw [← this]
    exact isAffineOpen_opensRange ψ
  refine ⟨hWa, ?_⟩
  let a := secMap (p1 Z) hW1
  let b := secMap (p2 Z) hW2
  let φ := Algebra.TensorProduct.productMap a b
  have e1 : ψ ≫ pullback.fst Z.hom Z.hom =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫ j := by
    show ((pullbackSpecIso R B B).inv ≫ ψ₀) ≫ _ = _
    rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullbackSpecIso_inv_fst]
  have e2 : ψ ≫ pullback.snd Z.hom Z.hom =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B).toRingHom) ≫ j := by
    show ((pullbackSpecIso R B B).inv ≫ ψ₀) ≫ _ = _
    rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullbackSpecIso_inv_snd]
    rfl
  have a1 : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] B) ≫
      CommRingCat.ofHom φ.toRingHom = Scheme.Hom.appLE (pullback.fst Z.hom Z.hom) U W hW1 := by
    ext x
    show φ (x ⊗ₜ[R] 1) = a x
    simp [φ]
  have a2 : CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B).toRingHom ≫
      CommRingCat.ofHom φ.toRingHom = Scheme.Hom.appLE (pullback.snd Z.hom Z.hom) U W hW2 := by
    ext x
    show φ (1 ⊗ₜ[R] x) = b x
    simp [φ]
  have hS : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ψ = hWa.fromSpec := by
    refine pullback.hom_ext ?_ ?_
    · exact factorization_through_pullback j ψ e1 a1 (IsAffineOpen.SpecMap_appLE_fromSpec (pullback.fst Z.hom Z.hom) hU hWa hW1)
    · exact factorization_through_pullback j ψ e2 a2 (IsAffineOpen.SpecMap_appLE_fromSpec (pullback.snd Z.hom Z.hom) hU hWa hW2)
  exact commGroup_inv_eq_conj_twist_identity hWa.fromSpec ψ (by rw [hWa.range_fromSpec, hr]) _ hS

theorem dChartEx : DChartEx := by
  intro R _ Z D _
  refine ⟨fun U u hc z hz => ?_, fun c N' hN' h => ?_⟩
  · obtain ⟨hW, hφ⟩ := sq_main Z U hc.1
    have hWU := pre_dg Z U
    let W := (p1 Z).left ⁻¹ᵁ U ⊓ (p2 Z).left ⁻¹ᵁ U
    have hW1 : W ≤ (p1 Z).left ⁻¹ᵁ U := inf_le_left
    have hW2 : W ≤ (p2 Z).left ⁻¹ᵁ U := inf_le_right
    have hUW : U ≤ (dg Z).left ⁻¹ᵁ W := hWU.ge
    let a := secMap (p1 Z) hW1
    let b := secMap (p2 Z) hW2
    let m := secMap (dg Z) hUW
    have ma : ∀ x, m (a x) = x := fun x => by
      have h3 : U ≤ (dg Z ≫ p1 Z).left ⁻¹ᵁ U := fun y hy => by
        have := hW1 (hUW hy)
        exact this
      exact (secMap_comp (p1 Z) (dg Z) hW1 hUW h3 x).trans (secMap_self _ (diagonal_comp_fst Z) h3 x)
    have mb : ∀ x, m (b x) = x := fun x => by
      have h3 : U ≤ (dg Z ≫ p2 Z).left ⁻¹ᵁ U := fun y hy => by
        have := hW2 (hUW hy)
        exact this
      exact (secMap_comp (p2 Z) (dg Z) hW2 hUW h3 x).trans (secMap_self _ (diagonal_comp_snd Z) h3 x)
    obtain ⟨t, ht1, ht2⟩ := alg2 a b hφ m ma mb u hc.2
    let t' : Γ((XX Z).left, W) := t
    let N := (XX Z).left.basicOpen t'
    have hNW : N ≤ W := Scheme.basicOpen_le _ _
    have hNa : IsAffineOpen N := hW.basicOpen t'
    have hNU : (dg Z).left ⁻¹ᵁ N = U := by
      refine le_antisymm ((Scheme.Hom.preimage_mono _ hNW).trans hWU.le) ?_
      have h0 : Z.left.basicOpen (show Γ(Z.left, U) from m t) = U := by
        rw [show (show Γ(Z.left, U) from m t) = 1 from ht1]
        exact Scheme.basicOpen_of_isUnit _ isUnit_one
      have h1 : Z.left.basicOpen (show Γ(Z.left, U) from m t) =
          U ⊓ Z.left.basicOpen (((dg Z).left.app W).hom t') :=
        Scheme.basicOpen_res _ _ (homOfLE hUW).op
      rw [Scheme.preimage_basicOpen]
      rw [h0] at h1
      exact inf_eq_left.1 h1.symm
    have hNz : (dg Z).left z ∈ N := by
      have : z ∈ (dg Z).left ⁻¹ᵁ N := hNU.ge hz
      exact this
    refine ⟨⟨U, u, hc, N, hNa, hNW.trans hW1, hNW.trans hW2, ?_⟩, rfl, HEq.rfl, hNz⟩
    have hs : ∀ k, secMap (p2 Z) (hNW.trans hW2) (u k) - secMap (p1 Z) (hNW.trans hW1) (u k) =
        secRes (XX Z) hNW (b (u k) - a (u k)) := fun k => by
      rw [map_sub, secRes_secMap (p2 Z) hW2 hNW (hNW.trans hW2), secRes_secMap (p1 Z) hW1 hNW (hNW.trans hW1)]
    rw [ker_res Z hW hNa hNW, ker_pre (dg Z) hWU hUW]
    simp only [hs]
    refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun x hx => ?_) (Ideal.span_le.2 ?_)
    · have h3 := Ideal.mem_map_of_mem (secRes (XX Z) hNW).toRingHom (ht2 x hx)
      rw [Ideal.map_span, ← Set.range_comp, map_mul] at h3
      have hu : IsUnit ((secRes (XX Z) hNW).toRingHom t) := by
        have := (XX Z).left.toRingedSpace.isUnit_res_basicOpen t'
        rw [show (secRes (XX Z) hNW).toRingHom t = _ from secRes_apply (XX Z) hNW t]
        exact this
      exact (Ideal.unit_mul_mem_iff_mem _ hu).1 h3
    · rintro _ ⟨k, rfl⟩
      refine Ideal.mem_map_of_mem (secRes (XX Z) hNW).toRingHom ?_
      show m (b (u k) - a (u k)) = 0
      rw [map_sub, ma, mb, sub_self]
  · rw [ker_res Z c.aff hN' h, c.ker, Ideal.map_span, ← Set.range_comp]
    rfl

end geo

end UpperTheory.Gal.KunnethLefschetz.G
