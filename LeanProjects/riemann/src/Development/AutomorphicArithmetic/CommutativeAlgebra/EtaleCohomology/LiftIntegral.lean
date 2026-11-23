import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitsOfSplitOn

noncomputable section

open TensorProduct

namespace UpperTheory.Ru.crystallineComparison

section Alg

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

private lemma exists_idem [Algebra.FormallyUnramified R A] [Module.Finite R A] (σ : A →ₐ[R] R) :
    ∃ e : A, IsIdempotentElem e ∧ σ e = 1 ∧ ∀ a, a * e = algebraMap R A (σ a) * e := by
  obtain ⟨t, ht, ht1⟩ := Algebra.FormallyUnramified.iff_exists_tensorProduct.1
    (inferInstance : Algebra.FormallyUnramified R A)
  let f : A ⊗[R] A →ₐ[R] A :=
    Algebra.TensorProduct.lift ((Algebra.ofId R A).comp σ) (AlgHom.id R A) fun _ _ => Commute.all _ _
  have hf : ∀ x y, f (x ⊗ₜ y) = algebraMap R A (σ x) * y := fun x y => by
    simp [f, Algebra.ofId_apply]
  have key : ∀ a, a * f t = algebraMap R A (σ a) * f t := fun a => by
    have := congrArg f (ht a)
    rw [map_mul, map_sub, hf, hf, map_zero, map_one, map_one, one_mul, mul_one, sub_mul, sub_eq_zero] at this
    exact this
  have h1 : σ (f t) = 1 := by
    have : (σ.comp f) = σ.comp (Algebra.TensorProduct.lmul' R) := by
      ext x <;> simp [hf]
    have h2 := DFunLike.congr_fun this t
    simpa [ht1] using h2
  refine ⟨f t, ?_, h1, key⟩
  change f t * f t = f t
  rw [key, h1, map_one, one_mul]

private lemma finite_algHom (K : Type) [Field K] [Algebra R K] [Module.Finite R A] : Finite (A →ₐ[R] K) := by
  have : Finite (K ⊗[R] A →ₐ[K] K) := inferInstance
  refine Finite.of_injective (fun f : A →ₐ[R] K =>
    (Algebra.TensorProduct.lift (AlgHom.id K K) f fun _ _ => Commute.all _ _ : K ⊗[R] A →ₐ[K] K)) ?_
  intro f g h
  ext a
  simpa using DFunLike.congr_fun h (1 ⊗ₜ a)

private lemma quot_etale [Algebra.Etale R A] {e : A} (he : IsIdempotentElem e) :
    Algebra.Etale R (A ⧸ Ideal.span {e}) := by
  have hf : IsIdempotentElem (1 - e) := he.one_sub
  have : IsLocalization.Away (1 - e) (A ⧸ Ideal.span {e}) :=
    IsLocalization.away_of_isIdempotentElem hf (by simp [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker])
      Ideal.Quotient.mk_surjective
  have : Algebra.FormallyEtale A (A ⧸ Ideal.span {e}) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (1 - e))
  have : Algebra.FinitePresentation A (A ⧸ Ideal.span {e}) :=
    Algebra.FinitePresentation.quotient ⟨{e}, by simp⟩
  have : Algebra.Etale A (A ⧸ Ideal.span {e}) := ⟨inferInstance, inferInstance⟩
  exact Algebra.Etale.comp R A _

private lemma card_quot [Module.Finite R A] {e : A} (σ : A →ₐ[R] R) (h1 : σ e = 1)
    (he : ∀ a, a * e = algebraMap R A (σ a) * e) (hi : IsIdempotentElem e) (K : Type) [Field K] [Algebra R K] :
    Nat.card (A →ₐ[R] K) = Nat.card (A ⧸ Ideal.span {e} →ₐ[R] K) + 1 := by
  have hfin : Finite (A →ₐ[R] K) := finite_algHom K
  let π : A →ₐ[R] A ⧸ Ideal.span {e} := Ideal.Quotient.mkₐ R _
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hπe : π e = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  have hB : Finite (A ⧸ Ideal.span {e} →ₐ[R] K) :=
    Finite.of_injective (fun g => g.comp π) fun g g' h => by
      ext x
      obtain ⟨a, rfl⟩ := hπ x
      exact DFunLike.congr_fun h a
  let F : Option (A ⧸ Ideal.span {e} →ₐ[R] K) → (A →ₐ[R] K) := fun o =>
    o.elim ((Algebra.ofId R K).comp σ) fun g => g.comp π
  have hF : Function.Bijective F := by
    constructor
    · rintro (_ | g) (_ | g') h
      · rfl
      · have := DFunLike.congr_fun h e
        simp [F, h1, hπe, Algebra.ofId_apply] at this
      · have := DFunLike.congr_fun h e
        simp [F, h1, hπe, Algebra.ofId_apply] at this
      · congr 1
        ext x
        obtain ⟨a, rfl⟩ := hπ x
        exact DFunLike.congr_fun h a
    · intro f
      have hfe : IsIdempotentElem (f e) := hi.map f
      rcases IsIdempotentElem.iff_eq_zero_or_one.1 hfe with h0 | h0
      · have hk : ∀ a ∈ Ideal.span {e}, f a = 0 := fun a ha => by
          obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
          rw [map_mul, h0, mul_zero]
        refine ⟨some (Ideal.Quotient.liftₐ _ f hk), ?_⟩
        ext a
        simp only [F, π, Option.elim, AlgHom.comp_apply]
        exact Ideal.Quotient.lift_mk _ _ _
      · refine ⟨none, ?_⟩
        ext a
        have := congrArg f (he a)
        rw [map_mul, map_mul, h0, mul_one, mul_one, f.commutes] at this
        simp [F, this, Algebra.ofId_apply]
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Finite.card_option]

private lemma split_step [Module.Finite R A] [Algebra.Etale R A] {e : A} (σ : A →ₐ[R] R) (h1 : σ e = 1)
    (he : ∀ a, a * e = algebraMap R A (σ a) * e) (hi : IsIdempotentElem e) {d : ℕ}
    (z : Fin d → (A ⧸ Ideal.span {e} →ₐ[R] R))
    (hz : Function.Bijective fun (b : A ⧸ Ideal.span {e}) i => z i b) :
    ∃ w : Fin (d + 1) → (A →ₐ[R] R), Function.Bijective fun a i => w i a := by
  let π : A →ₐ[R] A ⧸ Ideal.span {e} := Ideal.Quotient.mkₐ R _
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hπe : π e = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  refine ⟨Fin.cons σ fun i => (z i).comp π, ?_, ?_⟩
  · intro a b h
    have h0 : σ a = σ b := congrFun h 0
    have hs : ∀ i : Fin d, z i (π a) = z i (π b) := fun i => congrFun h i.succ
    have hab : π a = π b := hz.1 (funext hs)
    have hmem : a - b ∈ Ideal.span {e} := by
      refine Ideal.Quotient.eq.1 hab
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
    have h2 : (a - b) * e = 0 := by
      rw [he, map_sub, h0, sub_self, map_zero, zero_mul]
    have h3 : (a - b) * e = a - b := by
      rw [← hc, mul_assoc, hi.eq]
    exact sub_eq_zero.1 (h3.symm.trans h2)
  · intro v
    obtain ⟨b, hb⟩ := hz.2 fun i => v i.succ
    obtain ⟨a, rfl⟩ := hπ b
    refine ⟨a * (1 - e) + algebraMap R A (v 0) * e, ?_⟩
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [h1]
    · have h2 : π (a * (1 - e) + algebraMap R A (v 0) * e) = π a := by
        simp only [map_add, map_mul, map_sub, map_one, hπe, sub_zero, mul_one, mul_zero, add_zero]
      change z i (π _) = v i.succ
      rw [h2]
      exact congrFun hb i

private lemma split_alg (H : ∀ (A : Type) [CommRing A] [Algebra R A], Algebra.Etale R A →
      Function.Surjective (PrimeSpectrum.comap (algebraMap R A)) → Nonempty (A →ₐ[R] R)) (d : ℕ) :
    ∀ (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A] [Algebra.Etale R A],
      (∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra R K], Nat.card (A →ₐ[R] K) = d) →
      ∃ z : Fin d → (A →ₐ[R] R), Function.Bijective fun a i => z i a := by
  induction d with
  | zero =>
    intro A _ _ _ _ hd
    refine ⟨Fin.elim0, ?_, fun v => ⟨0, Subsingleton.elim _ _⟩⟩
    have : Subsingleton A := by
      by_contra hn
      have : Nontrivial A := not_subsingleton_iff_nontrivial.1 hn
      obtain ⟨m, hm⟩ := Ideal.exists_maximal A
      letI := Ideal.Quotient.field m
      have h0 := hd (AlgebraicClosure (A ⧸ m))
      have hfin := finite_algHom (R := R) (A := A) (AlgebraicClosure (A ⧸ m))
      have hne : Nonempty (A →ₐ[R] AlgebraicClosure (A ⧸ m)) := ⟨IsScalarTower.toAlgHom R A _⟩
      have := Nat.card_pos (α := A →ₐ[R] AlgebraicClosure (A ⧸ m))
      omega
    exact fun a b _ => Subsingleton.elim a b
  | succ d ih =>
    intro A _ _ _ _ hd
    have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R A)) := by
      intro p
      have h0 := hd (AlgebraicClosure p.asIdeal.ResidueField)
      have hne : Nonempty (A →ₐ[R] AlgebraicClosure p.asIdeal.ResidueField) := by
        have := Nat.card_pos_iff.1 (h0 ▸ Nat.succ_pos d : 0 < Nat.card (A →ₐ[R] AlgebraicClosure p.asIdeal.ResidueField))
        exact this.1
      obtain ⟨g⟩ := hne
      refine ⟨⟨RingHom.ker g, RingHom.ker_isPrime _⟩, ?_⟩
      ext x
      have h2 : (algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField))
          (algebraMap R p.asIdeal.ResidueField x) = g (algebraMap R A x) := by
        rw [g.commutes, ← IsScalarTower.algebraMap_apply]
      change g (algebraMap R A x) = 0 ↔ x ∈ p.asIdeal
      rw [← h2, map_eq_zero, Ideal.algebraMap_residueField_eq_zero]
    obtain ⟨σ⟩ := H A inferInstance hsurj
    obtain ⟨e, hi, h1, he⟩ := exists_idem σ
    have := quot_etale (R := R) hi
    obtain ⟨z, hz⟩ := ih (A ⧸ Ideal.span {e}) fun K _ _ _ => by
      have := card_quot σ h1 he hi K
      have := hd K
      omega
    exact split_step σ h1 he hi z hz

end Alg

private lemma lift_integral {U R S : Type} [CommRing U] [CommRing R] [CommRing S] (g : U →+* R)
    (hg : Function.Injective g) (hc : ∀ x : R, g.IsIntegralElem x → ∃ u, g u = x) (ψ : U →+* S)
    (hψ : ψ.IsIntegral) (τ : S →+* R) (hτ : τ.comp ψ = g) : ∃ τ' : S →+* U, g.comp τ' = τ := by
  have hr : ∀ s, τ s ∈ g.range := fun s => by
    obtain ⟨p, hp, h0⟩ := hψ s
    refine hc _ ⟨p, hp, ?_⟩
    have := Polynomial.hom_eval₂ p ψ τ s
    rw [h0, map_zero, hτ] at this
    exact this.symm
  let e : U ≃+* g.range := RingEquiv.ofBijective g.rangeRestrict
    ⟨fun a b h => hg (congrArg Subtype.val h), RingHom.rangeRestrict_surjective g⟩
  refine ⟨(e.symm : g.range →+* U).comp (τ.codRestrict g.range hr), ?_⟩
  ext s
  have := e.apply_symm_apply (τ.codRestrict g.range hr s)
  exact congrArg Subtype.val this

section Sch

open CategoryTheory Limits AlgebraicGeometry

private lemma extend_pt {U R : Type} [CommRing U] [CommRing R] (g : U →+* R)
    (hg : Function.Injective g) (hc : ∀ x : R, g.IsIntegralElem x → ∃ u, g u = x) {P : Scheme.{0}}
    (q : P ⟶ Spec (CommRingCat.of U)) [IsFinite q] (t : Spec (CommRingCat.of R) ⟶ P)
    (ht : t ≫ q = Spec.map (CommRingCat.ofHom g)) :
    ∃ t' : Spec (CommRingCat.of U) ⟶ P, t' ≫ q = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom g) ≫ t' = t := by
  have : IsAffine P := isAffine_of_isAffineHom q
  let ψ : CommRingCat.of U ⟶ Γ(P, ⊤) := Spec.preimage (P.isoSpec.inv ≫ q)
  have hψ : Spec.map ψ = P.isoSpec.inv ≫ q := Spec.map_preimage _
  let τ : Γ(P, ⊤) ⟶ CommRingCat.of R := Spec.preimage (t ≫ P.isoSpec.hom)
  have hτ : Spec.map τ = t ≫ P.isoSpec.hom := Spec.map_preimage _
  have hfin : ψ.hom.Finite := (IsFinite.SpecMap_iff ψ).1 (by rw [hψ]; infer_instance)
  have hcomp : ψ ≫ τ = CommRingCat.ofHom g := Spec.map_injective (by
    rw [Spec.map_comp, hψ, hτ, Category.assoc, Iso.hom_inv_id_assoc, ht])
  obtain ⟨τ', hτ'⟩ := lift_integral g hg hc ψ.hom hfin.to_isIntegral τ.hom
    (congrArg CommRingCat.Hom.hom hcomp)
  have h1 : CommRingCat.ofHom τ' ≫ CommRingCat.ofHom g = τ := by
    ext a
    exact DFunLike.congr_fun hτ' a
  have h2 : ψ ≫ CommRingCat.ofHom τ' = 𝟙 _ := by
    ext a
    apply hg
    have := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcomp) a
    have h3 := DFunLike.congr_fun hτ' (ψ.hom a)
    simpa using h3.trans this
  refine ⟨Spec.map (CommRingCat.ofHom τ') ≫ P.isoSpec.inv, ?_, ?_⟩
  · rw [Category.assoc, ← hψ, ← Spec.map_comp, h2, Spec.map_id]
  · rw [← Category.assoc, ← Spec.map_comp, h1, hτ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private lemma split_sch {R : Type} [CommRing R]
    (H : ∀ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), Etale f → Surjective f → ∃ s, s ≫ f = 𝟙 _)
    (d : ℕ) {W : Scheme.{0}} (q : W ⟶ Spec (CommRingCat.of R)) [IsFinite q] [Etale q]
    (hd : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra R K],
      Nat.card {w : Spec (CommRingCat.of K) ⟶ W // w ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R K))} = d) :
    ∃ s : Fin d → (Spec (CommRingCat.of R) ⟶ W), (∀ i, s i ≫ q = 𝟙 _) ∧ IsIso (Sigma.desc s) := by
  have : IsAffine W := isAffine_of_isAffineHom q
  let ψ : CommRingCat.of R ⟶ Γ(W, ⊤) := Spec.preimage (W.isoSpec.inv ≫ q)
  have hψ : Spec.map ψ = W.isoSpec.inv ≫ q := Spec.map_preimage _
  letI : Algebra R Γ(W, ⊤) := ψ.hom.toAlgebra
  have hfin : Module.Finite R Γ(W, ⊤) := (IsFinite.SpecMap_iff ψ).1 (by rw [hψ]; infer_instance)
  have het : Algebra.Etale R Γ(W, ⊤) := by
    have h1 : Etale (Spec.map ψ) := by rw [hψ]; infer_instance
    have h2 := (HasRingHomProperty.Spec_iff (P := @Etale)).1 h1
    exact (RingHom.etale_algebraMap).1 h2
  have Hr : ∀ (A : Type) [CommRing A] [Algebra R A], Algebra.Etale R A →
      Function.Surjective (PrimeSpectrum.comap (algebraMap R A)) → Nonempty (A →ₐ[R] R) := by
    intro A _ _ hA hs
    have h1 : Etale (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
      (HasRingHomProperty.Spec_iff (P := @Etale)).2 ((RingHom.etale_algebraMap).2 hA)
    have h2 : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R A))) := ⟨hs⟩
    obtain ⟨s, hs⟩ := H _ _ h1 h2
    let σ : CommRingCat.of A ⟶ CommRingCat.of R := Spec.preimage s
    have hσ : Spec.map σ = s := Spec.map_preimage _
    have h3 : CommRingCat.ofHom (algebraMap R A) ≫ σ = 𝟙 _ := Spec.map_injective (by
      rw [Spec.map_comp, hσ, hs, Spec.map_id])
    exact ⟨{ σ.hom with
      commutes' := fun r => DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h3) r }⟩
  have hc : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra R K], Nat.card (Γ(W, ⊤) →ₐ[R] K) = d := by
    intro K _ _ _
    rw [← hd K]
    refine Nat.card_congr (Equiv.ofBijective (fun f => ⟨Spec.map (CommRingCat.ofHom f.toRingHom) ≫ W.isoSpec.inv, ?_⟩) ⟨?_, ?_⟩)
    · rw [Category.assoc, ← hψ, ← Spec.map_comp]
      congr 1
      ext r
      exact f.commutes r
    · intro f f' h
      have h1 := (cancel_mono W.isoSpec.inv).1 (congrArg Subtype.val h)
      have h2 := Spec.map_injective h1
      ext a
      exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h2) a
    · rintro ⟨w, hw⟩
      let φ : Γ(W, ⊤) ⟶ CommRingCat.of K := Spec.preimage (w ≫ W.isoSpec.hom)
      have hφ : Spec.map φ = w ≫ W.isoSpec.hom := Spec.map_preimage _
      have h3 : ψ ≫ φ = CommRingCat.ofHom (algebraMap R K) := Spec.map_injective (by
        rw [Spec.map_comp, hψ, hφ, Category.assoc, Iso.hom_inv_id_assoc, hw])
      refine ⟨{ φ.hom with
        commutes' := fun r => DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h3) r }, ?_⟩
      apply Subtype.ext
      change Spec.map (CommRingCat.ofHom φ.hom) ≫ W.isoSpec.inv = w
      rw [CommRingCat.ofHom_hom, hφ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨z, hz⟩ := split_alg Hr d Γ(W, ⊤) hc
  refine ⟨fun i => Spec.map (CommRingCat.ofHom (z i).toRingHom) ≫ W.isoSpec.inv, fun i => ?_, ?_⟩
  · rw [Category.assoc, ← hψ, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext r
    exact (z i).commutes r
  · let Φ : Γ(W, ⊤) →+* (Fin d → R) := Pi.ringHom fun i => (z i).toRingHom
    have hΦ : IsIso (CommRingCat.ofHom Φ) :=
      (ConcreteCategory.isIso_iff_bijective _).2 hz
    have he : Sigma.desc (fun i => Spec.map (CommRingCat.ofHom (z i).toRingHom) ≫ W.isoSpec.inv) =
        sigmaSpec (fun _ : Fin d => CommRingCat.of R) ≫ Spec.map (CommRingCat.ofHom Φ) ≫ W.isoSpec.inv := by
      refine Sigma.hom_ext _ _ fun i => ?_
      rw [Sigma.ι_desc, ι_sigmaSpec_assoc, ← Category.assoc, ← Spec.map_comp]
      rfl
    rw [he]
    infer_instance

end Sch

end UpperTheory.Ru.crystallineComparison

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.crystallineComparison in

theorem UpperTheory.Ru.crystallineComparison.splitEx :
    UpperTheory.Ru.crystallineComparison.SplitEx := by
  intro l hl Y T U _ hnz hcl hsec y
  let R := Localization.Away (l : U)
  let x : Spec (CommRingCat.of R) ⟶ Y := awayPt l U ≫ y
  have hunit : IsUnit ((l : ℕ) : R) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := R) (l : U)
    simpa using this

  let V : Y.Opens := Y.basicOpen (l : Γ(Y, ⊤))
  have hV : Set.range x ⊆ Set.range V.ι := by
    have hu : IsUnit (x.appTop (l : Γ(Y, ⊤))) := by
      have := hunit.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      rw [map_natCast] at this
      rw [map_natCast]
      exact this
    have hpre : x ⁻¹ᵁ V = ⊤ := by
      rw [Scheme.preimage_basicOpen]
      exact Scheme.basicOpen_of_isUnit _ hu
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨a, rfl⟩
    have : a ∈ x ⁻¹ᵁ V := hpre ▸ trivial
    exact this
  let x' : Spec (CommRingCat.of R) ⟶ V.toScheme := IsOpenImmersion.lift V.ι x hV
  have hx' : x' ≫ V.ι = x := IsOpenImmersion.lift_fac _ _ _
  have sq : IsPullback (pullback.fst (T.p ∣_ V) x' ≫ (T.p ⁻¹ᵁ V).ι) (pullback.snd (T.p ∣_ V) x') T.p x := by
    rw [← hx']
    exact (IsPullback.of_hasPullback (T.p ∣_ V) x').paste_horiz (isPullback_morphismRestrict T.p V).flip
  have het0 : Etale (T.p ∣_ V) := T.et
  have het1 : Etale (pullback.snd (T.p ∣_ V) x') := inferInstance
  have het : Etale (pullback.snd T.p x) := by
    have : pullback.snd T.p x = sq.isoPullback.inv ≫ pullback.snd (T.p ∣_ V) x' := by
      simp
    rw [this]
    infer_instance
  have hfin0 : IsFinite T.p := T.fin
  have hdeg : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra R K],
      Nat.card {w : Spec (CommRingCat.of K) ⟶ pullback T.p x //
        w ≫ pullback.snd T.p x = Spec.map (CommRingCat.ofHom (algebraMap R K))} = T.d := by
    intro K _ _ _
    have hl0 : ((l : ℕ) : K) ≠ 0 := by
      have := hunit.map (algebraMap R K)
      rw [map_natCast] at this
      exact this.ne_zero
    rw [← T.deg K hl0 (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ x)]
    refine Nat.card_congr (Equiv.ofBijective (fun w => ⟨w.1 ≫ pullback.fst T.p x, ?_⟩) ⟨?_, ?_⟩)
    · rw [Category.assoc, pullback.condition, ← Category.assoc, w.2]
    · rintro ⟨w, hw⟩ ⟨w', hw'⟩ h
      apply Subtype.ext
      refine pullback.hom_ext (congrArg Subtype.val h) (hw.trans hw'.symm)
    · rintro ⟨w, hw⟩
      exact ⟨⟨pullback.lift w _ hw, pullback.lift_snd _ _ _⟩, Subtype.ext (pullback.lift_fst _ _ _)⟩
  obtain ⟨s, hs, hiso⟩ := split_sch hsec T.d (pullback.snd T.p x) hdeg
  have hinj : Function.Injective (algebraMap U R) :=
    IsLocalization.injective R (Submonoid.powers_le.2 hnz)
  have hext : ∀ i, ∃ t' : Spec (CommRingCat.of U) ⟶ pullback T.p y,
      t' ≫ pullback.snd T.p y = 𝟙 _ ∧ awayPt l U ≫ t' ≫ pullback.fst T.p y = s i ≫ pullback.fst T.p x := by
    intro i
    have hc : s i ≫ pullback.fst T.p x ≫ T.p = awayPt l U ≫ y := by
      rw [pullback.condition, ← Category.assoc, hs, Category.id_comp]
    obtain ⟨t', h1, h2⟩ := extend_pt (algebraMap U R) hinj hcl (pullback.snd T.p y)
      (pullback.lift (s i ≫ pullback.fst T.p x) (awayPt l U) (by rw [Category.assoc, hc]))
      (pullback.lift_snd _ _ _)
    refine ⟨t', h1, ?_⟩
    rw [← Category.assoc, h2, pullback.lift_fst]
  choose t' ht1 ht2 using hext
  refine ⟨fun i => t' i ≫ pullback.fst T.p y, fun i => ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, ht1, Category.id_comp]
  · have hz : ∀ i, (awayPt l U ≫ t' i ≫ pullback.fst T.p y) ≫ T.p = awayPt l U ≫ y := fun i => by
      rw [ht2, Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
    refine ⟨hz, ?_⟩
    convert hiso using 2
    funext i
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst]
      exact ht2 i
    · rw [pullback.lift_snd, hs]
