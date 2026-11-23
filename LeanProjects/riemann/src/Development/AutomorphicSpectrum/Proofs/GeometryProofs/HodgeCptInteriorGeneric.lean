import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceDecompositionInternalStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeBasic

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped TensorProduct

theorem mem_abLocus_of_map {X Y : Scheme.{0}} {G : Over X} {G' : Over Y} {f : X ⟶ Y} {φ : G.left ⟶ G'.left}
    (h : IsPullback φ G.hom G'.hom f) {x : X} (hx : f x ∈ abLocus G') : x ∈ abLocus G := by
  intro K _ _ t hxt
  obtain ⟨u, rfl⟩ := hxt
  have hp : IsProper (pullback.snd G'.hom (t ≫ f)) := hx K (t ≫ f) ⟨u, by simp⟩
  have sq : IsPullback (pullback.fst G.hom t ≫ φ) (pullback.snd G.hom t) G'.hom (t ≫ f) :=
    (IsPullback.of_hasPullback G.hom t).paste_horiz h
  rw [← sq.isoPullback_hom_snd]
  infer_instance

theorem mem_of_dense_of_maximal {P : Type} [TopologicalSpace P] [TopologicalSpace.NoetherianSpace P] [QuasiSober P]
    {U : Set P} (hU : IsOpen U) (hd : Dense U) {y : P} (hy : ∀ y', y' ⤳ y → y' = y) : y ∈ U := by
  classical
  have hCi : IsIrreducible (irreducibleComponent y) := isIrreducible_irreducibleComponent
  have hCc : IsClosed (irreducibleComponent y) := isClosed_irreducibleComponent
  have hgen := hCi.isGenericPoint_genericPoint_closure
  rw [hCc.closure_eq] at hgen
  have hη : hCi.genericPoint = y := hy _ (hgen.specializes mem_irreducibleComponent)
  rw [hη] at hgen
  have hmax := irreducibleComponent_mem_irreducibleComponents y
  set D : Set P := ⋃₀ (irreducibleComponents P \ {irreducibleComponent y}) with hD
  have hDc : IsClosed D := by
    rw [hD, Set.sUnion_eq_biUnion]
    exact Set.Finite.isClosed_biUnion
      (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset Set.diff_subset)
      fun C hC => isClosed_of_mem_irreducibleComponents C hC.1
  have hyD : y ∉ D := by
    rintro ⟨C, ⟨hC, hne⟩, hyC⟩
    have hle : irreducibleComponent y ⊆ C := by
      rw [← hgen.def]
      exact (isClosed_of_mem_irreducibleComponents C hC).closure_subset_iff.2 (by simpa using hyC)
    exact hne (le_antisymm (hmax.2 hC.1 hle) hle)
  obtain ⟨u, huD, huU⟩ := hd.inter_open_nonempty Dᶜ hDc.isOpen_compl ⟨y, hyD⟩
  have huC : u ∈ irreducibleComponent y := by
    by_contra hne
    refine huD ⟨irreducibleComponent u, ⟨irreducibleComponent_mem_irreducibleComponents u, ?_⟩,
      mem_irreducibleComponent⟩
    intro e
    exact hne (by
      have : u ∈ irreducibleComponent u := mem_irreducibleComponent
      rw [Set.mem_singleton_iff.1 e] at this
      exact this)
  exact (hgen.specializes huC).mem_open hU huU

theorem noetherianSpace_pullback {X : Scheme.{0}} {O F : Type} [CommRing O] [Field F] {s : X ⟶ Sp O}
    (hs : IsProjOver s) (β : O →+* F) : TopologicalSpace.NoetherianSpace ↥(pullback s (spMap β)) := by
  obtain ⟨N, i, hi, rfl⟩ := hs
  have := isProper_str O N
  have : IsProper (i ≫ PSpace.str O N) := inferInstance
  have hl : LocallyOfFiniteType (pullback.snd (i ≫ PSpace.str O N) (spMap β)) := inferInstance
  have hq : QuasiCompact (pullback.snd (i ≫ PSpace.str O N) (spMap β)) := inferInstance
  have : IsLocallyNoetherian (pullback (i ≫ PSpace.str O N) (spMap β)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd _ _)
  have : CompactSpace ↥(pullback (i ≫ PSpace.str O N) (spMap β)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd _ _)
  have : IsNoetherian (pullback (i ≫ PSpace.str O N) (spMap β)) := {}
  infer_instance

theorem isIntegral_tensor {O Ω₀ F : Type} [CommRing O] [Field Ω₀] [Field F] [Algebra O Ω₀] [Algebra O F]
    (hγ : Function.Injective (algebraMap O Ω₀))
    (hF : ∀ u : F, ∃ a : O, a ≠ 0 ∧ _root_.IsIntegral O (a • u)) :
    Algebra.IsIntegral Ω₀ (Ω₀ ⊗[O] F) := by
  have h1 : ∀ u : F, _root_.IsIntegral Ω₀ ((1 : Ω₀) ⊗ₜ[O] u) := by
    intro u
    obtain ⟨a, ha, hi⟩ := hF u
    have h2 : _root_.IsIntegral O ((1 : Ω₀) ⊗ₜ[O] (a • u)) :=
      hi.map (Algebra.TensorProduct.includeRight : F →ₐ[O] Ω₀ ⊗[O] F)
    have h3 : _root_.IsIntegral Ω₀ ((1 : Ω₀) ⊗ₜ[O] (a • u)) := h2.tower_top
    have ha' : algebraMap O Ω₀ a ≠ 0 := fun h => ha (hγ (by rw [h, map_zero]))
    have e : (1 : Ω₀) ⊗ₜ[O] u = (algebraMap O Ω₀ a)⁻¹ • ((1 : Ω₀) ⊗ₜ[O] (a • u)) := by
      rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul, smul_eq_mul, _root_.mul_one, Algebra.smul_def,
        mul_inv_cancel₀ ha']
    rw [e]
    exact h3.smul _
  refine ⟨fun x => ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => exact isIntegral_zero
  | tmul a u =>
    have e : a ⊗ₜ[O] u = a • ((1 : Ω₀) ⊗ₜ[O] u) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [e]
    exact (h1 u).smul a
  | add x y hx hy => exact hx.add hy

theorem exists_integral_multiple_of_injective {O : Type} [CommRing O] {F : IntermediateField ℚ ℂ}
    [FiniteDimensional ℚ F] (β : O →+* F) (hβ : Function.Injective β) (u : F) :
    letI := β.toAlgebra
    ∃ a : O, a ≠ 0 ∧ _root_.IsIntegral O (a • u) := by
  letI := β.toAlgebra
  have : CharZero O := β.charZero
  have hQ : IsAlgebraic ℚ u := Algebra.IsAlgebraic.isAlgebraic u
  have hZ : IsAlgebraic ℤ u := (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 hQ
  have hO : IsAlgebraic O u := hZ.extendScalars (Int.cast_injective)
  exact hO.exists_integral_multiple

theorem eq_of_specializes_of_fst {X : Scheme.{0}} {O F Ω₀ : Type} [CommRing O] [Field F] [Field Ω₀] (s : X ⟶ Sp O)
    (β : O →+* F) (g₀ : O →+* Ω₀) (ξ₀ : Sp Ω₀ ⟶ X) (h₀ : IsCptGen ξ₀) (hs : ξ₀ ≫ s = spMap g₀)
    (hγ : Function.Injective g₀)
    (hF : letI := β.toAlgebra; ∀ u : F, ∃ a : O, a ≠ 0 ∧ _root_.IsIntegral O (a • u))
    {y y' : ↥(pullback s (spMap β))} (hy : pullback.fst s (spMap β) y = genPt ξ₀) (hyy : y' ⤳ y) : y' = y := by
  letI := β.toAlgebra
  letI := g₀.toAlgebra
  have hy' : pullback.fst s (spMap β) y' = genPt ξ₀ :=
    GlobalTheory.CompanionTheory.Ar.CptInh.nogen ξ₀ h₀ _ (hy ▸ hyy.map (pullback.fst s (spMap β)).continuous)
  have hsurj : SurjectiveOnStalks ξ₀ := by
    have : IsIso (Scheme.stalkClosedPointTo ξ₀) := (ConcreteCategory.isIso_iff_bijective _).2 h₀.bij
    rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₀]
    infer_instance
  have hemb := SurjectiveOnStalks.isEmbedding_pullback (pullback.fst s (spMap β)) ξ₀
  obtain ⟨z, hz, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.fst s (spMap β)) (g := ξ₀) y
    (IsLocalRing.closedPoint Ω₀) hy
  obtain ⟨z', hz', hz₂'⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.fst s (spMap β)) (g := ξ₀) y'
    (IsLocalRing.closedPoint Ω₀) hy'
  have hzz : z' ⤳ z := by
    rw [← hemb.isInducing.specializes_iff, specializes_prod]
    simp only [hz, hz', hz₂, hz₂']
    exact ⟨hyy, specializes_rfl⟩
  have sq : IsPullback (pullback.snd (pullback.fst s (spMap β)) ξ₀)
      (pullback.fst (pullback.fst s (spMap β)) ξ₀ ≫ pullback.snd s (spMap β)) (spMap g₀) (spMap β) := by
    rw [← hs]
    exact (IsPullback.of_hasPullback (pullback.fst s (spMap β)) ξ₀).flip.paste_vert
      (IsPullback.of_hasPullback s (spMap β))
  let e := sq.isoPullback ≪≫ pullbackSpecIso O Ω₀ F
  have hint : Algebra.IsIntegral Ω₀ (Ω₀ ⊗[O] F) := isIntegral_tensor hγ hF
  let p' : PrimeSpectrum (Ω₀ ⊗[O] F) := e.hom z'
  let p : PrimeSpectrum (Ω₀ ⊗[O] F) := e.hom z
  have hle : p' ≤ p := (PrimeSpectrum.le_iff_specializes _ _).2 (hzz.map e.hom.continuous)
  have hcm : (Ideal.comap (algebraMap Ω₀ (Ω₀ ⊗[O] F)) p'.asIdeal).IsMaximal :=
    Ideal.IsPrime.isMaximal' (Ideal.comap_isPrime _ _)
  have hmax : p'.asIdeal.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := Ω₀) p'.asIdeal hcm
  have heq : p' = p := PrimeSpectrum.ext (hmax.eq_of_le p.isPrime.ne_top hle)
  have hzeq : z' = z := by
    have h := congrArg e.inv heq
    simpa [p, p'] using h
  rw [← hz, ← hz', hzeq]

theorem mem_range_jQ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    (hβ : Function.Injective β) {Ω₀ : Type} [Field Ω₀] (ξ₀ : Sp Ω₀ ⟶ Y.X) (h₀ : IsCptGen ξ₀) (g₀ : O →+* Ω₀)
    (hs : ξ₀ ≫ Y.s = spMap g₀) (hg : Function.Injective g₀) (y : ↥(pullback Y.s (spMap β)))
    (hy : pullback.fst Y.s (spMap β) y = genPt ξ₀) : y ∈ Set.range Y.jQ := by
  have := noetherianSpace_pullback Y.proj β
  have := Y.jQ_open
  have := c.fin
  exact mem_of_dense_of_maximal Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense fun y' h' =>
    eq_of_specializes_of_fst Y.s β g₀ ξ₀ h₀ hs hg (exists_integral_multiple_of_injective β hβ) hy h'

theorem mem_regAt_of_isIntegral {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hg : IsCptGen ξ) (all : ∀ q : X, genPt ξ ⤳ q) (hn : IsNormalScheme X) (q : Cpt ξ) {a : Ω}
    (ha : _root_.IsIntegral ℤ a) : a ∈ regAt ξ q := by
  have hgen : IsGenericPoint (genPt ξ) (Set.univ : Set X) :=
    Set.eq_univ_of_forall fun q => specializes_iff_mem_closure.1 (all q)
  have : IrreducibleSpace X :=
    { isPreirreducible_univ := hgen.isIrreducible.2, toNonempty := ⟨genPt ξ⟩ }
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have := (hn x).1
    infer_instance
  have := isReduced_of_isReduced_stalk X
  have : AlgebraicGeometry.IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  have hgp : genericPoint X = genPt ξ := (genericPoint_spec X).eq hgen
  have key : ∀ (x : X) (_ : x = genericPoint X) (hs : x ⤳ genericPoint X),
      IsIso (X.presheaf.stalkSpecializes hs) := by
    rintro x rfl hs
    have : X.presheaf.stalkSpecializes hs = 𝟙 _ := TopCat.Presheaf.stalkSpecializes_refl _ _
    rw [this]
    infer_instance
  have hsp : genPt ξ ⤳ genericPoint X := hgp ▸ specializes_rfl
  have := key _ hgp.symm hsp
  let e : X.functionField →+* Ω := (X.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo ξ).hom
  have hs₁ : Function.Surjective (X.presheaf.stalkSpecializes hsp).hom :=
    ((ConcreteCategory.isIso_iff_bijective (X.presheaf.stalkSpecializes hsp)).1 inferInstance).2
  have he : Function.Surjective e := hg.bij.2.comp hs₁
  have hmap : ∀ x, genMap ξ q x = e (algebraMap (X.presheaf.stalk q.1) X.functionField x) := by
    intro x
    have h := TopCat.Presheaf.stalkSpecializes_comp X.presheaf hsp (genericPoint_specializes q.1)
    have h' := congrArg (fun m => (m ≫ Scheme.stalkClosedPointTo ξ).hom x) h
    exact h'.symm
  obtain ⟨b, rfl⟩ := he a
  have hb : _root_.IsIntegral ℤ b := by
    refine (isIntegral_algHom_iff e.toIntAlgHom e.injective).1 ha
  have := (hn q.1).2
  have hb' : _root_.IsIntegral (X.presheaf.stalk q.1) b := hb.tower_top
  obtain ⟨w, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hb'
  exact ⟨w, hmap w⟩

section Labels

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rt0_ne_zero (H : Host E) : H.rt0 ≠ 0 := by
  intro h
  have h1 := H.sqrt_neg_disc_sq
  rw [h] at h1
  have h2 : (H.d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  exact h2 (by simpa using h1.symm)

theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  have h := H.sqrt_neg_disc_sq
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, neg_zero] at h1 h2
  have hd : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
  have hre : H.rt0.re = 0 := by
    by_contra hne
    have him : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [him] at h1
    nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext
  · simp [hre]
  · simp

def labelHom (H : Host E) : CMType H ⊕ CMType H → (E →+* ℂ)
  | .inl τ => τ.1
  | .inr τ => ComplexEmbedding.conjugate τ.1

theorem embed_rt (H : Host E) (σ : E →+* ℂ) : σ (H.rt : E) = H.rt0 ∨ σ (H.rt : E) = -H.rt0 := by
  have h1 : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have h2 : σ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, h1, H.sqrt_neg_disc_sq]
    simp
  exact sq_eq_sq_iff_eq_or_eq_neg.1 h2

theorem labelHom_bijective (H : Host E) : Function.Bijective (labelHom H) := by
  have hval : ∀ τ : CMType H, ComplexEmbedding.conjugate τ.1 (H.rt : E) = -H.rt0 := fun τ => by
    rw [ComplexEmbedding.conjugate_coe_eq, τ.2, rt0_conj_neg_ne_zero]
  have hne : H.rt0 ≠ -H.rt0 := fun h => rt0_ne_zero H (self_eq_neg.1 h)
  constructor
  · rintro (τ | τ) (τ' | τ') h
    · exact congrArg _ (Subtype.ext h)
    · exact absurd (by simpa [labelHom, τ.2, hval τ'] using congrArg (· (H.rt : E)) h) hne
    · exact absurd (by simpa [labelHom, τ'.2, hval τ] using (congrArg (· (H.rt : E)) h).symm) hne
    · exact congrArg _ (Subtype.ext (star_injective h))
  · intro σ
    rcases embed_rt H σ with h | h
    · exact ⟨.inl ⟨σ, h⟩, rfl⟩
    · refine ⟨.inr ⟨ComplexEmbedding.conjugate σ, ?_⟩, ?_⟩
      · rw [ComplexEmbedding.conjugate_coe_eq, h, map_neg, rt0_conj_neg_ne_zero, neg_neg]
      · exact star_star σ

theorem coe_labelEmb {H : Host E} {l : Level H} (c : Coeff l) (s : CMType H ⊕ CMType H) (a : 𝓞 E) :
    ((labelEmb c s a : c.F) : ℂ) = labelHom H s (a : E) := by
  rcases s with τ | τ
  · rfl
  · show τ.1 ((H.bar a : 𝓞 E) : E) = ComplexEmbedding.conjugate τ.1 (a : E)
    rw [H.bar_eq, ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]

theorem labelEmb_injective {H : Host E} {l : Level H} (c : Coeff l) :
    Function.Injective (labelEmb (H := H) c) := by
  intro s s' h
  refine (labelHom_bijective H).1 ?_
  refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => ?_)
  show labelHom H s (a : E) = labelHom H s' (a : E)
  rw [← coe_labelEmb c, ← coe_labelEmb c, h]

end Labels

end GlobalTheory.CompanionTheory.Ar.HodgeBasic

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem HodgeCpt.basic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ)
    (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y), Function.Injective β → 𝔐.Interior 𝔐.ξ ∧
      (∃ x : Sp Ω ⟶ Xo.XF c, 𝔐.ξ ≫ 𝔐.f = x ≫ Y.j) ∧ CharZero Ω ∧ Function.Injective 𝔐.emb ∧
      (∀ s, Module.finrank Ω (𝔐.Vgen s) = labelRk D s) ∧ (⨆ s, 𝔐.Vgen s) = ⊤ ∧ iSupIndep 𝔐.Vgen ∧
      ∀ s a (q : Cpt 𝔐.ξ), 𝔐.emb s a ∈ regAt 𝔐.ξ q := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 hβ
  classical
  have hcst : Function.Injective 𝔐.cst := 𝔐.cst.injective
  have hchar : CharZero Ω := charZero_of_injective_ringHom hcst

  let g₀ : O →+* 𝔐.Ω₀ := (Spec.preimage (𝔐.ξ₀ ≫ Y.s)).hom
  have hs : 𝔐.ξ₀ ≫ Y.s = spMap g₀ := by
    show _ = Spec.map (CommRingCat.ofHom (Spec.preimage (𝔐.ξ₀ ≫ Y.s)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hfn : 𝔐.ξ ≫ 𝔐.f = spMap 𝔐.fn ≫ 𝔐.ξ₀ := 𝔐.fn_over
  have hcomp : 𝔐.fn.comp g₀ = 𝔐.cst.comp β := by
    have h1 : spMap (𝔐.fn.comp g₀) = spMap (𝔐.cst.comp β) := by
      rw [← 𝔐.cst_over, ← Category.assoc, hfn, Category.assoc, hs]
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  have hg : Function.Injective g₀ := by
    refine Function.Injective.of_comp (f := 𝔐.fn) ?_
    have : (𝔐.fn ∘ g₀) = 𝔐.cst ∘ β := congrArg DFunLike.coe hcomp
    rw [this]
    exact hcst.comp hβ

  have hw : (𝔐.ξ ≫ 𝔐.f) ≫ Y.s = spMap 𝔐.cst ≫ spMap β := by
    rw [Category.assoc, 𝔐.cst_over]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  let g : Sp Ω ⟶ pullback Y.s (spMap β) := pullback.lift (𝔐.ξ ≫ 𝔐.f) (spMap 𝔐.cst) hw
  have hgf : g ≫ pullback.fst _ _ = 𝔐.ξ ≫ 𝔐.f := pullback.lift_fst _ _ _
  have hall : ∀ w : Sp Ω, pullback.fst Y.s (spMap β) (g w) = genPt 𝔐.ξ₀ := by
    intro w
    rw [← Scheme.Hom.comp_apply, hgf, hfn, Scheme.Hom.comp_apply]
    exact congrArg 𝔐.ξ₀ (Subsingleton.elim (α := PrimeSpectrum 𝔐.Ω₀) _ _)
  have hran : Set.range g ⊆ Set.range Y.jQ := by
    rintro _ ⟨w, rfl⟩
    exact HodgeBasic.mem_range_jQ Y hβ 𝔐.ξ₀ 𝔐.gen₀ g₀ hs hg _ (hall w)
  have := Y.jQ_open
  have hinj : Function.Injective 𝔐.emb := by
    intro s s' h
    refine HodgeBasic.labelEmb_injective c (RingHom.ext fun a => hcst ?_)
    exact congrArg (fun m : 𝓞 E →+* Ω => m a) h
  letI : Fintype (CMType H) := Fintype.ofFinite _
  have hcard : Fintype.card (CMType H ⊕ CMType H) = Module.finrank ℚ E := by
    rw [Fintype.card_of_bijective (HodgeBasic.labelHom_bijective H), Embeddings.card]
  have hint := GlobalTheory.T.eigenspace_decomposition_internal Ω 𝔐.Li E 𝔐.ρ (CMType H ⊕ CMType H) 𝔐.emb hinj hcard
  refine ⟨?_, ⟨IsOpenImmersion.lift Y.jQ g hran, ?_⟩, hchar, hinj, ?_, hint.submodule_iSup_eq_top,
    hint.submodule_iSupIndep, ?_⟩
  · refine HodgeBasic.mem_abLocus_of_map 𝔐.m.cart.1 ?_
    have hf : ∀ w : Sp Ω, pullback.fst Y.s (spMap β) (g w) = 𝔐.f (𝔐.ξ w) := by
      intro w
      rw [← Scheme.Hom.comp_apply, hgf, Scheme.Hom.comp_apply]
    have h2 : g (IsLocalRing.closedPoint Ω) ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]
      exact hran ⟨_, rfl⟩
    exact (congrArg (· ∈ abLocus Y.t.G) (hf (IsLocalRing.closedPoint Ω))).mp h2
  · rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, hgf]
  · intro s
    obtain ⟨U, hU, b, hb, hfr⟩ := 𝔐.vb s ⟨genPt 𝔐.ξ, specializes_rfl⟩ (Set.mem_univ _)
    have hli := (hfr ⟨genPt 𝔐.ξ, specializes_rfl⟩ (Set.mem_univ _) hU).1
    show Module.finrank Ω (eigSp 𝔐.ρ (𝔐.cst.comp (labelEmb c s))) = _
    rw [← hb, finrank_span_eq_card hli, Fintype.card_fin]
  · intro s a q
    refine HodgeBasic.mem_regAt_of_isIntegral 𝔐.tie.gen 𝔐.all 𝔐.normal q ?_
    exact (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (𝔐.emb s).toIntAlgHom

end GlobalTheory.CompanionTheory.Ar
