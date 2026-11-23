import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimitiveRootHodgeCpt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionIntegrallyClosed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTwistOfLowers
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompEqIdOfTwists
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

section pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem qmk_eq_iff {N : ℕ} (n : ℕ) (x x' : Fin N → 𝓞 E) :
    qmk n x = qmk n x' ↔ ∃ z : Fin N → 𝓞 E, x = x' + n • z := by
  constructor
  · intro h
    have h' : ∀ i, ∃ w : 𝓞 E, x i - x' i = (n : 𝓞 E) * w := by
      intro i
      have h1 := congrFun (Multiplicative.ofAdd.injective h) i
      have h2 := Ideal.Quotient.eq.1 h1
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 h2
      exact ⟨w, hw⟩
    choose z hz using h'
    refine ⟨z, funext fun i => ?_⟩
    have := hz i
    show x i = x' i + n • z i
    rw [nsmul_eq_mul, ← this]; ring
  · rintro ⟨z, rfl⟩
    refine congrArg Multiplicative.ofAdd (funext fun i => ?_)
    refine Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 ⟨z i, ?_⟩)
    simp [nsmul_eq_mul]

theorem qmk_surjective {N : ℕ} (n : ℕ) (t : TorsT E N n) : ∃ x : Fin N → 𝓞 E, qmk n x = t := by
  have h : ∀ i, ∃ a : 𝓞 E, Ideal.Quotient.mk _ a = Multiplicative.toAdd t i := fun i => Ideal.Quotient.mk_surjective _
  choose x hx using h
  exact ⟨x, congrArg Multiplicative.ofAdd (funext hx)⟩

theorem qmk_add {N : ℕ} (n : ℕ) (x x' : Fin N → 𝓞 E) : qmk n (x + x') = qmk n x * qmk n x' := by
  refine congrArg Multiplicative.ofAdd (funext fun i => ?_)
  exact map_add (Ideal.Quotient.mk _) (x i) (x' i)

theorem exists_genPts (𝔐 : HodgeCpt Y S y) (n : ℕ) (T : (Fin (D.p + D.q) → 𝓞 E) → (Over.mk 𝔐.ξ ⟶ 𝔐.t.G))
    (hadd : ∀ x x', T (x + x') = T x * T x') (hlin : ∀ (a : 𝓞 E) x, T (a • x) = T x ≫ 𝔐.t.act.act a)
    (hker : ∀ x, T x = 1 ↔ ∃ z, x = n • z) (honto : ∀ g, g ^ n = 1 ↔ ∃ x, T x = g) :
    ∃ P : GenPts 𝔐 n, ∀ x, P.pt (qmk n x) = T x := by
  classical
  have hsub : ∀ x x', T (x - x') = 1 → T x = T x' := by
    intro x x' h
    have := hadd (x - x') x'
    rw [sub_add_cancel, h, _root_.one_mul] at this
    exact this
  have hdep : ∀ x x', qmk n x = qmk n x' → T x = T x' := by
    intro x x' h
    obtain ⟨z, hz⟩ := (qmk_eq_iff n x x').1 h
    refine hsub _ _ ((hker _).2 ⟨z, ?_⟩)
    rw [hz, add_sub_cancel_left]
  choose s hs using qmk_surjective (E := E) (N := D.p + D.q) n
  have hpt : ∀ x, T (s (qmk n x)) = T x := fun x => hdep _ _ (hs _)
  let pt : TorsT E (D.p + D.q) n →* (Over.mk 𝔐.ξ ⟶ 𝔐.t.G) := MonoidHom.mk' (fun t => T (s t)) (by
    intro a b
    obtain ⟨x, rfl⟩ := qmk_surjective n a
    obtain ⟨x', rfl⟩ := qmk_surjective n b
    rw [← qmk_add, hpt, hpt, hpt, hadd])
  have hptq : ∀ x, pt (qmk n x) = T x := hpt
  refine ⟨⟨pt, ?_, ?_, ?_⟩, hptq⟩
  · refine (injective_iff_map_eq_one pt).2 fun t ht => ?_
    obtain ⟨x, rfl⟩ := qmk_surjective n t
    rw [hptq] at ht
    obtain ⟨z, hz⟩ := (hker x).1 ht
    have h0 : qmk n x = qmk n (0 : Fin (D.p + D.q) → 𝓞 E) := (qmk_eq_iff n _ _).2 ⟨z, by rw [zero_add]; exact hz⟩
    rw [h0]
    exact congrArg Multiplicative.ofAdd (funext fun i => by simp)
  · intro g
    rw [honto]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨qmk n x, hptq x⟩
    · rintro ⟨t, rfl⟩
      obtain ⟨x, rfl⟩ := qmk_surjective n t
      exact ⟨x, (hptq x).symm⟩
  · intro a x
    rw [hptq, hptq, hlin]

end pts

section gen

open scoped TensorProduct

theorem isIntegral_tensor_of_ne {O Ω₀ F : Type} [CommRing O] [Field Ω₀] [Field F] [Algebra O Ω₀] [Algebra O F]
    (hF : ∀ u : F, ∃ a : O, algebraMap O Ω₀ a ≠ 0 ∧ _root_.IsIntegral O (a • u)) :
    Algebra.IsIntegral Ω₀ (Ω₀ ⊗[O] F) := by
  have h1 : ∀ u : F, _root_.IsIntegral Ω₀ ((1 : Ω₀) ⊗ₜ[O] u) := by
    intro u
    obtain ⟨a, ha', hi⟩ := hF u
    have h2 : _root_.IsIntegral O ((1 : Ω₀) ⊗ₜ[O] (a • u)) :=
      hi.map (Algebra.TensorProduct.includeRight : F →ₐ[O] Ω₀ ⊗[O] F)
    have h3 : _root_.IsIntegral Ω₀ ((1 : Ω₀) ⊗ₜ[O] (a • u)) := h2.tower_top
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

theorem exists_integral_multiple_of_ker {O Ω₀ : Type} [CommRing O] [Field Ω₀] {F : IntermediateField ℚ ℂ}
    [FiniteDimensional ℚ F] (β : O →+* F) (g₀ : O →+* Ω₀) (hk : ∀ a, g₀ a = 0 → β a = 0) (u : F) :
    letI := β.toAlgebra
    ∃ a : O, g₀ a ≠ 0 ∧ _root_.IsIntegral O (a • u) := by
  letI := β.toAlgebra
  have hQ : IsAlgebraic ℚ u := Algebra.IsAlgebraic.isAlgebraic u
  have hZ : IsAlgebraic ℤ u := (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 hQ
  obtain ⟨n, hn, hi⟩ := hZ.exists_integral_multiple
  refine ⟨(n : O), fun h => hn ?_, ?_⟩
  · have h1 := hk _ h
    rw [map_intCast] at h1
    exact_mod_cast h1
  · have e : (n : O) • u = n • u := by
      rw [Algebra.smul_def, zsmul_eq_mul]
      congr 1
      exact map_intCast β n
    rw [e]
    exact hi.tower_top

theorem eq_of_specializes_of_fst_of_ne {X : Scheme.{0}} {O F Ω₀ : Type} [CommRing O] [Field F] [Field Ω₀] (s : X ⟶ Sp O)
    (β : O →+* F) (g₀ : O →+* Ω₀) (ξ₀ : Sp Ω₀ ⟶ X) (h₀ : IsCptGen ξ₀) (hs : ξ₀ ≫ s = spMap g₀)
    (hF : letI := β.toAlgebra; ∀ u : F, ∃ a : O, g₀ a ≠ 0 ∧ _root_.IsIntegral O (a • u))
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
  have hint : Algebra.IsIntegral Ω₀ (Ω₀ ⊗[O] F) := isIntegral_tensor_of_ne hF
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

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem mem_range_jQ_of_ker (Y : Model Xo c β) {Ω₀ : Type} [Field Ω₀] (ξ₀ : Sp Ω₀ ⟶ Y.X) (h₀ : IsCptGen ξ₀)
    (g₀ : O₀ →+* Ω₀) (hs : ξ₀ ≫ Y.s = spMap g₀) (hk : ∀ a, g₀ a = 0 → β a = 0) (z : ↥(pullback Y.s (spMap β)))
    (hz : pullback.fst Y.s (spMap β) z = genPt ξ₀) : z ∈ Set.range Y.jQ := by
  have := HodgeBasic.noetherianSpace_pullback Y.proj β
  have := Y.jQ_open
  have := c.fin
  exact HodgeBasic.mem_of_dense_of_maximal Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense fun y' h' =>
    eq_of_specializes_of_fst_of_ne Y.s β g₀ ξ₀ h₀ hs (exists_integral_multiple_of_ker β g₀ hk) hz h'

theorem exists_point_of_hodgeCpt (𝔐 : HodgeCpt Y S y) : ∃ x : Sp Ω ⟶ Xo.XF c, 𝔐.ξ ≫ 𝔐.f = x ≫ Y.j := by
  have hcst : Function.Injective 𝔐.cst := 𝔐.cst.injective
  let g₀ : O₀ →+* 𝔐.Ω₀ := (Spec.preimage (𝔐.ξ₀ ≫ Y.s)).hom
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
  have hk : ∀ a, g₀ a = 0 → β a = 0 := by
    intro a ha
    apply hcst
    have := RingHom.congr_fun hcomp a
    simp only [RingHom.comp_apply, ha, map_zero] at this
    rw [map_zero]; exact this.symm
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
    exact mem_range_jQ_of_ker Y 𝔐.ξ₀ 𝔐.gen₀ g₀ hs hk _ (hall w)
  have := Y.jQ_open
  refine ⟨IsOpenImmersion.lift Y.jQ g hran, ?_⟩
  rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, hgf]

end gen

section main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem nsmul_vec_cancel {N m : ℕ} (hm : 0 < m) {x x' : Fin N → 𝓞 E} (h : m • x = m • x') : x = x' := by
  funext i
  have h1 : m • x i = m • x' i := congrFun h i
  rw [nsmul_eq_mul, nsmul_eq_mul] at h1
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hm.ne') h1

theorem nonempty_genTors_of_data (𝔐 : HodgeCpt Y S y) (p : ℕ) (hp : 0 < p) (hR : 1 ≤ 𝔐.R p) (ζ : Ωˣ)
    (hζ : IsPrimitiveRoot ζ (p ^ 𝔐.R p))
    (ew : (Over.mk 𝔐.ξ ⟶ 𝔐.t.G) → (Over.mk 𝔐.ξ ⟶ 𝔐.t.G) → Ωˣ)
    (hew : GenWeil 𝔐.t.G 𝔐.t.PP.L 𝔐.ξ (p ^ 𝔐.R p) ew)
    (τ : (Fin (D.p + D.q) → 𝓞 E) → (Over.mk 𝔐.ξ ⟶ 𝔐.t.G))
    (e : (Fin (D.p + D.q) → 𝓞 E) →+ (Fin (D.p + D.q) → 𝓞 E) →+ ZMod (p ^ 𝔐.R p))
    (h1 : ∀ x x', τ (x + x') = τ x * τ x') (h2 : ∀ (a : 𝓞 E) x, τ (a • x) = τ x ≫ 𝔐.t.act.act a)
    (h3 : ∀ g, g ^ (p ^ 𝔐.R p) = 1 ↔ ∃ x, τ x = g) (h4 : ∀ x x', ew (τ x) (τ x') = ζ ^ (e x x').val)
    (h5 : ∀ x, e x x = 0) (h6 : ∀ (a : 𝓞 E) x x', e (a • x) x' = e x (H.bar a • x'))
    (h7 : ∀ φ : (Fin (D.p + D.q) → 𝓞 E) →+ ZMod (p ^ 𝔐.R p), ∃ x, e x = φ)
    (h8 : ∀ x, e x = 0 → ∃ x', x = (p ^ 𝔐.R p) • x') : Nonempty (GenTors 𝔐 p) := by
  have hN0 : 0 < p ^ 𝔐.R p := pow_pos hp _
  haveI : NeZero (p ^ 𝔐.R p) := ⟨hN0.ne'⟩
  have hm0 : 0 < p ^ (𝔐.R p - 1) := pow_pos hp _
  have hpow : p ^ (𝔐.R p - 1) * p = p ^ 𝔐.R p := by
    rw [← pow_succ]; congr 1; omega
  have hτ0 : τ 0 = 1 := by
    have h := h1 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  have hτn : ∀ (m : ℕ) x, τ (m • x) = τ x ^ m := by
    intro m x
    induction m with
    | zero => rw [zero_smul, pow_zero, hτ0]
    | succ m ih => rw [succ_nsmul, h1, ih, pow_succ]
  have hew1 : ∀ g, g ^ (p ^ 𝔐.R p) = 1 → ew 1 g = 1 := by
    intro g hg
    have h := hew.mul_left 1 1 g (one_pow _) (one_pow _) hg
    rw [_root_.mul_one] at h
    exact mul_eq_left.1 h.symm
  have hker : ∀ x, τ x = 1 ↔ ∃ z, x = (p ^ 𝔐.R p) • z := by
    intro x
    constructor
    · intro hx
      apply h8
      refine AddMonoidHom.ext fun x' => ?_
      have ht : (τ x') ^ (p ^ 𝔐.R p) = 1 := (h3 _).2 ⟨x', rfl⟩
      have h := h4 x x'
      rw [hx, hew1 _ ht] at h
      have hd : p ^ 𝔐.R p ∣ (e x x').val := (hζ.pow_eq_one_iff_dvd _).1 h.symm
      exact (ZMod.val_eq_zero _).1 (Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt _))
    · rintro ⟨z, rfl⟩
      rw [hτn]
      exact (h3 _).2 ⟨z, rfl⟩
  obtain ⟨P₂, hP₂⟩ := exists_genPts 𝔐 _ τ h1 h2 hker h3
  obtain ⟨P₁, hP₁⟩ := exists_genPts 𝔐 p (fun x => τ (p ^ (𝔐.R p - 1) • x))
    (fun x x' => by simp only [smul_add, h1])
    (fun a x => by
      show τ (p ^ (𝔐.R p - 1) • a • x) = τ (p ^ (𝔐.R p - 1) • x) ≫ 𝔐.t.act.act a
      rw [smul_comm, h2])
    (fun x => by
      rw [hker]
      constructor
      · rintro ⟨z, hz⟩
        refine ⟨z, nsmul_vec_cancel hm0 ?_⟩
        rw [hz, ← hpow, mul_smul]
      · rintro ⟨z, rfl⟩
        exact ⟨z, by rw [← hpow, mul_smul]⟩)
    (fun g => by
      constructor
      · intro hg
        have hg' : g ^ (p ^ 𝔐.R p) = 1 := by
          rw [← hpow, mul_comm, pow_mul, hg, one_pow]
        obtain ⟨x₀, rfl⟩ := (h3 g).1 hg'
        rw [← hτn] at hg
        obtain ⟨z, hz⟩ := (hker _).1 hg
        refine ⟨z, ?_⟩
        have hx : x₀ = p ^ (𝔐.R p - 1) • z := nsmul_vec_cancel hp (by
          rw [hz, ← hpow, mul_comm, mul_smul])
        rw [hx]
      · rintro ⟨x, rfl⟩
        rw [← hτn, smul_smul, mul_comm, hpow, hτn]
        exact (h3 _).2 ⟨x, rfl⟩)
  have hζΩ : IsPrimitiveRoot (ζ : Ω) (p ^ 𝔐.R p) := hζ.map_of_injective (f := Units.coeHom Ω) Units.val_injective
  refine ⟨{ t₁ := P₁, t₂ := P₂, compat := fun x => ?_, ζ := ζ, ζ_prim := hζΩ, e := e, alt := h5, adj := h6,
            e_surj := h7, e_inj := h8, weil := ?_ }⟩
  · rw [hP₂, hP₁]
  · intro x x' k _ _ i g g' u hg hg'
    have tx : τ x ^ (p ^ 𝔐.R p) = 1 := (h3 _).2 ⟨x, rfl⟩
    have tx' : τ x' ^ (p ^ 𝔐.R p) = 1 := (h3 _).2 ⟨x', rfl⟩
    have hw := hew.weil (τ x) (τ x') tx tx' k i g g' u (by rw [hg, hP₂]) (by rw [hg', hP₂])
    rw [h4, Units.val_pow_eq_pow_val] at hw
    simpa only [Nat.cast_pow] using hw

theorem nonempty_genTors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → Nonempty (GenTors 𝔐 p) := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d _ hpq p _ hpS _ _ _
  have hchar : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  obtain ⟨y₀, hξ⟩ := exists_point_of_hodgeCpt 𝔐
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hN0 : 0 < p ^ 𝔐.R p := pow_pos hp0 _
  have hR : 1 ≤ 𝔐.R p := le_trans (by norm_num) (𝔐.R_ge p hpS)
  have hFT0 : FullTorsion Y.t.G (y₀ ≫ Y.j) (p ^ 𝔐.R p) :=
    HF.fullTorsion_push Y.t 𝔐.t 𝔐.f 𝔐.m 𝔐.ξ _ hξ.symm _ (𝔐.tors p hpS)
  obtain ⟨o', ⟨pm⟩⟩ := GlobalTheory.LevelGroup.pull_univ Y.oF y₀
  obtain ⟨n, -⟩ := GlobalTheory.Moduli.LevelAction.exists_comp_sabMap pm.toSABMap Y.m (h := y₀ ≫ Y.j) rfl
  obtain ⟨ζ₀, hζ₀⟩ := OmLink.root o' Y.t n hFT0 hN0 hpq
  have hne : ζ₀ ≠ 0 := hζ₀.ne_zero hN0.ne'
  let ζ : Ωˣ := Units.mk0 ζ₀ hne
  have hζ : IsPrimitiveRoot ζ (p ^ 𝔐.R p) := IsPrimitiveRoot.coe_units_iff.1 hζ₀
  obtain ⟨e₀, he₀⟩ := WeilObj.genWeil_of_obj GlobalTheory.CompanionTheory.Ar.Link.weilSt E H D l (KA l) (baseKA l) (Xo.XF c) Y.X _ Y.oF Y.t Y.j
    Y.m Ω y₀ (p ^ 𝔐.R p) hN0 hFT0 ⟨ζ₀, hζ₀⟩
  obtain ⟨ew, hew⟩ := HF.genWeil_move Y.t 𝔐.t 𝔐.f 𝔐.m 𝔐.ξ (y₀ ≫ Y.j) hξ.symm _ e₀ he₀
  let iK : Ω →+* AlgebraicClosure Ω := algebraMap Ω (AlgebraicClosure Ω)
  have hI : Nonempty (XR.TateIsoAt D 𝔐.t (spMap iK ≫ 𝔐.ξ)) := by
    let s₀ := pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s
    let β₀ : KA l →+* Ω := (Spec.preimage (y₀ ≫ s₀)).hom
    have h1 : spMap β₀ = y₀ ≫ s₀ := by
      simp only [β₀, spMap, CommRingCat.ofHom_hom, Spec.map_preimage]
    have hβ : (spMap iK ≫ y₀) ≫ s₀ = spMap (iK.comp β₀) := by
      rw [Category.assoc, WeilObj.spMap_comp_of, h1]
    obtain ⟨-, I₀, -, -, -⟩ := Y.oF.geom (AlgebraicClosure Ω) (spMap iK ≫ y₀) (iK.comp β₀) hβ
    obtain ⟨I₁, -, -⟩ := (XR.tateIsoAt_move E H D Y.X (Xo.XF c) Y.t Y.oF.t Y.j Y.m (AlgebraicClosure Ω)
      (spMap iK ≫ y₀) (spMap iK ≫ y₀ ≫ Y.j) (Category.assoc _ _ _).symm).2 I₀
    obtain ⟨I, -, -⟩ := (XR.tateIsoAt_move E H D Y.X 𝔐.X Y.t 𝔐.t 𝔐.f 𝔐.m (AlgebraicClosure Ω)
      (spMap iK ≫ 𝔐.ξ) (spMap iK ≫ y₀ ≫ Y.j) (by rw [Category.assoc, hξ])).1 I₁
    exact ⟨I⟩
  obtain ⟨I⟩ := hI
  obtain ⟨τ, e, h1, h2, h3, h4, h5, h6, h7, h8⟩ := HF.torsion_of_tate H D 𝔐.t 𝔐.ξ _ hN0 ζ hζ (AlgebraicClosure Ω) iK I
    (𝔐.tors p hpS) ew hew
  refine nonempty_genTors_of_data 𝔐 p hp0 hR ζ hζ ew hew τ e h1 h2 h3 h4 h5 (fun a x x' => ?_) h7 h8
  have hbar : RingOfIntegers.mapRingEquiv (HT.cmConj E) a = H.bar a := by
    ext
    rw [H.bar_eq]
    rfl
  rw [h6, hbar]

end main

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
