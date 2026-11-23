import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAVFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSubextensionPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDvrExtension
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.RootFrame
open scoped NNReal
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

private theorem ext_proper {X B : Scheme.{0}} (f : X ⟶ B) (hp : IsProper f) {V : Type} [CommRing V] [IsDomain V]
    [ValuationRing V] (y : Sp (FractionRing V) ⟶ X) (s : Sp V ⟶ B)
    (h : y ≫ f = spMap (algebraMap V (FractionRing V)) ≫ s) :
    ∃ χ : Sp V ⟶ X, y = spMap (algebraMap V (FractionRing V)) ≫ χ := by
  have hv : ValuativeCriterion f := by
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  let S : ValuativeCommSq f := { R := V, K := FractionRing V, i₁ := y, i₂ := s, commSq := ⟨h⟩ }
  obtain ⟨U⟩ := hv S
  exact ⟨U.default.l, U.default.fac_left.symm⟩

private theorem alg_map {K R C : Type} [Field K] [Field R] [CharZero R] [Field C] [Algebra R C] (k : K →+* C) (a : K)
    (h : IsAlgebraic ℤ a) : IsAlgebraic R (k a) :=
  (h.algHom k.toIntAlgHom).extendScalars (S := R) Int.cast_injective

private theorem int_map {A R C : Type} [CommRing A] [CommRing R] [CommRing C] [Algebra R C] (k : A →+* C) (a : A)
    (h : IsIntegral ℤ a) : IsIntegral R (k a) :=
  (h.map k.toIntAlgHom).tower_top

private theorem norm_le_one_of_isIntegral (p : ℕ) [Fact p.Prime] (x : ℂ_[p]) (h1 : IsIntegral 𝓞_ℂ_[p] x) :
    ‖x‖ ≤ 1 := by
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
  have h2 : Valued.v (y : ℂ_[p]) ≤ 1 := y.2
  rw [← GlobalTheory.FlatModel.coe_valued]
  exact NNReal.coe_le_one.mpr h2

private theorem descend_gen (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) (s : X ⟶ Sp (𝓞 F)) (hs : IsProper s)
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (k : K →+* ℂ_[p]) (z : Sp K ⟶ X) (hK : ∀ a : K, IsAlgebraic ℤ a) :
    ∃ (T : CDVR) (kO : T.V →+* 𝓞_ℂ_[p]) (yT : Sp T.V ⟶ X), T.FinRes ∧ Function.Injective kO ∧
      spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ spMap kO ≫ yT = spMap k ≫ z := by
  let T : CDVR := { V := ℤ_[p] }
  have hfin : T.FinRes := Finite.of_equiv _ (PadicInt.residueField (p := p)).symm.toEquiv
  let g : ℤ_[p] →+* ℂ_[p] := (algebraMap ℚ_[p] ℂ_[p]).comp (algebraMap ℤ_[p] ℚ_[p])
  have hg : Function.Injective g := (algebraMap ℚ_[p] ℂ_[p]).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])
  have hgO : ∀ a, g a ∈ 𝓞_ℂ_[p] := fun a => by
    show Valued.v (g a) ≤ 1
    rw [← NNReal.coe_le_one, GlobalTheory.FlatModel.coe_valued]
    show ‖algebraMap ℚ_[p] ℂ_[p] (a : ℚ_[p])‖ ≤ 1
    rw [norm_algebraMap']
    exact a.2
  let kO : T.V →+* 𝓞_ℂ_[p] := g.codRestrict (𝓞_ℂ_[p]) hgO
  let kk : T.Fr →+* ℂ_[p] := IsFractionRing.lift (K := FractionRing ℤ_[p]) hg
  have hk : ∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = kk (algebraMap T.V T.Fr a) := fun a =>
    (IsFractionRing.lift_algebraMap (K := FractionRing ℤ_[p]) hg a).symm
  letI algT : Algebra T.Fr ℂ_[p] := kk.toAlgebra
  let K' : IntermediateField T.Fr ℂ_[p] := algebraicClosure T.Fr ℂ_[p]
  have hKa : Algebra.IsAlgebraic T.Fr K' := algebraicClosure.isAlgebraic T.Fr ℂ_[p]
  haveI : CharZero T.Fr := RingHom.charZero kk
  have hkK : ∀ a, k a ∈ K' := fun a => by
    rw [mem_algebraicClosure_iff]
    exact alg_map k a (hK a)
  let k' : K →+* K' := k.codRestrict K' hkK
  have hft : LocallyOfFiniteType (s ≫ spMap (algebraMap ℤ (𝓞 F))) := by
    have : LocallyOfFiniteType (spMap (algebraMap ℤ (𝓞 F))) := by
      unfold spMap
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      exact RingHom.finiteType_algebraMap.mpr inferInstance
    infer_instance
  obtain ⟨L, yL, hLfin, hyL1, -⟩ := GlobalTheory.FinDesc.exists_finite_subext_point _ _ _ hft T.Fr K' hKa (spMap k' ≫ z)
    (spMap (algebraMap ℤ T.Fr)) (specZIsTerminal.hom_ext _ _)
  obtain ⟨kL, hkL⟩ : ∃ kL : L →+* ℂ_[p], kL = K'.val.toRingHom.comp L.val.toRingHom := ⟨_, rfl⟩
  have hkL1 : ∀ x : L, kL x = ((x : K') : ℂ_[p]) := fun x => by rw [hkL]; rfl
  obtain ⟨T', i, iF, ψ, kO', hT'fin, hkO'inj, hi, hψ, hkO', hint⟩ :=
    GlobalTheory.CdvrLiftCp.exists_cdvr_lift p T hfin kO kk hk L kL (fun a => by rw [hkL1]; rfl)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (yL ≫ s : Sp L ⟶ Sp (𝓞 F))
  obtain ⟨fL, hfLφ⟩ : ∃ fL : 𝓞 F →+* L, fL = φ.hom := ⟨_, rfl⟩
  have hφ' : yL ≫ s = spMap fL := by rw [← hφ, hfLφ]; rfl
  obtain ⟨β', hβ'⟩ := hint (𝓞 F) fL (fun a => norm_le_one_of_isIntegral p _
    (int_map (kL.comp fL) a (RingOfIntegers.isIntegral a)))
  have hring : ψ.toRingHom.comp fL = (algebraMap T'.V T'.Fr).comp β' := RingHom.ext fun a => (hβ' a).symm
  have hsq : (spMap ψ.toRingHom ≫ yL) ≫ s = spMap (algebraMap T'.V (FractionRing T'.V)) ≫ spMap β' := by
    rw [Category.assoc, hφ', spMap_spMap, spMap_spMap, hring]
  obtain ⟨yT, hyT⟩ := ext_proper s hs (spMap ψ.toRingHom ≫ yL) (spMap β') hsq
  refine ⟨T', kO', yT, hT'fin, hkO'inj, ?_⟩
  have hrk : (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO' = (kL.comp ψ.symm.toRingHom).comp (algebraMap T'.V T'.Fr) :=
    RingHom.ext hkO'
  have e1 : (kL.comp ψ.symm.toRingHom).comp ψ.toRingHom = K'.val.toRingHom.comp (algebraMap L K') :=
    RingHom.ext fun x => by
      show kL (ψ.symm (ψ x)) = _
      rw [RingEquiv.symm_apply_apply, hkL1]; rfl
  have e2 : K'.val.toRingHom.comp k' = k := RingHom.ext fun _ => rfl
  rw [← Category.assoc, spMap_spMap, hrk, ← spMap_spMap, Category.assoc, ← hyT, ← Category.assoc, spMap_spMap, e1,
    ← spMap_spMap, Category.assoc, hyL1, ← Category.assoc, spMap_spMap, e2]

private theorem descend (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) (s : X ⟶ Sp (𝓞 F)) (hs : IsProper s)
    (p : ℕ) [Fact p.Prime] (yb : Sp 𝓞_ℂ_[p] ⟶ X) (K : Type) [Field K] (k : K →+* ℂ_[p]) (z : Sp K ⟶ X)
    (hK : ∀ a : K, IsAlgebraic ℤ a) (hz : spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb = spMap k ≫ z) :
    ∃ (T : CDVR) (kO : T.V →+* 𝓞_ℂ_[p]) (yT : Sp T.V ⟶ X), T.FinRes ∧ Function.Injective kO ∧
      spMap kO ≫ yT = yb := by
  obtain ⟨T, kO, yT, h1, h2, h3⟩ := descend_gen F X s hs p K k z hK
  refine ⟨T, kO, yT, h1, h2, ?_⟩
  have hiO : Function.Injective (algebraMap 𝓞_ℂ_[p] ℂ_[p]) := (PadicComplexInt.integers p).hom_inj
  haveI : X.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from s]
    infer_instance⟩
  haveI : IsDominant (spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p])) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap 𝓞_ℂ_[p] ℂ_[p])).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 hiO]; exact bot_le)⟩
  exact ext_of_isDominant (spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p])) (h3.trans hz.symm)

private theorem point_of_sab {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [hpO : Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
    (hv : v.Integers O) (T : CDVR) (hy : T.FinRes) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr))
    (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr))) (x : Sp T.Fr ⟶ Xo.X) (m₁ : SABMap t' Xo.univ.t x)
    (k : T.Fr →+* C) (kO : T.V →+* O) (hk : ∀ a, algebraMap O C (kO a) = k (algebraMap T.V T.Fr a)) :
    letI := H.starRing
    ∃ (P : Point p v O (𝓞 E)) (π : P.G.left ⟶ G.G.left) (φ : P.A.A.left ⟶ t'.G.left),
      IsGrpPullback P.G G.G (spMap kO) π ∧ (∀ a, (P.oG.act a).left ≫ π = π ≫ (G.act.act a).left) ∧
      IsGrpPullback P.A.A t'.G (spMap k) φ ∧ φ ≫ m₂.φ = P.gen ≫ π ∧
      LBIso P.A.L (Xo.univ.t.PP.L.pull (φ ≫ m₁.φ)) := by
  letI := H.starRing
  haveI : IsDomain O := hv.hom_inj.isDomain _
  haveI : ValuationRing O := ValuationRing.of_integers _ hv
  have hinj : Function.Injective ((algebraMap O C).comp kO) := fun a b h => by
    simp only [RingHom.comp_apply, hk] at h
    exact IsFractionRing.injective T.V T.Fr (k.injective h)
  have hp0 : ∀ {R : Type} [CommRing R] (f : R →+* O), (p : R) ≠ 0 := fun f h =>
    (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero : (p : C) ≠ 0) (by
      rw [← map_natCast ((algebraMap O C).comp f), h, map_zero])
  have hpu : ∀ {R : Type} [CommRing R] (f : R →+* O), ¬ IsUnit (p : R) := fun f h =>
    hpO.out (by simpa using h.map f)
  haveI : IsLocalHom kO := ⟨fun a ha => by
    by_contra hau
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact not_isUnit_zero ha
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
    have hn : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, _root_.mul_one] at hu
      exact hau (hu ▸ u.isUnit)
    rw [hu, map_mul, map_pow] at ha
    have h1 : IsUnit (kO ϖ) := (isUnit_pow_iff hn).1 (isUnit_of_mul_isUnit_right ha)
    obtain ⟨n', u', hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hp0 kO) hϖ
    refine hpO.out ?_
    rw [← map_natCast kO, hu', map_mul, map_pow]
    exact (u'.isUnit.map kO).mul (h1.pow _)⟩
  obtain ⟨T', φ', G', m, hi, hf, -, -, U, -⟩ :=
    GlobalTheory.UnifAfterExt.exists_finite_ext_uniformised E H Dw l Xo T G t' m₂ _ m₁ hy
  obtain ⟨f', -, hf'⟩ := GlobalTheory.CharDepth.exists_local_extension_of_integral v hv φ' hi hf.to_isIntegral kO hinj
  have hI : ∃ n : ℕ, ∀ a ∈ IsLocalRing.maximalIdeal T'.V ^ n, f' a ∈ Ideal.span {(p : O)} := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T'.V
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hp0 f') hϖ
    refine ⟨n, fun a ha => ?_⟩
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    refine Ideal.mem_span_singleton'.2 ⟨f' (b * ↑u⁻¹), ?_⟩
    rw [← map_natCast f', ← map_mul, hu, _root_.mul_assoc, Units.inv_mul_cancel_left]
  obtain ⟨A, oA, φ, hφ, hφa, hL⟩ :=
    exists_polAV_fibre m₁ Xo.univ.proper Xo.univ.ample Xo.univ.ktriv (spMap k)
  have e1 : spMap f' ≫ spMap φ' = spMap kO := by rw [spMap_spMap, hf']
  have e2 : spMap k ≫ spMap (algebraMap T.V T.Fr) = spMap ((algebraMap O C).comp f') ≫ spMap φ' := by
    rw [spMap_spMap, spMap_spMap, RingHom.comp_assoc, hf']
    exact congrArg _ (RingHom.ext fun a => (hk a).symm)
  have h2 : IsGrpPullback A.A G.G (spMap ((algebraMap O C).comp f') ≫ spMap φ') (φ ≫ m₂.φ) :=
    (hφ.comp m₂.cart).congr e2 rfl
  obtain ⟨j, hj1, hj2⟩ : ∃ j : A.A.left ⟶ G'.G.left, j ≫ m.φ = φ ≫ m₂.φ ∧
      j ≫ G'.G.hom = A.A.hom ≫ spMap ((algebraMap O C).comp f') :=
    ⟨m.cart.1.lift _ _ (h2.1.w.trans (Category.assoc _ _ _).symm), m.cart.1.lift_fst _ _ _, m.cart.1.lift_snd _ _ _⟩
  have hj : IsGrpPullback A.A G'.G (spMap ((algebraMap O C).comp f')) j :=
    m.cart.cancel (h2.congr rfl hj1.symm) hj2
  have hja : ∀ a, (oA.act a).left ≫ j = j ≫ (G'.act.toRingAct.act a).left := fun a => m.cart.1.hom_ext
    (by
      change _ = (j ≫ (G'.act.act a).left) ≫ _
      rw [Category.assoc, Category.assoc, m.act, hj1, reassoc_of% hj1, reassoc_of% (hφa a), m₂.act])
    (by rw [Category.assoc, Category.assoc, Over.w, hj2, Over.w_assoc])
  obtain ⟨ε⟩ : Nonempty (Eps p C) := inferInstance
  obtain ⟨-, -, -, -, -, P, -, -, -, -, hA, -, -, -, -, π, -, hπ, -, -, -, hgen, hπa, -⟩ :=
    exists_point_of_unif U.U.toUnifPre G'.semi U.lin hv ε f' hI A oA j hj hja
  clear hja hφa hj
  clear oA
  subst hA
  refine ⟨P, π ≫ m.φ, φ, (hπ.comp m.cart).congr e1 rfl, fun a => ?_, hφ, ?_, hL⟩
  · rw [← Category.assoc, hπa, Category.assoc, Category.assoc]
    exact congrArg (π ≫ ·) (m.act a)
  · rw [← Category.assoc, eq_of_heq hgen, hj1]

private theorem lift_gen {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) {K C : Type} [Field K] [Field C] (k : K →+* C)
    (x : Sp K ⟶ Z.X) (yy : Sp C ⟶ Xo.XF c) (h : spMap k ≫ x = yy ≫ Z.j) :
    ∃ y : Sp K ⟶ Xo.XF c, y ≫ Z.j = x ∧ spMap k ≫ y = yy := by
  have h' : spMap k ≫ x = yy ≫ Z.jQ ≫ Limits.pullback.fst _ _ := h
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 c.F →+* K, x ≫ Z.s = spMap b :=
    ⟨(Spec.preimage (x ≫ Z.s)).hom, (Spec.map_preimage (x ≫ Z.s)).symm⟩
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : c.F →+* C, yy ≫ Z.jQ ≫ Limits.pullback.snd _ _ = spMap g₀ :=
    ⟨(Spec.preimage (yy ≫ Z.jQ ≫ Limits.pullback.snd _ _)).hom, (Spec.map_preimage _).symm⟩
  have e0 : k.comp b = g₀.comp (algebraMap (𝓞 c.F) c.F) := by
    have e : spMap (k.comp b) = spMap (g₀.comp (algebraMap (𝓞 c.F) c.F)) := by
      rw [← spMap_spMap, ← spMap_spMap, ← hb, ← hg₀, reassoc_of% h', Limits.pullback.condition]
      simp only [Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  have hbi : Function.Injective b := by
    have : Function.Injective (k.comp b) := by
      rw [e0]
      exact g₀.injective.comp (IsFractionRing.injective (𝓞 c.F) c.F)
    exact Function.Injective.of_comp (f := k) this
  let g : c.F →+* K := IsFractionRing.lift hbi
  have hg : g.comp (algebraMap (𝓞 c.F) c.F) = b := RingHom.ext fun a => IsFractionRing.lift_algebraMap hbi a
  have hkg : k.comp g = g₀ :=
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) (by rw [RingHom.comp_assoc, hg, e0])
  have hw : x ≫ Z.s = spMap g ≫ spMap (algebraMap (𝓞 c.F) c.F) := by rw [spMap_spMap, hg, hb]
  let yK : Sp K ⟶ Limits.pullback Z.s (spMap (algebraMap (𝓞 c.F) c.F)) := Limits.pullback.lift x (spMap g) hw
  have hyK : spMap k ≫ yK = yy ≫ Z.jQ := by
    refine Limits.pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Limits.pullback.lift_fst, h', Category.assoc]
    · rw [Category.assoc, Limits.pullback.lift_snd, Category.assoc, hg₀, spMap_spMap, hkg]
  have hr : Set.range yK ⊆ Set.range Z.jQ := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨q0⟩ : Nonempty (Sp C) := inferInstance
    have hq : q = spMap k q0 := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [hq, ← Scheme.Hom.comp_apply, hyK, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  haveI := Z.jQ_open
  have hy' : IsOpenImmersion.lift Z.jQ yK hr ≫ Z.jQ = yK := IsOpenImmersion.lift_fac _ _ _
  refine ⟨IsOpenImmersion.lift Z.jQ yK hr, ?_, ?_⟩
  · show _ ≫ Z.jQ ≫ Limits.pullback.fst _ _ = _
    rw [← Category.assoc, hy', Limits.pullback.lift_fst]
  · rw [← cancel_mono Z.jQ, Category.assoc, hy', hyK]

theorem UpperTheory.algebraic_p_adic_point_lifts :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (p : ℕ) [Fact p.Prime] (yb : Sp 𝓞_ℂ_[p] ⟶ Z.X) (yy : Sp ℂ_[p] ⟶ Xo.XF c), spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb = yy ≫ Z.j → AlgDef (spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb) → letI := H.starRing; ∃ (P : PtP E p) (π : P.G.left ⟶ Z.t.G.left) (ψ : P.A.A.left ⟶ Z.oF.t.G.left), PtOnG Z yb yy P π ψ := by
  intro E _ _ _ H Dw l Xo c Z p _ yb yy hyy halg
  letI := H.starRing
  obtain ⟨K, _, k₀, z, hK, hz⟩ := halg
  obtain ⟨T, kO, yT, hfin, hkO, hyT⟩ := descend c.F Z.X Z.s (projProper _ _ _ Z.proj) p yb K k₀ z hK hz
  have hiO : Function.Injective (algebraMap 𝓞_ℂ_[p] ℂ_[p]) := (PadicComplexInt.integers p).hom_inj
  have hinj : Function.Injective ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO) := hiO.comp hkO
  let k : T.Fr →+* ℂ_[p] := IsFractionRing.lift hinj
  have hk : ∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = k (algebraMap T.V T.Fr a) := fun a =>
    (IsFractionRing.lift_algebraMap hinj a).symm
  have hOO : (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO = k.comp (algebraMap T.V T.Fr) := RingHom.ext hk
  obtain ⟨y, hy1, hy2⟩ := lift_gen Z k (spMap (algebraMap T.V T.Fr) ≫ yT) yy (by
    rw [← hyy, ← hyT, sp_sp, sp_sp, hOO])
  have tr : ∀ {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {f g : S' ⟶ S}, f = g →
      ∀ m : SABMap s' s f, ∃ m' : SABMap s' s g, m'.φ = m.φ := by
    intro S S' s s' f g h m
    subst h
    exact ⟨m, rfl⟩
  obtain ⟨G, ⟨b⟩⟩ := exists_sab yT Z.t
  obtain ⟨t', ⟨q⟩⟩ := exists_sab y Z.oF.t
  obtain ⟨m₁, hm₁⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Z.m0.toSABMap q
  obtain ⟨e₂, he₂⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Z.m q
  obtain ⟨e₂', he₂'⟩ := tr (show y ≫ Z.jQ ≫ Limits.pullback.fst _ _ = spMap (algebraMap T.V T.Fr) ≫ yT from hy1) e₂
  obtain ⟨m₂, hm₂⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ b e₂'
  obtain ⟨P, π, φ, hπ, hπa, hφ, hgen, hL⟩ := point_of_sab Xo p ℂ_[p] (Valued.v : Valuation ℂ_[p] ℝ≥0) 𝓞_ℂ_[p]
    (PadicComplexInt.integers p) T hfin G t' m₂ _ m₁ k kO hk
  refine ⟨P, π ≫ b.φ, φ ≫ q.φ, hyy, (hπ.comp b.cart).congr hyT rfl, fun a => ?_, (hφ.comp q.cart).congr hy2 rfl, ?_, ?_⟩
  · rw [← Category.assoc, hπa, Category.assoc, Category.assoc]
    exact congrArg (π ≫ ·) (b.act a)
  · rw [Category.assoc, ← he₂, ← he₂', hm₂, reassoc_of% hgen]
  · exact LBIso.trans P.A.isLB (pull_isLB Xo.univ.t.PP.isLB _) (pull_isLB Z.oF.t.PP.isLB _) hL
      (GlobalTheory.LN.GenericPoint.lbIso_pull (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap Z.m0.toSABMap) _
        (by rw [hm₁, Category.assoc])).symm
