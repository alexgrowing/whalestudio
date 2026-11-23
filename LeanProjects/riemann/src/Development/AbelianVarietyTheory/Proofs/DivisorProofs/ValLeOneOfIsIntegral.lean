import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAVFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingPadicComplexInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralRuleRuleBaseChangeCoeffFieldIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAlgClosed

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SlopeDesc

open ReciprocityTheory.ChartRestriction.G.Out

section Val

variable {C O : Type} [Field C] [CharZero C] {v : Valuation C ℝ≥0} [CommRing O] [Algebra O C]

theorem exists_cdvr_over (hv : v.Integers O) (T : CDVR) (k : T.Fr →+* C) (kO : T.V →+* O)
    (hk : ∀ a, algebraMap O C (kO a) = k (algebraMap T.V T.Fr a)) {K' : Type} [Field K'] [NumberField K']
    (s : K' →+* C) :
    ∃ (T' : CDVR) (io' : K' →+* T'.Fr) (iT : T.Fr →+* T'.Fr) (e : ℕ) (φ : T.V →+* T'.V) (k' : T'.Fr →+* C)
      (kO' : T'.V →+* O), 0 < e ∧ (∀ a, vV T'.V (iT a) = (e : ℤ) * vV T.V a) ∧ (T.FinRes → T'.FinRes) ∧
      (∀ a, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a)) ∧ (∀ a, k' (iT a) = k a) ∧
      (∀ a, k' (io' a) = s a) ∧ (∀ a, algebraMap O C (kO' a) = k' (algebraMap T'.V T'.Fr a)) := by
  haveI : CharZero T.Fr := algebraRat.charZero _
  letI : Algebra T.Fr C := k.toAlgebra
  haveI : IsScalarTower ℚ T.Fr C := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let b := Module.finBasis ℚ K'
  let L := IntermediateField.adjoin T.Fr (Set.range fun i => s (b i))
  haveI : FiniteDimensional T.Fr L := IntermediateField.finiteDimensional_adjoin (by
    rintro _ ⟨i, rfl⟩
    exact ((Algebra.IsIntegral.isIntegral (R := ℚ) (b i)).map s.toRatAlgHom).tower_top)
  have hs : ∀ x, s x ∈ L := fun x => by
    rw [← b.sum_repr x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [Algebra.smul_def, map_mul, eq_ratCast, map_ratCast]
    exact mul_mem (SubfieldClass.ratCast_mem L _) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  obtain ⟨W, _, _, _, _, _, _, _, hc, hfin, hinj, hloc, -, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension T.V T.Fr L
  haveI : CharZero W := charZero_of_injective_algebraMap hinj
  let T' : CDVR := { V := W }
  let ψ : FractionRing W ≃ₐ[W] L := FractionRing.algEquiv W L
  let iT : T.Fr →+* FractionRing W := ψ.symm.toRingEquiv.toRingHom.comp (algebraMap T.Fr L)
  have hφ : ∀ a, iT (algebraMap T.V T.Fr a) = algebraMap W (FractionRing W) (algebraMap T.V W a) := by
    intro a
    have h1 : algebraMap T.Fr L (algebraMap T.V T.Fr a) = algebraMap W L (algebraMap T.V W a) :=
      (RingHom.congr_fun hc a).symm
    change ψ.symm (algebraMap T.Fr L (algebraMap T.V T.Fr a)) = _
    rw [h1, AlgEquiv.commutes]
  obtain ⟨e, he, hve⟩ := GlobalTheory.PlaceExtField.exists_index (algebraMap T.V W) iT hφ
  let k' : FractionRing W →+* C := L.val.toRingHom.comp ψ.toRingEquiv.toRingHom
  have hk' : ∀ a, k' (iT a) = k a := fun a => congrArg L.val (ψ.apply_symm_apply _)
  let kW : W →+* C := k'.comp (algebraMap W _)
  have hint : ∀ a : W, kW a ∈ (algebraMap O C).range := fun a => by
    obtain ⟨q, hq, hq0⟩ := (Algebra.IsIntegral.isIntegral (R := T.V) a)
    have : IsIntegral O (kW a) := ⟨q.map kO, hq.map _, by
      rw [Polynomial.eval₂_map, show (algebraMap O C).comp kO = kW.comp (algebraMap T.V W) from
        RingHom.ext fun x => (hk x).trans ((hk' _).symm.trans (congrArg k' (hφ x))), ← Polynomial.hom_eval₂, hq0,
        map_zero]⟩
    exact hv.exists_of_le_one (hv.mem_of_integral this)
  let j := RingEquiv.ofBijective (algebraMap O C).rangeRestrict
    ⟨fun a b hab => hv.hom_inj (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩
  refine ⟨T', ψ.symm.toRingEquiv.toRingHom.comp (s.codRestrict L hs), iT, e, algebraMap T.V W, k',
    j.symm.toRingHom.comp (kW.codRestrict _ hint), he, hve, fun h => ?_, fun a => (hφ a).symm, hk',
    fun a => congrArg L.val (ψ.apply_symm_apply _), fun a => congrArg Subtype.val (j.apply_symm_apply ⟨_, hint a⟩)⟩
  haveI : Finite (IsLocalRing.ResidueField T.V) := h
  exact Module.finite_of_finite (IsLocalRing.ResidueField T.V) (M := IsLocalRing.ResidueField W)

variable {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)}

theorem natCast_mem_iff {T : CDVR} {io : K →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e) {q : ℕ} (hq : q ≠ 0) :
    ((q : 𝓞 K) ∈ la.asIdeal ↔ 0 < vV T.V (q : T.Fr)) ∧ (0 < vV T.V (q : T.Fr) → 0 < vLa la (q : K)) := by
  have h1 := ho.2 (q : K)
  rw [map_natCast] at h1
  have he : (0 : ℤ) < e := by exact_mod_cast ho.1
  rw [h1, mul_pos_iff_of_pos_left he]
  refine ⟨?_, id⟩
  have h0 : la.valuation K (q : K) ≠ 0 := by simpa using hq
  have h2 : la.valuation K (q : K) < 1 ↔ (q : 𝓞 K) ∈ la.asIdeal := by
    simpa using la.valuation_lt_one_iff_mem (K := K) (q : 𝓞 K)
  rw [← h2, ← WithZero.log_lt_log h0 one_ne_zero, vLa]
  simp

omit [CharZero C] in

theorem val_vw_nonneg_iff {p : ℕ} (h0 : (p : C) ≠ 0) (h1 : v (p : C) < 1) (hp : 0 < vLa la (p : K)) (x : C) :
    0 ≤ val_vw la p v x ↔ v x ≤ 1 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hx
    have hx' : (1 : ℝ) < v x := by exact_mod_cast not_le.1 hx
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    have hl : Real.log (v (p : C)) < 0 :=
      Real.log_neg (by simpa [pos_iff_ne_zero] using h0) (by exact_mod_cast h1)
    rw [val_vw_of_ne la p v hx0, EReal.coe_nonneg] at h
    exact h.not_gt (mul_neg_of_pos_of_neg (by exact_mod_cast hp) (div_neg_of_pos_of_neg (Real.log_pos hx') hl))
  · rw [← val_vw_of_eq_one la p v v.map_one]
    exact val_vw_anti la h0 h1 (h.trans_eq v.map_one.symm)

omit [CharZero C] [NumberField K] in

theorem val_le_one_of_isIntegral (hv : v.Integers O) (s : K →+* C) {x : K} (hx : IsIntegral ℤ x) : v (s x) ≤ 1 :=
  hv.mem_of_integral (hx.map s.toIntAlgHom).tower_top

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)

theorem pointOver_ext {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
    [Algebra O C] [StarRing (𝓞 E)] {P : Point p v O (𝓞 E)} {V F V' F' : Type} [CommRing V] [Field F] [Algebra V F]
    [CommRing V'] [Field F'] [Algebra V' F'] {x₀ : Sp F ⟶ Xo.X} {k : F →+* C} {kO : V →+* O}
    {ψ : P.A.A.left ⟶ Xo.univ.t.G.left} (h : PointOver P x₀ k kO ψ) (iT : F →+* F') (φ : V →+* V') (k' : F' →+* C)
    (kO' : V' →+* O) (h1 : ∀ a, algebraMap V' F' (φ a) = iT (algebraMap V F a)) (h2 : ∀ a, k' (iT a) = k a)
    (h3 : ∀ a, algebraMap O C (kO' a) = k' (algebraMap V' F' a)) : PointOver P (spMap iT ≫ x₀) k' kO' ψ := by
  obtain ⟨hk, G, t', m₁, m₂, π, φA, a1, a2, a3, a4, a5, a6⟩ := h
  have e0 : spMap kO = spMap kO' ≫ spMap φ := by
    rw [spMap_spMap]
    exact congrArg _ (RingHom.ext fun a => P.integers.hom_inj (by rw [RingHom.comp_apply, h3, h1, h2, hk]))
  have e1 : spMap k = spMap k' ≫ spMap iT := by
    rw [spMap_spMap]
    exact congrArg _ (RingHom.ext fun a => (h2 a).symm)
  have e2 : spMap iT ≫ spMap (algebraMap V F) = spMap (algebraMap V' F') ≫ spMap φ := by
    rw [spMap_spMap, spMap_spMap]
    exact congrArg _ (RingHom.ext fun a => (h1 a).symm)
  have e3 : spMap k' ≫ spMap (algebraMap V' F') = spMap (algebraMap O C) ≫ spMap kO' := by
    rw [spMap_spMap, spMap_spMap]
    exact congrArg _ (RingHom.ext fun a => (h3 a).symm)
  obtain ⟨G', ⟨m⟩⟩ : ∃ G' : SAB H (Sp V'), Nonempty (SABMap G' G (spMap φ)) :=
    ⟨_, ⟨PullbackSections.sabM Out.CubePf.cubePull (spMap φ) G⟩⟩
  obtain ⟨t'', ⟨n⟩⟩ : ∃ t'' : SAB H (Sp F'), Nonempty (SABMap t'' t' (spMap iT)) :=
    ⟨_, ⟨PullbackSections.sabM Out.CubePf.cubePull (spMap iT) t'⟩⟩
  obtain ⟨m₁', b1⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₁ n
  obtain ⟨m₂', b2⟩ : ∃ m₂' : SABMap t'' G (spMap (algebraMap V' F') ≫ spMap φ), m₂'.φ = n.φ ≫ m₂.φ := by
    rw [← e2]
    exact sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₂ n
  obtain ⟨m', b3⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m m₂'
  obtain ⟨π', c1, c2⟩ : ∃ j : P.G.left ⟶ G'.G.left, j ≫ m.φ = π ∧ j ≫ G'.G.hom = P.G.hom ≫ spMap kO' :=
    ⟨m.cart.1.lift _ _ (a1.1.w.trans (by rw [e0, Category.assoc])), m.cart.1.lift_fst _ _ _, m.cart.1.lift_snd _ _ _⟩
  obtain ⟨φ', d1, d2⟩ : ∃ j : P.A.A.left ⟶ t''.G.left, j ≫ n.φ = φA ∧ j ≫ t''.G.hom = P.A.A.hom ≫ spMap k' :=
    ⟨n.cart.1.lift _ _ (a3.1.w.trans (by rw [e1, Category.assoc])), n.cart.1.lift_fst _ _ _, n.cart.1.lift_snd _ _ _⟩
  refine ⟨h3, G', t'', m₁', m', π', φ', m.cart.cancel (a1.congr e0 c1.symm) c2, fun a => m.cart.1.hom_ext ?_ ?_,
    n.cart.cancel (a3.congr e1 d1.symm) d2, m.cart.1.hom_ext ?_ ?_, ?_, a6⟩
  · change (_ ≫ π') ≫ m.φ = (π' ≫ _) ≫ m.φ
    rw [Category.assoc, Category.assoc, c1, a2, ← c1, Category.assoc]
    exact congrArg (π' ≫ ·) (m.act a).symm
  · rw [Category.assoc, Category.assoc, Over.w, c2, Over.w_assoc]
  · change (φ' ≫ m'.φ) ≫ m.φ = (_ ≫ π') ≫ m.φ
    rw [Category.assoc, Category.assoc, c1, ← b3, b2, ← Category.assoc, d1, a4]
  · have w1 : m'.φ ≫ G'.G.hom = _ := m'.cart.1.w
    rw [Category.assoc, Category.assoc, c2, w1, ← Category.assoc, d2, Category.assoc, e3, ← Category.assoc,
      ← Category.assoc, P.gen_pull.1.w]
  · rw [b1, ← Category.assoc, d1, a5]

theorem exists_intFr_ext {C O : Type} [Field C] [CharZero C] {v : Valuation C ℝ≥0} [CommRing O] [Algebra O C]
    (hv : v.Integers O) [Algebra c.F C] [Algebra c'.F C] (hs : AlgOver c c' hle C) {T : CDVR} {io : c.F →+* T.Fr}
    (y₀ : IntFr Xo c T io) (hy : y₀.IsAlg) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C) (kO : T.V →+* O)
    (hk : ∀ a, algebraMap O C (kO a) = k (algebraMap T.V T.Fr a)) {la : HeightOneSpectrum (𝓞 c.F)} {e : ℕ}
    (ho : OverLa la T.V io e) :
    ∃ (T' : CDVR) (io' : c'.F →+* T'.Fr) (y₀' : IntFr Xo c' T' io') (k' : letI := io'.toAlgebra; T'.Fr →ₐ[c'.F] C)
      (kO' : T'.V →+* O) (la' : HeightOneSpectrum (𝓞 c'.F)) (e' : ℕ) (iT : T.Fr →+* T'.Fr) (φ : T.V →+* T'.V),
      y₀'.IsAlg ∧ OverLa la' T'.V io' e' ∧ (∀ q : ℕ, q ≠ 0 → ((q : 𝓞 c'.F) ∈ la'.asIdeal ↔ (q : 𝓞 c.F) ∈ la.asIdeal)) ∧
      (∀ a, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a)) ∧ (∀ a, k' (iT a) = k a) ∧
      (∀ a, algebraMap O C (kO' a) = k' (algebraMap T'.V T'.Fr a)) ∧
      (letI := io.toAlgebra; letI := io'.toAlgebra; y₀'.1.x = spMap iT ≫ y₀.1.x ∧
        ∀ z : FrPt Xo c C, FrMap k y₀.1 z → FrMap k' y₀'.1 (z.ext hle hs)) := by
  letI := io.toAlgebra
  obtain ⟨T', io', iT, e₁, φ, k', kO', he, hve, hfin, h1, h2, h3, h4⟩ :=
    exists_cdvr_over hv T k.toRingHom kO hk (algebraMap c'.F C)
  have hio : ∀ x, io' (incF c c' hle x) = (iT.comp io) x := fun x =>
    k'.injective ((h3 _).trans ((hs x).trans ((k.commutes x).symm.trans (h2 _).symm)))
  obtain ⟨⟨y₁, -, -, ψ, hψ, hm⟩, -⟩ := GlobalTheory.PlaceInt.exists_isExt_and_trans E H Dw l Xo c T T' io y₀ iT e₁ he hve
  letI := (iT.comp io).toAlgebra
  letI := io'.toAlgebra
  let y' : IntFr Xo c' T' io' := ⟨y₁.1.ext hle hio, GlobalTheory.FlagTan.fromTest_of_isLocalRing _,
    (GlobalTheory.IntCoefExt.integral_res_iff hle T' io' (iT.comp io) hio _).2 y₁.2.2⟩
  have hq : ∀ q : ℕ, 0 < vV T'.V (q : T'.Fr) ↔ 0 < vV T.V (q : T.Fr) := fun q => by
    rw [← map_natCast iT, hve, mul_pos_iff_of_pos_left (by exact_mod_cast he)]
  obtain ⟨N, hN, hp⟩ := GlobalTheory.IntCoefExt.exists_nat_pos ho
  obtain ⟨la', e', ho'⟩ := GlobalTheory.IntCoefExt.exists_overLa io' hN ((hq N).2 hp)
  refine ⟨T', io', y', { k' with commutes' := h3 }, kO', la', e', iT, φ, hfin hy, ho', fun q h0 => ?_, h1, h2, h4,
    hm.1.trans (by rw [hψ]), fun z hz => ?_⟩
  · rw [(natCast_mem_iff ho' h0).1, (natCast_mem_iff ho h0).1, hq]
  · let k₀ : T'.Fr →ₐ[c.F] C := { k' with commutes' := fun a => (h2 _).trans (k.commutes a) }
    exact GlobalTheory.SecFieldChange.frMap_ext hle hio hs k₀ _ (fun _ => rfl)
      (GlobalTheory.FlagTan.frMap_of_comp hm hz fun a => (congrArg k' (DFunLike.congr_fun hψ a)).trans (h2 a))

attribute [local instance] algPadicInt algPadicField towerPadic factPadic PadicComplexHost.isAdicComplete

theorem nonneg_of_comb (B : ℝ) {f : Rul Xo c} {f' : Rul Xo c'} (hf : GlobalTheory.CoefChangeCompare.Natural c f)
    (hf' : GlobalTheory.CoefChangeCompare.Natural c' f') {β : c'.F} (hβ : IsIntegral ℤ β)
    (hrel : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω], ∃ (n : ℕ) (s : Fin n → (c'.F →+* Ω))
      (hs : ∀ k a, s k (incF c c' hle a) = algebraMap c.F Ω a),
      ∀ y : FrPt Xo c Ω, evR Xo c f y = ∑ k, s k β * evAlong hle (s k) (hs k) f' y)
    (h' : ∀ la, ∀ w ∈ (mixVals Xo c' B).1 la, 0 ≤ w f') : ∀ la, ∀ w ∈ (mixVals Xo c B).1 la, 0 ≤ w f := by
  intro la w hw
  have fin : ∀ (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]] (y : FrPt Xo c ℂ_[p]),
      (∀ (s : c'.F →+* ℂ_[p]) (hs : ∀ a, s (incF c c' hle a) = algebraMap c.F ℂ_[p] a),
        (Valued.v : Valuation ℂ_[p] ℝ≥0) (evAlong hle s hs f' y) ≤ 1) →
      0 ≤ val_vw la p (Valued.v : Valuation ℂ_[p] ℝ≥0) (evR Xo c f y) := by
    intro p hp _ y hy
    have hv := PadicComplexInt.integers p
    obtain ⟨n, s, hs, h⟩ := hrel ℂ_[p]
    rw [← val_vw_of_eq_one la p (Valued.v : Valuation ℂ_[p] ℝ≥0) (map_one _)]
    refine val_vw_anti la (Nat.cast_ne_zero.2 hp.out.ne_zero) (lt_one_of_not_isUnit hv Fact.out) ?_
    rw [map_one, h]
    refine Valuation.map_sum_le _ fun k _ => ?_
    rw [map_mul]
    exact mul_le_one' (val_le_one_of_isIntegral hv (s k) hβ) (hy _ _)
  have pos : ∀ (p : ℕ) [Fact p.Prime] {T' : CDVR} {io' : c'.F →+* T'.Fr} {la' : HeightOneSpectrum (𝓞 c'.F)} {e' : ℕ},
      OverLa la' T'.V io' e' → (T'.V →+* 𝓞_ℂ_[p]) → ∀ x : ℂ_[p],
      0 ≤ val_vw la' p (Valued.v : Valuation ℂ_[p] ℝ≥0) x → (Valued.v : Valuation ℂ_[p] ℝ≥0) x ≤ 1 := by
    intro p hp T' io' la' e' ho' kO' x
    refine (val_vw_nonneg_iff (Nat.cast_ne_zero.2 hp.out.ne_zero)
      (lt_one_of_not_isUnit (PadicComplexInt.integers p) Fact.out) ((natCast_mem_iff ho' hp.out.ne_zero).2 ?_) x).1
    rw [← map_natCast (algebraMap T'.V T'.Fr)]
    exact GlobalTheory.PlaceExtField.vV_pos (Nat.cast_ne_zero.2 hp.out.ne_zero) fun h =>
      (factPadic p).out (by simpa using h.map kO')
  by_cases hS : ∃ p ∈ htPrimes l B, ((p : ℕ) : 𝓞 c.F) ∈ la.asIdeal
  · obtain ⟨q, hq, hq'⟩ := hS
    rw [mixVals_of_mem hq hq'] at hw
    obtain ⟨p, hp, _, T, io, e, y₀, k, y, ho, hy, hH, rfl⟩ := hw
    refine fin p y fun s hs => ?_
    letI := s.toAlgebra
    letI := H.starRing
    letI := io.toAlgebra
    obtain ⟨-, kO, P, ψ, z, hP, hz, g, a, x, c1, c2, c3, c4, c5⟩ := hH
    obtain ⟨T', io', y₀', k', kO', la', e', iT, φ, b1, b2, b3, b4, b5, b6, b7, b8⟩ :=
      exists_intFr_ext hle P.integers hs y₀ hy k kO hP.1 ho
    letI := io'.toAlgebra
    have hl : ∀ τ, htLat c' P τ = htLat c P τ := fun τ => by
      have : embAt c' ℂ_[p] τ = embAt c ℂ_[p] τ := RingHom.ext fun a => hs (embF c τ a)
      unfold htLat embInt
      rw [this]
    have hH' : IsHTFrameCp p y₀' k' (y.ext hle hs) :=
      ⟨GlobalTheory.FlagTan.fromTest_of_isLocalRing _, kO', P, ψ, z.ext hle hs,
        b7 ▸ pointOver_ext hP iT φ k'.toRingHom kO' b4 b5 b6, b8 z hz, g, a, x, c1, c2, c3, c4,
        fun τ => (hl τ).symm ▸ c5 τ⟩
    refine pos p b2 kO' _ (h' la' (fun g => val_vw la' p (Valued.v : Valuation ℂ_[p] ℝ≥0) (evR Xo c' g (y.ext hle hs))) ?_)
    rw [mixVals_of_mem hq ((b3 q hq.1.ne_zero).2 hq')]
    exact ⟨p, hp, _, T', io', e', y₀', k', _, b2, b1, hH', rfl⟩
  · have hw' : w ∈ valSet Xo c (algCls Xo c) la := by
      have e : (mixVals Xo c B).1 la = valSet Xo c (algCls Xo c) la := if_neg hS
      exact e ▸ hw
    obtain ⟨⟨_, T, io, e, ho, y₀, hy, et, het, rfl⟩, rfl⟩ := hw'
    obtain ⟨p, hp, k₀, kO, hk⟩ := GlobalTheory.CompleteDvrEmbedding.exists_embedding_padicComplexInt T hy
    letI := io.toAlgebra
    letI : Algebra c.F ℂ_[p] := (k₀.comp io).toAlgebra
    let k : T.Fr →ₐ[c.F] ℂ_[p] := { k₀ with commutes' := fun _ => rfl }
    have hv := PadicComplexInt.integers p
    have h0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
    obtain ⟨z, hz⟩ := GlobalTheory.FlagTan.exists_frMap k y₀.1
    show 0 ≤ nval T.V e (evR Xo c f y₀.1)
    rw [← val_vw_map la hv h0 (factPadic p).out ho k₀ kO hk]
    refine (fin p z fun s hs => ?_).trans_eq (congrArg _ (GlobalTheory.FlagTan.evR_frMap hf hz))
    letI := s.toAlgebra
    obtain ⟨T', io', y₀', k', kO', la', e', iT, φ, b1, b2, b3, b4, b5, b6, b7, b8⟩ :=
      exists_intFr_ext hle hv hs y₀ hy k kO hk ho
    letI := io'.toAlgebra
    refine pos p b2 kO' _ ?_
    have e1 : evAlong hle s hs f' z = k'.toRingHom (evR Xo c' f' y₀'.1) := GlobalTheory.FlagTan.evR_frMap hf' (b8 z hz)
    rw [e1, val_vw_map la' hv h0 (factPadic p).out b2 k'.toRingHom kO' b6]
    refine h' la' (fun g => nval T'.V e' (evI y₀' g)) ?_
    have e2 : (mixVals Xo c' B).1 la' = valSet Xo c' (algCls Xo c') la' :=
      if_neg fun ⟨q, hq, hq'⟩ => hS ⟨q, hq, (b3 q hq.1.ne_zero).1 hq'⟩
    rw [e2]
    exact ⟨PtV.mk la' b2 y₀' b1 () trivial, rfl⟩

end GlobalTheory.SlopeDesc
