import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreimmersionFst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelDomainOverInclusion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointModelOverDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisMapCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingSectionCompatibility
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrOverHeightOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PropertyOfCodimOneLocalUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnitOfDvrUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthBasisChangeInvariaStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TanLinOfCombLinear
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IntegralOfFrChg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMulExpandAlt

set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel

noncomputable section

namespace GlobalTheory.FlatDenom

theorem exists_dvd_sum {V ι : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Fintype ι] (d a : ι → V)
    (h : ∑ i, a i * d i ≠ 0) : ∃ i, d i ∣ ∑ i, a i * d i := by
  classical
  have hne : (Finset.univ : Finset ι).Nonempty := by
    by_contra h0
    rw [Finset.not_nonempty_iff_eq_empty] at h0
    exact h (by rw [h0, Finset.sum_empty])
  have key : ∀ s : Finset ι, s.Nonempty → ∃ i, ∀ j ∈ s, d i ∣ d j := by
    intro s hs
    induction hs using Finset.Nonempty.cons_induction with
    | singleton a => exact ⟨a, fun j hj => by rw [Finset.mem_singleton.1 hj]⟩
    | cons a s ha hs ih =>
      obtain ⟨i, hi⟩ := ih
      rcases ValuationRing.dvd_total (d i) (d a) with h1 | h1
      · exact ⟨i, fun j hj => (Finset.mem_cons.1 hj).elim (fun e => e ▸ h1) (hi j)⟩
      · exact ⟨a, fun j hj => (Finset.mem_cons.1 hj).elim (fun e => e ▸ dvd_rfl) fun hj => h1.trans (hi j hj)⟩
  obtain ⟨i, hi⟩ := key _ hne
  exact ⟨i, Finset.dvd_sum fun j hj => Dvd.dvd.mul_left (hi j hj) _⟩

theorem det_mul_eq_sum {V : Type} [CommRing V] {m g : ℕ} (M : Matrix (Fin m) (Fin g) V) (C : Matrix (Fin g) (Fin m) V) :
    (M * C).det = ∑ J : Fin m → Fin g, (∏ i, M i (J i)) * (C.submatrix J id).det := by
  first
  | exact @_root_.GlobalTheory.DeterminantExpansion.det_mul_expand
  | exact _root_.GlobalTheory.DeterminantExpansion.det_mul_expand
  | (apply _root_.GlobalTheory.DeterminantExpansion.det_mul_expand <;> assumption)
  | (intros; apply _root_.GlobalTheory.DeterminantExpansion.det_mul_expand <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DeterminantExpansion.det_mul_expand <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DeterminantExpansion.det_mul_expand ..)

theorem exists_minor_dvd : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (m g : ℕ) (M : Matrix (Fin m) (Fin g) V) (C : Matrix (Fin g) (Fin m) V) (δ : V), δ ≠ 0 → M * C = δ • (1 : Matrix (Fin m) (Fin m) V) → (∃ I : Fin m → Fin g, (M.submatrix id I).det ∣ δ ^ m) ∧ ∃ J : Fin m → Fin g, (C.submatrix J id).det ∣ δ ^ m := by
  intro V _ _ _ m g M C δ hδ h
  have hd : (M * C).det = δ ^ m := by rw [h, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
  have h0 : δ ^ m ≠ 0 := pow_ne_zero _ hδ
  constructor
  · have e := det_mul_eq_sum C.transpose M.transpose
    rw [← Matrix.transpose_mul, Matrix.det_transpose, hd] at e
    obtain ⟨I, hI⟩ := exists_dvd_sum _ _ (e ▸ h0)
    refine ⟨I, ?_⟩
    rw [← e] at hI
    rwa [← Matrix.det_transpose]
  · have e := det_mul_eq_sum M C
    rw [hd] at e
    obtain ⟨J, hJ⟩ := exists_dvd_sum _ _ (e ▸ h0)
    exact ⟨J, e ▸ hJ⟩

open GlobalTheory.HartogsUnit in

theorem exists_nat_mul_mem : ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A] [CharZero A] (a : FractionRing A), (∀ (T : CDVR) (α : A →+* T.V) (ι : FractionRing A →+* T.Fr), Function.Injective α → (∀ x, ι (algebraMap A (FractionRing A) x) = algebraMap T.V T.Fr (α x)) → (∀ n : ℕ, 0 < n → IsUnit (n : T.V)) → ι a ∈ (algebraMap T.V T.Fr).range) → ∃ (m : ℕ) (b : A), 0 < m ∧ algebraMap A (FractionRing A) b = (m : FractionRing A) * a := by
  intro A _ _ _ _ _ a h
  classical
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := A) a
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyK : algebraMap A (FractionRing A) y ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A _)).2 hy0

  have hmem : ∀ (p : Ideal A) [p.IsPrime] (n : ℕ), algebraMap A (Localization.AtPrime p) y ∣
      algebraMap A (Localization.AtPrime p) (n * x) → ∃ w, toFrac p w =
        (n : FractionRing A) * (algebraMap A (FractionRing A) x / algebraMap A (FractionRing A) y) := by
    rintro p _ n ⟨w, hw⟩
    refine ⟨w, ?_⟩
    have := congrArg (toFrac p) hw
    rw [map_mul (toFrac p), ← RingHom.comp_apply, ← RingHom.comp_apply, toFrac_comp, map_mul, map_natCast] at this
    rw [← mul_div_assoc, this, mul_div_cancel_left₀ _ hyK]
  have key : ∀ p : PrimeSpectrum A, p.asIdeal.height = 1 → ∃ n : ℕ, 0 < n ∧
      algebraMap A (Localization.AtPrime p.asIdeal) y ∣ algebraMap A (Localization.AtPrime p.asIdeal) (n * x) := by
    intro p hp
    let L := Localization.AtPrime p.asIdeal
    haveI : IsDomain L := IsLocalization.isDomain_localization p.asIdeal.primeCompl_le_nonZeroDivisors
    haveI : IsDiscreteValuationRing L := isDiscreteValuationRing_of_height_eq_one p.asIdeal hp _
    have hinj : Function.Injective (algebraMap A L) :=
      IsLocalization.injective L p.asIdeal.primeCompl_le_nonZeroDivisors
    have hyL : algebraMap A L y ≠ 0 := (map_ne_zero_iff _ hinj).2 hy0
    by_cases hn : ∃ n : ℕ, 0 < n ∧ ¬ IsUnit (n : L)
    · obtain ⟨n, hn0, hn⟩ := hn
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible L
      obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hyL hϖ
      have hd : ϖ ∣ (n : L) := by
        rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
        exact hn
      refine ⟨n ^ k, pow_pos hn0 k, ?_⟩
      rw [hu, map_mul, map_natCast, Nat.cast_pow, Units.mul_left_dvd]
      exact (pow_dvd_pow_of_dvd hd k).mul_right _
    · push_neg at hn
      obtain ⟨T, iT, h1, h2⟩ := GlobalTheory.HeightOneCompletion.exists_cdvr_of_height_eq_one A p hp
      have hα : Function.Injective (iT.comp (algebraMap A L)) := h1.comp hinj
      have hα' : Function.Injective ((algebraMap T.V T.Fr).comp (iT.comp (algebraMap A L))) :=
        (IsFractionRing.injective T.V T.Fr).comp hα
      obtain ⟨s, hs⟩ := h T _ (IsFractionRing.lift hα') hα (fun x => IsFractionRing.lift_algebraMap hα' x)
        fun n hn0 => by simpa using (hn n hn0).map iT
      rw [map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap,
        eq_div_iff ((map_ne_zero_iff _ hα').2 hy0)] at hs
      have hs' : s * iT (algebraMap A L y) = iT (algebraMap A L x) :=
        IsFractionRing.injective T.V T.Fr (by rw [map_mul]; exact hs)
      refine ⟨1, one_pos, ?_⟩
      rw [Nat.cast_one, one_mul]
      rcases ValuationRing.dvd_total (algebraMap A L y) (algebraMap A L x) with h3 | ⟨c, hc⟩
      · exact h3
      · have h4 : iT (algebraMap A L y) * (s * iT c) = iT (algebraMap A L y) * 1 := by
          rw [mul_one, ← mul_assoc, mul_comm _ s, hs', ← map_mul, ← hc]
        have h5 := mul_left_cancel₀ ((map_ne_zero_iff _ h1).2 hyL) h4
        have h6 : IsUnit c := (isUnit_map_iff iT c).1 (IsUnit.of_mul_eq_one_right _ h5)
        rw [hc]
        exact h6.mul_right_dvd.2 dvd_rfl
  choose! n hn0 hn using key
  have hfin : {p : PrimeSpectrum A | p.asIdeal.height = 1 ∧ y ∈ p.asIdeal}.Finite := by
    refine Set.Finite.of_finite_image (f := PrimeSpectrum.asIdeal)
      ((Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {y})).subset ?_)
      fun _ _ _ _ h => PrimeSpectrum.ext h
    rintro _ ⟨p, ⟨hp, hyp⟩, rfl⟩
    refine ⟨⟨p.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hyp⟩, fun q ⟨hq, hyq⟩ hqp => ?_⟩
    by_contra hne
    have hlt : q < p.asIdeal := lt_of_le_of_ne hqp fun e => hne e.ge
    have hq0 : (⊥ : Ideal A) < q := bot_lt_iff_ne_bot.2 fun e => hy0 (by
      have := hyq (Ideal.mem_span_singleton_self y); rwa [e, Ideal.mem_bot] at this)
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hq0
    rw [hp] at h1
    rw [Ideal.height_bot, zero_add] at h2
    have h3 : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left h2 1).trans h1
    exact absurd h3 (by decide)
  refine ⟨∏ p ∈ hfin.toFinset, n p, ?_⟩
  have hm : ((∏ p ∈ hfin.toFinset, n p : ℕ) : FractionRing A) *
      (algebraMap A (FractionRing A) x / algebraMap A (FractionRing A) y) ∈ (algebraMap A (FractionRing A)).range := by
    refine (GlobalTheory.mem_range_algebraMap_iff_forall_height_eq_one (A := A) _).mpr fun p _ hp => ?_
    obtain ⟨w, hw⟩ := hmem p (∏ p ∈ hfin.toFinset, n p) (by
      by_cases hyp : y ∈ p
      · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (hfin.mem_toFinset.2 ⟨hp, hyp⟩ : (⟨p, inferInstance⟩ : PrimeSpectrum A) ∈ _)
        rw [hk, Nat.cast_mul, mul_right_comm, map_mul]
        exact (hn ⟨p, inferInstance⟩ hp).mul_right _
      · exact (IsLocalization.map_units (Localization.AtPrime p) (⟨y, hyp⟩ : p.primeCompl)).dvd)
    rw [GlobalTheory.mem_primeLocalSubalgebra_iff, ← hw]
    exact toFrac_mem p w
  obtain ⟨b, hb⟩ := hm
  exact ⟨b, Finset.prod_pos fun p hp => hn0 p (hfin.mem_toFinset.1 hp).1, hb⟩

section Tan

open MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)}

theorem exists_comb (hv : ∀ i, IsTanAtG t x (v i)) (a : Fin m → S) : ∃ w, IsCombAtG t x v a w :=
  ⟨_, (GlobalTheory.LieMet.isComb_iff (fun i => GlobalTheory.LieMet.tanOf (hv i)) a _).2 rfl⟩

theorem tan_of_comb (hv : ∀ i, IsTanAtG t x (v i)) {a : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x v a w) : IsTanAtG t x w := by
  rw [GlobalTheory.FlatModel.Proj.eq_of_comb (fun i => GlobalTheory.LieMet.tanOf (hv i)) h]
  exact GlobalTheory.LieMet.isTan_tv _

theorem eig_of_comb (hv : ∀ i, IsTanAtG t x (v i)) {s : 𝓞 E →+* S} (he : ∀ i, IsEigG t s (v i)) {a : Fin m → S}
    {w : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x v a w) : IsEigG t s w := by
  rw [GlobalTheory.FlatModel.Proj.eq_of_comb (fun i => GlobalTheory.LieMet.tanOf (hv i)) h]
  intro b
  have h1 : ∀ i, actR t.act b (GlobalTheory.LieMet.tanOf (hv i)) = s b • GlobalTheory.LieMet.tanOf (hv i) := fun i => by
    rw [← GlobalTheory.ShFam.Pad.Pull.eig_iff]
    exact he i b
  rw [GlobalTheory.ShFam.Pad.Pull.eig_iff]
  simp only [map_sum, map_smul, h1, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem isEigG_push {X' : Scheme.{0}} {t' : SAB H X'} {f : X' ⟶ X} (ν : SABMap t' t f) {x' : Sp S ⟶ X'}
    {w : Sp (DualNumber S) ⟶ t'.G.left} (hw : w ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x')
    (s : 𝓞 E →+* S) : IsEigG t' s w ↔ IsEigG t s (w ≫ ν.φ) := by
  refine ⟨fun h a => ?_, fun h a => ?_⟩
  · rw [Category.assoc, ← ν.act, ← Category.assoc, h a, Category.assoc]
  · apply ν.cart.1.hom_ext
    · rw [Category.assoc, ν.act, ← Category.assoc, h a, Category.assoc]
    · rw [Category.assoc, Over.w, Category.assoc, hw, ← Category.assoc, GlobalTheory.LocM.BaseMdl.epsMul_comp]

theorem comb_vecMul (hv : ∀ i, IsTanAtG t x (v i)) {n : ℕ} {q : Fin n → (Sp (DualNumber S) ⟶ t.G.left)}
    {M : Matrix (Fin n) (Fin m) S} (hM : ∀ i, IsCombAtG t x v (M i) (q i)) {a : Fin n → S}
    {w : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x q a w) : IsCombAtG t x v (Matrix.vecMul a M) w := by
  rw [← Matrix.mulVec_transpose]
  exact GlobalTheory.TangentLinear.isCombAtG_mulVec v hv q M.transpose a w hM h

end Tan

open GlobalTheory.LocM.BaseMdl in
set_option maxHeartbeats 1000000 in

theorem exists_change {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) {R : Type} [CommRing R] {ξ : Sp R ⟶ Y.X} {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ Y.t.G.left)} (he : IsTanBasis Y.t ξ e) {σ : E →+* ℂ}
    {U : Matrix (Fin g) (Fin g) R} {L : Type} [CommRing L] [Algebra c.F L] {φ : R →+* L} {y : FrPt Xo c L}
    {M : Matrix (Fin (Dw.mult σ)) (Fin g) L} {C : Matrix (Fin g) (Fin (Dw.mult σ)) L}
    (h : IsFrameCoord Y ξ e U φ y σ M C) {k : Type} [Field k] [Algebra c.F k] {ι : L →ₐ[c.F] k} {y' z : FrPt Xo c k}
    (hm : FrMap ι y y') (hzy : z.x = y'.x) (hz : GlobalTheory.AllWt.ptF z ≫ Y.j = spMap (ι.toRingHom.comp φ) ≫ ξ)
    {M' : Matrix (Fin (Dw.mult σ)) (Fin g) k} {C' : Matrix (Fin g) (Fin (Dw.mult σ)) k}
    (h' : IsFrameCoord Y ξ e U (ι.toRingHom.comp φ) z σ M' C') :
    ∃ a : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) k, (∀ i, IsCombAt y'.x (y'.u σ) (a i) (z.u σ i)) ∧
      M' = a * M.map ι ∧ C' * a = C.map ι := by
  have hx : GlobalTheory.AllWt.ptF z ≫ pullback.fst _ _ = y'.x := (pullback.lift_fst _ _ _).trans hzy
  have hz' : GlobalTheory.AllWt.ptF z ≫ Y.jQ ≫ pullback.fst _ _ = spMap (ι.toRingHom.comp φ) ≫ ξ := hz
  have hpt : GlobalTheory.AllWt.ptF z = spMap ι.toRingHom ≫ GlobalTheory.AllWt.ptF y := by
    apply pullback.hom_ext
    · rw [hx, hm.1, Category.assoc, GlobalTheory.AllWt.ptF, pullback.lift_fst]
    · rw [Category.assoc, GlobalTheory.AllWt.ptF, GlobalTheory.AllWt.ptF, pullback.lift_snd, pullback.lift_snd]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact ι.comp_algebraMap.symm
  choose a ha using fun i => (y'.basis σ (z.u σ i) (hzy ▸ z.tan σ i) (z.eig σ i)).exists
  choose w hw1 hw2 hw3 using h.1
  choose w' hw1' hw2' hw3' using h'.1
  have hbt := (isTanBasis_bc he (ι.toRingHom.comp φ)).1
  have hq2 : ∀ j, (spMap (dualMap ι.toRingHom) ≫ w j) ≫ Y.oF.t.G.hom =
      spMap (algebraMap k (DualNumber k)) ≫ GlobalTheory.AllWt.ptF z := fun j => by
    rw [Category.assoc, hw1, hpt, ← Category.assoc, ← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hq1 : (fun j => (spMap (dualMap ι.toRingHom) ≫ w j) ≫ Y.m0.toSABMap.φ) = y'.u σ := funext fun j => by
    rw [Category.assoc, hw2, hm.2.1]
  have hq3 : ∀ j, IsCombAtG Y.t (spMap (ι.toRingHom.comp φ) ≫ ξ) (bcV Y.t (ι.toRingHom.comp φ) e) (M.map ι j)
      ((spMap (dualMap ι.toRingHom) ≫ w j) ≫ Y.m.φ) := fun j => by
    have := GlobalTheory.LocM.Cht.FlagBase.isCombAtG_bc Y.t ι.toRingHom (hw3 j)
    rw [sp_sp] at this
    rw [← bcV_bcV, Category.assoc]
    exact this
  have hM : M' = Matrix.of a * M.map ι := by
    ext1 i
    refine funext_iff.1 ?_
    have h1 : IsCombAtG Y.oF.t (GlobalTheory.AllWt.ptF z) (fun j => spMap (dualMap ι.toRingHom) ≫ w j) (a i) (w' i) :=
      (comb_push Y.m0.toSABMap hq2 (a i) (hw1' i)).2 (by rw [hq1, hw2', hx]; exact ha i)
    have h2 := comb_vecMul hbt hq3 (hz' ▸ (comb_push Y.m hq2 (a i) (hw1' i)).1 h1)
    exact (he.2 k _ _ (tan_of_comb hbt h2)).unique (hw3' i) h2
  refine ⟨Matrix.of a, ha, hM, ?_⟩
  haveI : CharZero k := charZero_of_injective_algebraMap (algebraMap c.F k).injective
  have hδ : ((discr E : ℤ) : k) ≠ 0 := Int.cast_ne_zero.2 (discr_ne_zero E)
  have e1 : C.map ι * M.map ι = U.map (ι.toRingHom.comp φ) := by
    rw [← Matrix.map_mul (f := ι), h.2.1, Matrix.map_map]; rfl
  have e2 : M.map ι * C.map ι = ((discr E : ℤ) : k) • 1 := by
    rw [← Matrix.map_mul (f := ι), h.2.2]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have e3 : C' * Matrix.of a * M.map ι = C.map ι * M.map ι := by rw [Matrix.mul_assoc, ← hM, h'.2.1, e1]
  have e4 := congrArg (· * C.map ι) e3
  simp only [Matrix.mul_assoc (C' * Matrix.of a), Matrix.mul_assoc (C.map ι), e2, Matrix.mul_smul, Matrix.mul_one] at e4
  exact smul_right_injective _ hδ e4

theorem value_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (R : Type) [CommRing R] (ξ : Sp R ⟶ Y.X) (g : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ Y.t.G.left)), IsTanBasis Y.t ξ e → ∀ (Z : Comp Xo c) (f : Rul Xo c) (σ₁ σ₂ : E →+* ℂ), DetLaw Z f σ₁ σ₂ → ∀ (U₁ U₂ : Matrix (Fin g) (Fin g) R) (L : Type) [CommRing L] [IsLocalRing L] [Algebra c.F L] (φ : R →+* L) (y : FrPt Xo c L), GlobalTheory.AllWt.ptF y ≫ Y.j = spMap φ ≫ ξ → LiesOn Z y → ∀ (M₁ : Matrix (Fin (Dw.mult σ₁)) (Fin g) L) (C₁ : Matrix (Fin g) (Fin (Dw.mult σ₁)) L) (M₂ : Matrix (Fin (Dw.mult σ₂)) (Fin g) L) (C₂ : Matrix (Fin g) (Fin (Dw.mult σ₂)) L), IsFrameCoord Y ξ e U₁ φ y σ₁ M₁ C₁ → IsFrameCoord Y ξ e U₂ φ y σ₂ M₂ C₂ → ∀ (k : Type) [Field k] [Algebra c.F k] (ι : L →ₐ[c.F] k) (ψ : R →+* k), (∀ a, ψ a = ι (φ a)) → ∀ z : FrPt Xo c k, GlobalTheory.AllWt.ptF z ≫ Y.j = spMap ψ ≫ ξ → ∀ (M₁' : Matrix (Fin (Dw.mult σ₁)) (Fin g) k) (C₁' : Matrix (Fin g) (Fin (Dw.mult σ₁)) k) (M₂' : Matrix (Fin (Dw.mult σ₂)) (Fin g) k) (C₂' : Matrix (Fin g) (Fin (Dw.mult σ₂)) k), IsFrameCoord Y ξ e U₁ ψ z σ₁ M₁' C₁' → IsFrameCoord Y ξ e U₂ ψ z σ₂ M₂' C₂' → ∀ (I : Fin (Dw.mult σ₁) → Fin g) (J : Fin (Dw.mult σ₂) → Fin g), evR Xo c f z * (M₁'.submatrix id I).det * (C₂'.submatrix J id).det = ι (evR Xo c f y * (M₁.submatrix id I).det * (C₂.submatrix J id).det) := by
  intro E _ _ _ H Dw l Xo c Y R _ ξ g e he Z f σ₁ σ₂ hL U₁ U₂ L _ _ _ φ y hy hyZ M₁ C₁ M₂ C₂ h₁ h₂ k _ _ ι ψ hψ z hz
    M₁' C₁' M₂' C₂' h₁' h₂' I J
  obtain rfl : ψ = ι.toRingHom.comp φ := RingHom.ext hψ
  obtain ⟨y', hm⟩ := GlobalTheory.FlagTan.exists_frMap ι y
  have := isPreimmersion_j Y
  have hpt : GlobalTheory.AllWt.ptF y' = spMap ι.toRingHom ≫ GlobalTheory.AllWt.ptF y := by
    apply pullback.hom_ext
    · rw [Category.assoc, GlobalTheory.AllWt.ptF, GlobalTheory.AllWt.ptF, pullback.lift_fst, pullback.lift_fst, hm.1]
    · rw [Category.assoc, GlobalTheory.AllWt.ptF, GlobalTheory.AllWt.ptF, pullback.lift_snd, pullback.lift_snd]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact ι.comp_algebraMap.symm
  have hzy0 : GlobalTheory.AllWt.ptF z = GlobalTheory.AllWt.ptF y' := by
    rw [← cancel_mono Y.j, hz, hpt, Category.assoc, hy, sp_sp]
  have hzy : z.x = y'.x := by
    have := congrArg (· ≫ pullback.fst _ _) hzy0
    simpa only [GlobalTheory.AllWt.ptF, pullback.lift_fst] using this
  have hy'Z : LiesOn Z y' := fun s => by
    rw [hpt, Scheme.Hom.comp_apply]
    exact hyZ _
  obtain ⟨a₁, ha₁, hM₁, -⟩ := exists_change Y he h₁ hm hzy hz h₁'
  obtain ⟨a₂, ha₂, -, hC₂⟩ := exists_change Y he h₂ hm hzy hz h₂'
  have k1 := hL.2 k z y' hy'Z hzy a₁ a₂ ha₁ ha₂
  rw [GlobalTheory.FlagTan.evR_frMap hL.1 hm] at k1
  have k2 : (M₁'.submatrix id I).det = a₁.det * ι (M₁.submatrix id I).det := by
    rw [AlgHom.map_det, ← Matrix.det_mul, hM₁]; rfl
  have k3 : ι (C₂.submatrix J id).det = (C₂'.submatrix J id).det * a₂.det := by
    rw [AlgHom.map_det, ← Matrix.det_mul]
    congr 1
    ext i j
    exact (congrFun (congrFun hC₂ (J i)) j).symm
  rw [map_mul, map_mul, k2, k3]
  linear_combination (ι (M₁.submatrix id I).det * (C₂'.submatrix J id).det) * k1

open GlobalTheory.ModelFrameCompare MonObj in
set_option maxHeartbeats 1000000 in

theorem images_eigenBasis {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (σ : E →+* ℂ) (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (xV : Sp T.V ⟶ Y.X)
    (yy : Sp T.Fr ⟶ Xo.XF c) (hxV : yy ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ xV)
    (hpt : letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1 = yy) :
    ∃ v : Fin (Dw.mult σ) → (Sp (DualNumber T.V) ⟶ Y.t.G.left), (∀ j, IsTanAtG Y.t xV (v j)) ∧
      (∀ u : Sp (DualNumber T.V) ⟶ Y.t.G.left, IsTanAtG Y.t xV u →
        (∀ (a : 𝓞 E) (z : T.V), algebraMap T.V T.Fr z = io (embK c σ a) →
          u ≫ (Y.t.act.act a).left = spMap (epsMul z) ≫ u) →
        ∃ cf : Fin (Dw.mult σ) → T.V, IsCombAtG Y.t xV v cf u) ∧
      ∀ (cf : Fin (Dw.mult σ) → T.V) (u : Sp (DualNumber T.V) ⟶ Y.t.G.left)
        (w : Sp (DualNumber T.Fr) ⟶ Y.oF.t.G.left), IsCombAtG Y.t xV v cf u →
        w ≫ Y.m.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ u →
        (letI := io.toAlgebra; IsCombAt y₀.1.x (y₀.1.u σ) (fun j => algebraMap T.V T.Fr (cf j))
          (w ≫ Y.m0.toSABMap.φ)) := by
  let _ := io.toAlgebra
  obtain ⟨G₂, ⟨m⟩⟩ : ∃ G : SAB H (Sp T.V), Nonempty (SABMap G Y.t xV) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull xV Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨t₂, n₀, n₂, m', -, h2⟩ := GlobalTheory.ThetaFrameCheck.genFibre_tied Xo c T _ _ Y xV yy hxV G₂ m
  obtain ⟨n₁, hn₁⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t Y.oF.t t₂ _ yy Y.m0.toSABMap m'
  obtain ⟨G, t', m1, m2, ⟨ub, ht, he, hb, hl⟩, -⟩ := y₀.2.2
  have hx : y₀.1.x = yy ≫ pullback.fst _ _ := by
    rw [← hpt]
    exact (pullback.lift_fst _ _ _).symm
  obtain ⟨m1', hm1'⟩ := exists_sabMap_congr m1 hx
  obtain ⟨k, n, hk1, hk2⟩ := GlobalTheory.sab_extensions_iso E H Dw l Xo T.V T.Fr _ G G₂ t' t₂ m1' m2 n₁ n₂
  obtain ⟨nm, hnm⟩ := sabComp pullCubComp E H _ _ _ Y.t G₂ G xV (𝟙 _) m n
  obtain ⟨q₀, hq₀⟩ := exists_sabMap_congr nm (Category.id_comp xV)
  rw [hnm] at hq₀
  obtain ⟨B, hB, hBt, hBe, hBc⟩ := GlobalTheory.FactorDepth.Extension.exists_tanEquiv q₀
  refine ⟨fun j => (B (ub σ j)).left, fun j => (hBt _).2 (ht σ j), ?_, ?_⟩
  · intro u hu hue
    obtain ⟨w', hw'⟩ := B.surjective (ovT hu)
    have e : u = (B w').left := by rw [hw']; rfl
    subst e
    obtain ⟨cf, hcf, -⟩ := hb σ w' ((hBt _).1 hu) fun a z hz => (hBe _ a z).1 (hue a z hz)
    exact ⟨cf, (hBc _ _ cf w').2 hcf⟩
  · intro cf u w hc hw
    have h3 := GlobalTheory.LocM.Cht.FlagBase.isCombAtG_bc Y.t (algebraMap T.V T.Fr) hc
    obtain ⟨q, hq⟩ := sabComp pullCubComp E H _ _ _ Y.t Y.oF.t t₂ _ yy Y.m m'
    choose u' hu1 hu2 using hl σ
    have hov : ∀ j, u' j ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      intro j
      apply spMap_frac_cancel (V := T.V)
      rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc, hu2, Category.assoc, Over.w (ub σ j), spMap_comp',
        ← dualMap_comp_alg, ← spMap_comp']
      rfl
    have hov' : ∀ j, (u' j ≫ k.φ) ≫ t₂.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ 𝟙 _ := by
      intro j
      rw [Category.assoc, k.cart.1.w, ← Category.assoc, hov]
    have hvec : ∀ j, spMap (dualMap (algebraMap T.V T.Fr)) ≫ (B (ub σ j)).left = (u' j ≫ k.φ) ≫ q.φ := by
      intro j
      rw [hB, hq₀, hq, ← Category.assoc, ← hu2, Category.assoc, ← Category.assoc m2.φ, hk2]
      simp only [Category.assoc, h2]
    have hpt' : spMap (algebraMap T.V T.Fr) ≫ xV = 𝟙 _ ≫ yy ≫ Y.jQ ≫ pullback.fst _ _ := by
      rw [Category.id_comp, ← hxV]; rfl
    have h4 : IsCombAtG Y.t (𝟙 _ ≫ yy ≫ Y.jQ ≫ pullback.fst _ _) (fun j => (u' j ≫ k.φ) ≫ q.φ)
        (fun j => algebraMap T.V T.Fr (cf j)) (w ≫ Y.m.φ) := by
      rw [← hpt', hw]
      simpa only [hvec] using h3
    obtain ⟨w₂, hw₂, hc₂⟩ := isCombAtG_reflect q (𝟙 _) (fun j => u' j ≫ k.φ) hov' h4
    have hw₂' : w₂ ≫ m'.φ = w := by
      refine Y.m.cart.1.hom_ext ?_ ?_
      · rw [Category.assoc, ← hq, hw₂]
      · have := isPreimmersion_j Y
        have hmono : Mono Y.j := inferInstance
        have e2 : w₂ ≫ t₂.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ 𝟙 _ := by
          obtain ⟨uu, -, hh⟩ := hc₂
          rw [← hh]; exact Over.w _
        have e1 : u ≫ Y.t.G.hom = spMap (algebraMap T.V (DualNumber T.V)) ≫ xV := by
          obtain ⟨uu, -, hh⟩ := hc
          rw [← hh]; exact Over.w _
        rw [Category.assoc, m'.cart.1.w, ← Category.assoc, e2, Category.comp_id]
        apply hmono.right_cancellation
        have e3 : spMap (dualMap (algebraMap T.V T.Fr)) ≫ spMap (algebraMap T.V (DualNumber T.V)) ≫ xV =
            spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ yy ≫ Y.j := by
          rw [← Category.assoc, spMap_comp', dualMap_comp_alg, ← spMap_comp', Category.assoc, hxV]
        show (spMap _ ≫ yy) ≫ Y.j = w ≫ Y.oF.t.G.hom ≫ Y.jQ ≫ pullback.fst _ _
        rw [← Y.m.cart.1.w, ← Category.assoc w, hw, Category.assoc (spMap _) u, e1, e3, Category.assoc]
    have h5 := isCombAtG_push n₁ (𝟙 _) hc₂
    have hv5 : (fun j => (u' j ≫ k.φ) ≫ n₁.φ) = y₀.1.u σ := by
      funext j
      rw [Category.assoc, hk1, hm1', hu1]
    rw [hv5, hn₁, ← Category.assoc w₂, hw₂', Category.id_comp, ← hx] at h5
    exact h5

end GlobalTheory.FlatDenom

end
