import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEmbOfFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.AinfK GroundTheory.LocalField.FormalGroup GlobalTheory.AcrisK
open GlobalTheory.BKReal GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.PZ.PeriodVector

section Algebra

variable {F E K B : Type} [Field F] [Field E] [Field K] [CommRing B] [Algebra F E] [Algebra F K] [Algebra E K]
  [IsScalarTower F E K] [Algebra F B] [Algebra E B] [IsScalarTower F E B]

variable (F E K B) in

theorem exists_eps [FiniteDimensional F E] [CharZero F] : ∃ ε : K ⊗[F] B,
    (∀ c : E, (algebraMap E K c ⊗ₜ[F] (1 : B)) * ε = ((1 : K) ⊗ₜ[F] algebraMap E B c) * ε) ∧
    (∀ s : B →ₐ[F] B, (∀ c, s (algebraMap E B c) = algebraMap E B c) →
      Algebra.TensorProduct.map (AlgHom.id F K) s ε = ε) ∧
    ∀ (ι : Type) [Fintype ι] (b : Module.Basis ι E K) (a : ι → B),
      ε * ∑ i, b i ⊗ₜ[F] a i = 0 → ∀ i, a i = 0 := by
  classical
  have : Algebra.FormallyUnramified F E := Algebra.FormallyUnramified.of_isSeparable F E
  obtain ⟨t, h1, h2⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := F) (S := E)).1 this
  let r : E ⊗[F] E →ₐ[F] K ⊗[F] B :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom F E K) (IsScalarTower.toAlgHom F E B)
  refine ⟨r t, fun c => ?_, fun s hs => ?_, fun ι _ b a h i => ?_⟩
  · have := congrArg r (h1 c)
    rw [map_mul, map_sub, map_zero, sub_mul, sub_eq_zero] at this
    simpa [r] using this.symm
  · have : (Algebra.TensorProduct.map (AlgHom.id F K) s).comp r = r := by
      ext c
      · simp [r]
      · simp [r, hs]
    exact DFunLike.congr_fun this t
  · let n : K ⊗[F] B →ₐ[F] K ⊗[E] B := Algebra.TensorProduct.productMap
      ((Algebra.TensorProduct.includeLeft : K →ₐ[E] K ⊗[E] B).restrictScalars F)
      ((Algebra.TensorProduct.includeRight : B →ₐ[E] K ⊗[E] B).restrictScalars F)
    have hn : n.comp r = (IsScalarTower.toAlgHom F E (K ⊗[E] B)).comp (Algebra.TensorProduct.lmul' F) := by
      ext c
      · simp [r, n]
      · simp [r, n, Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def]
    have h3 : n (r t) = 1 := by
      have := DFunLike.congr_fun hn t
      rw [AlgHom.comp_apply, AlgHom.comp_apply, h2, map_one] at this
      exact this
    have h4 := congrArg n h
    rw [map_mul, h3, one_mul, map_sum, map_zero] at h4
    have h5 := congrArg (fun x => TensorProduct.lid E B (LinearMap.rTensor B (b.coord i) x)) h4
    simpa [n, Finsupp.single_apply] using h5

variable (F E K B) in

theorem exists_section [FiniteDimensional F E] [CharZero F] :
    ∃ (Q : Type) (_ : CommRing Q) (iL : K →+* Q) (iR : B →+* Q) (sec : Q → K ⊗[F] B),
      (∀ c : E, iR (algebraMap E B c) = iL (algebraMap E K c)) ∧
      (∀ (ι : Type) [Fintype ι] (b : Module.Basis ι E K) (a : ι → B),
        ∑ i, iR (a i) * iL (b i) = 0 → ∀ i, a i = 0) ∧
      (∀ x, sec x = 0 → x = 0) ∧
      (∀ x (c : E), ((1 : K) ⊗ₜ[F] algebraMap E B c) * sec x = algebraMap E K c • sec x) ∧
      ∀ s : B →ₐ[F] B, (∀ c, s (algebraMap E B c) = algebraMap E B c) → ∃ s' : Q →+* Q,
        (∀ c, s' (iL c) = iL c) ∧ (∀ y, s' (iR y) = iR (s y)) ∧ ∀ x c, s' x = iL c * x →
          Algebra.TensorProduct.map (AlgHom.id F K) s (sec x) = c • sec x := by
  obtain ⟨ε, h1, h2, h3⟩ := exists_eps F E K B
  have hsm : ∀ (x : K) (z : K ⊗[F] B), x • z = (x ⊗ₜ[F] (1 : B)) * z := fun x z => Algebra.smul_def x z
  let J : Ideal (K ⊗[F] B) := LinearMap.ker (LinearMap.mul (K ⊗[F] B) _ ε)
  let q := Ideal.Quotient.mk J
  have hq : ∀ x y, q x = q y ↔ ε * x = ε * y := fun x y => by
    rw [Ideal.Quotient.eq, ← sub_eq_zero, ← mul_sub]
    rfl
  let iL : K →+* K ⊗[F] B := Algebra.TensorProduct.includeLeftRingHom
  let iR : B →+* K ⊗[F] B := (Algebra.TensorProduct.includeRight : B →ₐ[F] K ⊗[F] B).toRingHom
  choose z hz using (Ideal.Quotient.mk_surjective : Function.Surjective q)
  refine ⟨(K ⊗[F] B) ⧸ J, inferInstance, q.comp iL, q.comp iR, fun x => ε * z x, fun c => ?_,
    fun ι _ b a h => h3 ι b a ?_, fun x h0 => ?_, fun x c => ?_, fun s hs => ?_⟩
  · change q (1 ⊗ₜ _) = q (_ ⊗ₜ 1)
    rw [hq, mul_comm, ← h1, mul_comm]
  · rw [← mul_zero ε, ← hq, map_zero, ← h, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change _ = q (1 ⊗ₜ _) * q (_ ⊗ₜ 1)
    rw [← map_mul q, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  · rw [← hz x, ← map_zero q, hq, mul_zero]
    exact h0
  · rw [hsm, ← mul_assoc, ← h1, mul_assoc]
  · let s' := (Algebra.TensorProduct.map (AlgHom.id F K) s).toRingHom
    have hε : s' ε = ε := h2 s hs
    let s'' : (K ⊗[F] B) ⧸ J →+* (K ⊗[F] B) ⧸ J :=
      Ideal.Quotient.lift J (q.comp s') fun a ha => by
        have ha' : ε * a = 0 := ha
        rw [RingHom.comp_apply, ← map_zero q, hq, ← hε, ← map_mul s', ha', map_zero, mul_zero]
    have hs'' : ∀ a, s'' (q a) = q (s' a) := fun a => rfl
    refine ⟨s'', fun c => ?_, fun y => rfl, fun x c h6 => ?_⟩
    · change q (c ⊗ₜ s 1) = q (c ⊗ₜ 1)
      rw [map_one]
    · rw [← hz x, hs'', RingHom.comp_apply, ← map_mul q, hq] at h6
      change s' _ = _
      rw [map_mul, hε, h6, hsm, mul_left_comm]
      rfl

theorem exists_vec [FiniteDimensional F E] {W : Type} [AddCommGroup W] [Module K W] (σ : E →ₐ[F] E)
    (hσ : Function.Bijective σ) (hfix : ∀ x, σ x = x → ∃ c : F, algebraMap F E c = x)
    (Φ : W →ₗ[K] W) (hΦ : Function.Injective Φ) (m : E → W →ₗ[K] W)
    (hm : ∀ c w, Φ (m c w) = m (σ c) (Φ w)) (v : W) (hv : v ≠ 0) (hc : ∀ c, m c v = algebraMap E K c • v)
    (π : K) (hπ : (Φ ^ Module.finrank F E) v = π • v) (D : Submodule K W) (hD : ∀ w ∈ D, Φ w ∈ D) (hvD : v ∈ D) :
    ∃ e ∈ D, (Φ ^ Module.finrank F E) e = π • e ∧
      Module.finrank K ↥(Submodule.span K (Set.range fun c => m c e)) = Module.finrank F E := by
  classical
  obtain ⟨emb, hbij, hemb⟩ := GlobalTheory.HWL.Letters.exists_emb_of_fixed σ hσ hfix (IsScalarTower.toAlgHom F E K)
  haveI : NeZero (Module.finrank F E) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨i₀, hi₀⟩ := hbij.2 (IsScalarTower.toAlgHom F E K)
  have heig : ∀ (j : ℕ) (c : E), m c ((Φ ^ j) v) = emb (i₀ + j) c • (Φ ^ j) v := by
    intro j
    induction j with
    | zero => intro c; simp [hi₀, hc]
    | succ j ih =>
      intro c
      obtain ⟨c, rfl⟩ := hσ.2 c
      rw [pow_succ', Module.End.mul_apply, ← hm, ih, map_smul, ← hemb (i₀ + j), Nat.cast_succ, add_assoc]
      rfl
  let w : ZMod (Module.finrank F E) → W := fun i => (Φ ^ i.val) v
  let τ : ZMod (Module.finrank F E) → E → K := fun i => emb (i₀ + i)
  have hw : ∀ i c, m c (w i) = τ i c • w i := fun i c => by
    simp only [w, τ, heig, ZMod.natCast_val, ZMod.cast_id', id]
  have hw0 : ∀ i, w i ≠ 0 := fun i h =>
    hv ((Module.End.iterate_injective hΦ i.val) (h.trans (map_zero _).symm))
  have hτ : LinearIndependent K τ := by
    have h := (linearIndependent_monoidHom E K).comp (fun i => ((emb (i₀ + i) : E →+* K) : E →* K))
      fun i j h => add_left_cancel (hbij.1 (AlgHom.ext fun x => DFunLike.congr_fun h x))
    exact h
  have hspan := span_flip_eq_top_iff_linearIndependent.2 hτ
  have hli : LinearIndependent K w := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    have h1 : ∀ x : ZMod (Module.finrank F E) → K, Fintype.linearCombination K (fun i => a i • w i) x = 0 := by
      intro x
      have hx : x ∈ Submodule.span K (Set.range (flip τ)) := hspan ▸ Submodule.mem_top
      refine (Submodule.span_le (p := LinearMap.ker (Fintype.linearCombination K fun i => a i • w i))).2 ?_ hx
      rintro _ ⟨c, rfl⟩
      have := congrArg (m c) ha
      simp only [map_sum, map_smul, hw, map_zero] at this
      change ∑ i, τ i c • a i • w i = 0
      simpa only [smul_comm (a _)] using this
    have h2 := h1 (Pi.single i 1)
    rw [Fintype.linearCombination_apply_single, one_smul] at h2
    exact (smul_eq_zero.1 h2).resolve_right (hw0 i)
  refine ⟨∑ i, w i, D.sum_mem fun i _ => ?_, ?_, ?_⟩
  · exact Module.End.pow_apply_mem_of_forall_mem _ hD v hvD
  · rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Module.End.mul_apply, ← pow_add, add_comm, pow_add, Module.End.mul_apply, hπ, map_smul]
  · have h1 : (fun c => m c (∑ i, w i)) = Fintype.linearCombination K w ∘ flip τ := by
      funext c
      simp only [map_sum, hw]
      rfl
    rw [h1, Set.range_comp, Submodule.span_image, hspan, Submodule.map_top,
      LinearMap.finrank_range_of_inj hli.fintypeLinearCombination_injective]
    simp

theorem iterate_finrank [FiniteDimensional F E] (σ : E →ₐ[F] E)
    (hσ : Function.Bijective σ) (hfix : ∀ x, σ x = x → ∃ c : F, algebraMap F E c = x) (c : E) :
    (σ ^ Module.finrank F E) c = c := by
  obtain ⟨emb, -, hemb⟩ := GlobalTheory.HWL.Letters.exists_emb_of_fixed σ hσ hfix (AlgHom.id F E)
  have h : ∀ (j : ℕ), emb j ((σ ^ j) c) = emb 0 c := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [← ih, pow_succ', Nat.cast_succ, ← hemb j]; rfl
  have h1 := h (Module.finrank F E)
  rw [ZMod.natCast_self] at h1
  exact (emb 0).injective h1

end Algebra

section Concrete

variable {l : ℕ} [hl : Fact l.Prime] (K : FinExt l)

theorem exists_basis (κ : W0 K → ↥(K0 K))
    (hκ : ∀ w, algebraMap ↥(K0 K) ↥K.1 (κ w) = oK K (thetaW (fK K) K w)) {ι : Type} [Fintype ι]
    (b : Module.Basis ι (W0 K) ↥(OL K)) : ∃ b' : Module.Basis ι ↥(K0 K) ↥K.1, ∀ i, b' i = oK K (b i) := by
  have hO : ∀ c : ↥(OL K), oK K c ∈ Submodule.span ↥(K0 K) (Set.range fun i => oK K (b i)) := fun c => by
    rw [← b.sum_repr c, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def, map_mul, algebraMap_WO, ← hκ, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hsp : ⊤ ≤ Submodule.span ↥(K0 K) (Set.range fun i => oK K (b i)) := fun x _ => by
    haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    haveI : Algebra.IsAlgebraic ℤ_[l] ↥K.1 :=
      (IsFractionRing.comap_isAlgebraic_iff (A := ℤ_[l]) (K := ℚ_[l]) (C := ↥K.1)).2 inferInstance
    obtain ⟨y, hy0, hy⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ_[l]) x).exists_integral_multiple
    have h1 := hO ⟨y • x, hy⟩
    have h2 : oK K ⟨y • x, hy⟩ = algebraMap ℚ_[l] ↥(K0 K) (y : ℚ_[l]) • x := by
      rw [algebraMap_smul]
      rfl
    rw [h2] at h1
    exact (Submodule.smul_mem_iff _ ((map_ne_zero _).2 (PadicInt.coe_ne_zero.2 hy0))).1 h1
  exact ⟨basisOfTopLeSpanOfCardEqFinrank _ hsp (by rw [← finrank_WO, Module.finrank_eq_card_basis b]),
    fun i => by simp⟩

theorem exists_coord {ι : Type} [Fintype ι] (b : Module.Basis ι (W0 K) ↥(OL K)) (y : CK K) :
    ∃ a : ι → Per.Acris l, y = ∑ i, inC K (a i) * inI K (b i) :=
  AcrisK.induction_on y (fun a c => ⟨fun i => a * aC l (wA l (fK K) (b.repr c i)), by
    conv_lhs => rw [← b.sum_repr c, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, map_mul, inC_wA, algebraMap_WO, mul_assoc]⟩)
    fun x y ⟨a, ha⟩ ⟨a', ha'⟩ => ⟨a + a', by
      rw [ha, ha', ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, map_add, add_mul]⟩

variable {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Algebra ↥(K0 K) B] [IsScalarTower ℚ_[l] ↥(K0 K) B]

theorem exists_lift (u : Per.Acris l →+* B) (hu : Function.Injective u) (κ : W0 K → ↥(K0 K))
    (hκ : ∀ w, algebraMap ↥(K0 K) ↥K.1 (κ w) = oK K (thetaW (fK K) K w))
    (hκ' : ∀ w, algebraMap ↥(K0 K) B (κ w) = u (aC l (wA l (fK K) w))) (t : BK K) (ht : t ≠ 0) :
    ∃ v : ↥K.1 ⊗[ℚ_[l]] B, v ≠ 0 ∧
      (∀ c : ↥(K0 K), ((1 : ↥K.1) ⊗ₜ[ℚ_[l]] algebraMap ↥(K0 K) B c) * v = algebraMap ↥(K0 K) ↥K.1 c • v) ∧
      ∀ (s : B →ₐ[ℚ_[l]] B) (s₀ : Per.Acris l → Per.Acris l) (S : BK K →+* BK K) (x : ↥K.1),
        (∀ c, s (algebraMap ↥(K0 K) B c) = algebraMap ↥(K0 K) B c) → (∀ a, s (u a) = u (s₀ a)) →
        (∀ a, S (toB K (inC K a)) = toB K (inC K (s₀ a))) → (∀ c, S (inK K c) = inK K c) →
        S t = inK K x * t → Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥K.1) s v = x • v := by
  classical
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := FiniteDimensional.of_injective
    (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1).toLinearMap (algebraMap ↥(K0 K) ↥K.1).injective
  obtain ⟨Q, _, iL, iR, sec, h1, h2, h3, h4, h5⟩ := exists_section ℚ_[l] ↥(K0 K) ↥K.1 B
  obtain ⟨ψ, hψC, hψK⟩ : ∃ ψ : BK K →+* Q, (∀ a, ψ (toB K (inC K a)) = iR (u a)) ∧ ∀ c, ψ (inK K c) = iL c :=
    have h : ∀ w : W0 K, (iR.comp u) (aC l (wA l (fK K) w)) = iL (oK K (thetaW (fK K) K w)) := fun w => by
      rw [RingHom.comp_apply, ← hκ, ← hκ', h1]
    ⟨liftB _ _ h, liftB_inC _ _ h, liftB_inK _ _ h⟩
  refine ⟨sec (ψ t), fun h0 => ht ?_, h4 _, fun s s₀ S x hs hs₀ hS hSK hSt => ?_⟩
  · obtain ⟨D, y, hy⟩ := exists_pow_mul t
    let b := Module.Free.chooseBasis (W0 K) ↥(OL K)
    obtain ⟨b', hb'⟩ := exists_basis K κ hκ b
    obtain ⟨a, ha⟩ := exists_coord K b y
    have h6 : ψ (toB K y) = ∑ i, iR (u (a i)) * iL (b' i) := by
      rw [ha, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_mul, ← inK_oK, hψC, hψK, hb']
    rw [← hy, map_mul, h3 _ h0, mul_zero] at h6
    have h7 : y = 0 := ha.trans (Finset.sum_eq_zero fun i _ => by
      rw [hu ((h2 _ b' _ h6.symm i).trans (map_zero u).symm), map_zero, zero_mul])
    rw [h7, map_zero] at hy
    exact ((isUnit_l K).pow D).mul_right_eq_zero.1 hy
  · obtain ⟨s', hL, hR, h⟩ := h5 s hs
    have hcomm : s'.comp ψ = ψ.comp S := ringHom_extB fun y => RingHom.congr_fun
      (AcrisK.ringHom_ext (u := (s'.comp ψ).comp (toB K)) (v := (ψ.comp S).comp (toB K)) (fun a => by
        simp only [RingHom.comp_apply, hψC, hS, hR, hs₀]) fun c => by
        simp only [RingHom.comp_apply, ← inK_oK, hSK, hψK, hL]) y
    have h6 := RingHom.congr_fun hcomm t
    rw [RingHom.comp_apply, RingHom.comp_apply, hSt, map_mul, hψK] at h6
    exact h _ _ h6

end Concrete

section Tied

variable {l : ℕ} [hl : Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (K : FinExt l)

theorem exists_unram (w : W0 K) : ∃ c : ↥(K0 K), algebraMap ↥(K0 K) ↥K.1 c = oK K (thetaW (fK K) K w) ∧
    T.eB (algebraMap ↥(K0 K) P.R.B c) = Per.aB l (wA l (fK K) w) := by
  obtain ⟨c, hc⟩ := (P.PD K).invB (T.eB.symm (Per.aB l (wA l (fK K) w))) fun g => T.eB.injective (by
    rw [P.PD_actB, T.actB, RingEquiv.apply_symm_apply]
    exact ((ActLaws.act_laws l).2.2.2.2.2.1 (g : GQ l) _).trans (congrArg (Per.aB l) (σA_wA g w)))
  refine ⟨c, ?_, by rw [hc, RingEquiv.apply_symm_apply]⟩
  obtain ⟨y, hy, hθ⟩ := T.om (c : Om l)
  have h1 : P.ιB (algebraMap ↥(K0 K) P.R.B c) = algebraMap (Om l) P.R.BdR (c : Om l) := by
    rw [← P.PD_ι K, AlgHom.commutes]
    rfl
  have h2 : T.eD (P.ιB (T.eB.symm (Per.aB l (wA l (fK K) w)))) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (wA l (fK K) w)) :=
    GlobalTheory.CrisIncl.incl_aB l _ T.incl (wA l (fK K) w)
  rw [← hc, h1, hy] at h2
  rw [(BdRField.bdR_isField l).2.1 h2, (thetaD_props l).2.2.2.1, ← intToOC_thetaW (fK K) K] at hθ
  exact Subtype.ext ((algebraMap (Om l) ℂ_[l]).injective hθ.symm)

end Tied

section Line

variable {F K B : Type} [Field F] [Field K] [CommRing B] [Algebra F K] [Algebra F B]

variable (F K B) in

def toLine : K ⊗[F] B ≃ₗ[K] (Fin 1 → K) ⊗[F] B :=
  AlgebraTensorModule.congr (LinearEquiv.funUnique (Fin 1) K K).symm (LinearEquiv.refl F B)

theorem toLine_map (s : B →ₐ[F] B) (x : K ⊗[F] B) :
    toLine F K B (Algebra.TensorProduct.map (AlgHom.id F K) s x) =
      AlgebraTensorModule.map (LinearMap.id : (Fin 1 → K) →ₗ[K] (Fin 1 → K)) s.toLinearMap (toLine F K B x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c y => simp [toLine]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem toLine_mul (b : B) (x : K ⊗[F] B) :
    toLine F K B (((1 : K) ⊗ₜ[F] b) * x) =
      AlgebraTensorModule.map (LinearMap.id : (Fin 1 → K) →ₗ[K] (Fin 1 → K)) (LinearMap.mulLeft F b)
        (toLine F K B x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c y => simp [toLine]
  | add x y hx hy => simp only [mul_add, map_add, hx, hy]

theorem map_pow_id {V : Type} [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V] (s : B →ₐ[F] B)
    (n : ℕ) : (AlgebraTensorModule.map (LinearMap.id : V →ₗ[K] V) s.toLinearMap : V ⊗[F] B →ₗ[K] V ⊗[F] B) ^ n =
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[K] V) (s ^ n).toLinearMap := by
  induction n with
  | zero => ext; simp
  | succ n ih => rw [pow_succ, ih]; ext; simp [pow_succ]

theorem exists_dcris {G E D : Type} [Group G] [Field E] [Algebra F E] [Algebra E K] [IsScalarTower F E K]
    [CommRing D] [Algebra E B] [IsScalarTower F E B] [Algebra F D] [Algebra E D] [Algebra K D]
    [IsScalarTower F K D] [IsScalarTower E K D] [IsScalarTower F E D] (PD : PeriodData G F E K B D)
    (hfix : ∀ x, PD.σ x = x → ∃ c : F, algebraMap F E c = x) (χ : G →* Kˣ)
    (ρ : Representation K G (Fin 1 → K)) (hρ : ∀ g, ρ g = (((χ g)⁻¹ : Kˣ) : K) • LinearMap.id) (π : K)
    (v : K ⊗[F] B) (hv0 : v ≠ 0) (hvc : ∀ c : E, ((1 : K) ⊗ₜ[F] algebraMap E B c) * v = algebraMap E K c • v)
    (h1 : Algebra.TensorProduct.map (AlgHom.id F K) (PD.φ ^ Module.finrank F E) v = π • v)
    (h2 : ∀ g, Algebra.TensorProduct.map (AlgHom.id F K) ((PD.actB g).toAlgHom.restrictScalars F) v =
      (χ g : K) • v) :
    ∃ e ∈ Dcris PD ρ, (φVB PD (LL := K) (V := Fin 1 → K) ^ Module.finrank F E) e = π • e ∧
      Module.finrank K ↥(Submodule.span K (Set.range fun c : E =>
        mulVB (Qp := F) (K₀ := E) (B := B) (LL := K) (V := Fin 1 → K) c e)) = Module.finrank F E := by
  haveI := PD.finK₀
  have hmem : ∀ w, w ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g w = w := fun w => by
    simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  refine exists_vec PD.σ PD.σ_bij hfix _ ?_ _ (fun c w => ?_) (toLine F K B v)
    ((map_ne_zero_iff _ (toLine F K B).injective).2 hv0) (fun c => ?_) _ ?_ _ (fun w hw => ?_) ?_
  · exact Module.Flat.lTensor_preserves_injective_linearMap (M := Fin 1 → K) PD.φ.toLinearMap PD.φ_inj
  · induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y => simp [φVB, mulVB, PD.φ_K₀]
    | add x y hx hy => simp only [map_add, hx, hy]
  · rw [mulVB, ← toLine_mul, hvc, map_smul]
  · rw [φVB, map_pow_id, ← toLine_map, h1, map_smul]
  · rw [hmem] at hw ⊢
    intro g
    conv_rhs => rw [← hw g]
    generalize w = z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y => simp [φVB, actVB, PD.φ_comm]
    | add x y hx hy => simp only [map_add, hx, hy]
  · rw [hmem]
    intro g
    have h3 : actVB PD ρ g = (((χ g)⁻¹ : Kˣ) : K) •
        AlgebraTensorModule.map LinearMap.id ((PD.actB g).toAlgHom.restrictScalars F).toLinearMap := by
      rw [actVB, hρ]
      exact AlgebraTensorModule.map_smul_left _ _ _
    rw [h3, LinearMap.smul_apply, ← toLine_map, h2, map_smul, smul_smul, Units.inv_mul, one_smul]

end Line

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (t : BK K), t ≠ 0 → frobB K t = inK K (π : ↥K.1) * t →
      (∀ g : ↥(GK K), galB g t = inK K (χ g : ↥K.1) * t) →
      ∃ e ∈ Dcris (P.PD K) (lineRep (K := K) (LL := K) χ⁻¹),
        (φVB (P.PD K) (LL := ↥K.1) (V := Fin 1 → ↥K.1) ^ Module.finrank ℚ_[l] ↥(K0 K)) e = ((π : ↥K.1)) • e ∧
        Module.finrank ↥K.1 ↥(Submodule.span ↥K.1 (Set.range fun c : ↥(K0 K) =>
            mulVB (Qp := ℚ_[l]) (K₀ := ↥(K0 K)) (B := P.R.B) (LL := ↥K.1) (V := Fin 1 → ↥K.1) c e)) =
          Module.finrank ℚ_[l] ↥(K0 K) := by
  intro l _ P AI ⟨T⟩ K χ π t ht hφ hg
  haveI := (P.PD K).finK₀
  choose κ hκ hκ' using exists_unram T K
  let u : Per.Acris l →+* P.R.B := T.eB.symm.toRingHom.comp (algebraMap (Per.Acris l) (Per.Bcris l))
  have hu : ∀ a, T.eB (u a) = algebraMap (Per.Acris l) (Per.Bcris l) a := fun a => T.eB.apply_symm_apply _
  obtain ⟨v, hv0, hvc, hv⟩ := exists_lift K u
    (T.eB.symm.injective.comp (PhiInj.algebraMap_acris_bcris_injective l)) κ hκ
    (fun w => T.eB.injective ((hκ' w).trans ((GlobalTheory.RingIface.aB_eq_alg l _).trans (hu _).symm))) t ht
  have hfix := GlobalTheory.HWL.Letters.sigma_fixed P K
  have hφn : ∀ (n : ℕ) (a : Per.Acris l), ((P.PD K).φ ^ n) (u a) = u ((⇑(phiA l))^[n] a) := fun n a => by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', AlgHom.mul_apply, ih, Function.iterate_succ_apply']
      refine T.eB.injective ?_
      rw [P.PD_φ, T.frob, hu, hu]
      exact (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.2 _
  have hσn : ∀ (n : ℕ) (c : ↥(K0 K)), ((P.PD K).φ ^ n) (algebraMap ↥(K0 K) P.R.B c) =
      algebraMap ↥(K0 K) P.R.B (((P.PD K).σ ^ n) c) := fun n c => by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', AlgHom.mul_apply, ih, (P.PD K).φ_K₀, pow_succ', AlgHom.mul_apply]
  have h1 := hv ((P.PD K).φ ^ Module.finrank ℚ_[l] ↥(K0 K)) _ (frobB K) _
    (fun c => by rw [hσn, iterate_finrank _ (P.PD K).σ_bij hfix]) (hφn _)
    (fun a => by rw [frobB_toB, frobC_inC]; rfl) frobB_inK hφ
  have h2 := fun g : ↥(GK K) => hv (((P.PD K).actB g).toAlgHom.restrictScalars ℚ_[l]) (sigA (g : GQ l)) (galB g) _
    (fun c => ((P.PD K).actB g).commutes c) (fun a => T.eB.injective (by
      change T.eB ((P.PD K).actB g (u a)) = _
      rw [P.PD_actB, T.actB, hu, hu]
      exact (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.1 (g : GQ l) a))
    (fun a => by rw [galB_toB, galC_inC]) (galB_inK g) (hg g)
  exact exists_dcris (P.PD K) hfix χ _ (fun _ => rfl) _ v hv0 hvc h1 h2

end GlobalTheory.PZ.PeriodVector
