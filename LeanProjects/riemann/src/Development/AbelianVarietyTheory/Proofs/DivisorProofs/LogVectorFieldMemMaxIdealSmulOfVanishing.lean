import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLePreimageOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogVectorFieldBasisToroidalModelSnc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqLogDerivationExtendLocalizationAw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqOfLogDerivationExtendEq
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogBack

section Algebra

open IsLocalRing GlobalTheory.LogDerProj GlobalTheory.LogBasis

theorem prime_X {σ k : Type} [CommRing k] [IsDomain k] (s : σ) : Prime (MvPowerSeries.X s : MvPowerSeries σ k) := by
  classical
  let ρ := MvPowerSeries.rescale (σ := σ) (R := k) (fun i => if i = s then 0 else 1)
  have key : ∀ g, MvPowerSeries.X s ∣ g ↔ ρ g = 0 := by
    intro g
    rw [MvPowerSeries.X_dvd_iff, MvPowerSeries.ext_iff]
    refine forall_congr' fun n => ?_
    rw [MvPowerSeries.coeff_rescale, map_zero]
    by_cases hn : n s = 0
    · have : (n.prod fun i m => (if i = s then (0 : k) else 1) ^ m) = 1 := by
        refine Finset.prod_eq_one fun i hi => ?_
        have : i ≠ s := fun h => (Finsupp.mem_support_iff.1 hi) (h ▸ hn)
        simp [this]
      simp [hn, this]
    · have : (n.prod fun i m => (if i = s then (0 : k) else 1) ^ m) = 0 :=
        Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hn) (by simp [hn])
      simp [hn, this]
  refine ⟨?_, ?_, fun a b h => ?_⟩
  · intro h
    have := congrArg (MvPowerSeries.coeff (Finsupp.single s 1)) h
    simp [MvPowerSeries.coeff_X] at this
  · intro h
    have := h.map (MvPowerSeries.constantCoeff (σ := σ) (R := k))
    simp at this
  · rw [key, map_mul, mul_eq_zero, ← key, ← key] at h
    exact h

theorem exists_log_of_dvd {R ι : Type} [CommRing R] [IsDomain R] [Algebra ℤ R] [Fintype ι] (I : Ideal R) (δ : Derivation ℤ R R)
    (h0 : ∀ r, δ r ∈ I) (T a : ι → R) (hT : ∀ i, Prime (T i)) (ha : ∀ i, a i ∈ I) (hδ : ∀ i, δ (T i) = a i * T i)
    (N : ℕ) : ∀ g, g ∣ (∏ i, T i) ^ N → ∃ α ∈ I, δ g = α * g := by
  classical
  have step : ∀ i q, (∀ g, g ∣ q → ∃ α ∈ I, δ g = α * g) → ∀ g, g ∣ T i * q → ∃ α ∈ I, δ g = α * g := by
    rintro i q hq g ⟨h, hh⟩
    rcases (hT i).dvd_or_dvd (⟨q, hh.symm⟩ : T i ∣ g * h) with ⟨g', rfl⟩ | ⟨h', rfl⟩
    · obtain ⟨α, hα, e⟩ := hq g' ⟨h, mul_left_cancel₀ (hT i).ne_zero (by rw [hh]; ring)⟩
      refine ⟨α + a i, I.add_mem hα (ha i), ?_⟩
      rw [δ.leibniz, e, hδ, smul_eq_mul, smul_eq_mul]
      ring
    · exact hq g ⟨h', mul_left_cancel₀ (hT i).ne_zero (by rw [hh]; ring)⟩
  have steps : ∀ (s : Finset ι) q, (∀ g, g ∣ q → ∃ α ∈ I, δ g = α * g) →
      ∀ g, g ∣ (∏ i ∈ s, T i) * q → ∃ α ∈ I, δ g = α * g := by
    intro s q hq
    induction s using Finset.induction_on with
    | empty => simpa using hq
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, mul_assoc]
      exact step j _ ih
  induction N with
  | zero =>
    intro g hg
    rw [pow_zero] at hg
    obtain ⟨v, hv⟩ := hg
    exact ⟨δ g * v, I.mul_mem_right _ (h0 g), by linear_combination (δ g) * hv⟩
  | succ N ih =>
    rw [pow_succ']
    exact steps _ _ ih

theorem exists_dual {K R : Type} [CommRing K] [CommRing R] [Algebra K R]
    {n : ℕ} (z : Fin n → R) (bΩ : Module.Basis (Fin n) R Ω[R⁄K])
    (hb : ∀ i, bΩ i = KaehlerDifferential.D K R (z i)) :
    ∃ d : Fin n → Derivation ℤ R R, (∀ k l, d k (z l) = if k = l then 1 else 0) ∧
      (∀ k a, d k (algebraMap K R a) = 0) ∧
      ∀ D : Derivation ℤ R R, (∀ a, D (algebraMap K R a) = 0) → D = ∑ k, D (z k) • d k := by
  classical
  let d : Fin n → Derivation ℤ R R := fun k =>
    (KaehlerDifferential.linearMapEquivDerivation K R (bΩ.coord k)).restrictScalars ℤ
  have hd' : ∀ k r, d k r = bΩ.repr (KaehlerDifferential.D K R r) k := fun k r => rfl
  refine ⟨d, fun k l => by rw [hd', ← hb]; simp [Finsupp.single_apply, eq_comm], fun k a => by rw [hd']; simp,
    fun D hD => ?_⟩
  let D' : Derivation K R R := Derivation.mk'
    { toFun := D
      map_add' := map_add D
      map_smul' := fun a r => by
        simp only [Algebra.smul_def, D.leibniz, hD, RingHom.id_apply]
        simp }
    (fun x y => D.leibniz x y)
  have hD' : ∀ r, D' r = D r := fun _ => rfl
  ext r
  have := map_sum (Derivation.coeFnAddMonoidHom (R := ℤ) (A := R) (M := R)) (fun k => D (z k) • d k) Finset.univ
  have h3 := congrFun this r
  rw [Finset.sum_apply] at h3
  refine Eq.trans ?_ h3.symm
  rw [← hD', ← D'.liftKaehlerDifferential_comp_D r, ← bΩ.sum_repr (KaehlerDifferential.D K R r), map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, hb, D'.liftKaehlerDifferential_comp_D, hD']
  simp [hd', mul_comm]

theorem exists_sum_of_coords {K B R : Type} [Field K] [CharZero K] [CommRing B] [Algebra K B] [IsNoetherianRing B]
    [CommRing R] (I : Ideal R) {n m : ℕ} (z : Fin n → B) (bΩ : Module.Basis (Fin n) B Ω[B⁄K])
    (hb : ∀ i, bΩ i = KaehlerDifferential.D K B (z i)) (e : Fin m → Fin n) (he : Function.Injective e)
    (ψ : B →+* R) (D : Derivation ℤ B B) (hD : D ∈ logSub (algebraMap K B) (Ideal.span {∏ i, z (e i)}))
    (h0 : ∀ r, ψ (D r) ∈ I) (h1 : ∀ i c, D (z (e i)) = c * z (e i) → ψ c ∈ I) :
    ∃ (g : Fin n → B) (v : Fin n → Derivation ℤ B B), (∀ k, ψ (g k) ∈ I) ∧
      (∀ k, v k ∈ logSub (algebraMap K B) (Ideal.span {∏ i, z (e i)})) ∧ D = ∑ k, g k • v k := by
  classical
  have hQ : ∀ n : ℕ, IsUnit ((n : B) + 1) := fun n => by
    have := (IsUnit.mk0 ((n : K) + 1) (Nat.cast_add_one_ne_zero n)).map (algebraMap K B)
    simpa using this
  obtain ⟨d, hd, hd0, hspan⟩ := exists_dual z bΩ hb
  obtain ⟨b, hb'⟩ := exists_basis_of_dual hQ (algebraMap K B) z d hd hd0 hspan e he
    (logSub (algebraMap K B) (Ideal.span {∏ i, z (e i)})) (fun _ => Iff.rfl)
  have hv : ∀ k u, (∀ i, k = e i → z (e i) ∣ u) → u • d k ∈ logSub (algebraMap K B) (Ideal.span {∏ i, z (e i)}) := by
    intro k u hu
    refine ⟨fun a => by simp [hd0], mem_span_of_dvd _ (prod_mem_span _ _ _ fun i _ => ?_)⟩
    rw [Derivation.smul_apply, hd]
    split_ifs with h
    · simpa using hu i h
    · simp
  have key : ∀ k, ∃ (g : B) (v : Derivation ℤ B B), ψ g ∈ I ∧
      v ∈ logSub (algebraMap K B) (Ideal.span {∏ i, z (e i)}) ∧ D (z k) • d k = g • v := by
    intro k
    by_cases hk : ∃ i, e i = k
    · obtain ⟨i, rfl⟩ := hk
      have hc : D (z (e i)) = b.repr ⟨D, hD⟩ (e i) * z (e i) := by
        have h2 := congrArg Subtype.val (b.sum_repr ⟨D, hD⟩)
        rw [Submodule.coe_sum] at h2
        have := map_sum (Derivation.coeFnAddMonoidHom (R := ℤ) (A := B) (M := B))
          (fun k => ((b.repr ⟨D, hD⟩ k • b k : logSub (algebraMap K B) (Ideal.span {∏ i, z (e i)})) :
            Derivation ℤ B B)) Finset.univ
        have h3 := congrFun this (z (e i))
        rw [Finset.sum_apply, h2] at h3
        refine h3.trans ?_
        simp [hb']
      refine ⟨_, z (e i) • d (e i), h1 i _ hc, hv _ _ fun j hj => by rw [hj], ?_⟩
      rw [smul_smul, ← hc]
    · exact ⟨D (z k), (1 : B) • d k, h0 _, hv _ _ fun j hj => absurd ⟨j, hj.symm⟩ hk, by rw [one_smul]⟩
  choose g v hg hv' hgv using key
  exact ⟨g, v, hg, hv', (hspan D hD.1).trans (Finset.sum_congr rfl fun k _ => hgv k)⟩

theorem mem_smul_top_of_sum {K A B ι : Type} [Field K] [CommRing A] [CommRing B] [Algebra A B] [Fintype ι] (f : A)
    [IsLocalization.Away f B] (φ : K →+* A) (hφ : φ.FiniteType) (J m : Ideal A) (hm : m.IsMaximal) (hf : f ∉ m)
    (D : logSub φ J) (g : ι → B) (v : ι → Derivation ℤ B B)
    (hg : ∀ k, ∃ (s : Submonoid.powers f) (a : A), a ∈ m ∧ g k * algebraMap A B s = algebraMap A B a)
    (hv : ∀ k, v k ∈ logSub ((algebraMap A B).comp φ) (J.map (algebraMap A B)))
    (h : extL (S := B) f D.1 = ∑ k, g k • v k) : D ∈ m • (⊤ : Submodule A (logSub φ J)) := by
  classical
  have key : ∃ (s : Submonoid.powers f) (D' : logSub φ J), D' ∈ m • (⊤ : Submodule A (logSub φ J)) ∧
      (s : A) • extL (S := B) f D.1 = extL (S := B) f D'.1 := by
    rw [h]
    refine Finset.sum_induction _ (fun δ : Derivation ℤ B B => ∃ (s : Submonoid.powers f) (D' : logSub φ J),
      D' ∈ m • (⊤ : Submodule A (logSub φ J)) ∧ (s : A) • δ = extL (S := B) f D'.1) ?_ ⟨1, 0, zero_mem _, by simp⟩ ?_
    · rintro x y ⟨s, D₁, h₁, e₁⟩ ⟨t, D₂, h₂, e₂⟩
      refine ⟨s * t, (t : A) • D₁ + (s : A) • D₂,
        add_mem (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂), ?_⟩
      rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, map_add, map_smul, map_smul, ← e₁, ← e₂,
        smul_smul, smul_smul, smul_add, Submonoid.coe_mul, mul_comm (t : A)]
    · intro k _
      obtain ⟨s, a, ha, e⟩ := hg k
      obtain ⟨⟨D', t⟩, e'⟩ := exists_pow_smul_eq_res (S := B) f φ hφ J ⟨v k, hv k⟩
      have e'' : (t : A) • v k = extL (S := B) f D'.1 := congrArg Subtype.val e'
      refine ⟨s * t, a • D', Submodule.smul_mem_smul ha trivial, ?_⟩
      rw [Submodule.coe_smul, map_smul, ← e'', ← algebraMap_smul B a, ← e, ← algebraMap_smul B (t : A),
        ← algebraMap_smul B ((s * t : Submonoid.powers f) : A), smul_smul, smul_smul, Submonoid.coe_mul, map_mul]
      congr 1
      ring
  obtain ⟨s, D', hD', e⟩ := key
  obtain ⟨c, hc⟩ := exists_pow_smul_eq_of_res_eq (S := B) f φ hφ J ((s : A) • D) D' (Subtype.ext (by
    change extL (S := B) f ((s : A) • D.1) = extL (S := B) f D'.1
    rw [map_smul, e]))
  have h1 : ((c * s : Submonoid.powers f) : A) • D ∈ m • (⊤ : Submodule A (logSub φ J)) := by
    rw [Submonoid.coe_mul, mul_smul]
    have : (c : A) • (s : A) • D = (c : A) • D' := hc
    rw [this]
    exact Submodule.smul_mem _ _ hD'
  have h2 : ((c * s : Submonoid.powers f) : A) ∉ m := by
    obtain ⟨N, hN⟩ := (c * s).2
    rw [← hN]
    exact fun h => hf (hm.isPrime.mem_of_pow_mem N h)
  obtain ⟨y, i, hi, e1⟩ := hm.exists_inv h2
  rw [← one_smul A D, ← e1, add_smul, mul_smul]
  exact add_mem (Submodule.smul_mem _ _ h1) (Submodule.smul_mem_smul hi trivial)

theorem mem_smul_top_of_coords {K A B R : Type} [Field K] [CharZero K] [CommRing A] [CommRing B] [Algebra A B]
    [Algebra K B] [IsNoetherianRing B] [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra ℤ R] (f : A) [IsLocalization.Away f B]
    (φ : K →+* A) (hφ : φ.FiniteType) (hK : (algebraMap A B).comp φ = algebraMap K B) (J m : Ideal A)
    (hm : m.IsMaximal) (hf : f ∉ m) {n r : ℕ} (z : Fin n → B) (bΩ : Module.Basis (Fin n) B Ω[B⁄K])
    (hb : ∀ i, bΩ i = KaehlerDifferential.D K B (z i)) (e : Fin r → Fin n) (he : Function.Injective e)
    (hJ : J.map (algebraMap A B) = Ideal.span {∏ i, z (e i)}) (ψ : B →+* R)
    (hψ : ∀ g ∈ m, ψ (algebraMap A B g) ∈ maximalIdeal R) (D : logSub φ J) (δ : Derivation ℤ R R)
    (hδ : ∀ a, δ (ψ (algebraMap A B a)) = ψ (algebraMap A B (D.1 a))) (h0 : ∀ x, δ x ∈ maximalIdeal R)
    (h1 : ∀ i, ψ (z (e i)) ≠ 0 ∧ ∃ α ∈ maximalIdeal R, δ (ψ (z (e i))) = α * ψ (z (e i))) :
    D ∈ m • (⊤ : Submodule A (logSub φ J)) := by
  have hcomm : ∀ y, ψ (extL (S := B) f D.1 y) = δ (ψ y) := by
    intro y
    obtain ⟨⟨a, t⟩, e⟩ := IsLocalization.surj (Submonoid.powers f) y
    have hu : IsUnit (ψ (algebraMap A B t)) := (IsLocalization.map_units B t).map ψ
    have e' : y * algebraMap A B t = algebraMap A B a := e
    have h1 := congrArg (fun y => ψ (extL (S := B) f D.1 y)) e'
    have h2 := congrArg (fun y => δ (ψ y)) e'
    simp only [Derivation.leibniz, smul_eq_mul, map_mul, map_add, extL_algebraMap, hδ] at h1 h2
    exact hu.mul_left_cancel (by linear_combination h1 - h2)
  have hD : extL (S := B) f D.1 ∈ logSub (algebraMap K B) (Ideal.span {∏ i, z (e i)}) := by
    rw [← hK, ← hJ]
    exact (res (S := B) f φ J D).2
  obtain ⟨g, v, hg, hv, hs⟩ := exists_sum_of_coords (maximalIdeal R) z bΩ hb e he ψ _ hD
    (fun y => hcomm y ▸ h0 _) (fun i c hc => by
      obtain ⟨hne, α, hα, e1⟩ := h1 i
      rw [← hcomm, hc, map_mul] at e1
      exact mul_right_cancel₀ hne e1 ▸ hα)
  refine mem_smul_top_of_sum f φ hφ J m hm hf D g v (fun k => ?_) (fun k => by rw [hK, hJ]; exact hv k) hs
  obtain ⟨⟨a, t⟩, e⟩ := IsLocalization.surj (Submonoid.powers f) (g k)
  have e' : g k * algebraMap A B t = algebraMap A B a := e
  refine ⟨t, a, ?_, e'⟩
  have hle : m = (maximalIdeal R).comap (ψ.comp (algebraMap A B)) :=
    hm.eq_of_le (Ideal.comap_ne_top _ (maximalIdeal.isMaximal R).ne_top) hψ
  rw [hle, Ideal.mem_comap, RingHom.comp_apply, ← e', map_mul]
  exact Ideal.mul_mem_right _ _ (hg k)

end Algebra

section Geometry

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.LogBasis GlobalTheory.LogDerProj GlobalTheory.ZH.CrdCalc
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

theorem mem_basicOpen_iff {R : Type} [CommRing R] {X : Scheme.{0}} (χ : Sp R ⟶ X) (W : X.Opens) (h : ⊤ ≤ χ ⁻¹ᵁ W)
    (g : Γ(X, W)) (q : Sp R) : χ q ∈ X.basicOpen g ↔ valHom χ W h g ∉ q.asIdeal := by
  have b := Scheme.basicOpen_appLE χ ⊤ W h g
  rw [top_inf_eq, basicOpen_eq_of_affine'] at b
  change q ∈ χ ⁻¹ᵁ X.basicOpen g ↔ _
  rw [← b]
  rfl

theorem mem_smul_top_of_chart {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (p : X ⟶ Sp K) (n : ℕ)
    [SmoothOfRelativeDimension n p] (Z : Closeds X) (hI : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal Z))
    (U : X.affineOpens) (D : LogKS.logDer p (Scheme.IdealSheafData.vanishingIdeal Z) U) (m : Ideal Γ(X, U.1))
    (hm : m.IsMaximal) {R ι : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra ℤ R] [Fintype ι] (χ : Sp R ⟶ X)
    (hx : χ (closedPoint R) ∈ U.1) (hxm : ∀ f ∈ m, χ (closedPoint R) ∉ X.basicOpen f)
    (T a : ι → R) (hT : ∀ i, Prime (T i)) (hZ : ∀ q : Sp R, χ q ∈ Z → ∏ i, T i ∈ q.asIdeal)
    (δ : Derivation ℤ R R) (hδ : ∀ r, δ (valR χ U.1 r) = valR χ U.1 (D.1 r)) (hδT : ∀ i, δ (T i) = a i * T i)
    (h0 : ∀ r, δ r ∈ maximalIdeal R) (ha : ∀ i, a i ∈ maximalIdeal R) :
    D ∈ m • (⊤ : Submodule Γ(X, U.1) (LogKS.logDer p (Scheme.IdealSheafData.vanishingIdeal Z) U)) := by
  classical
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hIdef : I = Scheme.IdealSheafData.vanishingIdeal Z := rfl
  haveI : Smooth p := SmoothOfRelativeDimension.smooth n p
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨-, O, hxO, r, s, J, hrsp, hO⟩ := hI (χ (closedPoint R))
  obtain ⟨V, hV, e, hxV, he, H⟩ := exists_coords p n _ O.1 hxO s hrsp
  obtain ⟨f, hfV, hxf⟩ := U.2.exists_basicOpen_le ⟨_, hxV⟩ hx
  let W : X.affineOpens := ⟨X.basicOpen f, U.2.basicOpen f⟩
  obtain ⟨z, bΩ, hz, hb⟩ := H W.1 hfV W.2
  let ix : Fin J.card → Fin r := fun i => (J.equivFin.symm i).1
  have hix : Function.Injective ix := fun i j h => J.equivFin.symm.injective (Subtype.ext h)
  have hWO : W ≤ O := hfV.trans hV
  have hideal : I.ideal W = Ideal.span {∏ i, z (e (ix i))} := by
    rw [← I.map_ideal hWO, hIdef, hO, Ideal.map_span, Set.image_singleton, map_prod, ← Finset.prod_coe_sort J,
      ← J.equivFin.symm.prod_comp]
    simp only [hz]
    rfl
  have hW : W.1 ≤ U.1 := X.basicOpen_le f
  letI : Algebra K Γ(X, W.1) := (algX p W.1).toAlgebra
  haveI : IsNoetherianRing Γ(X, W.1) := IsLocallyNoetherian.component_noetherian W
  letI : Algebra Γ(X, U.1) Γ(X, W.1) := (resG X hW).toAlgebra
  haveI : IsLocalization.Away f Γ(X, W.1) := U.2.isLocalization_basicOpen f
  have hφ : (algX p U.1).FiniteType := by
    have h1 : (p.appLE ⊤ U.1 (by simp)).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ U _
    exact h1.comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.surjective)
  have hχ : ⊤ ≤ χ ⁻¹ᵁ W.1 := (top_le_iff χ W.1).2 hxf
  have hχU : ⊤ ≤ χ ⁻¹ᵁ U.1 := (top_le_iff χ U.1).2 hx
  have hval : ∀ g, valHom χ W.1 hχ (algebraMap Γ(X, U.1) Γ(X, W.1) g) = valR χ U.1 g := fun g =>
    (valR_eq χ W.1 hχ _).symm.trans (valR_res χ hW hχ g)
  refine mem_smul_top_of_coords (K := K) (B := Γ(X, W.1)) f (algX p U.1) hφ (GlobalTheory.TopForm.resG_comp_algX p hW)
    (I.ideal U) m hm (fun h => hxm f h hxf) z bΩ hb (e ∘ ix) (he.comp hix)
    ((I.map_ideal (U := W) (V := U) hW).trans hideal) (valHom χ W.1 hχ) (fun g hg => ?_) D δ
    (fun g => by rw [hval, hval]; exact hδ g) h0 (fun i => ?_)
  · rw [hval]
    exact fun hu => hxm g hg ((top_le_iff χ _).1 ((isUnit_valR_iff χ U.1 hχU g).1 hu))
  · have hrad : ∏ i, T i ∈ (Ideal.span {valHom χ W.1 hχ (z (e (ix i)))}).radical := by
      rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
      rintro P ⟨hP, hP'⟩
      let q : Sp R := (⟨P, hP'⟩ : PrimeSpectrum R)
      refine hZ q ?_
      have hq : χ q ∈ I.support := by
        rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := W) (hχ (Set.mem_univ q)), hideal,
          Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff]
        rintro _ rfl
        rw [mem_basicOpen_iff χ W.1 hχ, not_not, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
        exact Ideal.mul_mem_right _ _ (hP (Ideal.mem_span_singleton_self _))
      have hs : (I.support : Set X) = Z := by
        rw [hIdef, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      change χ q ∈ (Z : Set X)
      rw [← hs]
      exact hq
    obtain ⟨N, hN⟩ := hrad
    have hdvd := Ideal.mem_span_singleton.1 hN
    refine ⟨ne_zero_of_dvd_ne_zero (pow_ne_zero N (Finset.prod_ne_zero_iff.2 fun j _ => (hT j).ne_zero)) hdvd,
      exists_log_of_dvd _ δ h0 T a hT ha hδT N _ hdvd⟩

end Geometry

end GlobalTheory.LogBack

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
open GlobalTheory.LocM GlobalTheory.PolFan ReciprocityTheory.AnForm.R
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartDer

theorem GlobalTheory.LogBack.mem_smul_top_of_vanish : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension Dw.dim (genStr Y) → FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → ∀ x : Y.X, x ∉ interior Y → x ∈ U.1 → (∀ f ∈ m, x ∉ Y.X.basicOpen f) → ∀ (k : Type) [Field k] (m' d : ℕ) (ξ : Sp (ChartRing k m' d) ⟶ gen Y) (x' : gen Y), ξ (closedPoint _) = x' → genι Y x' = x → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → (FinalTheorems.stalkId (genBdIdeal Y) (ξ (closedPoint _))).map (Scheme.stalkClosedPointTo ξ).hom = Ideal.span {∏ i, bdParam k m' d i} → (∀ p : Sp (ChartRing k m' d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m' d i ∈ p.asIdeal) → ∀ (hU : ⊤ ≤ (ξ ≫ genι Y) ⁻¹ᵁ U.1) (DR : Derivation ℤ (ChartRing k m' d) (ChartRing k m' d)) (a : Fin m' → (ChartRing k m' d)), (∀ r, DR (valR (ξ ≫ genι Y) U.1 r) = valR (ξ ≫ genι Y) U.1 (D.1 r)) → (∀ i, DR (bdParam k m' d i) = a i * bdParam k m' d i) → (∀ r, residue _ (DR r) = 0) → (∀ i, residue _ (a i) = 0) → D ∈ m • (⊤ : Submodule Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U)) := by
  intro E _ _ _ H Dw l Xo c Y hs hsnc U D m hm x _ hxU hxm k _ m' d ξ x' hξ hx' _ _ hbd _ DR a hD hT h0 ha
  haveI := smooth_gen_iff.1 hs
  subst hξ hx'
  refine GlobalTheory.LogBack.mem_smul_top_of_chart Y.s Dw.dim (interior Y).compl (snc_gen_iff.1 hsnc) U D m hm (ξ ≫ genι Y)
    hxU hxm (bdParam k m' d) a (fun i => GlobalTheory.LogBack.prime_X _) (fun q hq => (hbd q).1 ?_) DR hD hT
    (fun r => (residue_eq_zero_iff _).1 (h0 r)) (fun i => (residue_eq_zero_iff _).1 (ha i))
  rw [mem_genBd_iff, ← coe_interior]
  exact hq
