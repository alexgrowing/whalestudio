import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExactOfTieLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSubOneWittTensorLatticeSurjectiveFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubOfMemSpan

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.EtaleExact TensorProduct

namespace GlobalTheory.EtaleSub

theorem powerSeries_cases {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) (g : PowerSeries O) :
    (∃ w, g = PowerSeries.C ϖ * w) ∨
      ∃ (k : ℕ) (u w : PowerSeries O), IsUnit u ∧ g = u * PowerSeries.X ^ k + PowerSeries.C ϖ * w := by
  classical
  have key : ∀ f : PowerSeries O, (∀ k, ϖ ∣ PowerSeries.coeff k f) → ∃ w, f = PowerSeries.C ϖ * w := by
    intro f hf
    choose c hc using hf
    exact ⟨PowerSeries.mk c, by ext k; simp [hc]⟩
  by_cases h : ∀ k, ϖ ∣ PowerSeries.coeff k g
  · exact Or.inl (key g h)
  right
  push_neg at h
  have hk : IsUnit (PowerSeries.coeff (Nat.find h) g) := by
    by_contra hn
    apply Nat.find_spec h
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
    exact hn
  obtain ⟨w, hw⟩ := key (PowerSeries.trunc (Nat.find h) g : Polynomial O) fun i => by
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with hi
    · exact not_not.1 (Nat.find_min h hi)
    · exact dvd_zero _
  refine ⟨Nat.find h, PowerSeries.mk fun i => PowerSeries.coeff (i + Nat.find h) g, w, ?_, ?_⟩
  · rw [PowerSeries.isUnit_iff_constantCoeff]
    simpa using hk
  · rw [← hw]
    exact PowerSeries.eq_shift_mul_X_pow_add_trunc _ g

theorem letter_cases {O E : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) [CommRing E] (n : ℕ) (p : ℕ) (hp0 : (p : O) ≠ 0) (hp1 : ¬ IsUnit (p : O))
    (a : LetA O n →+* E) (hπ : IsUnit (a letπ)) [IsAdicComplete (Ideal.span {(p : E)}) E]
    (hd : ∀ x : E, ∃ (f : LetA O n) (r : ℕ), x * a (letπ ^ r) - a f ∈ Ideal.span {(p : E)})
    (i : ZMod n) (x : E) :
    a (letE i) * x = 0 ∨ ∃ (k : ℕ) (u : E), IsUnit u ∧
      a (letE i) * x = a (letE i) * a (fun _ => PowerSeries.C ϖ) ^ k * u := by
  classical
  let ψ : PowerSeries O →+* E := a.comp (Pi.constRingHom (ZMod n) (PowerSeries O))
  have hψ : ∀ f : LetA O n, a (letE i) * a f = a (letE i) * ψ (f i) := by
    intro f
    change _ = a (letE i) * a (Function.const _ (f i))
    rw [← map_mul, ← map_mul]
    congr 1
    funext k
    by_cases hk : k = i
    · subst hk; simp [letE]
    · simp [letE, hk]
  have hidem : a (letE i) * a (letE i) = a (letE i) := by
    rw [hψ]; simp [letE]
  change _ ∨ ∃ (k : ℕ) (u : E), IsUnit u ∧ a (letE i) * x = a (letE i) * ψ (PowerSeries.C ϖ) ^ k * u
  set e := a (letE i)
  set w := ψ (PowerSeries.C ϖ) with hw
  obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  have hm : m ≠ 0 := by
    rintro rfl
    exact hp1 (by rw [hv]; simp)
  have hpE : (p : E) = ψ (PowerSeries.C (v : O)) * w ^ m := by
    rw [hw, ← map_pow, ← map_mul, ← map_pow, ← map_mul, ← hv, map_natCast, map_natCast]
  have hvu : IsUnit (ψ (PowerSeries.C (v : O))) := (v.isUnit.map _).map _
  have hwp : w ∣ (p : E) := by
    rw [hpE]; exact Dvd.dvd.mul_left (dvd_pow_self w hm) _
  have hpw : (p : E) ∣ w ^ m := by
    rw [hpE]; exact hvu.mul_left_dvd.2 dvd_rfl
  have hjac : w ∈ Ideal.jacobson (⊥ : Ideal E) := by
    have h1 : w ^ m ∈ Ideal.jacobson (⊥ : Ideal E) :=
      IsAdicComplete.le_jacobson_bot (Ideal.span {(p : E)}) (Ideal.mem_span_singleton.2 hpw)
    have h2 : w ∈ (Ideal.jacobson (⊥ : Ideal E)).radical := ⟨m, h1⟩
    have h3 := Ideal.radical_le_jacobson h2
    rwa [Ideal.jacobson_idem] at h3
  have hXu : IsUnit (ψ PowerSeries.X) := hπ
  have step : ∀ y : E, w ∣ e * y ∨ ∃ u, IsUnit u ∧ e * y = e * u := by
    intro y
    obtain ⟨f, r, hf⟩ := hd y
    obtain ⟨z, hz⟩ := hwp.trans (Ideal.mem_span_singleton.1 hf)
    have hr : IsUnit (a (letπ ^ r)) := by rw [map_pow]; exact hπ.pow r
    have h1 : e * y * a (letπ ^ r) = e * (ψ (f i) + w * z) := by
      rw [mul_add, ← hψ, ← hz]; ring
    rcases powerSeries_cases hϖ (f i) with ⟨g, hg⟩ | ⟨k, u, g, hu, hg⟩
    · left
      rw [← hr.dvd_mul_right, h1, hg, map_mul]
      exact ⟨e * (ψ g + z), by ring⟩
    · right
      obtain ⟨s, hs⟩ := (hu.map ψ).mul (hXu.pow k)
      obtain ⟨t, ht⟩ := hr
      have h2 : IsUnit (ψ (f i) + w * z) := by
        have h3 := (Ideal.mem_jacobson_bot.1 hjac ((ψ g + z) * ↑s⁻¹)).mul s.isUnit
        convert h3 using 1
        rw [hg, map_add, map_mul, map_mul, map_pow, ← hs, add_mul, mul_assoc, mul_assoc,
          Units.inv_mul]
        ring
      refine ⟨(ψ (f i) + w * z) * ↑t⁻¹, h2.mul t⁻¹.isUnit, ?_⟩
      rw [← mul_assoc, ← h1, ← ht, mul_assoc, Units.mul_inv, mul_one]
  by_cases h : ∀ k : ℕ, w ^ k ∣ e * x
  · left
    refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(p : E)}) E) _ fun k => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact (pow_dvd_pow_of_dvd hpw k).trans (by rw [← pow_mul]; exact h _)
  · right
    push_neg at h
    obtain ⟨k, hk⟩ : ∃ k, Nat.find h = k + 1 := Nat.exists_eq_succ_of_ne_zero fun h0 => by
      have := Nat.find_spec h
      rw [h0] at this
      simp at this
    have h1 := Nat.find_spec h
    rw [hk] at h1
    obtain ⟨y, hy⟩ : w ^ k ∣ e * x := not_not.1 (Nat.find_min h (by omega))
    have h2 : e * x = w ^ k * (e * y) := by
      rw [← hidem, mul_assoc, hy, hidem]; ring
    rcases step y with ⟨z, hz⟩ | ⟨u, hu, hz⟩
    · exact absurd ⟨z, by rw [h2, hz]; ring⟩ h1
    · exact ⟨k, u, hu, by rw [h2, hz]; ring⟩

section Sub

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]

theorem exists_subLat [IsDomain O] [IsPrincipalIdealRing O] (T : LocLat G Qp LL O)
    (S : Submodule O ↥T.L.T) (hS : ∀ g, ∀ x ∈ S, T.actT g x ∈ S) :
    ∃ (T' : LocLat G Qp LL O) (ι : LatHom T'.L T.L), Function.Injective ι.f ∧
      LinearMap.range (latMap ι) = S := by
  haveI := T.L.free
  haveI : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg
  let S₁ : Submodule O T.V := S.map T.L.T.subtype
  have hle : S₁ ≤ T.L.T := Submodule.map_subtype_le _ _
  let V' : Submodule LL T.V := Submodule.span LL (S₁ : Set T.V)
  have hS₁ : ∀ g, ∀ x ∈ S₁, T.ρ g x ∈ S₁ := by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨_, hS g x hx, rfl⟩
  have hV' : ∀ g, V' ≤ V'.comap (T.ρ g) := fun g =>
    Submodule.span_le.2 fun x hx => Submodule.subset_span (hS₁ g x hx)
  let ρ' : Representation LL G V' := T.ρ.subrepresentation V' hV'
  let S₂ : Submodule O V' := S₁.comap (V'.subtype.restrictScalars O)
  let e : S₂ ≃ₗ[O] S :=
    { toFun := fun x => ⟨⟨x.1.1, hle x.2⟩, by
        obtain ⟨y, hy, hy'⟩ := x.2
        have : (⟨x.1.1, hle x.2⟩ : ↥T.L.T) = y := Subtype.ext hy'.symm
        rw [this]
        exact hy⟩
      invFun := fun y => ⟨⟨y.1.1, Submodule.subset_span ⟨y.1, y.2, rfl⟩⟩, ⟨y.1, y.2, rfl⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  letI : TopologicalSpace V' := moduleTopology LL V'
  haveI : IsModuleTopology LL V' := ⟨rfl⟩
  haveI : ContinuousAdd V' := IsModuleTopology.toContinuousAdd LL V'
  haveI : ContinuousSMul LL V' := IsModuleTopology.toContinuousSMul LL V'
  haveI : ContinuousSMul LL T.V := IsModuleTopology.toContinuousSMul LL T.V
  obtain ⟨r, hr⟩ := V'.subtype.exists_leftInverse_of_injective V'.ker_subtype
  have hrc : Continuous r := IsModuleTopology.continuous_of_linearMap r
  let T' : LocLat G Qp LL O :=
    { V := V'
      ρ := ρ'
      cont := fun x => by
        have : (fun g => ρ' g x) = fun g => r (T.ρ g x) :=
          funext fun g => (LinearMap.congr_fun hr (ρ' g x)).symm
        rw [this]
        exact hrc.comp (T.cont x)
      L :=
        { T := S₂
          stable := fun g x hx => hS₁ g _ hx
          fg := Module.Finite.iff_fg.1 (Module.Finite.equiv e.symm)
          free := Module.Free.of_equiv e.symm
          span := by
            apply Submodule.map_injective_of_injective V'.injective_subtype
            rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
            congr 1
            ext x
            exact ⟨fun ⟨y, hy, h⟩ => h ▸ hy, fun hx => ⟨⟨x, Submodule.subset_span hx⟩, hx, rfl⟩⟩ } }
  refine ⟨T', ⟨V'.subtype, fun _ _ => rfl, IsModuleTopology.continuous_of_linearMap V'.subtype,
    fun x hx => hle hx⟩, V'.injective_subtype, ?_⟩
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (e y).2
  · intro hx
    exact ⟨e.symm ⟨x, hx⟩, rfl⟩

end Sub

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)

theorem faithfullyFlat_of_tie [IsDomain O] [IsDiscreteValuationRing O] (hp0 : (PD.p : O) ≠ 0)
    (hp1 : ¬ IsUnit (PD.p : O)) (hsep : ∀ x : RW, (∀ k : ℕ, (PD.p : RW) ^ k ∣ x) → x = 0)
    (htor : ∀ x : RW, (PD.p : RW) * x = 0 → x = 0) :
    letI := E.ioE.toRingHom.toAlgebra
    Module.FaithfullyFlat W.EE RW := by
  classical
  letI := E.ioE.toRingHom.toAlgebra
  haveI := PD.finK₀
  haveI : NeZero n := ⟨by rw [W.n_eq]; exact Module.finrank_pos.ne'⟩
  haveI := W.EE_complete
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖp : ϖ ∣ (PD.p : O) := by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
    exact hp1
  haveI : Module.Flat W.EE RW := by
    refine flat_of_letters (fun i : ZMod n => algebraMap (LetA O n) W.EE (letE i)) ?_ ?_
      (algebraMap (LetA O n) W.EE fun _ => PowerSeries.C ϖ)
      (letter_cases hϖ n PD.p hp0 hp1 _ W.EE_π fun x => by simpa using W.EE_dense x 1) ?_
    · have h1 : ∑ i, (letE i : LetA O n) = 1 := by
        funext k
        simp [letE, Finset.sum_apply, Pi.single_apply]
      rw [← map_sum, h1, map_one]
    · intro i
      rw [← map_mul]
      congr 1
      funext k
      by_cases hk : k = i
      · subst hk; simp [letE]
      · simp [letE, hk]
    · intro m hm
      have h1 : algebraMap (LetA O n) W.EE (fun _ => PowerSeries.C ϖ) = algebraMap O W.EE ϖ := by
        rw [IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
        rfl
      rw [h1, Algebra.smul_def] at hm
      have h2 : algebraMap O RW ϖ * m = 0 := by
        rw [← E.ioE.commutes]; exact hm
      obtain ⟨c, hc⟩ := hϖp
      refine htor m ?_
      rw [← map_natCast (algebraMap O RW), hc, map_mul, mul_right_comm, h2, zero_mul]
  refine ⟨fun m hm htop => ?_⟩
  refine map_ne_top_of_tie E (fun c => ?_) hsep m hm ?_
  · by_cases hc : IsUnit c
    · exact Or.inl hc
    · right
      obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
      refine ⟨k, ?_⟩
      rw [hu, Units.isUnit u |>.mul_left_dvd]
      refine pow_dvd_pow_of_dvd ?_ k
      rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
      exact hc
  · rw [Ideal.smul_top_eq_map] at htop
    rw [Ideal.eq_top_iff_one]
    exact (htop ▸ Submodule.mem_top : (1 : RW) ∈ (m.map (algebraMap W.EE RW)).restrictScalars W.EE)

theorem mem_of_jD_mem_span
    (hff : letI := E.ioE.toRingHom.toAlgebra; Module.FaithfullyFlat W.EE RW)
    (T : LocLat G Qp LL O) (N : Submodule W.EE (W.DD T)) (x : W.DD T)
    (hx : E.jD T x ∈ Submodule.span RW (E.jD T '' (N : Set (W.DD T)))) : x ∈ N := by
  letI := E.ioE.toRingHom.toAlgebra
  haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial
  haveI := T.L.free
  haveI := (W.DD_free T).1
  haveI := finite_DD E T
  refine mem_of_mem_span_image (R := RW) (E.jD T).toAddMonoidHom (E.jD_smul T)
    (fun _ => ?_) (E.jD_span T) N x hx
  rw [(W.DD_free T).2, Module.finrank_baseChange]

theorem map_mem_span {M : Type} [AddCommGroup M] [Module O M] (f : RW →ₐ[O] RW) (a : M →ₗ[O] M)
    (s : Set (RW ⊗[O] M)) (hs : ∀ x ∈ s, TensorProduct.map f.toLinearMap a x ∈ s) :
    ∀ x ∈ Submodule.span RW s, TensorProduct.map f.toLinearMap a x ∈ Submodule.span RW s := by
  have hsm : ∀ (r : RW) (x : RW ⊗[O] M), TensorProduct.map f.toLinearMap a (r • x) =
      f r • TensorProduct.map f.toLinearMap a x := by
    intro r x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a t => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem z hz => exact Submodule.subset_span (hs z hz)
  | zero => simp
  | add z w _ _ hz hw => rw [map_add]; exact Submodule.add_mem _ hz hw
  | smul r z _ hz => rw [hsm]; exact Submodule.smul_mem _ _ hz

theorem exists_sub_of_tie [IsDomain O] [IsPrincipalIdealRing O]
    (hff : letI := E.ioE.toRingHom.toAlgebra; Module.FaithfullyFlat W.EE RW)
    (hs : ∀ y, ∃ b, φR b - b = y)
    (hI : ∀ I : Ideal RW, (∀ x ∈ I, φR x ∈ I) → I ≤ Ideal.span {x | x ∈ I ∧ φR x = x})
    (T : LocLat G Qp LL O) (hfix : ∀ b, TWmap φR T b = b → ∃ t : ↥T.L.T, b = (1 : RW) ⊗ₜ[O] t)
    (D' : Submodule W.EE (W.DD T)) (hφ : ∀ x ∈ D', W.φD T x ∈ D')
    (hγ : ∀ g, ∀ x ∈ D', W.γD T g x ∈ D') :
    ∃ (T' : LocLat G Qp LL O) (ι : LatHom T'.L T.L), Function.Injective ι.f ∧
      LinearMap.range (W.map ι) = D' := by
  haveI := T.L.free
  haveI : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg
  set U := Submodule.span RW (E.jD T '' (D' : Set (W.DD T))) with hU
  have hUφ : ∀ x ∈ U, TWmap φR T x ∈ U := map_mem_span φR _ _ (by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨_, hφ x hx, E.jD_φ T x⟩)
  have hUg : ∀ g, ∀ x ∈ U, TWact (gR g) T g x ∈ U := fun g => map_mem_span (gR g) _ _ (by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨_, hγ _ x hx, E.jD_act T g x⟩)
  let S : Submodule O ↥T.L.T := (U.restrictScalars O).comap (TensorProduct.mk O RW ↥T.L.T 1)
  have hSm : ∀ t, t ∈ S ↔ (1 : RW) ⊗ₜ[O] t ∈ U := fun t => Iff.rfl
  obtain ⟨T', ι, hι, hr⟩ := exists_subLat T S fun g x hx => by
    have := hUg g _ ((hSm x).1 hx)
    rw [hSm]
    simpa [TWact] using this
  have hspan : Submodule.span RW (E.jD T '' (LinearMap.range (W.map ι) : Set (W.DD T))) = U := by
    rw [span_range_map]
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r t =>
        have h1 : latMap ι t ∈ S := hr ▸ LinearMap.mem_range_self _ t
        have h2 := U.smul_mem r ((hSm _).1 h1)
        simpa [TensorProduct.smul_tmul'] using h2
      | add x y hx hy => rw [map_add]; exact U.add_mem hx hy
    · refine (tensor_le_span φR hs hI U hUφ).trans (Submodule.span_le.2 ?_)
      rintro x ⟨hx, hx'⟩
      obtain ⟨t, rfl⟩ := hfix x hx'
      obtain ⟨y, rfl⟩ : t ∈ LinearMap.range (latMap ι) := hr ▸ (hSm t).2 hx
      exact ⟨(1 : RW) ⊗ₜ y, rfl⟩
  refine ⟨T', ι, hι, le_antisymm (fun x hx => ?_) (fun x hx => ?_)⟩
  · refine mem_of_jD_mem_span E hff T D' x ?_
    rw [← hU, ← hspan]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  · refine mem_of_jD_mem_span E hff T _ x ?_
    rw [hspan]
    exact Submodule.subset_span ⟨x, hx, rfl⟩

include E in

theorem map_injective_of_tie (hfl : Module.Flat O RW) {T' T : LocLat G Qp LL O}
    (ι : LatHom T'.L T.L) (hι : Function.Injective ι.f) : Function.Injective (W.map ι) := by
  have h1 : Function.Injective (latMap ι) := fun x y hxy =>
    Subtype.ext (hι (congrArg Subtype.val hxy))
  have h2 : Function.Injective ((latMap ι).baseChange RW) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := RW) (latMap ι) h1
  intro x y hxy
  refine E.jD_inj T' (h2 ?_)
  rw [← jD_map', ← jD_map', hxy]

end Generic

section Concrete

variable {l : ℕ} [Fact l.Prime]

theorem ideal_WCb (I : Ideal (WCb l)) : I ≤ Ideal.span {x | x ∈ I ∧ frobW l x = x} := by
  rcases eq_or_ne I ⊥ with rfl | hI
  · exact bot_le
  haveI : PerfectRing (Cb l) l := by
    haveI := (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).1
    infer_instance
  haveI : IsDiscreteValuationRing (WCb l) := WittVector.isDiscreteValuationRing (k := Cb l)
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI
    (WittVector.irreducible l (k := Cb l))
  refine hk.le.trans (Ideal.span_mono ?_)
  rintro _ rfl
  exact ⟨hk ▸ Ideal.mem_span_singleton_self _, by rw [map_pow, map_natCast]⟩

theorem ideal_RW (LL : FinExt l) (I : Ideal (RW LL)) (hI : ∀ x ∈ I, φRW LL x ∈ I) :
    I ≤ Ideal.span {x | x ∈ I ∧ φRW LL x = x} :=
  haveI := free_OL LL
  haveI := finite_OL LL
  ideal_le_span (frobW l) (GlobalTheory.ArtinSchreierWitt.main l).1 (fun I _ => ideal_WCb I) I hI

theorem torsionFree_RW (LL : FinExt l) (x : RW LL) (hx : (l : RW LL) * x = 0) : x = 0 := by
  classical
  haveI := free_OL LL
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := WCb l)
    (Module.Free.chooseBasis ℤ_[l] ↥(OL LL))
  apply e.injective
  rw [map_zero]
  ext i : 1
  have h : e ((l : RW LL) * x) i = 0 := by rw [hx, map_zero]; rfl
  rw [← nsmul_eq_mul, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul] at h
  exact (mul_eq_zero.1 h).resolve_left (WittVector.irreducible l (k := Cb l)).ne_zero

theorem faithfullyFlat_RW {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P} (E : LocFon l P AI H)
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) :
    letI := (E.E K s LL h).tie.ioE.toRingHom.toAlgebra
    Module.FaithfullyFlat (H.W K s LL h).EE (RW LL) := by
  obtain ⟨hdvr, -, h0, h1, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  have hp : (P.PD K).p = l := P.PD_p K
  exact faithfullyFlat_of_tie (E.E K s LL h).tie (by rw [hp]; exact h0) (by rw [hp]; exact h1)
    (by rw [hp]; exact sep_RW LL) (by rw [hp]; exact torsionFree_RW LL)

end Concrete

theorem exists_sublattice : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (H : LocHW l P) (E : LocFon l P AI H) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (D' : Submodule (H.W K s LL h).EE ((H.W K s LL h).DD T)), (∀ x ∈ D', (H.W K s LL h).φD T x ∈ D') → (∀ g, ∀ x ∈ D', (H.W K s LL h).γD T g x ∈ D') → ∃ (T' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T'.L T.L), Function.Injective ι.f ∧ LinearMap.range ((H.W K s LL h).map ι) = D' := by
  intro l _ P AI H E K s LL h T D' hφ hγ
  obtain ⟨hdvr, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  exact exists_sub_of_tie (E.E K s LL h).tie (faithfullyFlat_RW E K s LL h)
    (GlobalTheory.WittTensorFixed.ring_fixed l LL).1 (ideal_RW LL) T
    (fun b hb => ((GlobalTheory.WittTensorFixed.main l K LL T).2.1 b).1 hb) D' hφ hγ

private theorem flat_of_inj {R A : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [CommRing A] [IsDomain A] [Algebra R A] (h : Function.Injective (algebraMap R A)) :
    Module.Flat R A := by
  haveI : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective _ _).2 h
  infer_instance

theorem flat_RW {l : ℕ} [Fact l.Prime] (LL : FinExt l) : Module.Flat ↥(OL LL) (RW LL) := by
  haveI : Module.Flat ℤ_[l] (WCb l) :=
    flat_of_inj (GlobalTheory.WittTensorFixed.algebraMap_WCb_injective l)
  exact Module.Flat.baseChange ℤ_[l] ↥(OL LL) (WCb l)

theorem map_injective {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P}
    (E : LocFon l P AI H) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    {T' T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)} (ι : LatHom T'.L T.L)
    (hι : Function.Injective ι.f) : Function.Injective ((H.W K s LL h).map ι) :=
  map_injective_of_tie (E.E K s LL h).tie (flat_RW LL) ι hι

end GlobalTheory.EtaleSub
