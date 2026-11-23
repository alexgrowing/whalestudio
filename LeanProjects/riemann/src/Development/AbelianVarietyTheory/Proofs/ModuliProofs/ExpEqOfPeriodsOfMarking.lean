import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant

open Filter Topology Set

namespace GlobalTheory.ExpUnique

section Lift

variable {V : Type*} [AddCommGroup V] {Q : Type*} [Group Q] {e : V → Q}

theorem hom_zero (he : ∀ z w, e (z + w) = e z * e w) : e 0 = 1 := by
  have h := he 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem hom_sub (he : ∀ z w, e (z + w) = e z * e w) (z w : V) : e (z - w) = e z * (e w)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, ← he, sub_add_cancel]

theorem hom_eq_iff (he : ∀ z w, e (z + w) = e z * e w) {Λ : Set V} (hk : ∀ z, e z = 1 ↔ z ∈ Λ) (z w : V) :
    e z = e w ↔ z - w ∈ Λ := by
  rw [← hk, hom_sub he, mul_inv_eq_one]

end Lift

theorem isClosed_of_closed_near_zero {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (Γ : AddSubgroup G) (h : ∀ᶠ p in 𝓝 (0 : G), p ∈ closure (Γ : Set G) → p ∈ Γ) : IsClosed (Γ : Set G) := by
  refine isClosed_of_closure_subset fun p hp => ?_
  have ht : Tendsto (fun q => p - q) (𝓝 p) (𝓝 0) := by
    simpa using (continuous_sub_left p).tendsto p
  obtain ⟨q, hq, hqΓ⟩ := mem_closure_iff_nhds.1 hp _ (ht.eventually h)
  have h1 : p - q ∈ Γ.topologicalClosure := Γ.topologicalClosure.sub_mem hp (Γ.le_topologicalClosure hqΓ)
  simpa using Γ.add_mem (hq h1) hqΓ

theorem exists_realLinear_lift {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] {Q : Type*} [Group Q] {e e' : V → Q}
    (he : ∀ z w, e (z + w) = e z * e w) (he' : ∀ z w, e' (z + w) = e' z * e' w) (hs : Function.Surjective e)
    (hk : ∀ z, e z = 1 ↔ z ∈ Λ)
    (hc : ∀ᶠ p : V × V in 𝓝 0, p ∈ closure {p : V × V | e' p.1 = e p.2} → e' p.1 = e p.2) :
    ∃ h : V →L[ℝ] V, ∀ z, e (h z) = e' z := by
  have hiff : ∀ z w, e z = e w ↔ Λ.mkQ z = Λ.mkQ w := fun z w =>
    (hom_eq_iff he (Λ := Λ) hk z w).trans (Submodule.Quotient.eq Λ).symm
  choose s hs using fun z => hs (e' z)
  let Γ : AddSubgroup (V × V) :=
    { carrier := {p | e' p.1 = e p.2}
      zero_mem' := (hom_zero he').trans (hom_zero he).symm
      add_mem' := fun {a b} (ha : _ = _) (hb : _ = _) => by
        show e' (a.1 + b.1) = e (a.2 + b.2)
        rw [he, he', ha, hb]
      neg_mem' := fun {a} (ha : _ = _) => by
        show e' (-a.1) = e (-a.2)
        rw [← zero_sub, ← zero_sub a.2, hom_sub he, hom_sub he', ha, hom_zero he, hom_zero he'] }
  have hΓ : IsClosed (Γ : Set (V × V)) := isClosed_of_closed_near_zero Γ hc
  let Φ : V →+ V ⧸ Λ := AddMonoidHom.mk' (fun z => Λ.mkQ (s z)) fun a b => by
    rw [← map_add, ← hiff, he, hs, hs, hs, he']
  have : CompactSpace (V ⧸ Λ) := ⟨by
    rw [← Λ.mkQ_surjective.range_eq]
    exact IsZLattice.isCompact_range_of_periodic Λ _ Λ.isOpenQuotientMap_mkQ.continuous fun z w hw => by
      rw [map_add, Submodule.mkQ_apply Λ w, (Submodule.Quotient.mk_eq_zero Λ).2 hw, add_zero]⟩
  have hG : IsClosed {p : V × (V ⧸ Λ) | Φ p.1 = p.2} := by
    rw [← (IsOpenQuotientMap.id.prodMap Λ.isOpenQuotientMap_mkQ).isQuotientMap.isClosed_preimage]
    convert hΓ using 1
    ext p
    show Λ.mkQ (s p.1) = Λ.mkQ p.2 ↔ e' p.1 = e p.2
    rw [← hiff, hs]
  have hΦ : Continuous Φ := continuous_iff_isClosed.2 fun C hC => by
    convert isClosedMap_fst_of_compactSpace _ (hG.inter (hC.preimage continuous_snd)) using 1
    ext z
    exact ⟨fun hz => ⟨(z, Φ z), ⟨rfl, hz⟩, rfl⟩, by
      rintro ⟨p, ⟨h1, h2⟩, rfl⟩
      show Φ p.1 ∈ C
      rw [h1]
      exact h2⟩
  obtain ⟨h, hh, -⟩ := existsUnique_realLinear_lift (ex := Φ) (isDiscrete_ker_mkQ Λ) (Λ.isOpenMap_mkQ.nhds_le 0)
    hΦ.continuousAt
  exact ⟨h, fun z => ((hiff _ _).2 (hh z)).trans (hs z)⟩

theorem isBounded_sublevel {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {q : V → ℝ} (hq : Continuous q) (h2 : ∀ (r : ℝ) z, q (r • z) = r ^ 2 * q z) (hp : ∀ z, z ≠ 0 → 0 < q z)
    (c : ℝ) : Bornology.IsBounded {z | q z ≤ c} := by
  have := FiniteDimensional.proper_real V
  obtain ⟨m, hm, hle⟩ := (isCompact_sphere (0 : V) 1).exists_forall_le' hq.continuousOn (a := 0) fun z hz =>
    hp z (by rintro rfl; simp at hz)
  refine (Metric.isBounded_closedBall (x := (0 : V)) (r := max 1 (c / m))).subset fun z (hz : q z ≤ c) => ?_
  rw [mem_closedBall_zero_iff]
  by_contra hlt
  rw [not_le, max_lt_iff, div_lt_iff₀ hm] at hlt
  have h0 : ‖z‖ ≠ 0 := by linarith [hlt.1]
  have h1 := hle (‖z‖⁻¹ • z) (by simp [norm_smul, h0])
  have h3 : q z = ‖z‖ ^ 2 * q (‖z‖⁻¹ • z) := by rw [← h2, smul_inv_smul₀ h0]
  have h4 : ‖z‖ ^ 2 * m ≤ c := (mul_le_mul_of_nonneg_left h1 (sq_nonneg _)).trans (h3 ▸ hz)
  nlinarith [mul_pos hm (sub_pos.2 hlt.1)]

theorem end_eq_one_of_invariant (Y : Type*) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (σ : Module.End ℤ Y) (hi : Function.Injective σ) (q : Y → ℝ) (hq : ∀ c, {y | q y ≤ c}.Finite)
    (hσ : ∀ y, q (σ y) = q y) (M : ℕ) (hM : 3 ≤ M) (h : ∀ y, ∃ z, σ y = y + M • z) : σ = 1 := by
  classical
  let b := Module.Free.chooseBasis ℤ Y
  have hpow : ∀ (n : ℕ) y, q ((σ ^ n) y) = q y := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih => intro y; rw [pow_succ', Module.End.mul_apply, hσ, ih]
  have hS : (Set.univ.pi fun i => {y | q y ≤ q (b i)}).Finite := Set.Finite.pi fun i => hq _
  obtain ⟨m, -, n, -, hmn, hf⟩ := Set.infinite_univ.exists_lt_map_eq_of_mapsTo
    (f := fun (n : ℕ) i => (σ ^ n) (b i)) (t := Set.univ.pi fun i => {y | q y ≤ q (b i)})
    (fun n _ i _ => (hpow n (b i)).le) hS
  have h1 : σ ^ m = σ ^ n := b.ext fun i => congrFun hf i
  refine end_eq_one_of_pow_eq_one_of_congr Y σ (n - m) M (Nat.sub_pos_of_lt hmn) (LinearMap.ext fun y => ?_) hM h
  apply Module.End.iterate_injective hi m
  rw [← Module.End.mul_apply, ← pow_add, Nat.add_sub_cancel' hmn.le, ← h1]
  rfl

end GlobalTheory.ExpUnique

namespace GlobalTheory.ExpUnique

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem point_ext {X : Scheme.{0}} {x x' : Sp ℂ ⟶ X} {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ x' ⁻¹ᵁ U) (hv : ∀ f, valAt' x U f = valAt' x' U f) : x = x' := by
  have e : x.appLE U ⊤ h = x'.appLE U ⊤ h' := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom]
    ext f
    have := hv f
    rwa [valAt'_eq_valAt x h, valAt'_eq_valAt x' h'] at this
  have hV := isAffineOpen_top (Sp ℂ)
  have : IsIso hV.fromSpec := by rw [IsAffineOpen.fromSpec_top]; infer_instance
  rw [← cancel_epi hV.fromSpec, ← hU.SpecMap_appLE_fromSpec x hV h, ← hU.SpecMap_appLE_fromSpec x' hV h', e]

theorem eventually_eq_of_mem_closure {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}
    {e e' : V → (Sp ℂ ⟶ X)} (he : IsHolTo Set.univ e) (he' : IsHolTo Set.univ e') (h0 : e' 0 = e 0) :
    ∀ᶠ p : V × V in 𝓝 0, p ∈ closure {p : V × V | e' p.1 = e p.2} → e' p.1 = e p.2 := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (e 0 (default : PrimeSpectrum ℂ))) isOpen_univ
  have hx0 : ⊤ ≤ e 0 ⁻¹ᵁ U := (top_le_preimage_iff_mem _ _).2 hx
  have h1 : ∀ᶠ p : V × V in 𝓝 0, p.1 ∈ {b ∈ Set.univ | ⊤ ≤ e' b ⁻¹ᵁ U} :=
    (continuous_fst.tendsto (0 : V × V)).eventually ((he' U 0).1.mem_nhds ⟨trivial, by
      show ⊤ ≤ e' 0 ⁻¹ᵁ U
      rw [h0]; exact hx0⟩)
  have h2 : ∀ᶠ p : V × V in 𝓝 0, p.2 ∈ {b ∈ Set.univ | ⊤ ≤ e b ⁻¹ᵁ U} :=
    (continuous_snd.tendsto (0 : V × V)).eventually ((he U 0).1.mem_nhds ⟨trivial, hx0⟩)
  filter_upwards [h1, h2] with p hp1 hp2 hp
  refine point_ext hU hp1.2 hp2.2 fun f => ?_
  have c1 := ((he' U f).2.differentiableAt ((he' U f).1.mem_nhds hp1)).continuousAt
  have c2 := ((he U f).2.differentiableAt ((he U f).1.mem_nhds hp2)).continuousAt
  refine tendsto_nhds_unique_of_frequently_eq (l := 𝓝 p) (c1.tendsto.comp (continuous_fst.tendsto p))
    (c2.tendsto.comp (continuous_snd.tendsto p)) ((mem_closure_iff_frequently.1 hp).mono fun r (hr : _ = _) => ?_)
  show valAt' (e' r.1) U f = valAt' (e r.2) U f
  rw [hr]

theorem map_I_smul {g : ℕ} {X : Scheme.{0}} {e e' : (Fin g → ℂ) → (Sp ℂ ⟶ X)} (he : IsHolTo Set.univ e)
    (he' : IsHolTo Set.univ e') {v : Sp (DualNumber ℂ) ⟶ X} (hv : IsDerivAt0 e 0 v)
    (hu : ∀ w, IsDerivAt0 e w v → w = 0) (h : (Fin g → ℂ) →L[ℝ] (Fin g → ℂ)) (hh : ∀ z, e (h z) = e' z)
    (z : Fin g → ℂ) : h (Complex.I • z) = Complex.I • h z := by
  refine sub_eq_zero.1 (hu _ ⟨hv.1, fun U hU f => (hv.2 U hU f).trans ?_⟩)
  have hx : ⊤ ≤ e 0 ⁻¹ᵁ U := by
    rw [← hv.1, Scheme.Hom.comp_preimage]
    exact fun p _ => hU trivial
  have h0 : e' 0 = e 0 := by rw [← hh, map_zero]
  have d1 := ((he U f).2.differentiableAt ((he U f).1.mem_nhds ⟨trivial, hx⟩)).hasFDerivAt
  have d2 := ((he' U f).2.differentiableAt ((he' U f).1.mem_nhds ⟨trivial, h0 ▸ hx⟩)).hasFDerivAt
  have d3 := HasFDerivAt.comp 0 (f := h) (by rw [map_zero]; exact d1.restrictScalars ℝ) h.hasFDerivAt
  have d4 := (d2.restrictScalars ℝ).unique (by
    convert d3 using 1
    ext z
    show _ = valAt' (e (h z)) U f
    rw [hh])
  have d5 : ∀ w, fderiv ℂ (fun b => valAt' (e' b) U f) 0 w = fderiv ℂ (fun b => valAt' (e b) U f) 0 (h w) :=
    fun w => DFunLike.congr_fun d4 w
  rw [map_zero, map_sub, ← d5, map_smul, map_smul, d5, sub_self]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem eq_self_of_isometry (D : Datum H) (l : Level H) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) (h : (Fin g → ℂ) →L[ℝ] (Fin g → ℂ))
    (hI : ∀ z, h (Complex.I • z) = Complex.I • h z) (φ : D.La → D.La) (hφ : ∀ a, P (φ a) = h (P a))
    (hEF : ∀ a b, D.EF (φ a) (φ b) = D.EF a b) (hO : ∀ (c : 𝓞 E) a, φ (c • a) = c • φ a)
    (hM : ∀ b ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ z, φ b = b + l.M • z)
    (z : Fin g → ℂ) : h z = z := by
  obtain ⟨-, hinj, hd, hspan, Hm, -, hpos, hIm⟩ := hP
  let σ : Module.End ℤ D.La := (AddMonoidHom.mk' φ fun a b => hinj (by simp only [hφ, map_add])).toIntLinearMap
  have hσ : ∀ a, σ a = φ a := fun _ => rfl
  have := D.fin
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : Module.IsTorsionFree ℤ D.La :=
    Function.Injective.moduleIsTorsionFree P hinj fun r m => map_zsmul P r m
  have : Module.Free ℤ D.La := Module.free_of_finite_type_torsion_free'
  let B : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun u v => (hermForm Hm u v).im)
    (fun a b c => by simp [hermForm]) (fun r a b => by simp [hermForm])
    (fun a b c => by simp [hermForm, Matrix.mulVec_add]) (fun r a b => by simp [hermForm, Matrix.mulVec_smul])
  have hB : B.compl₁₂ h.toLinearMap h.toLinearMap = B := by
    refine LinearMap.ext_on_range hspan fun a => LinearMap.ext_on_range hspan fun b => ?_
    show (hermForm Hm (h (P a)) (h (P b))).im = (hermForm Hm (P a) (P b)).im
    rw [← hφ, ← hφ, hIm, hIm, hEF]
  have hq : ∀ u, (hermForm Hm u u).re = B (Complex.I • u) u := fun u => by
    show _ = (hermForm Hm (Complex.I • u) u).im
    simp [hermForm]
  have hbd := isBounded_sublevel (q := fun u => (hermForm Hm u u).re)
    (by unfold hermForm; fun_prop) (fun r u => by
      simp only [hq]
      rw [smul_comm, map_smul, map_smul, LinearMap.smul_apply, smul_smul, sq, smul_eq_mul]) hpos
  have key : σ = 1 := by
    refine end_eq_one_of_invariant D.La σ ((injective_iff_map_eq_zero σ).2 fun a ha => D.unimod.1 ?_)
      (fun a => (hermForm Hm (P a) (P a)).re) (fun c => ?_) (fun a => ?_) l.M l.three_le fun a => ?_
    · ext b
      rw [← hEF, ← hσ, ha, map_zero]
      rfl
    · refine Set.Finite.of_finite_image (f := P) ((Metric.finite_isBounded_inter_isClosed
        (s := P.range) DiscreteTopology.isDiscrete (hbd c) AddSubgroup.isClosed_of_discrete).subset ?_) hinj.injOn
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨ha, a, rfl⟩
    · simp only [hq, hσ, hφ, ← hI]
      exact LinearMap.congr_fun₂ hB _ _
    · obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp l.coprime)
      obtain ⟨z₁, hz₁⟩ := hM (j • a) (Submodule.smul_mem_smul hj trivial)
      obtain ⟨z₂, hz₂⟩ := ObjRigid.exists_eq_nsmul D l.M (i • (φ a - a)) fun b => by
        obtain ⟨w, hw⟩ := hM (H.bar i • b) (Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hi) trivial)
        have h1 := hEF a (H.bar i • b)
        rw [hw, map_add, map_nsmul, nsmul_eq_mul] at h1
        rw [D.adj, map_sub, LinearMap.sub_apply]
        exact ⟨-D.EF (φ a) w, by linarith⟩
      refine ⟨z₂ + z₁, ?_⟩
      rw [hO] at hz₁
      rw [hσ, smul_add, ← hz₂, ← sub_eq_iff_eq_add'.2 hz₁, ← smul_sub, ← add_smul, hij, one_smul, add_sub_cancel]
  have : h.toLinearMap = LinearMap.id := LinearMap.ext_on_range hspan fun a => by
    show h (P a) = P a
    rw [← hφ, ← hσ, key]
    rfl
  exact LinearMap.congr_fun this z

end GlobalTheory.ExpUnique

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open ExpUnique

theorem exp_eq_of_periods_of_marking : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (P : D'.La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ Xo.X) (e e' : (Fin g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)), (D'.p = D.p ∧ D'.q = D.q ∧ ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧ σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν l.A : ℂ) / l.A) ∧ t = f l.M') → (y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧ ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧ (∀ z, e z = 1 ↔ z ∈ (P).range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a))) → (y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧ ((∀ z w, e' (z + w) = e' z * e' w) ∧ Function.Surjective e' ∧ IsHolTo Set.univ (fun z => (e' z).left) ∧ (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e' z).left) w v.left) ∧ (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' 0).left → ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left)) ∧ (∀ z, e' z = 1 ↔ z ∈ (P).range) ∧ (∀ (a : 𝓞 E) z, e' (fun k => ty k (a : E) * z k) = e' z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e' ((k : ℂ)⁻¹ • P a)) (e' ((k : ℂ)⁻¹ • P a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = e' ((l.M : ℂ)⁻¹ • P (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = e' ((l.A : ℂ)⁻¹ • P (t a))) → e = e' := by
  rintro E _ _ _ H D l Xo σ g ty - - - D' t P y e e' ⟨-, -, f, ν, -, hf, -, -, rfl⟩
    ⟨-, hP, ⟨add, onto, hol, dv, du⟩, ker, lin, weil, eta, -⟩ ⟨-, -, ⟨add', -, hol', -, -⟩, ker', lin', weil', eta', -⟩
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hd : DiscreteTopology P.range := hP.2.2.1
  have : DiscreteTopology P.range.toIntSubmodule := hd
  have : IsZLattice ℝ P.range.toIntSubmodule := ⟨hP.2.2.2.1⟩
  obtain ⟨h, hh⟩ := exists_realLinear_lift P.range.toIntSubmodule add add' onto ker <| by
    filter_upwards [eventually_eq_of_mem_closure hol hol' (by rw [hom_zero add, hom_zero add'])] with p hp hc
    refine Over.OverMorphism.ext (hp (closure_mono (fun r hr => ?_) hc))
    exact congrArg (·.left) (show e' r.1 = e r.2 from hr)
  obtain ⟨v, hv, -⟩ := dv 0
  have hI := map_I_smul hol hol' hv (fun w hw => (du v hv.1).unique hw hv) h fun z => congrArg (·.left) (hh z)
  have hn : ∀ (k : ℕ) z, h ((k : ℂ)⁻¹ • z) = (k : ℂ)⁻¹ • h z := fun k z => by
    have : ∀ u : Fin g → ℂ, (k : ℂ)⁻¹ • u = (k : ℝ)⁻¹ • u := fun u => by
      rw [← Complex.coe_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
    rw [this, this, map_smul]
  choose φ hφ using fun a => (ker (h (P a))).1 ((hh _).trans ((ker' _).2 ⟨a, rfl⟩))
  have he' : ∀ (k : ℕ) a, e' ((k : ℂ)⁻¹ • P a) = e ((k : ℂ)⁻¹ • P (φ a)) := fun k a => by rw [← hh, hn, hφ]
  have key := eq_self_of_isometry D' l hP h hI φ hφ (fun a b => ?_) (fun c a => hP.2.1 ?_) fun b hb => ?_
  · exact funext fun z => by rw [← hh, key]
  ·
    rw [← sub_eq_zero]
    refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (d := ((D'.EF (φ a) (φ b) - D'.EF a b).natAbs + 1 : ℕ)) ?_
      (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)
    generalize hk : (D'.EF (φ a) (φ b) - D'.EF a b).natAbs + 1 = k
    have hk0 : 0 < k := hk ▸ Nat.succ_pos _
    have w1 := weil k (φ a) (φ b) (Units.mk0 _ (Complex.exp_ne_zero _)) hk0 rfl
    have w2 := weil' k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk0 rfl
    rw [he', he'] at w2
    have w3 := congrArg Units.val (weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB ℂ y _ _ _ _ _ w1 w2)
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 w3
    refine ⟨-n, Int.cast_injective (α := ℂ) ?_⟩
    have hk1 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk0.ne'
    have h2 := Complex.two_pi_I_ne_zero
    generalize 2 * (Real.pi : ℂ) * Complex.I = c at hn h2
    field_simp at hn
    push_cast
    linear_combination -hn
  ·
    let m : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
      LinearMap.pi fun k => (LinearMap.mulLeft ℝ (ty k (c : E))).comp (LinearMap.proj k)
    have hm : ∀ z, m z = fun k => ty k (c : E) * z k := fun _ => rfl
    have hc : h.toLinearMap ∘ₗ m = m ∘ₗ h.toLinearMap :=
      realLinear_eq_of_sub_mem_discrete (Γ := P.range) DiscreteTopology.isDiscrete fun z =>
        (hom_eq_iff add (Λ := P.range) ker _ _).1 (by
          show e (h (m z)) = e (m (h z))
          rw [hh, hm, hm, lin, lin', hh])
    have hPm : ∀ x, P (c • x) = m (P x) := fun x => funext (hP.1 c x)
    rw [hφ, hPm, hPm, hφ]
    exact LinearMap.congr_fun hc _
  ·
    have hM1 : (l.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
    have hadd : ∀ a b, φ (a + b) = φ a + φ b := fun a b => hP.2.1 (by simp only [hφ, map_add])
    have hns : ∀ (n : ℕ) a, φ (n • a) = n • φ a := fun n a => hP.2.1 (by simp only [hφ, map_nsmul])
    refine Submodule.smul_induction_on hb (fun j hj x _ => ?_) ?_
    · obtain ⟨a, w, rfl⟩ := (hf l.M' (Nat.lcm_pos hM l.A_pos)).2 x
      obtain ⟨r, hr⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
      have ha := Submodule.smul_mem_smul hj (Submodule.mem_top (x := a))
      obtain ⟨z, hz⟩ := (hom_eq_iff add (Λ := P.range) ker _ _).1
        ((he' _ _).symm.trans ((eta' _ ha).symm.trans (eta _ ha)))
      have h1 : φ (f l.M' (j • a)) = f l.M' (j • a) + l.M • z := hP.2.1 (by
        rw [map_add, map_nsmul, hz, ← Nat.cast_smul_eq_nsmul ℂ, ← smul_sub, smul_inv_smul₀ hM1, add_sub_cancel])
      have h2 : j • l.M' • w = l.M • r • j • w := by rw [hr, mul_smul, smul_comm j, smul_comm j]
      refine ⟨z + φ (r • j • w) - r • j • w, ?_⟩
      rw [smul_add, ← map_smul, h2, hadd, h1, hns, smul_sub, smul_add]
      abel
    · rintro x x' ⟨z, hz⟩ ⟨z', hz'⟩
      exact ⟨z + z', by rw [hadd, hz, hz', smul_add, add_add_add_comm]⟩

end GlobalTheory
