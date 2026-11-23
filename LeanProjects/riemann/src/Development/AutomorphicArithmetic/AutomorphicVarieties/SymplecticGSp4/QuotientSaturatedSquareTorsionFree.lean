import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.TanGlob
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ASmooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CotFg
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartRank
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSqz
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.DerHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.DerExtend
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.SpansOfDer
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

section

variable {O A X τ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [AddCommGroup X]
  {𝒜 : X → Submodule O A} {x : A →ₐ[O] O} {wt : τ → X} {φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)}

private noncomputable def powerSeriesCoefficientLinear (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (i : τ) :
    A →ₗ[O] FractionRing O :=
  ((MvPowerSeries.coeff (Finsupp.single i 1)).restrictScalars O) ∘ₗ φ.toLinearMap

private theorem m1bLin_apply (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (i : τ) (f : A) :
    powerSeriesCoefficientLinear φ i f = MvPowerSeries.coeff (Finsupp.single i 1) (φ f) := rfl

private theorem m1bLin_sat (h : IsChart 𝒜 x wt φ) (i : τ) : ∀ f ∈ satSq x, powerSeriesCoefficientLinear φ i f = 0 := by
  classical
  have h2 : ∀ f ∈ RingHom.ker x ^ 2, powerSeriesCoefficientLinear φ i f = 0 := by
    intro f hf
    rw [sq] at hf
    refine Submodule.mul_induction_on hf (fun a ha b hb => ?_) (fun a b ha hb => by rw [map_add, ha, hb, add_zero])
    have ha' : MvPowerSeries.coeff 0 (φ a) = 0 := by
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.const, show x a = 0 from ha, map_zero]
    have hb' : MvPowerSeries.coeff 0 (φ b) = 0 := by
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.const, show x b = 0 from hb, map_zero]
    rw [m1bLin_apply, map_mul, MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single]
    simp [Finset.Nat.antidiagonal_succ, ha', hb']
  rintro f ⟨c, hc, hf⟩
  have := h2 _ hf
  rw [map_smul] at this
  exact (smul_eq_zero.1 this).resolve_left hc

private theorem m1bLin_wt (h : IsChart 𝒜 x wt φ) (i : τ) {j : X} (hij : wt i ≠ j)
    {f : A} (hf : f ∈ 𝒜 j) : powerSeriesCoefficientLinear φ i f = 0 :=
  h.graded j f hf _ (by simpa [Finsupp.weight_single] using hij)

private theorem cotangent_rank_le_weight_count [Fintype τ] (h : IsChart 𝒜 x wt φ) (j : X) :
    Module.rank O (cotLat x 𝒜 j) ≤ (Nat.card {i // wt i = j} : ℕ) := by
  classical
  rw [Nat.card_eq_fintype_card]
  let ψ : cotLat x 𝒜 j →ₗ[O] ({i // wt i = j} → FractionRing O) :=
    LinearMap.pi fun i => ((satSq x).liftQ (powerSeriesCoefficientLinear φ i.1) (m1bLin_sat h i.1)) ∘ₗ (cotLat x 𝒜 j).subtype
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨_, f, hf, rfl⟩ h0
    apply Subtype.ext
    refine (Submodule.Quotient.mk_eq_zero _).2 (h.inj f hf.2 fun i => ?_)
    by_cases hi : wt i = j
    · exact congrFun h0 ⟨i, hi⟩
    · exact m1bLin_wt h i hi hf.1
  have h1 := LinearMap.rank_le_of_injective ψ hinj
  rwa [← IsLocalization.rank_eq (FractionRing O) (nonZeroDivisors O) le_rfl (N := {i // wt i = j} → FractionRing O),
    rank_fun'] at h1

private theorem quotient_saturated_square_torsion_free (q : A ⧸ satSq x) (c : O) (hc : c ≠ 0) (h : c • q = 0) : q = 0 := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨d, hd, h⟩ := h
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨d * c, mul_ne_zero hd hc, by rwa [mul_smul]⟩

omit [AddCommGroup X] in
private theorem spans_cotangent_of_rank_zero (j : X) (h : Module.rank O (cotLat x 𝒜 j) = 0) {κ : Type} (F : κ → A) :
    SpansCot x 𝒜 j F := by
  intro p hp
  obtain ⟨c, hc, h⟩ := rank_eq_zero_iff.1 h ⟨p, hp⟩
  exact ⟨c, hc, by rw [show c • p = 0 from congrArg Subtype.val h]; exact zero_mem _⟩

omit [AddCommGroup X] in
private theorem spans_cotangent_transfer_equal_rank {A' X' : Type} [CommRing A'] [Algebra O A'] {𝒜' : X' → Submodule O A'}
    {x' : A' →ₐ[O] O} (ι : A →ₐ[O] A') (hx : ∀ a, x' (ι a) = x a) {j : X} {j' : X'}
    (hmap : ∀ f ∈ 𝒜 j, ι f ∈ 𝒜' j') (hsurj : ∀ f' ∈ 𝒜' j', ∃ f ∈ 𝒜 j, ι f = f') (n : ℕ)
    (h1 : Module.rank O (cotLat x 𝒜 j) ≤ n) (h2 : Module.rank O (cotLat x' 𝒜' j') = n)
    {κ : Type} (F : κ → A) (hF : ∀ i, F i ∈ 𝒜 j ∧ x (F i) = 0) (hs : SpansCot x' 𝒜' j' fun i => ι (F i)) :
    SpansCot x 𝒜 j F := by
  have hsat : satSq x ≤ (satSq x').comap ι.toLinearMap := by
    rintro a ⟨c, hc, ha⟩
    refine ⟨c, hc, ?_⟩
    have hle : RingHom.ker x ^ 2 ≤ (RingHom.ker x' ^ 2).comap (ι : A →+* A') :=
      le_trans (Ideal.pow_right_mono (fun y hy => by
        show x' (ι y) = 0
        rw [hx]; exact hy) 2) (Ideal.le_comap_pow _ 2)
    have := hle ha
    rw [Ideal.mem_comap, RingHom.coe_coe, map_smul] at this
    exact this
  let P : (A ⧸ satSq x) →ₗ[O] (A' ⧸ satSq x') := Submodule.mapQ _ _ ι.toLinearMap hsat
  have hP : ∀ a, P ((satSq x).mkQ a) = (satSq x').mkQ (ι a) := fun a => rfl
  have hPL : ∀ q ∈ cotLat x 𝒜 j, P q ∈ cotLat x' 𝒜' j' := by
    rintro _ ⟨f, ⟨hf, hf0⟩, rfl⟩
    exact ⟨ι f, ⟨hmap f hf, (hx f).trans hf0⟩, rfl⟩
  let p : cotLat x 𝒜 j →ₗ[O] cotLat x' 𝒜' j' := P.restrict hPL
  have hp : Function.Surjective p := by
    rintro ⟨_, f', ⟨hf, hf0⟩, rfl⟩
    obtain ⟨f, hf1, rfl⟩ := hsurj f' hf
    exact ⟨⟨_, f, ⟨hf1, (hx f).symm.trans hf0⟩, rfl⟩, rfl⟩
  have hr := LinearMap.rank_eq_of_surjective hp
  have hk : Module.rank O (LinearMap.ker p) = 0 := by
    rw [hr, h2] at h1
    by_contra hne
    have h3 : (n : Cardinal) + 1 ≤ n := le_trans (by gcongr; exact Cardinal.one_le_iff_ne_zero.2 hne) h1
    norm_cast at h3
    omega
  have hinj : ∀ q ∈ cotLat x 𝒜 j, P q = 0 → q = 0 := fun q hq h0 => by
    obtain ⟨c, hc, h⟩ := rank_eq_zero_iff.1 hk ⟨⟨q, hq⟩, Subtype.ext h0⟩
    exact quotient_saturated_square_torsion_free q c hc (congrArg (fun z => z.1.1) h)
  have hsp : cotSpan x' (fun i => ι (F i)) = (cotSpan x F).map P := by
    rw [cotSpan, cotSpan, Submodule.map_span, ← Set.range_comp]
    rfl
  have hle : cotSpan x F ≤ cotLat x 𝒜 j := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨F i, hF i, rfl⟩
  intro q hq
  obtain ⟨c, hc, h⟩ := hs _ (hPL q hq)
  rw [hsp] at h
  obtain ⟨s, hs, h⟩ := h
  refine ⟨c, hc, ?_⟩
  have := hinj (c • q - s) (sub_mem (Submodule.smul_mem _ _ hq) (hle hs)) (by rw [map_sub, map_smul, h, sub_self])
  rw [sub_eq_zero.1 this]
  exact hs

end

private theorem origin_nonzero_weight_eq_zero {O X R : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R] (W : WPres O X R)
    (h : W.HasOrigin) {j : X} (hj : j ≠ 0) {f : R} (hf : f ∈ W.part j) : W.origin h f = 0 := by
  obtain ⟨g, hg, rfl⟩ := hf
  have := hg 0 (by simpa using hj.symm)
  exact (W.origin_π h g).trans (by simpa using this)

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}

private theorem origin_generators_eq_zero (M : Model D) : (∀ i, M.W.origin M.org (M.F i) = 0) ∧ (∀ i, M.W.origin M.org (M.E i) = 0) :=
  ⟨fun i => origin_nonzero_weight_eq_zero _ _ (by decide) (M.hF i), fun i => origin_nonzero_weight_eq_zero _ _ (by decide) (M.hE i)⟩

private theorem factor_through_quotient_by_generators (M : Model D) {K : Type} [CommRing K] [Algebra c.O K] (y : M.R →ₐ[c.O] K)
    (hF : ∀ i, y (M.F i) = 0) (hE : ∀ i, y (M.E i) = 0) (hZ : ∀ i, y (M.Z i) = 0) :
    ∃ y' : M.S →ₐ[c.O] K, ∀ f, y' (M.π f) = y f := by
  have hk : ∀ a ∈ RingHom.ker M.π, y a = 0 := by
    rw [M.ker]
    intro a ha
    have : Ideal.span (Set.range M.F ∪ Set.range M.E ∪ Set.range M.Z) ≤ RingHom.ker y := by
      refine Ideal.span_le.2 ?_
      rintro _ ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩)
      exacts [hF i, hE i, hZ i]
    exact this ha
  refine ⟨(Ideal.Quotient.liftₐ (RingHom.ker M.π) y hk).comp
    (Ideal.quotientKerAlgEquivOfSurjective M.surj).symm.toAlgHom, fun f => ?_⟩
  have : (Ideal.quotientKerAlgEquivOfSurjective M.surj).symm (M.π f) = Ideal.Quotient.mk _ f := by
    rw [AlgEquiv.symm_apply_eq]; rfl
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom]
  erw [this]
  rfl

private theorem derivation_zero_of_killing_generators (hD : D.Good) (hSo : SoV Ω l) (M : Model D) (w : ℤ × ℤ) (hw : w = -wPs ∨ w = 0)
    (δ : M.R →ₗ[c.O] c.O) (hδ : δ ∈ PtDer (M.W.origin M.org) c.O) (hwt : HasWt M.W.part w δ)
    (hF : ∀ i, δ (M.F i) = 0) (hE : ∀ i, δ (M.E i) = 0) (hZ : ∀ i, δ (M.Z i) = 0) : δ = 0 := by
  haveI : IsCO c.O (DualNumber c.O) := co_sqz c.O c.O c.O fun _ => rfl
  obtain ⟨y, hy⟩ := (der_hom c.O M.R c.O c.O (M.W.origin M.org) δ).1 ⟨δ, hδ, rfl⟩
  obtain ⟨y0, hy0⟩ := (der_hom c.O M.R c.O c.O (M.W.origin M.org) (0 : M.R →ₗ[c.O] c.O)).1 ⟨0, zero_mem _, rfl⟩
  obtain ⟨y', hy'⟩ := factor_through_quotient_by_generators M (K := DualNumber c.O) y
    (fun i => TrivSqZeroExt.ext ((hy _).1.trans ((origin_generators_eq_zero M).1 i)) ((hy _).2.trans (hF i)))
    (fun i => TrivSqZeroExt.ext ((hy _).1.trans ((origin_generators_eq_zero M).2 i)) ((hy _).2.trans (hE i)))
    (fun i => TrivSqZeroExt.ext ((hy _).1.trans (M.hZ i).2) ((hy _).2.trans (hZ i)))
  obtain ⟨y0', hy0'⟩ := factor_through_quotient_by_generators M (K := DualNumber c.O) y0
    (fun i => TrivSqZeroExt.ext ((hy0 _).1.trans ((origin_generators_eq_zero M).1 i)) (hy0 _).2)
    (fun i => TrivSqZeroExt.ext ((hy0 _).1.trans ((origin_generators_eq_zero M).2 i)) (hy0 _).2)
    (fun i => TrivSqZeroExt.ext ((hy0 _).1.trans (M.hZ i).2) (hy0 _).2)
  have ht := tanGlob D hD hSo (mapRep (y' : M.S →+* DualNumber c.O) M.ru.hom)
    ⟨M.S, _, _, _, M.ru, y', M.pt, rfl⟩ (fun g i j => by
      obtain ⟨f, -, hf⟩ := M.hom g i j
      show (y' (M.ru.hom g i j)).fst = _
      rw [← M.at0 g i j f hf, ← hf, hy', (hy f).1]) w hw (fun g i j hij => by
      obtain ⟨f, hf1, hf⟩ := M.hom g i j
      show (y' (M.ru.hom g i j)).snd = _
      rw [← hf, hy', (hy f).2]
      exact hwt _ hij f hf1)
  have he : y' = y0' := by
    refine M.gen _ y' y0' (Lift.ext (MonoidHom.ext fun g => Matrix.ext fun i j => ?_))
    rw [Lift.map_hom, Lift.map_hom]
    have h1 : (y' (M.ru.hom g i j)).snd = 0 := ht g i j
    obtain ⟨f, -, hf⟩ := M.hom g i j
    rw [← hf] at h1 ⊢
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [hy', hy0', (hy f).1, (hy0 f).1]
    · rw [h1, hy0', (hy0 f).2]; rfl
  ext f
  rw [← (hy f).2, ← hy', he, hy0', (hy0 f).2]

private theorem spans_cotangent_of_derivation_test (hD : D.Good) (hSo : SoV Ω l) (M : Model D) (w : ℤ × ℤ) (hw : w = -wPs ∨ w = 0)
    {κ : Type} (F : κ → M.W.A) (hF : ∀ i, F i ∈ M.W.gr w ∧ M.W.originA M.org (F i) = 0)
    (h : ∀ δ : M.R →ₗ[c.O] c.O, HasWt M.W.part w δ → (∀ i, δ (F i) = 0) →
      (∀ i, δ (M.F i) = 0) ∧ (∀ i, δ (M.E i) = 0) ∧ ∀ i, δ (M.Z i) = 0) :
    SpansCot (M.W.originA M.org) M.W.gr w F := by
  haveI := c.dvr
  refine spans_of_der c.O M.W.A (ℤ × ℤ) M.W.gr _ (fun i hi f hf => origin_nonzero_weight_eq_zero M.W M.org hi hf) w ?_ κ F hF
    fun δ hδ hwt h0 => ?_
  · rw [cot_fg]
    exact Submodule.fg_span (Set.finite_range _)
  · obtain ⟨δ', ⟨h1, rfl⟩, -⟩ := (der_extend c.O M.R (ℤ × ℤ) M.W M.org c.O).1 δ hδ
    have hwt' : HasWt M.W.part w δ' := fun i hi f hf => hwt i hi ⟨f, M.W.part_le_A hf⟩ hf
    obtain ⟨a, b, e⟩ := h δ' hwt' h0
    rw [derivation_zero_of_killing_generators hD hSo M w hw δ' h1 hwt' a b e, LinearMap.zero_comp]

private theorem cotangent_rank_at_weight_eq_dims (M : Model D) (w : ℤ × ℤ) :
    Module.rank c.O (cotLat (M.W.originA M.org) M.W.gr w) = (tDims M.r M.r' M.m w : ℕ) := by
  obtain ⟨τ, _, wt, φ, hc, hn⟩ := M.smooth
  haveI : Module.Finite c.O (cotLat (M.W.originA M.org) M.W.gr w) := by
    rw [Module.Finite.iff_fg, cot_fg]
    exact Submodule.fg_span (Set.finite_range _)
  rw [← Module.finrank_eq_rank, ← hn w]
  exact congrArg _ (chart_rank c.O M.W.A (ℤ × ℤ) M.W.gr _ τ wt φ hc w)

private theorem model_algebra_le_weight_algebra (M : Model D) : M.A ≤ M.W.A := by
  intro f hf
  exact (iSup_le fun n => le_iSup M.W.part (0, n) : (⨆ n, M.aPart n) ≤ ⨆ j, M.W.part j) hf

end

theorem UpperTheory.V.GradeZeroInterpolatingElement.m1b :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], SoV Ω l → SpansCot M.x0 M.gr (-1) M.eqns.F ∧ SpansCot M.x0 M.gr (-2) M.eqns.G ∧ SpansCot M.x0 M.gr 0 M.eqns.Z := by
  intro Ω _ _ _ l _ c D hD M _ hSo
  obtain ⟨τ, _, wt, φ, hc, hn⟩ := aSmooth D hD M
  have hsurj : ∀ n : ℤ, ∀ f' ∈ M.W.gr (0, n), ∃ f ∈ M.gr n, Subalgebra.inclusion (model_algebra_le_weight_algebra M) f = f' :=
    fun n f' hf => ⟨⟨f', M.aPart_le (n := n) hf⟩, hf, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · refine spans_cotangent_transfer_equal_rank (𝒜' := M.W.gr) (x' := M.W.originA M.org) (j' := -wPs) (Subalgebra.inclusion (model_algebra_le_weight_algebra M))
      (fun _ => rfl) (fun f hf => hf) (hsurj (-1)) M.r ?_ ?_ _ (fun i => ⟨M.hF i, (origin_generators_eq_zero M).1 i⟩) ?_
    · have := cotangent_rank_le_weight_count hc (-1)
      rwa [hn] at this
    · rw [cotangent_rank_at_weight_eq_dims]; rfl
    · exact spans_cotangent_of_derivation_test hD hSo M _ (Or.inl rfl) _ (fun i => ⟨M.hF i, (origin_generators_eq_zero M).1 i⟩) fun δ hw h0 =>
        ⟨h0, fun i => hw _ (by decide) _ (M.hE i), fun i => hw _ (by decide) _ (M.hZ i).1⟩
  · refine spans_cotangent_of_rank_zero _ ?_ _
    have := cotangent_rank_le_weight_count hc (-2)
    rw [hn] at this
    exact le_antisymm this zero_le
  · refine spans_cotangent_transfer_equal_rank (𝒜' := M.W.gr) (x' := M.W.originA M.org) (j' := 0) (Subalgebra.inclusion (model_algebra_le_weight_algebra M))
      (fun _ => rfl) (fun f hf => hf) (hsurj 0) M.m ?_ ?_ _ M.hZ ?_
    · have := cotangent_rank_le_weight_count hc 0
      rwa [hn] at this
    · rw [cotangent_rank_at_weight_eq_dims]; rfl
    · exact spans_cotangent_of_derivation_test hD hSo M _ (Or.inr rfl) _ M.hZ fun δ hw h0 =>
        ⟨fun i => hw _ (by decide) _ (M.hF i), fun i => hw _ (by decide) _ (M.hE i), h0⟩
