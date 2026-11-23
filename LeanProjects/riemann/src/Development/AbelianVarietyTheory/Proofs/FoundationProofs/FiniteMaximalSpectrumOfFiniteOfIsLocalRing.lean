import Mathlib

noncomputable section

namespace GlobalTheory

open IsLocalRing Polynomial TensorProduct

theorem idempotent_eq_of_sub_mem_jacobson {S : Type*} [CommRing S] {a b : S}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) (h : a - b ∈ (⊥ : Ideal S).jacobson) :
    a = b := by
  have hu : IsUnit ((a - b) * (-(a - b)) + 1) := Ideal.mem_jacobson_bot.1 h _
  have h0 : ((a - b) * (-(a - b)) + 1) * (a - b) = 0 := by
    have h1 := ha.eq
    have h2 := hb.eq
    linear_combination (-a - 1 + 3 * b) * h1 + (b + 1 - 3 * a) * h2
  exact sub_eq_zero.1 ((hu.mul_right_eq_zero).1 h0)

theorem isUnit_of_isUnit_mk_of_le_jacobson {S : Type*} [CommRing S] {J : Ideal S}
    (hJ : J ≤ (⊥ : Ideal S).jacobson) {x : S} (hx : IsUnit (Ideal.Quotient.mk J x)) : IsUnit x :=
  have := isLocalHom_of_le_jacobson_bot J hJ
  IsUnit.of_map (Ideal.Quotient.mk J) x hx

theorem algHom_ext_of_sub_mem_jacobson {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.EssFiniteType R A] [Algebra.FormallyUnramified R A]
    {f g : A →ₐ[R] B} (h : ∀ a, f a - g a ∈ (⊥ : Ideal B).jacobson) : f = g := by
  obtain ⟨t, ht, ht1⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := R) (S := A)).1
    inferInstance
  let φ : A ⊗[R] A →ₐ[R] B := Algebra.TensorProduct.lift f g fun _ _ ↦ .all _ _
  have key : ∀ x : A ⊗[R] A, f (Algebra.TensorProduct.lmul' R x) - φ x ∈
      (⊥ : Ideal B).jacobson := by
    intro x
    induction x with
    | zero => simp
    | tmul a b =>
      have : f (Algebra.TensorProduct.lmul' R (a ⊗ₜ b)) - φ (a ⊗ₜ b) = f a * (f b - g b) := by
        simp [φ, mul_sub]
      rw [this]
      exact Ideal.mul_mem_left _ _ (h b)
    | add x y hx hy =>
      rw [map_add, map_add, map_add, add_sub_add_comm]
      exact add_mem hx hy
  have hu : IsUnit (φ t) := by
    have h1 := key t
    rw [ht1, map_one] at h1
    have := Ideal.mem_jacobson_bot.1 h1 (-1)
    simpa using this
  ext a
  have := congr(φ $(ht a))
  simp only [map_mul, map_sub, map_zero, φ, Algebra.TensorProduct.lift_tmul, map_one, one_mul,
    mul_one] at this
  exact (sub_eq_zero.1 ((hu.mul_left_eq_zero).1 this)).symm

theorem exists_algHom_lift_of_etale_of_isLocalRing {R A S : Type*} [CommRing R] [CommRing A]
    [CommRing S] [Algebra R A] [Algebra R S] [Algebra.Etale R A] [IsLocalRing S] (J : Ideal S)
    [HenselianRing S J] (φ : A →ₐ[R] S ⧸ J) :
    ∃ ψ : A →ₐ[R] S, ∀ a, Ideal.Quotient.mk J (ψ a) = φ a := by
  have hJ : J ≤ (⊥ : Ideal S).jacobson := HenselianRing.jac
  have hJtop : J ≠ ⊤ := by
    rintro rfl
    rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] at hJ
    exact (maximalIdeal.isMaximal S).ne_top (top_le_iff.1 hJ)
  have : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJtop
  have : IsLocalRing (S ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  let Q : Ideal A := (maximalIdeal (S ⧸ J)).comap φ
  obtain ⟨f, hfQ, ⟨⟨P⟩⟩⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) Q
  have hf : IsUnit (φ f) := by
    simpa [Q] using hfQ
  let φ' : Localization.Away f →ₐ[R] S ⧸ J := IsLocalization.Away.liftAlgHom f hf
  have hφ' : ∀ a, φ' (algebraMap _ _ a) = φ a := fun a ↦ by simp [φ']
  obtain ⟨x₀, hx₀⟩ := Ideal.Quotient.mk_surjective (φ' P.x)
  have hm : P.HasMap (Ideal.Quotient.mkₐ R J x₀) := by
    have := P.hasMap.map φ'
    rwa [← hx₀] at this
  obtain ⟨x, hx, hxx⟩ := HenselianRing.is_henselian (I := J) (P.f.map (algebraMap R S))
    (P.monic_f.map _) x₀ (by
      rw [eval_map_algebraMap, ← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk R,
        ← aeval_algHom_apply]
      exact hm.1) (by
      rw [derivative_map, eval_map_algebraMap, ← Ideal.Quotient.mkₐ_eq_mk R,
        ← aeval_algHom_apply]
      exact hm.isUnit_derivative_f)
  have hxx' : Ideal.Quotient.mkₐ R J x = Ideal.Quotient.mkₐ R J x₀ := Ideal.Quotient.eq.2 hxx
  have hmx : P.HasMap x := by
    refine ⟨by simpa [eval_map_algebraMap] using hx.eq_zero, ?_⟩
    apply isUnit_of_isUnit_mk_of_le_jacobson hJ
    rw [← Ideal.Quotient.mkₐ_eq_mk R, ← aeval_algHom_apply, hxx']
    exact hm.2
  let ψ' : Localization.Away f →ₐ[R] S := (P.lift x hmx).comp P.equivRing.toAlgHom
  have hψ' : (Ideal.Quotient.mkₐ R J).comp ψ' = φ' := by
    apply P.hom_ext
    change Ideal.Quotient.mkₐ R J (P.lift x hmx (P.equivRing P.x)) = _
    rw [StandardEtalePresentation.equivRing_x, StandardEtalePair.lift_X, hxx']
    exact hx₀
  refine ⟨ψ'.comp (IsScalarTower.toAlgHom R A _), fun a ↦ ?_⟩
  rw [← hφ', ← hψ']
  rfl

theorem comap_eq_maximalIdeal_of_finite {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S] (n : Ideal S) [n.IsMaximal] :
    n.comap (algebraMap R S) = maximalIdeal R :=
  IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n)

theorem map_maximalIdeal_le_jacobson_of_finite (R S : Type*) [CommRing R] [IsLocalRing R]
    [CommRing S] [Algebra R S] [Module.Finite R S] :
    (maximalIdeal R).map (algebraMap R S) ≤ (⊥ : Ideal S).jacobson := by
  rw [Ideal.jacobson, le_sInf_iff]
  rintro n ⟨-, hn⟩
  rw [Ideal.map_le_iff_le_comap, comap_eq_maximalIdeal_of_finite]

theorem finite_maximalSpectrum_of_finite_of_isLocalRing (R S : Type*) [CommRing R] [IsLocalRing R]
    [CommRing S] [Algebra R S] [Module.Finite R S] : Finite (MaximalSpectrum S) := by
  have hfin := (Algebra.QuasiFinite.finite_primesOver (R := R) (S := S)
    (maximalIdeal R)).to_subtype
  refine Finite.of_injective (β := (maximalIdeal R).primesOver S) (fun n ↦ ⟨n.asIdeal,
    n.isMaximal.isPrime, ⟨(have := n.isMaximal; (comap_eq_maximalIdeal_of_finite n.asIdeal).symm)⟩⟩)
    fun a b h ↦ MaximalSpectrum.ext congr(($h).1)

theorem exists_idempotent_notMem_iff_of_henselian (R : Type*) {S : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (q : Ideal S) [hq : q.IsMaximal] :
    ∃ e : S, IsIdempotentElem e ∧ ∀ n : Ideal S, n.IsMaximal → (e ∉ n ↔ n = q) := by
  have : q.LiesOver (maximalIdeal R) := ⟨(comap_eq_maximalIdeal_of_finite q).symm⟩
  obtain ⟨R', _, _, _, P, _, _, e, he, P', _, _, hP'q, heP', hbij, -, H⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq (maximalIdeal R) q
  let ε : (maximalIdeal R).ResidueField ≃ₐ[R] P.ResidueField := .ofBijective _ hbij
  let ε' : (R ⧸ maximalIdeal R) ≃ₐ[R] (maximalIdeal R).ResidueField :=
    .ofBijective (IsScalarTower.toAlgHom _ _ _)
      (Ideal.bijective_algebraMap_quotient_residueField _)
  obtain ⟨σ, hσ⟩ := exists_algHom_lift_of_etale_of_isLocalRing (maximalIdeal R)
    ((ε'.trans ε).symm.toAlgHom.comp (IsScalarTower.toAlgHom R R' P.ResidueField))
  have hσP : ∀ a, σ a ∈ maximalIdeal R ↔ a ∈ P := fun a ↦ by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hσ, ← Ideal.algebraMap_residueField_eq_zero (I := P)]
    simp
  let τ : R' ⊗[R] S →ₐ[R] S :=
    Algebra.TensorProduct.lift ((Algebra.ofId R S).comp σ) (.id R S) fun _ _ ↦ .all _ _
  have hlies : ∀ n : Ideal S, n.IsMaximal → (n.comap τ).LiesOver P := fun n hn ↦ ⟨by
    ext a
    rw [← hσP, ← comap_eq_maximalIdeal_of_finite n]
    simp [τ, Ideal.under, Algebra.TensorProduct.algebraMap_apply]⟩
  have hcomap : ∀ n : Ideal S,
      (n.comap τ).comap Algebra.TensorProduct.includeRight.toRingHom = n := fun n ↦ by
    ext a
    simp [τ]
  refine ⟨τ e, he.map τ, fun n hn ↦ ⟨fun h ↦ ?_, ?_⟩⟩
  · have := H (n.comap τ) inferInstance (hlies n hn) h
    rw [← hcomap n, this, hP'q]
  · rintro rfl
    have := hlies n hn
    have : n.comap τ = P' :=
      Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hbij _ _ (by rw [hcomap, hP'q])
    rw [← this] at heP'
    exact heP'

theorem mem_jacobson_bot_of_forall_isMaximal {S : Type*} [CommRing S] {x : S}
    (h : ∀ n : Ideal S, n.IsMaximal → x ∈ n) : x ∈ (⊥ : Ideal S).jacobson := by
  rw [Ideal.jacobson, Ideal.mem_sInf]
  rintro n ⟨-, hn⟩
  exact h n hn

theorem one_sub_mem_iff_notMem_of_isIdempotentElem {S : Type*} [CommRing S] {e : S}
    (he : IsIdempotentElem e) (n : Ideal S) [hn : n.IsPrime] : 1 - e ∈ n ↔ e ∉ n := by
  refine ⟨fun h h' ↦ hn.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using add_mem h h')),
    fun h ↦ ?_⟩
  have : e * (1 - e) ∈ n := by rw [mul_sub, mul_one, he.eq, sub_self]; exact zero_mem _
  exact (hn.mem_or_mem this).resolve_left h

theorem idempotent_eq_of_forall_isMaximal {S : Type*} [CommRing S] {a b : S}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (h : ∀ n : Ideal S, n.IsMaximal → (a ∈ n ↔ b ∈ n)) : a = b := by
  refine idempotent_eq_of_sub_mem_jacobson ha hb
    (mem_jacobson_bot_of_forall_isMaximal fun n hn ↦ ?_)
  by_cases han : a ∈ n
  · exact sub_mem han ((h n hn).1 han)
  · have h1 := (one_sub_mem_iff_notMem_of_isIdempotentElem ha n).2 han
    have h2 := (one_sub_mem_iff_notMem_of_isIdempotentElem hb n).2 (mt (h n hn).2 han)
    simpa using sub_mem h2 h1

theorem exists_idempotent_notMem_iff_mem_of_henselian (R : Type*) {S : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (T : Set (MaximalSpectrum S)) :
    ∃ e : S, IsIdempotentElem e ∧ ∀ n : MaximalSpectrum S, (e ∉ n.asIdeal ↔ n ∈ T) := by
  have := finite_maximalSpectrum_of_finite_of_isLocalRing R S
  induction T, T.toFinite using Set.Finite.induction_on with
  | empty => exact ⟨0, .zero, by simp⟩
  | @insert q T hq _ ih =>
    obtain ⟨e, he, H⟩ := ih
    have := q.isMaximal
    obtain ⟨d, hd, H'⟩ := exists_idempotent_notMem_iff_of_henselian R q.asIdeal
    refine ⟨1 - (1 - d) * (1 - e), (hd.one_sub.mul he.one_sub).one_sub, fun n ↦ ?_⟩
    have := n.isMaximal
    rw [one_sub_mem_iff_notMem_of_isIdempotentElem (hd.one_sub.mul he.one_sub), not_not,
      Ideal.IsPrime.mul_mem_iff_mem_or_mem inferInstance,
      one_sub_mem_iff_notMem_of_isIdempotentElem hd, one_sub_mem_iff_notMem_of_isIdempotentElem he,
      H, H' _ this, Set.mem_insert_iff, MaximalSpectrum.ext_iff]

theorem exists_idempotent_lift_of_henselian (R : Type*) {S C : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S] [CommRing C]
    (π : S →+* C) (hπ : Function.Surjective π) {c : C} (hc : IsIdempotentElem c) :
    ∃ e : S, IsIdempotentElem e ∧ π e = c := by
  obtain ⟨e, he, H⟩ := exists_idempotent_notMem_iff_mem_of_henselian R (S := S)
    {n | ∃ m : Ideal C, m.IsMaximal ∧ m.comap π = n.asIdeal ∧ c ∉ m}
  refine ⟨e, he, idempotent_eq_of_forall_isMaximal (he.map π) hc fun m hm ↦ ?_⟩
  have := H ⟨m.comap π, Ideal.comap_isMaximal_of_surjective π hπ⟩
  rw [← not_iff_not]
  refine this.trans ⟨?_, fun h ↦ ⟨m, hm, rfl, h⟩⟩
  rintro ⟨m', -, h1, h2⟩
  rwa [← Ideal.comap_injective_of_surjective π hπ h1]

theorem existsUnique_idempotent_lift_of_henselian (R : Type*) {S C : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S] [CommRing C]
    (π : S →+* C) (hπ : Function.Surjective π) (hker : RingHom.ker π ≤ (⊥ : Ideal S).jacobson)
    {c : C} (hc : IsIdempotentElem c) :
    ∃! e : S, IsIdempotentElem e ∧ π e = c := by
  obtain ⟨e, he, h⟩ := exists_idempotent_lift_of_henselian R π hπ hc
  refine ⟨e, ⟨he, h⟩, fun e' ⟨he', h'⟩ ↦ idempotent_eq_of_sub_mem_jacobson he' he (hker ?_)⟩
  rw [RingHom.mem_ker, map_sub, h, h', sub_self]

theorem henselianRing_of_finite (R : Type*) {S : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S] (J : Ideal S)
    (hJ : J ≤ (⊥ : Ideal S).jacobson) : HenselianRing S J where
  jac := hJ
  is_henselian f hf a₀ h₁ h₂ := by
    nontriviality S using Subsingleton.elim _ (0 : S)
    obtain ⟨u, hu⟩ := (isUnit_of_isUnit_mk_of_le_jacobson hJ h₂).exists_left_inv
    set g := f /ₘ (X - C a₀) with hg
    have hfg : (X - C a₀) * g = f - C (f.eval a₀) := by
      rw [hg, X_sub_C_mul_divByMonic_eq_sub_modByMonic, modByMonic_X_sub_C_eq_C_eval]
    have hga : u * g.eval a₀ = 1 := by
      have := congr((derivative $hfg).eval a₀)
      simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, eval_add, eval_mul,
        eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero, eval_one, eval_zero, sub_zero,
        one_mul] at this
      rw [this, hu]
    have hdeg : g.degree < f.degree :=
      degree_divByMonic_lt f _ hf.ne_zero (by simp)
    let T := AdjoinRoot f
    have : Module.Finite S T := hf.finite_adjoinRoot
    have : Module.Finite R T := .trans S T
    let x : T := AdjoinRoot.root f
    let JT : Ideal T := J.map (algebraMap S T)
    let e₀ : T := u • aeval x g
    have hx0 : (x - algebraMap S T a₀) * e₀ ∈ JT := by
      have := congr(aeval x $hfg)
      simp only [map_mul, map_sub, aeval_X, aeval_C] at this
      rw [mul_smul_comm, this, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_sub, Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (neg_mem (Ideal.mem_map_of_mem _ h₁))
    have hdvd : ∀ (p : S[X]) (a : S),
        x - algebraMap S T a ∣ aeval x p - algebraMap S T (p.eval a) := fun p a ↦ by
      rw [← aeval_algebraMap_apply_eq_algebraMap_eval, ← eval_map_algebraMap,
        ← eval_map_algebraMap]
      exact sub_dvd_eval_sub _ _ _
    have hp0 : ∀ p : S[X], (aeval x p - algebraMap S T (p.eval a₀)) * e₀ ∈ JT := fun p ↦ by
      obtain ⟨c, hc⟩ : x - algebraMap S T a₀ ∣ aeval x p - algebraMap S T (p.eval a₀) := by
        exact hdvd p a₀
      rw [hc, mul_right_comm]
      exact Ideal.mul_mem_right _ _ hx0
    have he₀ : IsIdempotentElem (Ideal.Quotient.mk JT e₀) := by
      rw [IsIdempotentElem, ← map_mul, Ideal.Quotient.eq]
      have := hp0 (C u * g)
      rw [eval_mul, eval_C, hga, map_one, map_mul, aeval_C, ← Algebra.smul_def, sub_mul,
        one_mul] at this
      exact this
    obtain ⟨e, he, hee⟩ := exists_idempotent_lift_of_henselian R (Ideal.Quotient.mk JT)
      Ideal.Quotient.mk_surjective he₀
    rw [Ideal.Quotient.eq] at hee
    have hJT : ∀ y ∈ JT, y ∈ J • (⊤ : Submodule S T) := fun y hy ↦ by
      rw [Ideal.smul_top_eq_map]; exact hy
    have hp : ∀ p : S[X], (aeval x p - algebraMap S T (p.eval a₀)) * e ∈ JT := fun p ↦ by
      have := add_mem (hp0 p) (Ideal.mul_mem_left _ (aeval x p - algebraMap S T (p.eval a₀)) hee)
      rwa [← mul_add, add_sub_cancel] at this
    let μ : T →ₗ[S] T := LinearMap.mulRight S e
    have hle : (⊤ : Submodule S T).map μ ≤ Submodule.span S {e} := by
      refine Submodule.le_of_le_smul_of_le_jacobson_bot (Module.Finite.fg_top.map _) hJ ?_
      rintro _ ⟨y, -, rfl⟩
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
      rw [← AdjoinRoot.aeval_eq]
      refine Submodule.mem_sup.2 ⟨p.eval a₀ • e,
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _),
        μ ((aeval x p - algebraMap S T (p.eval a₀)) * e), ?_, ?_⟩
      · rw [← Submodule.map_smul'']
        exact Submodule.mem_map_of_mem (hJT _ (hp p))
      · simp only [μ, LinearMap.mulRight_apply, mul_assoc, he.eq, Algebra.smul_def]
        ring
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hle (Submodule.mem_map_of_mem
      (Submodule.mem_top (x := x))))
    simp only [μ, LinearMap.mulRight_apply, Algebra.smul_def] at ha
    let l : T →ₗ[S] S := (leval a₀).comp (AdjoinRoot.modByMonicHom hf)
    have hlJ : ∀ y ∈ JT, l y ∈ J := fun y hy ↦ by
      have := Submodule.mem_map_of_mem (f := l) (hJT y hy)
      rw [Submodule.map_smul''] at this
      have h2 := Submodule.smul_mono (le_refl J) (le_top (a := (⊤ : Submodule S T).map l)) this
      simpa using h2
    have hl0 : l e₀ = 1 := by
      simp only [e₀, map_smul, l, LinearMap.comp_apply, x]
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff hf).2 hdeg]
      simpa using hga
    have hle : IsUnit (l e) := by
      have := hlJ _ hee
      rw [map_sub, hl0] at this
      simpa using Ideal.mem_jacobson_bot.1 (hJ this) 1
    refine ⟨a, ?_, ?_⟩
    · obtain ⟨c, hc⟩ : x - algebraMap S T a ∣ aeval x f - algebraMap S T (f.eval a) := by
        exact hdvd f a
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self] at hc
      have : f.eval a • e = 0 := by
        rw [Algebra.smul_def]
        linear_combination (-e) * hc + c * ha
      have := congr(l $this)
      rw [map_smul, map_zero, smul_eq_mul] at this
      exact hle.mul_left_eq_zero.1 this
    · have := hp X
      rw [aeval_X, eval_X, sub_mul, ← ha, ← sub_mul, ← map_sub, ← Algebra.smul_def] at this
      have := hlJ _ this
      rw [map_smul, smul_eq_mul] at this
      exact (Ideal.mul_unit_mem_iff_mem _ hle).1 this

theorem henselianLocalRing_of_henselianRing (S : Type*) [CommRing S] [IsLocalRing S]
    [HenselianRing S (maximalIdeal S)] : HenselianLocalRing S where
  is_henselian f hf a₀ h₁ h₂ := HenselianRing.is_henselian f hf a₀ h₁ (h₂.map _)

theorem henselianLocalRing_of_finite (R S : Type*) [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S] [IsLocalRing S] :
    HenselianLocalRing S :=
  have := henselianRing_of_finite R (maximalIdeal S)
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  henselianLocalRing_of_henselianRing S

theorem isLocalRing_quotient_one_sub {S : Type*} [CommRing S] {e : S} (he : IsIdempotentElem e)
    (q : Ideal S) [hq : q.IsMaximal] (H : ∀ n : Ideal S, n.IsMaximal → (e ∉ n ↔ n = q)) :
    IsLocalRing (S ⧸ Ideal.span {1 - e}) := by
  have hle : Ideal.span {1 - e} ≤ q := by
    rw [Ideal.span_singleton_le_iff_mem, one_sub_mem_iff_notMem_of_isIdempotentElem he, H q hq]
  refine .of_unique_max_ideal ⟨q.map (Ideal.Quotient.mk _),
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by simpa using hle),
    fun m hm ↦ ?_⟩
  have := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective (K := m)
  have h : m.comap (Ideal.Quotient.mk _) = q := by
    rw [← H _ this, ← one_sub_mem_iff_notMem_of_isIdempotentElem he, Ideal.mem_comap,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)]
    exact zero_mem _
  rw [← h, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]

theorem exists_completeOrthogonalIdempotents_of_henselian (R S : Type*) [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    [Fintype (MaximalSpectrum S)] :
    ∃ e : MaximalSpectrum S → S, CompleteOrthogonalIdempotents e ∧
      ∀ (q : MaximalSpectrum S) (n : Ideal S), n.IsMaximal → (e q ∉ n ↔ n = q.asIdeal) := by
  classical
  choose e he H using fun q : MaximalSpectrum S ↦
    have := q.isMaximal; exists_idempotent_notMem_iff_of_henselian R q.asIdeal
  have horth : OrthogonalIdempotents e := by
    refine ⟨he, fun i j hij ↦ idempotent_eq_of_forall_isMaximal ((he i).mul (he j)) .zero
      fun n hn ↦ ?_⟩
    simp only [zero_mem, iff_true, hn.isPrime.mul_mem_iff_mem_or_mem]
    by_contra! h
    exact hij (MaximalSpectrum.ext (((H i n hn).1 h.1).symm.trans ((H j n hn).1 h.2)))
  refine ⟨e, ⟨horth, idempotent_eq_of_forall_isMaximal horth.isIdempotentElem_sum .one
    fun n hn ↦ ?_⟩, H⟩
  have h1 : (1 : S) ∉ n := (Ideal.ne_top_iff_one _).1 hn.ne_top
  simp only [h1, iff_false]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨n, hn⟩), Submodule.add_mem_iff_left,
    H _ n hn]
  refine Submodule.sum_mem _ fun i hi ↦ ?_
  by_contra h
  exact (Finset.mem_erase.1 hi).1 (MaximalSpectrum.ext ((H i n hn).1 h).symm)

theorem surjective_algebraMap_localization_of_henselian (R : Type*) {S : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (q : Ideal S) [hq : q.IsMaximal] :
    Function.Surjective (algebraMap S (Localization.AtPrime q)) := by
  obtain ⟨e, he, H⟩ := exists_idempotent_notMem_iff_of_henselian R q
  have heq : e ∉ q := (H q hq).2 rfl
  have he1 : algebraMap S (Localization.AtPrime q) e = 1 :=
    (IsIdempotentElem.iff_eq_one_of_isUnit
      (IsLocalization.map_units _ (⟨e, heq⟩ : q.primeCompl))).1 (he.map _)
  intro y
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl y
  have hu : IsUnit (e * s + (1 - e)) := by
    by_contra h
    obtain ⟨n, hn, hmem⟩ := exists_max_ideal_of_mem_nonunits h
    by_cases hen : e ∈ n
    · rw [Submodule.add_mem_iff_right _ (Ideal.mul_mem_right _ _ hen),
        one_sub_mem_iff_notMem_of_isIdempotentElem he] at hmem
      exact hmem hen
    · rw [Submodule.add_mem_iff_left _ ((one_sub_mem_iff_notMem_of_isIdempotentElem he n).2 hen),
        (H n hn).1 hen] at hmem
      exact (hq.isPrime.mem_or_mem hmem).elim heq s.2
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  refine ⟨a * v, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq]
  have := congr(algebraMap S (Localization.AtPrime q) $hv)
  simp only [map_mul, map_add, map_sub, map_one, he1, one_mul, sub_self, add_zero] at this
  rw [map_mul, mul_assoc, this, mul_one]

theorem finite_localization_of_henselian (R : Type*) {S : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (q : Ideal S) [q.IsMaximal] : Module.Finite R (Localization.AtPrime q) :=
  .of_surjective (IsScalarTower.toAlgHom R S _).toLinearMap
    (surjective_algebraMap_localization_of_henselian R q)

theorem henselianLocalRing_localization_of_henselian (R : Type*) {S : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (q : Ideal S) [q.IsMaximal] : HenselianLocalRing (Localization.AtPrime q) :=
  have := finite_localization_of_henselian R q
  henselianLocalRing_of_finite R _

theorem bijective_toPiLocalization_of_henselian (R S : Type*) [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S] :
    Function.Bijective (MaximalSpectrum.toPiLocalization S) := by
  classical
  refine ⟨MaximalSpectrum.toPiLocalization_injective S, fun y ↦ ?_⟩
  have := finite_maximalSpectrum_of_finite_of_isLocalRing R S
  have := Fintype.ofFinite (MaximalSpectrum S)
  obtain ⟨e, he, H⟩ := exists_completeOrthogonalIdempotents_of_henselian R S
  choose a ha using fun q : MaximalSpectrum S ↦
    have := q.isMaximal; surjective_algebraMap_localization_of_henselian R q.asIdeal (y q)
  have h1 : ∀ q : MaximalSpectrum S, algebraMap S (Localization.AtPrime q.asIdeal) (e q) = 1 :=
    fun q ↦ (IsIdempotentElem.iff_eq_one_of_isUnit (IsLocalization.map_units _
      (⟨e q, (H q _ q.isMaximal).2 rfl⟩ : q.asIdeal.primeCompl))).1 ((he.idem q).map _)
  refine ⟨∑ q, e q * a q, funext fun q ↦ ?_⟩
  rw [MaximalSpectrum.toPiLocalization_apply_apply, map_sum, Finset.sum_eq_single q]
  · rw [map_mul, h1, one_mul, ha]
  · intro p _ hpq
    have := congr(algebraMap S (Localization.AtPrime q.asIdeal) $(he.ortho hpq))
    rw [map_mul, h1, mul_one, map_zero] at this
    rw [map_mul, this, zero_mul]
  · simp

theorem exists_algEquiv_pi_henselianLocalRing.{v} (R : Type*) (S : Type v) [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S] :
    ∃ (ι : Type v) (_ : Finite ι) (T : ι → Type v) (_ : ∀ i, CommRing (T i))
      (_ : ∀ i, Algebra R (T i)) (_ : S ≃ₐ[R] Π i, T i),
      ∀ i, HenselianLocalRing (T i) ∧ Module.Finite R (T i) :=
  ⟨MaximalSpectrum S, finite_maximalSpectrum_of_finite_of_isLocalRing R S,
    fun q ↦ Localization.AtPrime q.asIdeal, inferInstance, inferInstance,
    .ofBijective ((MaximalSpectrum.toPiLocalization S).restrictScalars R)
      (bijective_toPiLocalization_of_henselian R S),
    fun q ↦ have := q.isMaximal
      ⟨henselianLocalRing_localization_of_henselian R _, finite_localization_of_henselian R _⟩⟩

theorem exists_algHom_lift_of_etale_of_henselian (R : Type*) {k A B : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing k] [CommRing A] [CommRing B] [Algebra R B]
    [Module.Finite R B] [Algebra k A] [Algebra k B] [Algebra.Etale k A] (J : Ideal B)
    (hJ : J ≤ (⊥ : Ideal B).jacobson) (φ : A →ₐ[k] B ⧸ J) :
    ∃ ψ : A →ₐ[k] B, ∀ a, Ideal.Quotient.mk J (ψ a) = φ a := by
  classical
  have := finite_maximalSpectrum_of_finite_of_isLocalRing R B
  have := Fintype.ofFinite (MaximalSpectrum B)
  obtain ⟨e, he, H⟩ := exists_completeOrthogonalIdempotents_of_henselian R B
  have key : ∀ q : MaximalSpectrum B, ∃ ψ : A →ₐ[k] B ⧸ Ideal.span {1 - e q},
      ∀ a b, Ideal.Quotient.mk J b = φ a →
        ψ a - Ideal.Quotient.mk _ b ∈ J.map (Ideal.Quotient.mk _) := fun q ↦ by
    have := q.isMaximal
    have := isLocalRing_quotient_one_sub (he.idem q) q.asIdeal (H q)
    let J' := J.map (Ideal.Quotient.mk (Ideal.span {1 - e q}))
    have : HenselianRing _ J' := henselianRing_of_finite R J' <| by
      refine Ideal.map_le_iff_le_comap.2 (hJ.trans ?_)
      rw [Ideal.comap_jacobson_of_surjective Ideal.Quotient.mk_surjective]
      exact Ideal.jacobson_mono bot_le
    obtain ⟨ψ, hψ⟩ := exists_algHom_lift_of_etale_of_isLocalRing J'
      ((Ideal.quotientMapₐ J' (Ideal.Quotient.mkₐ k _) Ideal.le_comap_map).comp φ)
    refine ⟨ψ, fun a b hb ↦ ?_⟩
    rw [← Ideal.Quotient.eq, hψ, AlgHom.comp_apply, ← hb]
    rfl
  choose ψ hψ using key
  let ε : B ≃ₐ[k] Π q, B ⧸ Ideal.span {1 - e q} :=
    .ofBijective (AlgHom.pi fun q ↦ Ideal.Quotient.mkₐ k _) he.bijective_pi
  refine ⟨ε.symm.toAlgHom.comp (AlgHom.pi ψ), fun a ↦ ?_⟩
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (φ a)
  rw [← hb, Ideal.Quotient.eq]
  set c := (ε.symm.toAlgHom.comp (AlgHom.pi ψ)) a
  have hc : ∀ q, Ideal.Quotient.mk _ c = ψ q a := fun q ↦
    congr($(ε.apply_symm_apply (AlgHom.pi ψ a)) q)
  rw [← one_mul (c - b), ← he.complete, Finset.sum_mul]
  refine Submodule.sum_mem _ fun q _ ↦ ?_
  have := hψ q a b hb
  rw [← hc, ← map_sub, Ideal.mem_quotient_iff_mem_sup] at this
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 this
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  have : e q * (c - b) = e q * y := by
    rw [← hyz]
    linear_combination (-w) * (he.idem q).eq
  rw [this]
  exact Ideal.mul_mem_left _ _ hy

theorem bijective_algHom_comp_of_etale_of_henselian (R : Type*) {k A B C : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing k] [CommRing A] [CommRing B] [CommRing C] [Algebra R B]
    [Module.Finite R B] [Algebra k A] [Algebra k B] [Algebra k C] [Algebra.Etale k A]
    (π : B →ₐ[k] C) (hπ : Function.Surjective π)
    (hker : RingHom.ker π ≤ (⊥ : Ideal B).jacobson) :
    Function.Bijective fun ψ : A →ₐ[k] B ↦ π.comp ψ := by
  refine ⟨fun f g h ↦ algHom_ext_of_sub_mem_jacobson fun a ↦ hker ?_, fun φ ↦ ?_⟩
  · rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact congr($h a)
  · let ε := Ideal.quotientKerAlgEquivOfSurjective hπ
    obtain ⟨ψ, hψ⟩ := exists_algHom_lift_of_etale_of_henselian R _ hker (ε.symm.toAlgHom.comp φ)
    refine ⟨ψ, AlgHom.ext fun a ↦ ?_⟩
    have := congr(ε $(hψ a))
    simpa [ε] using this

end GlobalTheory
