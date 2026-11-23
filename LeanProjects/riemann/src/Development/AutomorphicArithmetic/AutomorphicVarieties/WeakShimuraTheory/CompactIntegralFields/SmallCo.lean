import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.SmallExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CoefSup
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ClSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem exists_map_eq_algebraMap_padicInt_of_isDvr {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) {A : Type} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (f : A →+* 𝔞.V) (hf : 𝔞.IsDvr f) (c : Coef l) (t : ℤ_[l]) :
    ∃ a : A, f a = 𝔞.a c (algebraMap ℤ_[l] c.O t) := by
  classical
  haveI := c.dvr
  haveI := hf.loc
  haveI := 𝔞.loc c
  haveI := hf.complete
  have hlc : ((l : ℕ) : c.O) ∈ maximalIdeal c.O := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.2.1
  have hlA : ((l : ℕ) : A) ∈ maximalIdeal A := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 : IsUnit (𝔞.a c ((l : ℕ) : c.O)) := by
      have := hu.map f
      rwa [map_natCast, ← map_natCast (𝔞.a c)] at this
    have h2 := isUnit_of_map_unit (𝔞.a c) _ h1
    rw [mem_maximalIdeal, mem_nonunits_iff] at hlc
    exact hlc h2
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hmax : maximalIdeal A = Ideal.span {π} := hπ.maximalIdeal_eq
  obtain ⟨q, hq⟩ : ∃ q : A, ((l : ℕ) : A) = π * q := by
    rw [hmax, Ideal.mem_span_singleton'] at hlA
    obtain ⟨a, ha⟩ := hlA
    exact ⟨a, by rw [← ha, mul_comm]⟩
  have hdvd : ∀ m k : ℕ, m ≤ k → ((l : ℤ) ^ m ∣ ((t.appr k : ℕ) : ℤ) - ((t.appr m : ℕ) : ℤ)) := by
    intro m k hmk
    haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    have e1 : PadicInt.toZModPow m t = PadicInt.toZModPow m ((t.appr m : ℕ) : ℤ_[l]) := by
      rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow]
      exact PadicInt.appr_spec m t
    have e2 : PadicInt.toZModPow m t = PadicInt.toZModPow m ((t.appr k : ℕ) : ℤ_[l]) := by
      rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow]
      exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hmk) (PadicInt.appr_spec k t)
    rw [e1] at e2
    simp only [map_natCast] at e2
    have e3 : (((((t.appr k : ℕ) : ℤ) - ((t.appr m : ℕ) : ℤ)) : ℤ) : ZMod (l ^ m)) = 0 := by
      push_cast
      rw [e2, sub_self]
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (l ^ m)).mp e3
    exact_mod_cast this
  have hcau : ∀ {m k : ℕ}, m ≤ k → ((t.appr m : ℕ) : A) ≡ ((t.appr k : ℕ) : A)
      [SMOD (maximalIdeal A) ^ m • (⊤ : Submodule A A)] := by
    intro m k hmk
    rw [SModEq.sub_mem]
    obtain ⟨z, hz⟩ := hdvd m k hmk
    have hcast : ((t.appr m : ℕ) : A) - ((t.appr k : ℕ) : A) = -(((l : ℕ) : A) ^ m * (z : A)) := by
      have := congrArg (fun w : ℤ => (w : A)) hz
      push_cast at this
      rw [← this]
      ring
    have hmem : ((t.appr m : ℕ) : A) - ((t.appr k : ℕ) : A) ∈ (maximalIdeal A) ^ m := by
      rw [hcast]
      exact neg_mem (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlA m))
    simpa using Submodule.smul_mem_smul hmem (Submodule.mem_top : (1 : A) ∈ ⊤)
  obtain ⟨μ, hμ⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete (maximalIdeal A) A) hcau
  set d : 𝔞.V := f μ - 𝔞.a c (algebraMap ℤ_[l] c.O t) with hd_def
  have hdk : ∀ k : ℕ, ∃ v : 𝔞.V, d = f π ^ k * v := by
    intro k
    have h1 : μ - ((t.appr k : ℕ) : A) ∈ Ideal.span {π ^ k} := by
      rw [← Ideal.span_singleton_pow, ← hmax]
      have := (SModEq.sub_mem.mp (hμ k))
      rw [Ideal.smul_eq_mul, Ideal.mul_top] at this
      have := neg_mem this
      simpa using this
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp h1
    obtain ⟨w', hw'⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec k t)
    refine ⟨f w - f q ^ k * 𝔞.a c (algebraMap ℤ_[l] c.O w'), ?_⟩
    have hl : ((l : ℕ) : 𝔞.V) = f π * f q := by rw [← map_natCast f, hq, map_mul]
    have e1 : f μ = f ((t.appr k : ℕ) : A) + f (w * π ^ k) := by rw [hw]; simp
    have e2 : 𝔞.a c (algebraMap ℤ_[l] c.O t) = 𝔞.a c (algebraMap ℤ_[l] c.O ((t.appr k : ℕ) : ℤ_[l]))
        + 𝔞.a c (algebraMap ℤ_[l] c.O (w' * (l : ℤ_[l]) ^ k)) := by
      rw [hw', ← map_add, ← map_add]; simp
    rw [hd_def, e1, e2]
    simp only [map_natCast, map_mul, map_pow]
    rw [hl]
    ring
  have hd0 : d = 0 := by
    by_contra hd
    have hinj : Function.Injective 𝔞.toK := fun a b h => Subtype.ext h
    obtain ⟨p, hp0, hp⟩ := hf.alg (𝔞.toK d)
    have hp' : Polynomial.eval₂ f d p = 0 := by
      rw [← Polynomial.hom_eval₂] at hp
      exact (map_eq_zero_iff _ hinj).mp hp
    obtain ⟨r, hr, hndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp0 0
    simp only [map_zero, sub_zero] at hr hndvd
    have hr0 : r.coeff 0 ≠ 0 := fun h => hndvd (Polynomial.X_dvd_iff.mpr h)
    have hev : Polynomial.eval₂ f d r = 0 := by
      rw [hr, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X] at hp'
      rcases mul_eq_zero.mp hp' with h | h
      · exact absurd (pow_eq_zero_iff'.mp h).1 hd
      · exact h
    obtain ⟨s, hs⟩ := Polynomial.X_dvd_sub_C (p := r)
    have hc : f (r.coeff 0) = -(d * Polynomial.eval₂ f d s) := by
      have := congrArg (Polynomial.eval₂ f d) hs
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_C, Polynomial.eval₂_mul, Polynomial.eval₂_X, hev] at this
      linear_combination -this
    obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hπ
    obtain ⟨v, hv⟩ := hdk (e + 1)
    have hfπ : f π ≠ 0 := (map_ne_zero_iff f hf.inj).mpr hπ.ne_zero
    have key : f π ^ e * (f (u : A) + f π * (v * Polynomial.eval₂ f d s)) = 0 := by
      rw [hu, map_mul, map_pow] at hc
      linear_combination hc - (Polynomial.eval₂ f d s) * hv
    rcases mul_eq_zero.mp key with h | h
    · exact pow_ne_zero _ hfπ h
    · have hu' : IsUnit (f π * (v * Polynomial.eval₂ f d s)) := by
        have : f π * (v * Polynomial.eval₂ f d s) = -f (u : A) := by linear_combination h
        rw [this]
        exact ((u.isUnit).map f).neg
      exact hπ.not_isUnit (isUnit_of_map_unit f π (isUnit_of_mul_isUnit_left hu'))
  exact ⟨μ, sub_eq_zero.mp hd0⟩

private theorem exists_coef_forall_sub_mem_maximalIdeal_of_isDvr {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) {A : Type} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (f : A →+* 𝔞.V) (hf : 𝔞.IsDvr f) :
    ∃ c₁ : Coef l, ∀ c' : Coef l, c₁.O ≤ c'.O → ∀ x : A, ∃ z : c'.O,
      f x - 𝔞.a c' z ∈ maximalIdeal 𝔞.V := by
  classical
  haveI := hf.fin
  haveI := hf.loc
  haveI : Fintype (ResidueField A) := Fintype.ofFinite _
  choose rep hrep using IsLocalRing.residue_surjective (R := A)
  choose cc y hy using fun r : ResidueField A => 𝔞.alg (f (rep r))
  have hub : ∀ s : Finset (ResidueField A), ∃ c : Coef l, ∀ r ∈ s, (cc r).O ≤ c.O := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨c, -⟩ := UpperTheory.V.HV.exists_coef l 1
      exact ⟨c, by simp⟩
    | insert r s hr ih =>
      obtain ⟨c, hc⟩ := ih
      obtain ⟨c'', h1, h2⟩ := (UpperTheory.V.HV.coefSup l).1 (cc r) c
      refine ⟨c'', fun r' hr' => ?_⟩
      rcases Finset.mem_insert.mp hr' with rfl | h
      · exact h1
      · exact (hc r' h).trans h2
  obtain ⟨c₁, hc₁⟩ := hub Finset.univ
  refine ⟨c₁, fun c' hc' x => ?_⟩
  have hle : (cc (residue A x)).O ≤ c'.O := (hc₁ _ (Finset.mem_univ _)).trans hc'
  refine ⟨Subalgebra.inclusion hle (y (residue A x)), ?_⟩
  rw [𝔞.compat]
  have h1 : x - rep (residue A x) ∈ maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hrep, sub_self]
  have h2 : f (x - rep (residue A x)) ∈ maximalIdeal 𝔞.V := map_nonunit f _ h1
  have := Ideal.add_mem _ h2 (hy (residue A x))
  rw [map_sub] at this
  convert this using 1
  ring

private theorem exists_finset_coef_mem_subfield_closure_of_isDvr {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) {A : Type} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (f : A →+* 𝔞.V) (hf : 𝔞.IsDvr f) (c : Coef l) :
    ∃ s : Finset 𝔞.K, ∀ y : c.O,
      𝔞.toK (𝔞.a c y) ∈ Subfield.closure (Set.range (𝔞.toK.comp f) ∪ ↑s) := by
  classical
  haveI := c.fin
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := ℤ_[l]) (M := c.O)
  refine ⟨Finset.univ.image (fun i => 𝔞.toK (𝔞.a c (b i))), fun y => ?_⟩
  have hy : y ∈ Submodule.span ℤ_[l] (Set.range b) := by rw [hb]; trivial
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact Subfield.subset_closure
      (Or.inr (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
  | zero => rw [map_zero, map_zero]; exact Subfield.zero_mem _
  | add x z _ _ hx hz => rw [map_add, map_add]; exact Subfield.add_mem _ hx hz
  | smul t x _ hx =>
    rw [Algebra.smul_def, map_mul, map_mul]
    refine Subfield.mul_mem _ ?_ hx
    obtain ⟨a, ha⟩ := exists_map_eq_algebraMap_padicInt_of_isDvr 𝔞 f hf c t
    exact Subfield.subset_closure (Or.inl ⟨a, by simp [ha]⟩)

theorem UpperTheory.V.Ws.smallCo :
    ∀ {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) {ι Γ : Type} [Group Γ] [TopologicalSpace Γ] (P : PD ι Γ 𝔞.V), 𝔞.Small P →
      ∃ c₁ : Coef l, ∀ c' : Coef l, c₁.O ≤ c'.O → ∃ (R : Type) (_ : CommRing R) (_ : Algebra c'.O R) (_ : IsCO c'.O R) (f : R →+* 𝔞.V) (Q : PD ι Γ R),
        Function.Injective f ∧ f.comp (algebraMap c'.O R) = 𝔞.a c' ∧ (residue 𝔞.V).comp f = (𝔞.j c').comp (res c'.O R : R →+* ResidueField c'.O) ∧
        Q.Cont (maximalIdeal R) ∧ Q.map f = P := by
  intro l _ 𝔞 ι Γ _ _ P hP
  obtain ⟨A, _, _, _, f, P₁, hf, hP₁, rfl⟩ := hP
  obtain ⟨c₁, hc₁⟩ := exists_coef_forall_sub_mem_maximalIdeal_of_isDvr 𝔞 f hf
  refine ⟨c₁, fun c' hc' => ?_⟩
  obtain ⟨s, hs⟩ := exists_finset_coef_mem_subfield_closure_of_isDvr 𝔞 f hf c'
  obtain ⟨A', _, _, _, f', g, hf', hfg, hcl⟩ := UpperTheory.V.Ws.smallExt 𝔞 A f hf s
  haveI := hf'.loc
  haveI := hf.loc
  haveI := 𝔞.loc c'
  haveI := hf'.fin
  haveI := c'.dvr
  have hmem : ∀ y : c'.O, 𝔞.a c' y ∈ f'.range := fun y => hcl _ (hs y)
  let e : A' ≃+* f'.range := RingEquiv.ofBijective f'.rangeRestrict
    ⟨fun x y h => hf'.inj (congrArg Subtype.val h), f'.rangeRestrict_surjective⟩
  let φ : c'.O →+* A' := (e.symm : f'.range →+* A').comp ((𝔞.a c').codRestrict f'.range hmem)
  have hφ : ∀ y, f' (φ y) = 𝔞.a c' y := by
    intro y
    have : f'.rangeRestrict (φ y) = (𝔞.a c').codRestrict f'.range hmem y := e.apply_symm_apply _
    exact congrArg Subtype.val this
  letI : Algebra c'.O A' := φ.toAlgebra
  have hloc : IsLocalHom (algebraMap c'.O A') := ⟨fun y hy => by
    have : IsUnit (𝔞.a c' y) := by rw [← hφ]; exact hy.map f'
    exact isUnit_of_map_unit (𝔞.a c') y this⟩
  have hcl' : UpperTheory.V.CA.IsCL c'.O A' := ⟨inferInstance, hf'.complete, hloc, Module.Finite.of_finite⟩
  obtain ⟨S, hSmem, -, hco, hpow⟩ := UpperTheory.V.CA.cl_sub c'.O A' hcl'
  haveI := hco
  have hmV : ∀ u : A', u ∈ maximalIdeal A' → f' u ∈ maximalIdeal 𝔞.V := fun u hu => map_nonunit f' u hu
  have hmS : ∀ u : S, u ∈ maximalIdeal S → f' u ∈ maximalIdeal 𝔞.V := by
    intro u hu
    apply hmV
    have := (hpow 1 u).mp (by simpa using hu)
    simpa using this
  have hgS : ∀ x : A, g x ∈ S := by
    intro x
    rw [hSmem]
    obtain ⟨z, hz⟩ := hc₁ c' hc' x
    refine ⟨z, ?_⟩
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map f'
    rw [map_sub, ← RingHom.comp_apply f' g, hfg, show f' (algebraMap c'.O A' z) = 𝔞.a c' z from hφ z] at this
    rw [mem_maximalIdeal, mem_nonunits_iff] at hz
    exact hz this
  let g' : A →+* S := g.codRestrict S hgS
  have hg'm : ∀ x : A, x ∈ maximalIdeal A → g' x ∈ maximalIdeal S := by
    intro x hx
    have h1 : g x ∈ maximalIdeal A' := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have := hu.map f'
      rw [← RingHom.comp_apply f' g, hfg] at this
      exact (mem_nonunits_iff.mp ((mem_maximalIdeal _).mp (map_nonunit f x hx))) this
    have := (hpow 1 (g' x)).mpr (by rw [pow_one]; exact h1)
    rwa [pow_one] at this
  refine ⟨S, inferInstance, inferInstance, hco, f'.comp S.val.toRingHom, P₁.map g', ?_, ?_, ?_, ?_, ?_⟩
  · exact hf'.inj.comp Subtype.val_injective
  · exact RingHom.ext fun y => hφ y
  · ext x
    obtain ⟨a, ha⟩ := UpperTheory.V.Alg.IsCO.res_surj (O := c'.O) x
    have hres0 : UpperTheory.V.Alg.res c'.O S (x - algebraMap c'.O S a) = 0 := by
      simp [UpperTheory.V.Alg.res, (IsLocalRing.residue_eq_zero_iff _).mpr ha]
    have hrx : UpperTheory.V.Alg.res c'.O S x = residue c'.O a := by
      have := hres0
      rw [map_sub, AlgHom.commutes, sub_eq_zero] at this
      rw [this, IsLocalRing.ResidueField.algebraMap_eq]
    have hfx : residue 𝔞.V (f' (x : A')) = residue 𝔞.V (𝔞.a c' a) := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      have h3 : f' ((x : A') - ((algebraMap c'.O S a : S) : A')) ∈ maximalIdeal 𝔞.V := hmS _ ha
      rw [map_sub, show f' ((algebraMap c'.O S a : S) : A') = 𝔞.a c' a from hφ a] at h3
      exact h3
    show residue 𝔞.V (f' (x : A')) = 𝔞.j c' (UpperTheory.V.Alg.res c'.O S x)
    rw [hrx, hfx]
    simp [UpperTheory.V.Ws.Amb.j, IsLocalRing.ResidueField.map_residue]
  · intro i j N
    have hker : (maximalIdeal A) ^ N ≤ Ideal.comap g' ((maximalIdeal S) ^ N) :=
      (Ideal.pow_right_mono (fun x hx => hg'm x hx) N).trans (Ideal.le_comap_pow g' N)
    let ψ : A ⧸ (maximalIdeal A) ^ N →+* S ⧸ (maximalIdeal S) ^ N :=
      Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp g')
        (fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr (hker hx))
    exact (hP₁ i j N).comp ψ
  · rw [← hfg]
    rfl
