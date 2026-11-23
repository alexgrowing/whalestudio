import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLinearHomProd
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsAbelianSchemeOfIsPrincipal
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AutomorphicArithmetic.DivisorFrames.ExistsNsmulMemSumImageLatticeOfSurjectiveMod
import Development.AutomorphicArithmetic.DivisorFrames.ExistsInjectiveLatticeHomRingOfIntegersOfFinrank
open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCM.CplxGen

section Points

open scoped CategoryTheory.Obj

variable {S : Scheme.{0}} (f : Sp ℂ ⟶ S)

private def pt {G : Over S} (x : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback f).obj G) : Over.mk f ⟶ G :=
  Over.homMk (x.left ≫ pullback.fst G.hom f) (by
    have h : x.left ≫ pullback.snd G.hom f = 𝟙 _ := Over.w x
    rw [Category.assoc, pullback.condition, ← Category.assoc, h]
    exact Category.id_comp _)

private theorem pt_injective {G : Over S} : Function.Injective (pt f (G := G)) := fun a b e =>
  Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun q => q.left) e) ((Over.w a).trans (Over.w b).symm))

private theorem pt_surjective {G : Over S} : Function.Surjective (pt f (G := G)) := fun y =>
  ⟨Over.homMk (pullback.lift y.left (𝟙 _) ((Over.w y).trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _),
    Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩

private theorem pt_map {G G' : Over S} (φ : G ⟶ G') (x : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback f).obj G) :
    pt f (x ≫ (Over.pullback f).map φ) = pt f x ≫ φ := by
  refine Over.OverMorphism.ext ?_
  simp only [pt, Over.homMk_left, Over.comp_left, Over.pullback_map_left, Category.assoc]
  exact congrArg (x.left ≫ ·) (pullback.lift_fst _ _ _)

private theorem pt_mul {G : Over S} [GrpObj G] (x y : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback f).obj G) :
    pt f (x * y) = pt f x * pt f y := by
  let ρ : Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ f) ⟶ Over.mk f := Over.homMk (𝟙 _) (by simp)
  have h := (isGrpPullback_pullback G f).2 _ x y (ρ ≫ pt f x) (ρ ≫ pt f y) (Category.id_comp _) (Category.id_comp _)
  rw [← MonObj.comp_mul] at h
  refine Over.OverMorphism.ext ?_
  exact h.symm.trans (Category.id_comp _)

private theorem exists_unif (P : Out.PolAV S) : ∃ (L : LB ((Over.pullback f).obj P.A).left)
    (_ : HolUnif ((Over.pullback f).obj P.A) L P.g), IsAbelianScheme ((Over.pullback f).obj P.A) ∧
      SmoothOfRelativeDimension P.g ((Over.pullback f).obj P.A).hom := by
  have := P.isAb.comm
  let Q := TorsionTauCompare.polOfPullback P _ (isGrpPullback_pullback P.A f)
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨v, -⟩ := thetaUnifAV_all Q rig hrig
  exact ⟨_, v, Q.isAb, Q.smoothDim⟩

private theorem exists_unif_points (P Q : Out.PolAV S) :
    ∃ (ΛA : Submodule ℤ (Fin P.g → ℂ)) (ΛB : Submodule ℤ (Fin Q.g → ℂ))
      (eA : (Fin P.g → ℂ) → (Over.mk f ⟶ P.A)) (eB : (Fin Q.g → ℂ) → (Over.mk f ⟶ Q.A)),
      (∀ z w, eA (z + w) = eA z * eA w) ∧ Function.Surjective eA ∧ (∀ z, eA z = 1 ↔ z ∈ ΛA) ∧
      DiscreteTopology ΛA ∧ Submodule.span ℝ (ΛA : Set (Fin P.g → ℂ)) = ⊤ ∧
      (∀ z w, eB (z + w) = eB z * eB w) ∧ Function.Surjective eB ∧ (∀ z, eB z = 1 ↔ z ∈ ΛB) ∧
      DiscreteTopology ΛB ∧
      (∀ φ : P.A ⟶ P.A, IsMonHom φ → ∃ M : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ), ∀ z, eA (M z) = eA z ≫ φ) ∧
      (∀ φ : Q.A ⟶ Q.A, IsMonHom φ → ∃ M : (Fin Q.g → ℂ) →ₗ[ℂ] (Fin Q.g → ℂ), ∀ z, eB (M z) = eB z ≫ φ) ∧
      (∀ φ : P.A ⟶ Q.A, IsMonHom φ → ∃ M : (Fin P.g → ℂ) →ₗ[ℂ] (Fin Q.g → ℂ), ∀ z, eB (M z) = eA z ≫ φ) := by
  obtain ⟨L, u, hA, hdA⟩ := exists_unif f P
  obtain ⟨L', v, hB, hdB⟩ := exists_unif f Q
  have hu := TorusTransfer.tangent_bijective u hdA
  have hv := TorusTransfer.tangent_bijective v hdB
  have one : ∀ {G : Over S} [GrpObj G] (x : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback f).obj G), pt f x = 1 ↔ x = 1 :=
    fun {G} _ x => map_eq_one_iff (MonoidHom.mk' (pt f (G := G)) (pt_mul f)) (pt_injective f)
  refine ⟨u.Λ, v.Λ, fun z => pt f (u.ex z), fun z => pt f (v.ex z),
    fun z w => by beta_reduce; rw [u.ex_add, pt_mul],
    (pt_surjective f).comp u.ex_onto, fun z => (one _).trans (u.ker z), u.discrete, u.full,
    fun z w => by beta_reduce; rw [v.ex_add, pt_mul], (pt_surjective f).comp v.ex_onto, fun z => (one _).trans (v.ker z),
    v.discrete, fun φ _ => ?_, fun φ _ => ?_, fun φ _ => ?_⟩
  · obtain ⟨M, hM, -⟩ := HomLinear.exists_linear_of_isMonHom _ _ hA hA _ _ _ _ u u hu.1 hu.2
      ((Over.pullback f).map φ) inferInstance
    exact ⟨M, fun z => by beta_reduce; rw [hM, pt_map]⟩
  · obtain ⟨M, hM, -⟩ := HomLinear.exists_linear_of_isMonHom _ _ hB hB _ _ _ _ v v hv.1 hv.2
      ((Over.pullback f).map φ) inferInstance
    exact ⟨M, fun z => by beta_reduce; rw [hM, pt_map]⟩
  · obtain ⟨M, hM, -⟩ := HomLinear.exists_linear_of_isMonHom _ _ hA hB _ _ _ _ u v hv.1 hv.2
      ((Over.pullback f).map φ) inferInstance
    exact ⟨M, fun z => by beta_reduce; rw [hM, pt_map]⟩

end Points

private theorem lattice_mem_closure (E : Type) [Field E] [NumberField E] (gA gB p : ℕ)
    (ΛA : Submodule ℤ (Fin gA → ℂ)) (ΛB : Submodule ℤ (Fin gB → ℂ)) (αA : 𝓞 E →+* Module.End ℂ (Fin gA → ℂ))
    (αB : 𝓞 E →+* Module.End ℂ (Fin gB → ℂ)) (J : Fin p → (Fin gA → ℂ) →ₗ[ℂ] (Fin gB → ℂ))
    (hdim : 2 * gA ≤ Module.finrank ℚ E) (hAd : DiscreteTopology ΛA)
    (hAf : Submodule.span ℝ (ΛA : Set (Fin gA → ℂ)) = ⊤) (hBd : DiscreteTopology ΛB)
    (sA : ∀ s, ∀ z ∈ ΛA, αA s z ∈ ΛA) (sB : ∀ s, ∀ z ∈ ΛB, αB s z ∈ ΛB)
    (inter : ∀ a s z, J a (αA s z) = αB s (J a z)) (hJ : ∀ a, ∀ z ∈ ΛA, J a z ∈ ΛB)
    (honto : ∀ w, ∃ v : Fin p → (Fin gA → ℂ), w - ∑ a, J a (v a) ∈ ΛB) (l : Fin gB → ℂ) (hl : l ∈ ΛB) :
    l ∈ AddSubmonoid.closure {w : Fin gB → ℂ | ∃ (m : ℕ) (z : Fin p → 𝓞 E) (x : Fin gA → ℂ), 0 < m ∧ x ∈ ΛA ∧
      (∀ x' ∈ ΛA, (m : ℂ)⁻¹ • ∑ a, J a (αA (z a) x') ∈ ΛB) ∧ w = (m : ℂ)⁻¹ • ∑ a, J a (αA (z a) x)} := by
  classical
  obtain ⟨N, x, hN, hx, hNl⟩ := UpperTheory.exists_nsmul_mem_sum_image_lattice_of_surjective_mod gA gB p ΛA ΛB J hAf hBd hJ honto l hl
  obtain ⟨j, hj, hjs⟩ := UpperTheory.exists_injective_lattice_hom_ringOfIntegers_of_finrank_ge E gA ΛA αA hdim hAd sA
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  let I : Ideal (𝓞 E) := Ideal.span (Set.range j)
  by_cases hI : I = ⊥
  · have h0 : ∀ a, x a = 0 := fun a => by
      have h : j ⟨x a, hx a⟩ ∈ I := Ideal.subset_span ⟨_, rfl⟩
      rw [hI, Ideal.mem_bot, ← map_zero j] at h
      exact congrArg Subtype.val (hj h)
    simp only [h0, map_zero, Finset.sum_const_zero] at hNl
    rw [(smul_eq_zero.1 hNl).resolve_left hN.ne']
    exact zero_mem _
  obtain ⟨c, hcI, hc⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨I', hI'⟩ : I ∣ Ideal.span {c} := Ideal.dvd_span_singleton.2 hcI
  have hmem : ∀ t ∈ I, ∃ y : ΛA, j y = t := fun t ht => by
    refine Submodule.span_induction (p := fun t _ => ∃ y : ΛA, j y = t) (fun t ht => ht) ⟨0, map_zero _⟩ ?_ ?_ ht
    · rintro _ _ - - ⟨y, rfl⟩ ⟨y', rfl⟩
      exact ⟨y + y', map_add _ _ _⟩
    · rintro s _ - ⟨y, rfl⟩
      exact ⟨_, hjs s y⟩
  have hdiv : ∀ b ∈ I', ∀ y : ΛA, ∃ u, u * c = j y * b := fun b hb y =>
    Ideal.mem_span_singleton'.1 (hI' ▸ Ideal.mul_mem_mul (Ideal.subset_span ⟨y, rfl⟩) hb)
  have key : ∀ t ∈ I * I', ∃ u, u * c = t ∧ αB u l ∈ AddSubmonoid.closure
      {w : Fin gB → ℂ | ∃ (m : ℕ) (z : Fin p → 𝓞 E) (x : Fin gA → ℂ), 0 < m ∧ x ∈ ΛA ∧
        (∀ x' ∈ ΛA, (m : ℂ)⁻¹ • ∑ a, J a (αA (z a) x') ∈ ΛB) ∧ w = (m : ℂ)⁻¹ • ∑ a, J a (αA (z a) x)} := by
    intro t ht
    refine Submodule.mul_induction_on ht (fun r hr b hb => ?_) ?_
    · obtain ⟨y, rfl⟩ := hmem r hr
      choose φ hφ using hdiv b hb
      have hsw : ∀ y y' : ΛA, αA (φ y) y' = αA (φ y') y := fun y y' => by
        have h : (⟨αA (φ y) y', sA _ _ y'.2⟩ : ΛA) = ⟨αA (φ y') y, sA _ _ y.2⟩ := hj (by
          rw [hjs, hjs]
          refine mul_right_cancel₀ hc ?_
          linear_combination j y' * hφ y - j y * hφ y')
        exact congrArg Subtype.val h
      have hval : ∀ y' : ΛA, (N : ℂ)⁻¹ • ∑ a, J a (αA (φ ⟨x a, hx a⟩) y') = αB (φ y') l := fun y' => by
        have : ∑ a, J a (αA (φ ⟨x a, hx a⟩) y') = N • αB (φ y') l := by
          rw [← map_nsmul, hNl, map_sum]
          exact Finset.sum_congr rfl fun a _ => by rw [hsw, inter]
        rw [this, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN0, one_smul]
      refine ⟨φ y, hφ y, AddSubmonoid.subset_closure ⟨N, fun a => φ ⟨x a, hx a⟩, y, hN, y.2, fun x' hx' => ?_,
        (hval y).symm⟩⟩
      rw [hval ⟨x', hx'⟩]
      exact sB _ _ hl
    · rintro _ _ ⟨u, rfl, hu⟩ ⟨u', rfl, hu'⟩
      exact ⟨u + u', add_mul _ _ _, by rw [map_add, LinearMap.add_apply]; exact add_mem hu hu'⟩
  obtain ⟨u, hu, h⟩ := key c (hI' ▸ Ideal.mem_span_singleton_self c)
  obtain rfl : u = 1 := mul_right_cancel₀ hc (hu.trans (_root_.one_mul c).symm)
  simpa using h

section Unif

variable {P : Type} [CommGroup P] {g : ℕ} {e : (Fin g → ℂ) → P} {Λ : Submodule ℤ (Fin g → ℂ)}

private theorem eq_zero_of_smul_mem (hd : DiscreteTopology Λ) {z : Fin g → ℂ} (hz : ∀ t : ℂ, t • z ∈ Λ) : z = 0 := by
  have hc : Continuous fun t : ℂ => (⟨t • z, hz t⟩ : Λ) := by fun_prop
  have h := (IsLocallyConstant.iff_continuous _).2 hc |>.apply_eq_of_preconnectedSpace 1 0
  simpa using congrArg Subtype.val h

private theorem e_zero (hadd : ∀ z w, e (z + w) = e z * e w) : e 0 = 1 := by
  have h := hadd 0 0
  rw [add_zero] at h
  simpa using h.symm

private def eHom (hadd : ∀ z w, e (z + w) = e z * e w) : (Fin g → ℂ) →+ Additive P where
  toFun z := Additive.ofMul (e z)
  map_zero' := by rw [e_zero hadd]; rfl
  map_add' z w := by rw [hadd]; rfl

private theorem e_sub (hadd : ∀ z w, e (z + w) = e z * e w) (z w : Fin g → ℂ) : e (z - w) = e z * (e w)⁻¹ := by
  have h := hadd (z - w) w
  rw [sub_add_cancel] at h
  rw [h, mul_inv_cancel_right]

private theorem e_nsmul (hadd : ∀ z w, e (z + w) = e z * e w) (k : ℕ) (z : Fin g → ℂ) : e (k • z) = e z ^ k :=
  congrArg Additive.toMul (map_nsmul (eHom hadd) k z)

private theorem e_sum (hadd : ∀ z w, e (z + w) = e z * e w) {Idx : Type} (s : Finset Idx) (f : Idx → Fin g → ℂ) :
    e (s.sum f) = s.prod (fun i => e (f i)) :=
  congrArg Additive.toMul (map_sum (eHom hadd) f s)

private theorem mem_of_eq (hadd : ∀ z w, e (z + w) = e z * e w) (hker : ∀ z, e z = 1 ↔ z ∈ Λ) {z w : Fin g → ℂ}
    (h : e z = e w) : z - w ∈ Λ := by
  rw [← hker, e_sub hadd, h, mul_inv_cancel]

private theorem rigid (hadd : ∀ z w, e (z + w) = e z * e w) (hker : ∀ z, e z = 1 ↔ z ∈ Λ) (hd : DiscreteTopology Λ)
    {W : Type} [AddCommGroup W] [Module ℂ W] (M M' : W →ₗ[ℂ] (Fin g → ℂ)) (h : ∀ z, e (M z) = e (M' z)) :
    M = M' := by
  ext1 z
  have := eq_zero_of_smul_mem hd (z := M z - M' z) fun t => by
    have := mem_of_eq hadd hker (h (t • z))
    rwa [map_smul, map_smul, ← smul_sub] at this
  exact sub_eq_zero.1 this

end Unif

private theorem comp_prod' {S : Scheme.{0}} {T A B : Over S} [MonObj B] [IsCommMonObj B] {Idx : Type} (s : Finset Idx)
    (x : T ⟶ A) (f : Idx → (A ⟶ B)) : x ≫ s.prod f = s.prod (fun i => x ≫ f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.comp_mul, ih]

private theorem exists_widePullback_of_iteratedLine {P : Type} [CommGroup P] {p : ℕ} (f : Fin p ⊕ Fin 0 → P) (g : Fin p → P)
    (h : ∀ a, g a = f (Sum.inl a)) :
    (List.ofFn fun j : Fin (p + 0) => f (finSumFinEquiv.symm j)).prod * (∏ a, g a)⁻¹ = 1 := by
  rw [List.prod_ofFn, Equiv.prod_comp finSumFinEquiv.symm f, Fintype.prod_sum_type, mul_inv_eq_one]
  simp [h]

theorem _root_.GlobalTheory.T.cm_torsion_mem_closure_generators : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (n : ℕ), 0 < n →
    ∀ y : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G, y ^ n = 1 →
    y ∈ Submonoid.closure {w : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G |
      ∃ (m : ℕ) (x : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G) (z : Fin p → 𝓞 E),
        0 < m ∧ x ^ (n * m) = 1 ∧
        (∀ x' : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G, x' ^ m = 1 →
          x' ≫ ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a) = 1) ∧
        w = x ≫ ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)} := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p X n hn y hy
  classical
  obtain ⟨ΛA, ΛB, eA, eB, hAadd, hAsurj, hAker, hAd, hAf, hBadd, hBsurj, hBker, hBd, lA, lB, lJ⟩ :=
    exists_unif_points (spMap (σ₁.comp (algebraMap (𝓞 K) K))) (X.A true).pol X.B.pol
  choose αA hαA using fun s => lA ((X.A true).t.act.act s) ((X.A true).t.act.hom s)
  choose αB hαB using fun s => lB (X.B.t.act.act s) (X.B.t.act.hom s)
  choose J hJ using fun a : Fin p => lJ (GlobalTheory.FlatCM.phiP X a) (X.lin (Sum.inl a)).isMonHom
  have hdim : 2 * (X.A true).g ≤ Module.finrank ℚ E := by
    rw [GlobalTheory.CMSharedCompare.dim_eq (X.A true) X.split X.typeP X.ρ_sq]
    omega
  have act0 : ∀ {G : Over (Sp (𝓞 K))} [GrpObj G] (a : OAct (𝓞 E) G), a.act 0 = 1 := by
    intro G _ a
    have h := a.add 0 0
    rw [add_zero] at h
    simpa using h.symm

  let αA' : 𝓞 E →+* Module.End ℂ (Fin (X.A true).g → ℂ) :=
    { toFun := αA
      map_one' := rigid hAadd hAker hAd _ _ fun z => by
        rw [hαA, (X.A true).t.act.one, Category.comp_id]; rfl
      map_mul' := fun s t => rigid hAadd hAker hAd _ _ fun z => by
        show eA (αA (s * t) z) = eA (αA s (αA t z))
        rw [hαA, hαA, hαA, Category.assoc, ← (X.A true).t.act.mul, mul_comm]
      map_zero' := rigid hAadd hAker hAd _ _ fun z => by
        show eA (αA 0 z) = eA 0
        rw [hαA, act0, MonObj.comp_one, e_zero hAadd]
      map_add' := fun s t => rigid hAadd hAker hAd _ _ fun z => by
        show eA (αA (s + t) z) = eA (αA s z + αA t z)
        rw [hαA, hAadd, hαA, hαA, (X.A true).t.act.add, MonObj.comp_mul] }
  let αB' : 𝓞 E →+* Module.End ℂ (Fin X.B.g → ℂ) :=
    { toFun := αB
      map_one' := rigid hBadd hBker hBd _ _ fun z => by
        rw [hαB, X.B.t.act.one, Category.comp_id]; rfl
      map_mul' := fun s t => rigid hBadd hBker hBd _ _ fun z => by
        show eB (αB (s * t) z) = eB (αB s (αB t z))
        rw [hαB, hαB, hαB, Category.assoc, ← X.B.t.act.mul, mul_comm]
      map_zero' := rigid hBadd hBker hBd _ _ fun z => by
        show eB (αB 0 z) = eB 0
        rw [hαB, act0, MonObj.comp_one, e_zero hBadd]
      map_add' := fun s t => rigid hBadd hBker hBd _ _ fun z => by
        show eB (αB (s + t) z) = eB (αB s z + αB t z)
        rw [hαB, hBadd, hαB, hαB, X.B.t.act.add, MonObj.comp_mul] }
  have lin : ∀ a, Serre.IsLinearHom (X.A true).t.act X.B.t.act (GlobalTheory.FlatCM.phiP X a) := fun a => X.lin (Sum.inl a)
  have stabA : ∀ s, ∀ z ∈ ΛA, αA' s z ∈ ΛA := fun s z hz => by
    have := (X.A true).t.act.hom s
    rw [← hAker] at hz ⊢
    show eA (αA s z) = 1
    rw [hαA, hz, MonObj.one_comp]
  have stabB : ∀ s, ∀ z ∈ ΛB, αB' s z ∈ ΛB := fun s z hz => by
    have := X.B.t.act.hom s
    rw [← hBker] at hz ⊢
    show eB (αB s z) = 1
    rw [hαB, hz, MonObj.one_comp]
  have inter : ∀ a s z, J a (αA' s z) = αB' s (J a z) := fun a s z => by
    have h := rigid hBadd hBker hBd ((J a).comp (αA s)) ((αB s).comp (J a)) fun z => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hJ, hαA, hαB, hJ, Category.assoc, (lin a).comm,
        Category.assoc]
    exact congrArg (fun M : (Fin (X.A true).g → ℂ) →ₗ[ℂ] (Fin X.B.g → ℂ) => M z) h
  have hJΛ : ∀ a, ∀ z ∈ ΛA, J a z ∈ ΛB := fun a z hz => by
    have := (lin a).isMonHom
    rw [← hAker] at hz
    rw [← hBker, hJ, hz, MonObj.one_comp]
  have honto : ∀ w, ∃ v : Fin p → (Fin (X.A true).g → ℂ), w - ∑ a, J a (v a) ∈ ΛB := by
    intro w
    obtain ⟨x, hx⟩ := X.onto (eB w)
    choose v hv using fun a : Fin p => hAsurj (x (Sum.inl a))
    refine ⟨v, (hBker _).1 ?_⟩
    rw [e_sub hBadd, e_sum hBadd, hx]
    exact exists_widePullback_of_iteratedLine (fun j : Fin p ⊕ Fin 0 => (x j ≫ X.φ j :
      Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G)) (fun a => eB (J a (v a)))
      fun a => (hJ a (v a)).trans (congrArg (· ≫ GlobalTheory.FlatCM.phiP X a) (hv a))
  have hG : ∀ (u : Fin (X.A true).g → ℂ) (z : Fin p → 𝓞 E),
      eA u ≫ ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a) = eB (∑ a, J a (αA' (z a) u)) := by
    intro u z
    rw [comp_prod', e_sum hBadd]
    refine Finset.prod_congr rfl fun a _ => ?_
    show _ = eB (J a (αA (z a) u))
    rw [hJ, hαA, Category.assoc]
  obtain ⟨w, rfl⟩ := hBsurj y
  have hnw : n • w ∈ ΛB := (hBker _).1 (by rw [e_nsmul hBadd, hy])
  have hcl := lattice_mem_closure E (X.A true).g X.B.g p ΛA ΛB αA' αB' J hdim hAd hAf hBd
    stabA stabB inter hJΛ honto _ hnw
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have key : ∀ l ∈ AddSubmonoid.closure {w : Fin X.B.g → ℂ | ∃ (m : ℕ) (z : Fin p → 𝓞 E) (x : Fin (X.A true).g → ℂ),
      0 < m ∧ x ∈ ΛA ∧ (∀ x' ∈ ΛA, (m : ℂ)⁻¹ • ∑ a, J a (αA' (z a) x') ∈ ΛB) ∧
        w = (m : ℂ)⁻¹ • ∑ a, J a (αA' (z a) x)},
      eB ((n : ℂ)⁻¹ • l) ∈ Submonoid.closure {w : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G |
        ∃ (m : ℕ) (x : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G) (z : Fin p → 𝓞 E),
          0 < m ∧ x ^ (n * m) = 1 ∧
          (∀ x' : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G, x' ^ m = 1 →
            x' ≫ ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a) = 1) ∧
          w = x ≫ ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)} := by
    intro l hl
    induction hl using AddSubmonoid.closure_induction with
    | mem t ht =>
      obtain ⟨m, z, x, hm, hx, hkill, rfl⟩ := ht
      have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      refine Submonoid.subset_closure ⟨m, eA (((n * m : ℕ) : ℂ)⁻¹ • x), z, hm, ?_, ?_, ?_⟩
      · rw [← e_nsmul hAadd, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
          mul_inv_cancel₀ (by exact_mod_cast (Nat.mul_pos hn hm).ne'), one_smul]
        exact (hAker x).2 hx
      · intro x' hx'
        obtain ⟨u, rfl⟩ := hAsurj x'
        have hu : m • u ∈ ΛA := (hAker _).1 (by rw [e_nsmul hAadd, hx'])
        have h := hkill _ hu
        have e1 : (m : ℂ)⁻¹ • ∑ a, J a (αA' (z a) (m • u)) = ∑ a, J a (αA' (z a) u) := by
          simp only [map_nsmul, ← Finset.smul_sum]
          rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hm0, one_smul]
        rw [e1] at h
        rw [hG, (hBker _).2 h]
      · rw [hG]
        congr 1
        simp only [map_smul, ← Finset.smul_sum, smul_smul, Nat.cast_mul, mul_inv]
    | zero => rw [smul_zero, e_zero hBadd]; exact Submonoid.one_mem _
    | add a b _ _ ha hb => rw [smul_add, hBadd]; exact Submonoid.mul_mem _ ha hb
  have := key _ hcl
  rwa [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn0, one_smul] at this

end GlobalTheory.FlatCM.CplxGen

end
