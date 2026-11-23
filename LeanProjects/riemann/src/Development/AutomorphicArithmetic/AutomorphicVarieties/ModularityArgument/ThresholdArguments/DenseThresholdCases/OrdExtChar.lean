import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.ExtChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
namespace UpperTheory.V.Z.Ord.ExtensionCharacterAlt
section Poly
variable {C : Type*} [Field C]
private theorem coeff_pow_lin (a : C) (n : ℕ) :
    ((1 + Polynomial.C a * X) ^ n).coeff 0 = 1 ∧ ((1 + Polynomial.C a * X) ^ n).coeff 1 = (n : C) * a := by
  induction n with
  | zero => simp [Polynomial.coeff_one]
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih
    rw [pow_succ]
    refine ⟨by rw [mul_coeff_zero, h0]; simp, ?_⟩
    rw [Polynomial.mul_coeff_one, h0, h1]
    simp [Polynomial.coeff_one]
    ring
private theorem coeff_prod_lin {J : Type*} (S : Finset J) (a : J → C) (n : J → ℕ) :
    (∏ j ∈ S, (1 + Polynomial.C (a j) * X) ^ n j).coeff 0 = 1 ∧
      (∏ j ∈ S, (1 + Polynomial.C (a j) * X) ^ n j).coeff 1 = ∑ j ∈ S, (n j : C) * a j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Polynomial.coeff_one]
  | insert j S hj ih =>
    obtain ⟨h0, h1⟩ := ih
    obtain ⟨g0, g1⟩ := coeff_pow_lin (a j) (n j)
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    refine ⟨by rw [mul_coeff_zero, h0, g0, one_mul], ?_⟩
    rw [Polynomial.mul_coeff_one, h0, h1, g0, g1]
    ring
private theorem sum_eq_zero_of_prod {J : Type*} [Fintype J] (a : J → C) (e : J → ℤ) (T : Set C) (hT : T.Infinite)
    (hne : ∀ t ∈ T, ∀ j, 1 + t * a j ≠ 0) (h : ∀ t ∈ T, ∏ j, (1 + t * a j) ^ e j = 1) :
    ∑ j, (e j : C) * a j = 0 := by
  set P : C[X] := ∏ j, (1 + Polynomial.C (a j) * X) ^ (e j).toNat with hP
  set Q : C[X] := ∏ j, (1 + Polynomial.C (a j) * X) ^ (-e j).toNat with hQ
  have hev : ∀ t ∈ T, eval t P = eval t Q := fun t ht => by
    simp only [hP, hQ, eval_prod, eval_pow, eval_add, eval_mul, eval_one, eval_C, eval_X]
    have h1 := h t ht
    have h2 : ∀ j, (1 + t * a j) ^ e j = (1 + a j * t) ^ (e j).toNat / (1 + a j * t) ^ (-e j).toNat := fun j => by
      rw [mul_comm (a j) t, ← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ (hne t ht j), Int.toNat_sub_toNat_neg]
    simp_rw [h2] at h1
    rw [Finset.prod_div_distrib, div_eq_one_iff_eq] at h1
    · exact h1
    · exact Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (by rw [mul_comm]; exact hne t ht j)
  have hPQ : P = Q := Polynomial.eq_of_infinite_eval_eq P Q (hT.mono fun t ht => hev t ht)
  have c1 : P.coeff 1 = _ := (coeff_prod_lin Finset.univ a fun j => (e j).toNat).2
  have c2 : Q.coeff 1 = _ := (coeff_prod_lin Finset.univ a fun j => (-e j).toNat).2
  rw [hPQ, c2] at c1
  have : ∀ j, (e j : C) * a j = ((e j).toNat : C) * a j - ((-e j).toNat : C) * a j := fun j => by
    rw [← sub_mul]
    congr 1
    have := Int.toNat_sub_toNat_neg (e j)
    exact_mod_cast congrArg (Int.cast : ℤ → C) this.symm
  simp_rw [this]
  rw [Finset.sum_sub_distrib, c1, sub_self]
end Poly
section Emb
variable {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime]
private theorem tendsto_pow (w : HeightOneSpectrum (𝓞 L)) (hl : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) :
    Filter.Tendsto (fun m : ℕ => ((l : ℕ) : w.adicCompletion L) ^ m) Filter.atTop (nhds 0) := by
  refine Valued.tendsto_zero_pow_of_v_lt_one ?_
  have h1 : ((l : ℕ) : w.adicCompletion L) = algebraMap L (w.adicCompletion L) (((l : ℕ) : 𝓞 L) : L) := by simp
  rw [h1, HeightOneSpectrum.algebraMap_adicCompletion]
  simp only [Function.comp_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem w _).2 hl
private theorem exp_eq_zero (w : HeightOneSpectrum (𝓞 L)) (hl : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal)
    [Fintype (UpperTheory.V.W.Emb l w)] (U : Subgroup (w.adicCompletion L)ˣ) (hU : IsOpen (U : Set (w.adicCompletion L)ˣ))
    (e : UpperTheory.V.W.Emb l w → ℤ)
    (h : ∀ y ∈ U, ∏ j : UpperTheory.V.W.Emb l w, j.1 ((y : (w.adicCompletion L)ˣ) : w.adicCompletion L) ^ e j = 1) : e = 0 := by
  classical
  have hlin : ∀ z : w.adicCompletion L, ∑ j : UpperTheory.V.W.Emb l w, (e j : Qbar l) * j.1 z = 0 := fun z => by
    obtain ⟨W, hW, hWU⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hU
    have h1W : (1 : w.adicCompletion L) ∈ W ∩ {0}ᶜ := ⟨by
      have : (1 : (w.adicCompletion L)ˣ) ∈ Units.val ⁻¹' W := by rw [hWU]; exact U.one_mem
      simpa using this, by simp⟩
    have ht : Filter.Tendsto (fun m : ℕ => 1 + ((l : ℕ) : w.adicCompletion L) ^ m * z) Filter.atTop
        (nhds 1) := by
      simpa using ((tendsto_pow w hl).mul_const z).const_add 1
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 (ht ((hW.inter isOpen_compl_singleton).mem_nhds h1W))
    have hy : ∀ m, M ≤ m → ∃ y ∈ U, ((y : (w.adicCompletion L)ˣ) : w.adicCompletion L) =
        1 + ((l : ℕ) : w.adicCompletion L) ^ m * z := fun m hm => by
      obtain ⟨h1, h2⟩ := hM m hm
      refine ⟨Units.mk0 _ h2, ?_, rfl⟩
      have : Units.mk0 _ h2 ∈ Units.val ⁻¹' W := h1
      rw [hWU] at this
      exact this
    have hinj : Function.Injective fun m : ℕ => ((l : ℕ) : Qbar l) ^ (m + M) := fun a b hab => by
      have h2 : (((l : ℕ) ^ (a + M) : ℕ) : Qbar l) = ((l ^ (b + M) : ℕ) : Qbar l) := by
        push_cast
        exact hab
      have := Nat.pow_right_injective (Fact.out : l.Prime).two_le (Nat.cast_injective h2)
      omega
    refine sum_eq_zero_of_prod (fun j => j.1 z) e (Set.range fun m : ℕ => ((l : ℕ) : Qbar l) ^ (m + M))
      (Set.infinite_range_of_injective hinj) ?_ ?_
    · rintro _ ⟨m, rfl⟩ j
      obtain ⟨y, -, hy⟩ := hy (m + M) (by omega)
      have := (map_ne_zero j.1).2 y.ne_zero
      rw [hy] at this
      simpa using this
    · rintro _ ⟨m, rfl⟩
      obtain ⟨y, hyU, hy⟩ := hy (m + M) (by omega)
      refine Eq.trans ?_ (h y hyU)
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [hy]
      simp
  have hind := (linearIndependent_monoidHom (w.adicCompletion L) (Qbar l)).comp
    (fun j : UpperTheory.V.W.Emb l w => (j.1 : w.adicCompletion L →* Qbar l)) (fun a b hab => by
      refine Subtype.ext (RingHom.ext fun x => ?_)
      exact DFunLike.congr_fun hab x)
  have := Fintype.linearIndependent_iff.1 hind (fun j => (e j : Qbar l)) (funext fun z => by
    simpa [Finset.sum_apply] using hlin z)
  funext j
  exact_mod_cast this j
end Emb
section Grp
variable {J T M : Type*} [Fintype J] [Fintype T] [DecidableEq T] [CommGroup M]
private theorem prod_zpow_sum {S : Type*} (F : Finset S) (a : M) (c : S → ℤ) :
    ∏ j ∈ F, a ^ c j = a ^ ∑ j ∈ F, c j := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert j F hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add]
private theorem prod_fib (r : J → T) (p : J → M) (q : T → M)
    (hq : ∀ τ, q τ = ∏ j ∈ Finset.univ.filter (fun j => r j = τ), p j) (b : T → ℤ) :
    ∏ j, p j ^ b (r j) = ∏ τ, q τ ^ b τ := by
  rw [← Finset.prod_fiberwise Finset.univ r]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [hq, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [(Finset.mem_filter.1 hj).2]
private theorem prod_base (r : J → T) (q : T → M) (c : J → ℤ) :
    ∏ j, q (r j) ^ c j = ∏ τ, q τ ^ ∑ j ∈ Finset.univ.filter (fun j => r j = τ), c j := by
  rw [← Finset.prod_fiberwise Finset.univ r]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← prod_zpow_sum]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [(Finset.mem_filter.1 hj).2]
private theorem prod_collect (r : J → T) (p : J → M) (q : T → M)
    (hq : ∀ τ, q τ = ∏ j ∈ Finset.univ.filter (fun j => r j = τ), p j) (d : ℤ) (c : J → ℤ) :
    (∏ j, p j ^ c j) ^ d * (∏ j, q (r j) ^ c j)⁻¹ =
      ∏ j, p j ^ (d * c j - ∑ i ∈ Finset.univ.filter (fun i => r i = r j), c i) := by
  rw [prod_base r q c, ← prod_fib r p q hq, ← Finset.prod_zpow, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← zpow_mul, ← zpow_neg, ← zpow_add]
  congr 1
  ring
end Grp
section Ker
variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {C : Type} [CommGroup C] [TopologicalSpace C] [T2Space C]
private theorem ker_art (h : IsPlaceOver A v) {a : Weil h →* (v.adicCompletion K)ˣ} (ha : IsLocalArtin h a)
    (κ : Dec (F := K) A →* C) (hκ : Continuous κ) (s : Weil h) (hs : a s = 1) :
    κ (Subgroup.inclusion (Weil_le_Dec h) s) = 1 := by
  classical
  by_contra hne
  haveI : CompactSpace (Dec (F := K) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  set g := Subgroup.inclusion (Weil_le_Dec h) s with hg
  have hcl : IsClosed (κ.ker : Set (Dec (F := K) A)) := isClosed_singleton.preimage hκ
  have hWo : IsOpen ((fun x => g * x) ⁻¹' (κ.ker : Set (Dec (F := K) A))ᶜ) :=
    hcl.isOpen_compl.preimage (continuous_mul_left g)
  have h1W : (1 : Dec (F := K) A) ∈ (fun x => g * x) ⁻¹' (κ.ker : Set (Dec (F := K) A))ᶜ := by
    simpa using hne
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWo h1W
  set N : Subgroup (Dec (F := K) A) := κ.ker ⊔ U.toSubgroup with hN
  have hNo : IsOpen (N : Set (Dec (F := K) A)) := Subgroup.isOpen_mono le_sup_right U.isOpen
  haveI : N.Normal := Subgroup.sup_normal _ _
  have hgN : g ∉ N := fun hm => by
    have hm' : g ∈ ((κ.ker ⊔ U.toSubgroup : Subgroup _) : Set (Dec (F := K) A)) := hm
    rw [Subgroup.mul_normal] at hm'
    obtain ⟨k, hk, u, hu, e⟩ := hm'
    have h2 := hU (U.toSubgroup.inv_mem hu)
    apply h2
    have : g * u⁻¹ = k := by rw [← e]; group
    simpa [this] using hk
  have hcomm : ∀ x y : Dec (F := K) A ⧸ N, x * y = y * x := fun x y => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    refine Subgroup.mem_sup_left ?_
    simp [MonoidHom.mem_ker, mul_comm]
    rw [mul_mul_mul_comm]
    simp
  letI : CommGroup (Dec (F := K) A ⧸ N) := { (inferInstance : Group (Dec (F := K) A ⧸ N)) with mul_comm := hcomm }
  haveI : Finite (Dec (F := K) A ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNo
  haveI : NeZero (Monoid.exponent (Dec (F := K) A ⧸ N)) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Dec (F := K) A ⧸ N) ℂ
    (a := (g : Dec (F := K) A ⧸ N)) (fun e => hgN ((QuotientGroup.eq_one_iff g).1 e))
  let ξ : Weil h →* ℂˣ := (φ.comp (QuotientGroup.mk' N)).comp (Subgroup.inclusion (Weil_le_Dec h))
  have hi : Continuous ((Subgroup.inclusion (Weil_le_Dec h)).comp (ineIncl h)) := continuous_subtype_val.subtype_mk _
  have hξ : GlobalTheory.WeilDeligne.IsSmooth ξ := by
    refine Subgroup.isOpen_mono (H₁ := N.comap ((Subgroup.inclusion (Weil_le_Dec h)).comp (ineIncl h)))
      (H₂ := (ξ.comp (ineIncl h)).ker) (fun x hx => ?_) (hNo.preimage hi)
    exact (congrArg φ ((QuotientGroup.eq_one_iff _).2 hx)).trans (map_one φ)
  obtain ⟨χ, -, e⟩ := ha.factor ξ hξ
  apply hφ
  have := DFunLike.congr_fun e s
  simpa [ξ, hs] using this
end Ker
section Nm
open GroundTheory.Global.SemiLocal
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] {l : ℕ} [Fact l.Prime]
  {v : HeightOneSpectrum (𝓞 K)} (w : PlacesOver L v)
private noncomputable def resE (j : UpperTheory.V.W.Emb l w.1) : UpperTheory.V.W.Emb l v :=
  ⟨j.1.comp (completionMap v w.1), j.2.comp (continuous_completionMap v w.1)⟩
private theorem emb_norm [Fintype (UpperTheory.V.W.Emb l w.1)] [DecidableEq (UpperTheory.V.W.Emb l v)] (τ : UpperTheory.V.W.Emb l v)
    (y : w.1.adicCompletion L) :
    τ.1 (Algebra.norm (v.adicCompletion K) y) =
      ∏ j ∈ Finset.univ.filter (fun j : UpperTheory.V.W.Emb l w.1 => resE w j = τ), j.1 y := by
  letI := τ.1.toAlgebra
  haveI : ContinuousSMul (v.adicCompletion K) (Qbar l) := continuousSMul_of_algebraMap _ _ τ.2
  haveI : FiniteDimensional (v.adicCompletion K) (w.1.adicCompletion L) := GroundTheory.Global.finite_adicCompletion v w.1
  haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  refine (Algebra.norm_eq_prod_embeddings (v.adicCompletion K) (Qbar l) y).trans ?_
  have hc : ∀ σ : w.1.adicCompletion L →ₐ[v.adicCompletion K] Qbar l, Continuous σ := fun σ => by
    letI : NontriviallyNormedField (v.adicCompletion K) := Valued.toNontriviallyNormedField _ _
    have := LinearMap.continuous_of_finiteDimensional σ.toLinearMap
    exact this
  let e : (w.1.adicCompletion L →ₐ[v.adicCompletion K] Qbar l) ≃ {j : UpperTheory.V.W.Emb l w.1 // resE w j = τ} :=
    { toFun := fun σ => ⟨⟨σ, hc σ⟩, Subtype.ext (RingHom.ext fun x => σ.commutes x)⟩
      invFun := fun j => ⟨j.1.1, fun x => by
        have := congrArg (fun t : UpperTheory.V.W.Emb l v => t.1 x) j.2
        exact this⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Finset.prod_subtype (Finset.univ.filter (fun j : UpperTheory.V.W.Emb l w.1 => resE w j = τ))
    (p := fun j => resE w j = τ) (by simp)]
  exact Fintype.prod_equiv e _ _ fun σ => rfl
private theorem nm_eq_normU : UpperTheory.V.Z.Gam.nm w = GlobalTheory.BCChar.normU v w.1 := by
  have key : GroundTheory.Global.adicCompletionMap v w.1 = completionMap v w.1 := by
    refine RingHom.ext fun x => ?_
    refine congrFun ((HeightOneSpectrum.denseRange_algebraMap K v).equalizer
      (GroundTheory.Global.continuous_adicCompletionMap v w.1) (continuous_completionMap v w.1) (funext fun k => ?_)) x
    simp [GroundTheory.Global.adicCompletionMap_algebraMap, completionMap_algebraMap,
      IsScalarTower.algebraMap_apply K L (w.1.adicCompletion L)]
  unfold UpperTheory.V.Z.Gam.nm GlobalTheory.BCChar.normU
  rw [key]
end Nm
section Pow
variable {l : ℕ} [Fact l.Prime]
private noncomputable def powU {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))
    [Fintype (UpperTheory.V.W.Emb l w)] (c : UpperTheory.V.W.Emb l w → ℤ) : (w.adicCompletion F)ˣ →* (Qbar l)ˣ :=
  MonoidHom.mk' (fun y => ∏ j, Units.map (j.1 : w.adicCompletion F →* Qbar l) y ^ c j) fun x y => by
    simp only [map_mul, mul_zpow, Finset.prod_mul_distrib]
private theorem coe_powU {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))
    [Fintype (UpperTheory.V.W.Emb l w)] (c : UpperTheory.V.W.Emb l w → ℤ) (y : (w.adicCompletion F)ˣ) :
    ((powU w c y : (Qbar l)ˣ) : Qbar l) = ∏ j : UpperTheory.V.W.Emb l w, j.1 (y : w.adicCompletion F) ^ c j := by
  simp [powU, Units.coe_prod, Units.val_zpow_eq_zpow_val]
private theorem algPow_eq {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))
    [Fintype (UpperTheory.V.W.Emb l w)] (hh : (F →+* Qbar l) → ℤ) (y : (w.adicCompletion F)ˣ) :
    algPow w hh (y : w.adicCompletion F) =
      ((powU w (fun j : UpperTheory.V.W.Emb l w => hh (j.1.comp (algebraMap F (w.adicCompletion F)))) y : (Qbar l)ˣ) : Qbar l) := by
  rw [coe_powU]
  unfold algPow
  rw [finprod_eq_prod_of_fintype]
end Pow
section Const
open GroundTheory.Global.SemiLocal
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] {l : ℕ} [Fact l.Prime]
  {v : HeightOneSpectrum (𝓞 K)} (w : PlacesOver L v)
private theorem exists_const [Fintype (UpperTheory.V.W.Emb l w.1)] [Fintype (UpperTheory.V.W.Emb l v)]
    (hl : ((l : ℕ) : 𝓞 L) ∈ w.1.asIdeal) (ω : (w.1.adicCompletion L)ˣ →* ℂˣ) (hω : IsSmoothChar ω)
    (c : UpperTheory.V.W.Emb l w.1 → ℤ) (Hk : ∀ x, ω x = 1 → UpperTheory.V.Z.Gam.nm w x = 1 → powU w.1 c x = 1) :
    ∃ c0 : UpperTheory.V.W.Emb l v → ℤ, ∀ y, powU w.1 c y = powU v c0 (UpperTheory.V.Z.Gam.nm w y) := by
  classical
  haveI : FiniteDimensional (v.adicCompletion K) (w.1.adicCompletion L) := GroundTheory.Global.finite_adicCompletion v w.1
  set d : ℕ := Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) with hd
  have hd0 : 0 < d := Module.finrank_pos
  let inc : (v.adicCompletion K)ˣ →* (w.1.adicCompletion L)ˣ := Units.map (completionMap v w.1 : _ →* _)
  have hinc : Continuous inc := Continuous.units_map _ (continuous_completionMap v w.1)
  let χ : (v.adicCompletion K)ˣ →* ℂˣ := ω.comp inc
  have hχ : IsSmoothChar χ := IsOpen.preimage hinc hω
  have hnm : IsSmoothChar (χ.comp (UpperTheory.V.Z.Gam.nm w)) := by
    rw [nm_eq_normU]
    exact GlobalTheory.BCChar.isSmoothChar_comp_normU v w.1 hχ
  have hnorm : ∀ t, UpperTheory.V.Z.Gam.nm w (inc t) = t ^ d := fun t => Units.ext (by
    show Algebra.norm (v.adicCompletion K) (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (t : v.adicCompletion K)) = _
    rw [Algebra.norm_algebraMap]
    simp [hd])
  let U : Subgroup (w.1.adicCompletion L)ˣ := ω.ker ⊓ (χ.comp (UpperTheory.V.Z.Gam.nm w)).ker
  have hU : IsOpen (U : Set (w.1.adicCompletion L)ˣ) := IsOpen.inter hω hnm
  let p : (w.1.adicCompletion L)ˣ → UpperTheory.V.W.Emb l w.1 → (Qbar l)ˣ := fun y j => Units.map (j.1 : _ →* Qbar l) y
  let q : (w.1.adicCompletion L)ˣ → UpperTheory.V.W.Emb l v → (Qbar l)ˣ := fun y τ =>
    Units.map (τ.1 : _ →* Qbar l) (UpperTheory.V.Z.Gam.nm w y)
  have hq : ∀ y τ, q y τ = ∏ j ∈ Finset.univ.filter (fun j => resE w j = τ), p y j := fun y τ => Units.ext (by
    rw [Units.coe_prod]
    exact emb_norm w τ (y : w.1.adicCompletion L))
  let e : UpperTheory.V.W.Emb l w.1 → ℤ := fun j =>
    (d : ℤ) * c j - ∑ i ∈ Finset.univ.filter (fun i => resE w i = resE w j), c i
  have he : e = 0 := by
    refine exp_eq_zero w.1 hl U hU e fun y hy => ?_
    have h1 : ω (y ^ d * (inc (UpperTheory.V.Z.Gam.nm w y))⁻¹) = 1 := by
      have h2 : ω y = 1 := hy.1
      have h3 : ω (inc (UpperTheory.V.Z.Gam.nm w y)) = 1 := hy.2
      rw [map_mul, map_pow, map_inv, h2, h3]
      simp
    have h4 : UpperTheory.V.Z.Gam.nm w (y ^ d * (inc (UpperTheory.V.Z.Gam.nm w y))⁻¹) = 1 := by
      rw [map_mul, map_pow, map_inv, hnorm]
      simp
    have h5 := Hk _ h1 h4
    have h6 : powU w.1 c (inc (UpperTheory.V.Z.Gam.nm w y)) = ∏ j, q y (resE w j) ^ c j := rfl
    have h7 : powU w.1 c y = ∏ j, p y j ^ c j := rfl
    rw [map_mul, map_pow, map_inv, h6, h7, ← zpow_natCast, prod_collect (resE w) (p y) (q y) (hq y) (d : ℤ) c] at h5
    have h8 := congrArg (Units.val) h5
    rw [Units.coe_prod] at h8
    simpa [Units.val_zpow_eq_zpow_val, p, e] using h8
  let c0 : UpperTheory.V.W.Emb l v → ℤ := fun τ => (∑ i ∈ Finset.univ.filter (fun i => resE w i = τ), c i) / (d : ℤ)
  have hc : ∀ j, c j = c0 (resE w j) := fun j => by
    have h1 : e j = 0 := congrFun he j
    have h2 := sub_eq_zero.1 h1
    show c j = (∑ i ∈ Finset.univ.filter (fun i => resE w i = resE w j), c i) / (d : ℤ)
    rw [← h2, Int.mul_ediv_cancel_left _ (by exact_mod_cast hd0.ne')]
  refine ⟨c0, fun y => ?_⟩
  have h1 : powU w.1 c y = ∏ j, p y j ^ c0 (resE w j) :=
    Finset.prod_congr rfl fun j _ => by rw [← hc]
  rw [h1, prod_fib (resE w) (p y) (q y) (hq y) c0]
  rfl
end Const
section Res
variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω]
  [Algebra L Ω] [IsScalarTower K L Ω] [IsAlgClosure K Ω] [IsAlgClosure L Ω]
private theorem isOpenMap_res : IsOpenMap (AlgEquiv.restrictScalarsHom K : G L Ω →* G K Ω) := by
  have hc : Continuous (AlgEquiv.restrictScalarsHom K : G L Ω →* G K Ω) := UpperTheory.V.Af.continuous_restrictScalarsHom K L Ω
  have hinj : Function.Injective (AlgEquiv.restrictScalarsHom K : G L Ω →* G K Ω) := fun σ τ e =>
    AlgEquiv.ext fun z => DFunLike.congr_fun e z
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  let E : IntermediateField K Ω := (IsScalarTower.toAlgHom K L Ω).fieldRange
  haveI : FiniteDimensional K E :=
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L Ω)).toLinearEquiv.finiteDimensional
  have hE := IntermediateField.fixingSubgroup_isOpen E
  have hr : Set.range (AlgEquiv.restrictScalarsHom K : G L Ω →* G K Ω) = (E.fixingSubgroup : Set (G K Ω)) := by
    ext σ
    constructor
    · rintro ⟨τ, rfl⟩
      rintro ⟨_, y, rfl⟩
      exact τ.commutes y
    · intro hσ
      refine ⟨AlgEquiv.ofRingEquiv (f := (σ : Ω ≃+* Ω)) fun y => ?_, AlgEquiv.ext fun z => rfl⟩
      exact hσ ⟨_, y, rfl⟩
  exact (Topology.IsOpenEmbedding.mk (hc.isClosedEmbedding hinj).isEmbedding (hr ▸ hE)).isOpenMap
end Res
end UpperTheory.V.Z.Ord.ExtensionCharacterAlt
open UpperTheory.V.Z.Ord.ExtensionCharacterAlt GroundTheory.Global.SemiLocal in
theorem UpperTheory.V.Z.Ord.ext_character_of_literal_automorphy_n :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ExtChar := by
  intro _ K L Ω _ _ _ _ _ _ _ _ _ _ _ l _ ι v w A h hl a ha κ ψ hκ hres ω hh ho
  have h0 : IsPlaceOver A v := fun x => by
    rw [w.2.over, Ideal.under, Ideal.mem_comap, ← h]
    have : algebraMap L Ω ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K Ω (x : K) := by
      change algebraMap L Ω (algebraMap K L (x : K)) = _
      rw [← IsScalarTower.algebraMap_apply]
    rw [this]
  have hlw : ((l : ℕ) : 𝓞 L) ∈ w.1.asIdeal := by
    have : ((l : ℕ) : 𝓞 K) ∈ w.1.asIdeal.under (𝓞 K) := w.2.over ▸ hl
    simpa [Ideal.under, Ideal.mem_comap] using this
  obtain ⟨a0, ha0⟩ := GlobalTheory.localArtinExists_holds K Ω A v h0
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w.1
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) v
  letI : Fintype (UpperTheory.V.W.Emb l w.1) := Fintype.ofFinite _
  letI : Fintype (UpperTheory.V.W.Emb l v) := Fintype.ofFinite _
  let R := GlobalTheory.AboveL.ResEx.resW h0 h
  let inc0 := Subgroup.inclusion (Weil_le_Dec h0)
  let inc := Subgroup.inclusion (Weil_le_Dec h)
  have hN : ∀ s, a0 (R s) = UpperTheory.V.Z.Gam.nm w (a s) := fun s => by
    rw [nm_eq_normU]
    exact GlobalTheory.ArtinNormU.localArtin_normU K L Ω A v w.1 h0 h a0 a ha0 ha _ s fun z => rfl
  have hψ : ∀ s, ψ (inc s) = κ (inc0 (R s)) := fun s => hres (inc s) (inc0 (R s)) rfl
  have hval : ∀ s, ((ψ (inc s) : (Qbar l)ˣ) : Qbar l) =
      ι.symm (ω (a s)) * algPow w.1 (-hh) (a s : w.1.adicCompletion L) :=
    fun s => ho.val s (inc s) rfl (Set.mem_univ _)
  set c : UpperTheory.V.W.Emb l w.1 → ℤ := fun j => (-hh) (j.1.comp (algebraMap L (w.1.adicCompletion L))) with hcdef
  have Hk : ∀ x, ω x = 1 → UpperTheory.V.Z.Gam.nm w x = 1 → powU w.1 c x = 1 := fun x h1 h2 => by
    obtain ⟨s, rfl⟩ := ha.surj x
    have h3 := ker_art h0 ha0 κ hκ (R s) ((hN s).trans h2)
    have h4 := hval s
    rw [hψ, show κ (inc0 (R s)) = 1 from h3, h1, algPow_eq] at h4
    rw [show ι.symm (((1 : ℂˣ) : ℂ)) = 1 by simp, one_mul] at h4
    exact Units.ext h4.symm
  obtain ⟨c0, hc0⟩ := exists_const w hlw ω ho.smooth c Hk
  let ξ' : Weil h0 →* (Qbar l)ˣ := κ.comp inc0 * ((powU v c0).comp a0)⁻¹
  let ξ : Weil h0 →* ℂˣ := (Units.map ι.toRingHom.toMonoidHom).comp ξ'
  have hξR : ∀ s, ξ (R s) = ω (a s) := fun s => by
    refine Units.ext ?_
    have h1 : ((ξ' (R s) : (Qbar l)ˣ) : Qbar l) = ι.symm (ω (a s)) := by
      show (((κ (inc0 (R s)) * (powU v c0 (a0 (R s)))⁻¹ : (Qbar l)ˣ)) : Qbar l) = _
      rw [← hψ, hN, ← hc0, Units.val_mul, hval, algPow_eq, Units.val_inv_eq_inv_val, mul_assoc,
        mul_inv_cancel₀ (Units.ne_zero _), mul_one]
    show ι ((ξ' (R s) : (Qbar l)ˣ) : Qbar l) = _
    rw [h1, ι.apply_symm_apply]
  have hξ : GlobalTheory.WeilDeligne.IsSmooth ξ := by
    have hS : IsOpen (((ω.comp a).comp (ineIncl h)).ker : Set (Ine (F := L) A)) := IsOpen.preimage ha.cont ho.smooth
    obtain ⟨S', hS', e⟩ := isOpen_induced_iff.1 hS
    have hO : IsOpen ((Subtype.val : Ine (F := K) A → G K Ω) ⁻¹'
        ((AlgEquiv.restrictScalarsHom K : G L Ω →* G K Ω) '' S')) :=
      (isOpenMap_res _ hS').preimage continuous_subtype_val
    have h1S : (1 : G L Ω) ∈ S' := by
      have : (1 : Ine (F := L) A) ∈ Subtype.val ⁻¹' S' := by
        rw [e]
        exact one_mem _
      exact this
    refine Subgroup.isOpen_of_mem_nhds ((ξ.comp (ineIncl h0)).ker) (g := 1)
      (Filter.mem_of_superset (hO.mem_nhds ⟨1, h1S, map_one _⟩) ?_)
    rintro t ⟨σ, hσ, et⟩
    have hmem : σ ∈ Ine (F := L) A := by
      have ht := t.2
      rw [← et] at ht
      exact ⟨GlobalTheory.DelEps.WeilRes.mem_Dec_iff.2 fun x => GlobalTheory.DelEps.WeilRes.mem_Dec_iff.1 ht.1 x, fun x hx => ht.2 x hx⟩
    have hk : (⟨σ, hmem⟩ : Ine (F := L) A) ∈ Subtype.val ⁻¹' S' := hσ
    rw [e] at hk
    have hk' : ω (a (ineIncl h ⟨σ, hmem⟩)) = 1 := hk
    have e2 : ineIncl h0 t = R (ineIncl h ⟨σ, hmem⟩) := by
      rw [GlobalTheory.AboveL.ResEx.resW_ineIncl]
      exact congrArg _ (Subtype.ext et.symm)
    show ξ (ineIncl h0 t) = 1
    rw [e2, hξR, hk']
  obtain ⟨χ, hχ, e⟩ := ha0.factor ξ hξ
  refine ⟨χ⁻¹, ?_, fun x _ => ?_⟩
  · refine Subgroup.isOpen_mono (fun x hx => ?_) hχ
    show χ⁻¹ x = 1
    rw [MonoidHom.inv_apply, MonoidHom.mem_ker.1 hx, inv_one]
  · obtain ⟨s, rfl⟩ := ha.surj x
    have h1 := DFunLike.congr_fun e (R s)
    rw [hξR] at h1
    show ω (a s) * (χ (UpperTheory.V.Z.Gam.nm w (a s)))⁻¹ = 1
    rw [← hN, h1]
    simp [MonoidHom.comp_apply]
end
