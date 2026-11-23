import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DetCondTensorDefinite
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

private noncomputable def actZ (Dw : Datum H) : 𝓞 E →+* Module.End ℤ Dw.La := (Algebra.lsmul ℤ ℤ Dw.La).toRingHom

private theorem actZ_apply (Dw : Datum H) (o : 𝓞 E) :
    actZ Dw o = (LinearMap.lsmul (𝓞 E) Dw.La o).restrictScalars ℤ :=
  LinearMap.ext fun _ => rfl

private theorem flat_of_pid (V V' : Type) [CommRing V] [IsDomain V] [IsPrincipalIdealRing V] [CommRing V'] [IsDomain V']
    [Algebra V V'] [FaithfulSMul V V'] : Module.Flat V V' :=
  Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2
    (Submodule.isTorsionFree_iff_torsion_eq_bot.1
      (Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective V V')))

private theorem finrank_eig (Dw : Datum H) [Module.Finite ℤ Dw.La] [Module.Free ℤ Dw.La] {V : Type} [CommRing V]
    [IsDomain V] [IsPrincipalIdealRing V] (io : V →+* ℂ) (hin : Function.Injective io) (σ : 𝓞 E →+* V) :
    Module.finrank V (EigenSplit.eigenSub (EigenSplit.baseChangeAction V (actZ Dw)) σ) = Dw.p + Dw.q := by
  letI : Algebra V ℂ := io.toAlgebra
  have : FaithfulSMul V ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2 hin
  have : Module.Flat V ℂ := flat_of_pid V ℂ
  have hF := EigenSplit.finrank_eigenSub_of_flat (R := V) (R' := ℂ) (ρ := EigenSplit.baseChangeAction V (actZ Dw))
    (ρ' := EigenSplit.baseChangeAction ℂ (actZ Dw)) (f := EigenSplit.extendTensor ℤ V ℂ Dw.La)
    (EigenSplit.extendTensor_equivariant V ℂ (actZ Dw)) (EigenSplit.isBaseChange_extendTensor ℤ V ℂ Dw.La) σ
  have hT := TensorDet.finrank_eigenSub (E := E) (k := ℂ) (O := ℤ) (M := Dw.La)
    ((algebraMap V ℂ).comp σ) (RingHom.ext_int _ _)
  have e : TensorDet.rightAction ℂ ℤ (𝓞 E) Dw.La = EigenSplit.baseChangeAction ℂ (actZ Dw) := rfl
  rw [e, hF, Dw.rank] at hT
  exact hT

private theorem latData_pid (Dw : Datum H) {V : Type} [CommRing V] [IsDomain V] [IsPrincipalIdealRing V]
    (io : V →+* ℂ) (hin : Function.Injective io) (σ : 𝓞 E →+* V) :
    ∃ (N : ℕ) (a : Fin N → Dw.La) (T S : Fin (Dw.p + Dw.q) → Fin N → V), GlobalTheory.FlatModel.LatData Dw σ a T S := by
  classical
  obtain ⟨N, ⟨a⟩⟩ : ∃ k : ℕ, Nonempty (Module.Basis (Fin k) ℤ Dw.La) := by
    haveI := Dw.fin
    haveI : Module.Finite ℤ Dw.La := Module.Finite.trans (𝓞 E) Dw.La
    haveI : Module.IsTorsionFree ℤ Dw.La :=
      Function.Injective.moduleIsTorsionFree Dw.EF Dw.unimod.1 (fun r x => map_smul _ r x)
    haveI : Module.Free ℤ Dw.La := Module.free_of_finite_type_torsion_free'
    exact ⟨_, ⟨Module.finBasis ℤ Dw.La⟩⟩
  haveI : Module.Free ℤ Dw.La := Module.Free.of_basis a
  haveI : Module.Finite ℤ Dw.La := Module.Finite.of_basis a
  set K := EigenSplit.eigenSub (EigenSplit.baseChangeAction V (actZ Dw)) σ with hK
  haveI : Module.Finite V K := inferInstance
  haveI : Module.Free V K := Module.free_of_finite_type_torsion_free'
  have hrk : Module.finrank V K = Dw.p + Dw.q := finrank_eig Dw io hin σ
  let b : Module.Basis (Fin (Dw.p + Dw.q)) V K := Module.finBasisOfFinrankEq V K hrk
  obtain ⟨Q, hQ⟩ : ∃ Q, IsCompl K Q :=
    (EigenSplit.isSaturatedSubmodule_eigenSub (EigenSplit.baseChangeAction V (actZ Dw)) σ).exists_isCompl
  let pr := Submodule.linearProjOfIsCompl K Q hQ
  let f : Fin (Dw.p + Dw.q) → (V ⊗[ℤ] Dw.La →ₗ[V] V) := fun i => (b.coord i).comp pr
  have hf : ∀ i j, f i (b j) = if i = j then 1 else 0 := by
    intro i j
    show b.coord i (pr (b j)) = _
    rw [show pr (b j) = b j from Submodule.linearProjOfIsCompl_apply_left hQ (b j), Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply]
    simp [eq_comm]
  choose y hy using fun m' : Fin N => Dw.unimod.2 (a.coord m')
  let cc : Fin N → Fin N → ℤ := fun m' m => a.repr (y m') m
  have hcc : ∀ m' k, ∑ m, cc m' m * Dw.EF (a m) (a k) = if m' = k then 1 else 0 := by
    intro m' k
    have h0 : Dw.EF (y m') (a k) = ∑ m, cc m' m * Dw.EF (a m) (a k) := by
      calc Dw.EF (y m') (a k) = Dw.EF (∑ m, a.repr (y m') m • a m) (a k) := by rw [a.sum_repr]
        _ = ∑ m, cc m' m * Dw.EF (a m) (a k) := by
          simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, cc]
    rw [← h0, hy, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    simp [eq_comm]
  let tb := Algebra.TensorProduct.basis V a
  let T : Fin (Dw.p + Dw.q) → Fin N → V := fun j m => tb.repr (b j : V ⊗[ℤ] Dw.La) m
  let S : Fin (Dw.p + Dw.q) → Fin N → V := fun i m => ∑ m', f i (1 ⊗ₜ a m') * (cc m' m : V)
  have hT : ∀ j, ∑ m, T j m ⊗ₜ[ℤ] a m = (b j : V ⊗[ℤ] Dw.La) := by
    intro j
    conv_rhs => rw [← tb.sum_repr (b j : V ⊗[ℤ] Dw.La)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  have hS : ∀ i k, ∑ m, S i m * ((Dw.EF (a m) (a k) : ℤ) : V) = f i (1 ⊗ₜ a k) := by
    intro i k
    simp only [S, Finset.sum_mul]
    rw [Finset.sum_comm]
    have e : ∀ m', ∑ m, f i (1 ⊗ₜ a m') * (cc m' m : V) * ((Dw.EF (a m) (a k) : ℤ) : V)
        = f i (1 ⊗ₜ a m') * (if m' = k then 1 else 0) := by
      intro m'
      have h2 := congrArg (fun z : ℤ => (z : V)) (hcc m' k)
      simp only [Int.cast_sum, Int.cast_mul] at h2
      simp_rw [_root_.mul_assoc, ← Finset.mul_sum, h2]
      split_ifs <;> simp
    simp_rw [e, mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine ⟨N, a, T, S, ?_, ?_, ?_⟩
  · intro i o
    have hm := EigenSplit.mem_eigenSub.1 (b i).2 o
    rw [EigenSplit.baseChangeAction_apply, actZ_apply] at hm
    have e1 : ∑ m, T i m ⊗ₜ[ℤ] (o • a m)
        = ((LinearMap.lsmul (𝓞 E) Dw.La o).restrictScalars ℤ).baseChange V (∑ m, T i m ⊗ₜ[ℤ] a m) := by
      simp [map_sum, LinearMap.baseChange_tmul]
    rw [e1, hT, hm, ← hT, Finset.smul_sum]
    simp [TensorProduct.smul_tmul', smul_eq_mul]
  · intro i j
    have e2 : ∑ m, ∑ m', S i m * T j m' * ((Dw.EF (a m) (a m') : ℤ) : V) = f i (b j) := by
      rw [Finset.sum_comm]
      simp_rw [mul_comm (S i _) (T j _), _root_.mul_assoc, ← Finset.mul_sum, hS]
      rw [← hT j, map_sum]
      refine Finset.sum_congr rfl fun m' _ => ?_
      have e3 : T j m' ⊗ₜ[ℤ] a m' = T j m' • ((1 : V) ⊗ₜ[ℤ] a m') := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [e3, map_smul, smul_eq_mul]
    rw [e2, hf]
  · intro x hx
    have hxK : x ∈ K := EigenSplit.mem_eigenSub.2 fun o => by
      rw [EigenSplit.baseChangeAction_apply, actZ_apply]; exact hx o
    have e' : x = ∑ i, b.repr ⟨x, hxK⟩ i • (b i : V ⊗[ℤ] Dw.La) := by
      conv_lhs => rw [show x = ((⟨x, hxK⟩ : K) : V ⊗[ℤ] Dw.La) from rfl, ← b.sum_repr ⟨x, hxK⟩]
      simp only [Submodule.coe_sum, Submodule.coe_smul]
    rw [e']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hT i⟩)

private theorem latData_map (Dw : Datum H) {V V' J : Type} [CommRing V] [IsDomain V] [IsPrincipalIdealRing V]
    [CommRing V'] [IsDomain V'] [DecidableEq J] (φ : V →+* V') (hφ : Function.Injective φ) (σ : 𝓞 E →+* V) {N : ℕ}
    (a : Fin N → Dw.La) (T S : J → Fin N → V) (h : GlobalTheory.FlatModel.LatData Dw σ a T S) :
    GlobalTheory.FlatModel.LatData Dw (φ.comp σ) a (fun j m => φ (T j m)) (fun j m => φ (S j m)) := by
  letI : Algebra V V' := φ.toAlgebra
  have : FaithfulSMul V V' := (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  have : Module.Flat V V' := flat_of_pid V V'
  have hφa : algebraMap V V' = φ := rfl
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun i o => ?_, fun i j => ?_, fun x hx => ?_⟩
  · have := congrArg (EigenSplit.extendTensor ℤ V V' Dw.La) (h1 i o)
    simpa only [map_sum, EigenSplit.extendTensor_tmul, hφa, map_mul, RingHom.comp_apply] using this
  · have := congrArg φ (h2 i j)
    simpa only [map_sum, map_mul, map_intCast, apply_ite φ, map_one, map_zero] using this
  · have hxK : x ∈ EigenSplit.eigenSub (EigenSplit.baseChangeAction V' (actZ Dw)) ((algebraMap V V').comp σ) :=
      EigenSplit.mem_eigenSub.2 fun o => by
        rw [EigenSplit.baseChangeAction_apply, actZ_apply]; exact hx o
    rw [EigenSplit.eigenSub_eq_span_of_flat (EigenSplit.extendTensor_equivariant V V' (actZ Dw))
      (EigenSplit.isBaseChange_extendTensor ℤ V V' Dw.La) σ] at hxK
    refine (Submodule.span_le.2 ?_) hxK
    rintro _ ⟨y, hy, rfl⟩
    have hy' := h3 y fun o => by
      have := EigenSplit.mem_eigenSub.1 hy o
      rwa [EigenSplit.baseChangeAction_apply, actZ_apply] at this
    clear hy
    induction hy' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact Submodule.subset_span ⟨i, by simp only [map_sum, EigenSplit.extendTensor_tmul, hφa]⟩
    | zero => simp
    | add u v _ _ hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
    | smul c u _ hu =>
      rw [map_smul, ← algebraMap_smul V' c]
      exact Submodule.smul_mem _ _ hu

end SlopeTestRemainingChoices

private theorem exists_pid (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsPrincipalIdealRing V) (j : 𝓞 F →+* V) (io : V →+* F),
      Function.Injective io ∧ (∀ x, io (j x) = x) ∧ ∀ (k : F →+* ℂ_[p]) (x : V), ‖k (io x)‖ ≤ 1 := by
  have hp : p.Prime := Fact.out
  let P : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hP0 : P ≠ ⊥ := by
    simp [P, hp.ne_zero]
  haveI : P.IsPrime := (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
  let M := Algebra.algebraMapSubmonoid (𝓞 F) P.primeCompl
  have hM : M ≤ nonZeroDivisors (𝓞 F) :=
    map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective _ _) P.primeCompl_le_nonZeroDivisors
  haveI : IsDomain (Localization M) := IsLocalization.isDomain_localization hM
  haveI : IsDedekindDomain (Localization M) := IsLocalization.isDedekindDomain (𝓞 F) hM (Localization M)
  haveI : IsPrincipalIdealRing (Localization M) :=
    IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 F) P hP0
  have hu : ∀ y : M, IsUnit (algebraMap (𝓞 F) F y) := fun y =>
    IsUnit.mk0 _ ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 (nonZeroDivisors.ne_zero (hM y.2)))
  refine ⟨Localization M, inferInstance, inferInstance, inferInstance, algebraMap _ _, IsLocalization.lift hu, ?_, ?_, ?_⟩
  · rw [IsLocalization.lift_injective_iff]
    intro x y
    rw [(IsLocalization.injective (Localization M) hM).eq_iff, (FaithfulSMul.algebraMap_injective (𝓞 F) F).eq_iff]
  · intro x
    exact IsLocalization.lift_eq hu x
  · intro k x
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective M x
    obtain ⟨s, n, hn, rfl⟩ := s
    have h1 : ‖k (algebraMap (𝓞 F) F r)‖ ≤ 1 := by
      have hi : IsIntegral ℤ (k (algebraMap (𝓞 F) F r)) := by
        convert map_isIntegral_int k r.isIntegral_coe
        exact Subsingleton.elim _ _
      have hv := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).isIntegral_iff_v_le_one.1
        (IsIntegral.tower_top hi)
      exact_mod_cast hv
    have h2 : ‖((n : ℤ) : ℂ_[p])‖ = 1 := by
      have hn' : ¬ (p : ℤ) ∣ n := fun h => hn (Ideal.mem_span_singleton.2 h)
      rw [← map_intCast (algebraMap ℚ_[p] ℂ_[p]) n, norm_algebraMap']
      exact le_antisymm (Padic.norm_int_le_one n) (not_lt.1 fun h => hn' (Padic.norm_intCast_lt_one_iff.1 h))
    have h3 := congrArg (fun z => ‖k (IsLocalization.lift hu z)‖)
      (IsLocalization.mk'_spec (Localization M) r (⟨algebraMap ℤ (𝓞 F) n, n, hn, rfl⟩ : M))
    simp only [map_mul, IsLocalization.lift_eq, norm_mul, eq_intCast, map_intCast, h2, _root_.mul_one] at h3
    exact h3.le.trans h1

theorem UpperTheory.lattice_data_integral_specialisation :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (σ : 𝓞 E →+* F), ∃ (M : ℕ) (a : Fin M → Dw.La) (T S : Fin (Dw.p + Dw.q) → Fin M → F), ∀ k : F →+* ℂ_[p], ∃ (s : 𝓞 E →+* ↥(intO ℂ_[p])) (T' S' : Fin (Dw.p + Dw.q) → Fin M → ↥(intO ℂ_[p])), (∀ o, (s o : ℂ_[p]) = k (σ o)) ∧ (∀ j m, (T' j m : ℂ_[p]) = k (T j m)) ∧ (∀ j m, (S' j m : ℂ_[p]) = k (S j m)) ∧ GlobalTheory.FlatModel.LatData Dw s a T' S' := by
  intro E _ _ _ H Dw p _ F _ _ σ
  obtain ⟨V, _, _, _, j, io, hin, hj, hk⟩ := exists_pid p F
  have hint : ∀ o : 𝓞 E, σ o ∈ integralClosure ℤ F := fun o =>
    (RingOfIntegers.isIntegral o).map σ.toIntAlgHom
  let σ₀ : 𝓞 E →+* 𝓞 F := σ.codRestrict (integralClosure ℤ F) hint
  have hσ₀ : ∀ o, ((σ₀ o : 𝓞 F) : F) = σ o := fun _ => rfl
  obtain ⟨c⟩ : Nonempty (F →+* ℂ) := inferInstance
  obtain ⟨N, a, T, S, h⟩ := latData_pid Dw (c.comp io) (c.injective.comp hin) (j.comp σ₀)
  refine ⟨N, a, fun i m => io (T i m), fun i m => io (S i m), fun k => ?_⟩
  let φ : V →+* ↥(intO ℂ_[p]) := (k.comp io).codRestrict (intO ℂ_[p]) (hk k)
  have hφ : Function.Injective φ := fun x y hxy => hin (k.injective (congrArg Subtype.val hxy))
  refine ⟨φ.comp (j.comp σ₀), fun i m => φ (T i m), fun i m => φ (S i m), fun o => ?_, fun _ _ => rfl, fun _ _ => rfl,
    latData_map Dw φ hφ _ a T S h⟩
  show k (io (j (σ₀ o))) = _
  rw [hj, hσ₀]
