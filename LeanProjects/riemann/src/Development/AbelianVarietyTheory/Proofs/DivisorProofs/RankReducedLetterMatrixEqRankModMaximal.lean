import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Formalism.PieriBlockIdeals.PieriColumnMinors.HeckeLFunctionIdealEulerProduct
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.WachRank

theorem rank_map_inj {F κ : Type} [Field F] [Field κ] (ψ : F⟦X⟧ →+* κ) (hψ : Function.Injective ψ) {a b : ℕ}
    (M : Mx F⟦X⟧ a b) : (M.map ψ).rank = lrank M := by
  unfold lrank
  rw [← GlobalTheory.Core.Rk.rank_map_field (IsFractionRing.lift (K := LaurentSeries F) hψ), Matrix.map_map]
  congr 2
  funext x
  exact (IsFractionRing.lift_algebraMap hψ x).symm

theorem rank_eq_of_mul_eq {κ : Type} [Field κ] {a b : ℕ} (G' : Mx κ a a) (G : Mx κ b b) (X Y : Mx κ a b)
    (hG' : IsUnit G'.det) (hG : IsUnit G.det) (h : G' * X = Y * G) : X.rank = Y.rank := by
  rw [← Matrix.rank_mul_eq_right_of_isUnit_det G' X hG', h, Matrix.rank_mul_eq_left_of_isUnit_det G Y hG]

theorem mat_identity {S M M' : Type} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup M'] [Module S M']
    {n n' : ℕ} (u : Fin n → M) (B' : Module.Basis (Fin n') S M') (v : Fin n → M) (v' : Fin n' → M')
    (G : Mx S n n) (G' : Mx S n' n') (X Y : Mx S n' n) (f : M →ₗ[S] M')
    (hv : ∀ k, v k = ∑ j, G j k • u j) (hv' : ∀ k, v' k = ∑ j, G' j k • B' j)
    (hX : ∀ k, f (v k) = ∑ m, X m k • v' m) (hY : ∀ k, f (u k) = ∑ m, Y m k • B' m) : G' * X = Y * G := by
  ext r k
  have h := congrArg (fun z => B'.repr z r) (hX k)
  simp only [hv, hv', hY, map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
    Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h
  simp only [Matrix.mul_apply]
  rw [Finset.sum_congr rfl (fun m _ => mul_comm (G' r m) (X m k)), ← h]
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

theorem exists_unit_mat {S M : Type} [CommRing S] [AddCommGroup M] [Module S M] {n : ℕ}
    (B : Module.Basis (Fin n) S M) (v : Fin n → M) (hv : ⊤ ≤ Submodule.span S (Set.range v)) :
    ∃ G : Mx S n n, IsUnit G.det ∧ ∀ k, v k = ∑ j, G j k • B j := by
  have h1 : ∀ j, ∃ c : Fin n → S, ∑ k, c k • v k = B j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun S).1 (hv Submodule.mem_top)
  choose H hH using h1
  have h2 : ∀ k, v k = ∑ j, (Matrix.of fun j k => B.repr (v k) j) j k • B j := fun k => (B.sum_repr (v k)).symm
  have h3 : ∀ k, B k = ∑ j, (1 : Mx S n n) j k • B j := fun k => by simp [Matrix.one_apply]
  refine ⟨_, ?_, h2⟩
  have := mat_identity B B B v 1 _ (Matrix.of fun k j => H j k) 1 LinearMap.id h3 h2 (fun k => (hH k).symm) h3
  rw [mul_one] at this
  exact Matrix.isUnit_det_of_right_inverse this

theorem one_not_mem_map {Z O C : Type} [CommRing Z] [CommRing O] [CommRing C] [Algebra Z O] [Algebra Z C]
    [Module.FaithfullyFlat Z C] (I : Ideal O) (hI : I ≠ ⊤) :
    (1 : TensorProduct Z O C) ∉ Ideal.map (algebraMap O (TensorProduct Z O C)) I := by
  haveI : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  haveI : Nontrivial (TensorProduct Z (O ⧸ I) C) := Module.FaithfullyFlat.rTensor_nontrivial Z C (O ⧸ I)
  let f := Algebra.TensorProduct.map (Ideal.Quotient.mkₐ Z I) (AlgHom.id Z C)
  have hle : Ideal.map (algebraMap O (TensorProduct Z O C)) I ≤ RingHom.ker f := by
    rw [Ideal.map_le_iff_le_comap]
    intro c hc
    change f (TensorProduct.tmul Z c 1) = 0
    simp [f, Ideal.Quotient.eq_zero_iff_mem.2 hc]
  intro h
  have := hle h
  rw [RingHom.mem_ker, map_one] at this
  exact one_ne_zero this

theorem choose_max {O R : Type} [CommRing O] [CommRing R] [Algebra O R] {n : ℕ} [NeZero n]
    (φ₀ : O⟦X⟧ →ₐ[O] O⟦X⟧) (ι : LetA O n →ₐ[O] R) (φ : R →ₐ[O] R) (I : Ideal O)
    (hφ : ∀ x, ι (letφ φ₀ x) = φ (ι x)) (h1 : (1 : R) ∉ Ideal.map (algebraMap O R) I) (i : ZMod n) :
    ∃ m : Ideal R, m.IsMaximal ∧ Ideal.map (algebraMap O R) I ≤ m ∧ 1 - ι (letE i) ∈ m := by
  have hJ : Ideal.map (algebraMap O R) I ≤ Ideal.comap φ (Ideal.map (algebraMap O R) I) := by
    rw [Ideal.map_le_iff_le_comap]
    intro c hc
    rw [Ideal.mem_comap, Ideal.mem_comap, φ.commutes]
    exact Ideal.mem_map_of_mem _ hc
  have he : ∀ j : ZMod n, letφ φ₀ (letE j : LetA O n) = letE (j + 1) := fun j => by
    funext k
    change φ₀ ((letE j : LetA O n) (k - 1)) = _
    by_cases hk : k = j + 1
    · subst hk
      simp [letE]
    · have : k - 1 ≠ j := fun h => hk (by rw [← h]; ring)
      simp [letE, Pi.single_apply, hk, this]
  have hne : ι (letE i) ∉ Ideal.map (algebraMap O R) I := by
    intro h
    have h2 : ∀ k : ℕ, ι (letE (i + k)) ∈ Ideal.map (algebraMap O R) I := fun k => by
      induction k with
      | zero => simpa using h
      | succ k ih =>
        rw [Nat.cast_succ, ← add_assoc, ← he, hφ]
        exact hJ ih
    have h3 : ∀ j, ι (letE j) ∈ Ideal.map (algebraMap O R) I := fun j => by
      have := h2 (j - i).val
      rwa [ZMod.natCast_zmod_val, add_sub_cancel] at this
    have h4 : ∑ j : ZMod n, (letE j : LetA O n) = 1 := Finset.univ_sum_single (1 : ZMod n → O⟦X⟧)
    apply h1
    rw [← map_one ι, ← h4, map_sum]
    exact Ideal.sum_mem _ fun j _ => h3 j
  have hee : ι (letE i) * ι (letE i) = ι (letE i) := by
    rw [← map_mul]
    congr 1
    funext k
    by_cases hk : k = i <;> simp [letE, Pi.single_apply, hk]
  have hp : Ideal.map (algebraMap O R) I ⊔ Ideal.span {1 - ι (letE i)} ≠ ⊤ := by
    rw [Ideal.ne_top_iff_one]
    intro h
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    apply hne
    have : ι (letE i) = ι (letE i) * x := by linear_combination (-ι (letE i)) * hxy - c * hee
    rw [this]
    exact Ideal.mul_mem_left _ _ hx
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hp
  exact ⟨m, hm, le_sup_left.trans hle, hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))⟩

theorem exists_lift {O κ : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing κ] [Nontrivial κ]
    (θ : O⟦X⟧ →+* κ) (h0 : ∀ c ∈ maximalIdeal O, θ (C c) = 0) (hX : IsUnit (θ X)) :
    ∃ θ' : (ResidueField O)⟦X⟧ →+* κ, Function.Injective θ' ∧ ∀ f, θ' (PowerSeries.map (residue O) f) = θ f := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmax : maximalIdeal O = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hker : RingHom.ker (PowerSeries.map (residue O)) ≤ RingHom.ker θ := by
    intro f hf
    have h1 : ∀ k, ∃ d, d * ϖ = coeff k f := fun k => by
      have := congrArg (coeff k) (RingHom.mem_ker.1 hf)
      rw [coeff_map, map_zero, residue_eq_zero_iff, hmax] at this
      exact Ideal.mem_span_singleton'.1 this
    choose d hd using h1
    have h2 : f = C ϖ * PowerSeries.mk d := by
      ext k
      rw [coeff_C_mul, coeff_mk, ← hd, mul_comm]
    rw [RingHom.mem_ker, h2, map_mul, h0 ϖ (hmax ▸ Ideal.mem_span_singleton_self ϖ), zero_mul]
  have hsurj : Function.Surjective (PowerSeries.map (residue O)) :=
    PowerSeries.map_surjective _ residue_surjective
  have hc : ∀ f, RingHom.liftOfSurjective _ hsurj ⟨θ, hker⟩ (PowerSeries.map (residue O) f) = θ f := fun f =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ f
  refine ⟨_, (injective_iff_map_eq_zero _).2 fun f hf => ?_, hc⟩
  by_contra hf0
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hf0 PowerSeries.X_irreducible
  have h3 := hc X
  rw [map_X] at h3
  rw [map_mul, map_pow, h3] at hf
  exact ((u.isUnit.map _).mul (hX.pow k)).ne_zero hf

theorem exists_psi (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) {O R : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [CommRing R] [Algebra O R] {n : ℕ}
    (ι : LetA O n →ₐ[O] R) (m : Ideal R) (hm : m.IsMaximal) (hmO : Ideal.map (algebraMap O R) (maximalIdeal O) ≤ m)
    (i : ZMod n) (hi : 1 - ι (letE i) ∈ m) (hπ : IsUnit (ι letπ)) :
    ∃ ψ : (ResidueField O)⟦X⟧ →+* R ⧸ m, Function.Injective ψ ∧
      (∀ y : ZMod n → O⟦X⟧, Ideal.Quotient.mk m (ι (fun j => inc l O (y j))) =
        ψ (PowerSeries.map (residue O) (y i))) ∧
      ∀ c : O, Ideal.Quotient.mk m (algebraMap O R c) = ψ (C (residue O c)) := by
  haveI : Nontrivial (R ⧸ m) := Ideal.Quotient.nontrivial_iff.2 hm.ne_top
  let θ : O⟦X⟧ →+* R ⧸ m := (Ideal.Quotient.mk m).comp ((ι : LetA O n →+* R).comp (Pi.constRingHom (ZMod n) O⟦X⟧))
  have hθ : ∀ f, θ f = Ideal.Quotient.mk m (ι (fun _ => f)) := fun _ => rfl
  have hC : ∀ c, θ (C c) = Ideal.Quotient.mk m (algebraMap O R c) := fun c => by
    rw [hθ, ← ι.commutes]
    rfl
  have he : Ideal.Quotient.mk m (ι (letE i)) = 1 := by
    have := Ideal.Quotient.eq_zero_iff_mem.2 hi
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this.symm
  have hx : ∀ x : LetA O n, Ideal.Quotient.mk m (ι x) = θ (x i) := fun x => by
    have h1 : (letE i : LetA O n) * x = letE i * fun _ => x i := by
      funext k
      by_cases hk : k = i <;> simp [letE, Pi.single_apply, hk]
    have h2 := congrArg (fun z => Ideal.Quotient.mk m (ι z)) h1
    rw [hθ]
    simpa only [map_mul, he, one_mul] using h2
  obtain ⟨θ', hinj, hθ'⟩ := exists_lift θ (fun c hc => by
    rw [hC]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hmO (Ideal.mem_map_of_mem _ hc))) (hπ.map (Ideal.Quotient.mk m))
  letI : Algebra ℤ_[l] (ResidueField O) := ((residue O).comp (algebraMap ℤ_[l] O)).toAlgebra
  obtain ⟨hadd, hmul, hcst, -, -, -, -, hi'⟩ := pi0Subst_laws_hold l (ResidueField O)
  obtain ⟨-, hred, -⟩ := pi0Subst_reduction_holds l O (ResidueField O) (residue O) (fun _ => rfl)
  let incK : (ResidueField O)⟦X⟧ →+* (ResidueField O)⟦X⟧ :=
    RingHom.mk' ⟨⟨inc l (ResidueField O), by simpa using hcst 1⟩, hmul⟩ hadd
  have hK : ∀ f, incK f = inc l (ResidueField O) f := fun _ => rfl
  refine ⟨θ'.comp incK, hinj.comp (hi' hl), fun y => ?_, fun c => ?_⟩
  · rw [hx, RingHom.comp_apply θ', hK, ← hred, hθ']
  · rw [RingHom.comp_apply, hK, hcst, ← map_C, hθ', hC]

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {f : ℕ}
    {W : LocWach PD LL O v f} {RA' RW' : Type} [CommRing RA'] [CommRing RW'] [Algebra O RA'] [Algebra O RW']
    {inclR' : RA' →ₐ[O] RW'} {φR : RW' →ₐ[O] RW'} {gR : G → (RW' →ₐ[O] RW')} {πA : RA'}
    (E : EtTie W RA' RW' inclR' φR gR πA)

theorem ioE_φE [IsDomain O] (x : W.EE) : E.ioE (W.φE x) = φR (E.ioE x) := by
  obtain ⟨e, e₀, hsp, hj, -⟩ := E.one_e
  obtain ⟨e₁, he₁, hT⟩ := W.one_line
  haveI : Module.Free O ↥W.one.L.T := W.one.L.free
  have he₀ : e₀ ≠ 0 := by
    rintro rfl
    have h1 : (⟨e₁, hT ▸ Submodule.mem_span_singleton_self e₁⟩ : ↥W.one.L.T) ∈ Submodule.span O {(0 : ↥W.one.L.T)} :=
      hsp ▸ Submodule.mem_top
    rw [Submodule.span_zero_singleton, Submodule.mem_bot] at h1
    exact he₁ (congrArg Subtype.val h1)
  have hli : LinearIndependent O (fun _ : Unit => e₀) := by
    rw [linearIndependent_unique_iff]
    exact he₀
  let b₀ := Module.Basis.mk hli (by rw [← hsp, Set.range_const])
  have hb : Algebra.TensorProduct.basis RW' b₀ () = TensorProduct.tmul O (1 : RW') e₀ := by
    rw [Algebra.TensorProduct.basis_apply, Module.Basis.mk_apply]
  have hφe : W.φD _ e = e := E.jD_inj _ (by rw [E.jD_φ, hj]; simp [TWmap])
  have h2 := E.jD_φ _ (x • e)
  rw [W.φD_smul, hφe, E.jD_smul, E.jD_smul, hj] at h2
  have h3 : TWmap φR W.one (E.ioE x • TensorProduct.tmul O (1 : RW') e₀) =
      φR (E.ioE x) • TensorProduct.tmul O (1 : RW') e₀ := by
    simp [TWmap, TensorProduct.smul_tmul']
  rw [h3, ← hb] at h2
  simpa using congrArg (fun z => (Algebra.TensorProduct.basis RW' b₀).repr z ()) h2

theorem exists_unit_tie (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) {n : ℕ}
    (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (e : Module.Basis (Fin n) O ↥T.L.T) :
    ∃ M : Mx RW' n n, IsUnit M.det ∧
      ∀ k, E.jD T (b k : W.DD T) = ∑ j, M j k • Algebra.TensorProduct.basis RW' e j := by
  refine exists_unit_mat _ _ ?_
  rw [← E.jD_span T, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  refine (W.N_base T hT).inductionOn x
    (fun x => E.jD T x ∈ Submodule.span RW' (Set.range fun k => E.jD T (b k : W.DD T))) ?_ ?_ ?_ ?_
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro y
    rw [← b.sum_repr y, map_sum, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smul, ← algebraMap_smul W.EE, E.jD_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · intro s y hy
    rw [E.jD_smul]
    exact Submodule.smul_mem _ _ hy
  · intro y z hy hz
    rw [map_add]
    exact Submodule.add_mem _ hy hz

include E in

theorem rank_eq_of_tie (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O]
    [NeZero f] (h1 : (1 : RW') ∉ Ideal.map (algebraMap O RW') (maximalIdeal O))
    {T T' : LocLat G Qp LL O} {n n' : ℕ} (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T))
    (b' : Module.Basis (Fin n') (LetA O f) ↥(W.N T')) (g : LatHom T.L T'.L) (A : ZMod f → Mx O⟦X⟧ n' n)
    (e : Module.Basis (Fin n) O ↥T.L.T) (e' : Module.Basis (Fin n') O ↥T'.L.T) (a : Mx O n' n)
    (hT : IsCrys PD T.ρ) (hT' : IsCrys PD T'.ρ)
    (hmap : ∀ k, W.map g (b k : W.DD T) = ∑ m, (fun i => inc l O (A i m k) : LetA O f) • (b' m : W.DD T'))
    (ha : ∀ k, g.f (e k : T.V) = ∑ m, algebraMap O LL (a m k) • (e' m : T'.V)) (i : ZMod f) :
    lrank ((A i).map (PowerSeries.map (residue O))) = (a.map (residue O)).rank := by
  obtain ⟨M, hM, hb⟩ := exists_unit_tie E T hT b e
  obtain ⟨M', hM', hb'⟩ := exists_unit_tie E T' hT' b' e'
  let ι := inclR'.comp E.io
  have hι : ∀ x, ι x = E.ioE (algebraMap _ W.EE x) := fun x => (E.ioE_ext x).symm
  obtain ⟨m, hm, hmO, hmi⟩ := choose_max W.φ₀ ι φR (maximalIdeal O)
    (fun x => by rw [hι, hι, ← ioE_φE E, W.φE_ext]) h1 i
  obtain ⟨ψ, hψ, hψA, hψC⟩ := exists_psi l hl ι m hm hmO i hmi (by rw [hι]; exact W.EE_π.map E.ioE)
  have key : M' * (Matrix.of fun r k => ι (fun j => inc l O (A j r k))) = a.map (algebraMap O RW') * M := by
    refine mat_identity (Algebra.TensorProduct.basis RW' e)
      (Algebra.TensorProduct.basis RW' e') (fun k => E.jD T (b k : W.DD T)) (fun k => E.jD T' (b' k : W.DD T'))
      M M' _ _ (LinearMap.baseChange RW' ((g.f.restrictScalars O).restrict g.T_le)) hb hb' (fun k => ?_) (fun k => ?_)
    · have h1 := E.jD_map g (b k : W.DD T)
      rw [hmap k, map_sum] at h1
      refine h1.symm.trans (Finset.sum_congr rfl fun r _ => ?_)
      rw [Matrix.of_apply, hι, ← E.jD_smul, algebraMap_smul]
    · have h2 : ((g.f.restrictScalars O).restrict g.T_le) (e k) = ∑ r, a r k • e' r := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        refine (ha k).trans (Finset.sum_congr rfl fun r _ => ?_)
        rw [Submodule.coe_smul, algebraMap_smul]
      rw [Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul, h2, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Algebra.TensorProduct.basis_apply, Matrix.map_apply, algebraMap_smul, TensorProduct.tmul_smul]
  letI : Field (RW' ⧸ m) := Ideal.Quotient.field m
  have key2 := congrArg (fun Z => Matrix.map Z (Ideal.Quotient.mk m)) key
  simp only [Matrix.map_mul] at key2
  have hr := rank_eq_of_mul_eq _ _ _ _ (by
      have := hM'.map (Ideal.Quotient.mk m)
      rwa [RingHom.map_det] at this) (by
      have := hM.map (Ideal.Quotient.mk m)
      rwa [RingHom.map_det] at this) key2
  rw [← rank_map_inj ψ hψ, ← GlobalTheory.Core.Rk.rank_map_field (ψ.comp PowerSeries.C) (a.map (residue O))]
  convert hr using 2
  · ext1 r k
    exact (hψA fun j => A j r k).symm
  · ext1 r k
    exact (hψC (a r k)).symm

end Generic

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem main : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL) (T T' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (n n' : ℕ) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N T)) (b' : Module.Basis (Fin n') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N T')) (g : LatHom T.L T'.L) (A : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n' n) (e : Module.Basis (Fin n) ↥(OL LL) ↥T.L.T) (e' : Module.Basis (Fin n') ↥(OL LL) ↥T'.L.T) (a : Mx ↥(OL LL) n' n), IsCrys ((D.loc l).PD K) T.ρ → IsCrys ((D.loc l).PD K) T'.ρ → IsMapMat ((HW l).W K 1 LL hA.2.2) g b b' A → (∀ k, g.f (e k : T.V) = ∑ m, ((a m k : ↥(OL LL)) : ↥LL.1) • (e' m : T'.V)) → ∀ i, lrank ((A i).map (PowerSeries.map (residue ↥(OL LL)))) = (a.map (residue ↥(OL LL))).rank := by
  intro D HW F l _ K LL hA T T' n n' b b' g A e e' a hT hT' hmap ha i
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    Module.Finite.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).injective
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  exact rank_eq_of_tie ((F l).E K 1 LL hA.2.2).tie l hA.2.1
    (one_not_mem_map (Z := ℤ_[l]) (C := WCb l) _ (maximalIdeal.isMaximal ↥(OL LL)).ne_top) b b' g A e e' a hT hT' hmap ha i

end GlobalTheory.WachRank
