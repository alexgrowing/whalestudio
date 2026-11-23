import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitSumTensorDualOfCrys

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WachTensor

noncomputable section

namespace GlobalTheory.NL.BaseField

theorem range_of_approx {E E' R : Type} [CommRing E] [CommRing E'] [CommRing R] (f : E →+* R) (f' : E' →+* R)
    (p : ℕ) (hc : IsPrecomplete (Ideal.span {(p : E')}) E') (hsep : ∀ x : R, (∀ k : ℕ, (p : R) ^ k ∣ x) → x = 0)
    (h : ∀ x, ∃ y z, f x = f' y + p * f z) (x : E) : ∃ y, f' y = f x := by
  choose y z hyz using h
  let S : ℕ → E' := fun k => ∑ j ∈ Finset.range k, (p : E') ^ j * y (z^[j] x)
  have hS : ∀ k, f x = f' (S k) + (p : R) ^ k * f (z^[k] x) := by
    intro k
    induction k with
    | zero => simp [S]
    | succ k ih =>
      rw [ih, hyz (z^[k] x), Function.iterate_succ_apply']
      simp only [S, Finset.sum_range_succ, map_add, map_mul, map_pow, map_natCast]
      ring
  have hmem : ∀ (k : ℕ) (a : E'), a ∈ (Ideal.span {(p : E')} ^ k • ⊤ : Submodule E' E') ↔ (p : E') ^ k ∣ a := by
    intro k a
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨L, hL⟩ := hc.prec (f := S) (fun {m n} hmn => by
    rw [SModEq.sub_mem, hmem]
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      have : S m - S (n + 1) = S m - S n - (p : E') ^ n * y (z^[n] x) := by
        simp only [S, Finset.sum_range_succ]; ring
      rw [this]
      exact dvd_sub ih ((pow_dvd_pow _ hn).mul_right _))
  refine ⟨L, (sub_eq_zero.1 (hsep _ fun k => ?_)).symm⟩
  obtain ⟨c, hc⟩ := (hmem k _).1 (SModEq.sub_mem.1 (hL k))
  refine ⟨f' c + f (z^[k] x), ?_⟩
  have h2 := congrArg f' hc
  rw [map_sub, map_mul, map_pow, map_natCast] at h2
  rw [hS k]
  linear_combination h2

theorem series_ext {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (f g : PowerSeries O →ₐ[O] R) (π : R)
    (hf : f PowerSeries.X = π) (hg : g PowerSeries.X = π) (hsep : ∀ x : R, (∀ k : ℕ, π ^ k ∣ x) → x = 0)
    (a : PowerSeries O) : f a = g a := by
  refine sub_eq_zero.1 (hsep _ fun k => ?_)
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    have hC : ∀ (u : PowerSeries O →ₐ[O] R) c, u (PowerSeries.C c) = algebraMap O R c := fun u c => u.commutes c
    rw [PowerSeries.eq_X_mul_shift_add_const a, map_add, map_add, map_mul, map_mul, hf, hg, hC, hC,
      add_sub_add_right_eq_sub, ← mul_sub, pow_succ']
    exact mul_dvd_mul_left _ (ih _)

theorem isBaseChange_span {A E M ι : Type} [CommRing A] [CommRing E] [Algebra A E] [AddCommGroup M] [Module A M]
    [Module E M] [IsScalarTower A E M] (c : Module.Basis ι E M) (hl : LinearIndependent A c) :
    IsBaseChange E (Submodule.span A (Set.range c)).subtype := by
  let b := Module.Basis.span hl
  refine IsBaseChange.of_equiv ((b.baseChange E).equiv c (Equiv.refl _)) fun x => ?_
  have : (((b.baseChange E).equiv c (Equiv.refl _)).toLinearMap.restrictScalars A) ∘ₗ
      (TensorProduct.mk A E _ 1) = (Submodule.span A (Set.range c)).subtype := b.ext fun i => by
    have h := (b.baseChange E).equiv_apply i c (Equiv.refl _)
    rw [Module.Basis.baseChange_apply] at h
    simpa [b, Module.Basis.span_apply] using h
  exact LinearMap.congr_fun this x

theorem map_id_smul {O R M M' : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup M] [Module O M]
    [AddCommGroup M'] [Module O M'] (e : M →ₗ[O] M') (r : R) (x : R ⊗[O] M) :
    TensorProduct.map (LinearMap.id : R →ₗ[O] R) e (r • x) = r • TensorProduct.map LinearMap.id e x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [smul_add, map_add, hx, hx']
  | tmul r' u => simp [TensorProduct.smul_tmul']

theorem map_id_comm {O R M M' : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup M] [Module O M]
    [AddCommGroup M'] [Module O M'] (e : M →ₗ[O] M') (f : R →ₗ[O] R) (a : M →ₗ[O] M) (a' : M' →ₗ[O] M')
    (h : ∀ t, e (a t) = a' (e t)) (x : R ⊗[O] M) :
    TensorProduct.map (LinearMap.id : R →ₗ[O] R) e (TensorProduct.map f a x) =
      TensorProduct.map f a' (TensorProduct.map LinearMap.id e x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | tmul r' u => simp [h]

theorem map_id_symm {O R M M' : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup M] [Module O M]
    [AddCommGroup M'] [Module O M'] (e : M ≃ₗ[O] M') (x : R ⊗[O] M) :
    TensorProduct.map (LinearMap.id : R →ₗ[O] R) e.symm.toLinearMap
      (TensorProduct.map LinearMap.id e.toLinearMap x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | tmul r' u => simp

theorem mem_GK_of_chi {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K K' : FinExt l} {s : ℕ} (h' : K'.1 ≤ Ks K' s)
    (h0 : K0 K' = K0 K) {g : GQ l} (hg : g ∈ GK K) (hχ : P.χQ g = 1) : g ∈ GK K' := by
  have h1 : Ks K' s ≤ IntermediateField.fixedField (Subgroup.zpowers g) := by
    have hm : ∀ x, g x = x → x ∈ IntermediateField.fixedField (Subgroup.zpowers g) := by
      intro x hx
      rw [IntermediateField.mem_fixedField_iff]
      intro f hf
      have : Subgroup.zpowers g ≤ MulAction.stabilizer (GQ l) x := by
        rw [Subgroup.zpowers_le]; exact hx
      exact this hf
    refine sup_le ?_ ?_
    · rw [h0]
      intro x hx
      exact hm x (hg ⟨x, hx.1⟩)
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      obtain ⟨a, ha, hga⟩ := P.χQ_cyc g s x hx
      refine hm x ?_
      rw [hχ] at ha
      have h2 : ((l : ℤ) ^ s) ∣ (1 - a : ℤ) := by
        rw [← Padic.norm_int_le_pow_iff_dvd]
        simpa using ha
      have h3 : a ≡ 1 [MOD l ^ s] := (Nat.modEq_iff_dvd).2 (by simpa using h2)
      rw [hga, pow_eq_pow_mod a hx, h3, ← pow_eq_pow_mod 1 hx, pow_one]
  intro x
  exact (IntermediateField.mem_fixedField_iff _ _).1 (h1 (h' x.2)) g (Subgroup.mem_zpowers g)

section Generic

variable {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K] [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B] [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {PD' : PeriodData G' Qp K₀' K' B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n n' : ℕ}
    {W : LocWach PD LL O v n} {W' : LocWach PD' LL O v n'} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {gR' : G' → (RW →ₐ[O] RW)}
    {πA : RA} (E : EtTie W RA RW inclR φR gR πA) (E' : EtTie W' RA RW inclR φR gR' πA)

theorem n_ne_zero (W : LocWach PD LL O v n) : n ≠ 0 := by
  haveI := PD.finK₀
  rw [W.n_eq]
  exact Module.finrank_pos.ne'

theorem φA_letE (W : LocWach PD LL O v n) (i : ZMod n) : W.φA (letE (i - 1)) = letE i := by
  funext k
  change W.φ₀ ((Pi.single (i - 1) 1 : LetA O n) (k - 1)) = (Pi.single i 1 : LetA O n) k
  by_cases h : k = i
  · subst h; simp
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (fun e => h (sub_left_injective e)), map_zero]

theorem io_mem (hO : Function.Injective (algebraMap O LL)) (hd : Descends E') (hi : Function.Injective inclR)
    (hint : ∀ x : W'.EE, (∃ y, inclR y = E'.ioE x) → ∃ a : LetA O n', algebraMap _ W'.EE a = x)
    (hH : ∀ g' : G', W'.resΓ g' = 1 → ∃ g : G, W.resΓ g = 1 ∧ gR g = gR' g')
    (hsep : ∀ x : RA, (∀ k : ℕ, πA ^ k ∣ x) → x = 0) (a : LetA O n) : ∃ a', E'.io a' = E.io a := by
  classical
  haveI : NeZero n := ⟨n_ne_zero W⟩
  have h1 := hd (ZMod n) (fun i j => if j = i - 1 then 1 else 0)
    (fun i => E.ioE (algebraMap (LetA O n) W.EE (letE i))) ?_ ?_
  · have h2 : ∀ i, ∃ a', E'.io a' = E.io (letE i) := by
      intro i
      obtain ⟨e, he⟩ := h1 i
      rw [E.ioE_ext] at he
      obtain ⟨a', rfl⟩ := hint e ⟨_, he.symm⟩
      rw [E'.ioE_ext] at he
      exact ⟨a', hi he⟩
    choose u hu using h2
    have h3 : ∀ f : PowerSeries O, E'.io (fun _ => f) = E.io (fun _ => f) := fun f =>
      series_ext (E'.io.comp (AlgHom.pi fun _ => AlgHom.id O _)) (E.io.comp (AlgHom.pi fun _ => AlgHom.id O _)) πA
        E'.io_π E.io_π hsep f
    refine ⟨∑ i, u i * fun _ => a i, ?_⟩
    simp only [map_sum, map_mul, hu, h3]
    simp only [← map_mul, ← map_sum]
    congr 1
    funext k
    simp [letE, Finset.sum_apply, Pi.single_apply]
  · intro g' hg' i
    obtain ⟨g, hg, e⟩ := hH g' hg'
    rw [← e, ← ioE_γE E hO, hg, map_one]
    rfl
  · intro i
    rw [Finset.sum_eq_single (i - 1) (fun j _ hj => by simp [hj]) (by simp), if_pos rfl, map_one, one_mul,
      ← ioE_φE E hO, W.φE_ext]
    exact congrArg _ (congrArg _ (φA_letE W i).symm)

theorem ioE_mem (hp : PD'.p = PD.p) (hA : ∀ a, ∃ a', E'.io a' = E.io a)
    (hsep : ∀ x : RW, (∀ k : ℕ, (PD.p : RW) ^ k ∣ x) → x = 0) (x : W.EE) : ∃ x', E'.ioE x' = E.ioE x := by
  refine range_of_approx E.ioE.toRingHom E'.ioE.toRingHom PD.p (hp ▸ W'.EE_complete.toIsPrecomplete) hsep ?_ x
  intro x
  obtain ⟨a, m, h⟩ := W.EE_dense x 1
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.1 h
  obtain ⟨a', ha'⟩ := hA a
  obtain ⟨u, hu⟩ := (W.EE_π.pow m).exists_right_inv
  obtain ⟨u', hu'⟩ := (W'.EE_π.pow m).exists_right_inv
  refine ⟨algebraMap _ W'.EE a' * u', z * u, ?_⟩
  have h1 := congrArg E.ioE hu
  have h2 := congrArg E'.ioE hu'
  have h3 := congrArg E.ioE hz
  simp only [map_mul, map_pow, map_sub, map_one, map_natCast, E.ioE_ext, E'.ioE_ext, E.io_π, E'.io_π,
    pow_one] at h1 h2 h3
  change E.ioE x = E'.ioE _ + _ * E.ioE _
  rw [map_mul, map_mul, E'.ioE_ext, ha']
  linear_combination (E.ioE u) * h3 - (E.ioE x) * h1 + inclR (E.io a) * E'.ioE u' * h1
    - inclR (E.io a) * E.ioE u * h2

theorem jD_mem (hd : Descends E') (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤)
    (hφ : Function.Surjective φR) (hE : ∀ x, ∃ x', E'.ioE x' = E.ioE x)
    (T : LocLat G Qp LL O) (T' : LocLat G' Qp LL O) (e : ↥T.L.T →ₗ[O] ↥T'.L.T)
    (hH : ∀ g' : G', W'.resΓ g' = 1 → ∃ g : G, W.resΓ g = 1 ∧ gR g = gR' g' ∧
      ∀ t, e (T.actT g t) = T'.actT g' (e t)) (x : W.DD T) :
    ∃ x', E'.jD T' x' = TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) e (E.jD T x) := by
  obtain ⟨b⟩ := exists_basis_DD E T
  obtain ⟨U, hU⟩ := exists_frob_mat E hm hφ T b
  choose θ hθ using hE
  have h1 := mem_range_jD E' hd T' (fun a c => θ (U a c))
    (fun a => TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) e (E.jD T (b a))) ?_ ?_
  · choose y hy using h1
    refine ⟨∑ a, θ (b.repr x a) • y a, ?_⟩
    conv_rhs => rw [← b.sum_repr x]
    simp only [map_sum, E.jD_smul, E'.jD_smul, hθ, hy, map_id_smul]
  · intro g' hg' a
    obtain ⟨g, hg, e1, e2⟩ := hH g' hg'
    rw [TWact, ← map_id_comm e _ (T.actT g) _ e2, ← e1]
    exact congrArg _ (jD_fixed E T g hg _)
  · intro a
    conv_lhs => rw [hU a, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_id_smul, hθ, TWmap, TWmap, map_id_comm e _ LinearMap.id LinearMap.id (fun _ => rfl)]

theorem jD_smulA (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    E.jD T (a • x) = inclR (E.io a) • E.jD T x := by
  rw [← E.ioE_ext, ← E.jD_smul, algebraMap_smul]

theorem N_eq (T : LocLat G Qp LL O) (T' : LocLat G' Qp LL O) (e : ↥T'.L.T ≃ₗ[O] ↥T.L.T)
    (hT : IsCrys PD T.ρ) (h10 : p10 W' T') {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T))
    (hinj : Function.Injective E'.ioE)
    (hA : ∀ a, ∃ a', E'.io a' = E.io a) (hA' : ∀ a', ∃ a, E.io a = E'.io a')
    (hE : ∀ x, ∃ x', E'.ioE x' = E.ioE x) (hQ : E'.io W'.Q = E.io W.Q)
    (hD : ∀ x, ∃ x', TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) e.toLinearMap (E'.jD T' x') = E.jD T x)
    (hD' : ∀ x', ∃ x, E.jD T x = TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) e.toLinearMap (E'.jD T' x'))
    (hG : ∀ g' : G', ∃ g : G, gR g = gR' g' ∧ ∀ t, e (T'.actT g' t) = T.actT g (e t)) :
    TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) e.toLinearMap '' (E'.jD T' '' (W'.N T' : Set (W'.DD T'))) =
      E.jD T '' (W.N T : Set (W.DD T)) := by
  let J : W'.DD T' →ₗ[O] TW RW T :=
    (TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) e.toLinearMap) ∘ₗ E'.jD T'
  have hJ : ∀ x, TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) e.toLinearMap (E'.jD T' x) = J x := fun _ => rfl
  simp only [hJ] at hD hD'
  have Jinj : Function.Injective J := fun x y h => E'.jD_inj T' (by
    rw [← map_id_symm e (E'.jD T' x), hJ, h, ← hJ, map_id_symm])
  have JE : ∀ (c : W'.EE) x, J (c • x) = E'.ioE c • J x := fun c x => by
    rw [← hJ, E'.jD_smul, map_id_smul, hJ]
  have JA : ∀ (c : LetA O n') x, J (c • x) = inclR (E'.io c) • J x := fun c x => by
    rw [← hJ, jD_smulA, map_id_smul, hJ]
  have Jφ : ∀ x, J (W'.φD T' x) = TWmap φR T (J x) := fun x => by
    rw [← hJ, E'.jD_φ, TWmap, map_id_comm e.toLinearMap _ LinearMap.id LinearMap.id (fun _ => rfl), hJ, TWmap]
  choose ψ hψ using hD
  choose θ hθ using hA
  choose θ' hθ' using hA'
  choose θE hθE using hE
  obtain ⟨C, hC⟩ := exists_basis_jD E T ((W.N_base T hT).basis b)
  have hb : ∀ j, (W.N_base T hT).basis b j = (b j : W.DD T) := fun j => by
    rw [IsBaseChange.basis_apply b (W.N_base T hT) j]; rfl
  have hli : LinearIndependent W'.EE fun j => ψ (b j : W.DD T) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h1 := congrArg J hc
    simp only [map_sum, JE, hψ, map_zero, ← hb, ← hC] at h1
    exact hinj ((Fintype.linearIndependent_iff.1 C.linearIndependent _ h1 j).trans (map_zero _).symm)
  have hsp : ⊤ ≤ Submodule.span W'.EE (Set.range fun j => ψ (b j : W.DD T)) := by
    intro y _
    obtain ⟨x, hx⟩ := hD' y
    refine (Submodule.mem_span_range_iff_exists_fun _).2
      ⟨fun j => θE (((W.N_base T hT).basis b).repr x j), Jinj ?_⟩
    rw [← hx]
    conv_rhs => rw [← ((W.N_base T hT).basis b).sum_repr x]
    simp only [map_sum, JE, E.jD_smul, hθE, hψ, hb]
  let c := Module.Basis.mk hli hsp
  have hc : ∀ j, J (c j) = E.jD T (b j : W.DD T) := fun j => by rw [Module.Basis.mk_apply, hψ]
  have hliA : LinearIndependent (LetA O n') c := by
    refine c.linearIndependent.restrict_scalars fun x y h => W'.EE_inj ?_
    simpa [Algebra.smul_def] using h
  have hmem : ∀ y, y ∈ Submodule.span (LetA O n') (Set.range c) ↔ ∃ x ∈ W.N T, E.jD T x = J y := by
    intro y
    rw [Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨∑ j, θ' (a j) • (b j : W.DD T), Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (b j).2, ?_⟩
      simp only [map_sum, JA, jD_smulA, hθ', hc]
    · rintro ⟨x, hx, hy⟩
      refine ⟨fun j => θ (b.repr ⟨x, hx⟩ j), Jinj ?_⟩
      have h1 := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
      rw [← hy]
      conv_rhs => rw [show x = _ from h1.symm]
      simp only [map_sum, JA, hθ, hc, AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, jD_smulA]
  have hψN : ∀ x ∈ W.N T, ψ x ∈ Submodule.span (LetA O n') (Set.range c) :=
    fun x hx => (hmem _).2 ⟨x, hx, (hψ x).symm⟩
  obtain ⟨g', hg'⟩ := W'.resΓ_onto W'.gam
  obtain ⟨g, hg, hge⟩ := hG g'
  have Jγ : ∀ x y, E.jD T x = J y → E.jD T (W.γD T (W.resΓ g) x) = J (W'.γ T' y) := fun x y h => by
    rw [LocWach.γ, ← hg', ← hJ, E'.jD_act, TWact, map_id_comm _ _ _ (T.actT g) hge, hJ, ← h, E.jD_act, hg, TWact]
  have key := h10 (Submodule.span (LetA O n') (Set.range c)) ?_ (isBaseChange_span c hliA) ?_ ?_ ?_ ?_
  · rw [← key]
    ext z
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact (hmem y).1 hy
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, ⟨ψ x, hψN x hx, rfl⟩, hψ x⟩
  · refine ⟨r, c, fun j => Submodule.subset_span ⟨j, rfl⟩, fun x hx => ?_⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    refine ⟨a, ha.symm, fun a' ha' => funext ?_⟩
    exact Fintype.linearIndependent_iffₛ.1 hliA a' a (ha'.symm.trans ha.symm)
  · intro y hy
    obtain ⟨x, hx, h⟩ := (hmem y).1 hy
    exact (hmem _).2 ⟨_, W.N_Γ T _ x hx, Jγ x y h⟩
  · intro y hy
    obtain ⟨x, hx, h⟩ := (hmem y).1 hy
    obtain ⟨w, hw, h2⟩ := W.N_π T (W.resΓ g) x hx
    refine ⟨ψ w, hψN w hw, Jinj ?_⟩
    change J ((letπ : LetA O n') • ψ w) = _
    rw [JA, hψ, map_sub, ← h, ← Jγ x y h, ← map_sub, h2, jD_smulA, E.io_π, E'.io_π]
  · intro y hy
    obtain ⟨x, hx, h⟩ := (hmem y).1 hy
    obtain ⟨k, hk⟩ := W.N_φ T x hx
    refine ⟨k, (hmem _).2 ⟨W.Q ^ k • W.φD T x, hk, ?_⟩⟩
    rw [JA, jD_smulA, map_pow, map_pow E'.io, hQ, Jφ, E.jD_φ, h]
  · intro y hy
    obtain ⟨x, hx, h⟩ := (hmem y).1 hy
    obtain ⟨k, hk⟩ := W.N_φinv T x hx
    have h1 : ∀ z ∈ Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))),
        ∃ w ∈ φspan W' T' (Submodule.span (LetA O n') (Set.range c)), J w = E.jD T z := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨u, hu, rfl⟩ := hz
        exact ⟨_, Submodule.subset_span ⟨ψ u, hψN u hu, rfl⟩, by rw [Jφ, hψ, E.jD_φ]⟩
      | zero => exact ⟨0, zero_mem _, by rw [map_zero, map_zero]⟩
      | add z z' _ _ h1 h2 =>
        obtain ⟨w, hw, e1⟩ := h1
        obtain ⟨w', hw', e2⟩ := h2
        exact ⟨w + w', add_mem hw hw', by rw [map_add, map_add, e1, e2]⟩
      | smul a z _ h1 =>
        obtain ⟨w, hw, e1⟩ := h1
        exact ⟨θ a • w, Submodule.smul_mem _ _ hw, by rw [JA, jD_smulA, hθ, e1]⟩
    obtain ⟨w, hw, e1⟩ := h1 (W.Q ^ k • x) hk
    refine ⟨k, (show w = W'.Q ^ k • y from Jinj ?_) ▸ hw⟩
    rw [e1, JA, jD_smulA, map_pow, map_pow E'.io, hQ, h]

end Generic

end GlobalTheory.NL.BaseField
