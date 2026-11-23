import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSqz
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ContSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HhGroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KerGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.TactVanish
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.TchPoly

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem inf_pow_bot (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R)
    (h : maximalIdeal R * I = ⊥) : ∃ N : ℕ, ∀ x ∈ I, x ∈ maximalIdeal R ^ N → x = 0 := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (maximalIdeal R) (M := R) I
  refine ⟨k + 1, fun x hxI hxN => ?_⟩
  have hx : x ∈ (maximalIdeal R ^ (k + 1) • ⊤ ⊓ I : Submodule R R) := by
    refine ⟨?_, hxI⟩
    rw [smul_eq_mul, Ideal.mul_top]
    exact hxN
  rw [hk (k + 1) (by omega), show k + 1 - k = 1 by omega, pow_one] at hx
  have hle : (maximalIdeal R • (maximalIdeal R ^ k • ⊤ ⊓ I) : Submodule R R) ≤ maximalIdeal R * I :=
    Submodule.smul_mono le_rfl inf_le_right
  have hx' := hle hx
  rw [h] at hx'
  exact (Submodule.mem_bot R).mp hx'

private theorem lc_of_cont (R Γ : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [TopologicalSpace Γ]
    (I : Ideal R) (h : maximalIdeal R * I = ⊥) (x y : Γ → R) (hx : AdicCont (maximalIdeal R) x)
    (hy : AdicCont (maximalIdeal R) y) (hI : ∀ g, x g - y g ∈ I) : IsLocallyConstant fun g => x g - y g := by
  obtain ⟨N, hN⟩ := inf_pow_bot R I h
  have hc : IsLocallyConstant fun g => Ideal.Quotient.mk (maximalIdeal R ^ N) (x g - y g) := by
    have h1 := (hx N).comp₂ (hy N) (fun u v => u - v)
    simpa [map_sub] using h1
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  obtain ⟨U, hU, hgU, hUc⟩ := (IsLocallyConstant.iff_exists_open _).mp hc g
  refine ⟨U, hU, hgU, fun g' hg' => ?_⟩
  have he := hUc g' hg'
  rw [Ideal.Quotient.eq] at he
  have hd : (x g' - y g') - (x g - y g) ∈ I := I.sub_mem (hI g') (hI g)
  exact sub_eq_zero.mp (hN _ hd he)

private theorem cont_map {O R R' Γ : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] [TopologicalSpace Γ] (f : R →ₐ[O] R') (y : Γ → R)
    (hy : AdicCont (maximalIdeal R) y) : AdicCont (maximalIdeal R') fun g => f (y g) := fun N => by
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R') := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show f y ∈ maximalIdeal R'
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hy
  exact (hy N).comp (Ideal.quotientMap _ (f : R →+* R') hle)

private theorem square_zero_extension_ring (O R S X : Type) [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing S] [Algebra O S] [Algebra R S] [IsScalarTower O R S] (I : Ideal R) (hI : I * I = ⊥) (τ : X → S)
    (hτ : LinearIndependent R τ) (x0 : X) (h0 : τ x0 = 1) (F : Finset X) (hF : x0 ∉ F) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra O A) (_ : IsCO O A) (φ : A →ₐ[O] S) (q : A →ₐ[O] R) (i : R →ₐ[O] A),
      Function.Injective φ ∧ (∀ x, φ (i x) = algebraMap R S x) ∧ (∀ x, q (i x) = x) ∧
      ∀ e ∈ F, ∀ y ∈ I, ∃ z, φ z = τ e * algebraMap R S y ∧ q z = 0 := by
  classical
  have hII : ∀ a b : R, a ∈ I → b ∈ I → a * b = 0 := by
    intro a b ha hb
    have hab : a * b ∈ I * I := Ideal.mul_mem_mul ha hb
    rw [hI] at hab
    exact (Submodule.mem_bot R).mp hab
  have halg : ∀ c : O, algebraMap O (TrivSqZeroExt R (↥F → ↥I)) c =
      TrivSqZeroExt.inl (algebraMap O R c) := fun c => rfl
  let g : TrivSqZeroExt R (↥F → ↥I) → S := fun x =>
    algebraMap R S x.fst + ∑ e : ↥F, τ e * algebraMap R S (x.snd e : R)
  have hg_add : ∀ x y, g (x + y) = g x + g y := by
    intro x y
    simp only [g, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, Pi.add_apply, Submodule.coe_add,
      map_add, mul_add, Finset.sum_add_distrib]
    ring
  have hg_mul : ∀ x y, g (x * y) = g x * g y := by
    intro x y
    have hcross : (∑ e : ↥F, τ e * algebraMap R S (x.snd e : R)) *
        (∑ e : ↥F, τ e * algebraMap R S (y.snd e : R)) = 0 := by
      rw [Finset.sum_mul_sum]
      refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun e' _ => ?_
      have h0 : (x.snd e : R) * (y.snd e' : R) = 0 := hII _ _ (x.snd e).2 (y.snd e').2
      calc τ e * algebraMap R S (x.snd e : R) * (τ e' * algebraMap R S (y.snd e' : R))
          = τ e * τ e' * algebraMap R S ((x.snd e : R) * (y.snd e' : R)) := by rw [map_mul]; ring
        _ = 0 := by rw [h0, map_zero, mul_zero]
    simp only [g, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, op_smul_eq_smul, Pi.add_apply,
      Pi.smul_apply, Submodule.coe_add, Submodule.coe_smul, smul_eq_mul, map_add, map_mul, mul_add,
      Finset.sum_add_distrib]
    have e1 : ∑ e : ↥F, τ e * (algebraMap R S x.fst * algebraMap R S (y.snd e : R)) =
        algebraMap R S x.fst * ∑ e : ↥F, τ e * algebraMap R S (y.snd e : R) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by ring
    have e2 : ∑ e : ↥F, τ e * (algebraMap R S y.fst * algebraMap R S (x.snd e : R)) =
        algebraMap R S y.fst * ∑ e : ↥F, τ e * algebraMap R S (x.snd e : R) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by ring
    rw [e1, e2]
    linear_combination -hcross
  let φ : TrivSqZeroExt R (↥F → ↥I) →ₐ[O] S :=
    { toFun := g
      map_one' := by simp [g]
      map_mul' := hg_mul
      map_zero' := by simp [g]
      map_add' := hg_add
      commutes' := fun c => by
        simp only [halg, g, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, Pi.zero_apply,
          ZeroMemClass.coe_zero, map_zero, mul_zero, Finset.sum_const_zero, add_zero]
        exact (IsScalarTower.algebraMap_apply O R S c).symm }
  refine ⟨TrivSqZeroExt R (↥F → ↥I), inferInstance, inferInstance,
    co_sqz O R (↥F → ↥I) halg, φ, TrivSqZeroExt.fstHom O R (↥F → ↥I),
    TrivSqZeroExt.inlAlgHom O R (↥F → ↥I), ?_, fun x => ?_, fun x => rfl, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    change g x = 0 at hx
    let c : X → R := fun j => if j = x0 then x.fst else if h : j ∈ F then (x.snd ⟨j, h⟩ : R) else 0
    have hsum : ∑ j ∈ insert x0 F, c j • τ j = 0 := by
      rw [Finset.sum_insert hF]
      have hc0 : c x0 = x.fst := by simp [c]
      have hcF : ∀ j ∈ F, c j • τ j = τ j * algebraMap R S (if h : j ∈ F then (x.snd ⟨j, h⟩ : R) else 0) := by
        intro j hj
        have hne : j ≠ x0 := fun h => hF (h ▸ hj)
        simp only [c, if_neg hne, Algebra.smul_def]
        ring
      rw [Finset.sum_congr rfl hcF, hc0, Algebra.smul_def, h0, mul_one]
      rw [← Finset.sum_coe_sort F]
      simpa [g] using hx
    have hz := (linearIndependent_iff'.mp hτ) _ c hsum
    apply TrivSqZeroExt.ext
    · have := hz x0 (Finset.mem_insert_self _ _)
      simpa [c] using this
    · funext e
      have := hz e (Finset.mem_insert_of_mem e.2)
      have hne : (e : X) ≠ x0 := fun h => hF (h ▸ e.2)
      simp only [c, if_neg hne, dif_pos e.2] at this
      exact Subtype.ext this
  · change g (TrivSqZeroExt.inl x) = algebraMap R S x
    simp [g]
  · intro e he y hy
    refine ⟨TrivSqZeroExt.inr (Pi.single ⟨e, he⟩ ⟨y, hy⟩), ?_, by simp⟩
    change g _ = _
    simp only [g, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_zero, zero_add]
    rw [Finset.sum_eq_single ⟨e, he⟩]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · simp

private theorem ker_span (O X R R' : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [AddCommGroup X] [CommRing R] [Algebra O R] [IsCO O R] [CommRing R']
    [Algebra O R'] (p : R →ₐ[O] R') (hp : maximalIdeal R * RingHom.ker p = ⊥) (W : WPres O X R)
    (hW : IsHomog O W.wt (RingHom.ker (p.comp W.π))) :
    ∃ (n : ℕ) (ε : Fin n → R) (c : Fin n → X), (∀ i, ε i ∈ W.part (c i)) ∧ (∀ i, p (ε i) = 0) ∧
      ∀ u, p u = 0 → ∃ o : Fin n → O, u = ∑ i, o i • ε i := by
  haveI : Fintype W.σ := W.fin
  obtain ⟨n, f, c, hf, hJ⟩ := ker_gen O X W.σ W.wt (RingHom.ker (p.comp W.π)) hW
  have hfk : ∀ i, f i ∈ RingHom.ker (p.comp W.π) := fun i => hJ ▸ Ideal.subset_span ⟨i, rfl⟩
  refine ⟨n, fun i => W.π (f i), c, fun i => ⟨f i, hf i, rfl⟩, fun i => ?_, fun u hu => ?_⟩
  · exact (RingHom.mem_ker).mp (hfk i)
  · obtain ⟨F, rfl⟩ := W.surj u
    have hF : F ∈ Ideal.span (Set.range f) := by
      rw [← hJ, RingHom.mem_ker]
      exact hu
    obtain ⟨g, hg⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hF
    choose o ho using fun i => IsCO.res_surj (O := O) (W.π (g i))
    refine ⟨o, ?_⟩
    rw [← hg, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    have hm : (W.π (g i) - algebraMap O R (o i)) * W.π (f i) = 0 := by
      have hmem : (W.π (g i) - algebraMap O R (o i)) * W.π (f i) ∈ maximalIdeal R * RingHom.ker p :=
        Ideal.mul_mem_mul (ho i) ((RingHom.mem_ker).mpr ((RingHom.mem_ker).mp (hfk i)))
      rw [hp] at hmem
      exact (Submodule.mem_bot R).mp hmem
    rw [Algebra.smul_def]
    linear_combination hm

private theorem torus_data (O X R : Type) [CommRing O] [IsLocalRing O] [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] [CommRing R] [Algebra O R] [IsCO O R] :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra O S) (_ : IsCO O S) (_ : Algebra R S) (_ : IsScalarTower O R S)
      (T : Multiplicative X →* Sˣ), (∀ j, res O S (T j) = 1) ∧
      LinearIndependent R fun j : X => (T (Multiplicative.ofAdd j) : S) := by
  obtain ⟨n, t, h1, h2⟩ := tchar O X
  haveI hco : IsCO O (MvPowerSeries (Fin n) R) := co_mvps O R (Fin n)
  let T : Multiplicative X →* (MvPowerSeries (Fin n) R)ˣ :=
    (Units.map (MvPowerSeries.map (algebraMap O R) :
      MvPowerSeries (Fin n) O →+* MvPowerSeries (Fin n) R).toMonoidHom).comp t
  refine ⟨MvPowerSeries (Fin n) R, inferInstance, inferInstance, hco, inferInstance, inferInstance, T, ?_, ?_⟩
  · intro j
    have hm : (T j : MvPowerSeries (Fin n) R) - 1 ∈ maximalIdeal (MvPowerSeries (Fin n) R) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
      have hc : MvPowerSeries.constantCoeff ((T j : MvPowerSeries (Fin n) R) - 1) = 0 := by
        simp [T, MvPowerSeries.constantCoeff_map, h1 j]
      rw [hc]
      exact not_isUnit_zero
    rw [← res_eq_zero_iff O, map_sub, map_one, sub_eq_zero] at hm
    exact hm
  · rw [linearIndependent_iff']
    intro s g hg j hj
    apply h2 R s g _ j hj
    rw [← hg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPowerSeries.smul_eq_C_mul, mul_comm]
    rfl

private theorem split_data (O X R R' κ : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [CommRing R]
    [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] [Fintype κ] (d : κ → X) (p : R →ₐ[O] R')
    (hp : maximalIdeal R * RingHom.ker p = ⊥) (W : WPres O X R) (hz : ∀ s, W.z s ∈ maximalIdeal R)
    (hW : IsHomog O W.wt (RingHom.ker (p.comp W.π))) :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra O S) (_ : IsCO O S) (A : Type) (_ : CommRing A) (_ : Algebra O A)
      (_ : IsCO O A) (T : Multiplicative X →* Sˣ) (c : R →ₐ[O] S) (φ : A →ₐ[O] S) (q : A →ₐ[O] R) (i : R →ₐ[O] A),
      (∀ j, res O S (T j) = 1) ∧ Function.Injective φ ∧ (∀ x, q (i x) = x) ∧
      (∀ j, ∀ x ∈ W.part j, φ (i x) = T (Multiplicative.ofAdd j) * c x) ∧
      ∀ k u, p u = 0 → ∃ z, φ z = T (Multiplicative.ofAdd (d k)) * c u ∧ q z ∈ W.part (d k) ∧ p (q z) = 0 := by
  classical
  obtain ⟨S, iS, aOS, coS, aRS, tow, T, hT1, hTli⟩ := torus_data O X R
  obtain ⟨n, ε, cd, hεp, hεk, hsp⟩ := ker_span O X R R' p hp W hW
  obtain ⟨c, hc, -⟩ := tact O X R W hz S (IsScalarTower.toAlgHom O R S) T⁻¹
  have hkm : RingHom.ker p ≤ maximalIdeal R := by
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 : p 1 = 0 := by
      obtain ⟨y, hy⟩ := hu.exists_right_inv
      rw [← hy, map_mul, RingHom.mem_ker.mp hx, zero_mul]
    exact one_ne_zero ((map_one p).symm.trans h1)
  have hI : RingHom.ker p * RingHom.ker p = ⊥ := by
    rw [eq_bot_iff, ← hp]
    exact Ideal.mul_mono_left hkm
  let F : Finset X :=
    ((Finset.univ : Finset (κ × Fin n)).image fun ki => d ki.1 - cd ki.2).filter (· ≠ 0)
  have hF : (0 : X) ∉ F := by simp [F]
  obtain ⟨A, iA, aOA, coA, φ, q, i, hφ, hφi, hqi, hzF⟩ := square_zero_extension_ring O R S X (RingHom.ker p) hI
    (fun j => (T (Multiplicative.ofAdd j) : S)) hTli 0 (by simp) F hF
  refine ⟨S, iS, aOS, coS, A, iA, aOA, coA, T, c, φ, q, i, hT1, hφ, hqi, ?_, ?_⟩
  · intro j x hx
    rw [hφi, hc j x hx, MonoidHom.inv_apply, ← mul_assoc, Units.mul_inv, one_mul]
    rfl
  · intro k u hu
    obtain ⟨o, rfl⟩ := hsp u hu
    have hmk : ∀ l, o l • ε l ∈ RingHom.ker p := by
      intro l
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (RingHom.mem_ker.mpr (hεk l))
    have hTs : ∀ a b : X, (T (Multiplicative.ofAdd (a - b)) : S) =
        T (Multiplicative.ofAdd a) * ↑(T (Multiplicative.ofAdd b))⁻¹ := by
      intro a b
      rw [ofAdd_sub, map_div, div_eq_mul_inv, Units.val_mul]
    have hZ : ∀ l : Fin n, ∃ z : A, φ z = (if d k = cd l then 0 else
        (T (Multiplicative.ofAdd (d k - cd l)) : S) * algebraMap R S (o l • ε l)) ∧ q z = 0 := by
      intro l
      split_ifs with h
      · exact ⟨0, map_zero _, map_zero _⟩
      · have he : d k - cd l ∈ F := by
          simp only [F, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨⟨(k, l), rfl⟩, sub_ne_zero.mpr h⟩
        exact hzF _ he _ (hmk l)
    choose Z hZ1 hZ2 using hZ
    let v : R := ∑ l, if d k = cd l then o l • ε l else 0
    have hv : v ∈ W.part (d k) := by
      refine Submodule.sum_mem _ fun l _ => ?_
      split_ifs with h
      · rw [h]
        exact Submodule.smul_mem _ _ (hεp l)
      · exact Submodule.zero_mem _
    have hqz : q (i v + ∑ l, Z l) = v := by
      rw [map_add, hqi, map_sum]
      simp [hZ2]
    refine ⟨i v + ∑ l, Z l, ?_, by rw [hqz]; exact hv, ?_⟩
    · simp only [v, map_add, hφi, map_sum]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hZ1, hc (cd l) _ (Submodule.smul_mem _ _ (hεp l)), MonoidHom.inv_apply,
        IsScalarTower.coe_toAlgHom']
      split_ifs with h
      · rw [add_zero, h, ← mul_assoc, Units.mul_inv, one_mul]
      · rw [map_zero, zero_add, hTs, mul_assoc]
    · rw [hqz]
      simp only [v, map_sum]
      refine Finset.sum_eq_zero fun l _ => ?_
      split_ifs
      · exact RingHom.mem_ker.mp (hmk l)
      · exact map_zero _

private theorem hh_of_inj {O ι X : Type} [CommRing O] [IsLocalRing O] [Fintype ι] [DecidableEq ι] [AddCommGroup X]
    {w : ι → X} (Φ : FormData O w) {A S : Type} [CommRing A] [Algebra O A] [IsCO O A] [CommRing S] [Algebra O S]
    [IsCO O S] (φ : A →ₐ[O] S) (hφ : Function.Injective φ) (h : Matrix ι ι A) (hh : Φ.HH (h.map φ)) : Φ.HH h := by
  obtain ⟨h1, h2, h3⟩ := hh
  have hJ : (Φ.JR A).map φ = Φ.JR S := by
    ext a b
    simp [FormData.JR]
  have hinj : ∀ M M' : Matrix ι ι A, M.map φ = M'.map φ → M = M' := fun M M' hM => by
    ext a b
    exact hφ (congrFun (congrFun hM a) b)
  refine ⟨hinj _ _ ?_, fun a b hab => ?_, ?_⟩
  · change φ.mapMatrix (h.transpose * Φ.JR A * h) = φ.mapMatrix (Φ.JR A)
    rw [map_mul, map_mul]
    change (h.transpose).map φ * (Φ.JR A).map φ * h.map φ = (Φ.JR A).map φ
    rw [hJ, Matrix.transpose_map]
    exact h1
  · apply hφ
    rw [map_zero]
    exact h2 a b hab
  · ext a b
    have h4 := congrFun (congrFun h3 a) b
    simpa [res_map] using h4

private theorem inH_map {O ι X Γ : Type} [CommRing O] [IsLocalRing O] [Fintype ι] [DecidableEq ι] [AddCommGroup X]
    {w : ι → X} (Φ : FormData O w) [Group Γ] [TopologicalSpace Γ] {rbar : Γ →* Matrix ι ι (ResidueField O)}
    (r0 : Γ →* Matrix ι ι O) {A S : Type} [CommRing A] [Algebra O A] [IsCO O A] [CommRing S] [Algebra O S]
    [IsCO O S] (f : A →ₐ[O] S) (r : Lift O rbar A) (s : Γ) :
    (r.hom s * (r0 s⁻¹).map (algebraMap O A)).map f = (r.map f).hom s * (r0 s⁻¹).map (algebraMap O S) := by
  ext a b
  simp [Matrix.mul_apply]

private theorem loc_map {O ι X Γ : Type} [CommRing O] [IsLocalRing O] [Fintype ι] [DecidableEq ι] [AddCommGroup X]
    {w : ι → X} {Φ : FormData O w} [Group Γ] [TopologicalSpace Γ] {rbar : Γ →* Matrix ι ι (ResidueField O)}
    {r0 : Γ →* Matrix ι ι O} {N : Subgroup Γ} {L : Cond O rbar} (hL : Φ.IsLocCond r0 N L) {A S B : Type} [CommRing A]
    [Algebra O A] [IsCO O A] [CommRing S] [Algebra O S] [IsCO O S] [CommRing B] [Algebra O B] [IsCO O B]
    (φ : A →ₐ[O] S) (hφ : Function.Injective φ) (q : A →ₐ[O] B) (r : Lift O rbar A) (hr : Φ.InH r0 A r)
    (h : L S (r.map φ)) : L B (r.map q) := by
  obtain ⟨I, hI⟩ := hL.closed A r hr
  have hS := (hI S φ).mp h
  refine (hI B q).mpr fun x hx => ?_
  have hx0 : x = 0 := hφ (by rw [hS x hx, map_zero])
  rw [hx0, map_zero]

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Alg.loc_graded :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (rbar : Γ →* Matrix ι ι (ResidueField O)) (r0 : Lift O rbar O) (hbar : Φ.Normalises rbar), Φ.Normalises r0.hom → ∀ (N : Subgroup Γ) (L : Cond O rbar), Φ.IsLocCond r0.hom N L →
      ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (p : R →ₐ[O] R'), Function.Surjective p → maximalIdeal R * RingHom.ker p = ⊥ → ∀ (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → IsHomog O W.wt (RingHom.ker (p.comp W.π)) →
      ∀ r' : Lift O rbar R', Φ.InH r0.hom R' r' → L R' r' → (∀ s a b, r'.hom s a b ∈ (W.part (w a - w b)).map p.toLinearMap) →
      ∃ r : Lift O rbar R, Φ.InH r0.hom R r ∧ L R r ∧ r.map p = r' ∧ ∀ s a b, r.hom s a b ∈ W.part (w a - w b) := by
  intro O _ _ _ _ ι X _ _ _ _ _ w Φ _ Γ _ _ _ rbar r0 _ hnorm N L hL R _ _ _ R' _ _ _ p hps hpk W hz hW
    r' hr' hLr' hgr
  classical
  obtain ⟨r₁, hr₁, hLr₁, hr₁p⟩ := hL.lift R R' p hps hpk r' hr' hLr'
  have hy : ∀ ab : ι × ι, ∃ y : Γ → R, AdicCont (maximalIdeal R) y ∧
      (∀ g, y g ∈ W.part (w ab.1 - w ab.2)) ∧ ∀ g, p (y g) = r'.hom g ab.1 ab.2 :=
    fun ab => cont_section O X R R' p hps hpk W hz Γ (w ab.1 - w ab.2) (fun g => r'.hom g ab.1 ab.2)
      (r'.cont ab.1 ab.2) (fun g => hgr g ab.1 ab.2)
  choose y hyc hyp hyl using hy
  obtain ⟨S, _, _, _, A, _, _, _, T, c, φ, q, i, hT, hφ, hqi, hφi, hz'⟩ :=
    split_data O X R R' (ι × ι) (fun ab => w ab.1 - w ab.2) p hpk W hz hW
  choose Z hZφ hZq hZp using hz'
  let d : ι × ι → Γ → R := fun ab g => r₁.hom g ab.1 ab.2 - y ab g
  have hdk : ∀ ab g, p (d ab g) = 0 := by
    intro ab g
    have h1 : p (r₁.hom g ab.1 ab.2) = r'.hom g ab.1 ab.2 := by
      rw [← hr₁p, Lift.map_hom]
    simp only [d, map_sub, hyl, h1, sub_self]
  let M : Γ → Matrix ι ι A := fun g =>
    Matrix.of fun a b => i (y (a, b) g) + Z (a, b) (d (a, b) g) (hdk (a, b) g)
  let E : Γ → Matrix ι ι S := fun g =>
    Matrix.of fun a b => (T (Multiplicative.ofAdd (w a - w b)) : S) * c (r₁.hom g a b)
  have hME : ∀ g, (M g).map φ = E g := by
    intro g
    ext a b
    simp only [M, E, Matrix.map_apply, Matrix.of_apply, map_add]
    rw [hφi _ _ (hyp (a, b) g), hZφ, ← mul_add, ← map_add]
    congr 2
    simp [d]
  have hT0 : ∀ a b c' : ι, (T (Multiplicative.ofAdd (w a - w c')) : S) *
      T (Multiplicative.ofAdd (w c' - w b)) = T (Multiplicative.ofAdd (w a - w b)) := by
    intro a b c'
    rw [← Units.val_mul, ← map_mul, ← ofAdd_add]
    congr 3
    abel
  have hE1 : E 1 = 1 := by
    ext a b
    simp only [E, Matrix.of_apply, map_one, Matrix.one_apply]
    split_ifs with hab
    · subst hab
      simp
    · simp
  have hEm : ∀ g h, E (g * h) = E g * E h := by
    intro g h
    ext a b
    simp only [E, Matrix.of_apply, Matrix.mul_apply]
    rw [map_mul, Matrix.mul_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [map_mul, ← hT0 a b c']
    ring
  have hinj : ∀ P Q : Matrix ι ι A, P.map φ = Q.map φ → P = Q := fun P Q h => by
    ext a b
    exact hφ (congrFun (congrFun h a) b)
  have hmap1 : (1 : Matrix ι ι A).map φ = 1 := map_one φ.mapMatrix
  have hmapm : ∀ P Q : Matrix ι ι A, (P * Q).map φ = P.map φ * Q.map φ :=
    fun P Q => map_mul φ.mapMatrix P Q
  let rAh : Γ →* Matrix ι ι A :=
    { toFun := M
      map_one' := hinj _ _ (by rw [hME, hE1, hmap1])
      map_mul' := fun g h => hinj _ _ (by rw [hmapm, hME, hME, hME, hEm]) }
  have hdlc : ∀ ab, IsLocallyConstant (d ab) := fun ab =>
    lc_of_cont R Γ (RingHom.ker p) hpk (fun g => r₁.hom g ab.1 ab.2) (y ab) (r₁.cont ab.1 ab.2) (hyc ab)
      (fun g => RingHom.mem_ker.mpr (hdk ab g))
  have hZeq : ∀ ab u v (hu : p u = 0) (hv : p v = 0), u = v → Z ab u hu = Z ab v hv := by
    rintro ab u v hu hv rfl
    rfl
  have hZlc : ∀ ab, IsLocallyConstant fun g => Z ab (d ab g) (hdk ab g) := by
    intro ab
    rw [IsLocallyConstant.iff_exists_open]
    intro g
    obtain ⟨U, hU, hgU, hUc⟩ := (IsLocallyConstant.iff_exists_open _).mp (hdlc ab) g
    exact ⟨U, hU, hgU, fun g' hg' => hZeq _ _ _ _ _ (hUc g' hg')⟩
  have hcont : ∀ a b, AdicCont (maximalIdeal A) fun g => rAh g a b := by
    intro a b N'
    have h1 := cont_map i (y (a, b)) (hyc (a, b)) N'
    have h2 := (hZlc (a, b)).comp (Ideal.Quotient.mk (maximalIdeal A ^ N'))
    have hfun : (fun g => Ideal.Quotient.mk (maximalIdeal A ^ N') (rAh g a b)) = fun g =>
        Ideal.Quotient.mk (maximalIdeal A ^ N') (i (y (a, b) g)) +
          Ideal.Quotient.mk (maximalIdeal A ^ N') (Z (a, b) (d (a, b) g) (hdk (a, b) g)) := by
      funext g
      rw [← map_add]
      rfl
    rw [hfun]
    exact h1.comp₂ h2 (· + ·)
  have hred : ∀ g a b, res O A (rAh g a b) = rbar g a b := by
    intro g a b
    rw [← res_map φ]
    have h1 : φ (rAh g a b) = E g a b := congrFun (congrFun (hME g) a) b
    rw [h1]
    simp only [E, Matrix.of_apply, map_mul, hT, one_mul, res_map, r₁.red]
  let rA : Lift O rbar A := ⟨rAh, hcont, hred⟩
  have hφE : ∀ g a b, (rA.map φ).hom g a b =
      (T (Multiplicative.ofAdd (w a - w b)) : S) * (r₁.map c).hom g a b := by
    intro g a b
    rw [Lift.map_hom, Lift.map_hom]
    exact congrFun (congrFun (hME g) a) b
  have hInHc : Φ.InH r0.hom S (r₁.map c) := by
    intro s
    rw [← inH_map Φ r0.hom c r₁ s]
    exact (hh_group O ι X w Φ R).2.2.2.1 S c _ (hr₁ s)
  obtain ⟨I0, hI0⟩ := hL.closed R r₁ hr₁
  have hid : Lift.map (AlgHom.id O R) r₁ = r₁ :=
    Lift.ext (MonoidHom.ext fun g => Matrix.ext fun a b => by rw [Lift.map_hom]; rfl)
  have hI0z : ∀ x ∈ I0, x = 0 := (hI0 R (AlgHom.id O R)).mp (by rw [hid]; exact hLr₁)
  have hLc : L S (r₁.map c) := (hI0 S c).mpr fun x hx => by rw [hI0z x hx, map_zero]
  have hLA : L S (rA.map φ) := hL.torus S (r₁.map c) (rA.map φ) T hInHc hT (fun g a b => hφE g a b) hLc
  have hInHA : Φ.InH r0.hom A rA := by
    intro s
    apply hh_of_inj Φ φ hφ
    rw [inH_map Φ r0.hom φ rA s]
    have heq : (rA.map φ).hom s * (r0.hom s⁻¹).map (algebraMap O S) = Matrix.of fun a b =>
        (T (Multiplicative.ofAdd (w a - w b)) : S) *
          ((r₁.map c).hom s * (r0.hom s⁻¹).map (algebraMap O S)) a b := by
      ext a b
      simp only [Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c' _ => ?_
      by_cases hcb : w c' = w b
      · rw [hφE, hcb]
        ring
      · have h0 : r0.hom s⁻¹ c' b = 0 := hnorm.2.2 s⁻¹ c' b hcb
        simp [Matrix.map_apply, h0]
    rw [heq]
    exact (hh_group O ι X w Φ S).2.2.2.2.2 T _ (hInHc s)
  refine ⟨rA.map q, ?_, loc_map hL φ hφ q rA hInHA hLA, ?_, ?_⟩
  · intro s
    rw [← inH_map Φ r0.hom q rA s]
    exact (hh_group O ι X w Φ A).2.2.2.1 R q _ (hInHA s)
  · refine Lift.ext (MonoidHom.ext fun g => Matrix.ext fun a b => ?_)
    rw [Lift.map_hom, Lift.map_hom]
    change p (q (i (y (a, b) g) + Z (a, b) (d (a, b) g) (hdk (a, b) g))) = r'.hom g a b
    rw [map_add, hqi, map_add, hZp, add_zero, hyl]
  · intro s a b
    rw [Lift.map_hom]
    change q (i (y (a, b) s) + Z (a, b) (d (a, b) s) (hdk (a, b) s)) ∈ W.part (w a - w b)
    rw [map_add, hqi]
    have hq : q (Z (a, b) (d (a, b) s) (hdk (a, b) s)) ∈ W.part (w a - w b) := hZq (a, b) _ _
    exact (W.part (w a - w b)).add_mem (hyp (a, b) s) hq
