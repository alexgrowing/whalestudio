import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.FixBdQZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.DdSumZero

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private def ddBaseRingHom (X : Type) [CommRing X] (g : ℕ) : DD X g →+* X where
  toFun := DD.a
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

private def ddEpsCoordAddHom (X : Type) [CommRing X] (g : ℕ) (j : Fin g) : DD X g →+ X where
  toFun y := y.ep j
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem commuting_matrix_offdiag_zero {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n)
    (Z : Matrix (Fin n) (Fin n) x.A) (hZ : ∀ g, mat x.ρ g * Z = Z * mat x.ρ g) (i j : Fin n) (hij : i ≠ j) :
    Z i j = 0 := by
  have hmem : Matrix.single j j (1 : x.A) ∈ Ev (PowerSeries x.K) (PowerSeries x.K) n x.a := by
    show ∀ i' j' : Fin n, _
    intro i' j'
    refine ⟨fun _ => Submodule.mem_top, fun h => ?_⟩
    rw [Submodule.mem_bot, Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact h Iff.rfl
  obtain ⟨s, hs⟩ := x.span _ hmem
  have hcomm : ∀ M ∈ Submodule.span (PowerSeries x.K) (⇑(mat x.ρ) '' ↑F.G'), Z * M = M * Z := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem M hM =>
      obtain ⟨g, -, rfl⟩ := hM
      exact (hZ g).symm
    | zero => simp
    | add M N _ _ hM hN => rw [Matrix.mul_add, Matrix.add_mul, hM, hN]
    | smul c M _ hM => rw [Matrix.mul_smul, Matrix.smul_mul, hM]
  have h1 := hcomm _ hs
  rw [Matrix.mul_smul, Matrix.smul_mul] at h1
  have h2 := congrFun (congrFun h1 i) j
  simpa [hij, PowerSeries.X_ne_zero] using h2

private theorem skew_commuting_matrix_zero {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (hl : l ≠ 2)
    (Z : Matrix (Fin n) (Fin n) x.A) (hZ : ∀ g, mat x.ρ g * Z = Z * mat x.ρ g) (ht : Zᵀ = -Z) : Z = 0 := by
  have h2u : IsUnit (2 : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => ?_)
    have h' : ‖((2 : ℤ) : ℤ_[l])‖ < 1 := by simpa using h
    rw [PadicInt.norm_int_lt_one_iff_dvd] at h'
    have hl' : l ∣ 2 := by exact_mod_cast h'
    exact hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hl')
  have hu : IsUnit (2 : x.A) := by
    have := h2u.map ((algebraMap x.K (PowerSeries x.K)).comp (algebraMap ℤ_[l] x.K))
    rwa [map_ofNat] at this
  refine Matrix.ext fun i j => ?_
  by_cases hij : i = j
  · subst hij
    have h1 := congrFun (congrFun ht i) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h1
    have h2 : (2 : x.A) * Z i i = 0 := by linear_combination h1
    simpa using hu.mul_right_eq_zero.mp h2
  · exact commuting_matrix_offdiag_zero x Z hZ i j hij

private theorem rho1_map_ddBaseRingHom_eq_mat_rho {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (g : F.G₀) :
    (k.ρ1 x.A g).map (ddBaseRingHom x.A k.g) = mat x.ρ g := by
  have ha : ∀ y, ddBaseRingHom x.A k.g y = y.a := fun _ => rfl
  have hb : ∀ y : x.A, (algebraMap x.A (DD x.A k.g) y).a = y := fun _ => rfl
  have h0 : (0 : DD x.A k.g).a = 0 := rfl
  rw [Kap.ρ1, Matrix.map_mul]
  refine Matrix.ext fun i j => ?_
  simp [ha, hb, h0, DD.epM, NP.ρX, Matrix.mul_apply, Matrix.one_apply, apply_ite DD.a, DD.one_a]

private theorem map_ep_mul_eq_leibniz {X : Type} [CommRing X] {g n : ℕ} (M N : Matrix (Fin n) (Fin n) (DD X g)) (j : Fin g) :
    (M * N).map (fun y => y.ep j) = M.map DD.a * N.map (fun y => y.ep j) + M.map (fun y => y.ep j) * N.map DD.a := by
  refine Matrix.ext fun r c => ?_
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  rw [show (∑ t, M r t * N t c).ep j = ∑ t, (M r t * N t c).ep j from map_sum (ddEpsCoordAddHom X g j) _ _]
  simp [DD.mul_ep]

private theorem map_a_mul_eq_map_a_mul_map_a {X : Type} [CommRing X] {g n : ℕ} (M N : Matrix (Fin n) (Fin n) (DD X g)) :
    (M * N).map DD.a = M.map DD.a * N.map DD.a :=
  Matrix.map_mul (f := ddBaseRingHom X g)

private theorem skew_invariant_M1_zero {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (hl : l ≠ 2)
    (Z : Matrix (Fin n) (Fin n) (DD x.A k.g)) (hm : Z ∈ k.M1 x.A) (ht : Zᵀ = -Z)
    (hZ : ∀ g, k.ρ1 x.A g * Z * k.ρ1 x.A g⁻¹ = Z) : Z = 0 := by
  have hA0 : ∀ g : F.G₀, (k.ρ1 x.A g).map DD.a = mat x.ρ g := fun g => rho1_map_ddBaseRingHom_eq_mat_rho k g
  have hinv : ∀ g : F.G₀, mat x.ρ g⁻¹ * mat x.ρ g = 1 := fun g => by
    rw [← map_mul, inv_mul_cancel, map_one]
  have comm_of : ∀ W : Matrix (Fin n) (Fin n) x.A, (∀ g, mat x.ρ g * W * mat x.ρ g⁻¹ = W) →
      ∀ g, mat x.ρ g * W = W * mat x.ρ g := by
    intro W hW g
    calc mat x.ρ g * W = mat x.ρ g * W * (mat x.ρ g⁻¹ * mat x.ρ g) := by rw [hinv, Matrix.mul_one]
      _ = W * mat x.ρ g := by rw [← Matrix.mul_assoc, hW]
  have hA : Z.map DD.a = 0 := by
    apply skew_commuting_matrix_zero x hl
    · apply comm_of
      intro g
      have := congrArg (fun M => M.map DD.a) (hZ g)
      simpa only [map_a_mul_eq_map_a_mul_map_a, hA0] using this
    · refine Matrix.ext fun r c => ?_
      have h1 := congrFun (congrFun ht r) c
      simp only [Matrix.transpose_apply, Matrix.neg_apply] at h1
      simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.map_apply, h1, DD.neg_a]
  have hE : ∀ t : Fin k.g, Z.map (fun y => y.ep t) = 0 := by
    intro t
    apply skew_commuting_matrix_zero x hl
    · apply comm_of
      intro g
      have := congrArg (fun M => M.map (fun y => y.ep t)) (hZ g)
      simp only [map_ep_mul_eq_leibniz, map_a_mul_eq_map_a_mul_map_a, hA0, hA, Matrix.mul_zero, Matrix.zero_mul, zero_add,
        add_zero] at this
      exact this
    · refine Matrix.ext fun r c => ?_
      have h1 := congrFun (congrFun ht r) c
      simp only [Matrix.transpose_apply, Matrix.neg_apply] at h1
      simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.map_apply, h1, DD.neg_ep]
  refine Matrix.ext fun r c => ?_
  have hm' : (Z r c).ep' = 0 ∧ (Z r c).eta = 0 := by
    obtain ⟨h1, h2⟩ := (show ∀ i j : Fin n, _ from hm) r c
    by_cases hb : (↑r < x.a ↔ ↑c < x.a)
    · obtain ⟨-, -, h3, h4⟩ := h1 hb
      exact ⟨h3 rfl, h4 rfl⟩
    · obtain ⟨-, -, h3, h4⟩ := h2 hb
      exact ⟨h3 rfl, h4 rfl⟩
  rw [Matrix.zero_apply]
  refine DD.ext ?_ (funext fun t => ?_) ?_ ?_
  · simpa using congrFun (congrFun hA r) c
  · simpa using congrFun (congrFun (hE t) r) c
  · exact hm'.1
  · exact hm'.2

private def ddMapRingHom {A X : Type} [CommRing A] [CommRing X] (g : ℕ) (f : A →+* X) : DD A g →+* DD X g where
  toFun y := ⟨f y.a, fun j => f (y.ep j), fun j => f (y.ep' j), f y.eta⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' _ _ := by ext <;> simp
  map_mul' _ _ := by ext <;> simp

private theorem rho1_map_ddMapRingHom_eq_rho1 {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x)
    (X : Type) [CommRing X] [Algebra x.A X] (g : F.G₀) :
    (k.ρ1 x.A g).map (ddMapRingHom k.g (algebraMap x.A X)) = k.ρ1 X g := by
  have hr : ∀ y, ddMapRingHom k.g (algebraMap x.A X) y = ⟨algebraMap x.A X y.a, fun j => algebraMap x.A X (y.ep j), fun j => algebraMap x.A X (y.ep' j), algebraMap x.A X y.eta⟩ := fun _ => rfl
  have hb : ∀ (Y : Type) [CommRing Y] [Algebra x.A Y] (y : x.A), algebraMap x.A (DD Y k.g) y = ⟨algebraMap x.A Y y, 0, 0, 0⟩ := fun _ _ _ _ => rfl
  rw [Kap.ρ1, Kap.ρ1, Matrix.map_mul]
  congr 1
  · refine Matrix.ext fun i j => ?_
    rw [Matrix.map_apply]
    by_cases hij : i = j
    · subst hij
      refine DD.ext ?_ (funext fun t => ?_) (funext fun t => ?_) ?_ <;> simp [hr, DD.epM, DD.add_ep, DD.one_ep, DD.add_ep', DD.one_ep', DD.add_a, DD.add_eta, DD.one_eta, DD.one_a]
    · refine DD.ext ?_ (funext fun t => ?_) (funext fun t => ?_) ?_ <;> simp [hr, DD.epM, hij, DD.zero_ep, DD.zero_a]
  · refine Matrix.ext fun i j => ?_
    refine DD.ext ?_ (funext fun t => ?_) (funext fun t => ?_) ?_ <;> simp [hr, hb, NP.ρX]

theorem UpperTheory.V.Pa.h0G :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x), l ≠ 2 → ∃ C : ℕ, ∀ (m : ℕ), {Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g) | Y ∈ k.M1 (x.Am m) ∧ Yᵀ = -Y ∧ ∀ g : G0.G₀, k.ρ1 (x.Am m) g * Y * k.ρ1 (x.Am m) g⁻¹ = Y}.ncard ≤ Nat.card x.K ^ C := by
  intro l _ L G G0 h n x k hl
  obtain ⟨C, hC⟩ := fixBd l G0.frame n x k (k.M1 x.A) true false false false false true false false
    G0.G₀ (fun _ => 1) (fun s => k.ρ1 x.A s) (fun s => k.ρ1 x.A s⁻¹) true rfl
  refine ⟨C, fun m => ?_⟩
  have hfin : ∀ W : Submodule x.A (Matrix (Fin n) (Fin n) (DD x.A k.g)), W = ⊥ →
      Nat.card x.K ^ (m * Module.finrank x.A W + C) = Nat.card x.K ^ C := by
    rintro W rfl
    simp
  refine le_trans (le_of_eq ?_) ((hC m).trans (le_of_eq (hfin _ ?_)))
  · clear hC hfin
    congr 1
    ext Y
    have hred : ∀ s : G0.G₀, ((k.ρ1 x.A s).map fun y : DD x.A k.g =>
        (⟨(algebraMap x.A (x.Am m)) y.a, fun j => (algebraMap x.A (x.Am m)) (y.ep j),
          fun j => (algebraMap x.A (x.Am m)) (y.ep' j), (algebraMap x.A (x.Am m)) y.eta⟩ : DD (x.Am m) k.g))
        = k.ρ1 (x.Am m) s :=
      fun s => rho1_map_ddMapRingHom_eq_rho1 k (x.Am m) s
    simp only [Set.mem_setOf_eq, one_smul, forall_const, hred]
    exact Iff.rfl
  · rw [eq_bot_iff]
    intro Z hZ
    rw [Submodule.mem_bot]
    simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, ↓reduceIte] at hZ
    obtain ⟨⟨hm, ht⟩, hfix⟩ := hZ
    apply skew_invariant_M1_zero k hl Z hm
    · simpa [add_eq_zero_iff_eq_neg] using ht
    · intro g
      have := hfix g
      simpa [sub_eq_zero, Matrix.mul_assoc] using this
