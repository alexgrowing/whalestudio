import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.OrbitVanishingLocal
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.UZGen

noncomputable section

open IsLocalRing Formalism.MainNotions.V.Pf.V2.Calc

namespace UpperTheory.V.Alg.M

section Rees

variable {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ} (N : Fin k → Submodule B A)

def lat (m : Fin k →₀ ℕ) : Submodule B A := ∏ i, N i ^ m i

theorem lat_add (m m' : Fin k →₀ ℕ) : lat N (m + m') = lat N m * lat N m' := by
  simp [lat, pow_add, Finset.prod_mul_distrib]

theorem lat_zero : lat N 0 = 1 := by simp [lat]

theorem lat_single (i : Fin k) : lat N (Finsupp.single i 1) = N i := by
  rw [lat, Finset.prod_eq_single i] <;> simp +contextual [Finsupp.single_apply, eq_comm]

def rees : Subalgebra B (MvPolynomial (Fin k) A) where
  carrier := {p | ∀ m, MvPolynomial.coeff m p ∈ lat N m}
  mul_mem' {p q} hp hq m := by
    classical
    rw [MvPolynomial.coeff_mul]
    refine Submodule.sum_mem _ fun c hc => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hc, lat_add]
    exact Submodule.mul_mem_mul (hp _) (hq _)
  add_mem' {p q} hp hq m := by rw [MvPolynomial.coeff_add]; exact add_mem (hp m) (hq m)
  algebraMap_mem' b m := by
    classical
    rw [MvPolynomial.algebraMap_apply, MvPolynomial.coeff_C]
    split_ifs with h
    · rw [← h, lat_zero]; exact Submodule.algebraMap_mem b
    · exact zero_mem _

def mono (m : Fin k →₀ ℕ) (f : A) (hf : f ∈ lat N m) : rees N :=
  ⟨MvPolynomial.monomial m f, fun n => by
    classical
    rw [MvPolynomial.coeff_monomial]
    split_ifs with h
    · exact h ▸ hf
    · exact zero_mem _⟩

def sec (i : Fin k) (f : A) (hf : f ∈ N i) : rees N := mono N (Finsupp.single i 1) f ((lat_single N i).symm ▸ hf)

def toDeg (m : Fin k →₀ ℕ) : Deg k := fun i => (m i : ℤ)

theorem toDeg_add (m m' : Fin k →₀ ℕ) : toDeg (m + m') = toDeg m + toDeg m' := by
  funext i; simp [toDeg]

theorem toDeg_injective : Function.Injective (toDeg (k := k)) := fun m m' h =>
  Finsupp.ext fun i => Int.ofNat_inj.1 (congrFun h i)

def reesGr (d : Deg k) : Submodule B (rees N) where
  carrier := {p | ∀ m, toDeg m ≠ d → MvPolynomial.coeff m p.1 = 0}
  add_mem' {p q} hp hq m hm := by
    show MvPolynomial.coeff m (p.1 + q.1) = 0
    rw [MvPolynomial.coeff_add, hp m hm, hq m hm, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' c p hp m hm := by
    show MvPolynomial.coeff m (c • p.1) = 0
    rw [MvPolynomial.coeff_smul, hp m hm, smul_zero]

theorem mono_mem (m : Fin k →₀ ℕ) (f : A) (hf : f ∈ lat N m) : mono N m f hf ∈ reesGr N (toDeg m) := fun n hn => by
  classical
  show MvPolynomial.coeff n (MvPolynomial.monomial m f) = 0
  rw [MvPolynomial.coeff_monomial, if_neg]
  rintro rfl
  exact hn rfl

theorem sec_mem (i : Fin k) (f : A) (hf : f ∈ N i) : sec N i f hf ∈ reesGr N (e i) := by
  have : e i = toDeg (Finsupp.single i 1) := by
    funext j; simp [e, toDeg, Pi.single_apply, Finsupp.single_apply, eq_comm]
  rw [this]; exact mono_mem N _ _ _

instance : SetLike.GradedMonoid (reesGr N) where
  one_mem m hm := by
    classical
    show MvPolynomial.coeff m 1 = 0
    rw [MvPolynomial.coeff_one, if_neg]
    rintro rfl
    exact hm rfl
  mul_mem d d' p q hp hq m hm := by
    classical
    show MvPolynomial.coeff m (p.1 * q.1) = 0
    rw [MvPolynomial.coeff_mul]
    refine Finset.sum_eq_zero fun c hc => ?_
    by_cases h1 : toDeg c.1 = d
    · rw [hq c.2, mul_zero]
      intro h2
      exact hm (by rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hc, toDeg_add, h1, h2])
    · rw [hp _ h1, zero_mul]

theorem eq_sum_mono (p : rees N) : p = ∑ m ∈ p.1.support, mono N m (MvPolynomial.coeff m p.1) (p.2 m) := by
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finset_sum]
  exact p.1.as_sum

theorem rees_internal : DirectSum.IsInternal (reesGr N) := by
  classical
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · intro d
    rw [Submodule.disjoint_def]
    intro p hp hq
    have key : ∀ m, toDeg m = d → MvPolynomial.coeff m p.1 = 0 := by
      intro m hm
      refine Submodule.iSup_induction (motive := fun q : rees N => MvPolynomial.coeff m q.1 = 0) _ hq ?_ rfl ?_
      · intro j q hq
        by_cases hj : j = d
        · have : q = 0 := by simpa [hj] using hq
          rw [this]; rfl
        · have hq' : q ∈ reesGr N j := by simpa [hj] using hq
          exact hq' m (by rw [hm]; exact Ne.symm hj)
      · intro a b ha hb
        show MvPolynomial.coeff m (a.1 + b.1) = 0
        rw [MvPolynomial.coeff_add, ha, hb, add_zero]
    apply Subtype.ext
    ext m
    by_cases hm : toDeg m = d
    · exact key m hm
    · exact hp m hm
  · rw [eq_top_iff]
    intro p _
    rw [eq_sum_mono N p]
    exact Submodule.sum_mem _ fun m _ => Submodule.mem_iSup_of_mem _ (mono_mem N m _ _)

instance : GradedAlgebra (reesGr N) :=
  { (inferInstance : SetLike.GradedMonoid (reesGr N)), (rees_internal N).chooseDecomposition with }

def coefIdeal (J : Ideal A) : Ideal (rees N) where
  carrier := {p | ∀ m, MvPolynomial.coeff m p.1 ∈ J}
  add_mem' {p q} hp hq m := by
    show MvPolynomial.coeff m (p.1 + q.1) ∈ J
    rw [MvPolynomial.coeff_add]; exact add_mem (hp m) (hq m)
  zero_mem' _ := J.zero_mem
  smul_mem' c p hp m := by
    classical
    show MvPolynomial.coeff m (c.1 * p.1) ∈ J
    rw [MvPolynomial.coeff_mul]
    exact Submodule.sum_mem _ fun c _ => J.mul_mem_left _ (hp _)

end Rees

def dif {k : ℕ} : List (Deg k) → (Deg k → ℤ) → Deg k → ℤ
  | [], h, m => h m
  | d :: ds, h, m => dif ds h m - dif ds h (m - d)

def hilb {B R : Type} [CommRing B] [CommRing R] [Algebra B R] {k : ℕ} (F : GMod B R k) (m : Deg k) : ℤ :=
  ((Module.length B (F.gr m)).toNat : ℤ)

def locLen {O B K : Type} [CommRing O] [CommRing B] [Algebra O B] [Field K] [Algebra O K] (σ : B →ₐ[O] K)
    (M : Type) [AddCommGroup M] [Module B M] : ℕ∞ :=
  haveI : (RingHom.ker σ).IsPrime := RingHom.ker_isPrime σ
  Module.length (Localization.AtPrime (RingHom.ker σ)) (LocalizedModule (RingHom.ker σ).primeCompl M)

def theta {B : Type} [CommRing B] (β : B) (M : Type) [AddCommGroup M] [Module B M] : ℤ :=
  ((Module.length B (M ⧸ LinearMap.range (LinearMap.lsmul B M β))).toNat : ℤ) -
    ((Module.length B (LinearMap.ker (LinearMap.lsmul B M β))).toNat : ℤ)

section Graded

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]

def oz (j : ℤ) : Submodule (𝒜 0) A where
  carrier := 𝒜 j
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' c f hf := by
    have := SetLike.GradedMul.mul_mem c.2 hf
    rwa [zero_add] at this

@[simp] theorem mem_oz {j : ℤ} {f : A} : f ∈ oz 𝒜 j ↔ f ∈ 𝒜 j := Iff.rfl

def aPiece (J : Ideal A) (j : ℤ) : Submodule (𝒜 0) (A ⧸ J) :=
  (oz 𝒜 j).map (Ideal.Quotient.mkₐ (𝒜 0) J).toLinearMap

instance : IsScalarTower O (𝒜 0) A := IsScalarTower.of_algebraMap_eq fun _ => rfl

def res0 {K : Type} [CommRing K] [Algebra O K] (ξ : A →ₐ[O] K) : 𝒜 0 →ₐ[O] K :=
  ξ.comp (IsScalarTower.toAlgHom O (𝒜 0) A)

def mN (F : A) : Fin 3 → Submodule (𝒜 0) A :=
  ![oz 𝒜 (-2), oz 𝒜 2, Submodule.span (𝒜 0) {F ^ 2} ⊔ oz 𝒜 (-2) * oz 𝒜 (-2) * oz 𝒜 2]

def idD : Ideal (𝒜 0) := Ideal.span {b | ∃ f ∈ 𝒜 (-2), ∃ g ∈ 𝒜 2, (b : A) = f * g}

theorem sq_mem_neg {f : A} (hf : f ∈ 𝒜 (-1)) : f ^ 2 ∈ 𝒜 (-2) := by
  rw [sq]; exact SetLike.GradedMul.mul_mem hf hf

theorem sq_mem_pos {f : A} (hf : f ∈ 𝒜 1) : f ^ 2 ∈ 𝒜 2 := by
  rw [sq]; exact SetLike.GradedMul.mul_mem hf hf

variable {𝒜} {x : A →ₐ[O] O} {r s r' s' m : ℕ} (Q : Eqns 𝒜 x r s r' s' m)

abbrev mR : Type := rees (mN 𝒜 (Q.F (Fin.last r)))

abbrev mGr : Deg 3 → Submodule (𝒜 0) (mR Q) := reesGr (mN 𝒜 (Q.F (Fin.last r)))

def tsF : List (Deg 3 × mR Q) := List.ofFn fun i : Fin r => (e 0, sec _ 0 (Q.F i.castSucc ^ 2) (sq_mem_neg 𝒜 (Q.hF _)))

def tsR : List (Deg 3 × mR Q) :=
  (List.ofFn fun i : Fin s => (e 0, sec _ 0 (Q.G i) (Q.hG i))) ++
  (List.ofFn fun i : Fin r' => (e 1, sec _ 1 (Q.E i ^ 2) (sq_mem_pos 𝒜 (Q.hE i)))) ++
  (List.ofFn fun i : Fin s' => (e 1, sec _ 1 (Q.E' i) (Q.hE' i))) ++
  [(e 2, sec _ 2 (Q.F (Fin.last r) ^ 2) (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)))]

def ts : List (Deg 3 × mR Q) := tsF Q ++ tsR Q

def ideal2 : Ideal A :=
  Ideal.span ((Set.range fun i => Q.F i ^ 2) ∪ Set.range Q.G ∪ (Set.range fun i => Q.E i ^ 2) ∪ Set.range Q.E' ∪
    Set.range Q.Z)

abbrev mQ (J : Ideal (mR Q)) : GMod (𝒜 0) (mR Q) 3 := (GMod.self (mGr Q)).quo J

end Graded

def negW {τ : Type} (wt : τ → ℤ) (i : τ) : ℕ := (-wt i).toNat

def posW {τ : Type} (wt : τ → ℤ) (i : τ) : ℕ := (wt i).toNat

def fil (E : Type) [CommRing E] {τ : Type} (wt : τ → ℤ) (n : ℕ) : Submodule E (MvPowerSeries τ E) where
  carrier := {g | ∀ ν, Finsupp.weight (negW wt) ν < n → MvPowerSeries.coeff ν g = 0}
  add_mem' ha hb ν hν := by rw [map_add, ha ν hν, hb ν hν, add_zero]
  zero_mem' _ _ := map_zero _
  smul_mem' c g hg ν hν := by rw [map_smul, hg ν hν, smul_zero]

def cnt {τ : Type} (wt : τ → ℤ) (a b : ℤ) : ℤ :=
  (Nat.card {ν : τ →₀ ℕ // (Finsupp.weight (negW wt) ν : ℤ) = a ∧ (Finsupp.weight (posW wt) ν : ℤ) = b} : ℤ)

structure IsChart0 {O A τ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A]
    (𝒜 : ℤ → Submodule O A) (x : A →ₐ[O] O) (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) : Prop where
  graded : ∀ j, ∀ f ∈ 𝒜 j, φ f ∈ wtPart (FractionRing O) wt j
  const : ∀ f, MvPowerSeries.constantCoeff (φ f) = algebraMap O (FractionRing O) (x f)
  onto : ∀ i, ∃ f : A, MvPowerSeries.coeff (Finsupp.single i 1) (φ f) ≠ 0 ∧
    ∀ i', i' ≠ i → MvPowerSeries.coeff (Finsupp.single i' 1) (φ f) = 0
  wts : ∀ i, wt i = -2 ∨ wt i = -1 ∨ wt i = 1 ∨ wt i = 2

def leadKer {O A τ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] {𝒜 : ℤ → Submodule O A}
    [GradedAlgebra 𝒜] {x : A →ₐ[O] O} {r s r' s' m : ℕ} (Q : Eqns 𝒜 x r s r' s' m) (wt : τ → ℤ)
    (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) : Set (mR Q) :=
  {p | ∀ μ : Fin 3 →₀ ℕ, φ (MvPolynomial.coeff μ p.1) ∈ fil (FractionRing O) wt (2 * μ 0 + 4 * μ 2 + 1)}

end UpperTheory.V.Alg.M
