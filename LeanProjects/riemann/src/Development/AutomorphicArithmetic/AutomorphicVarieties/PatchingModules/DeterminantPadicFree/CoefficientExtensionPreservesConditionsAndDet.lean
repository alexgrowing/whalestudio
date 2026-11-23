import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ExtFree

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem l_zero {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Finite K] (f : ℤ_[l] →+* K) : (l : K) = 0 := by
  by_contra hne
  have hp : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  have hlp : ringChar K ≠ l := by
    intro h
    apply hne
    rw [← h]
    exact ringChar.Nat.cast_ringChar
  have hcop : l.Coprime (ringChar K) := (Nat.coprime_primes (Fact.out) hp).mpr hlp.symm
  have hu : IsUnit ((ringChar K : ℕ) : ℤ_[l]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hcop)
  have hu' := hu.map f
  rw [map_natCast, ringChar.Nat.cast_ringChar] at hu'
  exact not_isUnit_zero hu'

private theorem hom_uniq {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (f f' : ℤ_[l] →+* R) (h : (l : R) = 0) :
    f = f' := by
  ext x
  have hx := PadicInt.sub_zmodRepr_mem x
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hx
  obtain ⟨y, hy⟩ := hx
  have hx' : x = (PadicInt.zmodRepr x : ℤ_[l]) + y * l := by rw [hy]; ring
  rw [hx', map_add, map_add, map_mul, map_mul, map_natCast, map_natCast, map_natCast, map_natCast, h]
  simp

private theorem localization_quotient_separated_dvd {A K L : Type} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L] (g : A →+* L)
    (hi : Function.Injective g) (P : Polynomial A) (hs : (P.map (algebraMap A K)).Separable) :
    (P.map g).Separable := by
  have hP : P.map g = (P.map (algebraMap A K)).map (IsFractionRing.lift hi) := by
    rw [Polynomial.map_map]
    congr 1
    ext a
    simp [IsFractionRing.lift_algebraMap]
  rw [hP]
  exact hs.map

private theorem sep_map {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] (j : A →+* B)
    (hinj : Function.Injective j) (P : Polynomial A) (hs : (P.map (algebraMap A (FractionRing A))).Separable) :
    ((P.map j).map (algebraMap B (FractionRing B))).Separable := by
  rw [Polynomial.map_map]
  exact localization_quotient_separated_dvd (K := FractionRing A) ((algebraMap B (FractionRing B)).comp j)
    ((IsFractionRing.injective B (FractionRing B)).comp hinj) P hs

theorem UpperTheory.V.Pa.Det.coefficientExtension_preserves_conditions_and_det :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x x' : NP F n) (j : x.A →+* x'.A), x.Ext x' j → (∀ D : Subgroup F.G₀, x.N4 D → x'.N4 D) ∧ (x.N3 → x'.N3) ∧ GDet.ofRep (mat x'.ρ) = (GDet.ofRep (mat x.ρ)).map j := by
  intro l _ F n x x' j hE
  obtain ⟨hinj, hloc, hfin, hρ, ha, hψ⟩ := hE
  have hmat : ∀ g, mat x'.ρ g = (mat x.ρ g).map j := by
    intro g
    rw [hρ]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro Dg h4 Z hZ
    obtain ⟨m, b, p, hm, hsum, hlin, hdual, -, -⟩ := UpperTheory.V.Pa.Det.extFree j hinj hloc hfin
    have h0 : ((l : ℕ) : x'.A) = 0 := by
      simpa using congrArg (PowerSeries.C (R := x'.K)) (l_zero (algebraMap ℤ_[l] x'.K))
    have hj : algebraMap ℤ_[l] x'.A = j.comp (algebraMap ℤ_[l] x.A) := hom_uniq _ _ h0
    have heps : ∀ g, ((F.eps ℤ_[l] x'.A g : x'.Aˣ) : x'.A) = j (F.eps ℤ_[l] x.A g : x.Aˣ) := by
      intro g
      simp [GFrame.eps, pushCh, hj]
    have hZi : ∀ i, Z.map (p i) = 0 := by
      intro i
      apply h4
      intro g hg
      have lhs : ∀ (e : x.A) (M : Matrix (Fin n) (Fin n) x.A) a c,
          p i (j e * ∑ k, j (M a k) * Z k c) = e * ∑ k, M a k * p i (Z k c) := by
        intro e M a c
        rw [Finset.mul_sum, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← mul_assoc, ← map_mul, hlin, mul_assoc]
      have rhs : ∀ (M : Matrix (Fin n) (Fin n) x.A) a c,
          p i (∑ k, Z a k * j (M k c)) = ∑ k, p i (Z a k) * M k c := by
        intro M a c
        rw [map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_comm, hlin, mul_comm]
      ext a c
      have hac := congrFun (congrFun (hZ g hg) a) c
      simp only [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, hmat, Matrix.map_apply, heps] at hac
      simp only [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, Matrix.map_apply]
      rw [← lhs, ← rhs, hac]
    ext a c
    have hz : ∀ i, p i (Z a c) = 0 := by
      intro i
      have h1 := congrFun (congrFun (hZi i) a) c
      simpa only [Matrix.map_apply, Matrix.zero_apply] using h1
    rw [hsum (Z a c), Matrix.zero_apply]
    simp [hz]
  · intro h3 U hU hne
    obtain ⟨σ, hσ, hsep⟩ := h3 U hU hne
    refine ⟨σ, hσ, ?_⟩
    rw [hmat, Matrix.charpoly_map]
    exact sep_map j hinj _ hsep
  · apply GDet.ext
    intro B _ _ y
    show Matrix.det _ = Matrix.det _
    congr 1
    simp only [MonoidHom.coe_coe, AlgHom.coe_toRingHom, GDet.repAlg]
    congr 2
    apply congrArg
    ext g a b
    simp [hmat]
    try rfl
