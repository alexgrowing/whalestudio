import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws

section Mat

variable {R R' : Type} [CommRing R] [CommRing R']

def wM (R : Type) [CommRing R] (pr : Bool) : M4 R :=
  if pr then !![0, 0, -1, 0; 0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 0] else 1

def Par (X : M4 R) : Prop := ∀ i j, lamW j < lamW i → X i j = 0

def Cg (I : Ideal R) (X Y : M4 R) : Prop := ∀ i j, X i j - Y i j ∈ I

theorem adj_mul (X Y : M4 R) : adj (X * Y) = adj Y * adj X := (grp R).1 X Y

theorem adj_adj (X : M4 R) : adj (adj X) = X := (grp R).2.1 X

theorem adj_one : adj (1 : M4 R) = 1 := (grp R).2.2.2.2.1

theorem adj_map (f : R →+* R') (X : M4 R) : adj (X.map f) = (adj X).map f := (grp R).2.2.2.2.2.1 R' f X

theorem gsp_mul {ν ν' : R} {g g' : M4 R} (h : IsGSp ν g) (h' : IsGSp ν' g') : IsGSp (ν * ν') (g * g') :=
  (grp R).2.2.2.2.2.2.2.1 ν ν' g g' h h'

theorem sp_mul {g g' : M4 R} (h : IsGSp 1 g) (h' : IsGSp 1 g') : IsGSp 1 (g * g') := by
  simpa using gsp_mul h h'

theorem sp_adj_mul {g : M4 R} (h : IsGSp 1 g) : adj g * g = 1 := by simpa [IsGSp] using h

theorem sp_mul_adj {g : M4 R} (h : IsGSp 1 g) : g * adj g = 1 := mul_eq_one_comm.1 (sp_adj_mul h)

theorem sp_adj {g : M4 R} (h : IsGSp 1 g) : IsGSp 1 (adj g) := by
  rw [IsGSp, adj_adj, sp_mul_adj h, one_smul]

theorem gsp_conj {ν : R} {m g : M4 R} (hm : IsGSp 1 m) (h : IsGSp ν g) : IsGSp ν (adj m * g * m) := by
  simpa using gsp_mul (gsp_mul (sp_adj hm) h) hm

theorem gsp_map (f : R →+* R') {ν : R} {g : M4 R} (h : IsGSp ν g) : IsGSp (f ν) (g.map f) := by
  rw [IsGSp, adj_map, ← Matrix.map_mul, h]
  ext i j
  by_cases e : i = j <;> simp [e, Matrix.one_apply]

def conjSp {Γ : Type} [Group Γ] {m : M4 R} (hm : IsGSp 1 m) (r : Γ →* M4 R) : Γ →* M4 R where
  toFun g := adj m * r g * m
  map_one' := by rw [map_one, mul_one, sp_adj_mul hm]
  map_mul' g h := by
    rw [map_mul]
    calc adj m * (r g * r h) * m = adj m * r g * (m * adj m) * r h * m := by rw [sp_mul_adj hm]; simp only [mul_assoc, mul_one]
      _ = _ := by simp only [mul_assoc]

theorem wM_sp (pr : Bool) : IsGSp 1 (wM R pr) := by
  cases pr
  · simp [IsGSp, wM, adj_one]
  · unfold IsGSp
    ext i j
    fin_cases i <;> fin_cases j <;> simp [wM, adj, sgn, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, Fin.rev]

theorem wM_map (f : R →+* R') (pr : Bool) : (wM R pr).map f = wM R' pr := by
  cases pr
  · simp [wM]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [wM]

theorem wM_par (pr : Bool) : Par (wM R pr) := by
  cases pr
  · intro i j hij
    have : i ≠ j := by rintro rfl; exact lt_irrefl _ hij
    simp [wM, Matrix.one_apply, this]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [wM, lamW]

theorem wM_conj_diagonal (pr : Bool) (d : Fin 4 → R) :
    adj (wM R pr) * Matrix.diagonal d * wM R pr = Matrix.diagonal fun i => d (lab pr i) := by
  cases pr
  · simp [wM, adj_one, lab]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [wM, adj, sgn, lab, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal, Fin.rev]

theorem wM_false_mul (u : M4 R) : adj (wM R false) * u = u := by simp [wM, adj_one]

theorem wM_true_mul (u : M4 R) : (adj (wM R true) * u : M4 R) 0 0 = u 2 0 := by
  simp [wM, adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four]

theorem Par.mul {X Y : M4 R} (hX : Par X) (hY : Par Y) : Par (X * Y) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : lamW k < lamW i
  · rw [hX i k hk, zero_mul]
  · rw [hY k j (by omega), mul_zero]

theorem Par.adj {X : M4 R} (hX : Par X) : Par (adj X) := by
  intro i j hij
  have key : lamW i.rev < lamW j.rev := by
    fin_cases i <;> fin_cases j <;> simp_all [lamW] <;> decide
  simp [_root_.UpperTheory.V.GradeZeroInterpolatingElement.adj, hX _ _ key]

variable {I : Ideal R}

theorem Cg.refl (X : M4 R) : Cg I X X := fun i j => by simp

theorem Cg.symm {X Y : M4 R} (h : Cg I X Y) : Cg I Y X := fun i j => by
  simpa using neg_mem (h i j)

theorem Cg.trans {X Y Z : M4 R} (h : Cg I X Y) (h' : Cg I Y Z) : Cg I X Z := fun i j => by
  simpa using add_mem (h i j) (h' i j)

theorem Cg.mul {X Y X' Y' : M4 R} (h : Cg I X Y) (h' : Cg I X' Y') : Cg I (X * X') (Y * Y') := by
  intro i j
  have e : (X * X') i j - (Y * Y') i j =
      ∑ k, ((X i k - Y i k) * X' k j + Y i k * (X' k j - Y' k j)) := by
    simp only [Matrix.mul_apply, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [e]
  exact I.sum_mem fun k _ => I.add_mem (I.mul_mem_right _ (h i k)) (I.mul_mem_left _ (h' k j))

theorem Cg.adj {X Y : M4 R} (h : Cg I X Y) : Cg I (adj X) (adj Y) := by
  intro i j
  have e : UpperTheory.V.GradeZeroInterpolatingElement.adj X i j - UpperTheory.V.GradeZeroInterpolatingElement.adj Y i j = (sgn i * sgn j) • (X j.rev i.rev - Y j.rev i.rev) := by
    simp [UpperTheory.V.GradeZeroInterpolatingElement.adj, smul_sub]
  rw [e]
  exact zsmul_mem (h _ _) _

theorem unit_of_sub_mem [IsLocalRing R] {x y : R} (hy : IsUnit y) (h : x - y ∈ maximalIdeal R) : IsUnit x := by
  by_contra hx
  have hxm : x ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal x).2 hx
  have : y ∈ maximalIdeal R := by
    have := (maximalIdeal R).sub_mem hxm h
    simpa using this
  exact (IsLocalRing.mem_maximalIdeal y).1 this hy

end Mat

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

theorem Amb.unit_sub (𝔞 : Amb l) {x y : c.O} (h : residue c.O x ≠ residue c.O y) : IsUnit (𝔞.a c x - 𝔞.a c y) := by
  rw [← map_sub]
  refine IsUnit.map _ ?_
  by_contra hn
  exact h (sub_eq_zero.1 (by rw [← map_sub, residue_eq_zero_iff]; exact hn))

theorem Amb.unit_two (𝔞 : Amb l) (c : Coef l) (hl : l ≠ 2) : IsUnit (2 : 𝔞.V) := by
  have h2 : IsUnit (2 : ℤ_[l]) := by
    by_contra hn
    have hm : (2 : ℤ_[l]) ∈ maximalIdeal ℤ_[l] := (IsLocalRing.mem_maximalIdeal _).2 hn
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_ofNat] at hm
    have hd : l ∣ 2 := (ZMod.natCast_eq_zero_iff 2 l).1 (by exact_mod_cast hm)
    exact hl ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 hd)
  have h2O : IsUnit (2 : c.O) := by
    have := h2.map (algebraMap ℤ_[l] c.O)
    rwa [map_ofNat] at this
  have := h2O.map (𝔞.a c)
  rwa [map_ofNat] at this

theorem KPair.cg {D : Raw Ω c} {𝔞 : Amb l} {r u} (h : KPair D 𝔞 r u) (pr : Bool) (g : G ℚ Ω) :
    Cg (maximalIdeal 𝔞.V) (adj (wM 𝔞.V pr) * r g * wM 𝔞.V pr) (Matrix.diagonal fun i => 𝔞.a c (chi D pr i g)) := by
  obtain ⟨_, h2, _, _, _, _, _, _, _⟩ := h
  have hr0 : (D.r0 g).map (𝔞.a c) = Matrix.diagonal (fun i => 𝔞.a c (D.ps i g)) := by
    unfold Raw.r0
    simp [diagRep, Matrix.diagonal_map]
  have hcg : Cg (maximalIdeal 𝔞.V) (r g) ((D.r0 g).map (𝔞.a c)) := fun i j => by simpa using h2 g i j
  have := Cg.mul (Cg.mul (Cg.refl (I := maximalIdeal 𝔞.V) (adj (wM 𝔞.V pr))) hcg)
    (Cg.refl (I := maximalIdeal 𝔞.V) (wM 𝔞.V pr))
  rw [hr0, wM_conj_diagonal] at this
  simpa [chi] using this

theorem sg_sep {D : Raw Ω c} (hD : D.Good) (𝔞 : Amb l) (pr : Bool) : D.sg l ∈ D.Gp l ∧ ∀ i j, lamW i ≠ lamW j →
    IsUnit (𝔞.a c (chi D pr i (D.sg l)) - 𝔞.a c (D.ps j (D.sg l))) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hom, -, -, -, -, -, hfr, hcyc, hsep, -, -, -, -, -, -⟩ := hD
  have hl : l ∈ D.T := by
    unfold Raw.T
    exact Finset.mem_insert_self _ _
  refine ⟨?_, ?_⟩
  · have := (hfr l hl).1
    unfold Raw.Gp Dec
    exact this
  set s := D.sg l with hs
  let U : (c.O)ˣ →* (ResidueField c.O)ˣ := Units.map (residue c.O : c.O →* ResidueField c.O)
  have hU : ∀ χ : G ℚ Ω →* (c.O)ˣ, Raw.bar χ s = ((U (χ s) : (ResidueField c.O)ˣ) : ResidueField c.O) :=
    fun χ => rfl
  have hchi : chiO ℚ Ω l c.O s = 1 := by
    unfold chiO
    rw [MonoidHom.comp_apply, hcyc, map_one]
  have hom' : U (D.om s) = 1 := by
    have := hom s
    rw [hU, hU, hchi, map_one, Units.val_one] at this
    exact Units.ext this
  have hal : U (D.al s) = U (D.ξ s) := by
    unfold Raw.al
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv, hchi, hom', map_one, inv_one, one_mul]
  have hth : U (D.th s) = U (D.ξ s) * U (D.Psi s) := by
    unfold Raw.th
    rw [MonoidHom.mul_apply, map_mul, hal]
  have hsp : ∀ k : ℤ, U (D.ξ s) * U (D.Psi s) ^ k ≠ 1 := by
    intro k hk
    apply hsep l hl k
    rw [hU]
    simp [MonoidHom.mul_apply, map_mul, map_zpow, hk]
  have h0 : U (D.ξ s) ≠ 1 := by simpa using hsp 0
  have h1 : U (D.ξ s) * U (D.Psi s) ≠ 1 := by simpa using hsp 1
  have hm : U (D.ξ s) ≠ U (D.Psi s) := by
    intro he
    apply hsp (-1)
    rw [he, zpow_neg_one, mul_inv_cancel]
  clear_value U
  intro i j hij
  apply Amb.unit_sub 𝔞
  show Raw.bar (chi D pr i) s ≠ Raw.bar (D.ps j) s
  rw [hU, hU]
  intro he
  have he' := Units.ext he
  clear he hU hsep hfr hom hsp
  cases pr <;> fin_cases i <;> fin_cases j <;> simp [lamW] at hij <;>
    simp [chi, lab, Raw.ps, hal, hth] at he' <;>
    first
    | exact absurd he' hm | exact absurd he'.symm hm | exact absurd he' h0 | exact absurd he'.symm h0
    | exact absurd he' h1 | exact absurd he'.symm h1

end UpperTheory.V.Ws

end
