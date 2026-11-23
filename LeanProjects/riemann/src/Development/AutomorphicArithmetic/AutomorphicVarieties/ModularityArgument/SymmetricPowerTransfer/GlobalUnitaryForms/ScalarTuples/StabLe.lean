import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsIntConj

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open Matrix Loc Polynomial

section Abs

variable {O : Type} [CommRing O]

private theorem isInt_conj {B : Type} [Ring B] [Algebra O B] (a b k : B) (h1 : a * b = 1) (h2 : b * a = 1)
    (h : IsIntegral O k) : IsIntegral O (a * k * b) :=
  _root_.UpperTheory.Reformulated.B.Qf45.isInt_conj a b k h1 h2 h

private theorem isInt_mat {L : Type} [CommRing L] [Algebra O L] {n : Type} [Fintype n] [DecidableEq n]
    (N : Matrix n n L) (h : ∀ i j, IsIntegral O (N i j)) : IsIntegral O N := by
  let N' : Matrix n n (integralClosure O L) := fun i j => ⟨N i j, h i j⟩
  have h1 : IsIntegral (integralClosure O L) N' :=
    ⟨N'.charpoly, N'.charpoly_monic, by rw [← aeval_def]; exact Matrix.aeval_self_charpoly N'⟩
  have h2 : IsIntegral O N' := isIntegral_trans (R := O) (A := integralClosure O L) N' h1
  have h3 := h2.map ((integralClosure O L).val.mapMatrix (m := n))
  have e : (integralClosure O L).val.mapMatrix N' = N := by
    refine Matrix.ext fun i j => ?_
    rfl
  rwa [e] at h3

private theorem isInt_inter {L R : Type} [CommRing L] [Algebra O L] [CommRing R] [Algebra O R] {n : Type} [Fintype n]
    [DecidableEq n] (f : R → n → L) (hinj : ∀ c, f c = 0 → c = 0) (hadd : ∀ a b, f (a + b) = f a + f b)
    (hs : ∀ (r : O) c, f (r • c) = algebraMap O L r • f c)
    (M : Matrix n n L) (q : R) (hM : ∀ c, M *ᵥ f c = f (q * c)) (h : IsIntegral O M) : IsIntegral O q := by
  obtain ⟨p, hp, h0⟩ := h
  refine ⟨p, hp, ?_⟩
  have key : ∀ (p : O[X]) (c : R), aeval M p *ᵥ f c = f (aeval q p * c) := by
    intro p
    induction p using Polynomial.induction_on with
    | C r =>
      intro c
      rw [aeval_C, aeval_C, ← Algebra.smul_def, hs, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
        Matrix.one_mulVec]
      ext i
      simp [Algebra.smul_def]
    | add p q hp hq =>
      intro c
      simp only [map_add, Matrix.add_mulVec, hp, hq, add_mul, hadd]
    | monomial n r ih =>
      intro c
      have e1 : aeval M (C r * X ^ (n + 1)) = aeval M (C r * X ^ n) * M := by
        simp only [map_mul, map_pow, aeval_X, pow_succ, mul_assoc]
      have e2 : aeval q (C r * X ^ (n + 1)) = aeval q (C r * X ^ n) * q := by
        simp only [map_mul, map_pow, aeval_X, pow_succ, mul_assoc]
      rw [e1, e2, ← Matrix.mulVec_mulVec, hM, ih, mul_assoc]
  have := key p 1
  rw [aeval_def, h0, Matrix.zero_mulVec, mul_one] at this
  exact hinj _ (by rw [aeval_def] at this; exact this.symm)

end Abs

section DSide

variable {K : Type} [Field K] {Δ τ : K}

private theorem mt_sq (G : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) (hd : G.det = 1) (ht : G.trace = algebraMap K _ τ) :
    G * G = (-1 : K) • (1 : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) + τ • G := by
  have hd' : G 0 0 * G 1 1 - G 0 1 * G 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact hd
  have ht' : G 0 0 + G 1 1 = algebraMap K _ τ := by rw [← ht, Matrix.trace_fin_two]
  have hs : ∀ x : Lsq K Δ, τ • x = (G 0 0 + G 1 1) * x := fun x => by rw [ht', Algebra.smul_def]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, hs]
    linear_combination -hd'
  · simp [Matrix.mul_apply, Fin.sum_univ_two, hs]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, hs]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, hs]
    linear_combination -hd'

private def jA (γ : DX Δ) (h : HasTr γ τ) : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) (Lsq K Δ) :=
  QuadraticAlgebra.lift ⟨mt γ, mt_sq _ h.1 h.2⟩

private theorem jA_apply (γ : DX Δ) (h : HasTr γ τ) (x : Etau K τ) :
    jA γ h x = x.re • (1 : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) + x.im • mt γ := rfl

private theorem jA_entries (G : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) (a b : K) :
    (a • (1 : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) + b • G) 0 0 = algebraMap K _ a + algebraMap K _ b * G 0 0 ∧
    (a • (1 : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) + b • G) 0 1 = algebraMap K _ b * G 0 1 ∧
    (a • (1 : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) + b • G) 1 0 = algebraMap K _ b * G 1 0 ∧
    (a • (1 : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) + b • G) 1 1 = algebraMap K _ a + algebraMap K _ b * G 1 1 := by
  have hs : ∀ (c : K) (x : Lsq K Δ), c • x = algebraMap K (Lsq K Δ) c * x := fun c x => Algebra.smul_def c x
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Matrix.add_apply, Matrix.smul_apply, hs]

private theorem jA_det (γ : DX Δ) (h : HasTr γ τ) (x : Etau K τ) :
    (jA γ h x).det = algebraMap K _ (QuadraticAlgebra.norm x) := by
  have hd' : mt γ 0 0 * mt γ 1 1 - mt γ 0 1 * mt γ 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact h.1
  have ht' : mt γ 0 0 + mt γ 1 1 = algebraMap K _ τ := by rw [← h.2, Matrix.trace_fin_two]
  obtain ⟨e0, e1, e2, e3⟩ := jA_entries (Δ := Δ) (mt γ) x.re x.im
  rw [jA_apply, Matrix.det_fin_two, e0, e1, e2, e3, QuadraticAlgebra.norm_def]
  simp only [map_add, map_sub, map_mul, map_neg, map_one]
  linear_combination (algebraMap K (Lsq K Δ) x.re * algebraMap K (Lsq K Δ) x.im) * ht' +
    (algebraMap K (Lsq K Δ) x.im) ^ 2 * hd'

private theorem jA_inj (γ : DX Δ) (h : HasTr γ τ) (hr : τ ^ 2 - 4 ≠ 0) : Function.Injective (jA γ h) := by
  have hd' : mt γ 0 0 * mt γ 1 1 - mt γ 0 1 * mt γ 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact h.1
  have ht' : mt γ 0 0 + mt γ 1 1 = algebraMap K _ τ := by rw [← h.2, Matrix.trace_fin_two]
  have inj : Function.Injective (algebraMap K (Lsq K Δ)) := (algebraMap K (Lsq K Δ)).injective
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [jA_apply] at hx
  obtain ⟨e0, e1, e2, e3⟩ := jA_entries (Δ := Δ) (mt γ) x.re x.im
  rw [hx] at e0 e1 e2 e3
  simp only [Matrix.zero_apply] at e0 e1 e2 e3
  by_cases hb : x.im = 0
  · have ha : x.re = 0 := by
      apply inj
      rw [hb] at e0
      simpa using e0.symm
    ext
    · exact ha
    · exact hb
  · exfalso
    have hc : algebraMap K (Lsq K Δ) x.im⁻¹ * algebraMap K (Lsq K Δ) x.im = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hb, map_one]
    set c := algebraMap K (Lsq K Δ) x.im⁻¹
    set b := algebraMap K (Lsq K Δ) x.im
    have h01 : mt γ 0 1 = 0 := by linear_combination -c * e1 - mt γ 0 1 * hc
    have hD : mt γ 0 0 = mt γ 1 1 := by
      linear_combination -c * e0 + c * e3 - (mt γ 0 0 - mt γ 1 1) * hc
    have hdd : mt γ 0 0 * mt γ 0 0 = 1 := by
      rw [h01, ← hD] at hd'
      linear_combination hd'
    have ht2 : algebraMap K (Lsq K Δ) τ = 2 * mt γ 0 0 := by rw [← ht', ← hD]; ring
    apply hr
    apply inj
    rw [map_sub, map_pow, ht2, map_ofNat, map_zero]
    linear_combination 4 * hdd

private theorem zd_spec {n : DX Δ} (hn : n ∈ ZD Δ) :
    ∃ a : Kˣ, mt n = scalar (Fin 2) (algebraMap K (Lsq K Δ) a) := by
  rw [ZD, Subgroup.mem_subgroupOf] at hn
  obtain ⟨a, ha⟩ := hn
  exact ⟨a, by rw [mt, ← ha]; rfl⟩

private theorem zd_normal : (ZD Δ).Normal := ⟨fun n hn g => by
  obtain ⟨a, ha⟩ := zd_spec hn
  have : g * n * g⁻¹ = n := by
    rw [mul_inv_eq_iff_eq_mul]
    refine Subtype.ext (Units.ext ?_)
    show mt g * mt n = mt n * mt g
    rw [ha]
    exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).symm
  rwa [this]⟩

private theorem conj_sq {L : Type} [CommRing L] (Y Y' G T S S' : Matrix (Fin 2) (Fin 2) L) (n0 a b : L)
    (h1 : Y' * Y = 1) (h2 : Y * Y' = 1) (hS : S * S' = 1) (hab : a * b = 1) (hT : n0 • T = G * G)
    (hdet : G.det = n0) (hG : Y' * G * Y = a • S) : Y' * T * Y = S'.det • (S * S) := by
  have hdY : Y'.det * Y.det = 1 := by rw [← Matrix.det_mul, h1, Matrix.det_one]
  have hd : n0 = a ^ 2 * S.det := by
    have := congrArg Matrix.det hG
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, hdet] at this
    simp only [Fintype.card_fin] at this
    linear_combination this - n0 * hdY
  have hdS : S.det * S'.det = 1 := by rw [← Matrix.det_mul, hS, Matrix.det_one]
  have e : n0 • (Y' * T * Y) = (a ^ 2) • (S * S) := by
    calc n0 • (Y' * T * Y) = Y' * (n0 • T) * Y := by simp [Matrix.mul_smul, Matrix.smul_mul]
      _ = Y' * (G * G) * Y := by rw [hT]
      _ = (Y' * G * Y) * (Y' * G * Y) := by
        have : (Y' * G * Y) * (Y' * G * Y) = Y' * G * (Y * Y') * G * Y := by simp only [Matrix.mul_assoc]
        rw [this, h2]
        simp [Matrix.mul_assoc]
      _ = (a ^ 2) • (S * S) := by
        rw [hG]
        simp [Matrix.mul_smul, Matrix.smul_mul, smul_smul, pow_two]
  calc Y' * T * Y = (b ^ 2 * S'.det) • (n0 • (Y' * T * Y)) := by
        rw [smul_smul]
        have : b ^ 2 * S'.det * n0 = 1 := by
          rw [hd]
          linear_combination a ^ 2 * b ^ 2 * hdS + (a * b + 1) * hab
        rw [this, one_smul]
    _ = S'.det • (S * S) := by
        rw [e, smul_smul]
        congr 1
        linear_combination S'.det * (a * b + 1) * hab

private theorem quo_norm (s : (Etau K τ)ˣ) :
    algebraMap K (Etau K τ) (QuadraticAlgebra.norm (s : Etau K τ)) * quo s = (s : Etau K τ) * s := by
  have e1 : star ((s⁻¹ : (Etau K τ)ˣ) : Etau K τ) * star (s : Etau K τ) = 1 := by
    rw [← star_mul, Units.mul_inv, star_one]
  rw [QuadraticAlgebra.algebraMap_norm_eq_mul_star, quo]
  linear_combination ((s : Etau K τ) * s) * e1

private theorem int_D (O : Type) [CommRing O] [Algebra O K] (hr : τ ^ 2 - 4 ≠ 0) (γ : DX Δ)
    (j : (Etau K τ)ˣ →* DX Δ) (hγ : HasTr γ τ) (hj : IsEmb τ γ j) (y : DX Δ) (s : (Etau K τ)ˣ)
    (h : y⁻¹ * j s * y ∈ ZD Δ ⊔ KD Δ O) : IsIntegral O (quo s) := by
  haveI := zd_normal (Δ := Δ)
  have h' : y⁻¹ * j s * y ∈ ((ZD Δ ⊔ KD Δ O : Subgroup (DX Δ)) : Set (DX Δ)) := h
  rw [Subgroup.normal_mul, Set.mem_mul] at h'
  obtain ⟨n, hn, kk, hk, e⟩ := h'
  obtain ⟨a, ha⟩ := zd_spec hn
  have hk' : (kk : GL (Fin 2) (Lsq K Δ)) ∈ (GeneralLinearGroup.map
      ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ)).range := hk
  obtain ⟨k, hk⟩ := hk'
  let φ := GeneralLinearGroup.map (n := Fin 2)
    ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ)
  have hent : ∀ (g : GL (Fin 2) (integralClosure O (Lsq K Δ))) i j',
      IsIntegral O ((φ g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) i j') := fun g i j' =>
    (g.1 i j').2
  have h1 : mt y⁻¹ * mt y = 1 := congrArg (fun g : DX Δ => mt g) (inv_mul_cancel y)
  have h2 : mt y * mt y⁻¹ = 1 := congrArg (fun g : DX Δ => mt g) (mul_inv_cancel y)
  have hS : (φ k : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * (φ k⁻¹ : GL (Fin 2) (Lsq K Δ)) = 1 := by
    have : φ k * φ k⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact congrArg (fun g : GL (Fin 2) (Lsq K Δ) => (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ))) this
  have hjs : jA γ hγ s = mt (j s) := (hj s).symm
  have hT : algebraMap K (Lsq K Δ) (QuadraticAlgebra.norm (s : Etau K τ)) • jA γ hγ (quo s) =
      mt (j s) * mt (j s) := by
    have := congrArg (jA γ hγ) (quo_norm s)
    rw [map_mul, map_mul, AlgHom.commutes, ← Algebra.smul_def, hjs] at this
    rwa [algebraMap_smul]
  have hdet : (mt (j s)).det = algebraMap K (Lsq K Δ) (QuadraticAlgebra.norm (s : Etau K τ)) := by
    rw [← hjs, jA_det]
  have hG : mt y⁻¹ * mt (j s) * mt y = algebraMap K (Lsq K Δ) a • (φ k : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) := by
    have e' : mt n * mt kk = mt y⁻¹ * mt (j s) * mt y := congrArg (fun g : DX Δ => mt g) e
    rw [← e', ha, show mt kk = (φ k : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) from
      congrArg (fun g : GL (Fin 2) (Lsq K Δ) => (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ))) hk.symm,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
  have hab : algebraMap K (Lsq K Δ) a * algebraMap K (Lsq K Δ) ((a⁻¹ : Kˣ) : K) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hX := conj_sq _ _ _ _ _ _ _ _ _ h1 h2 hS hab hT hdet hG
  have hdI : IsIntegral O ((φ k⁻¹ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).det := by
    rw [Matrix.det_fin_two]
    exact ((hent _ _ _).mul (hent _ _ _)).sub ((hent _ _ _).mul (hent _ _ _))
  have hXI : IsIntegral O (mt y⁻¹ * jA γ hγ (quo s) * mt y) := by
    rw [hX]
    refine isInt_mat _ fun i j' => ?_
    rw [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]
    exact hdI.mul (((hent _ _ _).mul (hent _ _ _)).add ((hent _ _ _).mul (hent _ _ _)))
  have hTI := isInt_conj _ _ _ h2 h1 hXI
  have eT : mt y * (mt y⁻¹ * jA γ hγ (quo s) * mt y) * mt y⁻¹ = jA γ hγ (quo s) := by
    calc _ = (mt y * mt y⁻¹) * jA γ hγ (quo s) * (mt y * mt y⁻¹) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.one_mul, Matrix.mul_one]
  rw [eT] at hTI
  exact (isIntegral_algHom_iff ((jA γ hγ).restrictScalars O) (jA_inj γ hγ hr)).1 hTI

end DSide

section USide

variable {K : Type} [Field K] {Δ τ : K}

private theorem ofE_add (a b : Etau K τ) : ofE Δ (a + b) = ofE Δ a + ofE Δ b := by
  ext <;> simp [ofE]

private theorem ofE_mul (a b : Etau K τ) : ofE Δ (a * b) = ofE Δ a * ofE Δ b := by
  ext <;> simp [ofE]

private theorem ofE_smul (O : Type) [CommRing O] [Algebra O K] (r : O) (z : Etau K τ) :
    ofE Δ (r • z) = algebraMap O (Lsq K Δ) r • ofE Δ z := by
  have hr : ∀ x : K, algebraMap K (Lsq K Δ) (r • x) = algebraMap O (Lsq K Δ) r * algebraMap K (Lsq K Δ) x := fun x => by
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
  refine QuadraticAlgebra.ext ?_ ?_ <;> simp only [ofE, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, hr, algebraMap_smul] <;>
    exact (Algebra.smul_def r _).symm

private theorem int_U (O : Type) [CommRing O] [Algebra O K] {c : K} {d m : EL Δ τ} {δ : U3 Δ}
    {ι : (Etau K τ)ˣ →* U3 Δ} {P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)} (hM : Models c d m δ ι P)
    (y : U3 Δ) (s : (Etau K τ)ˣ) (h : y⁻¹ * ι s * y ∈ KU O Δ) : IsIntegral O (quo s) := by
  have hk : IsIntegral O ((y⁻¹ * ι s * y : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) :=
    isInt_mat _ fun i j => (h i j).1
  have h1 : (y : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * ((y⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) = 1 :=
    congrArg Subtype.val (mul_inv_cancel y)
  have h2 : ((y⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * (y : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) = 1 :=
    congrArg Subtype.val (inv_mul_cancel y)
  have hI := isInt_conj _ _ _ h1 h2 hk
  have e : (y : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * ((y⁻¹ * ι s * y : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *
      ((y⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) = (ι s : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) :=
    congrArg Subtype.val (show y * (y⁻¹ * ι s * y) * y⁻¹ = ι s by group)
  rw [e] at hI
  refine isInt_inter (O := O) (fun z => P (0, ofE Δ z)) ?_ ?_ ?_ _ (quo s) ?_ hI
  · intro z hz
    have h3 : ((0 : Lsq K Δ), ofE Δ z) = 0 := P.injective (hz.trans (map_zero P).symm)
    have h4 : ofE Δ z = 0 := congrArg Prod.snd h3
    have inj : Function.Injective (algebraMap K (Lsq K Δ)) := (algebraMap K (Lsq K Δ)).injective
    have h5 : algebraMap K (Lsq K Δ) z.re = 0 := congrArg QuadraticAlgebra.re h4
    have h6 : algebraMap K (Lsq K Δ) z.im = 0 := congrArg QuadraticAlgebra.im h4
    ext
    · exact inj (h5.trans (map_zero _).symm)
    · exact inj (h6.trans (map_zero _).symm)
  · intro a b
    rw [← map_add]
    simp [ofE_add]
  · intro r z
    rw [← map_smul, ofE_smul]
    simp
  · intro z
    rw [← hM.tor s]
    simp [tor, ofE_mul]

end USide

end UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Glob.stabLe :
    UpperTheory.V.Z.Sym.Glob.StabLe := by
  intro O K _ _ _ _ Δ τ _ hr
  refine ⟨fun γ j hγ hj y s h => ⟨int_D O hr γ j hγ hj y s h, int_D O hr γ j hγ hj y s⁻¹ ?_⟩,
    fun c d m δ ι P _ hM y s h => ⟨int_U O hM y s h, int_U O hM y s⁻¹ ?_⟩⟩
  · have := inv_mem h
    simpa [mul_assoc] using this
  · have := inv_mem h
    simpa [mul_assoc] using this
