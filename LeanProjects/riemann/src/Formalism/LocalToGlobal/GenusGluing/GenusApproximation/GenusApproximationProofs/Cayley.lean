import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.FactsW
import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.IdempotentCalculationHolds
import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.GlueSmulSame

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

section CayAlg

variable {A : Type} [CommRing A] {m : Type} [Fintype m] [DecidableEq m]

theorem cay_cT_apply (σ : A →+* A) (M : Matrix m m A) (i j : m) : Formalism.UG.cT σ M i j = σ (M j i) := rfl

theorem cay_cT_add (σ : A →+* A) (M N : Matrix m m A) :
    Formalism.UG.cT σ (M + N) = Formalism.UG.cT σ M + Formalism.UG.cT σ N := by
  ext i j; simp only [cay_cT_apply, Matrix.add_apply, map_add]

theorem cay_cT_sub (σ : A →+* A) (M N : Matrix m m A) :
    Formalism.UG.cT σ (M - N) = Formalism.UG.cT σ M - Formalism.UG.cT σ N := by
  ext i j; simp only [cay_cT_apply, Matrix.sub_apply, map_sub]

def IntM (S : Subring A) (Y : Matrix m m A) : Prop := ∀ i j, Y i j ∈ S

theorem IntM.add {S : Subring A} {Y Z : Matrix m m A} (hY : IntM S Y) (hZ : IntM S Z) : IntM S (Y + Z) :=
  fun i j => by rw [Matrix.add_apply]; exact add_mem (hY i j) (hZ i j)

theorem IntM.mul {S : Subring A} {Y Z : Matrix m m A} (hY : IntM S Y) (hZ : IntM S Z) : IntM S (Y * Z) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ (fun k _ => mul_mem (hY i k) (hZ k j))

theorem IntM.smul {S : Subring A} {c : A} (hc : c ∈ S) {Y : Matrix m m A} (hY : IntM S Y) : IntM S (c • Y) :=
  fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem hc (hY i j)

theorem IntM.one {S : Subring A} : IntM S (1 : Matrix m m A) :=
  fun i j => by
    by_cases h : i = j
    · rw [h, Matrix.one_apply_eq]; exact one_mem _
    · rw [Matrix.one_apply_ne h]; exact zero_mem _

end CayAlg

theorem cayleyUnitary_holds : CayleyU := by
  intro A _ σ _ n Q hQ
  set Qi : Matrix (Fin n) (Fin n) A := (Q⁻¹).val with hQi
  set Qm : Matrix (Fin n) (Fin n) A := Q.val with hQm
  have h1 : Qi * Qm = 1 := by rw [hQi, hQm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : Qm * Qi = 1 := by rw [hQi, hQm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hS : Formalism.UG.cT σ Qi * Formalism.UG.cT σ Qm = 1 := by rw [← Formalism.UG.cT_mul, h2, Formalism.UG.cT_one]
  have hsum : Formalism.UG.cT σ Qi * Qi = Formalism.UG.cT σ Qi + Qi := by
    calc Formalism.UG.cT σ Qi * Qi = Formalism.UG.cT σ Qi * (Qm + Formalism.UG.cT σ Qm) * Qi := by rw [hQ, Matrix.mul_one]
      _ = Formalism.UG.cT σ Qi * (Qm * Qi) + (Formalism.UG.cT σ Qi * Formalism.UG.cT σ Qm) * Qi := by
          rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = Formalism.UG.cT σ Qi + Qi := by rw [h2, hS, Matrix.mul_one, Matrix.one_mul]
  have hg : Formalism.UG.cT σ (Qi - 1) * (Qi - 1) = 1 := by
    rw [cay_cT_sub, Formalism.UG.cT_one]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul, hsum]
    abel
  have hg' : (Qi - 1) * Formalism.UG.cT σ (Qi - 1) = 1 := mul_eq_one_comm.mp hg
  refine ⟨⟨Qi - 1, Formalism.UG.cT σ (Qi - 1), hg', hg⟩, ?_, rfl⟩
  show Formalism.UG.cT σ (Qi - 1) * 1 * (Qi - 1) = 1
  rw [Matrix.mul_one, hg]

theorem cayleyRational_holds : CayleyQ := by
  intro A _ σ _ n x hx P hP
  set X : Matrix (Fin n) (Fin n) A := x.val with hX
  set Xi : Matrix (Fin n) (Fin n) A := (x⁻¹).val with hXi
  set Pm : Matrix (Fin n) (Fin n) A := P.val with hPm
  set Pi : Matrix (Fin n) (Fin n) A := (P⁻¹).val with hPi
  have hxu : Formalism.UG.cT σ X * X = 1 := by
    have h : Formalism.UG.cT σ X * 1 * X = 1 := hx
    rwa [Matrix.mul_one] at h
  have hXX : X * Xi = 1 := by rw [hX, hXi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hXiX : Xi * X = 1 := by rw [hX, hXi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hPP : Pm * Pi = 1 := by rw [hPm, hPi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiP : Pi * Pm = 1 := by rw [hPm, hPi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcX : Formalism.UG.cT σ X = Xi := by
    calc Formalism.UG.cT σ X = Formalism.UG.cT σ X * (X * Xi) := by rw [hXX, Matrix.mul_one]
      _ = (Formalism.UG.cT σ X * X) * Xi := by rw [Matrix.mul_assoc]
      _ = Xi := by rw [hxu, Matrix.one_mul]
  have hcP : Formalism.UG.cT σ Pm = Xi * Pm := by
    rw [hP, cay_cT_add, Formalism.UG.cT_one, hcX, Matrix.mul_add, Matrix.mul_one, hXiX, add_comm]
  have h3 : Formalism.UG.cT σ Pm * (Pi * X) = 1 := by
    rw [hcP, Matrix.mul_assoc, ← Matrix.mul_assoc Pm, hPP, Matrix.one_mul, hXiX]
  have key : Formalism.UG.cT σ Pi = Pi * X := by
    calc Formalism.UG.cT σ Pi = Formalism.UG.cT σ Pi * (Formalism.UG.cT σ Pm * (Pi * X)) := by rw [h3, Matrix.mul_one]
      _ = Formalism.UG.cT σ (Pm * Pi) * (Pi * X) := by rw [Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = Pi * X := by rw [hPP, Formalism.UG.cT_one, Matrix.one_mul]
  rw [key]
  calc Pi + Pi * X = Pi * (1 + X) := by rw [Matrix.mul_add, Matrix.mul_one]
    _ = 1 := by rw [← hP, hPiP]

section CayStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cay_denom {n : ℕ} (Y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ IntM (Formalism.L2.Herm.intAf F E) (iA F E (algebraMap (𝓞 F) E d) • Y) := by
  classical
  have h := fun p : Fin n × Fin n => Formalism.UG.P.levelaf_denom (F := F) (E := E) (Y p.1 p.2)
  choose d hd0 hd using h
  refine ⟨∏ p, d p, Finset.prod_ne_zero_iff.2 (fun p _ => hd0 p), fun i j => ?_⟩
  rw [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ (i, j)),
    map_mul, map_mul, mul_comm (iA F E (algebraMap (𝓞 F) E (d (i, j)))), mul_assoc]
  refine Subring.mul_mem _ (iA_algebraMap_mem _) ?_
  rw [iA_algebraMap]
  exact hd (i, j)

end CayStep

theorem cayleyStep_of : EAtNeZero → ApproxA → UnitNear → CayleyStep := by
  intro hE hAp hUN F E _ _ _ _ _ _ hc n v x hx hPu
  classical
  set σA := Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F) with hσA
  set σE : E →+* E := (hc.sig : E →+* E) with hσE
  have hσσ : ∀ a, σA (σA a) = a := Formalism.L2.DIV.sigR_sigR hc
  have hσEE : ∀ a, σE (σE a) = a := fun a => star_star a
  have hσι : ∀ a : E, σA (iA F E a) = iA F E (σE a) := fun a => rfl
  have hσD : ∀ r : 𝓞 F, σA (iA F E (algebraMap (𝓞 F) E r)) = iA F E (algebraMap (𝓞 F) E r) := by
    intro r; rw [iA_algebraMap]; simp [σA, Formalism.UG.sigR]
  have hσS : ∀ a ∈ Formalism.L2.Herm.intAf F E, σA a ∈ Formalism.L2.Herm.intAf F E :=
    fun a ha => (Formalism.L2.DIV.sigS hc ⟨a, ha⟩).2

  have hmul := (idempotentCalculation_holds F E).2.1
  have hev : eAt E v * eAt E v = eAt E v := by
    show eP E _ * eP E _ = eP E _
    rw [hmul]; exact eP_congr (fun u => and_self_iff)
  have heS : eAt E v ∈ Formalism.L2.Herm.intAf F E := eP_mem _
  have he0 : eAt E v ≠ 0 := hE F E v

  have hJ : (1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hx' : x ∈ Formalism.UG.UJ σA (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    have h := hx
    change _ ∈ Formalism.UG.UJ σA ((1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) at h
    rwa [hJ] at h
  set P : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := hPu.unit with hPdef
  have hPv : P.val = 1 + x.val := hPu.unit_spec
  have hQ := cayleyRational_holds _ σA hσσ n x hx' P hPv
  set Pm : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := P.val with hPm
  set Q : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := (P⁻¹).val with hQd
  set X : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := x.val with hX
  set Xi : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := (x⁻¹).val with hXi
  have hQP : Q * Pm = 1 := by rw [hQd, hPm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hXiX : Xi * X = 1 := by rw [hX, hXi, ← Units.val_mul, inv_mul_cancel, Units.val_one]

  obtain ⟨d1, hd1, hI1⟩ := cay_denom (F := F) (E := E) (Xi * Pm)
  obtain ⟨d2, hd2, hI2⟩ := cay_denom (F := F) (E := E) Pm
  obtain ⟨p0, hp0v, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  set D : 𝓞 F := p0 * d1 * d2 with hDd
  have hD0 : D ≠ 0 := mul_ne_zero (mul_ne_zero hp0 hd1) hd2
  have h20 : (2 : 𝓞 F) ≠ 0 := by
    intro h
    have h' := congrArg (algebraMap (𝓞 F) F) h
    rw [map_ofNat, map_zero] at h'
    exact two_ne_zero h'

  have happ := fun i j => hAp F E (2 * D) (mul_ne_zero h20 hD0) (Q i j)
  choose b s' hs' hb using happ
  set Q0 : Matrix (Fin n) (Fin n) E :=
    Matrix.of fun i j => (2 : E)⁻¹ * (b i j - σE (b j i) + (1 : Matrix (Fin n) (Fin n) E) i j) with hQ0d
  set s : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := Matrix.of fun i j => s' i j - σA (s' j i) with hsd
  have hs : IntM (Formalism.L2.Herm.intAf F E) s := fun i j => by
    rw [hsd, Matrix.of_apply]; exact sub_mem (hs' i j) (hσS _ (hs' j i))
  have hδE : ∀ i j : Fin n, σE ((1 : Matrix (Fin n) (Fin n) E) j i) = (1 : Matrix (Fin n) (Fin n) E) i j := by
    intro i j
    by_cases h : i = j
    · subst h; simp
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h), map_zero]
  have hδA : ∀ i j : Fin n, (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j =
      iA F E ((1 : Matrix (Fin n) (Fin n) E) i j) := by
    intro i j
    by_cases h : i = j
    · subst h; simp
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]
  have hQ0 : Q0 + Formalism.UG.cT σE Q0 = 1 := by
    ext i j
    rw [Matrix.add_apply, cay_cT_apply, hQ0d, Matrix.of_apply, Matrix.of_apply]
    simp only [map_mul, map_sub, map_add, map_inv₀, map_ofNat, hσEE, hδE]
    have h2 : (2 : E)⁻¹ * 2 = 1 := inv_mul_cancel₀ two_ne_zero
    linear_combination ((1 : Matrix (Fin n) (Fin n) E) i j) * h2
  have hι2 : iA F E (2 : E)⁻¹ * 2 = 1 := by
    have h2 : iA F E 2 = 2 := map_ofNat _ 2
    rw [← h2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  have hι2D : iA F E (algebraMap (𝓞 F) E (2 * D)) = 2 * iA F E (algebraMap (𝓞 F) E D) := by
    rw [map_mul, map_mul, map_ofNat, map_ofNat]
  have hQrep : Q = Q0.map (iA F E) + iA F E (algebraMap (𝓞 F) E D) • s := by
    ext i j
    have e1 := hb i j
    have e2 : σA (Q j i) = iA F E (σE (b j i)) + 2 * iA F E (algebraMap (𝓞 F) E D) * σA (s' j i) := by
      rw [hb j i, map_add, map_mul, hσι, hσD, hι2D]
    have e3 : Q i j + σA (Q j i) = iA F E ((1 : Matrix (Fin n) (Fin n) E) i j) := by
      have h := congrFun (congrFun hQ i) j
      rw [Matrix.add_apply, cay_cT_apply, hδA] at h
      exact h
    rw [hι2D] at e1
    rw [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hQ0d, hsd, Matrix.of_apply,
      Matrix.of_apply, map_mul, map_add, map_sub]
    linear_combination iA F E (2 : E)⁻¹ * e1 - iA F E (2 : E)⁻¹ * e2 + iA F E (2 : E)⁻¹ * e3 -
      (Q i j - iA F E (algebraMap (𝓞 F) E D) * s' i j + iA F E (algebraMap (𝓞 F) E D) * σA (s' j i)) * hι2

  set ι1 := iA F E (algebraMap (𝓞 F) E d1) with hι1
  set ι2 := iA F E (algebraMap (𝓞 F) E d2) with hι2
  set ιp := iA F E (algebraMap (𝓞 F) E p0) with hιp
  set e := eAt E v with he
  have hDf : iA F E (algebraMap (𝓞 F) E D) = ιp * (ι1 * ι2) := by
    rw [hDd, map_mul, map_mul, map_mul, map_mul, mul_assoc]
  set s'' : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := ι1 • ((ι2 • Pm) * s) with hs''d
  have hs'' : IntM (Formalism.L2.Herm.intAf F E) s'' :=
    IntM.smul (iA_algebraMap_mem _) (IntM.mul hI2 hs)
  have h5 : Q0.map (iA F E) = Q * (1 - ιp • s'') := by
    have h := eq_sub_of_add_eq hQrep.symm
    rw [h, Matrix.mul_sub, Matrix.mul_one, hs''d, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, ← Matrix.mul_assoc, hQP, Matrix.one_mul, smul_smul, smul_smul, hDf, mul_assoc]
  obtain ⟨R, hR, hRe⟩ := hUN F E hc v p0 hp0v n s'' hs''
  have h7 : e • (Q0.map (iA F E) * (R * Pm)) = e • 1 := by
    have h : Q0.map (iA F E) * (R * Pm) = Q * ((1 - ιp • s'') * R) * Pm := by
      rw [h5]; simp only [Matrix.mul_assoc]
    rw [h, ← Matrix.smul_mul, ← Matrix.mul_smul, hRe, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hQP]

  have hdet : Q0.det ≠ 0 := by
    intro h0
    apply he0
    have hd := congrArg Matrix.det h7
    rw [Matrix.det_smul, Matrix.det_smul, Matrix.det_mul, Matrix.det_one, mul_one] at hd
    have hz : (Q0.map (iA F E)).det = 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
    rw [hz, zero_mul, mul_zero, Fintype.card_fin] at hd
    have hpow : ∀ k : ℕ, e ^ (k + 1) = e := by
      intro k
      induction k with
      | zero => rw [zero_add, pow_one]
      | succ k ih => rw [pow_succ, ih, hev]
    rcases n with _ | k
    · rw [pow_zero] at hd
      rw [← mul_one e, ← hd, mul_zero]
    · rw [← hpow k]; exact hd.symm
  have hQ0u : IsUnit Q0 := (Matrix.isUnit_iff_isUnit_det Q0).2 (isUnit_iff_ne_zero.2 hdet)
  set Q0' : GL (Fin n) E := hQ0u.unit with hQ0'd
  have hQ0'v : Q0'.val = Q0 := hQ0u.unit_spec
  obtain ⟨γ, hγ, hγv⟩ := cayleyUnitary_holds E σE hσEE n Q0' (by rw [hQ0'v]; exact hQ0)
  refine ⟨γ, hγ, ?_⟩
  set G : Matrix (Fin n) (Fin n) E := (Q0'⁻¹).val with hGd
  have hGQ : G * Q0 = 1 := by rw [hGd, ← hQ0'v, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hGι : G.map (iA F E) * Q0.map (iA F E) = 1 := by
    rw [← Matrix.map_mul, hGQ, Matrix.map_one _ (map_zero _) (map_one _)]
  have h10 : e • G.map (iA F E) = e • (R * Pm) := by
    calc e • G.map (iA F E) = G.map (iA F E) * (e • 1) := by rw [Matrix.mul_smul, Matrix.mul_one]
      _ = G.map (iA F E) * (e • (Q0.map (iA F E) * (R * Pm))) := by rw [h7]
      _ = e • (R * Pm) := by rw [Matrix.mul_smul, ← Matrix.mul_assoc, hGι, Matrix.one_mul]
  have hγι : (Formalism.UG.bc (iA F E) γ).val = G.map (iA F E) - 1 := by
    show γ.val.map (iA F E) = _
    rw [hγv]
    ext i j
    rw [Matrix.map_apply, Matrix.sub_apply, Matrix.sub_apply, map_sub, hδA, Matrix.map_apply]
  have hRe' : e • R = e • 1 + (e * ιp) • (s'' * R) := by
    rw [Matrix.sub_mul, Matrix.one_mul, smul_sub, Matrix.smul_mul, smul_smul] at hRe
    exact sub_eq_iff_eq_add.mp hRe
  have hXiP : Xi * Pm = Xi + 1 := by rw [hPv, Matrix.mul_add, Matrix.mul_one, hXiX]
  have hW : Xi * s'' * R * Pm = (ι1 • (Xi * Pm)) * s * R * (ι2 • Pm) := by
    rw [hs''d]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    rw [mul_comm ι1 ι2]
  have hmain : e • (Xi * (G.map (iA F E) - 1)) = e • 1 + (e * ιp) • ((ι1 • (Xi * Pm)) * s * R * (ι2 • Pm)) := by
    rw [← hW]
    calc e • (Xi * (G.map (iA F E) - 1)) = Xi * (e • G.map (iA F E)) - e • Xi := by
          rw [Matrix.mul_sub, smul_sub, Matrix.mul_smul, Matrix.mul_one]
      _ = Xi * ((e • R) * Pm) - e • Xi := by rw [h10, Matrix.smul_mul]
      _ = e • (Xi * Pm) + (e * ιp) • (Xi * s'' * R * Pm) - e • Xi := by
          rw [hRe', Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
            Matrix.mul_smul, Matrix.one_mul, Matrix.mul_assoc Xi, Matrix.mul_assoc Xi, Matrix.mul_assoc s'']
      _ = e • 1 + (e * ιp) • (Xi * s'' * R * Pm) := by
          rw [hXiP, smul_add]; abel
  intro i j
  have hint : IntM (Formalism.L2.Herm.intAf F E) (e • (Xi * (G.map (iA F E) - 1))) := by
    rw [hmain]
    exact IntM.add (IntM.smul heS IntM.one)
      (IntM.smul (mul_mem heS (iA_algebraMap_mem _)) (IntM.mul (IntM.mul (IntM.mul hI1 hs) hR) hI2))
  have := hint i j
  rw [Matrix.smul_apply, smul_eq_mul] at this
  rw [Units.val_mul, hγι]
  exact this

end Formalism.L2.GenusGluing.Gen
