import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.FxTwflag
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicPointGalois

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J
section Fx
open Matrix Ws.Eb
private def sn {K : Type} [CommRing K] {n : ℕ} (X : Matrix (Fin n) (Fin n) (DualNumber K)) :
    Matrix (Fin n) (Fin n) K := Matrix.of fun i j => (X i j).snd
private theorem sn_mul {K : Type} [CommRing K] {n : ℕ} (X Y : Matrix (Fin n) (Fin n) (DualNumber K)) :
    sn (X * Y) = X.map (dF K) * sn Y + sn X * Y.map (dF K) := by
  ext a b
  simp only [sn, Matrix.mul_apply, Matrix.of_apply, Matrix.add_apply, Matrix.map_apply, TrivSqZeroExt.snd_sum,
    DualNumber.snd_mul, Finset.sum_add_distrib]
  rfl
private theorem sn_one {K : Type} [CommRing K] {n : ℕ} : sn (1 : Matrix (Fin n) (Fin n) (DualNumber K)) = 0 := by
  ext i j
  by_cases h : i = j <;> simp [sn, Matrix.one_apply, h]
private theorem fx_alg {M : Type} [Ring M] (A0 Ai A1 B1 R Ri y : M) (h1 : A0 * Ai = 1) (h2 : Ai * A0 = 1)
    (h3 : R * Ri = 1) (h4 : A0 * B1 + A1 * Ai = 0) :
    A0 * (y - (R * (Ai * A1) * Ri - Ai * A1)) * Ai = (A0 * (R * B1 + (y * R) * Ai) + A1 * (R * Ai)) * (A0 * Ri * Ai) := by
  have hB : B1 = -(Ai * A1 * Ai) := by
    calc B1 = Ai * (A0 * B1) := by rw [← mul_assoc, h2, one_mul]
      _ = Ai * (-(A1 * Ai)) := by rw [eq_neg_of_add_eq_zero_left h4]
      _ = _ := by noncomm_ring
  subst hB
  have h1' : ∀ x, A0 * (Ai * x) = x := fun x => by rw [← mul_assoc, h1, one_mul]
  have h2' : ∀ x, Ai * (A0 * x) = x := fun x => by rw [← mul_assoc, h2, one_mul]
  have h3' : ∀ x, R * (Ri * x) = x := fun x => by rw [← mul_assoc, h3, one_mul]
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, mul_assoc, h1', h2', h3', h1, h2, h3, mul_one]
  abel
private theorem tri_mul {K : Type} [CommRing K] {n : ℕ} (M N : Matrix (Fin n) (Fin n) K)
    (hM : ∀ i j, j < i → M i j = 0) (hN : ∀ i j, j < i → N i j = 0) :
    (∀ i j, j < i → (M * N) i j = 0) ∧ ∀ i, (M * N) i i = M i i * N i i := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with h | h
    · rw [hM i k h, zero_mul]
    · rw [hN k j (lt_of_lt_of_le hij h), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hM i k h, zero_mul]
      · rw [hN k i h, mul_zero]
    · exact fun h => absurd (Finset.mem_univ i) h
private theorem fx_ord {H K : Type} [Group H] [Field K] {n : ℕ} (I : Subgroup H) (ρ : H →* GL (Fin n) K)
    (y : H → Matrix (Fin n) (Fin n) K) (ρ' : H →* GL (Fin n) (DualNumber K)) (ht : IsTan ρ y ρ')
    (ψ' : Fin n → H →* (DualNumber K)ˣ) (hfl : W.HasFlag ρ' ψ')
    (hI : ∀ g ∈ I, ∀ i, (ψ' i g : DualNumber K).snd = 0) :
    Th.OrdAt I ρ (fun i => W.pushCh (dF K) (ψ' i)) y := by
  obtain ⟨Gm, hG⟩ := hfl
  have hρ : ∀ g, ρ g = Matrix.GeneralLinearGroup.map (dF K) (ρ' g) := fun g =>
    Units.ext (Matrix.ext fun i j => (congrArg TrivSqZeroExt.fst (ht g i j)).symm)
  have hs : ∀ g, sn (ρ' g : Matrix (Fin n) (Fin n) (DualNumber K)) = y g * (ρ g : Matrix (Fin n) (Fin n) K) := fun g =>
    Matrix.ext fun i j => congrArg TrivSqZeroExt.snd (ht g i j)
  set a : GL (Fin n) K := Matrix.GeneralLinearGroup.map (dF K) Gm with ha
  have hai : ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((Gm⁻¹ : GL (Fin n) (DualNumber K)) : Matrix (Fin n) (Fin n) (DualNumber K)).map (dF K) := by
    rw [ha, ← map_inv]; rfl
  have haa : (a : Matrix (Fin n) (Fin n) K) = (Gm : Matrix (Fin n) (Fin n) (DualNumber K)).map (dF K) := rfl
  set A1 := sn (Gm : Matrix (Fin n) (Fin n) (DualNumber K)) with hA1
  set B1 := sn ((Gm⁻¹ : GL (Fin n) (DualNumber K)) : Matrix (Fin n) (Fin n) (DualNumber K)) with hB1
  have h4 : (a : Matrix (Fin n) (Fin n) K) * B1 + A1 * ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 0 := by
    have := sn_mul (Gm : Matrix (Fin n) (Fin n) (DualNumber K)) ((Gm⁻¹ : GL (Fin n) (DualNumber K)) : Matrix (Fin n) (Fin n) (DualNumber K))
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, sn_one] at this
    rw [hai, haa]
    exact this.symm
  let E : H → Matrix (Fin n) (Fin n) (DualNumber K) := fun g => ((Gm * ρ' g * Gm⁻¹ : GL (Fin n) (DualNumber K)) : Matrix (Fin n) (Fin n) (DualNumber K))
  have hE0 : ∀ g, (((a * ρ g * a⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) = (E g).map (dF K) := fun g => by
    rw [hρ g, ha, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hEu : ∀ g i j, j < i → E g i j = 0 := fun g i j h => (hG g).1 i j h
  have hEd : ∀ g i, E g i i = (ψ' i g : DualNumber K) := fun g i => (hG g).2 i
  have hsE : ∀ g, sn (E g) = (a : Matrix (Fin n) (Fin n) K) * ((ρ g : Matrix (Fin n) (Fin n) K) * B1 + (y g * (ρ g : Matrix (Fin n) (Fin n) K)) * ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) +
      A1 * ((ρ g : Matrix (Fin n) (Fin n) K) * ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := fun g => by
    have e : E g = (Gm : Matrix (Fin n) (Fin n) (DualNumber K)) * ((ρ' g : Matrix (Fin n) (Fin n) (DualNumber K)) * ((Gm⁻¹ : GL (Fin n) (DualNumber K)) : Matrix (Fin n) (Fin n) (DualNumber K))) := by
      simp only [E, Units.val_mul, mul_assoc]
    have e2 : (ρ g : Matrix (Fin n) (Fin n) K) = (ρ' g : Matrix (Fin n) (Fin n) (DualNumber K)).map (dF K) := by
      rw [hρ g]; rfl
    rw [e, sn_mul, sn_mul, hs, Matrix.map_mul, ← e2, ← hai, ← haa]
  refine ⟨a, ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A1, fun g => ?_⟩
  have main : (a : Matrix (Fin n) (Fin n) K) * (y g - (Loc.adGL ρ g (((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A1) - ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A1)) * ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      sn (E g) * ((a * ρ g⁻¹ * a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [hsE, map_inv]
    simp only [Units.val_mul]
    exact fx_alg _ _ _ _ _ _ _ (Units.mul_inv a) (Units.inv_mul a) (Units.mul_inv (ρ g)) h4
  have hN : ∀ i j, j < i → ((a * ρ g⁻¹ * a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = 0 := fun i j h => by
    rw [hE0, Matrix.map_apply, hEu _ i j h, map_zero]
  have hT := tri_mul (sn (E g)) _ (fun i j h => by simp [sn, hEu g i j h]) hN
  refine ⟨fun i j h => ?_, fun i => ?_, fun i j h => ?_, fun hg i => ?_⟩
  · change ((a * ρ g * a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = 0
    rw [hE0, Matrix.map_apply, hEu _ i j h, map_zero]
  · change ((a * ρ g * a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i = _
    rw [hE0, Matrix.map_apply, hEd]
    rfl
  · rw [main]
    exact hT.1 i j h
  · rw [main, hT.2 i]
    have : sn (E g) i i = 0 := by
      simp only [sn, Matrix.of_apply, hEd]
      exact hI g hg i
    rw [this, zero_mul]
end Fx
section Tw
open Matrix Ws.Eb
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
  {F : Fr.Frame l (ResidueField O)} {n : ℕ} {G : W.GFrame l} {r : W.Resid G O n} (K : TwLink F r)
include K in
private theorem fx_kk {A : Type} [CommRing A] [Algebra O A] (g : G.G₀) :
    ((K.κA A g : Aˣ) : A) * (K.κA A (G.conj g) : Aˣ) = ((G.eps O A g ^ (1 - (n : ℤ)) : Aˣ) : A) := by
  have h := congrArg (Units.map (algebraMap O A : O →* A)) (K.κ_conj g)
  rw [map_mul, map_zpow] at h
  exact congrArg Units.val h
private theorem fx_form {A : Type} [CommRing A] [Algebra O A] (ρ : Fr.NRep F n A) :
    G.IsForm O n (K.tw ρ).toHomUnits (Jgl A n) := fun g => by
  have h1 : (ρ.r (K.π g))ᵀ * Jmat A n * ρ.r (F.conj (K.π g)) = Jmat A n := by
    have e : ρ.r (F.star (K.π g)) * ρ.r (F.conj (K.π g)) = 1 := by
      rw [← map_mul, Fr.Frame.star, map_inv, inv_mul_cancel, map_one]
    rw [ρ.pol] at e
    calc _ = Jmat A n * (Jmat A n * (ρ.r (K.π g))ᵀ * Jmat A n * ρ.r (F.conj (K.π g))) := by
          simp only [← Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.one_mul]
      _ = _ := by rw [e, Matrix.mul_one]
  change (((K.κA A g : Aˣ) : A) • ρ.r (K.π g))ᵀ * Jmat A n * (((K.κA A (G.conj g) : Aˣ) : A) • ρ.r (K.π (G.conj g))) = _ • Jmat A n
  rw [K.π_conj, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, h1, smul_smul,
    mul_comm ((K.κA A (G.conj g) : Aˣ) : A), fx_kk K g]
private theorem fx_ad {Q : Type} [Field Q] [Algebra O Q] (ρ : Fr.NRep F n Q) (g : G.G₀) (M : Matrix (Fin n) (Fin n) Q) :
    Loc.adGL (K.tw ρ).toHomUnits g M = ρ.r (K.π g) * M * ρ.r (K.π g)⁻¹ := by
  have e : (((K.tw ρ).toHomUnits g)⁻¹ : GL (Fin n) Q) = (K.tw ρ).toHomUnits g⁻¹ := (map_inv _ _).symm
  change ((K.tw ρ).toHomUnits g : Matrix (Fin n) (Fin n) Q) * M * (((K.tw ρ).toHomUnits g)⁻¹ : GL (Fin n) Q) = _
  rw [e]
  change (((K.κA Q g : Qˣ) : Q) • ρ.r (K.π g)) * M * (((K.κA Q g⁻¹ : Qˣ) : Q) • ρ.r (K.π g⁻¹)) = _
  rw [map_inv K.π, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, map_inv (K.κA Q), Units.mul_inv, one_smul]
variable {Q : Type} [Field Q] [Algebra O Q]
private noncomputable def fxY (ρD : Fr.NRep F n (DualNumber Q)) (g : G.G₀) : Matrix (Fin n) (Fin n) Q :=
  sn (ρD.r (K.π g)) * (ρD.map (dF Q)).r (K.π g)⁻¹
private theorem fx_rr (ρ : Fr.NRep F n Q) (h : F.G0) : ρ.r h⁻¹ * ρ.r h = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]
private theorem fx_rr' (ρ : Fr.NRep F n Q) (h : F.G0) : ρ.r h * ρ.r h⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]
private theorem fx_tan (ρD : Fr.NRep F n (DualNumber Q)) :
    IsTan (K.tw (ρD.map (dF Q))).toHomUnits (fxY K ρD) (K.tw ρD).toHomUnits := fun g i j => by
  have e : ((K.tw (ρD.map (dF Q))).toHomUnits g : Matrix (Fin n) (Fin n) Q) =
      ((K.κA Q g : Qˣ) : Q) • (ρD.map (dF Q)).r (K.π g) := rfl
  have e2 : fxY K ρD g * (ρD.map (dF Q)).r (K.π g) = sn (ρD.r (K.π g)) := by
    rw [fxY, Matrix.mul_assoc, fx_rr, Matrix.mul_one]
  rw [e, Matrix.mul_smul, e2]
  refine TrivSqZeroExt.ext rfl ?_
  change (((K.κA (DualNumber Q) g : (DualNumber Q)ˣ) : DualNumber Q) * ρD.r (K.π g) i j).snd = ((K.κA Q g : Qˣ) : Q) * (ρD.r (K.π g) i j).snd
  rw [DualNumber.snd_mul]
  have : (((K.κA (DualNumber Q) g : (DualNumber Q)ˣ) : DualNumber Q)).snd = 0 := rfl
  rw [this, zero_mul, add_zero]
  rfl
private theorem fx_coc (ρD : Fr.NRep F n (DualNumber Q)) (a b : G.G₀) :
    fxY K ρD (a * b) = fxY K ρD a + Loc.adGL (K.tw (ρD.map (dF Q))).toHomUnits a (fxY K ρD b) := by
  have hm : ∀ h, (ρD.r h).map (dF Q) = (ρD.map (dF Q)).r h := fun _ => rfl
  rw [fx_ad]
  simp only [fxY]
  rw [map_mul K.π, map_mul ρD.r, sn_mul, _root_.mul_inv_rev, map_mul (ρD.map (dF Q)).r, hm, hm, add_mul, add_comm]
  congr 1
  · rw [← Matrix.mul_assoc, Matrix.mul_assoc _ ((ρD.map (dF Q)).r (K.π b)), fx_rr', Matrix.mul_one]
  · simp only [Matrix.mul_assoc]
end Tw
section Core
open Matrix Ws.Eb
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
  {F : Fr.Frame l (ResidueField O)} {n : ℕ} {G : W.GFrame l} {r : W.Resid G O n} (K : TwLink F r)
  {Q : Type} [Field Q] [Algebra O Q]
private theorem fx_psi (ρD : Fr.NRep F n (DualNumber Q)) (v : G.Vl) :
    K.twψ (ρD.map (dF Q)) v = fun i => W.pushCh (dF Q) (K.twψ ρD v i) :=
  funext fun i => MonoidHom.ext fun g => Units.ext (map_mul (dF Q) (ρD.ψ (K.e v) i (K.lam v g) : DualNumber Q)
    ((K.κA (DualNumber Q) (G.φ v g) : (DualNumber Q)ˣ) : DualNumber Q)).symm
private theorem fx_snd (ρD : Fr.NRep F n (DualNumber Q)) (v : G.Vl) (i : Fin n) (g : G.Gv v)
    (h : (ρD.ψ (K.e v) i (K.lam v g) : DualNumber Q).snd = 0) : (K.twψ ρD v i g : DualNumber Q).snd = 0 := by
  change ((ρD.ψ (K.e v) i (K.lam v g) : DualNumber Q) * ((K.κA (DualNumber Q) (G.φ v g) : (DualNumber Q)ˣ) : DualNumber Q)).snd = 0
  rw [DualNumber.snd_mul, h, zero_mul, add_zero]
  exact mul_zero _
private theorem fx_twflag {A : Type} [CommRing A] [Algebra O A] (ρ : Fr.NRep F n A) (v : G.Vl)
    (h : W.HasFlag (ρ.r.comp (F.loc0 (K.e v))).toHomUnits (ρ.ψ (K.e v))) :
    W.HasFlag ((K.tw ρ).toHomUnits.comp (G.φ v)) (K.twψ ρ v) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, fun s => ?_⟩
  have key : ∀ i j, (a * ((K.tw ρ).toHomUnits.comp (G.φ v)) s * a⁻¹ : GL (Fin n) A) i j =
      ((K.κA A (G.φ v s) : Aˣ) : A) * (a * (ρ.r.comp (F.loc0 (K.e v))).toHomUnits (K.lam v s) * a⁻¹ : GL (Fin n) A) i j := fun i j => by
    change ((a : Matrix (Fin n) (Fin n) A) * (((K.κA A (G.φ v s) : Aˣ) : A) • ρ.r (K.π (G.φ v s))) *
      ((a⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)) i j =
      _ * ((a : Matrix (Fin n) (Fin n) A) * ρ.r (F.loc0 (K.e v) (K.lam v s)) * ((a⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)) i j
    rw [K.lam_loc, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [key, (ha _).1 i j hij, mul_zero]
  · rw [key, (ha _).2 i, mul_comm]
    rfl
variable [CharZero Q] [IsAlgClosed Q] [TopologicalSpace Q] [IsTopologicalRing Q]
private theorem fx_core (ρD : Fr.NRep F n (DualNumber Q))
    (hrc : ∀ i j, Continuous fun h => (ρD.r h i j).fst) (hsc : ∀ i j, Continuous fun h => (ρD.r h i j).snd)
    (hcont : Continuous (K.tw (ρD.map (dF Q))).toHomUnits)
    (hirr : MatIrr ⊤ (W.mat (K.tw (ρD.map (dF Q))).toHomUnits))
    (hine : ∀ u, ∀ g ∈ r.Ip u, K.tw ρD g = 1)
    (hfl : ∀ v, W.HasFlag (ρD.r.comp (F.loc0 v)).toHomUnits (ρD.ψ v))
    (hI : ∀ v i, ∀ g ∈ F.Iv v, (ρD.ψ v i g : DualNumber Q).snd = 0)
    (hZ : ∀ (P : GL (Fin n) Q) (R : Representation Q G.Γ (Matrix (Fin n) (Fin n) Q)),
      G.IsForm O n (K.tw (ρD.map (dF Q))).toHomUnits P → IsAdExt G (K.tw (ρD.map (dF Q))).toHomUnits P R →
      ∀ z ∈ Z1 R, Th.OrdCoc r (K.tw (ρD.map (dF Q))).toHomUnits (K.twψ (ρD.map (dF Q))) z → ∃ X, ∀ g, z g = R g X - X) :
    ∃ X : Matrix (Fin n) (Fin n) Q, ∀ h, sn (ρD.r h) = X * (ρD.map (dF Q)).r h - (ρD.map (dF Q)).r h * X := by
  have ht := fx_tan K ρD
  have hfull : Full (K.tw (ρD.map (dF Q))).toHomUnits :=
    (AlgebraTools.Det.irrIffSpan (W.mat (K.tw (ρD.map (dF Q))).toHomUnits)).1 fun N hN => hirr N fun g _ v hv => hN g v hv
  have c1 : Continuous fun g : G.G₀ => sn (ρD.r (K.π g)) :=
    continuous_matrix fun i j => (hsc i j).comp K.π_cont
  have c2 : Continuous fun g : G.G₀ => (ρD.map (dF Q)).r (K.π g)⁻¹ :=
    continuous_matrix fun i j => (hrc i j).comp (K.π_cont.inv)
  have hy : fxY K ρD ∈ Z1 (Loc.adGL (K.tw (ρD.map (dF Q))).toHomUnits) := ⟨c1.matrix_mul c2, fx_coc K ρD⟩
  obtain ⟨hP, hrel⟩ := cocRel G O _ (fxY K ρD) (K.tw ρD).toHomUnits (Jgl _ n) ht (fx_form K ρD)
  obtain ⟨R, hR⟩ := adExt G O _ _ hfull hP
  obtain ⟨Z, hZ'⟩ := hrel R hR
  obtain ⟨z, hz, hzy⟩ := cocExt G _ _ R hfull hcont hR _ hy Z hZ'
  have hs : ∀ g : G.G₀, sn ((K.tw ρD).toHomUnits g : Matrix (Fin n) (Fin n) (DualNumber Q)) =
      fxY K ρD g * ((K.tw (ρD.map (dF Q))).toHomUnits g).val := fun g =>
    Matrix.ext fun i j => congrArg TrivSqZeroExt.snd (ht g i j)
  have hoc : Th.OrdCoc r (K.tw (ρD.map (dF Q))).toHomUnits (K.twψ (ρD.map (dF Q))) z := by
    refine ⟨fun u g hg => ?_, fun v => ?_⟩
    · rw [hzy]
      have e := hs g
      have e1 : ((K.tw ρD).toHomUnits g : Matrix (Fin n) (Fin n) (DualNumber Q)) = 1 := hine u g hg
      rw [e1, sn_one] at e
      have e3 := congrArg (· * (((K.tw (ρD.map (dF Q))).toHomUnits g)⁻¹ : GL (Fin n) Q).val) e
      simpa only [Matrix.zero_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] using e3.symm
    · have h := fx_ord (G.Iv v) ((K.tw (ρD.map (dF Q))).toHomUnits.comp (G.φ v)) _ _ (ht.comp (G.φ v)) (K.twψ ρD v)
        (fx_twflag K ρD v (hfl _)) fun g hg i => fx_snd K ρD v i g (hI _ i _ ((K.lam_I v g).2 hg))
      rw [← fx_psi] at h
      simpa only [hzy] using h
  obtain ⟨X, hX⟩ := hZ _ R hP hR z hz hoc
  refine ⟨-X, fun h => ?_⟩
  obtain ⟨g, rfl⟩ := K.π_surj h
  have h1 : fxY K ρD g = (ρD.map (dF Q)).r (K.π g) * X * (ρD.map (dF Q)).r (K.π g)⁻¹ - X := by
    rw [← hzy, hX, hR.ad, fx_ad]
  have e2 : sn (ρD.r (K.π g)) = fxY K ρD g * (ρD.map (dF Q)).r (K.π g) := by
    rw [fxY, Matrix.mul_assoc, fx_rr, Matrix.mul_one]
  rw [e2, h1, Matrix.sub_mul, Matrix.mul_assoc _ _ ((ρD.map (dF Q)).r (K.π g)), fx_rr, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg]
  abel
end Core
section Sp
open Matrix Ws.Eb
private noncomputable def fxD {O A Q : Type} [CommRing O] [CommRing A] [Algebra O A] [Field Q] [Algebra O Q]
    (ξ : A →ₐ[O] Q) (D : A →ₗ[O] Q) (hD : D ∈ PtDer ξ Q) : A →ₐ[O] DualNumber Q :=
  have h1 : D 1 = 0 := by
    have h := hD 1 1
    rw [mul_one, map_one ξ, one_smul] at h
    exact left_eq_add.1 h
  { toFun := fun a => ⟨ξ a, D a⟩
    map_one' := TrivSqZeroExt.ext (map_one ξ) h1
    map_mul' := fun a b => TrivSqZeroExt.ext (map_mul ξ a b) (by
      refine Eq.trans ?_ (DualNumber.snd_mul _ _).symm
      change D (a * b) = ξ a * D b + D a * ξ b
      rw [mul_comm (D a)]
      exact hD a b)
    map_zero' := TrivSqZeroExt.ext (map_zero ξ) (map_zero D)
    map_add' := fun a b => TrivSqZeroExt.ext (map_add ξ a b) (map_add D a b)
    commutes' := fun a => TrivSqZeroExt.ext (ξ.commutes a) (by
      change D (algebraMap O A a) = 0
      rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]) }
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
  {F : Fr.Frame l (ResidueField O)} {n : ℕ} {G : W.GFrame l} {r : W.Resid G O n} (K : TwLink F r)
private theorem fx_ine [CharP (ResidueField O) l] {A : Type} [CommRing A] [Algebra O A] [IsCO O A] {ρ : Fr.NRep F n A}
    (h : Fr.IsLift O ρ) (u : G.St) (g : G.G₀) (hg : g ∈ r.Ip u) : K.tw ρ g = 1 := by
  obtain ⟨m, hm, h1, h2⟩ := K.tame u g hg.1
  have hχ : ∀ i, r.chib i g = 1 := fun i => (Subgroup.mem_iInf.1 hg.2) i
  have h3 : ∀ i j, res O A (K.tw ρ g i j - (1 : Matrix (Fin n) (Fin n) A) i j) = 0 := fun i j => by
    have e : K.tw ρ g i j = algebraMap O A (K.κ g) * ρ.r (K.π g) i j := rfl
    rw [map_sub, e, map_mul, AlgHom.commutes]
    by_cases hij : i = j
    · subst hij
      have e1 := congrArg Units.val ((K.chib i g).symm.trans (hχ i))
      have e2 : res O A (ρ.r (K.π g) i i) = ((F.Ψ (K.π g) ^ Fr.w n i : (ResidueField O)ˣ) : ResidueField O) :=
        h.2.1.1 (K.π g) i
      rw [e2, Matrix.one_apply_eq, map_one, mul_comm, sub_eq_zero]
      exact e1
    · have e2 : res O A (ρ.r (K.π g) i j) = 0 := h.2.2 (K.π g) i j hij
      rw [e2, Matrix.one_apply_ne hij, map_zero, mul_zero, sub_zero]
  have h4 : (K.tw ρ g).map (residue A) = 1 := by
    ext i j
    have h5 := h3 i j
    rw [res_eq_zero_iff, ← residue_eq_zero_iff, map_sub, sub_eq_zero] at h5
    refine h5.trans ?_
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  refine Pr.T.unipTorsion (A := A) (K.tw ρ g) (K.tw ρ g).charpoly n m (Matrix.charpoly_monic _)
    (Matrix.aeval_self_charpoly _) ?_ ?_ ?_
  · rw [← Matrix.charpoly_map, h4, Matrix.charpoly_one, Fintype.card_fin]
  · by_contra hn
    have h5 := (res_eq_zero_iff O A _).2 hn
    rw [map_natCast, CharP.cast_eq_zero_iff _ l] at h5
    exact hm h5
  · rw [← map_pow]
    have e : K.κA A (g ^ m) = 1 := by
      change Units.map _ (K.κ (g ^ m)) = 1
      rw [map_pow, h2, map_one]
    change ((K.κA A (g ^ m) : Aˣ) : A) • ρ.r (K.π (g ^ m)) = 1
    rw [e, map_pow K.π, h1, map_one, Units.val_one, one_smul]
private theorem fx_ineS [CharP (ResidueField O) l] {C : Type} [CommRing C] [Algebra O C] (S : Fr.Space O F n)
    (φ : S.A →ₐ[O] C) (u : G.St) (g : G.G₀) (hg : g ∈ r.Ip u) : K.tw (S.u.map (φ : S.A →+* C)) g = 1 := by
  have h := fx_ine K S.lift u g hg
  ext i j
  have h2 : ((algebraMap O S.A (K.κ g) * S.u.r (K.π g) i j : S.A) : S.R) = (1 : Matrix (Fin n) (Fin n) S.R) i j :=
    congrFun (congrFun h i) j
  have h1 : algebraMap O S.A (K.κ g) * S.u.r (K.π g) i j = (1 : Matrix (Fin n) (Fin n) S.A) i j := Subtype.ext (by
    rw [h2]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij])
  change algebraMap O C (K.κ g) * φ (S.u.r (K.π g) i j) = _
  rw [← φ.commutes, ← map_mul, h1]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
end Sp
theorem UpperTheory.V.J.fixOf_alt :
    _root_.UpperTheory.V.Th.DenseThresholdMainCase → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
        [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
        (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
        ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
        (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
        (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O)
        (ka : G L Ω →* (Qbar l)ˣ) (R : CReal k c₁ f 3 ka), W.Large L c₁ → IsKa σ M ι 3 ka →
        ∀ (ξ : R.S.A →ₐ[c₁.O] Qbar l) (x : R.B₀.Pt), IntPt R.S ξ → _root_.UpperTheory.V.Th.AutomorphicPointLocallyGeneric ι x (R.K.tw (ptRep R.S ξ)).toHomUnits →
          (∀ v, x.psi v = R.K.twψ (ptRep R.S ξ) v) → ∀ D ∈ FixTan R.S ξ,
          ∃ X : Matrix (Fin 3) (Fin 3) (Qbar l), ∀ g, (R.S.u.r g).map D = X * (ptRep R.S ξ).r g - (ptRep R.S ξ).r g * X := by
  intro hC Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ k c₁ _ f ka R hL hka ξ x hξ hN hψ D hD
  have hV : Nonempty Φ.V := by
    by_contra hV
    rw [not_nonempty_iff] at hV
    have h : _ < Φ.d := R.big.1
    simp [Fr.Frame.d] at h
  obtain ⟨v'⟩ := hV
  have hroot := (degEq Ω l ι c N e ψ η σ g₁ B M H L Φ k v').2
  obtain ⟨hrc, hsc, -⟩ := derRep l c₁ (Φ.ext f) R.C₀ 3 R.ok (Or.inr rfl) R.S ξ hξ D hD.1
  have hZ : Th.OrdZero R.r (R.K.tw (ptRep R.S ξ)).toHomUnits (R.K.twψ (ptRep R.S ξ)) := by
    have e : R.K.twψ (ptRep R.S ξ) = fun v => x.psi v := funext fun v => (hψ v).symm
    rw [e]
    exact hC l L Ω R.s R.V R.hV hroot c₁ hL 3 (by omega) (by omega) R.r R.v0 R.B₀ ι x _ hN
  exact fx_core R.K (R.S.u.map (fxD ξ D hD.1 : R.S.A →+* DualNumber (Qbar l))) hrc hsc hN.cont
    (fun U hU => hN.irr U fun g _ v hv => hU g trivial v hv) (fun u g hg => fx_ineS R.K R.S _ u g hg)
    (fun v => Fr.flag R.ok (Or.inr rfl) R.S _ _ v) (fun v i g hg => hD.2 v i g hg) hZ
end
