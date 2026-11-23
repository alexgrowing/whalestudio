import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.HomMu
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSqz
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

namespace UpperTheory.V.Th.Nm

section Cont

variable {G R : Type} [TopologicalSpace G] [CommRing R] {I : Ideal R} {n : ℕ}

private theorem ac_const (a : R) : AdicCont I fun _ : G => a := fun _ => IsLocallyConstant.const _

private theorem ac_add {f g : G → R} (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun x => f x + g x := fun N => by
  simp only [map_add]; exact (hf N).add (hg N)

private theorem ac_sub {f g : G → R} (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun x => f x - g x := fun N => by
  simp only [map_sub]; exact (hf N).sub (hg N)

private theorem ac_mul {f g : G → R} (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun x => f x * g x := fun N => by
  simp only [map_mul]; exact (hf N).mul (hg N)

private theorem ac_sum {ι : Type} (s : Finset ι) (f : ι → G → R) (hf : ∀ k, AdicCont I (f k)) :
    AdicCont I fun x => ∑ k ∈ s, f k x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ac_const (G := G) (I := I) 0
  | insert a s ha ih => simp only [Finset.sum_insert ha]; exact ac_add (hf a) ih

private theorem ac_comp {H : Type} [TopologicalSpace H] {f : G → R} (hf : AdicCont I f) {p : H → G} (hp : Continuous p) :
    AdicCont I fun x => f (p x) := fun N => (hf N).comp_continuous hp

private theorem ac_map {S : Type} [CommRing S] {J : Ideal S} (q : R →+* S) (hq : I ≤ J.comap q) {f : G → R}
    (hf : AdicCont I f) : AdicCont J fun x => q (f x) := fun N =>
  (hf N).comp (Ideal.quotientMap (J ^ N) q ((Ideal.pow_right_mono hq N).trans (Ideal.le_comap_pow q N)))

private def MC (I : Ideal R) (f : G → Matrix (Fin n) (Fin n) R) : Prop := ∀ i j, AdicCont I fun g => f g i j

private theorem mc_const (a : Matrix (Fin n) (Fin n) R) : MC I fun _ : G => a := fun _ _ => ac_const _

private theorem mc_sub {f g : G → Matrix (Fin n) (Fin n) R} (hf : MC I f) (hg : MC I g) : MC I fun x => f x - g x :=
  fun i j => ac_sub (hf i j) (hg i j)

private theorem mc_mul {f g : G → Matrix (Fin n) (Fin n) R} (hf : MC I f) (hg : MC I g) : MC I fun x => f x * g x :=
  fun i j => by
    simp only [Matrix.mul_apply]
    exact ac_sum _ (fun k x => f x i k * g x k j) fun k => ac_mul (hf i k) (hg k j)

private theorem mc_comp {H : Type} [TopologicalSpace H] {f : G → Matrix (Fin n) (Fin n) R} (hf : MC I f) {p : H → G}
    (hp : Continuous p) : MC I fun x => f (p x) := fun i j => ac_comp (hf i j) hp

end Cont

section Tri

variable {R : Type} [CommRing R] {n : ℕ} {A B : Matrix (Fin n) (Fin n) R}

private theorem ut_mul (hA : ∀ i j, j < i → A i j = 0) (hB : ∀ i j, j < i → B i j = 0) (i j : Fin n) (h : j < i) :
    (A * B) i j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge k i with hk | hk
  · rw [hA _ _ hk, zero_mul]
  · rw [hB _ _ (h.trans_le hk), mul_zero]

private theorem ut_diag (hA : ∀ i j, j < i → A i j = 0) (hB : ∀ i j, j < i → B i j = 0) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
  rcases lt_or_gt_of_ne hk with hk | hk
  · rw [hA _ _ hk, zero_mul]
  · rw [hB _ _ hk, mul_zero]

end Tri

section Du

variable {O : Type} [CommRing O] {n : ℕ}

private def du (A B : Matrix (Fin n) (Fin n) O) : Matrix (Fin n) (Fin n) (DualNumber O) :=
  Matrix.of fun i j => TrivSqZeroExt.inl (A i j) + TrivSqZeroExt.inr (B i j)

private theorem du_fst (A B : Matrix (Fin n) (Fin n) O) (i j : Fin n) : (du A B i j).fst = A i j := by simp [du]

private theorem du_snd (A B : Matrix (Fin n) (Fin n) O) (i j : Fin n) : (du A B i j).snd = B i j := by simp [du]

private theorem du_mul (A B C D : Matrix (Fin n) (Fin n) O) : du A B * du C D = du (A * C) (A * D + B * C) := by
  ext i j
  · simp [Matrix.mul_apply, TrivSqZeroExt.fst_sum, du_fst]
  · simp [Matrix.mul_apply, TrivSqZeroExt.snd_sum, du_fst, du_snd, Finset.sum_add_distrib, mul_comm]

private theorem du_one : du (1 : Matrix (Fin n) (Fin n) O) 0 = 1 := by
  ext i j
  · rw [du_fst]; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · rw [du_snd]; by_cases h : i = j <;> simp [Matrix.one_apply, h]

private theorem du_tr (A B : Matrix (Fin n) (Fin n) O) : (du A B)ᵀ = du Aᵀ Bᵀ := rfl

private theorem du_smul (a : O) (A : Matrix (Fin n) (Fin n) O) :
    algebraMap O (DualNumber O) a • du A 0 = du (a • A) 0 := by
  ext i j
  · simp [du_fst, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [du_snd, du_fst, TrivSqZeroExt.algebraMap_eq_inl]

private theorem du_trace (A B : Matrix (Fin n) (Fin n) O) : (du A B).trace.snd = B.trace := by
  simp [Matrix.trace, TrivSqZeroExt.snd_sum, du_snd]

private theorem mc_du {G : Type} [TopologicalSpace G] [IsLocalRing O] [IsLocalRing (DualNumber O)]
    {A B : G → Matrix (Fin n) (Fin n) O} (hA : MC (maximalIdeal O) A) (hB : MC (maximalIdeal O) B) :
    MC (maximalIdeal (DualNumber O)) fun g => du (A g) (B g) := fun i j => by
  have hq : maximalIdeal O ≤ (maximalIdeal (DualNumber O)).comap (algebraMap O (DualNumber O)) := fun a ha hu =>
    ha (by simpa [TrivSqZeroExt.algebraMap_eq_inl] using TrivSqZeroExt.isUnit_iff_isUnit_fst.1 hu)
  have := ac_add (ac_map _ hq (hA i j)) (ac_mul (ac_map _ hq (hB i j)) (ac_const (DualNumber.eps : DualNumber O)))
  convert this using 2 with g
  ext
  · simp [du_fst, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [du_snd, TrivSqZeroExt.algebraMap_eq_inl]

private def duU (w : GL (Fin n) O) (A : Matrix (Fin n) (Fin n) O) : GL (Fin n) (DualNumber O) where
  val := du (w : Matrix (Fin n) (Fin n) O) (A * w)
  inv := du ((w⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) (-(((w⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * A))
  val_inv := by
    rw [du_mul, Units.mul_inv, ← du_one]
    congr 1
    rw [mul_neg, ← mul_assoc, Units.mul_inv, mul_assoc, Units.mul_inv]; simp
  inv_val := by
    rw [du_mul, Units.inv_mul, ← du_one]
    congr 1
    rw [neg_mul, mul_assoc]; simp

end Du

section Main

variable {O : Type} [CommRing O] {n : ℕ}

private theorem mat_inv {G : Type} [Group G] (ρ : G →* GL (Fin n) O) (g : G) : mat ρ g⁻¹ * mat ρ g = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

private def duRep {G : Type} [Group G] (ρ : G →* GL (Fin n) O) (z : G → Matrix (Fin n) (Fin n) O)
    (hz : ∀ g g', z (g * g') = z g + mat ρ g * z g' * mat ρ g⁻¹) : G →* GL (Fin n) (DualNumber O) :=
  MonoidHom.toHomUnits
    { toFun := fun g => du (mat ρ g) (z g * mat ρ g)
      map_one' := by
        have h := hz 1 1
        simp only [mul_one, inv_one, map_one, one_mul, left_eq_add] at h
        rw [h, map_one, zero_mul, du_one]
      map_mul' := fun g h => by
        rw [du_mul, hz, map_mul, add_mul, add_comm]
        congr 2
        · rw [mul_assoc, ← mul_assoc (mat ρ g⁻¹), mat_inv, one_mul, mul_assoc]
        · rw [mul_assoc] }

private theorem mat_duRep {G : Type} [Group G] (ρ : G →* GL (Fin n) O) (z : G → Matrix (Fin n) (Fin n) O)
    (hz : ∀ g g', z (g * g') = z g + mat ρ g * z g' * mat ρ g⁻¹) (g : G) :
    mat (duRep ρ z hz :) g = du (mat ρ g) (z g * mat ρ g) :=
  MonoidHom.coe_toHomUnits _ g

private theorem duU_val (w : GL (Fin n) O) (A : Matrix (Fin n) (Fin n) O) :
    (duU w A).val = du w.val (A * w.val) := rfl

private theorem duU_inv (w : GL (Fin n) O) (A : Matrix (Fin n) (Fin n) O) :
    ((duU w A)⁻¹).val = du (w⁻¹).val (-((w⁻¹).val * A)) := rfl

private theorem conj_duRep {G : Type} [Group G] (ρ : G →* GL (Fin n) O) (z : G → Matrix (Fin n) (Fin n) O)
    (hz : ∀ g g', z (g * g') = z g + mat ρ g * z g' * mat ρ g⁻¹) (w : GL (Fin n) O) (Y : Matrix (Fin n) (Fin n) O) (g : G) :
    (((duU w (-Y))⁻¹ * duRep ρ z hz g * duU w (-Y) : GL (Fin n) (DualNumber O)) : Matrix (Fin n) (Fin n) (DualNumber O)) =
      du (w⁻¹ * ρ g * w : GL (Fin n) O) ((((w⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) *
        (z g - (mat ρ g * Y * mat ρ g⁻¹ - Y)) * (w : Matrix (Fin n) (Fin n) O)) *
        ((w⁻¹ * ρ g * w : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)) := by
  have e1 : (duRep ρ z hz g).val = du (mat ρ g) (z g * mat ρ g) := mat_duRep ρ z hz g
  have e2 : (ρ g).val = mat ρ g := rfl
  simp only [Units.val_mul]
  rw [e1, e2, duU_val, duU_inv, du_mul, du_mul]
  congr 1
  have h1 : ∀ X : Matrix (Fin n) (Fin n) O,
      (w : Matrix (Fin n) (Fin n) O) * (((w⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * X) = X := fun X => by
    rw [← mul_assoc, Units.mul_inv, one_mul]
  have h2 : ∀ X : Matrix (Fin n) (Fin n) O, mat ρ g⁻¹ * (mat ρ g * X) = X := fun X => by
    rw [← mul_assoc, mat_inv, one_mul]
  simp only [mul_assoc, mul_sub, sub_mul, add_mul, mul_neg, neg_mul, neg_neg, h1, h2]
  abel

private def diagCh {G R : Type} [Group G] [CommRing R] (τ : G →* GL (Fin n) R)
    (h : ∀ g i j, j < i → (τ g : GL (Fin n) R) i j = 0) (i : Fin n) : G →* Rˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => (τ g : GL (Fin n) R) i i
      map_one' := by simp
      map_mul' := fun g g' => by
        rw [map_mul, Units.val_mul]
        exact ut_diag (h g) (h g') i }

private theorem diagCh_val {G R : Type} [Group G] [CommRing R] (τ : G →* GL (Fin n) R)
    (h : ∀ g i j, j < i → (τ g : GL (Fin n) R) i j = 0) (i : Fin n) (g : G) :
    (diagCh τ h i g).val = (τ g).val i i := MonoidHom.coe_toHomUnits _ g

end Main

private theorem dualRep_gen :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (y : Pt F O n) (z : F.G₀ → Matrix (Fin n) (Fin n) O) [IsLocalRing (DualNumber O)], (∀ v (d : F.Gv v → O), AdicCont (maximalIdeal O) d → (∀ g h, d (g * h) = d g + d h) → ∀ g ∈ F.mu v, d g = 0) → OCoc y z → ∃ (ρ' : F.G₀ →* GL (Fin n) (DualNumber O)) (P' : GL (Fin n) (DualNumber O)) (ψ' : ∀ v, Fin n → F.Gv v →* (DualNumber O)ˣ), (∀ i j, AdicCont (maximalIdeal (DualNumber O)) fun g => mat ρ' g i j) ∧ F.IsForm O n ρ' P' ∧ (∀ v, HasFlag (ρ'.comp (F.φ v)) (ψ' v)) ∧ (∀ u, ∀ g ∈ F.Iu u, ρ' g = 1) ∧ pushRep (TrivSqZeroExt.fstHom O O O : DualNumber O →+* O) ρ' = y.ρ ∧ (∀ g, (mat ρ' g).trace.snd = (z g * mat y.ρ g).trace) ∧ ∀ v i, pushCh (TrivSqZeroExt.fstHom O O O : DualNumber O →+* O) (ψ' v i) = y.ψ v i ∧ (AdicCont (maximalIdeal (DualNumber O)) fun g => ((ψ' v i g : (DualNumber O)ˣ) : DualNumber O)) ∧ ∀ g, g ∈ F.Iv v ∨ g ∈ F.mu v → ((ψ' v i g : (DualNumber O)ˣ) : DualNumber O).snd = 0 := by
  intro l _ n F O _ _ _ y z _ hmu hz
  choose Y hY using hz.ord
  let b : ∀ v, F.Gv v → Matrix (Fin n) (Fin n) O := fun v g =>
    (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) *
      (z (F.φ v g) - dY F (mat y.ρ) (Y v) (F.φ v g)) * (y.w v : Matrix (Fin n) (Fin n) O)
  let T : ∀ v, F.Gv v → Matrix (Fin n) (Fin n) O := fun v g => ((y.w v)⁻¹ * y.ρ (F.φ v g) * y.w v : GL (Fin n) O)
  let τ : ∀ v, F.Gv v →* GL (Fin n) (DualNumber O) := fun v =>
    cj (duU (y.w v) (-Y v)) ((duRep y.ρ z hz.coc).comp (F.φ v))
  have hτ : ∀ v g, (τ v g : Matrix (Fin n) (Fin n) (DualNumber O)) = du (T v g) (b v g * T v g) := fun v g => by
    simp only [τ, cj_apply]
    exact conj_duRep y.ρ z hz.coc (y.w v) (Y v) (F.φ v g)
  have hut : ∀ v g i j, j < i → (τ v g : GL (Fin n) (DualNumber O)) i j = 0 := fun v g i j h => by
    rw [hτ]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [du_fst]; exact (hY v g).1 i j h
    · rw [du_snd]; exact ut_mul (hY v g).2.2.1 (hY v g).1 i j h
  have hfst : ∀ v i g, ((diagCh (τ v) (hut v) i g : (DualNumber O)ˣ) : DualNumber O).fst = (y.ψ v i g : O) :=
    fun v i g => by
      rw [diagCh_val, hτ, du_fst]; exact (hY v g).2.1 i
  have hsnd : ∀ v i g, ((diagCh (τ v) (hut v) i g : (DualNumber O)ˣ) : DualNumber O).snd =
      b v g i i * (y.ψ v i g : O) := fun v i g => by
    rw [diagCh_val, hτ, du_snd, ut_diag (hY v g).2.2.1 (hY v g).1, (hY v g).2.1 i]
  have cρ : MC (maximalIdeal O) fun g => mat y.ρ g := y.cont
  have cz : MC (maximalIdeal O) z := hz.cont
  have cb : ∀ v, MC (maximalIdeal O) (b v) := fun v =>
    mc_mul (mc_mul (mc_const _) (mc_comp (mc_sub cz (mc_sub (mc_mul (mc_mul cρ (mc_const _))
      (mc_comp cρ continuous_inv)) (mc_const _))) (F.φ_cont v))) (mc_const _)
  have cT : ∀ v, MC (maximalIdeal O) (T v) := fun v =>
    mc_mul (mc_mul (mc_const _) (mc_comp cρ (F.φ_cont v))) (mc_const _)
  refine ⟨duRep y.ρ z hz.coc, duU y.P 0, fun v => diagCh (τ v) (hut v), fun i j => ?_, fun g => ?_,
    fun v => ⟨(duU (y.w v) (-Y v))⁻¹, fun g => ?_⟩, fun u g hg => ?_, ?_, fun g => ?_, fun v i => ⟨?_, ?_, fun g hg => ?_⟩⟩
  · simp only [mat_duRep]
    exact mc_du cρ (mc_mul cz cρ) i j
  · have he : ((F.eps O (DualNumber O) g ^ (1 - (n : ℤ)) : (DualNumber O)ˣ) : DualNumber O) =
        algebraMap O (DualNumber O) ((F.eps O O g ^ (1 - (n : ℤ)) : Oˣ) : O) := by
      have : F.eps O (DualNumber O) g = Units.map (algebraMap O (DualNumber O) : O →* DualNumber O)
          (F.eps O O g) := Units.ext rfl
      rw [this, ← map_zpow]; rfl
    have hP : ((duU y.P 0 : GL (Fin n) (DualNumber O)) : Matrix (Fin n) (Fin n) (DualNumber O)) =
        du (y.P : Matrix (Fin n) (Fin n) O) 0 := by
      rw [duU_val, zero_mul]
    rw [he, hP, mat_duRep, mat_duRep, du_tr, du_mul, du_mul, du_smul, y.form g]
    congr 1
    rw [mul_assoc, ← mul_assoc (y.P : Matrix (Fin n) (Fin n) O), hz.pol, transpose_mul]
    simp only [mul_zero, zero_add, neg_mul, mul_neg, mul_assoc, neg_add_cancel]
  · rw [inv_inv, ← cj_apply]
    exact ⟨hut v g, fun i => (diagCh_val _ _ i g).symm⟩
  · refine Units.ext ?_
    refine (mat_duRep y.ρ z hz.coc g).trans ?_
    have h1 : mat y.ρ g = 1 := by
      show ((y.ρ g : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) = 1
      rw [y.ine u g hg]; rfl
    rw [hz.ine u g hg, h1, zero_mul, du_one]; rfl
  · ext g i j
    show (mat (duRep y.ρ z hz.coc :) g i j).fst = mat y.ρ g i j
    rw [mat_duRep, du_fst]
  · rw [mat_duRep, du_trace]
  · exact MonoidHom.ext fun g => Units.ext (hfst v i g)
  · have h := mc_du (cT v) (mc_mul (cb v) (cT v)) i i
    convert h using 2 with g
    rw [diagCh_val, hτ]
  · have h0 : b v g i i = 0 := by
      rcases hg with hg | hg
      · exact (hY v g).2.2.2 hg i
      · refine hmu v (fun g => b v g i i) (cb v i i) (fun s t => ?_) g hg
        have h := hsnd v i (s * t)
        rw [map_mul, Units.val_mul, TrivSqZeroExt.snd_mul, hsnd, hsnd, hfst, hfst] at h
        refine (y.ψ v i (s * t)).isUnit.mul_right_cancel ?_
        rw [← h, map_mul, Units.val_mul]
        simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
        ring
    rw [hsnd, h0, zero_mul]

end UpperTheory.V.Th.Nm

theorem UpperTheory.V.Th.Nm.dualRep :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c : Coef l) (y : Pt F c.O n) (z : F.G₀ → Matrix (Fin n) (Fin n) c.O) [IsCO c.O (DualNumber c.O)], OCoc y z → ∃ (ρ' : F.G₀ →* GL (Fin n) (DualNumber c.O)) (P' : GL (Fin n) (DualNumber c.O)) (ψ' : ∀ v, Fin n → F.Gv v →* (DualNumber c.O)ˣ), (∀ i j, AdicCont (maximalIdeal (DualNumber c.O)) fun g => mat ρ' g i j) ∧ F.IsForm c.O n ρ' P' ∧ (∀ v, HasFlag (ρ'.comp (F.φ v)) (ψ' v)) ∧ (∀ u, ∀ g ∈ F.Iu u, ρ' g = 1) ∧ pushRep (TrivSqZeroExt.fstHom c.O c.O c.O : DualNumber c.O →+* c.O) ρ' = y.ρ ∧ (∀ g, (mat ρ' g).trace.snd = (z g * mat y.ρ g).trace) ∧ ∀ v i, pushCh (TrivSqZeroExt.fstHom c.O c.O c.O : DualNumber c.O →+* c.O) (ψ' v i) = y.ψ v i ∧ (AdicCont (maximalIdeal (DualNumber c.O)) fun g => ((ψ' v i g : (DualNumber c.O)ˣ) : DualNumber c.O)) ∧ ∀ g, g ∈ F.Iv v ∨ g ∈ F.mu v → ((ψ' v i g : (DualNumber c.O)ˣ) : DualNumber c.O).snd = 0 := by
  intro l _ n F c y z _ hz
  exact dualRep_gen F c.O y z (fun v d => homMu c (F.Gv v) d) hz
