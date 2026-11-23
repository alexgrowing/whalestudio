import Development.AutomorphicArithmetic.AdelicQuotients.UnitaryLatticeExistsFrame
import Development.AutomorphicArithmetic.AdelicQuotients.LatticeOrderExistsInverseOneAddUniformizerSmul
import Development.AutomorphicArithmetic.AdelicQuotients.MemNhdsOneOfCongruenceLatticeOrder
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsIsotropicSplittingOfTwoMulLe
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.InertofProofK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsIsotropicSplittingAtInertPrime

set_option synthInstance.maxHeartbeats 200000

section
open scoped Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels UpperTheory.TP.BA
namespace UpperTheory.LatD
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} {v : Pl F}
private theorem at_self_pk {M : Type} [AddCommGroup M] [Module (AF F) M] {x : M} (hx : At (evFin F v) x) :
    sg v 1 • x = x := by
  have h1 := hx (1 - sg v 1) (by rw [map_sub, map_one, PositivityTheory.ThKH.Iwas.ev_sg, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  exact h1.symm
private theorem at_mulA_pk {a : AF F} (ha : At (evFin F v) a) (a' : AF F) : At (evFin F v) (a * a') := fun u hu => by
  have h := ha u hu
  rw [smul_eq_mul] at h ⊢
  rw [← mul_assoc, h, zero_mul]
private theorem sg_one_int_pk : evFin F v (sg v 1) ∈ v.adicCompletionIntegers F := by
  rw [PositivityTheory.ThKH.Iwas.ev_sg]; exact one_mem _
private theorem oh_gen_pk {a : AF F} (h1 : At (evFin F v) a) (h2 : evFin F v a ∈ v.adicCompletionIntegers F) (o : 𝓞 E) :
    a • inclR (F := F) (AF F) (o : E) ∈ Oh E v :=
  AddSubgroup.subset_closure ⟨a, h1, h2, o, rfl⟩
private theorem oh_ind_pk {p : AE F E → Prop}
    (gen : ∀ a : AF F, At (evFin F v) a → evFin F v a ∈ v.adicCompletionIntegers F → ∀ o : 𝓞 E, p (a • inclR (F := F) (AF F) (o : E)))
    (zero : p 0) (add : ∀ x y, p x → p y → p (x + y)) (neg : ∀ x, p x → p (-x)) {x : AE F E} (hx : x ∈ Oh E v) : p x := by
  refine AddSubgroup.closure_induction (p := fun x _ => p x) ?_ zero (fun x y _ _ h h' => add x y h h') (fun x _ h => neg x h) hx
  rintro _ ⟨a, h1, h2, o, rfl⟩
  exact gen a h1 h2 o
private theorem oh_mul_pk {x y : AE F E} (hx : x ∈ Oh E v) (hy : y ∈ Oh E v) : x * y ∈ Oh E v := by
  refine oh_ind_pk (p := fun x => x * y ∈ Oh E v) ?_ (by simp [zero_mem]) (fun x y h h' => by rw [add_mul]; exact add_mem h h')
    (fun x h => by rw [neg_mul]; exact neg_mem h) hx
  intro a h1 h2 o
  refine oh_ind_pk (p := fun y => a • inclR (F := F) (AF F) (o : E) * y ∈ Oh E v) ?_ (by simp [zero_mem])
    (fun x y h h' => by rw [mul_add]; exact add_mem h h') (fun x h => by rw [mul_neg]; exact neg_mem h) hy
  intro a' h1' h2' o'
  have e : a • inclR (F := F) (AF F) (o : E) * a' • inclR (F := F) (AF F) (o' : E) =
      (a * a') • inclR (F := F) (AF F) ((o * o' : 𝓞 E) : E) := by
    rw [smul_mul_smul_comm, ← map_mul]; rfl
  rw [e]
  exact oh_gen_pk (at_mulA_pk h1 a') (by rw [map_mul]; exact mul_mem h2 h2') _
private theorem oh_sg_pk {t : Fv F v} (ht : t ∈ v.adicCompletionIntegers F) : sg v t • (1 : AE F E) ∈ Oh E v := by
  have := oh_gen_pk (E := E) (PositivityTheory.ThKH.Iwas.at_sg t) (by rw [PositivityTheory.ThKH.Iwas.ev_sg]; exact ht) (1 : 𝓞 E)
  simpa using this
private theorem oh_smul_pk {t : Fv F v} (ht : t ∈ v.adicCompletionIntegers F) {x : AE F E} (hx : x ∈ Oh E v) :
    sg v t • x ∈ Oh E v := by
  have := oh_mul_pk (oh_sg_pk (E := E) ht) hx
  rwa [smul_mul_assoc, one_mul] at this
private theorem oh_matmul_pk {P Q : Matrix (Fin n) (Fin n) (AE F E)} (hP : ∀ i j, P i j ∈ Oh E v) (hQ : ∀ i j, Q i j ∈ Oh E v) (i j : Fin n) :
    (P * Q) i j ∈ Oh E v := by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => oh_mul_pk (hP i k) (hQ k j)
private theorem oh_mulVec_pk {P : Matrix (Fin n) (Fin n) (AE F E)} {w : Fin n → AE F E} (hP : ∀ i j, P i j ∈ Oh E v) (hw : ∀ i, w i ∈ Oh E v) (i : Fin n) :
    (P *ᵥ w) i ∈ Oh E v := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun k _ => oh_mul_pk (hP i k) (hw k)
private theorem lat_ind_pk {m : ℕ} {X : Spc F E m} {p : (Fin m → AE F E) → Prop}
    (gen : ∀ a : AF F, At (evFin F v) a → evFin F v a ∈ v.adicCompletionIntegers F → ∀ y ∈ X.L, p (fun i => a • inclR (F := F) (AF F) (y i)))
    (zero : p 0) (add : ∀ x y, p x → p y → p (x + y)) (neg : ∀ x, p x → p (-x)) {x : Fin m → AE F E} (hx : x ∈ PositivityTheory.ThK.latW X v) : p x := by
  refine AddSubgroup.closure_induction (p := fun x _ => p x) ?_ zero (fun x y _ _ h h' => add x y h h') (fun x _ h => neg x h) hx
  rintro _ ⟨a, h1, h2, y, hy, rfl⟩
  exact gen a h1 h2 y hy
private theorem lat_smul_pk {m : ℕ} {X : Spc F E m} {o : AE F E} (ho : o ∈ Oh E v) {z : Fin m → AE F E} (hz : z ∈ PositivityTheory.ThK.latW X v) :
    (fun i => o * z i) ∈ PositivityTheory.ThK.latW X v := by
  refine oh_ind_pk (p := fun o => (fun i => o * z i) ∈ PositivityTheory.ThK.latW X v) ?_ (by simp only [zero_mul]; exact zero_mem _)
    (fun x y h h' => by simp only [add_mul]; exact add_mem h h') (fun x h => by simp only [neg_mul]; exact neg_mem h) ho
  intro a h1 h2 o
  refine lat_ind_pk (p := fun z => (fun i => a • inclR (F := F) (AF F) (o : E) * z i) ∈ PositivityTheory.ThK.latW X v) ?_ (by simp only [Pi.zero_apply, mul_zero]; exact zero_mem _)
    (fun x y h h' => by simp only [Pi.add_apply, mul_add]; exact add_mem h h')
    (fun x h => by simp only [Pi.neg_apply, mul_neg]; exact neg_mem h) hz
  intro a' h1' h2' y hy
  refine AddSubgroup.subset_closure ⟨a * a', at_mulA_pk h1 a', by rw [map_mul]; exact mul_mem h2 h2', o • y, X.L.smul_mem o hy, ?_⟩
  funext i
  rw [smul_mul_smul_comm, ← map_mul]
  rfl
private theorem lat_mulVec_pk {m : ℕ} {X : Spc F E m} {P : Matrix (Fin m) (Fin n) (AE F E)} {w : Fin n → AE F E}
    (hP : ∀ j, (fun i => P i j) ∈ PositivityTheory.ThK.latW X v) (hw : ∀ j, w j ∈ Oh E v) : P *ᵥ w ∈ PositivityTheory.ThK.latW X v := by
  have e : P *ᵥ w = ∑ j, fun i => w j * P i j := by
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [e]
  exact sum_mem fun j _ => lat_smul_pk (hw j) (hP j)
private theorem vmv_mem_pk {X : Spc F E n} {W : Spc F E d} {z : Fin n → AE F E} {y : Fin d → AE F E}
    (hz : z ∈ PositivityTheory.ThK.latW X v) (hy : y ∈ PositivityTheory.ThK.latW W v) : Matrix.vecMulVec z y ∈ latAtV X W v := by
  refine lat_ind_pk (p := fun z => Matrix.vecMulVec z y ∈ latAtV X W v) ?_ ?_ ?_ ?_ hz
  · intro a h1 h2 x hx
    refine lat_ind_pk (p := fun y => Matrix.vecMulVec (fun i => a • inclR (F := F) (AF F) (x i)) y ∈ latAtV X W v) ?_ ?_ ?_ ?_ hy
    · intro a' h1' h2' y hy
      refine AddSubgroup.subset_closure ⟨a * a', at_mulA_pk h1 a', by rw [map_mul]; exact mul_mem h2 h2', x, hx, y, hy, ?_⟩
      ext i j
      simp [Matrix.vecMulVec_apply, incM, smul_mul_smul_comm]
      rw [mul_comm a a', mul_smul]
    · have e : Matrix.vecMulVec (fun i => a • inclR (F := F) (AF F) (x i)) (0 : Fin d → AE F E) = 0 := by
        ext i j; simp [Matrix.vecMulVec_apply]
      rw [e]; exact zero_mem _
    · intro x y h h'
      have := add_mem h h'
      rwa [show ∀ u (p q : Fin d → AE F E), Matrix.vecMulVec u p + Matrix.vecMulVec u q = Matrix.vecMulVec u (p + q) from fun u p q => by
        ext i j; simp [Matrix.vecMulVec_apply, mul_add]] at this
    · intro x h
      have := neg_mem h
      rwa [show ∀ u (p : Fin d → AE F E), -Matrix.vecMulVec u p = Matrix.vecMulVec u (-p) from fun u p => by
        ext i j; simp [Matrix.vecMulVec_apply]] at this
  · have e : Matrix.vecMulVec (0 : Fin n → AE F E) y = 0 := by
      ext i j; simp [Matrix.vecMulVec_apply]
    rw [e]; exact zero_mem _
  · intro x y h h'
    have := add_mem h h'
    rwa [show ∀ (p q : Fin n → AE F E) u, Matrix.vecMulVec p u + Matrix.vecMulVec q u = Matrix.vecMulVec (p + q) u from fun p q u => by
      ext i j; simp [Matrix.vecMulVec_apply, add_mul]] at this
  · intro x h
    have := neg_mem h
    rwa [show ∀ (p : Fin n → AE F E) u, -Matrix.vecMulVec p u = Matrix.vecMulVec (-p) u from fun p u => by
      ext i j; simp [Matrix.vecMulVec_apply]] at this
private theorem gam_ind_pk {X : Spc F E n} {W : Spc F E d} {p : Matrix (Fin n) (Fin d) (AE F E) → Prop}
    (gen : ∀ z ∈ PositivityTheory.ThK.latW X v, ∀ y ∈ PositivityTheory.ThK.latW W v, p (Matrix.vecMulVec z y))
    (zero : p 0) (add : ∀ x y, p x → p y → p (x + y)) (neg : ∀ x, p x → p (-x)) {γ : Matrix (Fin n) (Fin d) (AE F E)}
    (hγ : γ ∈ latAtV X W v) : p γ := by
  refine AddSubgroup.closure_induction (p := fun x _ => p x) ?_ zero (fun x y _ _ h h' => add x y h h') (fun x _ h => neg x h) hγ
  rintro _ ⟨a, h1, h2, x, hx, y, hy, rfl⟩
  have e : a • incM F (Matrix.vecMulVec x y) = Matrix.vecMulVec (fun i => a • inclR (F := F) (AF F) (x i))
      (fun j => sg v 1 • inclR (F := F) (AF F) (y j)) := by
    ext i j
    have e1 : a * sg v 1 = a := by rw [mul_comm]; exact at_self_pk h1
    simp [Matrix.vecMulVec_apply, incM, smul_mul_smul_comm, e1]
    rw [← mul_smul, mul_comm (sg v 1) a, e1]
  rw [e]
  exact gen _ (AddSubgroup.subset_closure ⟨a, h1, h2, x, hx, rfl⟩) _
    (AddSubgroup.subset_closure ⟨sg v 1, PositivityTheory.ThKH.Iwas.at_sg 1, sg_one_int_pk, y, hy, rfl⟩)
private theorem mul_eM_pk {M : Matrix (Fin n) (Fin n) (AE F E)} (h : At (evFin F v) M) : M * eM v n = M := by
  rw [Matrix.mul_smul, Matrix.mul_one]; exact at_self_pk h
private theorem eM_mul_pk {M : Matrix (Fin n) (Fin n) (AE F E)} (h : At (evFin F v) M) : eM v n * M = M := by
  rw [Matrix.smul_mul, Matrix.one_mul]; exact at_self_pk h
private theorem eM_mem_pk (i j : Fin n) : (eM (E := E) v n) i j ∈ Oh E v := by
  by_cases h : i = j
  · subst h
    simpa [eM] using oh_sg_pk (E := E) (v := v) (one_mem _)
  · simp [eM, h, zero_mem]
private theorem eM_at_pk : At (evFin F v) (eM (E := E) v n) := fun u hu => by
  rw [smul_smul, show u * sg v 1 = 0 from PositivityTheory.ThKH.Iwas.at_sg 1 u hu, zero_smul]
end UpperTheory.LatD
theorem UpperTheory.exists_weilLatticeDatum :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → X.IsHerm σ B r s → W.IsSkew σ B r' s' → 2 * n ≤ d → ∀ v : Pl F, ∃ Λ x₁ R ϖ, LatData σ X W v Λ x₁ R ϖ := by
  intro F E _ _ _ _ _ σ B n d X W r s r' s' hB hX hW hnd v
  have hYR : ∃ Y R, IsIsoW σ W v (n := n) Y R := by
    by_cases ht : Nonempty (E →ₐ[F] Fv F v)
    · obtain ⟨t⟩ := ht
      exact _root_.UpperTheory.exists_isotropic_splitting_of_two_mul_le F E σ B n d W r' s' hB hW hnd v t
    · obtain ⟨w, hw⟩ := _root_.PositivityTheory.ThK.inertof_proof_k F E σ B hB v (not_nonempty_iff.1 ht)
      exact _root_.UpperTheory.exists_isotropic_splitting_at_inert_prime F E σ B n d W r' s' hB hW hnd v w hw
  obtain ⟨Y, R, hY⟩ := hYR
  obtain ⟨b, c, hF⟩ := UpperTheory.unitaryLattice_exists_frame F E n X v hX.lat
  obtain ⟨ϖ, hϖ0, hϖ1⟩ : ∃ ϖ : Fv F v, ϖ ≠ 0 ∧ Valued.v ϖ < 1 := by
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
    have e : Valued.v ((π : F) : v.adicCompletion F) = v.valuation F π := v.valuedAdicCompletion_eq_valuation' π
    refine ⟨((π : F) : v.adicCompletion F), ?_, ?_⟩
    · intro h0
      rw [h0, map_zero, hπ] at e
      exact absurd e.symm (by simp)
    · rw [e, hπ]
      exact compareOfLessAndEq_eq_lt.mp rfl
  have hϖm : ϖ ∈ v.adicCompletionIntegers F := hϖ1.le
  have hmul : ∀ a ∈ abelian₂ (E := E) v b c, ∀ a' ∈ abelian₂ (E := E) v b c, a * a' ∈ abelian₂ (E := E) v b c := by
    intro a ha a' ha'
    refine ⟨PositivityTheory.ThKH.Iwas.at_mul_left ha.1 a', fun i j => ?_⟩
    have e : c * (a * a') * b = (c * a * b) * (c * a' * b) := by
      calc c * (a * a') * b = c * (a * eM v n * a') * b := by rw [UpperTheory.LatD.mul_eM_pk ha.1]
        _ = c * (a * (b * c) * a') * b := by rw [hF.bc]
        _ = (c * a * b) * (c * a' * b) := by simp only [Matrix.mul_assoc]
    rw [e]
    exact UpperTheory.LatD.oh_matmul_pk ha.2 ha'.2 i j
  have hact : ∀ a ∈ abelian₂ (E := E) v b c, ∀ z ∈ PositivityTheory.ThK.latW X v, a *ᵥ z ∈ PositivityTheory.ThK.latW X v := by
    intro a ha z hz
    have e : a *ᵥ z = b *ᵥ ((c * a * b) *ᵥ (c *ᵥ z)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      congr 1
      calc a = eM v n * a * eM v n := by rw [UpperTheory.LatD.mul_eM_pk (PositivityTheory.ThKH.Iwas.at_mul_right _ ha.1), UpperTheory.LatD.eM_mul_pk ha.1]
        _ = (b * c) * a * (b * c) := by rw [hF.bc]
        _ = b * (c * a * b) * c := by simp only [Matrix.mul_assoc]
    rw [e]
    exact UpperTheory.LatD.lat_mulVec_pk hF.col (UpperTheory.LatD.oh_mulVec_pk ha.2 (hF.coord z hz))
  refine ⟨abelian₂ (E := E) v b c, b * Y, R * c, ϖ, ?_⟩
  refine
    { at_mem := fun a ha => ha.1
      one_mem := ⟨UpperTheory.LatD.eM_at_pk, fun i j => ?_⟩
      mul_mem := hmul
      smul_mem := fun t ht a ha => ⟨fun u hu => by rw [smul_comm, ha.1 u hu, smul_zero], fun i j => ?_⟩
      act := ?_
      x_mem := ?_
      gram := ?_
      right := ?_
      r_mem := ?_
      ϖ_ne := hϖ0
      ϖ_mem := hϖm
      unit := UpperTheory.latticeOrder_exists_inverse_one_add_uniformizer_smul F E n X v b c hF ϖ hϖm hϖ1
      small := (UpperTheory.mem_nhds_one_of_congruence_latticeOrder F E σ n X v b c hF ϖ hϖ0 hϖ1).1
      nbhd := (UpperTheory.mem_nhds_one_of_congruence_latticeOrder F E σ n X v b c hF ϖ hϖ0 hϖ1).2 }
  · rw [UpperTheory.LatD.mul_eM_pk hF.at_c, hF.cb]
    exact UpperTheory.LatD.eM_mem_pk i j
  · rw [Matrix.mul_smul, Matrix.smul_mul]
    exact UpperTheory.LatD.oh_smul_pk ht (ha.2 i j)
  · intro a ha γ hγ
    refine UpperTheory.LatD.gam_ind_pk (p := fun γ => a * γ ∈ latAtV X W v) ?_ (by simp [zero_mem]) ?_ ?_ hγ
    · intro z hz y hy
      rw [Matrix.mul_vecMulVec]
      exact UpperTheory.LatD.vmv_mem_pk (hact a ha z hz) hy
    · intro x y h h'
      rw [Matrix.mul_add]; exact add_mem h h'
    · intro x h
      rw [Matrix.mul_neg]; exact neg_mem h
  · have e : b * Y = ∑ k, Matrix.vecMulVec (fun i => b i k) (Y k) := by
      ext i j
      simp [Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply]
    rw [e]
    exact sum_mem fun k _ => UpperTheory.LatD.vmv_mem_pk (hF.col k) (hY.what₂ k)
  · have hm : (b * Y).map (cA σ) = b.map (cA σ) * Y.map (cA σ) := Matrix.map_mul (f := (cA σ).toRingHom)
    rw [hm, Matrix.transpose_mul]
    have e : b * Y * incM F W.J * ((Y.map (cA σ))ᵀ * (b.map (cA σ))ᵀ) =
        b * (Y * incM F W.J * (Y.map (cA σ))ᵀ) * (b.map (cA σ))ᵀ := by simp only [Matrix.mul_assoc]
    rw [e, hY.gram, Matrix.mul_zero, Matrix.zero_mul]
  · have e : b * Y * (R * c) = b * (Y * R) * c := by simp only [Matrix.mul_assoc]
    rw [e, hY.right, UpperTheory.LatD.mul_eM_pk hF.at_b, hF.bc]
  · intro γ hγ
    refine ⟨PositivityTheory.ThKH.Iwas.at_mul_right _ (PositivityTheory.ThKH.Iwas.at_mul_right _ hF.at_c), ?_⟩
    refine UpperTheory.LatD.gam_ind_pk (p := fun γ => ∀ i j, (c * (γ * (R * c)) * b) i j ∈ Oh E v) ?_ (by simp [zero_mem]) ?_ ?_ hγ
    · intro z hz y hy i j
      have e : c * (Matrix.vecMulVec z y * (R * c)) * b = Matrix.vecMulVec (c *ᵥ z) (sg v 1 • (y ᵥ* R)) := by
        have e1 : c * (Matrix.vecMulVec z y * (R * c)) * b = c * Matrix.vecMulVec z y * R * (c * b) := by
          simp only [Matrix.mul_assoc]
        rw [e1, hF.cb, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.mul_smul, Matrix.mul_one]
        ext i j
        simp [Matrix.vecMulVec_apply]
      rw [e, Matrix.vecMulVec_apply]
      exact UpperTheory.LatD.oh_mul_pk (hF.coord z hz i) (UpperTheory.LatD.oh_smul_pk (one_mem _) (hY.coord y hy j))
    · intro x y h h' i j
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.add_mul]
      exact add_mem (h i j) (h' i j)
    · intro x h i j
      rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.neg_mul]
      exact neg_mem (h i j)
end
