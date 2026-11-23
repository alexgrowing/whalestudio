import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.BumpLat

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels UpperTheory.TP.BA

noncomputable section

namespace UpperTheory.AdelicOrderPrincipalUnitInverse

open PositivityTheory.ThKH.Iwas (ev_sg mul_sg at_sg)

private theorem unit_abs {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A] (φ : O →+* A) (S : Subring A)
    (hφ : ∀ t, φ t ∈ S) (hint : ∀ x ∈ S, φ.IsIntegralElem x) {ϖ : O} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal O) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (hM : ∀ i j, M i j ∈ S) :
    ∃ N : Matrix (Fin n) (Fin n) A, (∀ i j, N i j ∈ S) ∧ (1 + φ ϖ • M) * N = 1 := by
  let φS : O →+* S := φ.codRestrict S hφ
  letI : Algebra O S := φS.toAlgebra
  have hI : Algebra.IsIntegral O S := ⟨fun x => by
    obtain ⟨P, hP, h⟩ := hint x.1 x.2
    refine ⟨P, hP, ?_⟩
    apply Subtype.ext
    have : S.subtype (Polynomial.eval₂ φS x P) = Polynomial.eval₂ (S.subtype.comp φS) (S.subtype x) P :=
      Polynomial.hom_eval₂ P φS S.subtype x
    exact this.trans h⟩
  let M' : Matrix (Fin n) (Fin n) S := fun i j => ⟨M i j, hM i j⟩
  let Q : Matrix (Fin n) (Fin n) S := 1 + φS ϖ • M'
  have hdet : IsUnit Q.det := by
    by_contra h
    obtain ⟨m, hm, hq⟩ := exists_max_ideal_of_mem_nonunits h
    have hmax : (m.comap (algebraMap O S)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
    have heq : m.comap (algebraMap O S) = IsLocalRing.maximalIdeal O := IsLocalRing.eq_maximalIdeal hmax
    have hϖm : φS ϖ ∈ m := by
      have : ϖ ∈ m.comap (algebraMap O S) := heq ▸ hϖ
      exact this
    have hmap : (Ideal.Quotient.mk m).mapMatrix Q = 1 := by
      ext i j
      have h0 : Ideal.Quotient.mk m (φS ϖ) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hϖm
      simp [Q, Matrix.one_apply, apply_ite, h0]
    have h1 : Ideal.Quotient.mk m Q.det = 1 := by
      rw [RingHom.map_det, hmap, Matrix.det_one]
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hq] at h1
    haveI := Ideal.Quotient.nontrivial_iff.2 hm.ne_top
    exact zero_ne_one h1
  have hQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hdet
  refine ⟨S.subtype.mapMatrix Q⁻¹, fun i j => (Q⁻¹ i j).2, ?_⟩
  have hQ' : S.subtype.mapMatrix Q = 1 + φ ϖ • M := by
    ext i j
    simp [Q, M', φS, Matrix.one_apply, apply_ite]
    rfl
  rw [← hQ', ← map_mul, hQ, map_one]

open PositivityTheory.ThKH.Iwas (sgE comp_sgE at_sgE sgE_comp eq_zero_of_at)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem oh_induct {v : Pl F} {P : AE F E → Prop}
    (hg : ∀ a : AF F, At (evFin F v) a → evFin F v a ∈ v.adicCompletionIntegers F → ∀ o : 𝓞 E,
      P (a • inclR (F := F) (AF F) (o : E)))
    (h0 : P 0) (ha : ∀ x y, P x → P y → P (x + y)) (hn : ∀ x, P x → P (-x)) {x : AE F E} (hx : x ∈ Oh E v) : P x := by
  refine AddSubgroup.closure_induction (p := fun x _ => P x) ?_ h0 (fun x y _ _ => ha x y) (fun x _ => hn x) hx
  rintro z ⟨a, h1, h2, o, rfl⟩
  exact hg a h1 h2 o

private theorem e_smul {v : Pl F} {M : Type} [AddCommGroup M] [Module (AF F) M] {z : M} (h : At (evFin F v) z) :
    sg v 1 • z = z := by
  have h1 := h (1 - sg v 1) (by rw [map_sub, map_one, ev_sg, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  exact h1.symm

private theorem gen_mem {v : Pl F} (t : Fv F v) (ht : t ∈ v.adicCompletionIntegers F) : sg v t • (1 : AE F E) ∈ Oh E v :=
  AddSubgroup.subset_closure ⟨sg v t, at_sg t, by rw [ev_sg]; exact ht, 1, by simp⟩

private theorem oh_at {v : Pl F} {x : AE F E} (hx : x ∈ Oh E v) : At (evFin F v) x := by
  refine oh_induct (P := fun x => At (evFin F v) x) ?_ ?_ ?_ ?_ hx
  · intro a h1 _ o u hu
    rw [← smul_assoc, h1 u hu, zero_smul]
  · intro u _; exact smul_zero u
  · intro x y hx hy u hu; rw [smul_add, hx u hu, hy u hu, add_zero]
  · intro x hx u hu; rw [smul_neg, hx u hu, neg_zero]

private theorem oh_mul {v : Pl F} {x y : AE F E} (hx : x ∈ Oh E v) (hy : y ∈ Oh E v) : x * y ∈ Oh E v := by
  refine oh_induct (P := fun x => x * y ∈ Oh E v) ?_ (by simp [zero_mem]) ?_ ?_ hx
  · intro a h1 h2 o
    refine oh_induct (P := fun y => a • inclR (F := F) (AF F) (o : E) * y ∈ Oh E v) ?_ (by simp [zero_mem]) ?_ ?_ hy
    · intro a' h1' h2' o'
      refine AddSubgroup.subset_closure ⟨a * a', ?_, ?_, o * o', ?_⟩
      · intro u hu
        rw [smul_eq_mul, ← mul_assoc, ← smul_eq_mul u a, h1 u hu, zero_mul]
      · rw [map_mul]; exact mul_mem h2 h2'
      · rw [smul_mul_smul_comm]; simp
    · intro x y hx hy; rw [mul_add]; exact add_mem hx hy
    · intro x hx; rw [mul_neg]; exact neg_mem hx
  · intro x z hx hz; rw [add_mul]; exact add_mem hx hz
  · intro x hx; rw [neg_mul]; exact neg_mem hx

private theorem sgE_mul {v : Pl F} (x y : TensorProduct F (Fv F v) E) : sgE E v (x * y) = sgE E v x * sgE E v y := by
  have h : compFin F E v (sgE E v x * sgE E v y) = x * y := by rw [map_mul, comp_sgE, comp_sgE]
  rw [← h, sgE_comp]
  refine e_smul (v := v) fun u hu => ?_
  rw [← smul_mul_assoc, at_sgE x u hu, zero_mul]

private theorem sgE_one {v : Pl F} : sgE E v 1 = sg v 1 • (1 : AE F E) := by
  simpa using sgE_comp (E := E) (v := v) (1 : AE F E)

private def phi (E : Type) [Field E] [Algebra F E] (v : Pl F) : v.adicCompletionIntegers F →+* TensorProduct F (Fv F v) E :=
  (algebraMap (Fv F v) (TensorProduct F (Fv F v) E)).comp (v.adicCompletionIntegers F).subtype

private def SS (E : Type) [Field E] [NumberField E] [Algebra F E] (v : Pl F) : Subring (TensorProduct F (Fv F v) E) where
  carrier := {x | sgE E v x ∈ Oh E v ∧ (phi E v).IsIntegralElem x}
  mul_mem' := fun {x y} hx hy => ⟨by rw [sgE_mul]; exact oh_mul hx.1 hy.1, RingHom.IsIntegralElem.mul _ hx.2 hy.2⟩
  one_mem' := ⟨by rw [sgE_one]; exact gen_mem 1 (one_mem _), by
    simpa using (phi E v).isIntegralElem_map (x := 1)⟩
  add_mem' := fun {x y} hx hy => ⟨by rw [map_add]; exact add_mem hx.1 hy.1, RingHom.IsIntegralElem.add _ hx.2 hy.2⟩
  zero_mem' := ⟨by rw [map_zero]; exact zero_mem _, RingHom.isIntegralElem_zero _⟩
  neg_mem' := fun {x} hx => ⟨by rw [map_neg]; exact neg_mem hx.1, RingHom.IsIntegralElem.neg _ hx.2⟩

private theorem phi_mem {v : Pl F} (t : v.adicCompletionIntegers F) : phi E v t ∈ SS E v := by
  refine ⟨?_, (phi E v).isIntegralElem_map⟩
  have h : sgE E v (phi E v t) = sg v (t : Fv F v) • (1 : AE F E) := by
    change sg v (t : Fv F v) ⊗ₜ[F] (1 : E) = sg v (t : Fv F v) • ((1 : AF F) ⊗ₜ[F] (1 : E))
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h]
  exact gen_mem _ t.2

private theorem comp_mem {v : Pl F} {x : AE F E} (hx : x ∈ Oh E v) : compFin F E v x ∈ SS E v := by
  refine ⟨by rw [sgE_comp, e_smul (oh_at hx)]; exact hx, ?_⟩
  refine oh_induct (P := fun x => (phi E v).IsIntegralElem (compFin F E v x)) ?_ ?_ ?_ ?_ hx
  · intro a _ h2 o
    have h : compFin F E v (a • inclR (F := F) (AF F) (o : E)) =
        phi E v ⟨evFin F v a, h2⟩ * (1 ⊗ₜ[F] (o : E)) := by
      have e1 : a • inclR (F := F) (AF F) (o : E) = a ⊗ₜ[F] (o : E) := by
        change a • ((1 : AF F) ⊗ₜ[F] (o : E)) = _
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e1]
      change evFin F v a ⊗ₜ[F] (o : E) = (evFin F v a ⊗ₜ[F] (1 : E)) * ((1 : Fv F v) ⊗ₜ[F] (o : E))
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h]
    refine RingHom.IsIntegralElem.mul _ (phi E v).isIntegralElem_map ?_
    obtain ⟨P, hP, h0⟩ := NumberField.RingOfIntegers.isIntegral_coe o
    refine ⟨P.map (Int.castRingHom _), hP.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    let incl : E →+* TensorProduct F (Fv F v) E := inclR (F := F) (Fv F v)
    have hh : (phi E v).comp (Int.castRingHom _) = incl.comp (algebraMap ℤ E) := RingHom.ext_int _ _
    rw [hh]
    exact (Polynomial.hom_eval₂ P (algebraMap ℤ E) incl (o : E)).symm.trans (by rw [h0, map_zero])
  · rw [map_zero]; exact RingHom.isIntegralElem_zero _
  · intro x y hx hy; rw [map_add]; exact RingHom.IsIntegralElem.add _ hx hy
  · intro x hx; rw [map_neg]; exact RingHom.IsIntegralElem.neg _ hx

private theorem smul_comp {v : Pl F} (a : AF F) (z : AE F E) : compFin F E v (a • z) = evFin F v a • compFin F E v z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    change evFin F v (a * b) ⊗ₜ[F] x = evFin F v a • (evFin F v b ⊗ₜ[F] x)
    rw [TensorProduct.smul_tmul', smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

private theorem at_entry {v : Pl F} {ι κ : Type} {A : Matrix ι κ (AE F E)} (h : At (evFin F v) A) (i : ι) (j : κ) :
    At (evFin F v) (A i j) := fun u hu => congrFun (congrFun (h u hu) i) j

private theorem mat_eq {v : Pl F} {ι κ : Type} {A B : Matrix ι κ (AE F E)} (hA : At (evFin F v) A) (hB : At (evFin F v) B)
    (h : A.map (compFin F E v) = B.map (compFin F E v)) : A = B := by
  ext i j
  have h1 : compFin F E v (A i j - B i j) = 0 := by
    rw [map_sub, sub_eq_zero]; exact congrFun (congrFun h i) j
  have h2 : At (evFin F v) (A i j - B i j) := fun u hu => by
    rw [smul_sub, at_entry hA i j u hu, at_entry hB i j u hu, sub_zero]
  exact sub_eq_zero.1 (eq_zero_of_at h2 h1)

private theorem at_eM {v : Pl F} {n : ℕ} : At (evFin F v) (eM (E := E) v n) := fun u hu => by
  rw [eM, ← smul_assoc, at_sg 1 u hu, zero_smul]

private theorem eM_mul {v : Pl F} {n : ℕ} {A : Matrix (Fin n) (Fin n) (AE F E)} (h : At (evFin F v) A) : eM v n * A = A := by
  rw [eM, Matrix.smul_mul, one_mul, e_smul h]

private theorem mul_eM {v : Pl F} {n : ℕ} {A : Matrix (Fin n) (Fin n) (AE F E)} (h : At (evFin F v) A) : A * eM v n = A := by
  rw [eM, Matrix.mul_smul, mul_one, e_smul h]

private theorem max_mem {v : Pl F} {ϖ : Fv F v} (hϖ : ϖ ∈ v.adicCompletionIntegers F) (hlt : Valued.v ϖ < 1) :
    (⟨ϖ, hϖ⟩ : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have h1 : ϖ * (w : Fv F v) = 1 := congrArg Subtype.val hw
  have h2 : Valued.v (w : Fv F v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).1 w.2
  have h3 : Valued.v ϖ * Valued.v (w : Fv F v) = 1 := by rw [← map_mul, h1, map_one]
  have h4 : Valued.v ϖ * Valued.v (w : Fv F v) ≤ Valued.v ϖ := mul_le_of_le_one_right' h2
  exact absurd (h3 ▸ h4) (not_le.2 hlt)

end UpperTheory.AdelicOrderPrincipalUnitInverse

open UpperTheory.AdelicOrderPrincipalUnitInverse in
theorem UpperTheory.latticeOrder_exists_inverse_one_add_uniformizer_smul :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (X : Spc F E n) (v : Pl F) (b c : Matrix (Fin n) (Fin n) (AE F E)), IsFr X v b c → ∀ ϖ : Fv F v, ϖ ∈ v.adicCompletionIntegers F → Valued.v ϖ < 1 → ∀ p ∈ abelian₂ (E := E) v b c, ∃ q ∈ abelian₂ (E := E) v b c, (eM v n + sg v ϖ • p) * q = eM v n := by
  intro F E _ _ _ _ _ n X v b c hX ϖ hϖ hlt p hp
  have hpat : At (evFin F v) (c * p * b) := fun u hu => by
    rw [← Matrix.smul_mul, ← Matrix.smul_mul, hX.at_c u hu, Matrix.zero_mul, Matrix.zero_mul]
  obtain ⟨N, hN, hQ⟩ := unit_abs (phi E v) (SS E v) phi_mem (fun x hx => hx.2) (max_mem hϖ hlt)
    ((c * p * b).map (compFin F E v)) (fun i j => comp_mem (hp.2 i j))
  let N' : Matrix (Fin n) (Fin n) (AE F E) := N.map (PositivityTheory.ThKH.Iwas.sgE E v)
  have hN' : ∀ i j, N' i j ∈ Oh E v := fun i j => (hN i j).1
  have hNat : At (evFin F v) N' := fun u hu => by
    ext i j
    exact PositivityTheory.ThKH.Iwas.at_sgE _ u hu
  have hQt : (eM v n + sg v ϖ • (c * p * b)) * N' = eM v n := by
    refine mat_eq (v := v) ?_ at_eM ?_
    · exact fun u hu => by rw [← Matrix.mul_smul, hNat u hu, Matrix.mul_zero]
    · let Φ := (compFin F E v).mapMatrix (m := Fin n)
      have hsm : ∀ (a : AF F) (A : Matrix (Fin n) (Fin n) (AE F E)), Φ (a • A) = evFin F v a • Φ A := fun a A => by
        ext i j
        exact smul_comp a (A i j)
      have he : Φ (eM v n) = 1 := by
        rw [eM, hsm, PositivityTheory.ThKH.Iwas.ev_sg, one_smul, map_one]
      have hN2 : Φ N' = N := by
        ext i j
        exact PositivityTheory.ThKH.Iwas.comp_sgE _
      have hs : ϖ • Φ (c * p * b) = phi E v ⟨ϖ, hϖ⟩ • Φ (c * p * b) := by
        ext i j
        exact Algebra.smul_def ϖ (Φ (c * p * b) i j)
      change Φ _ = Φ _
      rw [map_mul, map_add, he, hN2, hsm, PositivityTheory.ThKH.Iwas.ev_sg, hs]
      exact hQ
  have hb1 : b * eM v n = b := mul_eM hX.at_b
  have hb2 : eM v n * b = b := eM_mul hX.at_b
  have hD : (eM v n + sg v ϖ • p) * b = b * (eM v n + sg v ϖ • (c * p * b)) := by
    rw [Matrix.add_mul, Matrix.mul_add, hb1, hb2, Matrix.smul_mul (sg v ϖ) p b, Matrix.mul_smul b (sg v ϖ)]
    congr 2
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hX.bc, eM_mul hp.1]
  refine ⟨b * N' * c, ⟨?_, ?_⟩, ?_⟩
  · intro u hu
    rw [← Matrix.smul_mul, ← Matrix.smul_mul, hX.at_b u hu, Matrix.zero_mul, Matrix.zero_mul]
  · intro i j
    have h : c * (b * N' * c) * b = N' := by
      calc c * (b * N' * c) * b = (c * b) * N' * (c * b) := by simp only [Matrix.mul_assoc]
        _ = N' := by rw [hX.cb, eM_mul hNat, mul_eM hNat]
    rw [h]
    exact hN' i j
  · calc (eM v n + sg v ϖ • p) * (b * N' * c) = ((eM v n + sg v ϖ • p) * b) * N' * c := by simp only [Matrix.mul_assoc]
      _ = b * ((eM v n + sg v ϖ • (c * p * b)) * N') * c := by rw [hD]; simp only [Matrix.mul_assoc]
      _ = eM v n := by rw [hQt, hb1, hX.bc]
