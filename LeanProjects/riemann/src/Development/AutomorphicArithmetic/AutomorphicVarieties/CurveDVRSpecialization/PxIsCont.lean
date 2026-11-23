import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransferAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.UnipTorsion
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CoB
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.DetMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TraceMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MemPowSmulLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CharpolyFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ExistsAdjoinCoeffCharacterSubMemMaximalIdealPow

set_option linter.overlappingInstances false

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V

section Gen

variable {n : ℕ} {A G : Type} [CommRing A] [Group G]

private theorem px_chi (ρ : G →* Matrix (Fin n) (Fin n) A) (y : MonoidAlgebra A G) :
    (W.GDet.ofRep ρ).chi y = (MonoidAlgebra.lift A _ G ρ y).charpoly := by
  change (W.GDet.repAlg ρ (Polynomial A) _).det = _
  unfold Matrix.charpoly
  congr 1
  have h : W.GDet.repAlg ρ (Polynomial A) (MonoidAlgebra.mapRingHom G Polynomial.C y) =
      (Polynomial.C : A →+* Polynomial A).mapMatrix (MonoidAlgebra.lift A _ G ρ y) := by
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single g r => ext i j : 2; simp [W.GDet.repAlg]
  rw [map_sub, h]
  ext i j : 2
  by_cases h : i = j <;> simp [W.GDet.repAlg, Matrix.charmatrix_apply, h, Matrix.one_apply]

private theorem px_tr (hn : n ≠ 0) (ρ : G →* Matrix (Fin n) (Fin n) A) (y : MonoidAlgebra A G) :
    (W.GDet.ofRep ρ).tr y = (MonoidAlgebra.lift A _ G ρ y).trace := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  rw [W.GDet.tr, W.GDet.lam, px_chi, Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin]
  simp

private theorem px_isCont [TopologicalSpace G] (I : Ideal A) (ρ : G →* Matrix (Fin n) (Fin n) A)
    (h : ∀ i j, AdicCont I fun g => ρ g i j) : (W.GDet.ofRep ρ).IsCont I := by
  intro i N
  have h1 : IsLocallyConstant fun g => (ρ g).map (Ideal.Quotient.mk (I ^ N)) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have := fun p : Fin n × Fin n => (h p.1 p.2 N).eventually_eq x
    exact (Filter.eventually_all.2 this).mono fun y hy => Matrix.ext fun a b => hy (a, b)
  have h2 := h1.comp fun M : Matrix (Fin n) (Fin n) (A ⧸ I ^ N) => (-1) ^ i * M.charpoly.coeff (n - i)
  convert h2 using 1
  funext g
  simp only [W.GDet.lam, px_chi, Matrix.charpoly_map, Function.comp_apply, MonoidAlgebra.lift_single, one_smul,
    Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one]

private theorem px_prod {M : Type} [Ring M] [Algebra A M] : ∀ {m : ℕ} (c : Fin m → A) (a : Fin m → M),
    (List.ofFn fun i => c i • a i).prod = (List.ofFn c).prod • (List.ofFn a).prod
  | 0, _, _ => by simp
  | m + 1, c, a => by
    simp only [List.ofFn_succ, List.prod_cons]
    rw [px_prod, smul_mul_smul_comm]

private theorem px_comm [TopologicalSpace G] [IsTopologicalGroup G] [IsLocalRing A] [IsNoetherianRing A] (ψ : G →* Aˣ)
    (h : AdicCont (maximalIdeal A) fun g => (ψ g : A)) {g : G} (hg : g ∈ (commutator G).topologicalClosure) :
    (ψ g : A) = 1 := by
  have h1 : (ψ g : A) - 1 ∈ ⨅ N : ℕ, maximalIdeal A ^ N := Ideal.mem_iInf.2 fun N => by
    have h2 := (h N).isClopen_fiber (Ideal.Quotient.mk _ 1)
    refine Ideal.Quotient.eq.1 (closure_minimal (fun s hs => ?_) h2.isClosed hg)
    have h3 : ψ s = 1 := Abelianization.commutator_subset_ker ψ hs
    simp [h3]
  rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal A).ne_top, Ideal.mem_bot, sub_eq_zero] at h1

private theorem px_cont {Γ R R' : Type} [TopologicalSpace Γ] [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (f : R →+* R') [IsLocalHom f] {a : Γ → R} (h : AdicCont (maximalIdeal R) a) :
    AdicCont (maximalIdeal R') fun g => f (a g) := fun N => by
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap f :=
    le_trans (Ideal.pow_right_mono (fun y hy => map_nonunit f y hy) N) (Ideal.le_comap_pow _ N)
  exact (h N).comp (Ideal.quotientMap _ f hle)

private theorem px_mul {Γ : Type} [TopologicalSpace Γ] {I : Ideal A} {a b : Γ → A} (ha : AdicCont I a)
    (hb : AdicCont I b) : AdicCont I fun g => a g * b g := fun N => by
  convert (ha N).mul (hb N) using 1
  funext g
  exact map_mul (Ideal.Quotient.mk _) _ _

private theorem px_coef {O : Type} [CommRing O] [Algebra O A] (B : Subalgebra O A) (M : Matrix (Fin n) (Fin n) A)
    (c : A) (hc : c ∈ B)
    (h : ∀ α, MvPolynomial.coeff α (∑ a : Fin 2, (MvPolynomial.X a : MvPolynomial (Fin 2) A) •
      (![1, M] a).map (MvPolynomial.C : A →+* MvPolynomial (Fin 2) A)).det ∈ B) (i : ℕ) : (c • M).charpoly.coeff i ∈ B := by
  let φ : MvPolynomial (Fin 2) A →ₐ[A] Polynomial A := MvPolynomial.aeval ![Polynomial.X, -Polynomial.C c]
  have h1 : φ (∑ a : Fin 2, (MvPolynomial.X a : MvPolynomial (Fin 2) A) • (![1, M] a).map (MvPolynomial.C : A →+* MvPolynomial (Fin 2) A)).det =
      (c • M).charpoly := by
    rw [AlgHom.map_det]
    unfold Matrix.charpoly
    congr 1
    ext i j : 2
    by_cases h : i = j <;> simp [φ, Fin.sum_univ_two, Matrix.charmatrix_apply, h, Matrix.one_apply, sub_eq_add_neg]
  generalize (∑ a : Fin 2, (MvPolynomial.X a : MvPolynomial (Fin 2) A) • (![1, M] a).map (MvPolynomial.C : A →+* MvPolynomial (Fin 2) A)).det = P at h h1
  have h2 : φ P ∈ Polynomial.liftsRing (B.val : B →+* A) := by
    rw [P.as_sum, map_sum]
    refine sum_mem fun α _ => ?_
    rw [MvPolynomial.aeval_monomial]
    refine mul_mem ⟨Polynomial.C ⟨_, h α⟩, by simp⟩ (prod_mem fun a _ => pow_mem ?_ _)
    fin_cases a
    · exact ⟨Polynomial.X, by simp⟩
    · exact ⟨-Polynomial.C ⟨c, hc⟩, by simp⟩
  obtain ⟨q, hq⟩ := h2
  rw [← h1, ← hq]
  simp

end Gen

section Tw

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
  {F : Frame l (ResidueField O)} {n : ℕ} {G : W.GFrame l} {r : W.Resid G O n} (K : Pr.TwLink F r)
  {A : Type} [CommRing A] [Algebra O A]

private theorem px_star (ρ : NRep F n A) (g : G.G₀) :
    MonoidAlgebra.lift A _ G.G₀ (K.tw ρ) (G.star O A n (MonoidAlgebra.single g 1)) =
      Jmat A n * (K.tw ρ g)ᵀ * Jmat A n := by
  have h0 : G.star O A n (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single (G.conj g)⁻¹ ((G.eps O A g ^ (1 - (n : ℤ)) : Aˣ) : A) := by
    simp only [W.GFrame.star, W.GFrame.starOp, MonoidAlgebra.lift_single, one_smul]
    rfl
  have h1 : ρ.r (K.π (G.conj g)⁻¹) = Jmat A n * (ρ.r (K.π g))ᵀ * Jmat A n := by
    rw [← ρ.pol, map_inv K.π, K.π_conj, Frame.star, map_inv F.conj]
  have h2 : K.κA A g * K.κA A (G.conj g) = G.eps O A g ^ (1 - (n : ℤ)) := by
    have := congrArg (Units.map (algebraMap O A : O →* A)) (K.κ_conj g)
    rw [map_mul, map_zpow] at this
    exact this
  rw [h0, MonoidAlgebra.lift_single, ← h2]
  change _ • (((K.κA A (G.conj g)⁻¹ : Aˣ) : A) • ρ.r (K.π (G.conj g)⁻¹)) =
    Jmat A n * (((K.κA A g : Aˣ) : A) • ρ.r (K.π g))ᵀ * Jmat A n
  rw [h1, smul_smul, ← Units.val_mul, map_inv, mul_inv_cancel_right, Matrix.transpose_smul, Matrix.mul_smul,
    Matrix.smul_mul]

private theorem px_ord (ρ : NRep F n A) (v : G.Vl) (g : Fin n → G.Gv v) :
    MonoidAlgebra.lift A _ G.G₀ (K.tw ρ) (G.oEl v (K.twψ ρ v) g) = 0 := by
  have h := ρ.ord (K.e v) fun i => K.lam v (g i)
  have h1 := px_prod (fun i => ((K.κA A (G.φ v (g i)) : Aˣ) : A)) fun i =>
    ρ.r (F.loc0 (K.e v) (K.lam v (g i))) - (ρ.ψ (K.e v) i (K.lam v (g i)) : A) • (1 : Matrix (Fin n) (Fin n) A)
  rw [ordProd] at h
  rw [h, smul_zero] at h1
  rw [W.GFrame.oEl, map_list_prod, List.map_ofFn, ← h1]
  congr 2
  funext i
  simp only [Function.comp_apply, map_sub, MonoidAlgebra.lift_single, one_smul, map_one, smul_sub, smul_smul, K.lam_loc]
  rw [mul_comm]
  rfl

variable [IsCO O A]

private theorem px_red {ρ : NRep F n A} (h : IsLift O ρ) (g : G.G₀) :
    (K.tw ρ g).map (res O A) = W.diagRep r.chib g := by
  ext i j
  have h0 : ((K.tw ρ g).map (res O A)) i j = residue O (K.κ g) * res O A (ρ.r (K.π g) i j) := by
    change res O A (algebraMap O A (K.κ g) * ρ.r (K.π g) i j) = _
    rw [map_mul, AlgHom.commutes]
    rfl
  rw [h0]
  change _ = diagonal (fun i => ((r.chib i g : (ResidueField O)ˣ) : ResidueField O)) i j
  by_cases hij : i = j
  · subst hij
    rw [diagonal_apply_eq, K.chib, mul_comm]
    exact congrArg (· * _) (h.2.1.1 (K.π g) i)
  · rw [diagonal_apply_ne _ hij]
    exact (congrArg (_ * ·) (h.2.2 (K.π g) i j hij)).trans (mul_zero _)

private theorem px_ine [CharP (ResidueField O) l] {ρ : NRep F n A} (h : IsLift O ρ) (u : G.St) (g : G.G₀)
    (hg : g ∈ r.Ip u) : K.tw ρ g = 1 := by
  obtain ⟨m, hm, h1, h2⟩ := K.tame u g hg.1
  have hχ : ∀ i, r.chib i g = 1 := fun i => (Subgroup.mem_iInf.1 hg.2) i
  have h3 : (K.tw ρ g).map (res O A) = 1 := by
    rw [px_red K h]
    show diagonal (fun i => ((r.chib i g : (ResidueField O)ˣ) : ResidueField O)) = 1
    simp [hχ]
  have h4 : (K.tw ρ g).map (residue A) = 1 := by
    ext i j
    have h5 : res O A (K.tw ρ g i j - (1 : Matrix (Fin n) (Fin n) A) i j) = 0 := by
      rw [map_sub, sub_eq_zero]
      refine (congrFun (congrFun h3 i) j).trans ?_
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
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
    show ((K.κA _ (g ^ m) : Aˣ) : A) • ρ.r (K.π (g ^ m)) = 1
    have : K.κA A (g ^ m) = 1 := by
      show Units.map _ (K.κ (g ^ m)) = 1
      rw [map_pow, h2, map_one]
    rw [this, map_pow K.π, h1, map_one]
    simp

private theorem px_psi {ρ : NRep F n A} (h : IsLift O ρ) (v : G.Vl) (i : Fin n) : r.IsPsi v i (K.twψ ρ v i) := by
  have hc : AdicCont (maximalIdeal A) fun g => ((K.twψ ρ v i g : Aˣ) : A) :=
    px_mul (fun N => (h.1.2 (K.e v) i N).comp_continuous (K.lam v).continuous)
      fun N => (px_cont (algebraMap O A) K.κ_cont N).comp_continuous (G.φ_cont v)
  refine ⟨hc, fun g => ?_, fun g => ?_⟩
  · change res O A ((ρ.ψ (K.e v) i (K.lam v g) : A) * algebraMap O A (K.κ (G.φ v g))) = _
    rw [map_mul, AlgHom.commutes, K.psib, K.chib, ← K.lam_loc]
    exact congrArg (· * _) (h.2.1.2 (K.e v) i (K.lam v g))
  · rw [px_comm _ hc (K.mu v g.2), r.th_comm v i g (K.mu v g.2), Units.val_one, map_one]

private noncomputable def px_pair [CharP (ResidueField O) l] (hn : n ≠ 0) {ρ : NRep F n A} (h : IsLift O ρ) : W.Pair r A where
  D := W.GDet.ofRep (K.tw ρ)
  ψ := K.twψ ρ
  cont := px_isCont _ _ fun i j => px_mul (px_cont (algebraMap O A) K.κ_cont)
    fun N => (h.1.1 i j N).comp_continuous K.π_cont
  red := by
    rw [(CA.d_gmap (W.GDet.ofRep (K.tw ρ))).2.2.2]
    exact congrArg W.GDet.ofRep (MonoidHom.ext (px_red K h))
  psi := px_psi K h
  P i g := by
    rw [W.GDet.lam, W.GDet.lam, px_chi, px_chi, px_star, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, Jmat_mul_Jmat,
      Matrix.one_mul, Matrix.charpoly_transpose, MonoidAlgebra.lift_single, one_smul]
  Ord v g s := by rw [px_tr hn, map_mul, px_ord, mul_zero, trace_zero]
  I u g hg s := by
    rw [px_tr hn, map_mul, map_sub, map_one, MonoidAlgebra.lift_single _ g, px_ine K h u g hg, one_smul, sub_self,
      mul_zero, trace_zero]

end Tw

theorem UpperTheory.V.Pr.phiEx :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (n : ℕ) (T : UpperTheory.V.Pr.Setup F n), T.PhiEx := by
  intro l _ O _ _ _ _ _ F n T
  haveI : IsNoetherianRing O := PrincipalIdealRing.isNoetherianRing
  have hn : n ≠ 0 := by have := T.n23; omega
  obtain ⟨f, hf, -⟩ := T.B.univ T.S.R (px_pair T.K hn T.S.lift)
  replace hf : T.B.u.Maps (f : T.B.B →+* T.S.R) (W.GDet.ofRep (T.K.tw T.S.ρ)) (T.K.twψ T.S.ρ) := hf
  have hlam : ∀ i g, f (T.B.u.D.lam i (MonoidAlgebra.single g 1)) =
      (W.GDet.ofRep (T.K.tw T.S.ρ)).lam i (MonoidAlgebra.single g 1) := fun i g => by
    have := ((CA.d_gmap T.B.u.D).2.2.1 (f : T.B.B →+* T.S.R) (MonoidAlgebra.single g 1)).2 i
    rw [MonoidAlgebra.mapRingHom_single, map_one, hf.1] at this
    exact this.symm
  have hψ : ∀ v i g, f (T.B.u.ψ v i g) =
      (T.S.ρ.ψ (T.K.e v) i (T.K.lam v g) : T.S.R) * algebraMap O T.S.R (T.K.κ (T.G.φ v g)) :=
    fun v i g => congrArg Units.val (DFunLike.congr_fun (hf.2 v i) g)
  have hmem : ∀ x, f x ∈ T.S.B := fun x N => by
    obtain ⟨y, hy, hxy⟩ := CA.exists_adjoin_coeff_character_sub_mem_maximalIdeal_pow T.r T.B N x
    have h1 : f y ∈ T.S.B := by
      refine (Algebra.adjoin_le (S := T.S.B.comap f) ?_) hy
      rintro a (⟨i, g, -, -, rfl⟩ | ⟨v, i, g, rfl⟩)
      · show f _ ∈ T.S.B
        rw [hlam, W.GDet.lam, px_chi, MonoidAlgebra.lift_single, one_smul]
        refine mul_mem (pow_mem (neg_mem (one_mem _)) _) ?_
        refine px_coef T.S.B (T.S.ρ.r (T.K.π g)) _ (T.S.B.algebraMap_mem (T.K.κ g : O)) (fun α => ?_) _
        have h2 := det_mem T.ok T.n23 T.S 2 ![1, T.K.π g] α
        have h3 : ∀ a : Fin 2, T.S.ρ.r (![1, T.K.π g] a) = ![1, T.S.ρ.r (T.K.π g)] a := fun a => by
          fin_cases a
          · exact map_one T.S.ρ.r
          · rfl
        simp only [h3] at h2
        exact h2
      · show f _ ∈ T.S.B
        rw [hψ]
        exact mul_mem (T.S.ψ_mem _ _ _) (T.S.B.algebraMap_mem _)
    obtain ⟨z, hz, hyz⟩ := h1 N
    refine ⟨z, hz, ?_⟩
    have hle : maximalIdeal T.B.B ^ N ≤ (maximalIdeal T.S.R ^ N).comap (f : T.B.B →+* T.S.R) := by
      refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
      show f y ∈ maximalIdeal T.S.R
      rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
      exact hy
    have h3 : f (x - y) ∈ maximalIdeal T.S.R ^ N := hle hxy
    rw [map_sub] at h3
    simpa using add_mem h3 hyz
  have hun : ∀ (u : Oˣ) (x : T.S.R), x * algebraMap O T.S.R u ∈ f.range → x ∈ f.range := fun u x hx => by
    have := mul_mem hx (f.range.algebraMap_mem ((u⁻¹ : Oˣ) : O))
    rwa [mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one] at this
  have hle : T.S.B ≤ f.range := by
    refine B_gen T.ok T.n23 T.S T.B.B f (fun g => ?_) fun v i g => ?_
    · obtain ⟨g, rfl⟩ := T.K.π_surj g
      refine hun (T.K.κ g) _ ⟨T.B.u.D.lam 1 (MonoidAlgebra.single g 1), (hlam 1 g).trans ?_⟩
      rw [← W.GDet.tr, px_tr hn, MonoidAlgebra.lift_single, one_smul, mul_comm]
      exact trace_smul _ _
    · obtain ⟨v, rfl⟩ := T.K.e.surjective v
      obtain ⟨g, rfl⟩ := (T.K.lam v).surjective g
      exact hun _ _ ⟨_, hψ v i g⟩
  refine ⟨f.codRestrict T.S.B hmem, hf, fun y => ?_⟩
  obtain ⟨x, hx⟩ := hle y.2
  exact ⟨x, Subtype.ext hx⟩
