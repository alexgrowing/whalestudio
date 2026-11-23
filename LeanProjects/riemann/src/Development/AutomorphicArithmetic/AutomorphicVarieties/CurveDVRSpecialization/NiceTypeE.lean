import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransferAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceIrrE

set_option linter.overlappingInstances false

open Matrix UpperTheory.V UpperTheory.V.W UpperTheory.V.U3

namespace UpperTheory.V.Pr

private def blk {H K : Type} [Group H] [CommRing K] (ρ : H →* GL (Fin 3) K)
    (hz : ∀ g, mat ρ g 0 1 = 0 ∧ mat ρ g 1 0 = 0 ∧ mat ρ g 1 2 = 0 ∧ mat ρ g 2 1 = 0) :
    H →* GL (Fin 2) K :=
  MonoidHom.toHomUnits
    { toFun := fun g => (mat ρ g).submatrix ![0, 2] ![0, 2]
      map_one' := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
      map_mul' := fun g h => by
        obtain ⟨a1, a2, a3, a4⟩ := hz g
        obtain ⟨b1, b2, b3, b4⟩ := hz h
        ext i j
        simp only [map_mul, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply]
        fin_cases i <;> fin_cases j <;>
          simp [map_mul, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, a1, a2, a3, a4, b1, b2, b3, b4] }

private def mid {H K : Type} [Group H] [CommRing K] (ρ : H →* GL (Fin 3) K)
    (hz : ∀ g, mat ρ g 0 1 = 0 ∧ mat ρ g 1 0 = 0 ∧ mat ρ g 1 2 = 0 ∧ mat ρ g 2 1 = 0) :
    H →* GL (Fin 1) K :=
  MonoidHom.toHomUnits
    { toFun := fun g => (mat ρ g).submatrix ![1] ![1]
      map_one' := by
        ext i j
        fin_cases i; fin_cases j; simp
      map_mul' := fun g h => by
        obtain ⟨a1, a2, a3, a4⟩ := hz g
        ext i j
        simp only [map_mul, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply]
        fin_cases i; fin_cases j
        simp [map_mul, Matrix.mul_apply, Fin.sum_univ_three, a2, a3] }

private def eqv : Fin 3 ≃ Fin 2 ⊕ Fin 1 where
  toFun := ![.inl 0, .inr 0, .inl 1]
  invFun := Sum.elim ![0, 2] ![1]
  left_inv := by decide
  right_inv := by decide

private theorem irr_one {H K : Type} [Group H] [Field K] (U : Subgroup H) (a : H → Matrix (Fin 1) (Fin 1) K) :
    MatIrr U a := by
  intro W _
  by_cases hW : W = ⊥
  · exact Or.inl hW
  · right
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    have h0 : v 0 ≠ 0 := fun h => hv0 (funext fun i => by fin_cases i; exact h)
    rw [eq_top_iff]
    intro u _
    have hu : u = (u 0 / v 0) • v := funext fun i => by
      fin_cases i
      simp [div_mul_cancel₀ _ h0]
    rw [hu]
    exact W.smul_mem _ hv

private theorem hom_zero {H K : Type} [Group H] [Field K] (U : Subgroup H) (a : H → Matrix (Fin 2) (Fin 2) K)
    (b : H → Matrix (Fin 1) (Fin 1) K) (h : MatIrr U a) (M : Matrix (Fin 1) (Fin 2) K)
    (hM : ∀ g ∈ U, M * a g = b g * M) : M = 0 := by
  have hinv : ∀ g ∈ U, ∀ v ∈ LinearMap.ker M.mulVecLin, a g *ᵥ v ∈ LinearMap.ker M.mulVecLin := by
    intro g hg v hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, hM g hg, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  rcases h _ hinv with hb | ht
  · have hv : ![M 0 1, -M 0 0] ∈ LinearMap.ker M.mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      ext i
      fin_cases i
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    rw [hb, Submodule.mem_bot] at hv
    have h1 := congrFun hv 0
    have h2 := congrFun hv 1
    simp at h1 h2
    ext i j
    fin_cases i
    fin_cases j <;> simp [h1, h2]
  · ext i j
    have hj : (Pi.single j 1 : Fin 2 → K) ∈ LinearMap.ker M.mulVecLin := by
      rw [ht]
      trivial
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hj
    have := congrFun hj i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

private theorem tw_form {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    {F : Fr.Frame l (IsLocalRing.ResidueField O)} {n : ℕ} {G : W.GFrame l} {r : W.Resid G O n} (K : TwLink F r)
    {A : Type} [CommRing A] [Algebra O A] (ρ : Fr.NRep F n A) (g : G.G₀) :
    (K.tw ρ g)ᵀ * Jmat A n * K.tw ρ (G.conj g) = ((G.eps O A g ^ (1 - (n : ℤ)) : Aˣ) : A) • Jmat A n := by
  have hc : ∀ h : F.G0, F.conj h = F.star h⁻¹ := fun h => by simp [Fr.Frame.star]
  have hr : (ρ.r (K.π g))ᵀ * Jmat A n * ρ.r (F.conj (K.π g)) = Jmat A n := by
    rw [hc, ρ.pol]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc _ (Jmat A n) (Jmat A n), Jmat_mul_Jmat, Matrix.mul_one, ← Matrix.transpose_mul,
      ← map_mul, inv_mul_cancel, map_one, Matrix.transpose_one, Matrix.one_mul]
  have hκ : (K.κA A g : A) * (K.κA A (G.conj g) : A) = ((G.eps O A g ^ (1 - (n : ℤ)) : Aˣ) : A) := by
    have := congrArg (fun u : Oˣ => ((Units.map (algebraMap O A : O →* A) u : Aˣ) : A)) (K.κ_conj g)
    simp [TwLink.κA, GFrame.eps, pushCh, map_zpow] at this ⊢
    rw [this]
    rfl
  simp only [TwLink.tw, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
    K.π_conj, hr, smul_smul]
  rw [← hκ, mul_comm]

private theorem blk_form {K : Type} [CommRing K] (X Y : Matrix (Fin 3) (Fin 3) K) (c : K)
    (hX : X 0 1 = 0 ∧ X 1 0 = 0 ∧ X 1 2 = 0 ∧ X 2 1 = 0) (hY : Y 0 1 = 0 ∧ Y 1 0 = 0 ∧ Y 1 2 = 0 ∧ Y 2 1 = 0)
    (h : Xᵀ * Jmat K 3 * Y = c • Jmat K 3) :
    (X.submatrix ![0, 2] ![0, 2])ᵀ * Jmat K 2 * Y.submatrix ![0, 2] ![0, 2] = c • Jmat K 2 ∧
    (X.submatrix ![1] ![1])ᵀ * Jmat K 1 * Y.submatrix ![1] ![1] = c • Jmat K 1 := by
  obtain ⟨x1, x2, x3, x4⟩ := hX
  obtain ⟨y1, y2, y3, y4⟩ := hY
  have he : ∀ i j, (Xᵀ * Jmat K 3 * Y) i j = (c • Jmat K 3) i j := fun i j => by rw [h]
  constructor
  · ext i j
    have := he (![0, 2] i) (![0, 2] j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.smul_apply,
      Fin.sum_univ_two, Fin.sum_univ_three] at this ⊢
    fin_cases i <;> fin_cases j <;>
      simp [Jmat, x1, x2, x3, x4, y1, y2, y3, y4] at this ⊢ <;>
      linear_combination this
  · ext i j
    have := he 1 1
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.smul_apply,
      Fin.sum_univ_one, Fin.sum_univ_three] at this ⊢
    fin_cases i
    fin_cases j
    simp [Jmat, x1, x2, x3, x4, y1, y2, y3, y4] at this ⊢
    linear_combination this

private def JU (K : Type) [CommRing K] (n : ℕ) : GL (Fin n) K := ⟨Jmat K n, Jmat K n, Jmat_mul_Jmat n, Jmat_mul_Jmat n⟩

end UpperTheory.V.Pr

theorem UpperTheory.V.Pr.niceTypeE :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (T : UpperTheory.V.Pr.Setup F 3) (x : Ideal T.S.A) (L : T.S.Loc x) (y : UpperTheory.V.W.Point T.r) (j : L.R →ₐ[O] y.A), IsLocalHom j → UpperTheory.V.Pr.Nice L.ρ (RingHom.ker j) → UpperTheory.V.W.mat y.ρ = T.K.tw (L.ρ.map (j : L.R →+* y.A)) → y.ψ = T.K.twψ (L.ρ.map (j : L.R →+* y.A)) → L.ρ.TE (RingHom.ker j) → y.TypeE := by
  intro l _ O _ _ _ _ _ F T x L y j hj hN hmat hψ hTE
  have hee : L.ρ.ee ≤ RingHom.ker j := hTE.2.2
  have hz0 : ∀ g (i k : Fin 3), Odd (Fr.w 3 i - Fr.w 3 k) → mat y.ρ g i k = 0 := by
    intro g i k hodd
    have hm : L.ρ.r (T.K.π g) i k ∈ RingHom.ker j := hee (Ideal.subset_span ⟨_, i, k, hodd, rfl⟩)
    rw [RingHom.mem_ker] at hm
    rw [hmat]
    simp [TwLink.tw, Fr.NRep.map, hm]
  have hz : ∀ g, mat y.ρF g 0 1 = 0 ∧ mat y.ρF g 1 0 = 0 ∧ mat y.ρF g 1 2 = 0 ∧ mat y.ρF g 2 1 = 0 := by
    intro g
    have e : ∀ i k, Odd (Fr.w 3 i - Fr.w 3 k) → mat y.ρF g i k = 0 := fun i k h => by
      show algebraMap y.A y.Fr (mat y.ρ g i k) = 0
      rw [hz0 g i k h, map_zero]
    refine ⟨e 0 1 ?_, e 1 0 ?_, e 1 2 ?_, e 2 1 ?_⟩ <;> decide
  have hF : ∀ g, (mat y.ρF g)ᵀ * Jmat y.Fr 3 * mat y.ρF (T.G.conj g) =
      ((T.G.eps O y.Fr g ^ (1 - ((3 : ℕ) : ℤ)) : y.Frˣ) : y.Fr) • Jmat y.Fr 3 := by
    intro g
    have h := UpperTheory.V.Pr.tw_form T.K (L.ρ.map (j : L.R →+* y.A)) g
    rw [← hmat] at h
    have h2 := congrArg (fun M => M.map (algebraMap y.A y.Fr)) h
    have heps : (T.G.eps O y.Fr g ^ (1 - ((3 : ℕ) : ℤ)) : y.Frˣ) =
        Units.map (algebraMap y.A y.Fr : y.A →* y.Fr) (T.G.eps O y.A g ^ (1 - ((3 : ℕ) : ℤ))) := by
      rw [map_zpow]
      congr 1
    have hs : ∀ (c : y.A) (M : Matrix (Fin 3) (Fin 3) y.A),
        (c • M).map (algebraMap y.A y.Fr) = algebraMap y.A y.Fr c • M.map (algebraMap y.A y.Fr) := fun c M => by
      ext
      simp
    rw [heps]
    simp only [Matrix.map_mul, Matrix.transpose_map, Jmat_map] at h2
    rw [hs, Jmat_map] at h2
    exact h2
  have hB := fun g => UpperTheory.V.Pr.blk_form _ _ _ (hz g) (hz (T.G.conj g)) (hF g)
  have hb : ∀ g, mat (UpperTheory.V.Pr.blk y.ρF hz) g = (mat y.ρF g).submatrix ![0, 2] ![0, 2] := fun g => rfl
  have hm : ∀ g, mat (UpperTheory.V.Pr.mid y.ρF hz) g = (mat y.ρF g).submatrix ![1] ![1] := fun g => rfl
  have hirr := UpperTheory.V.Pr.niceIrrE l O F T x L y j hj hN hmat hψ hTE ⊤ isOpen_univ
  rw [top_inf_eq] at hirr
  have hirr1 : MatIrr T.G.G' (mat (pushRep (algebraMap y.Fr y.Fb) (UpperTheory.V.Pr.blk y.ρF hz))) := hirr
  refine ⟨2, 1, by norm_num, le_rfl, UpperTheory.V.Pr.eqv, 1, UpperTheory.V.Pr.blk y.ρF hz, UpperTheory.V.Pr.mid y.ρF hz,
    ?_, ⟨UpperTheory.V.Pr.JU _ 2, ?_⟩, ⟨UpperTheory.V.Pr.JU _ 1, ?_⟩, hirr1, UpperTheory.V.Pr.irr_one _ _, ?_⟩
  · intro g
    have h1 : ((1 * y.ρF g * 1⁻¹ : GL (Fin 3) y.Fr) : Matrix (Fin 3) (Fin 3) y.Fr) = mat y.ρF g := by
      simp [mat]
    obtain ⟨a1, a2, a3, a4⟩ := hz g
    rw [h1, hb, hm]
    ext (i | i) (k | k) <;> fin_cases i <;> fin_cases k
    all_goals first
      | rfl
      | (simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂,
          Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
         first | exact a1 | exact a2 | exact a3 | exact a4)
  · intro g
    rw [hb, hb]
    exact (hB g).1
  · intro g
    rw [hm, hm]
    exact (hB g).2
  · intro M hM
    exact UpperTheory.V.Pr.hom_zero _ _ _ hirr1 M hM
