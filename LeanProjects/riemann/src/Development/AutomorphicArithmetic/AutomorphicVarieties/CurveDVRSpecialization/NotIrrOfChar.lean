import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType

open Matrix Polynomial UpperTheory.V.U3 Formalism.MainNotions.N

private noncomputable def diagRep {G κ : Type} [Group G] [Field κ] {n : ℕ} (χ : Fin n → G →* κˣ) :
    G →* GL (Fin n) κ :=
  (Units.map (Matrix.diagonalRingHom (Fin n) κ).toMonoidHom).comp
    ((MulEquiv.piUnits (M := fun _ : Fin n => κ)).symm.toMonoidHom.comp (MonoidHom.pi χ))

private theorem diagRep_val {G κ : Type} [Group G] [Field κ] {n : ℕ} (χ : Fin n → G →* κˣ) (g : G) :
    (diagRep χ g : Matrix (Fin n) (Fin n) κ) = diagonal fun i => ((χ i g : κˣ) : κ) := rfl

private theorem diagRep_single {G κ : Type} [Group G] [Field κ] {n : ℕ} (χ : Fin n → G →* κˣ) (g : G)
    (i : Fin n) : (diagRep χ g : Matrix (Fin n) (Fin n) κ) *ᵥ Pi.single i 1 =
      ((χ i g : κˣ) : κ) • (Pi.single i 1 : Fin n → κ) := by
  ext j
  rw [diagRep_val, mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  by_cases h : j = i
  · subst h
    simp
  · simp [Pi.single_apply, h]

private theorem diagRep_span {G κ ι : Type} [Group G] [Field κ] {n : ℕ} (χ : Fin n → G →* κˣ) (a : ι → Fin n) :
    IsInv (diagRep χ) (Submodule.span κ (Set.range fun i => (Pi.single (a i) 1 : Fin n → κ))) := by
  intro g v hv
  have hle : Submodule.span κ (Set.range fun i => (Pi.single (a i) 1 : Fin n → κ)) ≤
      (Submodule.span κ (Set.range fun i => (Pi.single (a i) 1 : Fin n → κ))).comap
        (Matrix.mulVecLin (diagRep χ g : Matrix (Fin n) (Fin n) κ)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply, diagRep_single]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact hle hv

private theorem diagRep_ss {G κ : Type} [Group G] [Field κ] {n : ℕ} (χ : Fin n → G →* κˣ) :
    IsSSRep (diagRep χ) := by
  classical
  intro W hW
  obtain ⟨I, hI, hmax⟩ := Finset.exists_max_image ((Finset.univ : Finset (Finset (Fin n))).filter
      (fun I : Finset (Fin n) => Disjoint W
        (Submodule.span κ ((fun i => (Pi.single i 1 : Fin n → κ)) '' (I : Set (Fin n))))))
      Finset.card ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp⟩⟩
  rw [Finset.mem_filter] at hI
  refine ⟨Submodule.span κ ((fun i => (Pi.single i 1 : Fin n → κ)) '' (I : Set (Fin n))), ?_, hI.2, ?_⟩
  · rw [Set.image_eq_range]
    exact diagRep_span χ (fun i : (I : Set (Fin n)) => (i : Fin n))
  · rw [codisjoint_iff, eq_top_iff, ← (Pi.basisFun κ (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [Pi.basisFun_apply]
    by_contra hj
    have hne : (Pi.single j 1 : Fin n → κ) ≠ 0 := by simp
    have hjI : j ∉ I := fun h => hj (Submodule.mem_sup_right (Submodule.subset_span ⟨j, h, rfl⟩))
    have hd : Disjoint W (Submodule.span κ ((fun i => (Pi.single i 1 : Fin n → κ)) ''
        ((insert j I : Finset (Fin n)) : Set (Fin n)))) := by
      rw [Finset.coe_insert, Set.image_insert_eq, Submodule.span_insert, sup_comm]
      exact hI.2.disjoint_sup_right_of_disjoint_sup_left ((Submodule.disjoint_span_singleton' hne).2 hj)
    have hc := hmax (insert j I) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hd⟩)
    rw [Finset.card_insert_of_notMem hjI] at hc
    omega

theorem UpperTheory.V.Pr.notIrrOfChar :
    UpperTheory.V.Pr.NotIrrOfChar := by
  intro G κ _ _ n hn r χ hch hirr
  have ssr : IsSSRep r := by
    intro W hW
    rcases hirr W (fun g _ v hv => hW g v hv) with rfl | rfl
    · exact ⟨⊤, fun g v _ => Submodule.mem_top, isCompl_bot_top⟩
    · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
      rw [(Submodule.mem_bot κ).1 hv, mulVec_zero]
      exact Submodule.zero_mem _
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix (diagRep χ) r (diagRep_ss χ) ssr
    (fun g => by rw [diagRep_val, charpoly_diagonal]; exact (hch g).symm)
  have hn0 : 0 < n := by omega
  set e0 : Fin n → κ := Pi.single (⟨0, hn0⟩ : Fin n) 1 with he0
  set v : Fin n → κ := ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) *ᵥ e0 with hv
  have hvne : v ≠ 0 := by
    intro h0
    have hPv : ((P : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) *ᵥ v = e0 := by
      rw [hv, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    rw [h0, mulVec_zero] at hPv
    have h1 := congrFun hPv ⟨0, hn0⟩
    simp [he0] at h1
  have hinv : ∀ g ∈ (⊤ : Subgroup G), ∀ u ∈ κ ∙ v, UpperTheory.V.Pr.gm r g *ᵥ u ∈ κ ∙ v := by
    intro g _ u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
    have hrg : UpperTheory.V.Pr.gm r g = ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) *
        (diagRep χ g : Matrix (Fin n) (Fin n) κ) * ((P : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) := by
      show ((r g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) = _
      rw [hP g, Units.val_mul, Units.val_mul]
    rw [mulVec_smul, hrg, hv, mulVec_mulVec, Matrix.mul_assoc, ← Units.val_mul P, mul_inv_cancel,
      Units.val_one, Matrix.mul_one, ← mulVec_mulVec, he0, diagRep_single, mulVec_smul, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  rcases hirr (κ ∙ v) hinv with h | h
  · exact hvne ((Submodule.span_singleton_eq_bot).1 h)
  · have hr := finrank_span_singleton (K := κ) hvne
    rw [h, finrank_top, Module.finrank_fin_fun] at hr
    omega
