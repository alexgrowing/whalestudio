import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DOfRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GChmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetOfRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetCH

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem lift_eq {n : ℕ} {B C G : Type} [CommRing B] [CommRing C] [Algebra B C] [Group G]
    (ρ : G →* Matrix (Fin n) (Fin n) C) (z : MonoidAlgebra B G) :
    MonoidAlgebra.lift B _ G ρ z = GDet.repAlg ρ C (MonoidAlgebra.mapRingHom G (algebraMap B C) z) := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g r => ext i j; simp [GDet.repAlg, Algebra.smul_def]

private theorem lift_CH {n : ℕ} {B C G : Type} [CommRing B] [CommRing C] [Algebra B C] [Group G]
    (D : GDet n B G) (ρ : G →* Matrix (Fin n) (Fin n) C) (h : D.map (algebraMap B C) = GDet.ofRep ρ)
    (z : MonoidAlgebra B G) (hz : z ∈ D.CH) : MonoidAlgebra.lift B _ G ρ z = 0 := by
  rw [lift_eq]
  refine (d_ofRep (Fintype.card_fin n) (GDet.repAlg ρ C) _).2.2.2 ?_
  rw [← d_toDet_ofRep.1 ρ, d_toDet_CH, ← h, g_chmap]
  exact TwoSidedIdeal.subset_span ⟨z, hz, rfl⟩

theorem UpperTheory.V.CA.f_rep :
    ∀ {n : ℕ} {B C G : Type} [CommRing B] [IsLocalRing B] [CommRing C] [Algebra B C] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (J : Ideal C) [IsHausdorff J C] (D : GDet n B G) (ρ : G →* Matrix (Fin n) (Fin n) C) (Z : Set (MonoidAlgebra B G)), maximalIdeal B ≤ J.comap (algebraMap B C) → (∀ a b, AdicCont J fun g => ρ g a b) → D.map (algebraMap B C) = GDet.ofRep ρ → (∀ z ∈ Z, MonoidAlgebra.lift B _ G ρ z = 0) → ∃ r : D.CHQuot Z →ₐ[B] Matrix (Fin n) (Fin n) C, ∀ g, r (D.toQuot Z (MonoidAlgebra.single g 1)) = ρ g := by
  intro n B C G _ _ _ _ _ _ _ _ _ J _ D ρ Z hm hc hD hZ
  have key : ∀ z ∈ D.chBar Z, MonoidAlgebra.lift B _ G ρ z = 0 := by
    intro z hz
    ext a b
    refine IsHausdorff.haus (I := J) inferInstance _ fun N => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    have hU : IsOpen (⋂ a, ⋂ b, {g : G | Ideal.Quotient.mk (J ^ N) (ρ g a b) = Ideal.Quotient.mk (J ^ N) (ρ 1 a b)}) :=
      isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => (hc a b N).isOpen_fiber _
    obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU (by simp)
    let φ : MonoidAlgebra B G →+* Matrix (Fin n) (Fin n) (C ⧸ J ^ N) :=
      (Ideal.Quotient.mk (J ^ N)).mapMatrix.comp (MonoidAlgebra.lift B _ G ρ).toRingHom
    have hφ : ∀ y, φ y = (MonoidAlgebra.lift B _ G ρ y).map (Ideal.Quotient.mk (J ^ N)) := fun _ => rfl
    have hle : D.chBar Z ≤ TwoSidedIdeal.ker φ := by
      refine (iInf₂_le N H).trans ?_
      rw [TwoSidedIdeal.span_le]
      intro y hy
      change _ ∈ TwoSidedIdeal.ker φ
      rw [TwoSidedIdeal.mem_ker]
      rcases hy with ((hy | hy) | ⟨x, hx, rfl⟩) | ⟨h, hh, rfl⟩
      · rw [hφ, lift_CH D ρ hD y hy]; simp
      · rw [hφ, hZ y hy]; simp
      · have hx' : algebraMap B C x ∈ J ^ N :=
          Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hm) N
            (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hx)
        ext i j
        rw [hφ, MonoidAlgebra.lift_single, Matrix.map_apply, Matrix.smul_apply, Algebra.smul_def, Matrix.zero_apply,
          Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mul_mem_right _ _ hx'
      · rw [map_sub, map_one, sub_eq_zero, ← φ.map_one]
        ext i j
        have := Set.mem_iInter.1 (Set.mem_iInter.1 (hH hh) i) j
        rw [hφ, hφ, map_one, MonoidAlgebra.lift_single, one_smul, ← ρ.map_one]
        exact this
    have := congrFun (congrFun ((TwoSidedIdeal.mem_ker φ).1 (hle hz)) a) b
    rw [hφ] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  refine ⟨RingCon.liftₐ _ (MonoidAlgebra.lift B _ G ρ) fun x y hxy => ?_, fun g => ?_⟩
  · have := key _ ((TwoSidedIdeal.rel_iff _ _ _).1 hxy)
    rwa [map_sub, sub_eq_zero] at this
  · change MonoidAlgebra.lift B _ G ρ _ = _
    simp
