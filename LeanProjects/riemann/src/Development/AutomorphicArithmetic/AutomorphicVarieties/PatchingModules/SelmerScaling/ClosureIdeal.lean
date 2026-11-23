import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem chi_rep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [Matrix.charpoly, Matrix.charmatrix]
  congr 1
  rw [map_sub, MonoidAlgebra.mapRingHom_single, map_one]
  ext i j : 2
  simp [GDet.repAlg, Matrix.one_apply, Matrix.diagonal_apply]

private theorem rep_single {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Algebra B A] [Group G]
    (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) (b : B) :
    GDet.repAlg ρ A (MonoidAlgebra.mapRingHom G (algebraMap B A) (MonoidAlgebra.single g b)) =
      algebraMap B A b • ρ g := by
  rw [MonoidAlgebra.mapRingHom_single]
  ext i j
  simp [GDet.repAlg]

theorem UpperTheory.V.Pa.vrRel :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), (∀ v (g : Fin S.n → S.L.Gv v), (List.ofFn fun i => S.U.vr (S.G.φ v (g i)) - algebraMap S.U.AA (Matrix (Fin S.n) (Fin S.n) S.U.AA) (algebraMap S.B S.U.AA (S.u.ψ v i (g i)))).prod = 0) ∧ (∀ w, ∀ g ∈ S.G.frame.Iu w, S.U.vr g = 1) ∧ (∀ j, (List.ofFn fun i => S.U.vr (S.P.ph j) - algebraMap S.U.AA (Matrix (Fin S.n) (Fin S.n) S.U.AA) (algebraMap S.B S.U.AA (S.P.U j i))).prod = 0) ∧ (∀ j i, (List.ofFn fun k => if k = i then 1 else S.U.vr (S.P.ph j) - algebraMap S.U.AA (Matrix (Fin S.n) (Fin S.n) S.U.AA) (algebraMap S.B S.U.AA (S.P.U j k))).prod * (S.U.vr (S.P.ta j) - 1 - algebraMap S.U.AA (Matrix (Fin S.n) (Fin S.n) S.U.AA) (algebraMap S.B S.U.AA (S.P.y j i))) = 0) ∧ ∀ i g, algebraMap S.B S.U.AA (S.u.D.lam i (MonoidAlgebra.single g 1)) = (-1) ^ i * (S.U.vr g).charpoly.coeff (S.n - i) := by
  intro l _ S
  let Φ : MonoidAlgebra S.B S.G.G₀ →+* Matrix (Fin S.n) (Fin S.n) S.U.AA :=
    (GDet.repAlg S.U.vr S.U.AA).toRingHom.comp (MonoidAlgebra.mapRingHom S.G.G₀ (algebraMap S.B S.U.AA))
  have h1 : ∀ g : S.G.G₀, Φ (MonoidAlgebra.single g 1) = S.U.vr g := fun g =>
    (rep_single S.U.vr g (1 : S.B)).trans (by rw [map_one, one_smul])
  have h2 : ∀ b : S.B, Φ (MonoidAlgebra.single 1 b) =
      algebraMap S.U.AA (Matrix (Fin S.n) (Fin S.n) S.U.AA) (algebraMap S.B S.U.AA b) := fun b =>
    (rep_single S.U.vr 1 b).trans (by rw [map_one, Algebra.algebraMap_eq_smul_one (A := Matrix _ _ _)])
  have hk : ∀ z ∈ pairGens S.u ∪ qGens (O := S.O) (F := S.G.frame) S.P.ph S.P.ta S.P.U S.P.y, Φ z = 0 := by
    intro z hz
    refine S.U.kills z ?_
    change z ∈ S.u.D.chBar _
    simp only [GDet.chBar, closureIdeal, TwoSidedIdeal.mem_iInf]
    exact fun N H => TwoSidedIdeal.subset_span (Or.inl (Or.inl (Or.inr hz)))
  refine ⟨fun v g => ?_, fun w g hg => ?_, fun j => ?_, fun j i => ?_, fun i g => ?_⟩
  · rw [← hk (S.G.frame.oEl v (S.u.ψ v) g) (Or.inl (Or.inl ⟨v, g, Or.inl rfl⟩)), GFrame.oEl, map_list_prod,
      List.map_ofFn]
    congr 2
    funext k
    simp only [Function.comp_apply]
    rw [map_sub, h1, h2]
  · have := hk _ (Or.inl (Or.inr ⟨w, g, (S.P.Ip w).symm ▸ hg, Or.inl rfl⟩))
    rwa [map_sub, h1, map_one, sub_eq_zero] at this
  · rw [← hk _ (Or.inr (Or.inl ⟨j, Or.inl rfl⟩)), q1El, map_list_prod, List.map_ofFn]
    congr 2
    funext k
    simp only [Function.comp_apply]
    rw [map_sub, h1, h2]
  · rw [← hk _ (Or.inr (Or.inr ⟨j, i, Or.inl rfl⟩)), q2El, map_mul, map_list_prod, List.map_ofFn, map_sub, map_sub,
      h1, h2, map_one]
    congr 3
    funext k
    simp only [Function.comp_apply]
    split_ifs
    · rw [map_one]
    · rw [map_sub, h1, h2]
  · rw [← ((UpperTheory.V.CA.d_gmap S.u.D).2.2.1 (algebraMap S.B S.U.AA) _).2 i, S.U.det, MonoidAlgebra.mapRingHom_single,
      map_one, GDet.lam, chi_rep]
