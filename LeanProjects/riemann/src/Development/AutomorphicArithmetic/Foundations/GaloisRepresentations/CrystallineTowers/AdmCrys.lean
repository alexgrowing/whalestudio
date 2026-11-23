import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.CrystallinePeriodsOfSmooth
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JointApproxOfMem
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorProductBasisCoordinates
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankInvariantsEqOfInvertiblePeriodMatrix
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

open TensorProduct in
private theorem isCrys_qRep {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) {d : ℕ}
    (r : ↥(GK K) →* GL (Fin d) ℚ_[l]) (Q : GL (Fin d) P.R.B)
    (hQ : ∀ g : ↥(GK K), ((r g).val.map (algebraMap ℚ_[l] P.R.B)) *
      (Q : Matrix (Fin d) (Fin d) P.R.B).map (P.actQ (g : GQ l)) = Q) :
    Formalism.WeaklyAdmissibleFiltrations.IsCrys (P.PD K) (((Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℚ_[l] ≃ₐ[ℚ_[l]] _) : _ →* _).comp
      ((Units.coeHom _).comp r) : Representation ℚ_[l] ↥(GK K) (Fin d → ℚ_[l])) := by
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := (P.PD K).finK₀
  haveI : Nontrivial P.R.B := by
    refine ⟨⟨(P.PD K).t, 0, fun h => (P.PD K).not_mem_filtration_two ?_⟩⟩
    rw [h, map_zero]
    exact Submodule.zero_mem _
  set ρ : Representation ℚ_[l] ↥(GK K) (Fin d → ℚ_[l]) :=
    ((Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℚ_[l] ≃ₐ[ℚ_[l]] _) : _ →* _).comp
      ((Units.coeHom _).comp r) with hρ
  let b := Pi.basisFun ℚ_[l] (Fin d)
  have hmat : ∀ g : ↥(GK K), LinearMap.toMatrix b b (ρ g) = (r g).val := by
    intro g
    rw [LinearMap.toMatrix_eq_toMatrix']
    ext i j
    simp [ρ, LinearMap.toMatrix'_apply, Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
  obtain ⟨e, -, -, he⟩ := GlobalTheory.tensorBasisCoords ℚ_[l] P.R.B (Fin d → ℚ_[l]) (Fin d) b
  have key := GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix ℚ_[l] ↥(K0 K) P.R.B ↥(GK K)
    (fun g => ((P.PD K).actB g).toRingEquiv.toRingHom) (Fin d)
    (fun g => (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] P.R.B))
    (fun x => ⟨fun h => (P.PD K).invB x h, by
      rintro ⟨c, rfl⟩ g
      exact ((P.PD K).actB g).commutes c⟩) Q
    (fun g => by
      rw [hmat g]
      have hB : (Q : Matrix (Fin d) (Fin d) P.R.B).map (((P.PD K).actB g).toRingEquiv.toRingHom) =
          (Q : Matrix (Fin d) (Fin d) P.R.B).map (P.actQ (g : GQ l)) := by
        ext i j
        simp only [Matrix.map_apply]
        exact P.PD_actB K g _
      rw [hB]
      exact hQ g)
    ((Formalism.WeaklyAdmissibleFiltrations.Dcris (P.PD K) ρ).map (e : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.B →ₗ[ℚ_[l]] (Fin d → P.R.B)))
    (fun x => by
      obtain ⟨y, rfl⟩ := e.surjective x
      have h1 : e y ∈ (Formalism.WeaklyAdmissibleFiltrations.Dcris (P.PD K) ρ).map (e : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.B →ₗ[ℚ_[l]] (Fin d → P.R.B)) ↔
          y ∈ Formalism.WeaklyAdmissibleFiltrations.Dcris (P.PD K) ρ := by
        constructor
        · rintro ⟨z, hz, hzy⟩
          have : z = y := e.injective hzy
          exact this ▸ hz
        · exact fun h => ⟨y, h, rfl⟩
      rw [h1]
      simp only [Formalism.WeaklyAdmissibleFiltrations.Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      refine forall_congr' fun g => ?_
      have h2 := he (ρ g) (((((P.PD K).actB g).toAlgHom.toLinearMap).restrictScalars ℚ_[l])) y
      have h3 : Formalism.WeaklyAdmissibleFiltrations.actVB (P.PD K) ρ g y = TensorProduct.map (ρ g)
          ((((P.PD K).actB g).toAlgHom.toLinearMap).restrictScalars ℚ_[l]) y := rfl
      rw [h3, ← e.injective.eq_iff, h2]
      rfl)
  rw [LinearEquiv.finrank_map_eq, Fintype.card_fin] at key
  rw [Formalism.WeaklyAdmissibleFiltrations.IsCrys, key, Module.finrank_fin_fun]

private theorem isCrys_of_mats {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K L : FinExt l) {d : ℕ}
    (r : ↥(GK K) →* GL (Fin d) ℚ_[l]) (r' : ↥(GK K) →* GL (Fin d) ↥L.1)
    (hr : ∀ σ i j, (r' σ).val i j = algebraMap ℚ_[l] ↥L.1 ((r σ).val i j))
    (A B : Matrix (Fin d) (Fin d) P.R.BdR)
    (hm : ∀ i j, A i j ∈ Set.range P.ιB ∧ B i j ∈ Set.range P.ιB) (hAB : A * B = 1)
    (hσ : ∀ σ : ↥(GK K), ((r σ).val).map (algebraMap ℚ_[l] P.R.BdR) * A.map (P.actQdR (σ : GQ l)) = A) :
    Formalism.WeaklyAdmissibleFiltrations.IsCrys (P.PD K) (GlobalTheory.CongPhi.matRep L r') := by
  choose a ha using fun i j => (hm i j).1
  choose c hc using fun i j => (hm i j).2
  let A' : Matrix (Fin d) (Fin d) P.R.B := Matrix.of a
  let B' : Matrix (Fin d) (Fin d) P.R.B := Matrix.of c
  have hA' : A'.map P.ιB = A := Matrix.ext fun i j => ha i j
  have hB' : B'.map P.ιB = B := Matrix.ext fun i j => hc i j
  have hinj : Function.Injective (fun X : Matrix (Fin d) (Fin d) P.R.B => X.map P.ιB) :=
    fun X Y h => Matrix.ext fun i j => GlobalTheory.PMon.iota_injective P (congrFun (congrFun h i) j)
  have hmapmul : ∀ X Y : Matrix (Fin d) (Fin d) P.R.B, (X * Y).map P.ιB = X.map P.ιB * Y.map P.ιB :=
    fun X Y => Matrix.map_mul (f := (P.ιB : P.R.B →+* P.R.BdR))
  have h1 : A' * B' = 1 := hinj (by
    show (A' * B').map P.ιB = (1 : Matrix (Fin d) (Fin d) P.R.B).map P.ιB
    rw [hmapmul, hA', hB', hAB, Matrix.map_one _ (map_zero _) (map_one _)])
  let Q : GL (Fin d) P.R.B := ⟨A', B', h1, mul_eq_one_comm.1 h1⟩
  have hQ := isCrys_qRep P K r Q (fun g => hinj (by
    show ((r g).val.map (algebraMap ℚ_[l] P.R.B) * A'.map (P.actQ (g : GQ l))).map P.ιB = A'.map P.ιB
    rw [hmapmul, hA']
    have e1 : ((r g).val.map (algebraMap ℚ_[l] P.R.B)).map P.ιB = (r g).val.map (algebraMap ℚ_[l] P.R.BdR) := by
      ext i j
      simp
    have e2 : (A'.map (P.actQ (g : GQ l))).map P.ιB = A.map (P.actQdR (g : GQ l)) := by
      rw [← hA']
      ext i j
      simp only [Matrix.map_apply]
      exact GlobalTheory.PMon.iota_act P _ _
    rw [e1, e2]
    exact hσ g))
  haveI := L.2
  refine (GlobalTheory.Pst.isCrys_ext_iff (P.PD K) (fun g => ⟨(r g : Matrix (Fin d) (Fin d) ℚ_[l]), fun x => rfl, fun x => ?_⟩)).2 hQ
  have : (r' g).val = (r g).val.map (algebraMap ℚ_[l] ↥L.1) := Matrix.ext fun i j => hr g i j
  show (r' g).val.mulVec x = _
  rw [this]

theorem UpperTheory.Gal.Seam.isCrys_of_isAdmP :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K L : FinExt l) (d : ℕ) (r : ↥(GK K) →* GL (Fin d) ℚ_[l]) (r' : ↥(GK K) →* GL (Fin d) ↥L.1), (∀ σ i j, (r' σ).val i j = algebraMap ℚ_[l] ↥L.1 ((r σ).val i j)) → UpperTheory.Gal.Seam.IsAdmP P (GK K) (fun σ => (r σ : Matrix (Fin d) (Fin d) ℚ_[l])) → Formalism.WeaklyAdmissibleFiltrations.IsCrys (P.PD K) (GlobalTheory.CongPhi.matRep L r') := by
  intro l _ P AI _ K L d r r' hr hA
  obtain ⟨A, B, hm, hAB, hσ⟩ := hA
  exact isCrys_of_mats P K L r r' hr A B hm hAB hσ
