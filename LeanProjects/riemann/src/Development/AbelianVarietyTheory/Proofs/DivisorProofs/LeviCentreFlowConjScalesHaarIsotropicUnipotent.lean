import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrOfIsotropic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalCoordinatesGroupLaw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFrameCoordsOfMemIsotropicUnipoten
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentRadicalPointWithCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviSectionIsotropicFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicFrameDecompositionSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameLeviNormalizesRadicalProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectHaarMeasureProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSkewA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddHaarCharLeftRightMatrixMulAdeleTensorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddHaarCharSkewHermitianNormScaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousChartIsotropicUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviConjScalarIdeleUnipotentCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitSmulOfCentralParabolicLeviStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

noncomputable section
namespace GlobalTheory.ResidueEisenstein.ModConj

set_option maxHeartbeats 1000000 in

theorem modulus_conj_flow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ b, IsFlowJ σ J X Y b → ∀ ν : Measure (unipRad σ J X), ν.IsHaarMeasure → ∀ (t : ℝ) (f : GAd σ J → ℝ≥0∞), Measurable f → ∫⁻ u : unipRad σ J X, f (b t * u * (b t)⁻¹) ∂ν = ENNReal.ofReal (Real.exp (-(((n : ℝ) - (r + 1)) * t))) * ∫⁻ u : unipRad σ J X, f u ∂ν := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW b hb ν hν t f hf
  classical
  obtain ⟨m, Z, J₀, hF⟩ := GlobalTheory.SphEis.exists_fr_of_isotropic F E σ h n J hJ (r + 1) X Y hW.xx hW.yy hW.xy
  obtain ⟨lv, hlv⟩ := GlobalTheory.SphEis.exists_isLv F E σ n J (r + 1) m X Y Z J₀ hF
  have hlaw := GlobalTheory.SphEis.crd_law F E σ n J (r + 1) m X Y Z J₀ hF lv hlv
  have hmem := hb.mem t
  obtain ⟨l, hl⟩ := GlobalTheory.T.exists_unit_smul_of_central_parabolicLevi F E σ n J r m X Y Z J₀ hF (b t) hmem (fun k hk => hb.comm t k hk)
  obtain ⟨γ, hγ⟩ : ∃ γ : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E),
      (matHom _ σ J (b t)).1 * adMat F Y = adMat F Y * γ := by
    have h1 := hmem
    simp only [GlobalTheory.StdPar.levi, Subgroup.mem_iInf] at h1
    obtain ⟨B, -, e⟩ := (h1 (Fin.last r) (Finset.mem_singleton_self _)).2
    exact ⟨B.1, e⟩
  obtain ⟨δ, hδdet, hδJ, hconj⟩ := GlobalTheory.T.leviConj_scalarIdele_unipotentCoordinates F E σ n J (r + 1) m X Y Z J₀ hF (b t) l γ hl hγ
  have habs : ((absE F E l : ℝ≥0) : ℝ) ^ (r + 1) = Real.exp t := by
    obtain ⟨β, hβ, hβt⟩ := hb.onX t
    have hL : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
      rw [← Matrix.map_mul, GlobalTheory.StdPar.yx h hJ hW, Matrix.map_one _ (map_zero _) (map_one _)]
    have e1 : adMat F X * β.1 = (l : AF F ⊗[F] E) • adMat F X := hβ.symm.trans hl
    have hβ' : β.1 = (l : AF F ⊗[F] E) • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) := by
      have e2 := congrArg (adMat F (cT (σ : E →+* E) Y * J) * ·) e1
      simp only [← Matrix.mul_assoc, hL, Matrix.one_mul, Matrix.mul_smul] at e2
      rw [e2]
    have hdet : Matrix.GeneralLinearGroup.det β = l ^ (r + 1) := by
      ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, hβ', Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin,
        Units.val_pow_eq_pow_val]
    rw [← hβt, hdet, map_pow, NNReal.coe_pow]

  have hFD : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨eE⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : SecondCountableTopology (AF F ⊗[F] E) := eE.secondCountableTopology
  haveI : LocallyCompactSpace (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin (r + 1) → Fin m → AF F ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin (r + 1) → Fin m → AF F ⊗[F] E))
  haveI : T2Space (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin (r + 1) → Fin m → AF F ⊗[F] E))
  letI : MeasurableSpace (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) := borel _
  haveI : BorelSpace (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin (r + 1) → Fin (r + 1) → AF F ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin (r + 1) → Fin (r + 1) → AF F ⊗[F] E))
  letI : MeasurableSpace (Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) := borel _
  haveI : BorelSpace (Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) := ⟨rfl⟩
  have hsc : Continuous (sigR (AF F) σ) := by
    have h0 := IsModuleTopology.continuous_of_linearMap (R := AF F) (LinearMap.baseChange (AF F) σ.toLinearMap)
    refine h0.congr fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => simp [LinearMap.baseChange_tmul, sigR]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hcT : ∀ {p q : ℕ}, Continuous fun M : Matrix (Fin p) (Fin q) (AF F ⊗[F] E) => cT (sigR (AF F) σ) M :=
    fun {p q} => (continuous_id.matrix_map hsc).matrix_transpose
  have hSk : IsClosed (skewA σ (r + 1) : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E))) :=
    isClosed_eq (continuous_id.add hcT) continuous_const
  haveI : LocallyCompactSpace (skewA σ (r + 1)) := hSk.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hff := GlobalTheory.SphEis.frame_facts F E σ n J (r + 1) m X Y Z J₀ hF
  haveI : LocallyCompactSpace (unipRad σ J X) := GlobalTheory.UAut.locallyCompact_unipRad h hJ hff.1
  haveI i1 : SecondCountableTopology (skewA σ (r + 1)) :=
    TopologicalSpace.Subtype.secondCountableTopology (skewA σ (r + 1) : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)))
  have i2 : BorelSpace (skewA σ (r + 1)) := inferInstance
  have i3 : T2Space (skewA σ (r + 1)) := inferInstance
  have i4 : SecondCountableTopology (unipRad σ J X) := inferInstance
  have i5 : BorelSpace (unipRad σ J X) := inferInstance
  have i6 : T2Space (unipRad σ J X) := inferInstance

  have cTadd : ∀ {p q : ℕ} (M N : Matrix (Fin p) (Fin q) (AF F ⊗[F] E)),
      cT (sigR (AF F) σ) (M + N) = cT (sigR (AF F) σ) M + cT (sigR (AF F) σ) N := fun M N => Matrix.ext fun i k => by simp [cT]
  have cTsub : ∀ {p q : ℕ} (M N : Matrix (Fin p) (Fin q) (AF F ⊗[F] E)),
      cT (sigR (AF F) σ) (M - N) = cT (sigR (AF F) σ) M - cT (sigR (AF F) σ) N := fun M N => Matrix.ext fun i k => by simp [cT]
  have cTsmul : ∀ {p q : ℕ} (a : AF F ⊗[F] E) (M : Matrix (Fin p) (Fin q) (AF F ⊗[F] E)),
      cT (sigR (AF F) σ) (a • M) = sigR (AF F) σ a • cT (sigR (AF F) σ) M := fun a M => Matrix.ext fun i k => by simp [cT]
  have hJ0 : cT (σ : E →+* E) J₀⁻¹ = J₀⁻¹ := GlobalTheory.SphEis.UnipCrd.cT_inv_herm σ J₀ hF.herm₀
  have hpx : ∀ x y : Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E),
      cT (sigR (AF F) σ) (x * GlobalTheory.SphEis.plus σ J₀ y) = y * GlobalTheory.SphEis.plus σ J₀ x := fun x y => by
    simp only [GlobalTheory.SphEis.plus, GlobalTheory.SphEis.crdLaw_cT_mul, GlobalTheory.SphEis.UnipCrd.cT_cT σ h, GlobalTheory.SphEis.UnipCrd.cT_adMat, hJ0,
      Matrix.mul_assoc]
  set hf2 : AF F ⊗[F] E := inclR (F := F) (AF F) (2⁻¹ : E) with hhf2
  have hh : hf2 + hf2 = 1 := by
    rw [hhf2, ← map_add, ← map_one (inclR (F := F) (AF F))]; congr 1; norm_num
  have hsh : sigR (AF F) σ hf2 = hf2 := by
    rw [hhf2]; simp [sigR, inclR, map_ofNat]
  have hcond : ∀ (x : Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) (s : skewA σ (r + 1)),
      ((s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) - hf2 • (x * GlobalTheory.SphEis.plus σ J₀ x)) +
        cT (sigR (AF F) σ) ((s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) - hf2 • (x * GlobalTheory.SphEis.plus σ J₀ x)) +
        x * GlobalTheory.SphEis.plus σ J₀ x = 0 := fun x s => by
    have hs : (s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) + cT (sigR (AF F) σ) s = 0 := s.2
    rw [cTsub, cTsmul, hsh, hpx]
    rw [show (s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) - hf2 • (x * GlobalTheory.SphEis.plus σ J₀ x) +
        (cT (sigR (AF F) σ) s - hf2 • (x * GlobalTheory.SphEis.plus σ J₀ x)) + x * GlobalTheory.SphEis.plus σ J₀ x =
        ((s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) + cT (sigR (AF F) σ) s) +
          (1 - (hf2 + hf2)) • (x * GlobalTheory.SphEis.plus σ J₀ x) by rw [sub_smul, one_smul, add_smul]; abel, hs, hh, sub_self, zero_smul, add_zero]

  obtain ⟨φ, hφc, hφ⟩ := GlobalTheory.T.exists_continuous_chart_isotropicUnipotentRadical F E σ n J (r + 1) m X Y Z J₀ hF
  have hφmem : ∀ p, φ p ∈ unipRad σ J X := by
    rintro ⟨x, s⟩
    obtain ⟨u, hu, hcu⟩ := GlobalTheory.SphEis.UnipCrd.exists_unipRad_crd F E σ n J (r + 1) m X Y Z J₀ hF x _ (hcond x s)
    have e := (hlaw (φ (x, s)) u x _ 0 0 (hφ x s)).2.1 hcu
    rw [e]
    exact hu
  let βc : GAd σ J → Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) := fun u =>
    adMat F (cT (σ : E →+* E) Y * J) * ((matHom _ σ J u).1 * adMat F Z)
  let κc : GAd σ J → Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E) := fun u =>
    adMat F (cT (σ : E →+* E) Y * J) * ((matHom _ σ J u).1 * adMat F Y)
  have hβc : ∀ u x c, GlobalTheory.SphEis.Crd σ J X Y Z J₀ u x c → βc u = x := fun u x c hu => by
    simp only [βc]
    rw [hu.onZ, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, hF.dz, hF.dc]
    simp
  have hκc : ∀ u x c, GlobalTheory.SphEis.Crd σ J X Y Z J₀ u x c → κc u = c := fun u x c hu => by
    simp only [κc]
    rw [hu.onD]
    simp only [Matrix.mul_add, Matrix.mul_sub, ← Matrix.mul_assoc]
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, hF.dd, hF.dz, hF.dc]
    simp
  have hβcont : Continuous βc := continuous_const.matrix_mul (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const)
  have hκcont : Continuous κc := continuous_const.matrix_mul (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const)
  have hPcont : Continuous fun x : Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) => x * GlobalTheory.SphEis.plus σ J₀ x :=
    continuous_id.matrix_mul (continuous_const.matrix_mul hcT)
  have hinvmem : ∀ u : unipRad σ J X, κc u + hf2 • (βc u * GlobalTheory.SphEis.plus σ J₀ (βc u)) ∈ skewA σ (r + 1) := fun u => by
    obtain ⟨x, c, hc, hcc⟩ := GlobalTheory.SphEis.exists_crd_of_mem_unipRad F E σ n J (r + 1) m X Y Z J₀ hF u u.2
    rw [hβc _ _ _ hc, hκc _ _ _ hc, mem_skewA, cTadd, cTsmul, hsh, hpx]
    rw [show c + hf2 • (x * GlobalTheory.SphEis.plus σ J₀ x) + (cT (sigR (AF F) σ) c + hf2 • (x * GlobalTheory.SphEis.plus σ J₀ x)) =
        (c + cT (sigR (AF F) σ) c + x * GlobalTheory.SphEis.plus σ J₀ x) + ((hf2 + hf2) - 1) • (x * GlobalTheory.SphEis.plus σ J₀ x) by rw [sub_smul, one_smul, add_smul]; abel,
      hcc, hh, sub_self, zero_smul, add_zero]
  have hinvc : Continuous fun u : unipRad σ J X => κc u + hf2 • (βc u * GlobalTheory.SphEis.plus σ J₀ (βc u)) :=
    (hκcont.comp continuous_subtype_val).add ((hPcont.comp (hβcont.comp continuous_subtype_val)).const_smul hf2)
  let Φ : Unit × (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) × skewA σ (r + 1)) ≃ₜ unipRad σ J X :=
    { toFun := fun p => ⟨φ p.2, hφmem p.2⟩
      invFun := fun u => ((), (βc u, ⟨κc u + hf2 • (βc u * GlobalTheory.SphEis.plus σ J₀ (βc u)), hinvmem u⟩))
      left_inv := fun p => by
        obtain ⟨⟨⟩, x, s⟩ := p
        have e1 := hβc _ _ _ (hφ x s)
        have e2 := hκc _ _ _ (hφ x s)
        refine Prod.ext rfl (Prod.ext e1 (Subtype.ext ?_))
        change κc (φ (x, s)) + hf2 • (βc (φ (x, s)) * GlobalTheory.SphEis.plus σ J₀ (βc (φ (x, s)))) = s
        rw [e1, e2, sub_add_cancel]
      right_inv := fun u => by
        obtain ⟨x, c, hc, -⟩ := GlobalTheory.SphEis.exists_crd_of_mem_unipRad F E σ n J (r + 1) m X Y Z J₀ hF u u.2
        apply Subtype.ext
        have h1 := hφ (βc u) ⟨_, hinvmem u⟩
        have e3 : ((⟨_, hinvmem u⟩ : skewA σ (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) -
            inclR (F := F) (AF F) (2⁻¹ : E) • (βc u * GlobalTheory.SphEis.plus σ J₀ (βc u)) = κc u := add_sub_cancel_right _ _
        rw [e3] at h1
        have hu' : GlobalTheory.SphEis.Crd σ J X Y Z J₀ u (βc u) (κc u) := by
          rw [hβc _ _ _ hc, hκc _ _ _ hc]; exact hc
        change φ (βc u, ⟨_, hinvmem u⟩) = u
        exact (hlaw _ u _ _ 0 0 h1).2.1 hu'
      continuous_toFun := Continuous.subtype_mk (hφc.comp continuous_snd) _
      continuous_invFun := continuous_const.prodMk ((hβcont.comp continuous_subtype_val).prodMk
        (hinvc.subtype_mk hinvmem)) }

  have hplusc : Continuous (GlobalTheory.SphEis.plus σ J₀ : Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) → _) :=
    continuous_const.matrix_mul hcT

  have hT : ∀ q' : unipRad σ J X, ∃ (l' : Unit) (f₁ : Unit → Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E))
      (g₁ : Unit × Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) → skewA σ (r + 1)), Continuous f₁ ∧ Continuous g₁ ∧
      ∀ l a c, Φ (l, a, c) * q' = Φ (l * l', a + f₁ l, c + g₁ (l, a)) := by
    intro q'
    obtain ⟨⟨⟨⟩, x', s'⟩, rfl⟩ := Φ.surjective q'
    have hgmem : ∀ a : Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E),
        hf2 • (x' * GlobalTheory.SphEis.plus σ J₀ a - a * GlobalTheory.SphEis.plus σ J₀ x') ∈ skewA σ (r + 1) := fun a => by
      rw [mem_skewA, cTsmul, hsh, cTsub, hpx, hpx, ← smul_add]
      simp
    have hgc : Continuous fun p : Unit × Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) =>
        hf2 • (x' * GlobalTheory.SphEis.plus σ J₀ p.2 - p.2 * GlobalTheory.SphEis.plus σ J₀ x') :=
      ((continuous_const.matrix_mul (hplusc.comp continuous_snd)).sub (continuous_snd.matrix_mul continuous_const)).const_smul hf2
    have hgc' : Continuous fun p : Unit × Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) =>
        (⟨_, hgmem p.2⟩ : skewA σ (r + 1)) := hgc.subtype_mk _
    have hgc'' : Continuous fun p : Unit × Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) =>
        s' + (⟨_, hgmem p.2⟩ : skewA σ (r + 1)) := continuous_const.add hgc'
    refine ⟨(), fun _ => x', fun p => s' + ⟨_, hgmem p.2⟩, continuous_const, hgc'', fun l a c => ?_⟩
    obtain ⟨⟩ := l
    apply Subtype.ext
    change φ (a, c) * φ (x', s') = φ (a + x', c + (s' + ⟨_, hgmem a⟩))
    have h1 := (hlaw _ _ a _ x' _ (hφ a c)).1 (hφ x' s')
    have h2 := hφ (a + x') (c + (s' + ⟨_, hgmem a⟩))
    simp only [← hhf2] at h1 h2
    have hQ : a * GlobalTheory.SphEis.plus σ J₀ x' = hf2 • (a * GlobalTheory.SphEis.plus σ J₀ x') + hf2 • (a * GlobalTheory.SphEis.plus σ J₀ x') := by
      rw [← add_smul, hh, one_smul]
    have hLR : ((c : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) - hf2 • (a * GlobalTheory.SphEis.plus σ J₀ a)) +
        ((s' : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) - hf2 • (x' * GlobalTheory.SphEis.plus σ J₀ x')) - a * GlobalTheory.SphEis.plus σ J₀ x' =
        (((c + (s' + ⟨_, hgmem a⟩) : skewA σ (r + 1))) : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) -
          hf2 • ((a + x') * GlobalTheory.SphEis.plus σ J₀ (a + x')) := by
      rw [show (((c + (s' + ⟨_, hgmem a⟩) : skewA σ (r + 1))) : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) =
      (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) + ((s' : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) +
        hf2 • (x' * GlobalTheory.SphEis.plus σ J₀ a - a * GlobalTheory.SphEis.plus σ J₀ x')) from rfl]
      rw [GlobalTheory.SphEis.crdLaw_plus_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
      conv_lhs => rw [hQ]
      simp only [smul_add, smul_sub]
      abel
    rw [← hLR] at h2
    exact (hlaw _ _ _ _ 0 0 h1).2.1 h2

  have hconjmem : ∀ u ∈ unipRad σ J X, b t * u * (b t)⁻¹ ∈ unipRad σ J X :=
    (GlobalTheory.ResidueEisenstein.frame_levi_facts F E σ n J r X Y h hJ hW).1 (b t) hmem
  let α : unipRad σ J X →* unipRad σ J X :=
    { toFun := fun u => ⟨b t * u * (b t)⁻¹, hconjmem u u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun u v => Subtype.ext (by simp [mul_assoc]) }
  have hαc : Continuous α :=
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _

  let lI : GL (Fin (r + 1)) (AF F ⊗[F] E) :=
    Units.map (Matrix.scalar (Fin (r + 1)) : AF F ⊗[F] E →+* Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)).toMonoidHom l
  have hlI : (lI : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) = (l : AF F ⊗[F] E) • 1 := by
    simp [lI, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hdetlI : Matrix.GeneralLinearGroup.det lI = l ^ (r + 1) := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hlI, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin,
      Units.val_pow_eq_pow_val]
  let sA : Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) →+ Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) :=
    (GlobalTheory.ModuLR.lrCE lI δ).toAddEquiv.toAddMonoidHom
  have hsA : ∀ a, sA a = (l : AF F ⊗[F] E) • (a * δ.1) := fun a => by
    change lI.1 * a * δ.1 = _
    rw [hlI, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
  let u2 : (AF F ⊗[F] E)ˣ := l * Units.map (sigR (AF F) σ).toMonoidHom l
  have hu2 : (u2 : AF F ⊗[F] E) = (l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E) := rfl
  have hsu2 : sigR (AF F) σ (u2 : AF F ⊗[F] E) = u2 := by
    rw [hu2, map_mul, GlobalTheory.SphEis.UnipCrd.sigR_invol σ h, mul_comm]
  have hsu2' : sigR (AF F) σ ((u2⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = (u2⁻¹ : (AF F ⊗[F] E)ˣ) := by
    refine Units.eq_inv_of_mul_eq_one_left ?_
    conv_lhs => rw [← hsu2]
    rw [← map_mul, Units.mul_inv, map_one]
  have hsk : ∀ a : AF F ⊗[F] E, sigR (AF F) σ a = a → ∀ s ∈ skewA σ (r + 1), a • s ∈ skewA σ (r + 1) := fun a ha s hs => by
    rw [mem_skewA, cTsmul, ha, ← smul_add, (mem_skewA.1 hs), smul_zero]
  let Lc : skewA σ (r + 1) ≃ₜ+ skewA σ (r + 1) :=
    { toFun := fun s => ⟨(u2 : AF F ⊗[F] E) • (s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)), hsk _ hsu2 _ s.2⟩
      invFun := fun s => ⟨((u2⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • (s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)),
        hsk _ hsu2' _ s.2⟩
      left_inv := fun s => Subtype.ext (by simp [smul_smul])
      right_inv := fun s => Subtype.ext (by simp [smul_smul])
      map_add' := fun s s' => Subtype.ext (by simp [smul_add])
      continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.const_smul (u2 : AF F ⊗[F] E)) _
      continuous_invFun := Continuous.subtype_mk
        (continuous_subtype_val.const_smul (((u2⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E))) _ }
  let sC : skewA σ (r + 1) →+ skewA σ (r + 1) := Lc.toAddEquiv.toAddMonoidHom
  have hsC : ∀ s, (sC s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) =
      ((l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E)) • (s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) :=
    fun s => rfl
  have hδJ' : ∀ M : Matrix (Fin m) (Fin (r + 1)) (AF F ⊗[F] E),
      δ.1 * (adMat F J₀⁻¹ * (cT (sigR (AF F) σ) δ.1 * M)) = adMat F J₀⁻¹ * M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hδJ]
  have hαΦ : ∀ (l' : Unit) a c, α (Φ (l', a, c)) = Φ (l', sA a, sC c) := by
    intro l' a c
    obtain ⟨⟩ := l'
    apply Subtype.ext
    change b t * φ (a, c) * (b t)⁻¹ = φ (sA a, sC c)
    have h1 := hconj _ _ _ (hφ a c)
    have h2 := hφ (sA a) (sC c)
    simp only [← hhf2] at h1 h2
    have e3 : sA a * GlobalTheory.SphEis.plus σ J₀ (sA a) =
        ((l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E)) • (a * GlobalTheory.SphEis.plus σ J₀ a) := by
      rw [hsA]
      simp only [GlobalTheory.SphEis.plus, cTsmul, GlobalTheory.SphEis.crdLaw_cT_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Matrix.mul_assoc, hδJ']
      rw [mul_comm (sigR (AF F) σ (l : AF F ⊗[F] E))]
    rw [e3, hsC] at h2
    rw [← hsA] at h1
    rw [smul_sub, smul_comm ((l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E)) hf2] at h1
    exact (hlaw _ _ _ _ 0 0 h1).2.1 h2

  set kA : ℝ≥0 := (absE F E l ^ ((r + 1) * m))⁻¹ with hkA
  set kC : ℝ≥0 := (absE F E l ^ ((r + 1) * (r + 1)))⁻¹ with hkC
  have hl0 : absE F E l ≠ 0 := fun h0 => by
    have e := map_mul (absE F E) l l⁻¹
    rw [mul_inv_cancel, map_one, h0, zero_mul] at e
    exact zero_ne_one e.symm
  have hsA' : ∀ ν' : Measure (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)), ν'.IsAddHaarMeasure → ν'.map sA = kA • ν' := by
    intro ν' hν'
    have e := addEquivAddHaarChar_smul_map ν' (GlobalTheory.ModuLR.lrCE lI δ)
    rw [GlobalTheory.T.addHaarChar_leftRight_matrixMul_adeleTensor F E σ h (r + 1) m lI δ, hdetlI, hδdet, one_pow, mul_one, map_pow, ← pow_mul] at e
    change ν'.map (GlobalTheory.ModuLR.lrCE lI δ) = kA • ν'
    conv_rhs => rw [← e]
    rw [smul_smul, hkA, inv_mul_cancel₀ (pow_ne_zero _ hl0), one_smul]
  have hsC' : ∀ ν' : Measure (skewA σ (r + 1)), ν'.IsAddHaarMeasure → ν'.map sC = kC • ν' := by
    intro ν' hν'
    have e := addEquivAddHaarChar_smul_map ν' Lc
    rw [GlobalTheory.T.addHaarChar_skewHermitian_normScale F E σ h (r + 1) l Lc (fun s => rfl)] at e
    change ν'.map Lc = kC • ν'
    conv_rhs => rw [← e]
    rw [smul_smul, hkC, inv_mul_cancel₀ (pow_ne_zero _ hl0), one_smul]
  have hmap := GlobalTheory.ModulusCoord.map_haar_eq_smul_of_coords (unipRad σ J X) Unit
    (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) (skewA σ (r + 1)) Φ hT α sA sC kA kC hαc
    (GlobalTheory.ModuLR.lrCE lI δ).continuous Lc.continuous hαΦ hsA' hsC' ν hν
  have hfm : Measurable fun u : unipRad σ J X => f u := hf.comp measurable_subtype_coe
  have hk : ((kA * kC : ℝ≥0) : ℝ) = Real.exp (-(((n : ℝ) - (r + 1)) * t)) := by
    have hn : (n : ℝ) = m + 2 * (r + 1) := by exact_mod_cast hF.dim.symm
    rw [hkA, hkC, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_pow, pow_mul, pow_mul, habs, hn,
      ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    push_cast
    ring
  calc ∫⁻ u, f (b t * u * (b t)⁻¹) ∂ν = ∫⁻ u, (fun v : unipRad σ J X => f v) (α u) ∂ν := rfl
    _ = ∫⁻ v, f v ∂(ν.map α) := (lintegral_map hfm hαc.measurable).symm
    _ = ∫⁻ v, f v ∂((kA * kC) • ν) := by rw [hmap]
    _ = ((kA * kC : ℝ≥0) : ℝ≥0∞) * ∫⁻ v, f v ∂ν := by rw [lintegral_smul_measure]; rfl
    _ = _ := by rw [← hk, ENNReal.ofReal_coe_nnreal]

end GlobalTheory.ResidueEisenstein.ModConj
