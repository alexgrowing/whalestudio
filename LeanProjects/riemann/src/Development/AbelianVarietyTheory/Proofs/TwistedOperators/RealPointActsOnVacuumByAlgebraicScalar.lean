import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisOSumSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRepSuppSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplittingHeckeCharExistsArchimedeanExponent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.RealScalarAlg

open Matrix
open scoped Kronecker ComplexOrder

open GlobalTheory.Grid (neg sgn ofSgn)

variable {D : D7}

def EIn {m n : Type} (M : Matrix m n ℂ) : Prop := ∀ i j, M i j ∈ algebraicClosure ℚ ℂ

section Entries

variable {ι κ ι' κ' : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem EIn.add {M N : Matrix ι κ ℂ} (hM : EIn M) (hN : EIn N) : EIn (M + N) := fun i j => add_mem (hM i j) (hN i j)

theorem EIn.sub {M N : Matrix ι κ ℂ} (hM : EIn M) (hN : EIn N) : EIn (M - N) := fun i j => sub_mem (hM i j) (hN i j)

theorem EIn.neg {M : Matrix ι κ ℂ} (hM : EIn M) : EIn (-M) := fun i j => neg_mem (hM i j)

theorem EIn.smul {c : ℂ} (hc : c ∈ algebraicClosure ℚ ℂ) {M : Matrix ι κ ℂ} (hM : EIn M) : EIn (c • M) :=
  fun i j => mul_mem hc (hM i j)

theorem EIn.one : EIn (1 : Matrix ι ι ℂ) := fun i j => by
  rw [Matrix.one_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem EIn.mul {M : Matrix ι κ ℂ} {N : Matrix κ ι' ℂ} (hM : EIn M) (hN : EIn N) : EIn (M * N) := fun i j => by
  rw [Matrix.mul_apply]; exact sum_mem fun k _ => mul_mem (hM i k) (hN k j)

theorem EIn.transpose {M : Matrix ι κ ℂ} (hM : EIn M) : EIn Mᵀ := fun i j => hM j i

theorem EIn.kron {M : Matrix ι κ ℂ} {N : Matrix ι' κ' ℂ} (hM : EIn M) (hN : EIn N) :
    EIn (Matrix.kroneckerMap (· * ·) M N) := fun i j => by
  rw [Matrix.kroneckerMap_apply]; exact mul_mem (hM _ _) (hN _ _)

theorem EIn.det {M : Matrix ι ι ℂ} (hM : EIn M) : M.det ∈ algebraicClosure ℚ ℂ := by
  let M' : Matrix ι ι (algebraicClosure ℚ ℂ) := fun i j => ⟨M i j, hM i j⟩
  have e : M = (algebraicClosure ℚ ℂ).val.toRingHom.mapMatrix M' := by ext i j; rfl
  rw [e, ← RingHom.map_det]
  exact (M'.det).2

end Entries

theorem half_mem : (1 / 2 : ℂ) ∈ algebraicClosure ℚ ℂ := div_mem (one_mem _) (ofNat_mem _ 2)

theorem detPlus_mem {m n : ℕ} {sS : Matrix (Fin n) (Fin n) ℂ} {sT : Matrix (Fin m) (Fin m) ℂ}
    {a' : Matrix (Fin n) (Fin n) ℂ} {b : Matrix (Fin m) (Fin m) ℂ} (hS : EIn sS) (hT : EIn sT) (ha : EIn a') (hb : EIn b) :
    GlobalTheory.WeilParts.detPlus sS sT a' b ∈ algebraicClosure ℚ ℂ := by
  unfold GlobalTheory.WeilParts.detPlus
  have k1 : EIn (sT ⊗ₖ sSᵀ) := hT.kron hS.transpose
  have k2 : EIn (b ⊗ₖ a'ᵀ) := hb.kron ha.transpose
  have k3 : EIn ((1 + sT ⊗ₖ sSᵀ) * (b ⊗ₖ a'ᵀ)) := (EIn.one.add k1).mul k2
  have k4 : EIn ((1 / 2 : ℂ) • ((1 + sT ⊗ₖ sSᵀ) * (b ⊗ₖ a'ᵀ))) := k3.smul half_mem
  have k5 : EIn ((1 / 2 : ℂ) • (1 - sT ⊗ₖ sSᵀ)) := (EIn.one.sub k1).smul half_mem
  exact (k4.add k5).det

theorem compAt_mt_mul (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g h : GA D V) :
    compAt θ τ (Formalism.L2.Theta.mt V (g * h)) = compAt θ τ (Formalism.L2.Theta.mt V g) * compAt θ τ (Formalism.L2.Theta.mt V h) := by
  have e : Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
    unfold Formalism.L2.Theta.mt; rw [map_mul, Units.val_mul]
  rw [e]
  exact Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_mt_fin (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g : GA D V) (hg : g ∈ GfC V) :
    compAt θ τ (Formalism.L2.Theta.mt V g) = 1 := by
  have h1 : infHom V g = 1 := hg
  have e : compAt θ τ (Formalism.L2.Theta.mt V g) = (Units.val (infHom V g)).map (θ τ) := rfl
  rw [e, h1, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem eIn_rat {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) :
    EIn (compAt θ τ (Formalism.L2.Theta.mt V γ)) := by
  obtain ⟨x, -, e⟩ := hγ
  have hm : Formalism.L2.Theta.mt V γ = (x : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D) := by
    exact (congrArg Units.val e).symm
  intro i j
  rw [hm]
  show θ τ (infPart D (incA D (x i j))) ∈ _
  have e2 : infPart D (incA D (x i j)) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] (x i j : D.host.E) := by
    simp [infPart, incA, inclR, Algebra.TensorProduct.map_tmul]
  rw [e2, (hθ τ).1, mem_algebraicClosure_iff]
  exact ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (x i j : D.host.E))).algHom (tauE D τ).toRatAlgHom

theorem eIn_real {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) (a : GA D V)
    (h : γ * a ∈ GfC V) : EIn (compAt θ τ (Formalism.L2.Theta.mt V a)) ∧ EIn (compAt θ τ (Formalism.L2.Theta.mt V a⁻¹)) := by
  constructor
  · have e : a = γ⁻¹ * (γ * a) := by group
    rw [e, compAt_mt_mul, compAt_mt_fin θ τ V _ h, Matrix.mul_one]
    exact eIn_rat hθ τ V _ (inv_mem hγ)
  · have e : a⁻¹ = (γ * a)⁻¹ * γ := by group
    rw [e, compAt_mt_mul, compAt_mt_fin θ τ V _ (inv_mem h), Matrix.one_mul]
    exact eIn_rat hθ τ V _ hγ

theorem exists_root_alg {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (hV : ∀ τ, (gramAt D V τ).det ≠ 0)
    (g : GA D V) (hg : g ∈ GinfC V) (hA : ∀ τ, (compAt θ τ (Formalism.L2.Theta.mt V g)).det ∈ algebraicClosure ℚ ℂ) :
    ∃ x, IsDetRoot V g x ∧ ∀ ν : (AE D)ˣ →* Circle, (∀ τ, ∃ a, HasInfExp D ν τ a) →
      ((ν x : Circle) : ℂ) ∈ algebraicClosure ℚ ℂ := by
  classical
  have hu : ∀ τ, ‖(compAt θ τ (Formalism.L2.Theta.mt V g)).det‖ = 1 := fun τ => by
    have h : (compAt θ τ (Formalism.L2.Theta.mt V g))ᴴ * gramAt D V τ * compAt θ τ (Formalism.L2.Theta.mt V g) = gramAt D V τ :=
      GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
    have h2 := congrArg (fun M => ‖Matrix.det M‖) h
    simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star] at h2
    have h3 : ‖(gramAt D V τ).det‖ ≠ 0 := norm_ne_zero_iff.2 (hV τ)
    have h4 : ‖(compAt θ τ (Formalism.L2.Theta.mt V g)).det‖ ^ 2 = 1 := by
      apply mul_left_cancel₀ h3; linear_combination h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4
  have hw : ∀ τ, ∃ w : ℂ, w ^ 2 = (compAt θ τ (Formalism.L2.Theta.mt V g)).det ∧ ‖w‖ = 1 := fun τ => by
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (compAt θ τ (Formalism.L2.Theta.mt V g)).det two_pos
    refine ⟨w, hw, (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 ?_⟩
    rw [← norm_pow, hw, hu]
  choose w hw1 hw2 using hw
  have hw0 : ∀ τ, w τ ≠ 0 := fun τ h => by simpa [h] using hw2 τ
  have hwA : ∀ τ, w τ ∈ algebraicClosure ℚ ℂ := fun τ => by
    have := hA τ
    rw [← hw1, mem_algebraicClosure_iff] at this
    exact mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow two_pos this)
  choose x hx1 hx2 using fun τ => GlobalTheory.VacuumCharacter.exists_idele_at hθ τ (w τ) (hw0 τ)
  have hf : finPart D ((∏ τ, x τ : (AE D)ˣ) : AE D) = 1 := by
    rw [Units.coe_prod, map_prod]; exact Finset.prod_eq_one fun τ _ => hx1 τ
  have hi : ∀ τ, θ τ (infPart D ((∏ τ, x τ : (AE D)ˣ) : AE D)) = w τ := fun τ => by
    rw [Units.coe_prod, map_prod, map_prod]
    simp [hx2]
  refine ⟨∏ τ, x τ, ?_, fun ν hc => ?_⟩
  · refine GlobalTheory.VacuumCharacter.adele_ext hθ ?_ fun τ => ?_
    · have hd : finPart D (Formalism.L2.Theta.mt V g).det = 1 := by
        have hg' : finHom V g = 1 := hg
        have : (Formalism.L2.Theta.mt V g).map (finPart D) = 1 := congrArg Units.val hg'
        rw [RingHom.map_det]
        exact (congrArg Matrix.det this).trans Matrix.det_one
      rw [map_mul, hf]
      exact ((congrArg₂ (· * ·) hd (GlobalTheory.VacuumCharacter.finPart_cA _ hf)).trans (one_mul 1)).symm
    · rw [map_mul, map_mul, hi]
      have e1 := GlobalTheory.FockCompare.comp_cA hθ τ ((∏ τ, x τ : (AE D)ˣ) : AE D)
      have e2 := GlobalTheory.VacuumCharacter.det_compAt θ τ (Formalism.L2.Theta.mt V g)
      rw [hi] at e1
      refine Eq.trans ?_ (congrArg₂ (· * ·) e2 e1.symm)
      have : w τ * starRingEnd ℂ (w τ) = 1 := by rw [Complex.mul_conj', hw2]; simp
      rw [← hw1]; linear_combination (-w τ) * this
  · rw [map_prod]
    rw [show ((∏ τ, ν (x τ) : Circle) : ℂ) = ∏ τ, (ν (x τ) : ℂ) from map_prod Circle.coeHom _ _]
    refine prod_mem fun τ _ => ?_
    obtain ⟨a, n, -, -, h⟩ := hc τ
    rw [h θ hθ (x τ) (hx1 τ) (fun τ' h' => by rw [hx2, if_neg h']), hx2, if_pos rfl, hw2]
    simp only [Complex.ofReal_one, div_one]
    exact zpow_mem (hwA τ) n

theorem realScalar : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW},
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ C : ℂ, IsAlgebraic ℚ C ∧ X.ω t (a, a') X.vac = C • X.vac := by
  intro D T L sc G W i j A A' WW X hX t γ hγ a ha γ' hγ' a' ha' hγa hγa'
  classical
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hψ : IsStdChar D W.ψ (-1) := hI.isVac.1
  set om' := (X.ω t).toSgn true with hom'
  have hom := hI.weil t
  have hsA : ∀ τ, X.rA.s τ = 1 := fun τ => (hX.std.2.2 τ).1
  have hsW : ∀ τ, X.rW.s τ = 1 := fun τ => (hX.stdW.2.2 τ).1
  set g : GA D (neg A) := (ofSgn true A).symm a with hgdef
  have hga : ofSgn true A g = a := MulEquiv.apply_symm_apply _ _
  have hg : g ∈ GinfC (neg A) := (GlobalTheory.SgnIdent.mem_GinfC_sgn true A g).2 (by rw [hga]; exact ha)
  have cS : ∀ τ, IsCartanInv (gramAt D (neg A) τ) (-X.rA.s τ) := fun τ => GlobalTheory.Grid.isCartanInv_sgn true A τ (hI.rigA.2.2 τ).1
  have cT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hI.rigW.2.2 τ).1
  have hdet : ∀ τ, (gramAt D (neg A) τ).det ≠ 0 := fun τ h0 => by
    have := (cS τ).2.2.det_pos.ne'
    rw [Matrix.det_mul, h0, zero_mul] at this
    exact this rfl
  have hdetW : ∀ τ, (gramAt D WW τ).det ≠ 0 := fun τ h0 => by
    have := (cT τ).2.2.det_pos.ne'
    rw [Matrix.det_mul, h0, zero_mul] at this
    exact this rfl
  have mg : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt (neg A) g) = compAt W.θ τ (Formalism.L2.Theta.mt A a) := fun τ => by
    have e := GlobalTheory.Grid.mt_ofSgn true A g
    rw [hga] at e
    rw [e]
  have mgi : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt (neg A) g⁻¹) = compAt W.θ τ (Formalism.L2.Theta.mt A a⁻¹) := fun τ => by
    have e := GlobalTheory.Grid.mt_ofSgn true A g⁻¹
    rw [map_inv, hga] at e
    rw [e]
  have eA := fun τ => eIn_real hθ τ A γ hγ a hγa
  have eW := fun τ => eIn_real hθ τ WW γ' hγ' a' hγa'
  obtain ⟨x, hx, hxν⟩ := exists_root_alg hθ (neg A) hdet g hg fun τ => by rw [mg]; exact (eA τ).1.det
  obtain ⟨y, hy, hyν⟩ := exists_root_alg hθ WW hdetW a' ha' fun τ => (eW τ).1.det
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have hC := GlobalTheory.WeilVacChar.vacuum_character D W.ψ hψ (neg A) WW W.θ hθ _ _ om' η hη hom (fun τ => -X.rA.s τ) X.rW.s cS cT
    g hg a' ha' (fun τ => by rw [hsA]; simp) (fun τ => by rw [hsW]; simp) x y hx hy X.vac hI.isVac.2.theta hI.isVac.2.fock
  have hexp : ∀ (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → ResEta D χ n → ∀ k : ℕ,
      ∀ τ, ∃ b, HasInfExp D (χ * (η ^ k)⁻¹) τ b := fun χ n h1 h2 k τ => by
    obtain ⟨b, hb⟩ := GlobalTheory.SplitCharExp.exists_hasInfExp D W.θ χ n τ hθ h1 h2
    exact ⟨_, GlobalTheory.VacuumCharacter.hasInfExp_twist hb (hη.2.2.2 τ) k⟩
  have key : X.ω t (a, a') X.vac = om' (g, a') X.vac := by
    show _ = X.ω t (ofSgn true A g, a') X.vac
    rw [hga]
  rw [key, hC]
  refine ⟨_, ?_, rfl⟩
  · rw [← mem_algebraicClosure_iff, Circle.coe_mul, Circle.coe_inv]
    refine mul_mem (mul_mem (inv_mem (hxν _ (hexp _ _ hom.hecT hom.resT _))) (hyν _ (hexp _ _ hom.hecS hom.resS _)))
      (prod_mem fun τ _ => ?_)
    rw [mgi]
    have hs1 : EIn (-X.rA.s τ) := by rw [hsA]; exact EIn.one.neg
    have hs2 : EIn (X.rW.s τ) := by rw [hsW]; exact EIn.one
    exact detPlus_mem hs1 hs2 (eA τ).2 (eW τ).1

end GlobalTheory.RealScalarAlg

end
