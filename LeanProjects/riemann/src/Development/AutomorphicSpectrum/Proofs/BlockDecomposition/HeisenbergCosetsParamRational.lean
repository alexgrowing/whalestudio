import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainFourierUnfolding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellCosetsHermitianParam
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCellInvariantUnipotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinConvergent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelParabolicQuotientIffRowsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryCellBlockNormalFormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryBlockInvertibleCriterionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicFactorizationRowsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowsProportionalOfTransformStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowsOfWeylHeisenbergProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylHeisenbergLeviRationalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCentreRationalFormStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf.CellGlue

section Field

variable {K : Type} [Field K] {n ρ p : ℕ}

theorem zinc_eq_comp (hn : ρ + p = n) (v : Fin ρ → K) :
    zinc hn v = Sum.elim v (fun _ : Fin p => (0 : K)) ∘ (finSumFinEquiv.trans (finCongr hn)).symm := rfl

theorem bl_mulVec_zinc (hn : ρ + p = n) (X : Matrix (Fin ρ) (Fin p) K) (c : Matrix (Fin p) (Fin p) K) (v : Fin ρ → K) :
    (bl hn (-1) X 0 c).mulVec (zinc hn v) = - zinc hn v := by
  rw [zinc_eq_comp]
  unfold bl
  rw [Matrix.submatrix_mulVec_equiv]
  funext i
  simp only [Function.comp_apply, Pi.neg_apply, Equiv.symm_symm]
  generalize (finSumFinEquiv.trans (finCongr hn)).symm i = j
  have e : (Sum.elim v (fun _ : Fin p => (0 : K)) ∘ ⇑(finSumFinEquiv.trans (finCongr hn)).symm) ∘
      ⇑(finSumFinEquiv.trans (finCongr hn)) = Sum.elim v (fun _ : Fin p => (0 : K)) := by
    funext t
    simp
  rw [e, Matrix.fromBlocks_mulVec]
  rcases j with j | j
  · simp [Function.comp_def, Matrix.neg_mulVec]
    exact congrFun (Matrix.mulVec_zero X) j
  · simp [Function.comp_def]
    exact congrFun (Matrix.mulVec_zero c) j

theorem zinc_eq_zero (hn : ρ + p = n) {v : Fin ρ → K} (h : zinc hn v = 0) : v = 0 := by
  funext j
  have := congrFun h (finSumFinEquiv.trans (finCongr hn) (Sum.inl j))
  rw [zinc_eq_comp] at this
  simpa using this

theorem ker_rows_eq_bot (hn : ρ + p = n) {T : Matrix (Fin n) (Fin n) K} (hT : IsUnit T.det)
    (η : Matrix (Fin ρ) (Fin p) K) (a c : Matrix (Fin p) (Fin p) K) :
    LinearMap.ker ((T * rowC hn η a c).mulVecLin ∘ₗ zinc hn) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  have h0 : (T * rowC hn η a c).mulVec (zinc hn v) = 0 := hv
  rw [← Matrix.mulVec_mulVec] at h0
  have h1 : (rowC hn η a c).mulVec (zinc hn v) = 0 := by
    have := congrArg (T⁻¹).mulVec h0
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hT, Matrix.one_mulVec, Matrix.mulVec_zero] at this
  have h2 : (rowC hn η a c).mulVec (zinc hn v) = - zinc hn v := bl_mulVec_zinc hn _ _ _
  rw [h2, neg_eq_zero] at h1
  exact zinc_eq_zero hn h1

theorem exists_unit_lowerC {x r : Matrix (Fin (n + n)) (Fin (n + n)) K} (hx : IsUnit x.det) (hr : IsUnit r.det)
    (hS : IsSiegelP (x * r⁻¹)) : ∃ T : Matrix (Fin n) (Fin n) K, IsUnit T.det ∧ lowerC x = T * lowerC r := by
  set S := x * r⁻¹ with hSd
  have hSr : S * r = x := by rw [hSd, mul_assoc, Matrix.nonsing_inv_mul _ hr, mul_one]
  have hdet : IsUnit S.det := by
    rw [hSd, Matrix.det_mul]
    exact hx.mul (Matrix.isUnit_nonsing_inv_det _ hr)
  have hd : IsUnit (GlobalTheory.CompanionTheory.RatPtsUnn.blkD S).det := by
    rw [GlobalTheory.CompanionTheory.RatPtsUnn.det_eq_of_lowerLeft_zero S hS] at hdet
    exact isUnit_of_mul_isUnit_right hdet
  refine ⟨_, hd, ?_⟩
  rw [← hSr]
  exact GlobalTheory.CompanionTheory.SwUnf.lowerC_siegel_mul hS r

theorem isUnitary_mul_inv (σ : K →+* K) {m : ℕ} {J y z : Matrix (Fin m) (Fin m) K} (hz : IsUnit z.det)
    (hy : IsUnitary σ J y) (h2 : IsUnitary σ J z) : IsUnitary σ J (y * z⁻¹) := by
  have hy' : cT σ y * J * y = J := hy
  have hz' : cT σ z * J * z = J := h2
  change cT σ (y * z⁻¹) * J * (y * z⁻¹) = J
  have e1 : cT σ z⁻¹ * cT σ z = 1 := by
    rw [← GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_mul_sq, Matrix.mul_nonsing_inv _ hz, GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_one_sq]
  have e2 : z * z⁻¹ = 1 := Matrix.mul_nonsing_inv _ hz
  rw [GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_mul_sq]
  calc cT σ z⁻¹ * cT σ y * J * (y * z⁻¹) = cT σ z⁻¹ * (cT σ y * J * y) * z⁻¹ := by simp only [mul_assoc]
    _ = cT σ z⁻¹ * (cT σ z * J * z) * z⁻¹ := by rw [hy', hz']
    _ = (cT σ z⁻¹ * cT σ z) * J * (z * z⁻¹) := by simp only [mul_assoc]
    _ = J := by rw [e1, e2, one_mul, mul_one]

end Field

open GlobalTheory.CompanionTheory.EisCellsAsm in

theorem cell : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (M : Maps D hn),
    ∃ e : ratHerm D ρ × (Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E) → Cosets (P D n) (GF D n),
      Function.Injective e ∧
      (∀ q, zKer hn (ratOf q.out) = ⊥ ↔ q ∈ Set.range e) ∧
      (∀ (l l' : ratHerm D ρ) u (h : M.nzx l'.1 0 ∈ GF D n),
        rmulEquiv (P D n) (GF D n) ⟨M.nzx l'.1 0, h⟩ (e (l, u)) = e (l' + l, u)) ∧
      ∀ f : G D n → ℂ, LeftInv (P D n ⊓ GF D n) f → ∀ (l : ratHerm D ρ) u (y : G D n),
        term (P D n) (GF D n) f y (e (l, u)) =
          f (M.w * M.nzx l.1 0 * M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * y) := by
  intro D n ρ p hn M
  have hσ : ∀ x, sg D (sg D x) = x := sg_sg D
  obtain ⟨hadd, hsh, hemb, hc⟩ := GlobalTheory.T.heisenberg_centre_rational_form M
  choose hnm ζ hζ hζm using hc
  choose a b hab using fun q : Cosets (P D p) (GF D p) =>
    GlobalTheory.CompanionTheory.SwUnf.BigCell.exists_blockMatrixTwoByTwoFin_eq (ratOf (Quotient.out q))
  let cc : Cosets (P D p) (GF D p) → Matrix (Fin p) (Fin p) D.host.E := fun q => lowerC (ratOf (Quotient.out q))
  let dd : Cosets (P D p) (GF D p) → Matrix (Fin p) (Fin p) D.host.E :=
    fun q => GlobalTheory.CompanionTheory.RatPtsUnn.blkD (ratOf (Quotient.out q))
  have hab' : ∀ q, ratOf (Quotient.out q) = blk4 (a q) (b q) (cc q) (dd q) := hab
  have hmat : ∀ q, mat ((Quotient.out q : GF D p) : G D p) = (blk4 (a q) (b q) (cc q) (dd q)).map (incA D) := fun q => by
    rw [← hab']
    exact mat_ratOf _
  have hI := fun (l : ratHerm D ρ) (u : Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E) =>
    GlobalTheory.T.weyl_heisenberg_levi_rational hn M l.1 (ζ l) (hζ l) u.2 (Quotient.out u.1) (a u.1) (b u.1) (cc u.1) (dd u.1) (hmat u.1)
  let R : ratHerm D ρ → Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E →
      Matrix (Fin (n + n)) (Fin (n + n)) D.host.E :=
    fun l u => wM hn * nM hn (ζ l) * sM hn (sg D) u.2 * eM hn (a u.1) (b u.1) (cc u.1) (dd u.1)
  let c : ratHerm D ρ → Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E → GF D n :=
    fun l u => ⟨M.w * M.nzx l.1 0 * M.sh (u.2.map (incA D)) * M.emb (Quotient.out u.1 : GF D p), (hI l u).1⟩
  have hcm : ∀ l u, mat (c l u : G D n) = (R l u).map (incA D) := fun l u => (hI l u).2
  have hRs : ∀ l u, IsUnit (R l u).det ∧ IsUnitary (sg D) (blk4 0 1 (-1) 0) (R l u) := fun l u => by
    have e : ratOf (c l u) = R l u := Matrix.map_injective incA_injective ((mat_ratOf _).symm.trans (hcm l u))
    rw [← e]
    exact GlobalTheory.CompanionTheory.SwUnf.BigCell.ratOf_spec _
  have hRC : ∀ l u, lowerC (R l u) = rowC hn u.2 (a u.1) (cc u.1) := fun l u =>
    (GlobalTheory.T.rows_of_weyl_heisenberg_product (sg D) hσ hn _ _ _ _ _ _).1
  have hRD : ∀ l u, GlobalTheory.CompanionTheory.RatPtsUnn.blkD (R l u) = rowD hn (sg D) (ζ l) u.2 (b u.1) (dd u.1) := fun l u =>
    (GlobalTheory.T.rows_of_weyl_heisenberg_product (sg D) hσ hn _ _ _ _ _ _).2
  refine ⟨fun x => mk ((P D n).subgroupOf (GF D n)) (c x.1 x.2), ?_, ?_, ?_, ?_⟩
  · rintro ⟨l₁, q₁, η₁⟩ ⟨l₂, q₂, η₂⟩ h
    have hS := (mk_eq_iff_siegel GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn (c l₁ (q₁, η₁)) (c l₂ (q₂, η₂)) (hRs l₁ _).1
      (hcm l₁ _) (hcm l₂ _)).1 h
    obtain ⟨T, hT1, hT2⟩ := (GlobalTheory.T.siegel_parabolic_quotient_iff_rows (sg D) hσ (R l₂ (q₂, η₂)) (R l₁ (q₁, η₁)) (hRs l₁ _).1 (hRs l₂ _).2
      (hRs l₁ _).2).1 hS
    rw [hRC, hRC] at hT1
    rw [hRD, hRD] at hT2
    obtain ⟨⟨T', h1, h2⟩, h3⟩ := GlobalTheory.T.rows_proportional_of_transform (sg D) hσ hn (a q₁) (b q₁) (cc q₁) (dd q₁) (a q₂) (b q₂) (cc q₂) (dd q₂)
      (ζ l₁) (ζ l₂) η₁ η₂ T hT1 hT2
    have hq : q₁ = q₂ := by
      have hs1 := GlobalTheory.CompanionTheory.SwUnf.BigCell.ratOf_spec (Quotient.out q₁)
      have hs2 := GlobalTheory.CompanionTheory.SwUnf.BigCell.ratOf_spec (Quotient.out q₂)
      have hSp := (GlobalTheory.T.siegel_parabolic_quotient_iff_rows (sg D) hσ (ratOf (Quotient.out q₂)) (ratOf (Quotient.out q₁)) hs1.1 hs2.2 hs1.2).2
        ⟨T', h1, h2⟩
      have := (mk_eq_iff_siegel GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn (Quotient.out q₁) (Quotient.out q₂) hs1.1
        (mat_ratOf _) (mat_ratOf _)).2 hSp
      exact (Quotient.out_eq q₁).symm.trans (this.trans (Quotient.out_eq q₂))
    subst hq
    have hU : IsUnit (blk4 (a q₁) (b q₁) (cc q₁) (dd q₁)).det := by
      rw [← hab']
      exact (GlobalTheory.CompanionTheory.SwUnf.BigCell.ratOf_spec _).1
    obtain ⟨e1, e2⟩ := h3 hU rfl rfl rfl rfl
    have hl : l₁ = l₂ := Subtype.ext (Subtype.ext (by rw [← hζ l₁, ← hζ l₂, e1]))
    rw [hl, e2]
  · intro q
    have hspec := GlobalTheory.CompanionTheory.SwUnf.BigCell.ratOf_spec (Quotient.out q)
    constructor
    · intro hz
      have hker : LinearMap.ker ((lowerC (ratOf (Quotient.out q))).mulVecLin ∘ₗ zinc hn) = ⊥ := by
        rw [LinearMap.ker_comp]
        exact hz
      obtain ⟨T₀, a₁, b₁, Z, a₂, b₂, X, Y, a₃, b₃, W, a₄, b₄, c', d', hU, hD, hL1, hL2⟩ :=
        GlobalTheory.T.unitary_cell_block_normal_form (sg D) hσ hn _ hspec.1 hspec.2 hker
      obtain ⟨ζ₀, η₀, T, hyD, hyU, hζ₀, hr1, hr2⟩ :=
        GlobalTheory.T.unitary_block_invertible_criterion (sg D) hσ hn a₁ b₁ Z a₂ b₂ X Y a₃ b₃ W a₄ b₄ c' d' hU hD
      generalize a₄ + a₃ * X = a' at hyD hyU hr1
      generalize b₄ + a₃ * Y = b' at hyD hyU hr2
      obtain ⟨γ, hγ, hγm⟩ := GlobalTheory.CompanionTheory.RatPtsUnn.clause2 _ hyD hyU
      let q' : Cosets (P D p) (GF D p) := mk ((P D p).subgroupOf (GF D p)) ⟨γ, hγ⟩
      have hs2 := GlobalTheory.CompanionTheory.SwUnf.BigCell.ratOf_spec (Quotient.out q')
      have hSy : IsSiegelP (blk4 a' b' c' d' * (ratOf (Quotient.out q'))⁻¹) :=
        (mk_eq_iff_siegel GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn (Quotient.out q') ⟨γ, hγ⟩ hs2.1 (mat_ratOf _) hγm).1
          (Quotient.out_eq q')
      have hsU := isUnitary_mul_inv (sg D) hs2.1 hyU hs2.2
      obtain ⟨A, B, hsb⟩ := GlobalTheory.CompanionTheory.SwUnf.BigCell.exists_blockMatrixTwoByTwoFin_eq (blk4 a' b' c' d' * (ratOf (Quotient.out q'))⁻¹)
      rw [(GlobalTheory.CompanionTheory.SwUnf.BigCell.isSiegelParabolic_iff _).1 hSy] at hsb
      generalize GlobalTheory.CompanionTheory.RatPtsUnn.blkD (blk4 a' b' c' d' * (ratOf (Quotient.out q'))⁻¹) = Dd at hsb
      rw [hsb] at hsU
      have hy : blk4 a' b' c' d' = blk4 A B 0 Dd * blk4 (a q') (b q') (cc q') (dd q') := by
        rw [← hsb, ← hab', mul_assoc, Matrix.nonsing_inv_mul _ hs2.1, mul_one]
      obtain ⟨ζ₂, η₂, T₂, hζ₂, hC, hDd⟩ := GlobalTheory.T.parabolic_factorization_rows (sg D) hσ hn a' b' c' d' (a q') (b q') (cc q') (dd q') A B Dd
        hsU hy ζ₀ η₀ hζ₀
      let bq : HermQ D ρ := ⟨ζ₂, fun i j => congrFun (congrFun hζ₂ i) j⟩
      let l₂ : ratHerm D ρ := ⟨⟨ζ₂.map (incA D), adj_map_herm bq⟩, ⟨ζ₂, rfl⟩⟩
      have hl : ζ l₂ = ζ₂ := Matrix.map_injective incA_injective (hζ l₂)
      refine ⟨(l₂, (q', η₂)), ?_⟩
      have hsp : IsSiegelP (ratOf (Quotient.out q) * (R l₂ (q', η₂))⁻¹) :=
        (GlobalTheory.T.siegel_parabolic_quotient_iff_rows (sg D) hσ _ _ (hRs l₂ _).1 hspec.2 (hRs l₂ _).2).2 ⟨T₀ * T * T₂, by
          rw [hRC, hL1, hr1, hC]
          simp only [mul_assoc], by
          rw [hRD, hL2, hr2, hDd, hl]
          simp only [mul_assoc]⟩
      exact ((mk_eq_iff_siegel GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn (c l₂ (q', η₂)) (Quotient.out q) (hRs l₂ _).1 (hcm l₂ _)
        (mat_ratOf _)).2 hsp).trans (Quotient.out_eq q)
    · rintro ⟨⟨l, u⟩, rfl⟩
      have hspec' := GlobalTheory.CompanionTheory.SwUnf.BigCell.ratOf_spec (Quotient.out (mk ((P D n).subgroupOf (GF D n)) (c l u)))
      have hS := (mk_eq_iff_siegel GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn (c l u) (Quotient.out (mk ((P D n).subgroupOf (GF D n)) (c l u)))
        (hRs l u).1 (hcm l u) (mat_ratOf _)).1 (Quotient.out_eq _).symm
      obtain ⟨T, hT, hTC⟩ := exists_unit_lowerC hspec'.1 (hRs l u).1 hS
      rw [hRC] at hTC
      have h := ker_rows_eq_bot hn hT u.2 (a u.1) (cc u.1)
      rw [← hTC, LinearMap.ker_comp] at h
      exact h
  · intro l l' u h
    change rmulEquiv (P D n) (GF D n) ⟨M.nzx l'.1 0, h⟩ (mk ((P D n).subgroupOf (GF D n)) (c l u)) =
      mk ((P D n).subgroupOf (GF D n)) (c (l' + l) u)
    have e : c (l' + l) u = c l u * ⟨M.nzx l'.1 0, h⟩ := by
      apply Subtype.ext
      change M.w * M.nzx (l' + l).1 0 * M.sh (u.2.map (incA D)) * M.emb (Quotient.out u.1 : GF D p) =
        M.w * M.nzx l.1 0 * M.sh (u.2.map (incA D)) * M.emb (Quotient.out u.1 : GF D p) * M.nzx l'.1 0
      have e1 : ((l' + l : ratHerm D ρ) : hermA D ρ) = l.1 + l'.1 := Subtype.ext (add_comm l'.1.1 l.1.1)
      have h1 := hemb l'.1 (Quotient.out u.1 : GF D p).1
      have h2 := hsh l'.1 (u.2.map (incA D))
      rw [e1, hadd]
      calc M.w * (M.nzx l.1 0 * M.nzx l'.1 0) * M.sh (u.2.map (incA D)) * M.emb (Quotient.out u.1 : GF D p)
          = M.w * M.nzx l.1 0 * (M.nzx l'.1 0 * M.sh (u.2.map (incA D))) * M.emb (Quotient.out u.1 : GF D p) := by
            simp only [mul_assoc]
        _ = M.w * M.nzx l.1 0 * M.sh (u.2.map (incA D)) * (M.nzx l'.1 0 * M.emb (Quotient.out u.1 : GF D p)) := by
            rw [h2]
            simp only [mul_assoc]
        _ = _ := by
            rw [h1]
            simp only [mul_assoc]
    rw [e]
    exact rmul_mk _ _
  · intro f hf l u y
    exact term_mk hf y (c l u)

end GlobalTheory.CompanionTheory.ZUnf.CellGlue
