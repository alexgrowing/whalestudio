import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeNegTransposeGram
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefClassDecompIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SmulMemOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainDataPrincipalCongruenceLevel
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp

theorem fdgram_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = (xᴴ * (G.map τ)ᵀ * x)ᵀ := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.transpose_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp [RCLike.star_def]
  ring

theorem permM_conj {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ} (e : ι ≃ Fin r) (M : Matrix ι ι ℂ) :
    (permM e)ᴴ * M * permM e = M.submatrix e.symm e.symm := by
  ext a b
  rw [Matrix.mul_apply, ← e.symm.sum_comp]
  simp [permM, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [← e.symm.sum_comp]
  simp

theorem jpq_eq_diagonal (p q : ℕ) :
    Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ : Fin p => (1 : ℂ)) (fun _ : Fin q => -1)) := by
  rw [Formalism.UG.Jpq, ← Matrix.fromBlocks_diagonal, Matrix.diagonal_one, ← Matrix.diagonal_neg]
  rfl

theorem sumElim_sgn {p q r : ℕ} (hcard : r = q + p) (a : Fin r) :
    Sum.elim (fun _ : Fin p => (1 : ℂ)) (fun _ : Fin q => -1)
        (((finCongr hcard).trans (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin q) (Fin p)))) a) =
      -(((sgn q (a : ℕ) : ℝ)) : ℂ) := by
  by_cases h : (a : ℕ) < q
  · have ha : finCongr hcard a = Fin.castAdd p ⟨a, h⟩ := Fin.ext rfl
    have hv : ((finCongr hcard).trans (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin q) (Fin p)))) a =
        Sum.inr ⟨a, h⟩ := by
      rw [Equiv.trans_apply, Equiv.trans_apply, ha, finSumFinEquiv_symm_apply_castAdd]
      rfl
    rw [hv]
    simp [sgn, h]
  · have hlt := a.isLt
    have ha : finCongr hcard a = Fin.natAdd q ⟨(a : ℕ) - q, by omega⟩ := Fin.ext (by simp; omega)
    have hv : ((finCongr hcard).trans (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin q) (Fin p)))) a =
        Sum.inl ⟨(a : ℕ) - q, by omega⟩ := by
      rw [Equiv.trans_apply, Equiv.trans_apply, ha, finSumFinEquiv_symm_apply_natAdd]
      rfl
    rw [hv]
    simp [sgn, h]

theorem exists_frame_of_sig {n p q : ℕ} {Gc : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature Gc p q)
    {A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ} (hA : Aᴴ * Formalism.UG.Jpq p q * A = Gc) :
    ∃ (e : Fin p ⊕ Fin q ≃ Fin n) (x : Matrix (Fin n) (Fin n) ℂ), x.det ≠ 0 ∧ A * x = permM e ∧
      (-(xᴴ * Gc * x))ᵀ = Matrix.diagonal fun a : Fin n => ((sgn q (a : ℕ) : ℝ) : ℂ) := by
  obtain ⟨L, hl, hr⟩ := GlobalTheory.DecompCompare.frame_inv h hA
  obtain ⟨e0, -⟩ := h
  have hcard : n = q + p := by
    have h2 := Fintype.card_congr e0
    simp only [Fintype.card_fin, Fintype.card_sum] at h2
    omega
  set π : Fin n ≃ Fin p ⊕ Fin q :=
    (finCongr hcard).trans (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin q) (Fin p))) with hπ
  have hAx : A * (L * permM π.symm) = permM π.symm := by rw [← Matrix.mul_assoc, hr, Matrix.one_mul]
  refine ⟨π.symm, L * permM π.symm, ?_, hAx, ?_⟩
  · have h1 : (L * permM π.symm) * ((permM π.symm)ᵀ * A) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (permM π.symm), permM_mul_transpose, Matrix.one_mul, hl]
    intro h0
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h2
    exact zero_ne_one h2
  · have key : ∀ y : Matrix (Fin n) (Fin n) ℂ, yᴴ * Gc * y = (A * y)ᴴ * Formalism.UG.Jpq p q * (A * y) := fun y => by
      rw [← hA, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [key, hAx, permM_conj, Equiv.symm_symm, jpq_eq_diagonal, Matrix.submatrix_diagonal_equiv,
      Matrix.diagonal_neg, Matrix.diagonal_transpose]
    congr 1
    funext a
    rw [Function.comp_apply, hπ, sumElim_sgn hcard a, neg_neg]

end GlobalTheory.CovTop.VolUp

namespace GlobalTheory.CovTop.VolUp

theorem exists_ident_frame : ∀ (D : D7) (V : HSp D) (P Q : ℕ), V.SigOK → (∀ τ, V.sig τ = (P, Q)) →
    ∀ A : Frames V, IsFrames V A → ∃ (X₀ : Data D.host.E V.rank) (σ : D.what₂.Tau ≃ X₀.Ψ) (x : Frame X₀.Ψ V.rank)
      (e : ∀ ρ : D.what₂.Tau, Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2 ≃ Fin V.rank),
      X₀.Gm = -(V.gram)ᵀ ∧ (∀ ρ, (σ ρ).1 = tauE D ρ) ∧ IsOrth X₀ x ∧
        IsIdent (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) X₀.Ψ X₀.Gm x σ A e := by
  intro D V P Q hV hs A hA
  choose e x hdet hAx hg using fun ρ => exists_frame_of_sig (hV (tauE D ρ)) (hA ρ)
  have hrk : V.rank = Q + P := by
    have h := hV D.host.φ₀
    rw [hs] at h
    obtain ⟨e0, -⟩ := h
    have h2 := Fintype.card_congr e0
    simp only [Fintype.card_fin, Fintype.card_sum] at h2
    omega
  have hmapT : ∀ ρ, ((-(V.gram)ᵀ).map (tauE D ρ))ᵀ = -(gramAt D V ρ) := fun ρ => by
    ext a b
    simp [gramAt]
  have hgr : ∀ ρ, ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) (-(V.gram)ᵀ) (x ρ) =
      Matrix.diagonal fun a : Fin V.rank => ((sgn Q (a : ℕ) : ℝ) : ℂ) := fun ρ => by
    have h1 := hg ρ
    simp only [hs] at h1
    rw [fdgram_eq, hmapT, Matrix.mul_neg, Matrix.neg_mul]
    exact h1
  have hin : ∀ ρ, tauE D ρ ∈ Formalism.L2.Pj.cmTypeOfSqrt D := fun ρ => by
    rw [Formalism.L2.Pj.mem_cm_type_iff, Formalism.L2.Theta.tauE_sqrtMinusD]
    exact (D.host.φ₀_mem).symm
  have hmem : ∀ τ : D.host.E →+* ℂ, τ ∈ Formalism.L2.Pj.cmTypeOfSqrt D ↔ ∃ ρ, τ = tauE D ρ := by
    intro τ
    refine ⟨fun h => ?_, fun ⟨ρ, hρ⟩ => hρ ▸ hin ρ⟩
    obtain ⟨ρ, hρ⟩ := (GlobalTheory.CMTypePlaces.mk_tauE_bijective D).2 (InfinitePlace.mk τ)
    rcases InfinitePlace.mk_eq_iff.1 hρ with h' | h'
    · exact ⟨ρ, h'.symm⟩
    · exact absurd (h' ▸ h) ((Formalism.L2.Pj.cm_type_mem_iff_conj_not_mem D _).1 (hin ρ))
  have hinj : Function.Injective (tauE D) := fun _ _ h =>
    (GlobalTheory.CMTypePlaces.mk_tauE_bijective D).1 (by simp only [h])
  obtain ⟨hh, hd, hfg, hsp, -⟩ := GlobalTheory.Member.selfDualLat_neg_gram_transpose D V
  obtain ⟨n, hn, hnint⟩ := GlobalTheory.PrincData.exists_nat_herm_int (-(V.gram)ᵀ) (GlobalTheory.Member.latC V) hfg
  obtain ⟨k, hk, hkint⟩ := GlobalTheory.PrincData.exists_nat_int (-(2 * D.host.xi0))
  obtain ⟨X, hΨ, hG, hp, -, -, -, -, -, -⟩ := GlobalTheory.FlagData.exists_data GlobalTheory.latMinkowski D.host.E V.rank Q 3
    (3 * n * k) (Formalism.L2.Pj.cmTypeOfSqrt D) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V) D.host.xi0 (-(2 * D.host.xi0))
    (Formalism.L2.Pj.cm_type_mem_iff_conj_not_mem D) hh hd (by omega)
    (fun τ hτ => by
      obtain ⟨ρ, rfl⟩ := (hmem τ).1 hτ
      exact ⟨x ρ, hdet ρ, hgr ρ⟩)
    hfg hsp le_rfl (Formalism.L2.Pj.conj_xi0_alt D)
    (by
      obtain ⟨ρ, -⟩ := (GlobalTheory.CMTypePlaces.mk_tauE_bijective D).2 (InfinitePlace.mk D.host.φ₀)
      intro h
      have h1 := Formalism.L2.Theta.xi_zero_im_pos D ρ
      rw [h] at h1
      simp at h1)
    (Or.inr rfl)
    (fun τ hτ => by
      obtain ⟨ρ, rfl⟩ := (hmem τ).1 hτ
      have h1 := Formalism.L2.Theta.xi_zero_im_pos D ρ
      simp [map_ofNat]
      linarith)
    (by positivity)
    (fun u hu v hv => by
      have e1 : ((3 * n * k : ℕ) : D.host.E) / ((3 : ℕ) : D.host.E) * (-(2 * D.host.xi0)) *
          ReciprocityTheory.ChartRestriction.G.FD.herm (-(V.gram)ᵀ) u v =
          ((k : D.host.E) * (-(2 * D.host.xi0))) * ((n : D.host.E) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(V.gram)ᵀ) u v) := by
        push_cast
        field_simp
      rw [e1]
      exact hkint.mul (hnint u hu v hv))
  let σ : D.what₂.Tau ≃ X.Ψ := Equiv.ofBijective (fun ρ => ⟨tauE D ρ, by rw [hΨ]; exact hin ρ⟩)
    ⟨fun _ _ h => hinj (congrArg Subtype.val h), fun τ => by
      obtain ⟨ρ, h⟩ := (hmem τ.1).1 (hΨ ▸ τ.2)
      exact ⟨ρ, Subtype.ext h.symm⟩⟩
  refine ⟨X, σ, fun τ => x (σ.symm τ), e, hG, fun ρ => rfl, fun τ => ?_, fun ρ => ⟨?_, ?_⟩⟩
  · have hτ : τ.1 = tauE D (σ.symm τ) := (congrArg Subtype.val (σ.apply_symm_apply τ)).symm
    show ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (x (σ.symm τ)) = _
    rw [hG, hp, hτ]
    exact hgr _
  · rw [hA ρ, hG]
    show gramAt D V ρ = -((-(V.gram)ᵀ).map (tauE D ρ))ᵀ
    rw [hmapT, neg_neg]
  · show A ρ * x (σ.symm (σ ρ)) = permM (e ρ)
    rw [σ.symm_apply_apply]
    exact hAx ρ

end GlobalTheory.CovTop.VolUp
