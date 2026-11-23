import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramHspOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddCharStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondegStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianNegTraceZeroInvHermitianUnimodularStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

namespace GlobalTheory.BigDat.ThBox

theorem isThetaFunO_mul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T S₁ T₁ S₂ T₂ : HSp D} (p₁ : WO S T →+ WO S₁ T₁)
    (p₂ : WO S T →+ WO S₂ T₂) (c₁ : Continuous p₁) (c₂ : Continuous p₂)
    (hs : ∀ x y, symplO S T x y = symplO S₁ T₁ (p₁ x) (p₁ y) + symplO S₂ T₂ (p₂ x) (p₂ y))
    (r₁ : ∀ γ, ∃ γ', p₁ (ratW T S γ) = ratW T₁ S₁ γ') (r₂ : ∀ γ, ∃ γ', p₂ (ratW T S γ) = ratW T₂ S₂ γ')
    (hi : ∀ u, u.map (infPart D) = 0 → (p₁ u).map (infPart D) = 0 ∧ (p₂ u).map (infPart D) = 0)
    (hf : ∀ u, u.map (finPart D) = 0 → (p₁ u).map (finPart D) = 0 ∧ (p₂ u).map (finPart D) = 0)
    {f₁ : WO S₁ T₁ → ℂ} {f₂ : WO S₂ T₂ → ℂ} (h₁ : IsThetaFunO ψ S₁ T₁ f₁) (h₂ : IsThetaFunO ψ S₂ T₂ f₂) :
    IsThetaFunO ψ S T fun u => f₁ (p₁ u) * f₂ (p₂ u) := by
  have hH : ∀ x y, symplOH S T x y = symplOH S₁ T₁ (p₁ x) (p₁ y) + symplOH S₂ T₂ (p₂ x) (p₂ y) := fun x y => by
    unfold symplOH
    rw [hs, mul_add]
  refine ⟨fun γ w => ?_, ?_, (h₁.cont.comp c₁).mul (h₂.cont.comp c₂), fun k L hL hL0 w => ?_⟩
  · obtain ⟨γ₁, e₁⟩ := r₁ γ
    obtain ⟨γ₂, e₂⟩ := r₂ γ
    rw [map_add, map_add, hH, e₁, e₂, h₁.quasi, h₂.quasi, neg_add, AddChar.map_add_eq_mul]
    ring
  · obtain ⟨U₁, o₁, hU₁⟩ := h₁.level
    obtain ⟨U₂, o₂, hU₂⟩ := h₂.level
    refine ⟨U₁.comap p₁ ⊓ U₂.comap p₂, (o₁.preimage c₁).inter (o₂.preimage c₂), fun u hu h0 => funext fun w => ?_⟩
    have a₁ := congrFun (hU₁ (p₁ u) hu.1 (hi u h0).1) (p₁ w)
    have a₂ := congrFun (hU₂ (p₂ u) hu.2 (hi u h0).2) (p₂ w)
    unfold heisO at a₁ a₂ ⊢
    beta_reduce
    rw [← a₁, ← a₂, hH, p₁.map_add, p₂.map_add, AddChar.map_add_eq_mul]
    ring
  · simp only [map_add]
    exact (h₁.smooth k (p₁.comp L) (c₁.comp hL) (fun t => (hf _ (hL0 t)).1) (p₁ w)).mul
      (h₂.smooth k (p₂.comp L) (c₂.comp hL) (fun t => (hf _ (hL0 t)).2) (p₂ w))

theorem mulG_map_zero {D : D7} {R : Type} [CommRing R] (φ : AE D →+* R) (S : HSp D) {n : ℕ}
    (x : Matrix (Fin n) (Fin S.rank) (AE D)) (h : x.map φ = 0) : (mulG S x).map φ = 0 := by
  rw [mulG_eq, Matrix.map_mul, h, Matrix.zero_mul]

theorem continuous_mulG {D : D7} (S : HSp D) {n : ℕ} : Continuous (mulG S (n := n)) := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  exact continuous_id.matrix_mul continuous_const

theorem mulG_rat {D : D7} (S : HSp D) {n : ℕ} (x : Matrix (Fin n) (Fin S.rank) D.host.E) :
    mulG S (x.map (incA D)) = (x * S.gram).map (incA D) := by
  rw [mulG_eq, Matrix.map_mul]

theorem infPart_cA {D : D7} (x : AE D) :
    infPart D (cA D x) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add, hx, hy]
  | tmul a x => rfl

theorem finPart_cA {D : D7} (x : AE D) :
    finPart D (cA D x) = sigR (Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add, hx, hy]
  | tmul a x => rfl

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

theorem maps_map_zero {R : Type} [CommRing R] (φ : AE D →+* R) (hφ : ∀ x, φ x = 0 → φ (cA D x) = 0) (e : Num G i j)
    (u : Pt G i j) (h : u.map φ = 0) : (mapV e u).map φ = 0 ∧ (mapW e u).map φ = 0 := by
  have h0 : ∀ a b, φ (u a b) = 0 := fun a b => congrFun (congrFun h a) b
  refine ⟨mulG_map_zero φ _ _ (Matrix.ext fun a b => h0 _ _), ?_⟩
  have h2 := mulG_map_zero φ (spV₁ G i j) ((u.submatrix id fun k => e (.inr k)).map (cA D))
    (Matrix.ext fun a b => hφ _ (h0 _ _))
  exact Matrix.ext fun a b => (map_neg φ _).trans (neg_eq_zero.2 (congrFun (congrFun h2 a) b))

theorem continuous_mapV (e : Num G i j) : Continuous (mapV e) :=
  (continuous_mulG (negSp (spW G i j))).comp (continuous_id.matrix_submatrix id fun k => e (.inl k)).matrix_transpose

theorem continuous_mapW (e : Num G i j) : Continuous (mapW e) := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  exact ((continuous_mulG (spV₁ G i j)).comp ((continuous_id.matrix_submatrix id fun k => e (.inr k)).matrix_map
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D))).neg

theorem mapV_rat (e : Num G i j) (γ : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) D.host.E) :
    ∃ γ', mapV e (γ.map (incA D)) = ratW (spV G i j) (negSp (spW G i j)) γ' :=
  ⟨_, mulG_rat (negSp (spW G i j)) (γ.submatrix id fun k => e (.inl k))ᵀ⟩

theorem mapW_rat (e : Num G i j) (γ : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) D.host.E) :
    ∃ γ', mapW e (γ.map (incA D)) = ratW (spW G i j) (spV₁ G i j) γ' :=
  ⟨-_, (congrArg Neg.neg (mulG_rat (spV₁ G i j) ((γ.submatrix id fun k => e (.inr k)).map star))).trans
    (Matrix.map_neg _ (map_neg (incA D)) _).symm⟩

theorem thetaPt_box : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (t : T) (i j : ℕ) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
    (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X → IsTriple Bs Γ X om om' →
    (∀ Φ ∈ schA D.host.F (Ix G i j), ∀ Φ' ∈ schA D.host.F (Ix G i j), thetaPt Γ W.ψ (Φ + Φ') = thetaPt Γ W.ψ Φ + thetaPt Γ W.ψ Φ') ∧
    (∀ Φ ∈ schA D.host.F (Ix G i j), ∀ Φ' ∈ schA D.host.F (Ix G i j), thetaPt Γ W.ψ Φ = thetaPt Γ W.ψ Φ' → Φ = Φ') ∧
    ∀ (f₁ : HomV G i j → ℂ) (f₂ : HomW G i j → ℂ), IsThetaFunO W.ψ _ _ f₁ → IsThetaFunO W.ψ _ _ f₂ →
      ∃ Φ ∈ schA D.host.F (Ix G i j), thetaPt Γ W.ψ Φ = box e f₁ f₂ := by
  intro D T L sc G W M t i j e Bs Γ X om om' h hT
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.hermitianSelfDualLatticeSpace_form_hermitian_nondeg_unimodular D Bs hT.base _ Γ.V _ _ hT.geo.hV
  obtain ⟨hJ, L', hL, h4, h5, h6⟩ := GlobalTheory.T.skewHermitian_neg_traceZero_inv_hermitian_unimodular D Bs hT.base _ Γ.W _ _ hT.geo.hW
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  let T₀ := GlobalTheory.WeilSchrodinger.hspOf D Γ.V.Jᵀ h1 h2 Γ.V.L hT.geo.hV.lat h3 (fun _ => (0, 0))
  let S₀ := GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 L' hL h6 (fun _ => (0, 0))
  have eA : Γ.V.J = T₀.gramᵀ := by rw [GlobalTheory.WeilSchrodinger.gram_hspOf]; rfl
  have eB : (-1 : AE D) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S₀.gram⁻¹) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
    have e1 : (-D.host.xi0 • Γ.W.J⁻¹)⁻¹ = (-D.host.xi0)⁻¹ • Γ.W.J := Matrix.inv_eq_left_inv (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJ,
        inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul])
    have e2 : D.host.xi0 • (-D.host.xi0)⁻¹ • Γ.W.J = -Γ.W.J := by
      rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ, neg_one_smul]
    show (-1 : AE D) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (-D.host.xi0 • Γ.W.J⁻¹)⁻¹)
    rw [e1, e2]
    funext a b
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  have hψ : IsStdChar D W.ψ (-1) := h.ψ ▸ GlobalTheory.T.isStdChar_neg_one_of_standardTraceAdelicAddChar D Bs.ψ hT.base.std
  obtain ⟨ha, hi, hs⟩ := GlobalTheory.ThetaTransform.thetaTr_bij (S := S₀) (T := T₀) Γ.M.co hψ eA eB hT.geo.hM.rat
  refine ⟨ha, hi, fun f₁ f₂ hf₁ hf₂ => (hs _).1 ?_⟩
  exact isThetaFunO_mul (S := S₀) (T := T₀) (AddMonoidHom.mk' (mapV e) (mapV_add e)) (AddMonoidHom.mk' (mapW e) (mapW_add e))
    (continuous_mapV e) (continuous_mapW e)
    (fun x y => (GlobalTheory.ThetaTransform.symplO_eq_symp eA eB x y).trans (symp_eq e Γ h.JW h.JWW x y))
    (mapV_rat e) (mapW_rat e)
    (maps_map_zero (infPart D) (fun x hx => by rw [infPart_cA, hx, map_zero]) e)
    (maps_map_zero (finPart D) (fun x hx => by rw [finPart_cA, hx, map_zero]) e) hf₁ hf₂

end GlobalTheory.BigDat.ThBox

end
