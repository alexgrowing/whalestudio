import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlaceIsoReadingComponentsCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedHermitianFormQuadSumEqTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeSelfDualEverywhere

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.FlipMatch.RowChart

open GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (blk blk_mul blk_one blk_transpose blk_map)

section Alg

variable {k : Type} [Field k] {n p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d)

theorem mul_cols {m : Type} (A : Matrix (Fin n) (Fin n) k) (U : Matrix (Fin n) (Fin d) k) (f : m → Fin d) :
    (A * U).submatrix id f = A * U.submatrix id f := rfl

theorem inv_of_blk {c cc : GL (Fin d) k} {βV : GL (Fin p) k} {β₁ : GL (Fin q) k}
    (hC : c.val * cc.val = blk e βV.val (-β₁.val)) :
    (c⁻¹).valᵀ * (cc⁻¹).valᵀ = blk e (βV⁻¹).valᵀ (-(β₁⁻¹).valᵀ) := by
  have h1 : (c.val * cc.val) * blk e (βV⁻¹).val (-(β₁⁻¹).val) = 1 := by
    rw [hC, blk_mul, neg_mul_neg, Units.mul_inv, Units.mul_inv, blk_one]
  have h2 : (cc⁻¹).val * (c⁻¹).val = blk e (βV⁻¹).val (-(β₁⁻¹).val) := by
    calc _ = (cc⁻¹).val * (c⁻¹).val * ((c.val * cc.val) * blk e (βV⁻¹).val (-(β₁⁻¹).val)) := by rw [h1, Matrix.mul_one]
      _ = (cc⁻¹).val * ((c⁻¹).val * c.val) * cc.val * blk e (βV⁻¹).val (-(β₁⁻¹).val) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [Units.inv_mul, Matrix.mul_one, Units.inv_mul, Matrix.one_mul]
  rw [← transpose_mul, h2, blk_transpose, transpose_neg]

theorem tr_eq {b β g : GL (Fin n) k} {Gm : Matrix (Fin n) (Fin n) k} (hg : g.val = -(β.valᵀ * Gmᵀ * b.val))
    {c cc : GL (Fin d) k} {βV : GL (Fin p) k} {β₁ : GL (Fin q) k} (hC : c.val * cc.val = blk e βV.val (-β₁.val))
    (U : Matrix (Fin n) (Fin d) k) :
    (g.val * ((b⁻¹).val * U * (c⁻¹).valᵀ) * (invT cc).val).submatrix id (fun a => e (.inl a)) =
        ((βV⁻¹).val * ((U.submatrix id fun a => e (.inl a))ᵀ * -Gm) * β.val)ᵀ ∧
      (g.val * ((b⁻¹).val * U * (c⁻¹).valᵀ) * (invT cc).val).submatrix id (fun a => e (.inr a)) =
        -(β.valᵀ * Gmᵀ) * (U.submatrix id fun a => e (.inr a)) * -(β₁⁻¹).valᵀ := by
  have h : g.val * ((b⁻¹).val * U * (c⁻¹).valᵀ) * (invT cc).val =
      (-(β.valᵀ * Gmᵀ) * U) * blk e (βV⁻¹).valᵀ (-(β₁⁻¹).valᵀ) := by
    rw [← inv_of_blk e hC, invT_val, hg]
    simp only [Matrix.neg_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc b.val, Units.mul_inv, Matrix.one_mul]
  rw [h, GlobalTheory.RouteCoords.submatrix_mul_blk_inl, GlobalTheory.RouteCoords.submatrix_mul_blk_inr, mul_cols, mul_cols]
  refine ⟨?_, rfl⟩
  simp only [transpose_mul, transpose_neg, transpose_transpose, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]

theorem mu_eq {b β g : GL (Fin n) k} {Gm : Matrix (Fin n) (Fin n) k} (hg : g.val = -(β.valᵀ * Gmᵀ * b.val))
    {c cc : GL (Fin d) k} {βV : GL (Fin p) k} {β₁ : GL (Fin q) k} (hC : c.val * cc.val = blk e βV.val (-β₁.val))
    {ξ : k} (hξ : ξ ≠ 0) (GV : Matrix (Fin p) (Fin p) k) (G₁ : Matrix (Fin q) (Fin q) k)
    (U : Matrix (Fin n) (Fin d) k) :
    (ξ⁻¹ • ((invT g).val * -(b.valᵀ * Gm * U * (ξ • blk e GVᵀ G₁ᵀ)ᵀ * c.val) * cc.val)).submatrix id (fun a => e (.inl a)) =
        (β⁻¹).val * (U.submatrix id fun a => e (.inl a)) * (GV * βV.val) ∧
      (ξ⁻¹ • ((invT g).val * -(b.valᵀ * Gm * U * (ξ • blk e GVᵀ G₁ᵀ)ᵀ * c.val) * cc.val)).submatrix id (fun a => e (.inr a)) =
        (β⁻¹).val * -((U.submatrix id fun a => e (.inr a)) * G₁) * β₁.val := by
  have h0 : (invT g).val * -(b.valᵀ * Gm) = (β⁻¹).val := by
    have h1 : -(b.valᵀ * Gm) = g.valᵀ * (β⁻¹).val := by
      rw [hg]
      simp only [transpose_mul, transpose_neg, transpose_transpose, Matrix.neg_mul, Matrix.mul_assoc, Units.mul_inv,
        Matrix.mul_one]
    rw [h1, invT_val, ← Matrix.mul_assoc, ← transpose_mul, Units.mul_inv, transpose_one, Matrix.one_mul]
  have h : ξ⁻¹ • ((invT g).val * -(b.valᵀ * Gm * U * (ξ • blk e GVᵀ G₁ᵀ)ᵀ * c.val) * cc.val) =
      ((β⁻¹).val * U) * blk e (GV * βV.val) (G₁ * -β₁.val) := by
    rw [← blk_mul, ← hC, ← h0, transpose_smul, blk_transpose, transpose_transpose, transpose_transpose]
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul, smul_neg, smul_smul,
      inv_mul_cancel₀ hξ, one_smul]
  rw [h, GlobalTheory.RouteCoords.submatrix_mul_blk_inl, GlobalTheory.RouteCoords.submatrix_mul_blk_inr, mul_cols, mul_cols]
  refine ⟨rfl, ?_⟩
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]

end Alg

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {v : HeightOneSpectrum (𝓞 F)} {τ : E →ₐ[F] Fv F v} {L : Submodule (𝓞 E) (Fin n → E)}

theorem single_int (i j : Fin n) : (Pi.single j 1 : Fin n → Fv F v) i ∈ v.adicCompletionIntegers F := by
  rw [Pi.single_apply]
  split_ifs
  exacts [one_mem _, zero_mem _]

theorem pairing_int (h : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) (hL : IsSelfDualAt σ J L v)
    {b β g : GL (Fin n) (Fv F v)} (hb : IsSplitBasis τ L b) (hβ : IsSplitBasis (τ.comp σ) L β)
    (hg : g.val = β.valᵀ * J.map τ * b.val) :
    (∀ i j, g.val i j ∈ v.adicCompletionIntegers F) ∧ ∀ i j, (g⁻¹).val i j ∈ v.adicCompletionIntegers F := by
  have key : ∀ z y : Fin n → Fv F v, (β.val *ᵥ z) ⬝ᵥ J.map τ *ᵥ (b.val *ᵥ y) = z ⬝ᵥ g.val *ᵥ y := fun z y => by
    rw [hg, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec z β.valᵀ, vecMul_transpose]
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · have := (mem_splitLat_comp_iff h hJ hL).1 ((hβ _).1 fun r => single_int r i) _ ((hb _).1 fun r => single_int r j)
    rw [key] at this
    simpa using this
  · refine (hβ fun j => (g⁻¹).val i j).2 ((mem_splitLat_comp_iff h hJ hL).2 fun x hx => ?_)
    have hx' : b.val *ᵥ ((b⁻¹).val *ᵥ x) = x := by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
    have h1 := (hb _).2 (hx'.symm ▸ hx) i
    rw [← hx', key]
    have h2 : (fun j => (g⁻¹).val i j) ⬝ᵥ g.val *ᵥ ((b⁻¹).val *ᵥ x) = ((g⁻¹).val *ᵥ (g.val *ᵥ ((b⁻¹).val *ᵥ x))) i := rfl
    rw [h2, mulVec_mulVec, Units.inv_mul, one_mulVec]
    exact h1

omit [NumberField E] in
theorem splitLat_le {τ' : E →ₐ[F] Fv F v} {L' : Submodule (𝓞 E) (Fin n → E)}
    (h : ∀ x ∈ L, ∃ x' ∈ L', ∀ i, τ (x i) = τ' (x' i)) : splitLat τ L ≤ splitLat τ' L' := by
  rintro _ ⟨y, hy, rfl⟩
  refine latLoc_induction (p := fun y => splitVec τ y ∈ splitLat τ' L') (fun a ha x hx => ?_) ?_
    (fun y z hy hz => ?_) (fun y hy => ?_) hy
  · obtain ⟨x', hx', e⟩ := h x hx
    exact ⟨_, tmul_mem_latLoc ha hx', funext fun i => by simp [splitVec, e]⟩
  · have e1 : splitVec τ (0 : Fin n → Fv F v ⊗[F] E) = 0 := funext fun i => by simp [splitVec]
    rw [e1]; exact zero_mem _
  · rw [splitVec_add]; exact add_mem hy hz
  · have e1 : splitVec τ (-y) = -splitVec τ y := funext fun i => by simp [splitVec]
    rw [e1]; exact neg_mem hy

end Lat

section Frame

theorem isFrameAt_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (h : IsFrame β Λ)
    (w : HeightOneSpectrum (𝓞 E)) (c : E ⊗[F] Formalism.L2.Herm.Af F →+* w.adicCompletion E)
    (hι : ∀ x, c (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) x) = algebraMap E _ x)
    (hc : ∀ x ∈ Formalism.L2.Herm.intAf F E, c x ∈ Formalism.UG.Ov E w) : IsFrameAt w Λ (GeneralLinearGroup.map c β) := by
  have k1 : ∀ x ∈ Formalism.L2.Herm.hatL (F := F) Λ, (fun i => c (x i)) ∈ latAt w Λ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      exact Submodule.subset_span ⟨x, hx, funext fun i => (hι _).symm⟩
    | zero => exact (funext fun _ => map_zero c : (fun i => c ((0 : Fin n → _) i)) = 0) ▸ zero_mem _
    | add x z _ _ hx hz =>
      have := add_mem hx hz
      convert this using 1
      exact funext fun i => map_add c _ _
    | smul r x _ hx =>
      have := (latAt w Λ).smul_mem ⟨c r.1, hc _ r.2⟩ hx
      convert this using 1
      exact funext fun i => map_mul c _ _
  have k2 : ∀ x ∈ latAt w Λ, ∀ i, (((GeneralLinearGroup.map c β)⁻¹).val *ᵥ x) i ∈ Formalism.UG.Ov E w := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      intro i
      have h1 := hc _ ((h _).1 (Submodule.subset_span ⟨x, hx, rfl⟩) i)
      have h2 := RingHom.map_mulVec c (β⁻¹).val (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) i
      have h3 : c ∘ (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) = fun i => algebraMap E _ (x i) :=
        funext fun i => hι _
      rw [h3] at h2
      exact h2 ▸ h1
    | zero => intro i; rw [mulVec_zero]; exact zero_mem _
    | add x z _ _ hx hz => intro i; rw [mulVec_add]; exact add_mem (hx i) (hz i)
    | smul r x _ hx =>
      intro i
      have := mulVec_smul ((GeneralLinearGroup.map c β)⁻¹).val r.1 x
      rw [show ((GeneralLinearGroup.map c β)⁻¹).val *ᵥ (r • x) = _ from this]
      exact mul_mem r.2 (hx i)
  intro y
  refine ⟨fun hy => ?_, fun hy i => ?_⟩
  · have e : (GeneralLinearGroup.map c β).val *ᵥ y =
        ∑ j, (⟨y j, hy j⟩ : Formalism.UG.Ov E w) • fun i => c ((β.val *ᵥ Pi.single j 1) i) := by
      funext i
      rw [Finset.sum_apply, mulVec, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mulVec_single_one]
      exact mul_comm _ _
    rw [e]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (k1 _ ((h _).2 fun l => ?_))
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec, Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  · have := k2 _ hy i
    rwa [mulVec_mulVec, Units.inv_mul, one_mulVec] at this

variable {D : D7} {n : ℕ}

theorem isFrameAt_loc {β : GL (Fin n) (Formalism.IndefR.Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (h : IsFrame β Λ) (w : Pl D.host.E) : IsFrameAt w Λ (loc w β) :=
  isFrameAt_map h w (cpt w) (fun x =>
    congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z w) (GlobalTheory.AdeleBaseChange.map_tmul_one (toAd_spec D) x))
    fun x hx => (mem_OA_iff _).1 hx w

variable {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)

theorem eq_complEquiv {jj : Fv D.host.F v ≃+* Kw (splitPrime τ)} (h : IsPlaceIso τ (splitPrime τ) jj) :
    jj = complEquiv τ (splitPrime_under τ) := by
  classical
  refine RingEquiv.ext fun x => ?_
  have hp : piW τ (atPl (splitPrime τ) (complEquiv τ (splitPrime_under τ) x)) = x :=
    (complEquiv τ (splitPrime_under τ)).injective (by rw [isPlaceIso_complEquiv τ, (atPl_spec _ _).2, Pi.single_eq_same])
  conv_lhs => rw [← hp, h, (atPl_spec _ _).2, Pi.single_eq_same]

theorem isSplitBasis_conj {β : GL (Fin n) (Kw (splitPrime τ))} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (h : IsFrameAt (splitPrime τ) Λ β) :
    IsSplitBasis (τ.comp D.sp.cm.sig) (GlobalTheory.TripleSpaceW.conjSub Λ)
      (GeneralLinearGroup.map (complEquiv τ (splitPrime_under τ)).symm.toRingHom β) := by
  set ψ := complEquiv τ (splitPrime_under τ) with hψ
  have h2 : ∀ x, ψ (τ x) = algebraMap D.host.E _ x := complMap_apply_emb τ _
  have h3 : ∀ a, Valued.v (ψ a) = Valued.v a := SplitTie.valued_complMap τ _
  have e : splitLat (τ.comp D.sp.cm.sig) (GlobalTheory.TripleSpaceW.conjSub Λ) = splitLat τ Λ := by
    refine le_antisymm (splitLat_le fun x hx => ⟨star x, hx, fun i => rfl⟩) (splitLat_le fun x hx => ⟨star x, ?_, fun i => ?_⟩)
    · rw [GlobalTheory.TripleSpaceW.mem_conjSub, star_star]; exact hx
    · change τ (x i) = τ (star (star (x i)))
      rw [star_star]
  intro u
  rw [e, ← SplitChart.map_mem_latAt_iff h2 h3]
  have e2 : (fun i => ψ (((GeneralLinearGroup.map ψ.symm.toRingHom β).val *ᵥ u) i)) = β.val *ᵥ fun i => ψ (u i) := by
    funext i
    simp [mulVec, dotProduct, map_sum, GeneralLinearGroup.map_apply]
  rw [e2, ← h]
  exact forall_congr' fun i => (SplitChart.map_mem_Ov_iff h3).symm

end Frame

theorem piW_cA_eq {D : D7} {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (z : AE D) :
    piW τ (cA D z) = piW (τ.comp D.sp.cm.sig) z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a x => exact (piW_tmul τ a (D.sp.cm.sig x)).trans (piW_tmul (τ.comp D.sp.cm.sig) a x).symm
  | add x y hx hy => rw [RingHom.map_add (cA D), RingHom.map_add (piW τ), RingHom.map_add (piW _), hx, hy]

section Rows

variable {D : D7} {n : ℕ} {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)

theorem exists_rows {J : Matrix (Fin n) (Fin n) D.host.E} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hJ : IsHermND D.sp.cm.sig Jᵀ) (hL : IsSelfDualAt D.sp.cm.sig Jᵀ (GlobalTheory.TripleSpaceW.conjSub Λ) v)
    {b : GL (Fin n) (Fv D.host.F v)} (hb : IsSplitBasis τ (GlobalTheory.TripleSpaceW.conjSub Λ) b)
    {β : GL (Fin n) (Kw (splitPrime τ))} (hβ : IsFrameAt (splitPrime τ) Λ β) :
    ∃ g ∈ KO (Kw (splitPrime τ)) (Fin n), g.val = -(β.valᵀ * (J.map (algebraMap D.host.E (Kw (splitPrime τ))))ᵀ *
      b.val.map (complEquiv τ (splitPrime_under τ))) := by
  have hβ' := isSplitBasis_conj τ hβ
  have hI := (isLocIso_complEquiv τ).2.2
  set ψ := complEquiv τ (splitPrime_under τ) with hψ
  have h2 : ∀ x, ψ (τ x) = algebraMap D.host.E _ x := complMap_apply_emb τ _
  have hd : (Jᵀ.map τ).det ≠ 0 := by
    have e : (Jᵀ.map τ).det = τ Jᵀ.det := (RingHom.map_det (τ : D.host.E →+* Fv D.host.F v) _).symm
    rw [e]
    exact (map_ne_zero _).2 hJ.2
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : GL (Fin n) (Fv D.host.F v),
      g₀.val = (GeneralLinearGroup.map ψ.symm.toRingHom β).valᵀ * Jᵀ.map τ * b.val :=
    ⟨(invT (GeneralLinearGroup.map ψ.symm.toRingHom β))⁻¹ * GeneralLinearGroup.mkOfDetNeZero _ hd * b, rfl⟩
  obtain ⟨k1, k2⟩ := pairing_int (isCMExt_host D) hJ hL hb hβ' hg₀
  have hint : ∀ x ∈ v.adicCompletionIntegers D.host.F, -ψ x ∈ (ValuativeRel.valuation (Kw (splitPrime τ))).integer :=
    fun x hx => neg_mem ((hI x).2 ((isEquiv_Fv v).le_one_iff_le_one.2 hx))
  refine ⟨-GeneralLinearGroup.map ψ.toRingHom g₀, (mem_KO_iff _).2 ⟨fun i j => hint _ (k1 i j), fun i j => ?_⟩, ?_⟩
  · rw [← neg_inv, ← map_inv]
    exact hint _ (k2 i j)
  · have e : (-GeneralLinearGroup.map ψ.toRingHom g₀).val = -(g₀.val.map ψ.toRingHom) := rfl
    have e1 : ((GeneralLinearGroup.map ψ.symm.toRingHom β).valᵀ).map ψ.toRingHom = β.valᵀ :=
      Matrix.ext fun i j => ψ.apply_symm_apply _
    have e2 : (Jᵀ.map τ).map ψ.toRingHom = (J.map (algebraMap D.host.E (Kw (splitPrime τ))))ᵀ :=
      Matrix.ext fun i j => h2 _
    rw [e, hg₀, Matrix.map_mul, Matrix.map_mul, e1, e2]
    rfl

theorem cpt_cA_atPl : cpt (D := D) (splitPrime τ) (toEAf D (cA D (atPl (splitPrime τ) 1))) = 0 := by
  classical
  have hp2 : piW (τ.comp D.sp.cm.sig) (atPl (splitPrime τ) 1) = 0 :=
    (complEquiv (τ.comp D.sp.cm.sig) (splitPrime_under _)).injective (by
      rw [isPlaceIso_complEquiv (τ.comp D.sp.cm.sig), (atPl_spec _ _).2,
        Pi.single_eq_of_ne (splitPrime_comp_ne (isCMExt_host D) τ), map_zero])
  rw [← isPlaceIso_complEquiv τ, piW_cA_eq, hp2, map_zero]

theorem half_cancel {R : Type} [CommRing R] {m r : ℕ} {ε : R} {x : Matrix (Fin m) (Fin r) R} {A B : Matrix (Fin r) (Fin r) R}
    (hAB : B * A = 1) (h : ∀ a b, ε * (x * A) a b = (x * A) a b) (a : Fin m) (b : Fin r) : ε * x a b = x a b := by
  have h1 : ε • (x * A) = x * A := Matrix.ext h
  have h2 := congrArg (fun y : Matrix (Fin m) (Fin r) R => y * B) h1
  simp only [Matrix.smul_mul, Matrix.mul_assoc, mul_eq_one_comm.1 hAB, Matrix.mul_one] at h2
  exact congrFun (congrFun h2 a) b

theorem isHalf_of_mulG {ε : AE D} (S : HSp D) {m : ℕ} {x : Matrix (Fin m) (Fin S.rank) (AE D)} (h : IsHalf ε (mulG S x)) :
    IsHalf ε x := half_cancel (GlobalTheory.RouteCoords.inv_mul_gram S) h

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

theorem mixHalf_entries {e : Num G i j} {ε : AE D} {u} (hu : u ∈ mixHalf e ε) :
    (∀ a k, ε * u a (e (.inl k)) = u a (e (.inl k))) ∧ (∀ a k, cA D ε * cA D (u a (e (.inl k))) = cA D (u a (e (.inl k)))) ∧
      (∀ a k, ε * cA D (u a (e (.inr k))) = cA D (u a (e (.inr k)))) ∧
      ∀ a k, cA D ε * u a (e (.inr k)) = u a (e (.inr k)) := by
  have h1 : ∀ a k, ε * u a (e (.inl k)) = u a (e (.inl k)) := fun a k => isHalf_of_mulG _ hu.1 k a
  have h2 : ∀ a k, ε * cA D (u a (e (.inr k))) = cA D (u a (e (.inr k))) :=
    isHalf_of_mulG (spV₁ G i j) (x := (u.submatrix id fun k => e (.inr k)).map (cA D)) fun a k =>
      neg_injective ((mul_neg _ _).symm.trans (hu.2 a k))
  refine ⟨h1, fun a k => by rw [← RingHom.map_mul, h1], h2, fun a k => ?_⟩
  have := congrArg (cA D) (h2 a k)
  rwa [RingHom.map_mul, GlobalTheory.DualPairCheck.cA_cA] at this

theorem at_cA {ε : AE D} (h : At (evFin D.host.F v) ε) : At (evFin D.host.F v) (cA D ε) := fun a ha => by
  have : cA D (a • ε) = a • cA D ε := map_smul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) a ε
  rw [← this, h a ha, map_zero]

theorem at_of_mixHalf {e : Num G i j} {ε : AE D} (h : At (evFin D.host.F v) ε) {u} (hu : u ∈ mixHalf e ε) :
    At (evFin D.host.F v) u := fun a ha => by
  obtain ⟨h1, -, -, h2⟩ := mixHalf_entries hu
  ext r s
  obtain ⟨k | k, rfl⟩ := e.surjective s
  · rw [Matrix.smul_apply, ← h1, ← smul_mul_assoc, h a ha, zero_mul, Matrix.zero_apply]
  · rw [Matrix.smul_apply, ← h2, ← smul_mul_assoc, at_cA h a ha, zero_mul, Matrix.zero_apply]

end Rows

section Main

abbrev cw {D : D7} (w : Pl D.host.E) : AE D →+* Kw w := (cpt (D := D) w).comp (toEAf D)

theorem map_mulG {D : D7} (w : Pl D.host.E) (S : HSp D) {m : ℕ} (x : Matrix (Fin m) (Fin S.rank) (AE D)) :
    ((mulG S x).map fun a => cpt (D := D) w (toEAf D a)) =
      HMul.hMul (x.map (cw w)) (S.gram.map (algebraMap D.host.E (Kw w))) := by
  have e : (S.gram.map (incA D)).map (cw w) = S.gram.map (algebraMap D.host.E (Kw w)) :=
    Matrix.ext fun a b => Good.cpt_incA w _
  rw [← e]
  exact Matrix.map_mul (f := cw w)

theorem map_mulG_neg {D : D7} (w : Pl D.host.E) (S : HSp D) {m : ℕ} (x : Matrix (Fin m) (Fin S.rank) (AE D)) :
    ((mulG (negSp S) x).map fun a => cpt (D := D) w (toEAf D a)) =
      HMul.hMul (x.map (cw w)) (-S.gram.map (algebraMap D.host.E (Kw w))) := by
  have e : (negSp S).gram.map (algebraMap D.host.E (Kw w)) = -S.gram.map (algebraMap D.host.E (Kw w)) :=
    Matrix.ext fun a b => map_neg (algebraMap D.host.E (Kw w)) _
  rw [← e]
  exact map_mulG w (negSp S) x

theorem map_neg_mulG {D : D7} (w : Pl D.host.E) (S : HSp D) {m : ℕ} (x : Matrix (Fin m) (Fin S.rank) (AE D)) :
    ((-mulG S x).map fun a => cpt (D := D) w (toEAf D a)) =
      -HMul.hMul (x.map (cw w)) (S.gram.map (algebraMap D.host.E (Kw w))) := by
  rw [← map_mulG]
  exact Matrix.map_neg (cw w) (RingHom.map_neg (cw w)) _

theorem chart_coX {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) {k : Type} [Field k]
    (j : Fv F v ≃+* k) (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) :
    (coX t b c u).map j = ((GeneralLinearGroup.map j.toRingHom b)⁻¹).val * (u.map (piW t)).map j *
      ((GeneralLinearGroup.map j.toRingHom c)⁻¹).valᵀ := by
  change (coX t b c u).map j.toRingHom = _
  rw [coX, Matrix.map_mul, Matrix.map_mul]
  rfl

theorem chart_coY {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v))
    (c : GL (Fin d) (Fv F v)) {k : Type} [Field k] (j : Fv F v ≃+* k) (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) :
    (coY σ X Y t b c u).map j = -((GeneralLinearGroup.map j.toRingHom b).valᵀ * (X.J.map t).map j *
      (u.map (piW (t.comp σ))).map j * ((Y.J.map t).map j)ᵀ * (GeneralLinearGroup.map j.toRingHom c).val) := by
  change (coY σ X Y t b c u).map j.toRingHom = _
  rw [coY, Matrix.map_neg _ (map_neg _), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]
  rfl

theorem charts {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n p q d : ℕ}
    (e : Fin p ⊕ Fin q ≃ Fin d) (X : Spc F E n) (Y : Spc F E d) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t : E →ₐ[F] Fv F v)
    (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) {k : Type} [Field k] (j : Fv F v ≃+* k)
    (β g : GL (Fin n) k) (Gm : Matrix (Fin n) (Fin n) k) (hg : g.val = -(β.valᵀ * Gmᵀ * b.val.map j))
    (cc : GL (Fin d) k) (βV : GL (Fin p) k) (β₁ : GL (Fin q) k) (hC : c.val.map j * cc.val = blk e βV.val (-β₁.val))
    {ξ : k} (hξ : ξ ≠ 0) (GV : Matrix (Fin p) (Fin p) k) (G₁ : Matrix (Fin q) (Fin q) k)
    (hJ : (X.J.map t).map j = Gm) (hJ' : (Y.J.map t).map j = ξ • blk e GVᵀ G₁ᵀ)
    {A C₁ C₂ : Type} (ρ : Fin n ≃ A) (ρ₁ : Fin p ≃ C₁) (ρ₂ : Fin q ≃ C₂)
    (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) (U U' : Matrix (Fin n) (Fin d) k)
    (hU : (u.map (piW t)).map j = U) (hU' : (u.map (piW (t.comp σ))).map j = U')
    (tr mu : Matrix A (C₁ ⊕ C₂) k)
    (htr : tr = chart j ρ (e.symm.trans (Equiv.sumCongr ρ₁ ρ₂)) g (invT cc) (coX t b c u))
    (hmu : mu = ξ⁻¹ • chart j ρ (e.symm.trans (Equiv.sumCongr ρ₁ ρ₂)) (invT g) cc (coY σ X Y t b c u)) :
    (∀ r a, tr r (.inl a) = ((βV⁻¹).val * ((U.submatrix id fun a => e (.inl a))ᵀ * -Gm) * β.val) (ρ₁.symm a) (ρ.symm r)) ∧
    (∀ r a, mu r (.inr a) = ((β⁻¹).val * -((U'.submatrix id fun a => e (.inr a)) * G₁) * β₁.val) (ρ.symm r) (ρ₂.symm a)) ∧
    ((∀ r a, U r (e (.inl a)) = 0) → ∀ r a, tr r (.inl a) = 0) ∧ ((∀ r a, U r (e (.inr a)) = 0) → ∀ r a, tr r (.inr a) = 0) ∧
    ((∀ r a, U' r (e (.inl a)) = 0) → ∀ r a, mu r (.inl a) = 0) ∧ ((∀ r a, U' r (e (.inr a)) = 0) → ∀ r a, mu r (.inr a) = 0) := by
  obtain ⟨t1, t2⟩ := tr_eq e (b := GeneralLinearGroup.map j.toRingHom b) (c := GeneralLinearGroup.map j.toRingHom c) hg hC U
  obtain ⟨m1, m2⟩ := mu_eq e (b := GeneralLinearGroup.map j.toRingHom b) (c := GeneralLinearGroup.map j.toRingHom c) hg hC
    hξ GV G₁ U'
  rw [chart, chart_coX, hU] at htr
  rw [chart, chart_coY, hU', hJ, hJ'] at hmu
  have T1 : ∀ r a, tr r (.inl a) = _ := fun r a => (congrFun (congrFun htr r) (.inl a)).trans (congrFun (congrFun t1 (ρ.symm r)) (ρ₁.symm a))
  have T2 : ∀ r a, tr r (.inr a) = _ := fun r a => (congrFun (congrFun htr r) (.inr a)).trans (congrFun (congrFun t2 (ρ.symm r)) (ρ₂.symm a))
  have M1 : ∀ r a, mu r (.inl a) = _ := fun r a => (congrFun (congrFun hmu r) (.inl a)).trans (congrFun (congrFun m1 (ρ.symm r)) (ρ₁.symm a))
  have M2 : ∀ r a, mu r (.inr a) = _ := fun r a => (congrFun (congrFun hmu r) (.inr a)).trans (congrFun (congrFun m2 (ρ.symm r)) (ρ₂.symm a))
  refine ⟨T1, M2, fun h r a => ?_, fun h r a => ?_, fun h r a => ?_, fun h r a => ?_⟩
  · rw [T1, show (U.submatrix id fun a => e (.inl a)) = 0 from Matrix.ext h]; simp
  · rw [T2, show (U.submatrix id fun a => e (.inr a)) = 0 from Matrix.ext h]; simp
  · rw [M1, show (U'.submatrix id fun a => e (.inl a)) = 0 from Matrix.ext h]; simp
  · rw [M2, show (U'.submatrix id fun a => e (.inr a)) = 0 from Matrix.ext h]; simp

theorem gram_blk {D : D7} (w : Pl D.host.E) (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) :
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e).map (algebraMap D.host.E (Kw w)) =
      xiAt w • blk e (A.gram.map (algebraMap D.host.E (Kw w)))ᵀ (B.gram.map (algebraMap D.host.E (Kw w)))ᵀ := by
  have e1 := blk_map e A.gramᵀ B.gramᵀ (map_zero (algebraMap D.host.E (Kw w)))
  rw [transpose_map, transpose_map] at e1
  rw [← e1]
  exact Matrix.ext fun a b => map_mul (algebraMap D.host.E (Kw w)) _ _

section Co

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (B : Frames G) (t : T) {i j : Fin D.R.m}
  (e : Num G i j) (w : Pl D.host.E)
  (u : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D))

theorem mixCo_inl (r s) : mixCo B t e w u r (.inl s) =
    (((loc w (B.β i (j + 1)))⁻¹).val * HMul.hMul ((u.map (cw w)).submatrix id fun a => e (.inl a))ᵀ
      (-(spW G i j).gram.map (algebraMap D.host.E (Kw w))) * (loc w (B.β (i + 1) (j + 1))).val)
      ((finCongr (rank_vertex G t w (X := (i, j + 1)) ⟨i.2.le, j.2⟩).symm).symm s) ((finCongr (rankW G t i j w)).symm r) := by
  have e1 : ((mulG (negSp (spW G i j)) (colV e u)ᵀ).map fun a => cpt (D := D) w (toEAf D a)) =
      HMul.hMul ((u.map (cw w)).submatrix id fun a => e (.inl a))ᵀ (-(spW G i j).gram.map (algebraMap D.host.E (Kw w))) :=
    map_mulG_neg _ _ _
  rw [mixCo, fromCols_apply_inl, Frames.coord, e1]
  rfl

theorem mixCo_inr (r s) : mixCo B t e w u r (.inr s) =
    (((loc w (B.β (i + 1) (j + 1)))⁻¹).val * -HMul.hMul (((u.map (cA D)).map (cw w)).submatrix id fun a => e (.inr a))
      ((spV₁ G i j).gram.map (algebraMap D.host.E (Kw w))) * (loc w (B.β (i + 1) j)).val)
      ((finCongr (rankW G t i j w)).symm r) ((finCongr (rank_vertex G t w (X := (i + 1, j)) ⟨i.2, j.2.le⟩).symm).symm s) := by
  have e1 : ((adjV₁ e u).map fun a => cpt (D := D) w (toEAf D a)) =
      -HMul.hMul (((u.map (cA D)).map (cw w)).submatrix id fun a => e (.inr a))
        ((spV₁ G i j).gram.map (algebraMap D.host.E (Kw w))) :=
    map_neg_mulG w (spV₁ G i j) ((u.submatrix id fun k => e (.inr k)).map (cA D))
  rw [mixCo, fromCols_apply_inr, Frames.coord, e1]
  rfl

end Co

theorem isMixChart_of {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (B : Frames G) (t : T)
    (i j : Fin D.R.m) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) {v : Pl D.host.F}
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (ψ : Fv D.host.F v ≃+* Kw (splitPrime τ)) (hjj : IsPlaceIso τ (splitPrime τ) ψ)
    (h2 : ∀ x, ψ (τ x) = algebraMap D.host.E (Kw (splitPrime τ)) x)
    (hJW : Γ.V.J = (spW G i j).gram) (hJWW : Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e)
    (cc : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw (splitPrime τ)))
    (hcc : (Γ.W.bas v).val.map ψ * cc.val = basCols B e (splitPrime τ))
    (g : GL (Fin (spW G i j).rank) (Kw (splitPrime τ)))
    (hg : g.val = -((loc (splitPrime τ) (B.β (i + 1) (j + 1))).valᵀ *
      ((spW G i j).gram.map (algebraMap D.host.E (Kw (splitPrime τ))))ᵀ * (Γ.V.bas v).val.map ψ)) :
    IsMixChart v (mixHalf e (atPl (splitPrime τ) 1)) (mixHalf e (cA D (atPl (splitPrime τ) 1))) (mixCo B t e (splitPrime τ))
      (fun u => chart ψ (finCongr (rankW G t i j (splitPrime τ))) (colsEq t e (splitPrime τ)) g (invT cc)
        (coX τ (Γ.V.bas v) (Γ.W.bas v) u))
      (fun u => (xiAt (splitPrime τ))⁻¹ • chart ψ (finCongr (rankW G t i j (splitPrime τ))) (colsEq t e (splitPrime τ)) (invT g) cc
        (coY D.sp.cm.sig Γ.V Γ.W τ (Γ.V.bas v) (Γ.W.bas v) u))
      (Assignment.one.block _ _)ᶜ := by
  have hξ : xiAt (D := D) (splitPrime τ) ≠ 0 := (map_ne_zero _).2 cmHost_imaginaryGenerator_ne_zero
  have eU : ∀ u : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D),
      (u.map (piW τ)).map ψ = u.map (cw (splitPrime τ)) := fun u => Matrix.ext fun a b => hjj _
  have eU' : ∀ u : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D),
      (u.map (piW (τ.comp D.sp.cm.sig))).map ψ = (u.map (cA D)).map (cw (splitPrime τ)) :=
    fun u => Matrix.ext fun a b => (congrArg ψ (piW_cA_eq τ _).symm).trans (hjj _)
  have eJ : (Γ.V.J.map τ).map ψ = (spW G i j).gram.map (algebraMap D.host.E (Kw (splitPrime τ))) := by
    rw [← hJW]
    exact Matrix.ext fun a b => h2 _
  have eJ' : (Γ.W.J.map τ).map ψ = xiAt (splitPrime τ) • blk e
      ((spV G i j).gram.map (algebraMap D.host.E (Kw (splitPrime τ))))ᵀ
      ((spV₁ G i j).gram.map (algebraMap D.host.E (Kw (splitPrime τ))))ᵀ := by
    rw [← gram_blk, ← hJWW]
    exact Matrix.ext fun a b => h2 _
  have key := fun u : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D) =>
    charts D.sp.cm.sig e Γ.V Γ.W τ (Γ.V.bas v) (Γ.W.bas v) ψ (loc (splitPrime τ) (B.β (i + 1) (j + 1))) g
      ((spW G i j).gram.map (algebraMap D.host.E (Kw (splitPrime τ)))) hg cc (loc (splitPrime τ) (B.β i (j + 1)))
      (loc (splitPrime τ) (B.β (i + 1) j)) hcc hξ ((spV G i j).gram.map (algebraMap D.host.E (Kw (splitPrime τ))))
      ((spV₁ G i j).gram.map (algebraMap D.host.E (Kw (splitPrime τ)))) eJ eJ' (finCongr (rankW G t i j (splitPrime τ)))
      (finCongr (rank_vertex G t (splitPrime τ) (X := (i, j + 1)) ⟨i.2.le, j.2⟩).symm)
      (finCongr (rank_vertex G t (splitPrime τ) (X := (i + 1, j)) ⟨i.2, j.2.le⟩).symm) u _ _ (eU u) (eU' u) _ _ rfl rfl
  have hε := at_atPl τ 1
  have h0 : cw (splitPrime τ) (cA D (atPl (splitPrime τ) 1)) = 0 := cpt_cA_atPl τ
  have z : ∀ x : AE D, cA D (atPl (splitPrime τ) 1) * x = x → cw (splitPrime τ) x = 0 := fun x hx => by
    rw [← hx, RingHom.map_mul, h0, zero_mul]
  rw [compl_block_one]
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨-, a2, -, a4⟩ := mixHalf_entries hu
    obtain ⟨k1, k2, -, k4, k5, -⟩ := key u
    replace k4 := k4 fun r a => z _ (a4 r a)
    replace k5 := k5 fun r a => z _ (a2 r a)
    refine ⟨at_of_mixHalf hε hu, ?_, ?_, ?_⟩
    · rintro r (s | s) hs
      · simp [Assignment.block] at hs
      · exact k4 r s
    · rintro r (s | s) hs
      · exact k5 r s
      · simp [Assignment.block] at hs
    · refine Matrix.ext fun r s => ?_
      rcases s with s | s
      · refine Eq.trans ?_ (congrArg₂ (· + ·) (k1 r s) (k5 r s)).symm
        exact (mixCo_inl B t e _ u r s).trans (add_zero _).symm
      · refine Eq.trans ?_ (congrArg₂ (· + ·) (k4 r s) (k2 r s)).symm
        exact (mixCo_inr B t e _ u r s).trans (zero_add _).symm
  · obtain ⟨a1, -, a3, -⟩ := mixHalf_entries hu
    obtain ⟨-, -, k3, -, -, k6⟩ := key u
    replace k3 := k3 fun r a => z _ (a1 r a)
    replace k6 := k6 fun r a => z _ (a3 r a)
    refine ⟨at_of_mixHalf (at_cA hε) hu, ?_, ?_⟩
    · rintro r (s | s) hs
      · exact k3 r s
      · simp [Assignment.block] at hs
    · rintro r (s | s) hs
      · simp [Assignment.block] at hs
      · exact k6 r s

theorem exists_mixChart : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
    (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X →
    ∀ (v : Bs.P) (w : Pl D.host.E), splitPrime (Bs.τ v) = w → ∀ jj : Fv D.host.F v ≃+* Kw w, IsPlaceIso (Bs.τ v) w jj → IsLocIso jj →
    ∀ cc : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w), (Γ.W.bas v).val.map jj * cc.val = basCols B e w →
    ∃ g ∈ KO (Kw w) (Fin (spW G i j).rank),
      IsMixChart v.1 (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w)
        (fun u => chart jj (finCongr (rankW G t i j w)) (colsEq t e w) g (invT cc) (coX (Bs.τ v) (Γ.V.bas v) (Γ.W.bas v) u))
        (fun u => (xiAt w)⁻¹ • chart jj (finCongr (rankW G t i j w)) (colsEq t e w) (invT g) cc
          (coY D.sp.cm.sig Γ.V Γ.W (Bs.τ v) (Γ.V.bas v) (Γ.W.bas v) u))
        (Assignment.one.block _ _)ᶜ := by
  classical
  intro D T L sc G μ₀ hL W B t i j M e Bs Γ X om om' h hT hTi v w hw jj hjj _ cc hcc
  subst hw
  obtain rfl := eq_complEquiv _ hjj
  have hV := hT.geo.hV
  have hJT : IsHermND D.sp.cm.sig Γ.V.Jᵀ := ⟨fun i j => by simpa using hV.herm j i, by
    rw [Matrix.det_transpose]; exact GlobalTheory.HermSelfDualLoc.det_ne_zero_of_isHerm _ Bs hV⟩
  have hsd := GlobalTheory.HermSelfDualLoc.isSelfDualAt_transpose _ _ _ Bs _ Γ.V _ _ hT.base hV v
  have hb := hV.bas v
  rw [hTi.1] at hsd hb
  obtain ⟨g, hgK, hg⟩ := exists_rows (Bs.τ v) hJT hsd hb
    (isFrameAt_loc (B.isFrame_β hL (i := (i : ℕ) + 1) (j := (j : ℕ) + 1) i.2 j.2) (splitPrime (Bs.τ v)))
  have hJW : Γ.V.J = (spW G i j).gram := h.JW.trans (one_smul _ _)
  rw [hJW] at hg
  exact ⟨g, hgK, isMixChart_of B t i j e Γ (Bs.τ v) _ hjj (complMap_apply_emb _ _) hJW h.JWW cc hcc g hg⟩

end Main

end GlobalTheory.FlipMatch.RowChart

end
