import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalAddCharUnramifiedOfSplitsCompletelyAbovePla
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoAtEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeHermitianSkewStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.LinBarCoords

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.EmbChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compFin_algebraMap (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (u : AF F) :
    compFin F E v (algebraMap (AF F) (AE F E) u) = algebraMap (Fv F v) (Fv F v ⊗[F] E) (evFin F v u) := rfl

theorem at_tensAt (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (y : Fv F v ⊗[F] E) : At (evFin F v) (tensAt E v y) := by
  intro u hu
  rw [Algebra.smul_def, mul_comm, tensAt_mul_right, compFin_algebraMap, hu, map_zero, mul_zero, map_zero]

theorem eq_tensAt_of_at (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {z : AE F E} (hz : At (evFin F v) z) :
    z = tensAt E v (compFin F E v z) := by
  have h1 : (1 - atPlace v 1) • z = 0 := hz _ (by rw [map_sub, map_one, evFin_atPlace, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  conv_lhs => rw [h1]
  rw [Algebra.smul_def, show algebraMap (AF F) (AE F E) (atPlace v 1) = tensAt E v 1 from rfl, tensAt_mul_right, one_mul]

theorem piW_tensAt (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (t : E →ₐ[F] Fv F v) (y : Fv F v ⊗[F] E) : piW t (tensAt E v y) = splitProj t y := by
  show splitProj t (compFin F E v (tensAt E v y)) = _
  rw [compFin_tensAt]

end GlobalTheory.LinBarCoords

namespace GlobalTheory.LinBarCoords

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.EmbChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_matrix {m n : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {x : Matrix m n (AE F E)} :
    At (evFin F v) x ↔ ∀ i j, At (evFin F v) (x i j) := by
  constructor
  · intro h i j u hu
    have := congrFun (congrFun (h u hu) i) j
    simpa using this
  · intro h u hu
    ext i j
    simpa using h i j u hu

def liftM (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {m n : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (t : E →ₐ[F] Fv F v) :
    Matrix m n (Fv F v) × Matrix m n (Fv F v) →+ Matrix m n (AE F E) :=
  AddMonoidHom.mk' (fun p => Matrix.of fun i j => tensAt E v ((splitAlgEquiv hcm t).symm (p.1 i j, p.2 i j)))
    (fun p q => by ext i j; simp only [Prod.fst_add, Prod.snd_add, Matrix.add_apply, Matrix.of_apply, ← Prod.mk_add_mk, map_add])

theorem liftM_at (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {m n : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (t : E →ₐ[F] Fv F v)
    (p : Matrix m n (Fv F v) × Matrix m n (Fv F v)) : At (evFin F v) (liftM σ hcm v t p) :=
  (at_matrix v).2 fun _ _ => at_tensAt v _

theorem liftM_fst (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {m n : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (t : E →ₐ[F] Fv F v)
    (p : Matrix m n (Fv F v) × Matrix m n (Fv F v)) : (liftM σ hcm v t p).map (piW t) = p.1 := by
  ext i j
  simp [liftM, piW_tensAt]

theorem liftM_snd (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {m n : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (t : E →ₐ[F] Fv F v)
    (p : Matrix m n (Fv F v) × Matrix m n (Fv F v)) : (liftM σ hcm v t p).map (piW (t.comp σ)) = p.2 := by
  ext i j
  simp [liftM, piW_tensAt]

theorem eq_zero_of_at (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {m n : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (t : E →ₐ[F] Fv F v)
    {x : Matrix m n (AE F E)} (hx : At (evFin F v) x) (h1 : x.map (piW t) = 0) (h2 : x.map (piW (t.comp σ)) = 0) :
    x = 0 := by
  ext i j
  rw [eq_tensAt_of_at v ((at_matrix v).1 hx i j)]
  have e : compFin F E v (x i j) = 0 := split_ext hcm t (by rw [map_zero]; exact (by simpa using congrFun (congrFun h1 i) j : piW t (x i j) = 0))
    (by rw [map_zero]; exact (by simpa using congrFun (congrFun h2 i) j : piW (t.comp σ) (x i j) = 0))
  rw [e, map_zero]; rfl

end GlobalTheory.LinBarCoords

namespace GlobalTheory.LinBarCoords
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem det_ne_zero_of_hasSig {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  set A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm with hA'
  have key : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA, hA', Matrix.transpose_submatrix,
      Matrix.submatrix_mul (Aᵀ * M) (A.map star) e.symm id e.symm Function.bijective_id,
      Matrix.submatrix_mul Aᵀ M e.symm id id Function.bijective_id, Matrix.submatrix_id_id, Matrix.submatrix_map]
  have hd := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg,
    Matrix.det_one, mul_one, Matrix.det_mul, Matrix.det_mul] at hd
  intro h0
  rw [h0, mul_zero, zero_mul] at hd
  exact (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hd.symm

theorem det_map_isUnit : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (c : ℂ) (r s : ℕ), c ≠ 0 → (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (c • J.map (B.emb w).1) r s) →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (t : E →ₐ[F] Fv F v), IsUnit (J.map t).det := by
  intro F E _ _ _ _ _ B n J c r s hc hs v t
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  have h1 := det_ne_zero_of_hasSig (hs (NumberField.InfinitePlace.mk φ))
  have e1 : (J.map (B.emb (NumberField.InfinitePlace.mk φ)).1).det = (B.emb (NumberField.InfinitePlace.mk φ)).1 J.det :=
    (RingHom.map_det _ J).symm
  rw [Matrix.det_smul, e1] at h1
  have hJ : J.det ≠ 0 := fun h0 => h1 (by rw [h0, map_zero, mul_zero])
  have e2 : (J.map t).det = t J.det := (RingHom.map_det (t : E →+* Fv F v) J).symm
  rw [isUnit_iff_ne_zero, e2]
  exact (map_ne_zero_iff _ (t : E →+* Fv F v).injective).2 hJ

end GlobalTheory.LinBarCoords

namespace GlobalTheory.LinBarCoords
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.EmbChart

theorem exists_split_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (t : E →ₐ[F] Fv F v),
    ∃ uT uM : Matrix (Fin a') (Fin (a + a')) (Fv F v) →+ Matrix (Fin a') (Fin (a + a')) (AE F E),
      (∀ Y, At (evFin F v) (uT Y) ∧ (uT Y).map (piW t) = 0 ∧ GlobalTheory.LinBarAt.coAt G t (uT Y) = Y) ∧
      (∀ z, At (evFin F v) (uM z) ∧ (uM z).map (piW (t.comp σ)) = 0 ∧ (uM z).map (piW t) = -z) ∧
      (∀ u, At (evFin F v) u → ∃ Y z, u = uT Y + uM z) ∧
      (∀ x u, At (evFin F v) x → At (evFin F v) u →
        evFin F v (symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) x u) =
          ∑ i, ∑ j, (x.map (piW t)) i j * GlobalTheory.LinBarAt.coAt G t u i j -
            ∑ i, ∑ j, GlobalTheory.LinBarAt.coAt G t x i j * (u.map (piW t)) i j) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v t
  have hcm := hTr.base.cm
  have hP : IsUnit (G.V'.J.map t).det := det_map_isUnit B G.V'.J 1 _ _ one_ne_zero (fun w => by rw [one_smul]; exact hTr.geo.hV'.sig w) v t
  have hQ : IsUnit ((G.W.J.map t)ᵀ).det := by
    rw [Matrix.det_transpose]; exact det_map_isUnit B G.W.J Complex.I _ _ Complex.I_ne_zero hTr.geo.hW.sig v t
  set P := G.V'.J.map t with hPdef
  set Q := (G.W.J.map t)ᵀ with hQdef
  let L := liftM σ hcm (m := Fin a') (n := Fin (a + a')) v t
  let uT : Matrix (Fin a') (Fin (a + a')) (Fv F v) →+ Matrix (Fin a') (Fin (a + a')) (AE F E) :=
    AddMonoidHom.mk' (fun Y => L (0, -(P⁻¹ * Y * Q⁻¹))) (fun Y Y' => by
      rw [Matrix.mul_add, Matrix.add_mul, neg_add, ← map_add, Prod.mk_add_mk, add_zero])
  let uM : Matrix (Fin a') (Fin (a + a')) (Fv F v) →+ Matrix (Fin a') (Fin (a + a')) (AE F E) :=
    AddMonoidHom.mk' (fun z => L (-z, 0)) (fun z z' => by rw [neg_add, ← map_add, Prod.mk_add_mk, add_zero])
  have hco : ∀ u, GlobalTheory.LinBarAt.coAt G t u = -(P * u.map (piW (t.comp σ)) * Q) := fun u => by
    simp [GlobalTheory.LinBarAt.coAt, hPdef, hQdef]
  have hTc : ∀ Y, (uT Y).map (piW (t.comp σ)) = -(P⁻¹ * Y * Q⁻¹) := fun Y => liftM_snd σ hcm v t _
  have hTt : ∀ Y, (uT Y).map (piW t) = 0 := fun Y => liftM_fst σ hcm v t _
  have hMc : ∀ z, (uM z).map (piW (t.comp σ)) = 0 := fun z => liftM_snd σ hcm v t _
  have hMt : ∀ z, (uM z).map (piW t) = -z := fun z => liftM_fst σ hcm v t _
  have hTa : ∀ Y, At (evFin F v) (uT Y) := fun Y => liftM_at σ hcm v t _
  have hMa : ∀ z, At (evFin F v) (uM z) := fun z => liftM_at σ hcm v t _
  refine ⟨uT, uM, fun Y => ⟨hTa Y, hTt Y, ?_⟩, fun z => ⟨hMa z, hMc z, hMt z⟩, fun u hu => ?_, fun x u hx hu => ?_⟩
  · have e1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hP
    have e2 : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ hQ
    rw [hco, hTc, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    simp only [← Matrix.mul_assoc, e1, Matrix.one_mul]
    simp only [Matrix.mul_assoc, e2, Matrix.mul_one]
  · refine ⟨GlobalTheory.LinBarAt.coAt G t u, -(u.map (piW t)), ?_⟩
    have hd : At (evFin F v) (u - (uT (GlobalTheory.LinBarAt.coAt G t u) + uM (-(u.map (piW t))))) := by
      intro c hc
      rw [smul_sub, smul_add, hu c hc, hTa _ c hc, hMa _ c hc, add_zero, sub_zero]
    refine (sub_eq_zero.1 (eq_zero_of_at σ hcm v t hd ?_ ?_))
    · rw [Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _), hTt, hMt, neg_neg, zero_add, sub_self]
    · rw [Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _), hTc, hMc, add_zero, hco, Matrix.mul_neg, Matrix.neg_mul, neg_neg,
        Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ, Matrix.mul_one, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hP, Matrix.one_mul, sub_self]
  · rw [GlobalTheory.T.local_lattice_hermitian_skew hcm v t G.V'.J G.W.J hTr.geo.hV'.herm hTr.geo.hW.skew x u hx, hco, hco]

end GlobalTheory.LinBarCoords
