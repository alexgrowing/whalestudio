import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeometricLemmaCellOneBlockSwapEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFunctorTorusCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRelParabColEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedRepSigmaApplyQuotientStatement
open GlobalTheory.PRep GlobalTheory.SmGL Matrix

noncomputable section

namespace GlobalTheory.CellDetFirst

open scoped TensorProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem inducing_mk (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (p : relParab k (colEq u v)) (w : ℂ ⊗[ℂ] ℂ) :
    sigmaC χ₁ χ₂ u v p (Submodule.Quotient.mk w) =
    (((χ₂ * absPow k ((v : ℂ) / 2)) (GeneralLinearGroup.det (p.1 true)) *
      deltaHalf k (Two (Fin u) (Fin v))
        (leviProj k (two (stdSum (rfl : u + v = u + v))) ⟨p.1 false, (mem_relParab_colEq _).1 p.2⟩) *
      (χ₁ (GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : u + v = u + v)))
          ⟨p.1 false, (mem_relParab_colEq _).1 p.2⟩ false)) *
        (χ₂ * absPow k (-(1 / 2))) (GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : u + v = u + v)))
          ⟨p.1 false, (mem_relParab_colEq _).1 p.2⟩ true))) : ℂˣ) : ℂ) • Submodule.Quotient.mk w :=
  GlobalTheory.T.induced_rep_sigma_apply_quotient χ₁ χ₂ u v p w

abbrev rhoL (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) :
    Representation ℂ (Levi k (Two (Fin u) (Fin v))) (ℂ ⊗[ℂ] ℂ) :=
  (extTensor (detRep (Fin u) χ₁) (detRep (Fin v) (χ₂ * absPow k (-(1 / 2))))).comp
    (leviTwo k (Fin u) (Fin v)).symm.toMonoidHom

def toFun (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ)
    (φ : IndSp (two (stdSum (rfl : u + v = u + v))) (rhoL (k := k) χ₁ χ₂ u v))
    (x : Levi k (Two (Fin (u + v)) (Fin 1))) :
    Jacquet (rhoM (k := k) χ₁ χ₂ u v) (relUnip k (rowEq u v)) :=
  (((χ₂ * absPow k ((v : ℂ) / 2)) (GeneralLinearGroup.det (x true)) : ℂˣ) : ℂ) •
    Submodule.Quotient.mk (φ.1.1 (x false))

theorem toFun_law (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ)
    (φ : IndSp (two (stdSum (rfl : u + v = u + v))) (rhoL (k := k) χ₁ χ₂ u v))
    (p : relParab k (colEq u v)) (x : Levi k (Two (Fin (u + v)) (Fin 1))) :
    toFun χ₁ χ₂ u v φ ((p : Levi k (Two (Fin (u + v)) (Fin 1))) * x) =
      sigmaC χ₁ χ₂ u v p (toFun χ₁ χ₂ u v φ x) := by
  have hq := (mem_relParab_colEq (p : Levi k (Two (Fin (u + v)) (Fin 1)))).1 p.2
  have h1 := parInd_law (two (stdSum (rfl : u + v = u + v))) (rhoL χ₁ χ₂ u v) φ ⟨_, hq⟩ (x false)
  have h2 : rhoL χ₁ χ₂ u v (leviProj k (two (stdSum (rfl : u + v = u + v))) ⟨_, hq⟩) (φ.1.1 (x false)) =
      ((χ₁ (GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : u + v = u + v))) ⟨_, hq⟩ false)) *
        (χ₂ * absPow k (-(1 / 2))) (GeneralLinearGroup.det
          (leviProj k (two (stdSum (rfl : u + v = u + v))) ⟨_, hq⟩ true)) : ℂˣ) : ℂ) • φ.1.1 (x false) :=
    GlobalTheory.IndLineGL.CellTorus.extTensor_detRep_apply χ₁ (χ₂ * absPow k (-(1 / 2))) _ _
  unfold toFun
  rw [map_smul, inducing_mk]
  show (((χ₂ * absPow k ((v : ℂ) / 2)) (GeneralLinearGroup.det (p.1 true * x true)) : ℂˣ) : ℂ) •
    Submodule.Quotient.mk (φ.1.1 (p.1 false * x false)) = _
  rw [h1, h2]
  rw [map_mul, map_mul, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul, smul_smul, smul_smul,
    smul_smul]
  congr 1
  simp only [Units.val_mul]
  ring

theorem toFun_smooth {χ₁ χ₂ : kˣ →* ℂˣ} (hχ₂ : IsSmoothChar χ₂) (u v : ℕ)
    (φ : IndSp (two (stdSum (rfl : u + v = u + v))) (rhoL (k := k) χ₁ χ₂ u v)) :
    (⟨toFun χ₁ χ₂ u v φ, fun p x => toFun_law χ₁ χ₂ u v φ p x⟩ :
      indSpace (relParab k (colEq u v)) (sigmaC χ₁ χ₂ u v)) ∈
        smoothPart (ind (relParab k (colEq u v)) (sigmaC χ₁ χ₂ u v)) := by
  have hc : IsSmoothChar (χ₂ * absPow k ((v : ℂ) / 2)) :=
    hχ₂.mul (isSmoothChar_of_isUnram (isUnram_absPow k _))
  have hd := (hc.detChar (n := Fin 1)).comp
    (Pi.evalMonoidHom (fun j => GL (Two (Fin (u + v)) (Fin 1) j) k) true) (continuous_apply true)
  have hφ : IsOpen {g : GL (Fin (u + v)) k | ind _ _ g φ.1 = φ.1} := φ.2
  refine mem_smoothPart_of_nhds (Filter.mem_of_superset
    (((hφ.preimage (continuous_apply false)).inter hd).mem_nhds ⟨by simp, by simp⟩) ?_)
  rintro y ⟨hy1, hy2⟩
  have hy2' : (χ₂ * absPow k ((v : ℂ) / 2)) (GeneralLinearGroup.det (y true)) = 1 := MonoidHom.mem_ker.1 hy2
  refine Subtype.ext (funext fun x => ?_)
  show toFun χ₁ χ₂ u v φ (x * y) = toFun χ₁ χ₂ u v φ x
  have h3 : φ.1.1 (x false * y false) = φ.1.1 (x false) :=
    congrArg (fun F => F.1 (x false)) (show ind _ _ (y false) φ.1 = φ.1 from hy1)
  unfold toFun
  rw [Pi.mul_apply, Pi.mul_apply, h3, map_mul, map_mul, hy2', mul_one]

def toCell {χ₁ χ₂ : kˣ →* ℂˣ} (hχ₂ : IsSmoothChar χ₂) (u v : ℕ) :
    IndSp (two (stdSum (rfl : u + v = u + v))) (rhoL (k := k) χ₁ χ₂ u v) →ₗ[ℂ]
      smoothPart (ind (relParab k (colEq u v)) (sigmaC (k := k) χ₁ χ₂ u v)) where
  toFun φ := ⟨⟨toFun χ₁ χ₂ u v φ, fun p x => toFun_law χ₁ χ₂ u v φ p x⟩, toFun_smooth hχ₂ u v φ⟩
  map_add' φ ψ := Subtype.ext (Subtype.ext (funext fun x => by
    show toFun χ₁ χ₂ u v (φ + ψ) x = toFun χ₁ χ₂ u v φ x + toFun χ₁ χ₂ u v ψ x
    simp only [toFun]
    rw [← smul_add, ← Submodule.Quotient.mk_add]
    rfl))
  map_smul' c φ := Subtype.ext (Subtype.ext (funext fun x => by
    show toFun χ₁ χ₂ u v (c • φ) x = c • toFun χ₁ χ₂ u v φ x
    simp only [toFun]
    rw [smul_comm, ← Submodule.Quotient.mk_smul]
    rfl))

theorem toCell_apply {χ₁ χ₂ : kˣ →* ℂˣ} (hχ₂ : IsSmoothChar χ₂) (u v : ℕ)
    (φ : IndSp (two (stdSum (rfl : u + v = u + v))) (rhoL (k := k) χ₁ χ₂ u v)) (x) :
    (toCell hχ₂ u v φ).1.1 x = toFun χ₁ χ₂ u v φ x := rfl

theorem toCell_injective {χ₁ χ₂ : kˣ →* ℂˣ} (hχ₂ : IsSmoothChar χ₂) (u v : ℕ) :
    Function.Injective (toCell (k := k) (χ₁ := χ₁) hχ₂ u v) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro φ hφ
  refine Subtype.ext (Subtype.ext (funext fun x₁ => ?_))
  have h := congrArg (fun F => F.1.1 (leviTwo k (Fin (u + v)) (Fin 1) (x₁, 1))) hφ
  simp only [toCell_apply] at h
  have h' : (Submodule.Quotient.mk (φ.1.1 x₁) :
      Jacquet (rhoM (k := k) χ₁ χ₂ u v) (relUnip k (rowEq u v))) = 0 := by
    have e : toFun χ₁ χ₂ u v φ (leviTwo k (Fin (u + v)) (Fin 1) (x₁, 1)) =
        Submodule.Quotient.mk (φ.1.1 x₁) := by
      unfold toFun
      show ((((χ₂ * absPow k ((v : ℂ) / 2)) (GeneralLinearGroup.det (1 : GL (Fin 1) k)) : ℂˣ) : ℂ) • _) = _
      rw [map_one, map_one, Units.val_one, one_smul]
      rfl
    rw [← e]
    exact h
  rw [Submodule.Quotient.mk_eq_zero, twKer_rhoM, Submodule.mem_bot] at h'
  exact h'

abbrev CellSp (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) : Type :=
  smoothPart (ind (relParab k (colEq u v)) (sigmaC (k := k) χ₁ χ₂ u v))

def incl (u v : ℕ) : GL (Fin (u + v)) k →* Levi k (Two (Fin (u + v)) (Fin 1)) :=
  (leviTwo k (Fin (u + v)) (Fin 1)).toMonoidHom.comp (MonoidHom.inl _ _)

theorem incl_false (u v : ℕ) (x₁ : GL (Fin (u + v)) k) : incl u v x₁ false = x₁ := rfl

theorem incl_true (u v : ℕ) (x₁ : GL (Fin (u + v)) k) : incl u v x₁ true = 1 := rfl

def restr (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (Φ : CellSp (k := k) χ₁ χ₂ u v) (x₁ : GL (Fin (u + v)) k) :
    ℂ ⊗[ℂ] ℂ :=
  Submodule.quotEquivOfEqBot _ (twKer_rhoM (k := k) χ₁ χ₂ u v) (Φ.1.1 (incl u v x₁))

theorem mk_restr (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (Φ : CellSp (k := k) χ₁ χ₂ u v) (x₁ : GL (Fin (u + v)) k) :
    (Submodule.Quotient.mk (restr χ₁ χ₂ u v Φ x₁) :
      Jacquet (rhoM (k := k) χ₁ χ₂ u v) (relUnip k (rowEq u v))) = Φ.1.1 (incl u v x₁) :=
  (Submodule.quotEquivOfEqBot _ (twKer_rhoM (k := k) χ₁ χ₂ u v)).symm_apply_apply _

theorem restr_law (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (Φ : CellSp (k := k) χ₁ χ₂ u v)
    (q : parab k (two (stdSum (rfl : u + v = u + v)))) (x₁ : GL (Fin (u + v)) k) :
    restr χ₁ χ₂ u v Φ ((q : GL (Fin (u + v)) k) * x₁) =
      ((twist (rhoL (k := k) χ₁ χ₂ u v) (deltaHalf k (Two (Fin u) (Fin v)))).comp
        (leviProj k (two (stdSum (rfl : u + v = u + v))))) q (restr χ₁ χ₂ u v Φ x₁) := by
  have hmem : incl u v (q : GL (Fin (u + v)) k) ∈ relParab k (colEq u v) := (mem_relParab_colEq _).2 q.2
  have h1 : Φ.1.1 (incl u v (q : GL (Fin (u + v)) k) * incl u v x₁) =
      sigmaC χ₁ χ₂ u v ⟨_, hmem⟩ (Φ.1.1 (incl u v x₁)) := Φ.1.2 ⟨_, hmem⟩ (incl u v x₁)
  have h2 : rhoL χ₁ χ₂ u v (leviProj k (two (stdSum (rfl : u + v = u + v))) q) (restr χ₁ χ₂ u v Φ x₁) =
      ((χ₁ (GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : u + v = u + v))) q false)) *
        (χ₂ * absPow k (-(1 / 2))) (GeneralLinearGroup.det
          (leviProj k (two (stdSum (rfl : u + v = u + v))) q true)) : ℂˣ) : ℂ) • restr χ₁ χ₂ u v Φ x₁ :=
    GlobalTheory.IndLineGL.CellTorus.extTensor_detRep_apply χ₁ (χ₂ * absPow k (-(1 / 2))) _ _
  rw [MonoidHom.comp_apply, twist_apply, h2, smul_smul]
  unfold restr
  rw [map_mul, h1, ← mk_restr χ₁ χ₂ u v Φ x₁, inducing_mk, map_smul]
  unfold restr
  rw [Submodule.quotEquivOfEqBot_apply_mk]
  congr 1
  simp only [Subtype.coe_mk, incl_true, incl_false, Subtype.coe_eta, map_one, one_mul, Units.val_mul]

theorem restr_smooth (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (Φ : CellSp (k := k) χ₁ χ₂ u v) :
    (⟨restr χ₁ χ₂ u v Φ, fun q x₁ => restr_law χ₁ χ₂ u v Φ q x₁⟩ :
      indSpace (parab k (two (stdSum (rfl : u + v = u + v))))
        ((twist (rhoL (k := k) χ₁ χ₂ u v) (deltaHalf k (Two (Fin u) (Fin v)))).comp
          (leviProj k (two (stdSum (rfl : u + v = u + v)))))) ∈ smoothPart (ind _ _) := by
  have hΦ : IsOpen {y : Levi k (Two (Fin (u + v)) (Fin 1)) |
      ind (relParab k (colEq u v)) (sigmaC χ₁ χ₂ u v) y Φ.1 = Φ.1} := Φ.2
  have hcont : Continuous (incl (k := k) u v) :=
    (continuous_leviTwo k).comp (continuous_id.prodMk continuous_const)
  refine mem_smoothPart_of_nhds (Filter.mem_of_superset ((hΦ.preimage hcont).mem_nhds ?_) ?_)
  · show ind (relParab k (colEq u v)) (sigmaC χ₁ χ₂ u v) (incl u v 1) Φ.1 = Φ.1
    refine Subtype.ext (funext fun y => ?_)
    show Φ.1.1 (y * incl u v 1) = Φ.1.1 y
    rw [map_one, mul_one]
  · intro g₁ hg
    refine Subtype.ext (funext fun x₁ => ?_)
    show restr χ₁ χ₂ u v Φ (x₁ * g₁) = restr χ₁ χ₂ u v Φ x₁
    have h := congrArg (fun F => F.1 (incl u v x₁))
      (show ind (relParab k (colEq u v)) (sigmaC χ₁ χ₂ u v) (incl u v g₁) Φ.1 = Φ.1 from hg)
    have h' : Φ.1.1 (incl u v (x₁ * g₁)) = Φ.1.1 (incl u v x₁) :=
      (congrArg (fun y => Φ.1.1 y) (map_mul (incl (k := k) u v) x₁ g₁)).trans h
    unfold restr
    exact congrArg _ h'

theorem toCell_surjective {χ₁ χ₂ : kˣ →* ℂˣ} (hχ₂ : IsSmoothChar χ₂) (u v : ℕ) :
    Function.Surjective (toCell (k := k) (χ₁ := χ₁) hχ₂ u v) := by
  intro Φ
  refine ⟨⟨⟨restr χ₁ χ₂ u v Φ, fun q x₁ => restr_law χ₁ χ₂ u v Φ q x₁⟩, restr_smooth χ₁ χ₂ u v Φ⟩,
    Subtype.ext (Subtype.ext (funext fun x => ?_))⟩
  show toFun χ₁ χ₂ u v _ x = Φ.1.1 x
  have hx : x = leviTwo k (Fin (u + v)) (Fin 1) (1, x true) * incl u v (x false) := by
    funext j
    cases j
    · exact (one_mul (x false)).symm
    · exact (mul_one (x true)).symm
  have hp : leviTwo k (Fin (u + v)) (Fin 1) (1, x true) ∈ relParab k (colEq u v) :=
    (mem_relParab_colEq _).2 (one_mem _)
  have h1 : Φ.1.1 (leviTwo k (Fin (u + v)) (Fin 1) (1, x true) * incl u v (x false)) =
      sigmaC χ₁ χ₂ u v ⟨_, hp⟩ (Φ.1.1 (incl u v (x false))) := Φ.1.2 ⟨_, hp⟩ _
  have hl : leviProj k (two (stdSum (rfl : u + v = u + v)))
      ⟨(leviTwo k (Fin (u + v)) (Fin 1) (1, x true)) false, (mem_relParab_colEq _).1 hp⟩ = 1 :=
    map_one (leviProj k (two (stdSum (rfl : u + v = u + v))))
  conv_rhs => rw [hx, h1, ← mk_restr χ₁ χ₂ u v Φ (x false), inducing_mk]
  unfold toFun
  rw [hl]
  simp only [map_one, Pi.one_apply, Units.val_one, mul_one]
  rfl

def mapF {χ₁ χ₂ : kˣ →* ℂˣ} (hχ₂ : IsSmoothChar χ₂) (u v : ℕ) :
    (extTensor (prod₂ (detRep (Fin u) χ₁) (detRep (Fin v) (χ₂ * absPow k (-(1 / 2)))))
      (detRep (Fin 1) (χ₂ * absPow k ((v : ℂ) / 2)))).IntertwiningMap
    ((cellFunctor (rowEq u v) (colEq u v) (rhoM (k := k) χ₁ χ₂ u v)).comp
      (leviTwo k (Fin (u + v)) (Fin 1)).toMonoidHom) where
  toLinearMap := (toCell hχ₂ u v).comp (TensorProduct.rid ℂ _).toLinearMap
  isIntertwining' g := TensorProduct.ext' fun φ c => Subtype.ext (Subtype.ext (funext fun x => by
    show toFun χ₁ χ₂ u v (TensorProduct.rid ℂ _ (extTensor _ _ g (φ ⊗ₜ c))) x =
      toFun χ₁ χ₂ u v (TensorProduct.rid ℂ _ (φ ⊗ₜ c)) (x * leviTwo k (Fin (u + v)) (Fin 1) g)
    rw [extTensor_tmul, TensorProduct.rid_tmul, TensorProduct.rid_tmul]
    unfold toFun
    show (((χ₂ * absPow k ((v : ℂ) / 2)) (GeneralLinearGroup.det (x true)) : ℂˣ) : ℂ) •
        Submodule.Quotient.mk ((detRep (Fin 1) (χ₂ * absPow k ((v : ℂ) / 2)) g.2 c) • φ.1.1 (x false * g.1)) =
      (((χ₂ * absPow k ((v : ℂ) / 2)) (GeneralLinearGroup.det (x true * g.2)) : ℂˣ) : ℂ) •
        Submodule.Quotient.mk (c • φ.1.1 (x false * g.1))
    rw [detRep, ofChar_apply, detChar_apply, map_mul GeneralLinearGroup.det (x true) g.2,
      map_mul (χ₂ * absPow k ((v : ℂ) / 2)), Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul,
      smul_smul, smul_smul, Units.val_mul]
    congr 1
    ring))

theorem mapF_bijective {χ₁ χ₂ : kˣ →* ℂˣ} (hχ₂ : IsSmoothChar χ₂) (u v : ℕ) :
    Function.Bijective (mapF (k := k) (χ₁ := χ₁) hχ₂ u v) :=
  ⟨(toCell_injective hχ₂ u v).comp (TensorProduct.rid ℂ _).injective,
    (toCell_surjective hχ₂ u v).comp (TensorProduct.rid ℂ _).surjective⟩

theorem main : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → ∀ (u v : ℕ)
    (b : SizeMatrix (Two (Fin u) (Fin (v + 1))) (Two (Fin (u + v)) (Fin 1))), b.1 false true = 0 →
    ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin u) (Fin (v + 1)) i)
      (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Two (Fin (u + v)) (Fin 1) j),
      Nonempty (Representation.Equiv ((cellFunctor f g ((extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)).comp
          (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom)).comp
            (leviTwo k (Fin (u + v)) (Fin 1)).toMonoidHom)
        (extTensor (prod₂ (detRep (Fin u) χ₁) (detRep (Fin v) (χ₂ * absPow k (-(1 / 2)))))
          (detRep (Fin 1) (χ₂ * absPow k ((v : ℂ) / 2))))) := by
  intro k _ _ _ _ χ₁ χ₂ _ h₂ u v b hb
  have e := eq_sizeFirst b hb
  subst e
  exact ⟨rowEq u v, colEq u v, ⟨(LocGL.equivOfBijective (mapF h₂ u v) (mapF_bijective h₂ u v)).symm⟩⟩

end GlobalTheory.CellDetFirst
