import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubSmulMemOfEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockRepEquivFirst
open GlobalTheory.PRep GlobalTheory.SmGL Matrix

noncomputable section
namespace GlobalTheory.CellFirstDet
open DetProdCells
open scoped TensorProduct

def colTrueSigma (u v : ℕ) : (Σ i, Fin ((cellFirst u v).1 i true)) ≃ (Σ x, Two (Fin u) (Fin v) x) :=
  Equiv.sigmaCongrRight fun i => match i with
    | false => Equiv.refl _
    | true => Equiv.refl _

def cols (u v : ℕ) : ∀ j, (Σ i, Fin ((cellFirst u v).1 i j)) ≃ Two (Fin 1) (Fin (u + v)) j
  | false => (cellFirst u v).nonempty_cols.some false
  | true => (colTrueSigma u v).trans (two (stdSum rfl))

def what₂ (u v : ℕ) : ∀ i, (Σ j, Fin ((cellFirst u v).1 i j)) ≃ Two (Fin (u + 1)) (Fin v) i :=
  (cellFirst u v).nonempty_rows.some

theorem modExp_bool (m : Bool → Type) [∀ a, Fintype (m a)] :
    modExp m false = Fintype.card (m true) ∧ modExp m true = -Fintype.card (m false) := by
  constructor <;> simp [modExp, Finset.sum_filter, Fintype.sum_bool]

theorem card_b (u v : ℕ) (i j : Bool) : Fintype.card (Fin ((cellFirst u v).1 i j)) = (cellFirst u v).1 i j :=
  Fintype.card_fin _

theorem modExp_rowF (u v : ℕ) : modExp (fun j => Fin ((cellFirst u v).1 false j)) false = u ∧
    modExp (fun j => Fin ((cellFirst u v).1 false j)) true = -1 := by
  obtain ⟨h1, h2⟩ := modExp_bool (fun j => Fin ((cellFirst u v).1 false j))
  exact ⟨h1.trans (by rw [card_b]; rfl), h2.trans (by rw [card_b]; rfl)⟩

theorem modExp_colT (u v : ℕ) : modExp (fun i => Fin ((cellFirst u v).1 i true)) false = v ∧
    modExp (fun i => Fin ((cellFirst u v).1 i true)) true = -u := by
  obtain ⟨h1, h2⟩ := modExp_bool (fun i => Fin ((cellFirst u v).1 i true))
  exact ⟨h1.trans (by rw [card_b]; rfl), h2.trans (by rw [card_b]; rfl)⟩

theorem modExp_two (u v : ℕ) : modExp (Two (Fin u) (Fin v)) false = v ∧
    modExp (Two (Fin u) (Fin v)) true = -u := by
  constructor <;> simp [modExp, Finset.sum_filter, Fintype.sum_bool]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_eq_one_of_card {n : ℕ} (h : n = 0) (g : GL (Fin n) k) : GeneralLinearGroup.det g = 1 := by
  subst h
  ext
  simp [Matrix.det_isEmpty]

theorem extTensor_detRep_apply {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (χ ψ : kˣ →* ℂˣ) (g : GL a k × GL b k) (w : ℂ ⊗[ℂ] ℂ) :
    extTensor (detRep a χ) (detRep b ψ) g w =
      ((χ (GeneralLinearGroup.det g.1) * ψ (GeneralLinearGroup.det g.2) : ℂˣ) : ℂ) • w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [extTensor_tmul]
    simp only [detRep, ofChar_apply, detChar_apply, Units.val_mul]
    rw [← smul_eq_mul, ← smul_eq_mul, TensorProduct.smul_tmul', TensorProduct.tmul_smul, ← TensorProduct.smul_tmul',
      smul_smul, mul_comm]
    exact TensorProduct.smul_tmul' _ _ _
  | add x y hx hy => rw [map_add, hx, hy, smul_add]

variable (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ)

abbrev detPair : Representation ℂ (Levi k (Two (Fin (u + 1)) (Fin v))) (ℂ ⊗[ℂ] ℂ) :=
  (extTensor (detRep (Fin (u + 1)) χ₁) (detRep (Fin v) χ₂)).comp
    (leviTwo k (Fin (u + 1)) (Fin v)).symm.toMonoidHom

theorem detPair_apply (g : Levi k (Two (Fin (u + 1)) (Fin v))) (w : ℂ ⊗[ℂ] ℂ) :
    detPair χ₁ χ₂ u v g w =
      ((χ₁ (GeneralLinearGroup.det (g false)) * χ₂ (GeneralLinearGroup.det (g true)) : ℂˣ) : ℂ) • w :=
  extTensor_detRep_apply χ₁ χ₂ _ w

theorem twKer_detPair : twKer (detPair χ₁ χ₂ u v) (relUnip k (what₂ u v)) 1 = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨n, w, rfl⟩
  have h : ∀ i, GeneralLinearGroup.det ((n : Levi k (Two (Fin (u + 1)) (Fin v))) i) = 1 := fun i =>
    det_eq_one_of_mem_unipRad k (n.2 i trivial)
  rw [detPair_apply, h, h]
  simp

abbrev cellRep := (twist ((relJac (what₂ u v) (detPair χ₁ χ₂ u v)).comp
    (swapBlocks k (fun i j => Fin ((cellFirst u v).1 i j))))
      (relDeltaHalf k (fun j i => Fin ((cellFirst u v).1 i j)))).comp (relProj k (cols u v))

abbrev ltwo (p : relParab k (cols u v)) : Levi k (Two (Fin u) (Fin v)) :=
  leviProj k (two (stdSum (rfl : u + v = u + v))) ⟨p.1 true, p.2 true trivial⟩

def kappa (p : relParab k (cols u v)) : ℂˣ :=
  (χ₁ * absPow k (-(u : ℂ) / 2)) (GeneralLinearGroup.det (p.1 false)) *
    deltaHalf k (Two (Fin u) (Fin v)) (ltwo u v p) *
      ((χ₁ * absPow k (1 / 2)) (GeneralLinearGroup.det (ltwo u v p false)) *
        χ₂ (GeneralLinearGroup.det (ltwo u v p true)))

theorem cellRep_apply (p : relParab k (cols u v)) (w : Jacquet (detPair χ₁ χ₂ u v) (relUnip k (what₂ u v))) :
    cellRep χ₁ χ₂ u v p w = (kappa χ₁ χ₂ u v p : ℂ) • w := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  simp only [cellRep, MonoidHom.comp_apply, twist_apply]
  rw [relJac_mk, detPair_apply, Submodule.Quotient.mk_smul, smul_smul, smul_smul]
  congr 1
  rw [← Units.val_mul, ← Units.val_mul]
  congr 1
  have hdet : ∀ i, GeneralLinearGroup.det (relEmb k (what₂ u v)
      (swapBlocks k (fun i j => Fin ((cellFirst u v).1 i j)) (relProj k (cols u v) p)) i) =
        GeneralLinearGroup.det (relProj k (cols u v) p true i) *
          GeneralLinearGroup.det (relProj k (cols u v) p false i) := fun i => by
    rw [relEmb_apply, det_leviEmb, Fintype.prod_bool]
    rfl
  have h0 : GeneralLinearGroup.det (relProj k (cols u v) p false true) = 1 := det_eq_one_of_card rfl _
  have hpf : GeneralLinearGroup.det (p.1 false) = GeneralLinearGroup.det (relProj k (cols u v) p false false) := by
    have := det_parab k (cols u v false) ⟨p.1 false, p.2 false trivial⟩
    rw [Fintype.prod_bool] at this
    refine this.trans ?_
    show GeneralLinearGroup.det (relProj k (cols u v) p false true) * _ = _
    rw [h0, one_mul]
    rfl
  have hrowT : deltaHalf k (fun j => Fin ((cellFirst u v).1 true j))
      (swapBlocks k (fun i j => Fin ((cellFirst u v).1 i j)) (relProj k (cols u v) p) true) = 1 :=
    OneBlockCell.deltaHalf_eq_one_of_single (n := fun j => (cellFirst u v).1 true j) true
      (fun j hj => by cases j; rfl; exact absurd rfl hj) _
  have hcolF : deltaHalf k (fun i => Fin ((cellFirst u v).1 i false)) (relProj k (cols u v) p false) = 1 :=
    OneBlockCell.deltaHalf_eq_one_of_single (n := fun i => (cellFirst u v).1 i false) false
      (fun i hi => by cases i; exact absurd rfl hi; rfl) _
  rw [relDeltaHalf_apply, relDeltaHalf_apply, Fintype.prod_bool, Fintype.prod_bool, hrowT, hcolF, hdet, hdet, h0,
    deltaHalf_apply, deltaHalf_apply, Fintype.prod_bool, Fintype.prod_bool, (modExp_rowF u v).1, (modExp_rowF u v).2,
    (modExp_colT u v).1, (modExp_colT u v).2]
  simp only [kappa, hpf, deltaHalf_apply, Fintype.prod_bool, (modExp_two u v).1, (modExp_two u v).2]
  have hB : GeneralLinearGroup.det (ltwo u v p false) = GeneralLinearGroup.det (relProj k (cols u v) p true false) := rfl
  have hC : GeneralLinearGroup.det (ltwo u v p true) = GeneralLinearGroup.det (relProj k (cols u v) p true true) := rfl
  have hs1 : GeneralLinearGroup.det ((swapBlocks k fun i j ↦ Fin ((cellFirst u v).1 i j)) (relProj k (cols u v) p) false true) =
    GeneralLinearGroup.det (relProj k (cols u v) p true false) := rfl
  have hs2 : GeneralLinearGroup.det ((swapBlocks k fun i j ↦ Fin ((cellFirst u v).1 i j)) (relProj k (cols u v) p) false false) =
    GeneralLinearGroup.det (relProj k (cols u v) p false false) := rfl
  rw [hB, hC, hs1, hs2]
  generalize GeneralLinearGroup.det (relProj k (cols u v) p false false) = A
  generalize GeneralLinearGroup.det (relProj k (cols u v) p true false) = B
  generalize GeneralLinearGroup.det (relProj k (cols u v) p true true) = C
  simp only [MonoidHom.mul_apply, map_mul, mul_one, one_mul, Int.cast_neg, Int.cast_natCast, Int.cast_one, neg_div,
    absPow_neg, MonoidHom.inv_apply]
  apply Units.ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, _root_.mul_inv_rev, inv_inv]
  ring

abbrev rho2 : Representation ℂ (Levi k (Two (Fin u) (Fin v))) (ℂ ⊗[ℂ] ℂ) :=
  (extTensor (detRep (Fin u) (χ₁ * absPow k (1 / 2))) (detRep (Fin v) χ₂)).comp
    (leviTwo k (Fin u) (Fin v)).symm.toMonoidHom

abbrev theta : Jacquet (detPair χ₁ χ₂ u v) (relUnip k (what₂ u v)) ≃ₗ[ℂ] ℂ ⊗[ℂ] ℂ :=
  Submodule.quotEquivOfEqBot _ (twKer_detPair χ₁ χ₂ u v)

theorem mem_relParab_left (a : GL (Fin 1) k) :
    leviTwo k (Fin 1) (Fin (u + v)) (a, 1) ∈ relParab k (cols u v) := by
  intro j _
  cases j
  · exact DiagCell.mem_parab_of_single (n := fun i => (cellFirst u v).1 i false) (cols u v false) false
      (fun i hi => by cases i; exact absurd rfl hi; rfl) a
  · exact (parab k _).one_mem

theorem mem_relParab_right (q : GL (Fin (u + v)) k) (hq : q ∈ parab k (two (stdSum (rfl : u + v = u + v)))) :
    leviTwo k (Fin 1) (Fin (u + v)) (1, q) ∈ relParab k (cols u v) := by
  intro j _
  cases j
  · exact (parab k _).one_mem
  · exact hq

theorem kappa_left (a : GL (Fin 1) k) :
    kappa χ₁ χ₂ u v ⟨_, mem_relParab_left u v a⟩ =
      (χ₁ * absPow k (-(u : ℂ) / 2)) (GeneralLinearGroup.det a) := by
  have h : ltwo u v ⟨_, mem_relParab_left u v a⟩ = 1 := map_one (leviProj k (two (stdSum (rfl : u + v = u + v))))
  simp only [kappa, h, map_one, Pi.one_apply, mul_one]
  rfl

theorem kappa_right (q : GL (Fin (u + v)) k) (hq : q ∈ parab k (two (stdSum (rfl : u + v = u + v)))) :
    kappa χ₁ χ₂ u v ⟨_, mem_relParab_right u v q hq⟩ =
      deltaHalf k (Two (Fin u) (Fin v)) (leviProj k (two (stdSum (rfl : u + v = u + v))) ⟨q, hq⟩) *
        ((χ₁ * absPow k (1 / 2)) (GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : u + v = u + v))) ⟨q, hq⟩ false)) *
          χ₂ (GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : u + v = u + v))) ⟨q, hq⟩ true))) := by
  have h : GeneralLinearGroup.det ((leviTwo k (Fin 1) (Fin (u + v)) (1, q)) false) = 1 := map_one _
  simp only [kappa, h, map_one, one_mul]
  rfl

abbrev CellSp := smoothPart (ind (relParab k (cols u v)) (cellRep χ₁ χ₂ u v))

abbrev ProdSp := IndSp (two (stdSum (rfl : u + v = u + v))) (rho2 χ₁ χ₂ u v)

theorem cell_left (F : CellSp χ₁ χ₂ u v) (a : GL (Fin 1) k) (y : GL (Fin (u + v)) k) :
    F.1.1 (leviTwo k (Fin 1) (Fin (u + v)) (a, y)) =
      ((χ₁ * absPow k (-(u : ℂ) / 2)) (GeneralLinearGroup.det a) : ℂ) •
        F.1.1 (leviTwo k (Fin 1) (Fin (u + v)) (1, y)) := by
  have h : leviTwo k (Fin 1) (Fin (u + v)) (a, y) =
      leviTwo k (Fin 1) (Fin (u + v)) (a, 1) * leviTwo k (Fin 1) (Fin (u + v)) (1, y) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  rw [h]
  refine (F.1.2 ⟨_, mem_relParab_left u v a⟩ _).trans ((cellRep_apply χ₁ χ₂ u v _ _).trans ?_)
  rw [kappa_left]

abbrev sigma2 := (twist (rho2 χ₁ χ₂ u v) (deltaHalf k (Two (Fin u) (Fin v)))).comp
  (leviProj k (two (stdSum (rfl : u + v = u + v))))

theorem sigma2_apply (q : parab k (two (stdSum (rfl : u + v = u + v)))) (w : ℂ ⊗[ℂ] ℂ) :
    sigma2 χ₁ χ₂ u v q w =
      ((deltaHalf k (Two (Fin u) (Fin v)) (leviProj k (two (stdSum (rfl : u + v = u + v))) q) *
        ((χ₁ * absPow k (1 / 2)) (GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : u + v = u + v))) q false)) *
          χ₂ (GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : u + v = u + v))) q true))) : ℂˣ) : ℂ) • w := by
  simp only [sigma2, MonoidHom.comp_apply, twist_apply]
  rw [extTensor_detRep_apply, smul_smul, ← Units.val_mul]
  rfl

def toIndFun (F : CellSp χ₁ χ₂ u v) : indSpace (parab k (two (stdSum (rfl : u + v = u + v)))) (sigma2 χ₁ χ₂ u v) :=
  ⟨fun y => theta χ₁ χ₂ u v (F.1.1 (leviTwo k (Fin 1) (Fin (u + v)) (1, y))), fun q y => by
      dsimp only
      have h : leviTwo k (Fin 1) (Fin (u + v)) (1, (q : GL (Fin (u + v)) k) * y) =
          leviTwo k (Fin 1) (Fin (u + v)) (1, q) * leviTwo k (Fin 1) (Fin (u + v)) (1, y) := by
        rw [← map_mul, Prod.mk_mul_mk, mul_one]
      have hF := (F.1.2 ⟨_, mem_relParab_right u v q q.2⟩ (leviTwo k (Fin 1) (Fin (u + v)) (1, y))).trans
        (cellRep_apply χ₁ χ₂ u v ⟨_, mem_relParab_right u v q q.2⟩ (F.1.1 (leviTwo k (Fin 1) (Fin (u + v)) (1, y))))
      rw [h]
      refine (congrArg (theta χ₁ χ₂ u v) hF).trans ?_
      rw [sigma2_apply, map_smul]
      exact congrArg (fun c : ℂˣ => (c : ℂ) • theta χ₁ χ₂ u v (F.1.1 (leviTwo k (Fin 1) (Fin (u + v)) (1, y))))
        (kappa_right χ₁ χ₂ u v q q.2)⟩

theorem toIndFun_apply (F : CellSp χ₁ χ₂ u v) (y : GL (Fin (u + v)) k) :
    (toIndFun χ₁ χ₂ u v F).1 y = theta χ₁ χ₂ u v (F.1.1 (leviTwo k (Fin 1) (Fin (u + v)) (1, y))) := rfl

theorem ind_val_apply {G H W : Type} [Group G] [AddCommGroup W] [Module ℂ W] {P : Subgroup G}
    (σ : Representation ℂ P W) (g x : G) (f : indSpace P σ) : (ind P σ g f).1 x = f.1 (x * g) := rfl

theorem toIndFun_smooth (F : CellSp χ₁ χ₂ u v) :
    toIndFun χ₁ χ₂ u v F ∈ smoothPart (ind (parab k (two (stdSum (rfl : u + v = u + v)))) (sigma2 χ₁ χ₂ u v)) := by
  refine mem_smoothPart_of_nhds ?_
  have hc : Continuous fun y : GL (Fin (u + v)) k => leviTwo k (Fin 1) (Fin (u + v)) (1, y) :=
    (continuous_leviTwo k).comp (Continuous.prodMk continuous_const continuous_id)
  have hF : IsOpen {g | ind (relParab k (cols u v)) (cellRep χ₁ χ₂ u v) g F.1 = F.1} := F.2
  have h0 : ind (relParab k (cols u v)) (cellRep χ₁ χ₂ u v) 1 F.1 = F.1 :=
    LinearMap.congr_fun (map_one (ind (relParab k (cols u v)) (cellRep χ₁ χ₂ u v))) F.1
  have h1 : {g | ind (relParab k (cols u v)) (cellRep χ₁ χ₂ u v) g F.1 = F.1} ∈
      nhds (leviTwo k (Fin 1) (Fin (u + v)) (1, 1)) := by
    have : leviTwo k (Fin 1) (Fin (u + v)) (1, 1) = 1 := map_one _
    rw [this]
    exact hF.mem_nhds h0
  refine Filter.mem_of_superset (hc.continuousAt.preimage_mem_nhds h1) fun y hy => ?_
  have hy' : ind (relParab k (cols u v)) (cellRep χ₁ χ₂ u v) (leviTwo k (Fin 1) (Fin (u + v)) (1, y)) F.1 =
    F.1 := hy
  show ind (parab k (two (stdSum (rfl : u + v = u + v)))) (sigma2 χ₁ χ₂ u v) y (toIndFun χ₁ χ₂ u v F) =
    toIndFun χ₁ χ₂ u v F
  refine Subtype.ext (funext fun z => ?_)
  simp only [ind_val_apply, toIndFun_apply]
  have h2 := congrArg (fun f => f.1 (leviTwo k (Fin 1) (Fin (u + v)) (1, z))) hy'
  simp only [ind_val_apply] at h2
  refine congrArg (theta χ₁ χ₂ u v) ((congrArg F.1.1 ?_).trans h2)
  rw [← map_mul, Prod.mk_mul_mk, mul_one]

def ofIndFun (φ : ProdSp χ₁ χ₂ u v) : indSpace (relParab k (cols u v)) (cellRep χ₁ χ₂ u v) :=
  ⟨fun x => ((χ₁ * absPow k (-(u : ℂ) / 2)) (GeneralLinearGroup.det (x false)) : ℂ) •
      (theta χ₁ χ₂ u v).symm (φ.1.1 (x true)), fun p x => by
    dsimp only
    have h1 : φ.1.1 ((p : Levi k (Two (Fin 1) (Fin (u + v)))) true * x true) =
        sigma2 χ₁ χ₂ u v ⟨(p : Levi k (Two (Fin 1) (Fin (u + v)))) true, p.2 true trivial⟩ (φ.1.1 (x true)) :=
      φ.1.2 ⟨(p : Levi k (Two (Fin 1) (Fin (u + v)))) true, p.2 true trivial⟩ (x true)
    have h2 : ((p : Levi k (Two (Fin 1) (Fin (u + v)))) * x) true = (p : Levi k (Two (Fin 1) (Fin (u + v)))) true * x true := rfl
    have h3 : ((p : Levi k (Two (Fin 1) (Fin (u + v)))) * x) false = (p : Levi k (Two (Fin 1) (Fin (u + v)))) false * x false := rfl
    rw [h2, h3, h1, sigma2_apply, cellRep_apply, map_smul, smul_smul, smul_smul, map_mul, map_mul]
    congr 1
    simp only [kappa, Units.val_mul]
    ring⟩

theorem ofIndFun_apply (φ : ProdSp χ₁ χ₂ u v) (x : Levi k (Two (Fin 1) (Fin (u + v)))) :
    (ofIndFun χ₁ χ₂ u v φ).1 x = ((χ₁ * absPow k (-(u : ℂ) / 2)) (GeneralLinearGroup.det (x false)) : ℂ) •
      (theta χ₁ χ₂ u v).symm (φ.1.1 (x true)) := rfl

theorem ofIndFun_smooth (hχ₁ : IsSmoothChar χ₁) (φ : ProdSp χ₁ χ₂ u v) :
    ofIndFun χ₁ χ₂ u v φ ∈ smoothPart (ind (relParab k (cols u v)) (cellRep χ₁ χ₂ u v)) := by
  refine mem_smoothPart_of_nhds ?_
  have hχ : IsSmoothChar (detChar (Fin 1) (χ₁ * absPow k (-(u : ℂ) / 2))) :=
    (hχ₁.mul (isSmoothChar_of_isUnram (isUnram_absPow k _))).detChar
  have hφ : IsOpen {g | ind (parab k (two (stdSum (rfl : u + v = u + v)))) (sigma2 χ₁ χ₂ u v) g φ.1 = φ.1} := φ.2
  have ho := (hχ.preimage (continuous_apply (A := fun j => GL (Two (Fin 1) (Fin (u + v)) j) k) false)).inter
    (hφ.preimage (continuous_apply (A := fun j => GL (Two (Fin 1) (Fin (u + v)) j) k) true))
  have h0 : ind (parab k (two (stdSum (rfl : u + v = u + v)))) (sigma2 χ₁ χ₂ u v) 1 φ.1 = φ.1 :=
    LinearMap.congr_fun (map_one (ind (parab k (two (stdSum (rfl : u + v = u + v)))) (sigma2 χ₁ χ₂ u v))) φ.1
  refine Filter.mem_of_superset (ho.mem_nhds ⟨MonoidHom.mem_ker.2 (map_one _), h0⟩) fun x hx => ?_
  obtain ⟨hx1, hx2⟩ := hx
  have hx1' : (χ₁ * absPow k (-(u : ℂ) / 2)) (GeneralLinearGroup.det (x false)) = 1 := MonoidHom.mem_ker.1 hx1
  have hx2' : ind (parab k (two (stdSum (rfl : u + v = u + v)))) (sigma2 χ₁ χ₂ u v) (x true) φ.1 = φ.1 := hx2
  refine Subtype.ext (funext fun z => ?_)
  simp only [ind_val_apply, ofIndFun_apply]
  have h2 := congrArg (fun f => f.1 (z true)) hx2'
  simp only [ind_val_apply] at h2
  have h3 : (z * x) false = z false * x false := rfl
  have h4 : (z * x) true = z true * x true := rfl
  rw [h3, h4, h2, map_mul, map_mul, hx1', mul_one]

def cellEquiv (hχ₁ : IsSmoothChar χ₁) : CellSp χ₁ χ₂ u v ≃ₗ[ℂ] ProdSp χ₁ χ₂ u v where
  toFun F := ⟨toIndFun χ₁ χ₂ u v F, toIndFun_smooth χ₁ χ₂ u v F⟩
  invFun φ := ⟨ofIndFun χ₁ χ₂ u v φ, ofIndFun_smooth χ₁ χ₂ u v hχ₁ φ⟩
  map_add' F G := Subtype.ext (Subtype.ext (funext fun y => by
    simp only [Submodule.coe_add, Pi.add_apply, toIndFun_apply, map_add]))
  map_smul' c F := Subtype.ext (Subtype.ext (funext fun y => by
    simp only [Submodule.coe_smul, Pi.smul_apply, toIndFun_apply, map_smul, RingHom.id_apply]))
  left_inv F := Subtype.ext (Subtype.ext (funext fun x => by
    simp only [ofIndFun_apply, toIndFun_apply, LinearEquiv.symm_apply_apply]
    have hx : x = leviTwo k (Fin 1) (Fin (u + v)) (x false, x true) :=
      (MulEquiv.apply_symm_apply (leviTwo k (Fin 1) (Fin (u + v))) x).symm
    exact ((congrArg F.1.1 hx).trans (cell_left χ₁ χ₂ u v F (x false) (x true))).symm))
  right_inv φ := Subtype.ext (Subtype.ext (funext fun y => by
    simp only [ofIndFun_apply, toIndFun_apply]
    have e1 : (leviTwo k (Fin 1) (Fin (u + v)) (1, y)) false = 1 := rfl
    have e2 : (leviTwo k (Fin 1) (Fin (u + v)) (1, y)) true = y := rfl
    rw [e1, e2, map_one, map_one, Units.val_one, one_smul, LinearEquiv.apply_symm_apply]))

theorem cellEquiv_val (hχ₁ : IsSmoothChar χ₁) (F : CellSp χ₁ χ₂ u v) (y : GL (Fin (u + v)) k) :
    (cellEquiv χ₁ χ₂ u v hχ₁ F).1.1 y = theta χ₁ χ₂ u v (F.1.1 (leviTwo k (Fin 1) (Fin (u + v)) (1, y))) := rfl

theorem prod₂_val (φ : ProdSp χ₁ χ₂ u v) (x y : GL (Fin (u + v)) k) :
    (prod₂ (detRep (Fin u) (χ₁ * absPow k (1 / 2))) (detRep (Fin v) χ₂) x φ).1.1 y = φ.1.1 (y * x) := rfl

theorem cellFunctor_val (F : CellSp χ₁ χ₂ u v) (x y : Levi k (Two (Fin 1) (Fin (u + v)))) :
    (cellFunctor (what₂ u v) (cols u v) (detPair χ₁ χ₂ u v) x F).1.1 y = F.1.1 (y * x) := rfl

theorem cellEquiv_act (hχ₁ : IsSmoothChar χ₁) (F : CellSp χ₁ χ₂ u v) (g : GL (Fin 1) k × GL (Fin (u + v)) k) :
    cellEquiv χ₁ χ₂ u v hχ₁ (cellFunctor (what₂ u v) (cols u v) (detPair χ₁ χ₂ u v) (leviTwo k (Fin 1) (Fin (u + v)) g) F) =
      ((χ₁ * absPow k (-(u : ℂ) / 2)) (GeneralLinearGroup.det g.1) : ℂ) •
        prod₂ (detRep (Fin u) (χ₁ * absPow k (1 / 2))) (detRep (Fin v) χ₂) g.2 (cellEquiv χ₁ χ₂ u v hχ₁ F) := by
  refine Subtype.ext (Subtype.ext (funext fun y => ?_))
  simp only [Submodule.coe_smul, Pi.smul_apply, cellEquiv_val, prod₂_val, cellFunctor_val]
  have hmul : leviTwo k (Fin 1) (Fin (u + v)) (1, y) * leviTwo k (Fin 1) (Fin (u + v)) g =
      leviTwo k (Fin 1) (Fin (u + v)) (g.1, y * g.2) := by
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  rw [hmul, cell_left, map_smul]

theorem cellFirst_det_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → ∀ (u v : ℕ), ∃ (f : ∀ i, (Σ j, Fin ((GlobalTheory.DetProdCells.cellFirst u v).1 i j)) ≃ Two (Fin (u + 1)) (Fin v) i) (g : ∀ j, (Σ i, Fin ((GlobalTheory.DetProdCells.cellFirst u v).1 i j)) ≃ Two (Fin 1) (Fin (u + v)) j), Nonempty (Representation.Equiv ((cellFunctor f g ((extTensor (detRep (Fin (u + 1)) χ₁) (detRep (Fin v) χ₂)).comp (leviTwo k (Fin (u + 1)) (Fin v)).symm.toMonoidHom)).comp (leviTwo k (Fin 1) (Fin (u + v))).toMonoidHom) (extTensor (detRep (Fin 1) (χ₁ * absPow k (-(u : ℂ) / 2))) (prod₂ (detRep (Fin u) (χ₁ * absPow k (1 / 2))) (detRep (Fin v) χ₂)))) := by
  intro k _ _ _ _ χ₁ χ₂ h₁ _ u v
  refine ⟨what₂ u v, cols u v, ⟨.mk ((cellEquiv χ₁ χ₂ u v h₁).trans (TensorProduct.lid ℂ _).symm) fun g => ?_⟩⟩
  refine LinearMap.ext fun F => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply, TensorProduct.lid_symm_apply,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  refine (congrArg (fun w => (1 : ℂ) ⊗ₜ[ℂ] w) (cellEquiv_act χ₁ χ₂ u v h₁ F g)).trans ?_
  have hc : ((χ₁ * absPow k (-(u : ℂ) / 2)) (GeneralLinearGroup.det g.1) : ℂ) • (1 : ℂ) =
      detRep (Fin 1) (χ₁ * absPow k (-(u : ℂ) / 2)) g.1 1 := by
    rw [detRep, ofChar_apply, detChar_apply, smul_eq_mul, mul_one]
  simp only [extTensor_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', hc]

end GlobalTheory.CellFirstDet
