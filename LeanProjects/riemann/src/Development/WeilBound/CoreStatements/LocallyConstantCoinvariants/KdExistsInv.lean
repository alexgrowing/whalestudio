import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.KdMulRight
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ExistsEqMulApplyZero

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Loc

variable {k : Type} [Field k] {α β : Type} [Fintype α] [Fintype β]

def ofM (Y : Matrix α β k) : α × β → k := fun p => Y p.1 p.2

def toM (y : α × β → k) : Matrix α β k := Matrix.of fun i j => y (i, j)

omit [Field k] [Fintype α] [Fintype β] in
@[simp] theorem toM_ofM (Y : Matrix α β k) : toM (ofM Y) = Y := rfl

omit [Field k] [Fintype α] [Fintype β] in
@[simp] theorem ofM_toM (y : α × β → k) : ofM (toM y) = y := rfl

theorem dot_ofM (Y Z : Matrix α β k) : ofM Y ⬝ᵥ ofM Z = trace (Yᵀ * Z) := by
  simp only [dotProduct, ofM, Fintype.sum_prod_type, trace, diag, mul_apply, transpose_apply]
  exact Finset.sum_comm

theorem schr_schr {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ] (a b : (κ → R) × (κ → R))
    (φ : (κ → R) → ℂ) : schr ψ a (schr ψ b φ) = ψ (⅟(2 : R) * (a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2)) • schr ψ (a + b) φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, Prod.fst_add, Prod.snd_add, add_assoc,
    add_dotProduct, dotProduct_add]
  congr 2
  have h : ⅟(2 : R) + ⅟(2 : R) = 1 := invOf_two_add_invOf_two
  linear_combination (a.1 ⬝ᵥ b.2) * (-h)

variable [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k]

theorem schr_mem [Invertible (2 : k)] {ψ : AddChar k ℂ} (hψ : Continuous ψ) {κ : Type} [Fintype κ] (w : (κ → k) × (κ → k))
    {φ : (κ → k) → ℂ} (h : φ ∈ SB (κ → k)) : schr ψ w φ ∈ SB (κ → k) := by
  haveI := nonarch_field k
  have hl := GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψ
  refine ⟨(hl.comp_continuous (by fun_prop)).mul (h.1.comp_continuous (by fun_prop)), ?_⟩
  exact (h.2.comp_homeomorph (Homeomorph.addRight w.1)).mul_left

variable [DecidableEq β]

def rm (g : GL β k) : (α × β → k) ≃ₜ (α × β → k) where
  toFun y := ofM (toM y * g.1)
  invFun y := ofM (toM y * (g⁻¹).1)
  left_inv y := by simp only [toM_ofM, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ofM_toM]
  right_inv y := by simp only [toM_ofM, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ofM_toM]
  continuous_toFun := continuous_pi fun p => by simp only [ofM, toM, mul_apply, of_apply]; fun_prop
  continuous_invFun := continuous_pi fun p => by simp only [ofM, toM, mul_apply, of_apply]; fun_prop

def rmL (g : GL β k) : Module.End ℂ ((α × β → k) → ℂ) := LinearMap.funLeft ℂ ℂ (rm g)

theorem rmL_apply (g : GL β k) (Φ : (α × β → k) → ℂ) (y) : rmL g Φ y = Φ (ofM (toM y * g.1)) := rfl

theorem rmL_mem (g : GL β k) {Φ : (α × β → k) → ℂ} (h : Φ ∈ SB (α × β → k)) : rmL g Φ ∈ SB (α × β → k) :=
  ⟨h.1.comp_continuous (rm g).continuous, h.2.comp_homeomorph (rm g)⟩

theorem rmL_inv (g : GL β k) (Φ : (α × β → k) → ℂ) : rmL g⁻¹ (rmL g Φ) = Φ := funext fun y => by
  simp only [rmL_apply, toM_ofM, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ofM_toM]

theorem rmL_schr [Invertible (2 : k)] (ψ : AddChar k ℂ) (g : GL β k) (w) (Φ : (α × β → k) → ℂ) :
    rmL g (schr ψ w Φ) = schr ψ (ofM (toM w.1 * (g⁻¹).1), ofM (toM w.2 * (g.1)ᵀ)) (rmL g Φ) := funext fun y => by
  have e1 : ofM (toM y * g.1) ⬝ᵥ w.2 = y ⬝ᵥ ofM (toM w.2 * (g.1)ᵀ) := by
    rw [← ofM_toM w.2, ← ofM_toM y, dot_ofM, dot_ofM]
    simp only [toM_ofM, transpose_mul, Matrix.mul_assoc]
    rw [trace_mul_comm, Matrix.mul_assoc]
  have e2 : w.1 ⬝ᵥ w.2 = ofM (toM w.1 * (g⁻¹).1) ⬝ᵥ ofM (toM w.2 * (g.1)ᵀ) := by
    rw [dot_ofM, transpose_mul, Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_assoc _ (g.1)ᵀ, ← transpose_mul,
      Units.inv_mul, transpose_one, Matrix.mul_one, ← dot_ofM]; rfl
  have e3 : ofM (toM y * g.1) + w.1 = ofM (toM (y + ofM (toM w.1 * (g⁻¹).1)) * g.1) := by
    have : toM (y + ofM (toM w.1 * (g⁻¹).1)) = toM y + toM w.1 * (g⁻¹).1 := rfl
    rw [this, Matrix.add_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]; rfl
  simp only [rmL_apply, schr]
  rw [e1, e3, ← e2]

omit [DecidableEq β] [ValuativeRel k] [IsNonarchimedeanLocalField k] [Field k] in
theorem kd_exists_inv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {ι : (X → ℂ) →ₗ[ℂ] (Y → ℂ)}
    (hb : Set.BijOn ι (SB X : Set _) (SB Y : Set _)) : ∃ j : (Y → ℂ) →ₗ[ℂ] (X → ℂ),
      (∀ Φ ∈ SB Y, j Φ ∈ SB X ∧ ι (j Φ) = Φ) ∧ ∀ φ ∈ SB X, j (ι φ) = φ := by
  let e : SB X ≃ₗ[ℂ] SB Y := LinearEquiv.ofBijective (ι.restrict fun φ h => hb.1 h)
    ⟨fun a b h => Subtype.ext (hb.2.1 a.2 b.2 (congrArg Subtype.val h)), fun b => by
      obtain ⟨a, ha, e⟩ := hb.2.2 b.2
      exact ⟨⟨a, ha⟩, Subtype.ext e⟩⟩
  obtain ⟨j, hj⟩ := LinearMap.exists_extend ((SB X).subtype ∘ₗ e.symm.toLinearMap)
  have h1 : ∀ Φ (h : Φ ∈ SB Y), j Φ = (e.symm ⟨Φ, h⟩).1 := fun Φ h => LinearMap.congr_fun hj ⟨Φ, h⟩
  have h2 : ∀ Φ ∈ SB Y, j Φ ∈ SB X ∧ ι (j Φ) = Φ := fun Φ h => by
    rw [h1 Φ h]
    exact ⟨(e.symm _).2, congrArg Subtype.val (e.apply_symm_apply ⟨Φ, h⟩)⟩
  exact ⟨j, h2, fun φ h => hb.2.1 (h2 _ (hb.1 h)).1 h (h2 _ (hb.1 h)).2⟩

end Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype κ] {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)}

variable (σ t JA JB) in

structure Grams : Prop where
  uA : IsUnit (JA.map (piW t))
  uB : IsUnit (JB.map (piW t))
  sym : ∃ ε : Fv F v, ε * ε = 1 ∧ JA.map (piW (t.comp σ)) = ε • (JA.map (piW t))ᵀ ∧
    JB.map (piW (t.comp σ)) = (-ε) • (JB.map (piW t))ᵀ

variable (σ t JA JB) in

def coord (u : Matrix α β (AE F E)) : (α × β → Fv F v) × (α × β → Fv F v) :=
  (ofM (-(JA.map (piW t) * u.map (piW (t.comp σ)) * (JB.map (piW t))ᵀ)), ofM (-u.map (piW t)))

theorem symp_eq (h : IsSec σ t sec) (hG : Grams σ t JA JB) {u : Matrix α β (AE F E)} (hu : At (evFin F v) u)
    (u' : Matrix α β (AE F E)) : symp (R := AF F) (cA σ) (-1) JA JB u u' = sgl v
      ((coord σ t JA JB u).1 ⬝ᵥ (coord σ t JA JB u').2 - (coord σ t JA JB u').1 ⬝ᵥ (coord σ t JA JB u).2) := by
  obtain ⟨ε, hε, hA, hB⟩ := hG.sym
  have e : hTens (cA σ) JA JB u u' = trace (JAᵀ * u * JB * (u'.map (cA σ))ᵀ) := by
    simp only [hTens, trace, diag, mul_apply, transpose_apply, map_apply, Finset.sum_mul]
    calc _ = ∑ i, ∑ k, ∑ j, ∑ l, u i j * JA i k * JB j l * cA σ (u' k l) := Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, ∑ l, u i j * JA i k * JB j l * cA σ (u' k l) := Finset.sum_comm
      _ = ∑ k, ∑ l, ∑ j, ∑ i, u i j * JA i k * JB j l * cA σ (u' k l) := Finset.sum_congr rfl fun k _ => by
        rw [Finset.sum_comm]
        calc _ = ∑ j, ∑ l, ∑ i, u i j * JA i k * JB j l * cA σ (u' k l) := Finset.sum_congr rfl fun j _ => Finset.sum_comm
          _ = _ := Finset.sum_comm
      _ = _ := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun i _ => by ring
  have ha : At (evFin F v) (-1 * hTens (cA σ) JA JB u u') := fun a ha => by
    rw [e, ← mul_smul_comm, ← trace_smul, (((hu.kd_mul_left JAᵀ).kd_mul_right JB).kd_mul_right _) a ha, trace_zero, mul_zero]
  rw [symp, h.trace _ ha, e]
  congr 1
  simp only [map_mul, map_neg, map_one, AddMonoidHom.map_trace, Matrix.map_mul, transpose_map, h.conj1, h.conj2, hA, hB, coord, dot_ofM,
    transpose_smul, transpose_transpose, Matrix.smul_mul, Matrix.mul_smul, smul_smul, trace_smul, smul_eq_mul, transpose_neg,
    transpose_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, trace_neg]
  set A := JA.map (piW t)
  set B := JB.map (piW t)
  set P := u.map (piW t)
  set Q := u.map (piW (t.comp σ))
  set P' := u'.map (piW t)
  set Q' := u'.map (piW (t.comp σ))
  have e1 : trace (B * (Q'ᵀ * Aᵀ) * P) = trace (Aᵀ * P * B * Q'ᵀ) := by
    rw [Matrix.mul_assoc (Aᵀ * P), trace_mul_comm (Aᵀ * P)]; simp only [Matrix.mul_assoc]
  have e2 : trace (B * (Qᵀ * Aᵀ) * P') = trace (A * Q * Bᵀ * P'ᵀ) := by
    rw [← trace_transpose, transpose_mul, trace_mul_comm]; simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
  rw [e1, e2]
  linear_combination (trace (A * Q * Bᵀ * P'ᵀ)) * hε

end PositivityTheory.KCo
