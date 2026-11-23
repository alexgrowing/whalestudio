import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.VaceigenDual
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDict

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKG.LocalRamifiedLeviRestriction

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix
open PositivityTheory.KCo PositivityTheory.ThK
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

def lrH (P : GL (Fin n) k) (Q : GL (Fin d) k) : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k where
  toFun Y := P.1 * Y * Q.1
  invFun Y := (P⁻¹).1 * Y * (Q⁻¹).1
  left_inv Y := by
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  right_inv Y := by
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

def chg {Z : Type} (P : GL (Fin n) k) (Q : GL (Fin d) k) (s : ℂ) (ι : (Z → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)) :
    (Z → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ) := s • (LinearMap.funLeft ℂ ℂ (lrH P Q) ∘ₗ ι)

theorem chg_apply {Z : Type} (P : GL (Fin n) k) (Q : GL (Fin d) k) (s : ℂ) (ι : (Z → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ))
    (φ : Z → ℂ) (Y : Matrix (Fin n) (Fin d) k) : chg P Q s ι φ Y = s * ι φ (P.1 * Y * Q.1) := rfl

theorem bij_smul {Z Y : Type} [TopologicalSpace Z] [TopologicalSpace Y] {ι : (Z → ℂ) →ₗ[ℂ] (Y → ℂ)}
    (hb : Set.BijOn ι (SB Z : Set _) (SB Y : Set _)) {s : ℂ} (hs : s ≠ 0) : Set.BijOn (s • ι) (SB Z : Set _) (SB Y : Set _) := by
  refine ⟨fun φ h => (SB Y).smul_mem s (hb.1 h), fun a ha b hb' e => hb.2.1 ha hb' (smul_right_injective _ hs e), fun Φ h => ?_⟩
  obtain ⟨φ, h1, h2⟩ := hb.2.2 h
  refine ⟨s⁻¹ • φ, (SB Z).smul_mem _ h1, ?_⟩
  rw [LinearMap.smul_apply, map_smul, smul_smul, mul_inv_cancel₀ hs, one_smul, h2]

variable {P g g' : GL (Fin n) k} {Q h h' : GL (Fin d) k} {ν α β : kˣ →* ℂˣ} (s : ℂ) (Φ : Matrix (Fin n) (Fin d) k → ℂ)
  (Y : Matrix (Fin n) (Fin d) k)

theorem B_left (key : (g'.1)ᵀ * P.1 = P.1 * (g.1)ᵀ) (hd : gdet g' = gdet g) :
    s * omB ν α g' 1 Φ (P.1 * Y * Q.1) = omB ν α g 1 (fun Y => s * Φ (P.1 * Y * Q.1)) Y := by
  simp only [omB, hd, map_one, Units.val_one, apow_one, Matrix.mul_one, mul_one, ← Matrix.mul_assoc, key]
  ring

theorem B_right (key : Q.1 * h'.1 = h.1 * Q.1) (hd : gdet h' = gdet h) :
    s * omB ν α 1 h' Φ (P.1 * Y * Q.1) = omB ν α 1 h (fun Y => s * Φ (P.1 * Y * Q.1)) Y := by
  simp only [omB, hd, map_one, Units.val_one, apow_one, Matrix.one_mul, one_mul, mul_one, transpose_one, Matrix.mul_assoc, key]
  ring

theorem gdet_conj (b g : GL (Fin n) k) : gdet (b⁻¹ * g * b) = gdet g := by
  rw [gdet_mul, gdet_mul, mul_right_comm, ← gdet_mul, inv_mul_cancel, gdet, map_one, one_mul]

end Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
  {ψ : AddChar (AF F) ℂ}

theorem reads_chg {ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)} {T S S'}
    (hR : Reads v ι T S) {P : GL (Fin n) (Fv F v)} {Q : GL (Fin d) (Fv F v)} {s : ℂ}
    (hS : ∀ Φ Y, s * S Φ (P.1 * Y * Q.1) = S' (fun Y => s * Φ (P.1 * Y * Q.1)) Y) : Reads v (chg P Q s ι) T S' := fun φ hφ => by
  obtain ⟨φ₁, h1, h2, h3⟩ := hR φ hφ
  refine ⟨φ₁, h1, h2, funext fun Y => ?_⟩
  rw [chg_apply, h3, hS]
  rfl

theorem comp_comp (hσ : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) : (t.comp σ).comp σ = t :=
  AlgHom.ext fun x => congrArg t (Vac.sigma_sigma hσ x)

theorem chrW_conj (hσ : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {χ : Chr F E} {K : Subgroup (AF F)ˣ} {m : ℕ} (hχ : ResEtaPow K χ m)
    (x : (Fv F v)ˣ) : chrW χ (t.comp σ) x = (chrW χ t x)⁻¹ := by
  obtain ⟨⟨sec, h⟩, -⟩ := section_statement F E σ hσ v t
  obtain ⟨⟨sec', h'⟩, -⟩ := section_statement F E σ hσ v (t.comp σ)
  obtain ⟨g, ha, h1, h2⟩ := h.exists_gl (β := Unit) (GeneralLinearGroup.scalar _ x) 1
  let z : (AE F E)ˣ := GeneralLinearGroup.det g
  have hz : (z : AE F E) = g.1 () () := det_unique _
  have za : At (evFin F v) ((z : AE F E) - 1) := by
    rw [hz]
    simpa using kd_at_matrix.1 ha () ()
  have z1 : piW t z = x := by
    rw [hz]
    simpa using congrFun (congrFun h1 ()) ()
  have z2 : piW (t.comp σ) z = 1 := by
    rw [hz]
    simpa using congrFun (congrFun h2 ()) ()
  let z' : (AE F E)ˣ := Units.map (cA σ : AE F E →* AE F E) z
  have a1 := (h.idele z x za z1 z2).1 χ
  have a2 := (h'.idele z' x (by simpa [z'] using h.atConj _ za) ((h.conj _).2.trans z1)
    (by rw [comp_comp hσ]; exact (h.conj _).1.trans z2)).1 χ
  have a3 := hχ (Units.map (Algebra.norm (AF F) : AE F E →* AF F) z)
  rw [if_pos (Subgroup.mem_sup_right (MonoidHom.mem_range.2 ⟨z, rfl⟩)), show Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E)
    (Units.map (Algebra.norm (AF F) : AE F E →* AF F) z) = z * z' from Units.ext (GlobalTheory.Doubling.algebraMap_norm_eq hσ _),
    map_mul, Circle.coe_mul, a1, a2] at a3
  exact eq_inv_of_mul_eq_one_right (Units.ext a3)

theorem chrW_div (χ χ' : Chr F E) (t : E →ₐ[F] Fv F v) (x : (Fv F v)ˣ) : chrW (χ / χ') t x = chrW χ t x / chrW χ' t x :=
  map_div Circle.toUnits _ _

end PositivityTheory.ThKG.LocalRamifiedLeviRestriction
