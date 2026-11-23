import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitDict
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.LocalDef
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.VaceigenDual
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.LmOfLinBar
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictAd
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictMod
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictSec
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfActs

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThK.SplitDict

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix
open PositivityTheory.KCo
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

theorem A_left (key : (g'.1)ᵀ * P.1 = P.1 * (g⁻¹).1) (hd : gdet g' = (gdet g)⁻¹) :
    s * omB ν α g' 1 Φ (P.1 * Y * Q.1) = omA ν β g 1 (fun Y => s * Φ (P.1 * Y * Q.1)) Y := by
  simp only [omA, omB, hd, map_one, map_inv, Units.val_one, apow_one, apow_inv, Matrix.mul_one, mul_one, ← Matrix.mul_assoc, key,
    neg_div]
  ring

theorem A_right (key : Q.1 * h'.1 = (invT h).1 * Q.1) (hd : gdet h' = (gdet h)⁻¹) (hα : ∀ x, α x = (β x)⁻¹) {ν' : kˣ →* ℂˣ} :
    s * omB ν' α 1 h' Φ (P.1 * Y * Q.1) = omA ν β 1 h (fun Y => s * Φ (P.1 * Y * Q.1)) Y := by
  simp only [omA, omB, hd, hα, map_one, map_inv, inv_inv, inv_one, Units.val_one, apow_one, apow_inv, Matrix.one_mul, one_mul,
    mul_one, transpose_one, Matrix.mul_assoc, key, neg_div]
  ring

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

theorem gdet_rel {U : GL (Fin n) k} (e : (invT g')⁻¹ * U * g = U) : gdet g' = (gdet g)⁻¹ := by
  have := congrArg gdet e
  rw [gdet_mul, gdet_mul, ← map_inv, gdet_invT, mul_right_comm, mul_eq_right, gdet, map_inv, inv_inv] at this
  exact eq_inv_of_mul_eq_one_left this

end Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
  {ψ : AddChar (AF F) ℂ}

theorem lin_chg {π₁ π₀ : AE F E →+* Fv F v} {co co' ι} (hι : M.IsLin ψ π₁ π₀ co ι) (P : GL (Fin n) (Fv F v))
    (Q : GL (Fin d) (Fv F v)) {s : ℂ} (hs : s ≠ 0) (hco : ∀ u, P.1 * co' u * Q.1 = co u) : M.IsLin ψ π₁ π₀ co' (chg P Q s ι) := by
  refine ⟨bij_smul (bij_comp hι.bij _) hs, fun u hu h0 φ hφ φ₁ hφ₁ ha Y => ?_, fun u hu h0 φ hφ φ₁ hφ₁ ha x hx hx0 => ?_⟩
  · rw [chg_apply, chg_apply, hι.trans u hu h0 φ hφ φ₁ hφ₁ ha, Matrix.mul_add, Matrix.add_mul, hco]
  · rw [chg_apply, chg_apply, hco, hι.mult u hu h0 φ hφ φ₁ hφ₁ ha x hx hx0, mul_left_comm]

theorem reads_chg {ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)} {T S S'}
    (hR : Reads v ι T S) {P : GL (Fin n) (Fv F v)} {Q : GL (Fin d) (Fv F v)} {s : ℂ}
    (hS : ∀ Φ Y, s * S Φ (P.1 * Y * Q.1) = S' (fun Y => s * Φ (P.1 * Y * Q.1)) Y) : Reads v (chg P Q s ι) T S' := fun φ hφ => by
  obtain ⟨φ₁, h1, h2, h3⟩ := hR φ hφ
  refine ⟨φ₁, h1, h2, funext fun Y => ?_⟩
  rw [chg_apply, h3, hS]
  rfl

theorem exists_cond (hψ : IsStd ψ) (v : Pl F) : ∃ δ : (Fv F v)ˣ, ∀ x : Fv F v,
    (∀ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (x * y) = 1) ↔ δ.1 * x ∈ v.adicCompletionIntegers F := by
  have e : ∀ (α : Af F) (x : Fv F v), α * singleFin v x = singleFin v (x * α v) := fun α x => by
    apply af_ext
    intro u
    by_cases hu : u = v
    · subst hu
      rw [map_mul, evalV_singleFin_self, evalV_singleFin_self, mul_comm]
      rfl
    · rw [map_mul, evalV_singleFin_ne hu, evalV_singleFin_ne hu, mul_zero]
  have s1 : ∀ x : Fv F v, singleFin v x v = x := fun x => evalV_singleFin_self v x
  have s0 : ∀ (x : Fv F v) u, u ≠ v → singleFin v x u = 0 := fun x u hu => evalV_singleFin_ne hu x
  have h1 : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (x * y) = 1) ↔
      x ∈ GlobalTheory.Idele.localIdeal v (GlobalTheory.StdDual.codiff F) := fun x => by
    have := GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.PsiNontriv.isStd_fin_rat hψ) (singleFin v x)
    refine ⟨fun H => ?_, fun H y hy => ?_⟩
    · have h2 := this.2 (fun α hα => by rw [e]; exact H _ (hα v)) v
      rwa [s1] at h2
    · have h2 := this.1 (fun u => by
        by_cases hu : u = v
        · subst hu; rw [s1]; exact H
        · rw [s0 x u hu]; exact zero_mem _) (singleFin v y) (fun u => by
        by_cases hu : u = v
        · subst hu; rw [s1]; exact hy
        · rw [s0 y u hu]; exact zero_mem _)
      rwa [e, s1] at h2
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hx : Valued.v (algebraMap F (Fv F v) (π ^ FractionalIdeal.count F v (GlobalTheory.StdDual.codiff F))) =
      WithZero.exp (-FractionalIdeal.count F v (GlobalTheory.StdDual.codiff F)) := by
    rw [GlobalTheory.Idele.valued_algebraMap, map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one]
  have hne : algebraMap F (Fv F v) (π ^ FractionalIdeal.count F v (GlobalTheory.StdDual.codiff F)) ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hx
    exact WithZero.exp_ne_zero hx.symm
  refine ⟨(Units.mk0 _ hne)⁻¹, fun x => ?_⟩
  rw [h1, GlobalTheory.Idele.mem_localIdeal_iff GlobalTheory.StdDual.codiff_ne_zero, HeightOneSpectrum.mem_adicCompletionIntegers,
    Units.val_inv_eq_inv_val, Units.val_mk0, map_mul, map_inv₀, hx, inv_mul_le_one₀ WithZero.exp_pos]

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

theorem lat_idem (hσ : IsCMExt F E σ) (X : Spc F E n) (W : Spc F E d) (t : E →ₐ[F] Fv F v) :
    ∃ e : AE F E, piW t e = 1 ∧ piW (t.comp σ) e = 0 ∧ ∀ γ ∈ latAtV X W v, e • γ ∈ latAtV X W v := by
  have key : ∀ y ∈ intLoc F E v, ∃ z : AE F E, compFin F E v z = y ∧ ∀ γ ∈ latAtV X W v, z • γ ∈ latAtV X W v := fun y hy => by
    refine intLoc_induction (p := fun y => ∃ z : AE F E, compFin F E v z = y ∧ ∀ γ ∈ latAtV X W v, z • γ ∈ latAtV X W v)
      (fun a ha x => ⟨sgl v a ⊗ₜ[F] (x : E), ?_, fun γ hγ => ?_⟩) ⟨0, map_zero _, fun γ _ => by rw [zero_smul]; exact zero_mem _⟩
      ?_ ?_ hy
    · change evFin F v (sgl v a) ⊗ₜ[F] (x : E) = _
      rw [ev_sgl]
    · induction hγ using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a', -, ha', p, hp, q, hq, rfl⟩ := hz
        refine AddSubgroup.subset_closure ⟨sgl v a * a', fun u hu => ?_, ?_, x • p, X.L.smul_mem x hp, q, hq, ?_⟩
        · rw [smul_eq_mul, ← mul_assoc, mul_sgl, hu, zero_mul, map_zero, zero_mul]
        · rw [map_mul, ev_sgl]; exact mul_mem ha ha'
        · ext i j
          change (sgl v a ⊗ₜ[F] (x : E)) * (a' • ((1 : AF F) ⊗ₜ[F] (p i * q j))) =
            (sgl v a * a') • ((1 : AF F) ⊗ₜ[F] (((x : E) * p i) * q j))
          rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul, smul_eq_mul, smul_eq_mul,
            mul_one, mul_one, mul_assoc]
      | zero => rw [smul_zero]; exact zero_mem _
      | add _ _ _ _ h h' => rw [smul_add]; exact add_mem h h'
      | neg _ _ h => rw [smul_neg]; exact neg_mem h
    · rintro _ _ ⟨z, rfl, hz⟩ ⟨z', rfl, hz'⟩
      exact ⟨z + z', map_add _ _ _, fun γ hγ => by rw [add_smul]; exact add_mem (hz γ hγ) (hz' γ hγ)⟩
    · rintro _ ⟨z, rfl, hz⟩
      exact ⟨-z, map_neg _ _, fun γ hγ => by rw [neg_smul]; exact neg_mem (hz γ hγ)⟩
  obtain ⟨e, he, h⟩ := key _ (splitIdem_mem hσ t)
  refine ⟨e, ?_, ?_, h⟩
  · change splitProj t (compFin F E v e) = 1
    rw [he, splitProj_splitIdem]
  · change splitProj (t.comp σ) (compFin F E v e) = 0
    rw [he, splitProj_comp_splitIdem]

theorem map_smul_ring (π : AE F E →+* Fv F v) (e : AE F E) (γ : Matrix (Fin n) (Fin d) (AE F E)) : (e • γ).map π = π e • γ.map π :=
  Matrix.ext fun _ _ => map_mul π _ _

def IsInt (Y : Matrix (Fin n) (Fin d) (Fv F v)) : Prop := ∀ i j, Y i j ∈ v.adicCompletionIntegers F

variable {b : GL (Fin n) (Fv F v)} {c : GL (Fin d) (Fv F v)}

theorem lat_to (h : IsSec σ t sec) (hb : IsSplitBasis t X.L b) (hc : IsSplitBasis t W.L c) {γ} (hγ : γ ∈ latAtV X W v) :
    IsInt ((b⁻¹).1 * γ.map (piW t) * (c⁻¹).1ᵀ) := by
  have mem : ∀ {m : ℕ} {L : Submodule (𝓞 E) (Fin m → E)} {p}, p ∈ L → (fun i => t (p i)) ∈ splitLat t L := fun {m L p} hp =>
    ⟨fun i => (1 : Fv F v) ⊗ₜ[F] p i, AddSubgroup.subset_closure ⟨1, one_mem _, p, hp, rfl⟩, funext fun i => one_mul _⟩
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, ha, p, hp, q, hq, rfl⟩ := hz
    have e : (vecMulVec p q).map t = vecMulVec (fun i => t (p i)) fun j => t (q j) := Matrix.ext fun i j => map_mul t _ _
    rw [h.smul1, incM_map h, e, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul, vecMul_transpose]
    exact fun i j => mul_mem ha (mul_mem (hb.mem_iff.1 (mem hp) i) (hc.mem_iff.1 (mem hq) j))
  | zero => rw [Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul]; exact fun _ _ => zero_mem _
  | add _ _ _ _ h h' => rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul]; exact fun i j => add_mem (h i j) (h' i j)
  | neg _ _ h => rw [Matrix.map_neg _ (map_neg _), Matrix.mul_neg, Matrix.neg_mul]; exact fun i j => neg_mem (h i j)

theorem lat_from (hσ : IsCMExt F E σ) (h : IsSec σ t sec) (hb : IsSplitBasis t X.L b) (hc : IsSplitBasis t W.L c)
    {Y : Matrix (Fin n) (Fin d) (Fv F v)} (hY : IsInt Y) :
    ∃ γ ∈ latAtV X W v, γ.map (piW t) = b.1 * Y * c.1ᵀ ∧ γ.map (piW (t.comp σ)) = 0 := by
  let I := (latAtV X W v).map (piW t).toAddMonoidHom.mapMatrix
  have key : ∀ y ∈ latLoc F X.L v, ∀ z ∈ latLoc F W.L v, vecMulVec (splitVec t y) (splitVec t z) ∈ I := fun y hy z hz => by
    have z0 : ∀ {m : ℕ}, splitVec t (0 : Fin m → Fv F v ⊗[F] E) = 0 := funext fun _ => map_zero _
    have ng : ∀ {m : ℕ} (y : Fin m → Fv F v ⊗[F] E), splitVec t (-y) = -splitVec t y := fun _ => funext fun _ => map_neg _ _
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, p, hp, rfl⟩ := hy
      induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a', ha', q, hq, rfl⟩ := hz
        refine ⟨sgl v (a * a') • incM F (vecMulVec p q), AddSubgroup.subset_closure ⟨sgl v (a * a'), GlobalTheory.LatVac.at_liftV v _,
          by rw [ev_sgl]; exact mul_mem ha ha', p, hp, q, hq, rfl⟩, ?_⟩
        refine (h.smul1 _ _).trans ?_
        rw [incM_map h, ev_sgl]
        ext i j : 1
        change a * a' * t (p i * q j) = a * t (p i) * (a' * t (q j))
        rw [map_mul]; ring
      | zero => rw [z0, show vecMulVec _ (0 : Fin d → Fv F v) = 0 from Matrix.ext fun _ _ => mul_zero _]; exact zero_mem _
      | add _ _ _ _ h h' => rw [splitVec_add, vecMulVec_add]; exact add_mem h h'
      | neg _ _ h => rw [ng, vecMulVec_neg]; exact neg_mem h
    | zero => rw [z0, zero_vecMulVec]; exact zero_mem _
    | add _ _ _ _ h h' => rw [splitVec_add, add_vecMulVec]; exact add_mem h h'
    | neg _ _ h => rw [ng, neg_vecMulVec]; exact neg_mem h
  have hm : b.1 * Y * c.1ᵀ ∈ I := by
    have e : b.1 * Y * c.1ᵀ = ∑ j, vecMulVec (b.1 *ᵥ fun i => Y i j) (c.1 *ᵥ Pi.single j 1) := by
      ext i k : 1
      rw [Matrix.sum_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [vecMulVec_apply, mulVec_single_one]
      rfl
    rw [e]
    refine sum_mem fun j _ => ?_
    obtain ⟨y, hy, e1⟩ := (hb _).1 fun i => hY i j
    obtain ⟨z, hz, e2⟩ := (hc (Pi.single j 1)).1 fun i => by
      by_cases e : i = j
      · subst e; simp
      · simp [e]
    rw [← e1, ← e2]
    exact key y hy z hz
  obtain ⟨γ, hγ, e⟩ := hm
  obtain ⟨e₀, h1, h2, h3⟩ := lat_idem hσ X W t
  refine ⟨e₀ • γ, h3 γ hγ, ?_, ?_⟩
  · rw [map_smul_ring, h1, one_smul]; exact e
  · rw [map_smul_ring, h2, zero_smul]

theorem hTens_zero (h : IsSec σ t sec) {u u' : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evFin F v) u)
    (h0 : u.map (piW t) = 0 ∧ u'.map (piW t) = 0 ∨ u.map (piW (t.comp σ)) = 0 ∧ u'.map (piW (t.comp σ)) = 0) :
    hTens (cA σ) (incM F X.J) (incM F W.J) u u' = 0 := by
  have z : ∀ {π : AE F E →+* Fv F v} {w : Matrix (Fin n) (Fin d) (AE F E)}, w.map π = 0 → ∀ i j, π (w i j) = 0 :=
    fun e i j => congrFun (congrFun e i) j
  refine h.ext _ (fun a ha => ?_) ?_ ?_
  · simp only [hTens, Finset.smul_sum, ← smul_mul_assoc, fun i j => kd_at_matrix.1 hu i j a ha, zero_mul, Finset.sum_const_zero]
  · rcases h0 with h0 | h0
    · simp only [hTens, map_sum, map_mul, z h0.1, zero_mul, Finset.sum_const_zero]
    · simp only [hTens, map_sum, map_mul, (h.conj _).1, z h0.2, mul_zero, Finset.sum_const_zero]
  · rcases h0 with h0 | h0
    · simp only [hTens, map_sum, map_mul, (h.conj _).2, z h0.2, mul_zero, Finset.sum_const_zero]
    · simp only [hTens, map_sum, map_mul, z h0.1, zero_mul, Finset.sum_const_zero]

theorem vac_ind {B : Base F E} (hB : B.IsGood σ) {r s r' s' : ℕ} (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') {φ}
    (hφ : M.IsVac B.ψ v φ) {π₁ π₀ : AE F E →+* Fv F v} {co ι} (hι : M.IsLin B.ψ π₁ π₀ co ι)
    (iso : ∀ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) u →
      (u.map π₁ = 0 ∧ u'.map π₁ = 0 ∨ u.map π₀ = 0 ∧ u'.map π₀ = 0) → hTens (cA σ) (incM F X.J) (incM F W.J) u u' = 0)
    (spl : ∀ γ ∈ latAtV X W v, ∃ γ₀ ∈ latAtV X W v, γ₀.map π₁ = 0 ∧ (γ - γ₀).map π₀ = 0)
    (sur : ∀ Y, ∃ x, At (evFin F v) x ∧ x.map π₀ = 0 ∧ co x = Y)
    (int : ∀ x, At (evFin F v) x → x.map π₀ = 0 → (x ∈ latAtV X W v ↔ ∀ u ∈ latAtV X W v, u.map π₁ = 0 →
      B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) x u) = 1) → (x ∈ latAtV X W v ↔ IsInt (co x))) :
    ∃ c : ℂ, c ≠ 0 ∧ ι φ = c • intInd v := by
  obtain ⟨hs, hne, θ, -, hθ⟩ := hφ
  have hAt := (GlobalTheory.LatVac.latAtV_at_stable X W v).1
  have fix : ∀ γ ∈ latAtV X W v, (γ.map π₁ = 0 ∨ γ.map π₀ = 0) → Acts (evFin F v) (M.co.rho B.ψ γ) φ φ := fun γ hγ h0 => by
    have := hθ γ hγ
    rwa [symp, iso γ γ (hAt γ hγ) (h0.imp (fun e => ⟨e, e⟩) fun e => ⟨e, e⟩), mul_zero, map_zero, mul_zero,
      AddChar.map_zero_eq_one, one_smul] at this
  have k3 : ∀ x ∈ latAtV X W v, x.map π₀ = 0 → ι φ (co x) = ι φ 0 := fun x hx h0 => by
    rw [hι.trans x (hAt x hx) h0 φ hs φ hs (fix x hx (Or.inr h0)) 0, zero_add]
  have k1 : ∀ x, At (evFin F v) x → x.map π₀ = 0 → ι φ (co x) ≠ 0 → ∀ u ∈ latAtV X W v, u.map π₁ = 0 →
      B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) x u) = 1 := fun x hx h0 h1 u hu hu0 =>
    (mul_eq_right₀ h1).1 (hι.mult u (hAt u hu) hu0 φ hs φ hs (fix u hu (Or.inl hu0)) x hx h0).symm
  have k2 : ∀ x, At (evFin F v) x → x.map π₀ = 0 → (∀ u ∈ latAtV X W v, u.map π₁ = 0 →
      B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) x u) = 1) → x ∈ latAtV X W v := fun x hx h0 H =>
    Vac.mem_latAtV hB hX hW v hx fun γ hγ => by
      obtain ⟨γ₀, h1, h2, h3⟩ := spl γ hγ
      have e0 : symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (γ - γ₀) x = 0 := by
        rw [symp, iso _ x ((hAt γ hγ).kd_sub (hAt γ₀ h1)) (Or.inr ⟨h3, h0⟩), mul_zero, map_zero]
      have e1 : symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) γ x =
          -symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) x γ₀ := by
        simp only [M.co.form, map_sub, Prod.fst_sub, Prod.snd_sub, sub_dotProduct, dotProduct_sub] at e0 ⊢
        linear_combination e0
      rw [e1, AddChar.map_neg_eq_inv, H γ₀ h1 h2, inv_one]
  have h0 : ι φ 0 ≠ 0 := by
    have : ι φ ≠ 0 := fun e => hne (hι.bij.2.1 hs (zero_mem _) (by rw [e, map_zero]))
    obtain ⟨Y, hY⟩ := Function.ne_iff.1 this
    obtain ⟨x, hx, hx0, rfl⟩ := sur Y
    rwa [← k3 x (k2 x hx hx0 (k1 x hx hx0 hY)) hx0]
  refine ⟨ι φ 0, h0, funext fun Y => ?_⟩
  obtain ⟨x, hx, hx0, rfl⟩ := sur Y
  have hi := int x hx hx0 ⟨fun H => k1 x hx hx0 (by rwa [k3 x H hx0]), k2 x hx hx0⟩
  by_cases H : x ∈ latAtV X W v
  · rw [k3 x H hx0, Pi.smul_apply, intInd, Set.indicator_of_mem (hi.1 H), Pi.one_apply, smul_eq_mul, mul_one]
  · rw [Pi.smul_apply, intInd, Set.indicator_of_notMem (fun e => H (hi.2 e)), smul_zero]
    by_contra h1
    exact H (k2 x hx hx0 (k1 x hx hx0 h1))

theorem grams {B : Base F E} (h : IsSec σ t sec) {r s r' s' : ℕ} (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') :
    Grams σ t (incM F X.J) (incM F W.J) := by
  have uu : ∀ {m : ℕ} {J : Matrix (Fin m) (Fin m) E}, IsUnit J.det → IsUnit ((incM F J).map (piW t)) := fun {m J} hJ => by
    rw [incM_map h]
    exact ((Matrix.isUnit_iff_isUnit_det J).2 hJ).map (t : E →+* Fv F v).mapMatrix
  exact ⟨uu (Vac.herm_det hX), uu (Vac.skew_det hW), 1, one_mul _, Matrix.ext fun i j => by
      simp [incM, (h.inc _).1, (h.inc _).2, hX.herm], Matrix.ext fun i j => by simp [incM, (h.inc _).1, (h.inc _).2, hW.skew]⟩

theorem cancel_lr (Y : Matrix (Fin n) (Fin d) (Fv F v)) : (b⁻¹).1 * (b.1 * Y * c.1ᵀ) * (c⁻¹).1ᵀ = Y := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, ← transpose_mul, Units.inv_mul,
    transpose_one, Matrix.mul_one]

theorem cancel_rl (Y : Matrix (Fin n) (Fin d) (Fv F v)) : b.1 * ((b⁻¹).1 * Y * (c⁻¹).1ᵀ) * c.1ᵀ = Y :=
  cancel_lr (b := b⁻¹) (c := c⁻¹) Y

theorem vacuum_image_intertwiner {B : Base F E} (hB : B.IsGood σ) {r s r' s' : ℕ} (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') {φ}
    (hφ : M.IsVac B.ψ v φ) (hb : IsSplitBasis t X.L b) (hc : IsSplitBasis t W.L c) {ι} (hι : M.IsLinW B.ψ t b c ι) :
    ∃ c : ℂ, c ≠ 0 ∧ ι φ = c • intInd v := by
  obtain ⟨⟨sec, h⟩, -⟩ := section_statement F E σ hB.cm v t
  obtain ⟨e, e1, e2, e3⟩ := lat_idem hB.cm X W t
  refine vac_ind hB hX hW hφ hι (fun u u' hu h0 => hTens_zero h hu h0) (fun γ hγ => ⟨γ - e • γ, sub_mem hγ (e3 γ hγ), ?_, ?_⟩)
    (fun Y => ⟨secM sec (b.1 * Y * c.1ᵀ) 0, h.atM _ _, h.sndM _ _, ?_⟩) fun x hx h0 _ => ⟨lat_to h hb hc, fun H => ?_⟩
  · rw [Matrix.map_sub _ (map_sub _), map_smul_ring, e1, one_smul, sub_self]
  · rw [sub_sub_cancel, map_smul_ring, e2, zero_smul]
  · rw [h.fstM, cancel_lr]
  · obtain ⟨γ, hγ, h1, h2⟩ := lat_from hB.cm h hb hc H
    rw [cancel_rl] at h1
    rwa [h.extM (hx.kd_sub ((GlobalTheory.LatVac.latAtV_at_stable X W v).1 γ hγ)) h1.symm (h0.trans h2.symm)]

theorem vac_Bar {B : Base F E} (hB : B.IsGood σ) {r s r' s' : ℕ} (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') {φ}
    (hφ : M.IsVac B.ψ v φ) (hb : IsSplitBasis t X.L b) (hc : IsSplitBasis t W.L c) {δ : Fv F v}
    (hδ : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, psiLoc B.ψ v (x * y) = 1) ↔ δ * x ∈ v.adicCompletionIntegers F)
    {b' : GL (Fin n) (Fv F v)} (hb' : b'.1 = δ • b.1) {ι} (hι : M.IsLinBar B.ψ t b' c ι) :
    ∃ c : ℂ, c ≠ 0 ∧ ι φ = c • intInd v := by
  obtain ⟨⟨sec, h⟩, -⟩ := section_statement F E σ hB.cm v t
  obtain ⟨e, e1, e2, e3⟩ := lat_idem hB.cm X W t
  have hG := grams h hX hW
  have co : ∀ (p : Matrix (Fin n) (Fin n) (Fv F v)) (u : Matrix (Fin n) (Fin d) (AE F E)),
      -(pᵀ * X.J.map t * u.map (piW (t.comp σ)) * (W.J.map t)ᵀ * c.1) =
        pᵀ * toM (coord σ t (incM F X.J) (incM F W.J) u).1 * c.1 := fun p u => by
    rw [coord, incM_map h, incM_map h, toM_ofM, Matrix.mul_neg, Matrix.neg_mul]
    simp only [Matrix.mul_assoc]
  refine vac_ind hB hX hW hφ hι (fun u u' hu h0 => hTens_zero h hu h0.symm) (fun γ hγ => ⟨e • γ, e3 γ hγ, ?_, ?_⟩)
    (fun Y => ?_) fun x hx h0 H => H.trans ?_
  · rw [map_smul_ring, e2, zero_smul]
  · rw [Matrix.map_sub _ (map_sub _), map_smul_ring, e1, one_smul, sub_self]
  · obtain ⟨x, hx, h1, -⟩ := exists_coord h hG (ofM ((invT b').1 * Y * (c⁻¹).1), 0)
    refine ⟨x, hx, coord_snd.1 (congrArg Prod.snd h1), ?_⟩
    rw [co, h1, toM_ofM]
    exact (lrH (invT b') c⁻¹).left_inv Y
  · set C := b.1ᵀ * toM (coord σ t (incM F X.J) (incM F W.J) x).1 * c.1 with hC
    have sy : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) (Z : Matrix (Fin n) (Fin d) (Fv F v)), u.map (piW t) = b.1 * Z * c.1ᵀ →
        B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) x u) = psiV B.ψ v (ofM C ⬝ᵥ ofM (-Z)) := fun u Z hu => by
      rw [symp_eq h hG hx, coord_snd.2 h0, dotProduct_zero, sub_zero, ← ofM_toM (coord σ t (incM F X.J) (incM F W.J) x).1]
      change psiV B.ψ v (_ ⬝ᵥ ofM (-u.map (piW t))) = _
      rw [hu, dot_ofM, dot_ofM, hC, transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_neg, Matrix.mul_neg, trace_neg,
        trace_neg, Matrix.mul_assoc c.1ᵀ, trace_mul_comm c.1ᵀ]
      simp only [Matrix.mul_assoc]
    have e : -(b'.1ᵀ * X.J.map t * x.map (piW (t.comp σ)) * (W.J.map t)ᵀ * c.1) = δ • C := by
      rw [co, hb', transpose_smul, Matrix.smul_mul, Matrix.smul_mul]
    refine Iff.trans ?_ (show IsInt (δ • C) ↔ _ by rw [e])
    refine ⟨fun H i j => (hδ (C i j)).1 fun y hy => ?_, fun H u hu _ => ?_⟩
    · obtain ⟨u, hu, h1, h2⟩ := lat_from hB.cm h hb hc (Y := -Matrix.single i j y) fun i' j' => neg_mem (by
        rw [Matrix.single, of_apply]
        split_ifs
        exacts [hy, zero_mem _])
      have := H u hu h2
      rw [sy u _ h1, neg_neg, dot_ofM, trace_mul_single] at this
      exact (by simpa using this : psiV B.ψ v (C i j * y) = 1)
    · rw [sy u _ (cancel_rl _).symm]
      refine Finset.sum_induction _ (fun a => psiV B.ψ v a = 1) (fun a a' ha ha' => by rw [AddChar.map_add_eq_mul, ha, ha', one_mul])
        (AddChar.map_zero_eq_one _) fun p _ => (hδ (C p.1 p.2)).2 (H p.1 p.2) _ (neg_mem (lat_to h hb hc hu p.1 p.2))

theorem dictX : DictX := dictX_of model_existence cyclicity adjoint_statement section_statement action_uniqueness

def inB {m : ℕ} {J : Matrix (Fin m) (Fin m) E} (t : E →ₐ[F] Fv F v) (b : GL (Fin m) (Fv F v)) (g : UA σ J) : GL (Fin m) (Fv F v) :=
  b⁻¹ * GeneralLinearGroup.map (piW t) g.1 * b

theorem rescale {ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)} {P : GL (Fin n) (Fv F v)}
    {Q : GL (Fin d) (Fv F v)} {φ} {a : ℂ} (ha : a ≠ 0) (h : chg P Q 1 ι φ = a • intInd v) : chg P Q a⁻¹ ι φ = intInd v :=
  funext fun Y => by
    have := congrFun h Y
    rw [chg_apply, one_mul] at this
    rw [chg_apply, this, Pi.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ ha]

theorem model_Bar {B : Base F E} (hB : B.IsGood σ) {r s r' s' : ℕ} (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    (hφ : M.IsVac B.ψ v (M.vac v)) {χX χW : Chr F E} {om : Rep σ X W} (hom : M.IsWeil B.ψ χX χW om)
    (hb : IsSplitBasis t X.L b) (hc : IsSplitBasis t W.L c) {δ : Fv F v}
    (hδ : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, psiLoc B.ψ v (x * y) = 1) ↔ δ * x ∈ v.adicCompletionIntegers F)
    {b' : GL (Fin n) (Fv F v)} (hb' : b'.1 = δ • b.1) : ∃ ι, M.IsLinBar B.ψ t b' c ι ∧ ι (M.vac v) = intInd v ∧
      (∀ g ∈ UAt σ X (evFin F v), Reads v ι (om (g, 1)) (omB (chrW χW t) (chrW χX t) (inB t b' g) 1)) ∧
      ∀ h ∈ UAt σ W (evFin F v), Reads v ι (om (1, h)) (omB (chrW χW t) (chrW χX t) 1 (inB t c h)) := by
  obtain ⟨⟨ι, hι⟩, -, -, k⟩ := dictX F E σ n d B X W M om χX χW hB ⟨_, _, hX⟩ ⟨_, _, hW⟩ hom v t
  have lin : ∀ a : ℂ, a ≠ 0 → M.IsLinBar B.ψ t b' c (chg (invT b') c⁻¹ a ι) := fun a ha => lin_chg hι _ _ ha fun u => by
    simp only [invT_val, Units.val_one, transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_assoc, Units.mul_inv]
    rw [← Matrix.mul_assoc, ← transpose_mul, Units.mul_inv, transpose_one, Matrix.one_mul]
  obtain ⟨a, ha, e⟩ := vac_Bar hB hX hW hφ hb hc hδ hb' (lin 1 one_ne_zero)
  refine ⟨_, lin _ (inv_ne_zero ha), rescale ha e, fun g hg => reads_chg ((k ι hι).1 g hg (GeneralLinearGroup.map (piW t) g.1) rfl)
    fun Φ Y => B_left _ Φ Y ?_ (gdet_conj _ _).symm, fun g hg => reads_chg ((k ι hι).2 g hg (GeneralLinearGroup.map (piW t) g.1) rfl)
    fun Φ Y => B_right _ Φ Y ?_ (gdet_conj _ _).symm⟩
  · rw [invT_val, ← transpose_mul, ← transpose_mul, ← Units.val_mul, ← Units.val_mul, inB, mul_inv_cancel_right]
  · rw [← Units.val_mul, ← Units.val_mul, inB, mul_inv_cancel_right]

theorem model_alt {B : Base F E} (hB : B.IsGood σ) {r s r' s' : ℕ} (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    (hφ : M.IsVac B.ψ v (M.vac v)) {χX χW : Chr F E} {om : Rep σ X W} (hom : M.IsWeil B.ψ χX χW om)
    (hb : IsSplitBasis t X.L b) (hc : IsSplitBasis t W.L c) {ν β : (Fv F v)ˣ →* ℂˣ} (hν : chrW χW (t.comp σ) = ν)
    (hβ : ∀ x, chrW χX (t.comp σ) x = (β x)⁻¹) : ∃ ι, M.IsLinW B.ψ t b c ι ∧ ι (M.vac v) = intInd v ∧
      (∀ g ∈ UAt σ X (evFin F v), Reads v ι (om (g, 1)) (omA ν β (inB t b g) 1)) ∧
      ∀ h ∈ UAt σ W (evFin F v), Reads v ι (om (1, h)) (omA ν β 1 (inB t c h)) := by
  obtain ⟨⟨ι, hι⟩, -, -, k⟩ := dictX F E σ n d B X W M om χX χW hB ⟨_, _, hX⟩ ⟨_, _, hW⟩ hom v (t.comp σ)
  obtain ⟨⟨sec, h⟩, -⟩ := section_statement F E σ hB.cm v (t.comp σ)
  have hG := grams h hX hW
  obtain ⟨A, hA⟩ := hG.uA
  obtain ⟨D, hD⟩ := hG.uB
  have rel : ∀ {m : ℕ} {J : Matrix (Fin m) (Fin m) E} {U : GL (Fin m) (Fv F v)}, U.1 = (incM F J).map (piW (t.comp σ)) →
      ∀ g : UA σ J, (invT (GeneralLinearGroup.map (piW (t.comp σ)) g.1))⁻¹ * U * GeneralLinearGroup.map (piW t) g.1 = U :=
    fun {m J U} hU g => Units.ext (by
      have := h.unit_rel g
      rw [comp_comp hB.cm, ← hU] at this
      exact this)
  have hι' := hι
  unfold Model.IsLinBar at hι'
  rw [comp_comp hB.cm, ← incM_map h, ← incM_map h, ← hA, ← hD] at hι'
  have lin : ∀ a : ℂ, a ≠ 0 → M.IsLinW B.ψ t b c (chg (-(A * b)) (invT (D * c))⁻¹ a ι) := fun a ha =>
    lin_chg hι' _ _ ha fun u => by
      simp only [invT_inv_val, Units.val_neg, Units.val_mul, transpose_mul, Units.val_one, transpose_one, Matrix.one_mul,
        Matrix.mul_one, Matrix.neg_mul]
      rw [Matrix.mul_assoc A.1, ← Matrix.mul_assoc, Matrix.mul_assoc A.1, cancel_rl]
  obtain ⟨a, ha, e⟩ := vacuum_image_intertwiner hB hX hW hφ hb hc (lin 1 one_ne_zero)
  subst hν
  refine ⟨_, lin _ (inv_ne_zero ha), rescale ha e, fun g hg =>
    reads_chg ((k ι hι).1 g hg (GeneralLinearGroup.map (piW (t.comp σ)) g.1) rfl)
    fun Φ Y => A_left _ Φ Y ?_ ((gdet_rel (rel hA g)).trans (congrArg _ (gdet_conj _ _).symm)), fun g hg =>
    reads_chg ((k ι hι).2 g hg (GeneralLinearGroup.map (piW (t.comp σ)) g.1) rfl)
    fun Φ Y => A_right _ Φ Y ?_ ((gdet_rel (rel hD g)).trans (congrArg _ (gdet_conj _ _).symm)) hβ⟩
  · rw [← invT_inv_val, ← Units.val_mul, ← Units.val_mul, inB, mul_neg, neg_mul, ← mul_assoc,
      eq_mul_inv_of_mul_eq (rel hA g)]
    congr 2
    group
  · have e1 := congrArg invT (rel hD g)
    rw [map_mul, map_mul, map_inv, invT_invT, mul_assoc, inv_mul_eq_iff_eq_mul, ← mul_inv_eq_iff_eq_mul] at e1
    rw [← Units.val_mul, ← Units.val_mul, ← e1]
    simp only [inB, map_mul, map_inv]
    congr 1
    group

theorem split_place_dictionary : Dict := by
  intro F E _ _ _ _ _ σ B a a' G X om om' T v τ
  have hB := T.base
  obtain ⟨b, b₀, b', c, δ, hb, hb₀, hc, hδ, hb', hP⟩ : ∃ (b : GL (Fin a) (Fv F v)) (b₀ b' : GL (Fin a') (Fv F v))
      (c : GL (Fin (a + a')) (Fv F v)) (δ : Fv F v), IsSplitBasis τ G.V.L b ∧ IsSplitBasis τ G.V'.L b₀ ∧ IsSplitBasis τ G.W.L c ∧
      (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, psiLoc B.ψ v (x * y) = 1) ↔ δ * x ∈ v.adicCompletionIntegers F) ∧
      b'.1 = δ • b₀.1 ∧ ∀ hv : v ∈ B.P, τ = B.τ ⟨v, hv⟩ → b = G.V.bas v ∧ b' = G.V'.bas v ∧ c = G.W.bas v := by
    by_cases H : ∃ hv : v ∈ B.P, τ = B.τ ⟨v, hv⟩
    · obtain ⟨hv, rfl⟩ := H
      exact ⟨_, _, _, _, 1, T.geo.hV.bas ⟨v, hv⟩, T.geo.hV'.bas ⟨v, hv⟩, T.geo.hW.bas ⟨v, hv⟩,
        fun x => by rw [one_mul]; exact hB.psiP v hv x, (one_smul _ _).symm, fun _ _ => ⟨rfl, rfl, rfl⟩⟩
    · have := T.geo.hV.lat
      have := T.geo.hV'.lat
      have := T.geo.hW.lat
      obtain ⟨b, hb⟩ := exists_isSplitBasis τ G.V.L hB.cm
      obtain ⟨b₀, hb₀⟩ := exists_isSplitBasis τ G.V'.L hB.cm
      obtain ⟨c, hc⟩ := exists_isSplitBasis τ G.W.L hB.cm
      obtain ⟨δ, hδ⟩ := exists_cond hB.std v
      exact ⟨b, b₀, δ • b₀, c, δ, hb, hb₀, hc, hδ, rfl, fun hv e => absurd ⟨hv, e⟩ H⟩
  obtain ⟨ι, l1, v1, g1, h1⟩ := model_alt hB T.geo.hV T.geo.hW (T.geo.hM.vac v) T.weil hb hc (ν := chrW X.ν τ) (β := chrW X.β τ)
    (MonoidHom.ext fun x => by
      rw [chrW_div, chrW_conj hB.cm τ T.chars.resα, chrW_conj hB.cm τ T.chars.resβ, Chars.ν, chrW_div, inv_div_inv])
    (chrW_conj hB.cm τ T.chars.resβ)
  obtain ⟨ι', l2, v2, g2, h2⟩ := model_Bar hB T.geo.hV' T.geo.hW (T.geo.hM'.vac v) T.weil' hb₀ hc hδ hb'
  refine ⟨b, b', c, ι, ι', inB τ b, inB τ b', inB τ c, l1, l2, hP, v1, v2, g1, h1, g2, h2, fun x => ?_⟩
  obtain ⟨-, -, k, -⟩ := dictX F E σ _ _ B _ _ G.M om _ _ hB ⟨_, _, T.geo.hV⟩ ⟨_, _, T.geo.hW⟩ T.weil v τ
  obtain ⟨h, hh, e⟩ := k (c * x * c⁻¹)
  refine ⟨h, hh, ?_⟩
  rw [inB, show GeneralLinearGroup.map (piW τ) h.1 = c * x * c⁻¹ from Units.ext e]
  group

end PositivityTheory.ThK.SplitDict
