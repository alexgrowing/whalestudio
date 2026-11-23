import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksSubOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLinearOfBilinearSchwartzBruhatProduct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanSchwartzBruhatProductEqTop
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilInertPlaceVacuumEigenfunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotallyDisconnectedProductLocallyCompactStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.DblLin

open Matrix

def schrLin {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w : (κ → R) × (κ → R)) : ((κ → R) → ℂ) →ₗ[ℂ] ((κ → R) → ℂ) where
  toFun := schr ψ w
  map_add' f g := by funext x; simp only [schr, Pi.add_apply, mul_add]
  map_smul' a f := by funext x; simp only [schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def conjLin {Y Y' : Type} (ι : (Y → ℂ) →ₗ[ℂ] (Y' → ℂ)) : (Y → ℂ) →ₗ[ℂ] (Y' → ℂ) where
  toFun φ := star (ι (star φ))
  map_add' f g := by rw [star_add, map_add, star_add]
  map_smul' a f := by rw [star_smul, map_smul, star_smul, star_star]; rfl

theorem star_mem_SB {Y : Type} [TopologicalSpace Y] {f : Y → ℂ} (hf : f ∈ SB Y) : star f ∈ SB Y :=
  ⟨hf.1.comp star, hf.2.comp_left (g := star) (star_zero ℂ)⟩

theorem conjLin_bijOn {Y Y' : Type} [TopologicalSpace Y] [TopologicalSpace Y'] (ι : (Y → ℂ) →ₗ[ℂ] (Y' → ℂ))
    (h : Set.BijOn ι (SB Y : Set (Y → ℂ)) (SB Y' : Set (Y' → ℂ))) :
    Set.BijOn (conjLin ι) (SB Y : Set (Y → ℂ)) (SB Y' : Set (Y' → ℂ)) := by
  refine ⟨fun φ hφ => star_mem_SB (h.mapsTo (star_mem_SB hφ)), fun φ hφ φ' hφ' e => ?_, fun g hg => ?_⟩
  · have e' : ι (star φ) = ι (star φ') := star_injective e
    exact star_injective (h.injOn (star_mem_SB hφ) (star_mem_SB hφ') e')
  · obtain ⟨φ, hφ, e⟩ := h.surjOn (star_mem_SB hg)
    refine ⟨star φ, star_mem_SB hφ, ?_⟩
    show star (ι (star (star φ))) = g
    rw [star_star, e, star_star]

def colsHomeo (m a b k : Type) [TopologicalSpace k] :
    Matrix m (a ⊕ b) k ≃ₜ Matrix m a k × Matrix m b k where
  toFun Y := (Y.submatrix id Sum.inl, Y.submatrix id Sum.inr)
  invFun p := Matrix.fromCols p.1 p.2
  left_inv Y := by ext i (j | j) <;> rfl
  right_inv p := by ext <;> rfl
  continuous_toFun := (continuous_id.matrix_submatrix _ _).prodMk (continuous_id.matrix_submatrix _ _)
  continuous_invFun := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    rcases j with j | j
    · exact (continuous_apply_apply i j).comp continuous_fst
    · exact (continuous_apply_apply i j).comp continuous_snd

theorem eqOn_SB_of_box {k : Type} [TopologicalSpace k] [T2Space k] [LocallyCompactSpace k] [TotallyDisconnectedSpace k]
    {κ : Type} [Fintype κ] {N : Type} [AddCommGroup N] [Module ℂ N] (L₁ L₂ : ((κ ⊕ κ → k) → ℂ) →ₗ[ℂ] N)
    (h : ∀ a ∈ SB (κ → k), ∀ b ∈ SB (κ → k), L₁ (boxFun a b) = L₂ (boxFun a b)) :
    ∀ φ ∈ SB (κ ⊕ κ → k), L₁ φ = L₂ φ := by
  intro φ hφ
  let e : (κ ⊕ κ → k) ≃ₜ (κ → k) × (κ → k) := Homeomorph.sumArrowHomeomorphProdArrow
  let M₁ : GlobalTheory.SplitWeil.SB ((κ → k) × (κ → k)) →ₗ[ℂ] N :=
    L₁ ∘ₗ (SB (κ ⊕ κ → k)).subtype ∘ₗ GlobalTheory.LocFlat.CFac.comapH e
  let M₂ : GlobalTheory.SplitWeil.SB ((κ → k) × (κ → k)) →ₗ[ℂ] N :=
    L₂ ∘ₗ (SB (κ ⊕ κ → k)).subtype ∘ₗ GlobalTheory.LocFlat.CFac.comapH e
  have hM : M₁ = M₂ := LinearMap.ext_on_range (GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top _ _)
    fun q => h q.1.1 q.1.2 q.2.1 q.2.2
  have := LinearMap.congr_fun hM (GlobalTheory.LocFlat.CFac.comapH e.symm ⟨φ, hφ⟩)
  have e2 : ((GlobalTheory.LocFlat.CFac.comapH e (GlobalTheory.LocFlat.CFac.comapH e.symm ⟨φ, hφ⟩)).1 : (κ ⊕ κ → k) → ℂ) = φ := by
    funext x
    simp only [GlobalTheory.LocFlat.CFac.comapH_apply, Homeomorph.symm_apply_apply]
  simp only [M₁, M₂, LinearMap.comp_apply, Submodule.subtype_apply] at this
  rw [← e2]
  exact this

theorem coord_inl {m k : Type} [Fintype m] [DecidableEq m] [Field k] {d : ℕ} (B : Matrix m m k)
    (A : Matrix m (Fin d ⊕ Fin d) k) (c : GL (Fin d) k) :
    (B * A * ((GlobalTheory.DblScal.dsum c)⁻¹).valᵀ).submatrix id Sum.inl = B * A.toCols₁ * (c⁻¹).valᵀ := by
  have e : ((GlobalTheory.DblScal.dsum c)⁻¹).val = Matrix.fromBlocks (c⁻¹).val 0 0 (c⁻¹).val := rfl
  conv_lhs => rw [e, fromBlocks_transpose, ← Matrix.fromCols_toCols A, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks]
  ext i j
  simp

theorem coord_inr {m k : Type} [Fintype m] [DecidableEq m] [Field k] {d : ℕ} (B : Matrix m m k)
    (A : Matrix m (Fin d ⊕ Fin d) k) (c : GL (Fin d) k) :
    (B * A * ((GlobalTheory.DblScal.dsum c)⁻¹).valᵀ).submatrix id Sum.inr = B * A.toCols₂ * (c⁻¹).valᵀ := by
  have e : ((GlobalTheory.DblScal.dsum c)⁻¹).val = Matrix.fromBlocks (c⁻¹).val 0 0 (c⁻¹).val := rfl
  conv_lhs => rw [e, fromBlocks_transpose, ← Matrix.fromCols_toCols A, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks]
  ext i j
  simp

theorem dblLin : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ dd : GlobalTheory.DblScal.DblCo σ X W, IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
    ∃ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd ∧
      ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₂ ∈ SB (Fin n × Fin d → Fv F v),
        ιd (boxFun φ₁ φ₂) = fun Y => ι φ₁ (Y.submatrix id Sum.inl) *
          starRingEnd ℂ (ι (fun x => starRingEnd ℂ (φ₂ x)) (Y.submatrix id Sum.inr)) := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair v t b c ι hι dd hdd
  classical
  have hψ1 : ∀ x, ‖B.ψ x‖ = 1 := GlobalTheory.StdCharFromIsStd.norm_psi hpair.base.std
  have hψc : Continuous B.ψ := hpair.base.std.1
  have hψv : ∀ x, ‖GlobalTheory.LatVac.psiAt B.ψ v x‖ = 1 := fun x => hψ1 _
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin d) (Fv F v)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin d → Fv F v))
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin d) (Fv F v)) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin d → Fv F v))
  obtain ⟨ιd, hbij, hprod⟩ := GlobalTheory.T.totally_disconnected_product_locally_compact (Homeomorph.sumArrowHomeomorphProdArrow (X := Fv F v)
    (ι := Fin n × Fin d) (ι' := Fin n × Fin d)) (colsHomeo (Fin n) (Fin d) (Fin d) (Fv F v)) ι (conjLin ι) hι.bij
    (conjLin_bijOn ι hι.bij)
  have hbox : ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₂ ∈ SB (Fin n × Fin d → Fv F v),
      ιd (boxFun φ₁ φ₂) = fun Y => ι φ₁ (Y.submatrix id Sum.inl) * star (ι (star φ₂) (Y.submatrix id Sum.inr)) :=
    fun φ₁ h₁ φ₂ h₂ => hprod φ₁ h₁ φ₂ h₂

  have hsplit : ∀ u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E),
      GlobalTheory.LatVac.locCo dd v u = (Sum.elim (GlobalTheory.LatVac.locCo M.co v u.toCols₁).1 (GlobalTheory.LatVac.locCo M.co v u.toCols₂).1,
        Sum.elim (GlobalTheory.LatVac.locCo M.co v u.toCols₁).2 (-(GlobalTheory.LatVac.locCo M.co v u.toCols₂).2)) := by
    intro u
    have e := hdd u.toCols₁ u.toCols₂
    rw [Matrix.fromCols_toCols] at e
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · rcases k with k | k <;>
        simp [GlobalTheory.LatVac.locCo, e]
    · rcases k with k | k <;>
        simp [GlobalTheory.LatVac.locCo, e]
  have hat1 : ∀ u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E), At (evFin F v) u → At (evFin F v) u.toCols₁ :=
    fun u hu a ha => Matrix.ext fun i j => congrFun (congrFun (hu a ha) i) (Sum.inl j)
  have hat2 : ∀ u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E), At (evFin F v) u → At (evFin F v) u.toCols₂ :=
    fun u hu a ha => Matrix.ext fun i j => congrFun (congrFun (hu a ha) i) (Sum.inr j)
  have hmap1 : ∀ (u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) (π : AE F E →+* Fv F v), u.map π = 0 →
      u.toCols₁.map π = 0 := fun u π h => Matrix.ext fun i j => congrFun (congrFun h i) (Sum.inl j)
  have hmap2 : ∀ (u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) (π : AE F E →+* Fv F v), u.map π = 0 →
      u.toCols₂.map π = 0 := fun u π h => Matrix.ext fun i j => congrFun (congrFun h i) (Sum.inr j)
  have hc1 : ∀ (u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) (π : AE F E →+* Fv F v), (u.map π).toCols₁ = u.toCols₁.map π :=
    fun u π => rfl
  have hc2 : ∀ (u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) (π : AE F E →+* Fv F v), (u.map π).toCols₂ = u.toCols₂.map π :=
    fun u π => rfl

  have hloc : ∀ u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E), At (evFin F v) u →
      ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), ∀ φ₁, Acts (evFin F v) (dd.rho B.ψ u) φ φ₁ →
        φ₁ = schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v u) φ := fun u hu φ hφ φ₁ hA =>
    GlobalTheory.TensUniq.eq_of_tens_eq v φ _ _ hφ fun r hr =>
      (hA r hr).symm.trans (GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v u hu φ r hr)

  have hschr : ∀ u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E), ∀ a ∈ SB (Fin n × Fin d → Fv F v),
      ∀ b' ∈ SB (Fin n × Fin d → Fv F v),
      ιd (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v u) (boxFun a b')) = fun Y =>
        ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u.toCols₁) a) (Y.submatrix id Sum.inl) *
          star (ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u.toCols₂) (star b'))
            (Y.submatrix id Sum.inr)) := by
    intro u a ha b' hb
    have e0 : boxFun a b' = boxFun a (fun x => star ((star b') x)) := by
      funext x; simp [boxFun]
    rw [hsplit u, e0, GlobalTheory.DblVacLine.schr_box _ hψv]
    rw [hbox _ (GlobalTheory.SchrSB.schr_mem_SB B.ψ hψc v _ a ha)
      (fun x => star (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u.toCols₂) (star b') x))
      (star_mem_SB (GlobalTheory.SchrSB.schr_mem_SB B.ψ hψc v _ _ (star_mem_SB hb)))]
    have e1 : (star fun x => star (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u.toCols₂) (star b') x)) =
        schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u.toCols₂) (star b') := by
      funext x; simp
    rw [e1]
  refine ⟨ιd, ⟨hbij, ?_, ?_⟩, hbox⟩
  · intro u hu hu0 φ hφ φ₁ hφ₁ hA Y
    rw [hloc u hu φ hφ φ₁ hA]
    set sh := (b⁻¹).val * u.map (piW t) * ((GlobalTheory.DblScal.dsum c)⁻¹).valᵀ
    have key := eqOn_SB_of_box (ιd ∘ₗ schrLin (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v u))
      (LinearMap.funLeft ℂ ℂ (fun Y => Y + sh) ∘ₗ ιd) (fun a ha b' hb => ?_) φ hφ
    · exact congrFun key Y
    show ιd (schr _ _ (boxFun a b')) = fun Y => ιd (boxFun a b') (Y + sh)
    rw [hschr u a ha b' hb, hbox a ha b' hb]
    funext Y
    have t1 := hι.trans u.toCols₁ (hat1 u hu) (hmap1 u _ hu0) a ha _ (GlobalTheory.SchrSB.schr_mem_SB B.ψ hψc v _ a ha)
      (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v _ (hat1 u hu) a) (Y.submatrix id Sum.inl)
    have t2 := hι.trans u.toCols₂ (hat2 u hu) (hmap2 u _ hu0) _ (star_mem_SB hb) _
      (GlobalTheory.SchrSB.schr_mem_SB B.ψ hψc v _ _ (star_mem_SB hb))
      (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v _ (hat2 u hu) _) (Y.submatrix id Sum.inr)
    have s1 : (Y + sh).submatrix id Sum.inl = Y.submatrix id Sum.inl + (b⁻¹).1 * u.toCols₁.map (piW t) * (c⁻¹).1ᵀ := by
      rw [show (Y + sh).submatrix id Sum.inl = Y.submatrix id Sum.inl + sh.submatrix id Sum.inl from rfl, coord_inl, hc1]
    have s2 : (Y + sh).submatrix id Sum.inr = Y.submatrix id Sum.inr + (b⁻¹).1 * u.toCols₂.map (piW t) * (c⁻¹).1ᵀ := by
      rw [show (Y + sh).submatrix id Sum.inr = Y.submatrix id Sum.inr + sh.submatrix id Sum.inr from rfl, coord_inr, hc2]
    rw [t1, t2]
    beta_reduce
    rw [s1, s2]
  · intro u hu hu0 φ hφ φ₁ hφ₁ hA x hx hx0
    rw [hloc u hu φ hφ φ₁ hA]
    set P := (b⁻¹).val * x.map (piW t) * ((GlobalTheory.DblScal.dsum c)⁻¹).valᵀ
    set z := B.ψ (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J)) x u)
    have key := eqOn_SB_of_box (LinearMap.proj P ∘ₗ ιd ∘ₗ schrLin (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v u))
      (z • (LinearMap.proj P ∘ₗ ιd)) (fun a ha b' hb => ?_) φ hφ
    · exact key
    show ιd (schr _ _ (boxFun a b')) P = z * ιd (boxFun a b') P
    rw [hschr u a ha b' hb, hbox a ha b' hb]
    have p1 : P.submatrix id Sum.inl = (b⁻¹).1 * x.toCols₁.map (piW t) * (c⁻¹).1ᵀ := by
      rw [coord_inl, hc1]
    have p2 : P.submatrix id Sum.inr = (b⁻¹).1 * x.toCols₂.map (piW t) * (c⁻¹).1ᵀ := by
      rw [coord_inr, hc2]
    have m1 := hι.mult u.toCols₁ (hat1 u hu) (hmap1 u _ hu0) a ha _ (GlobalTheory.SchrSB.schr_mem_SB B.ψ hψc v _ a ha)
      (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v _ (hat1 u hu) a) x.toCols₁ (hat1 x hx) (hmap1 x _ hx0)
    have m2 := hι.mult u.toCols₂ (hat2 u hu) (hmap2 u _ hu0) _ (star_mem_SB hb) _
      (GlobalTheory.SchrSB.schr_mem_SB B.ψ hψc v _ _ (star_mem_SB hb))
      (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v _ (hat2 u hu) _) x.toCols₂ (hat2 x hx) (hmap2 x _ hx0)
    beta_reduce
    rw [p1, p2, m1, m2]
    have hs : symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J)) x u =
        symp (cA σ) (-1) (incM F X.J) (incM F W.J) x.toCols₁ u.toCols₁ -
          symp (cA σ) (-1) (incM F X.J) (incM F W.J) x.toCols₂ u.toCols₂ := by
      conv_lhs => rw [← Matrix.fromCols_toCols x, ← Matrix.fromCols_toCols u]
      exact GlobalTheory.DblVacLine.symp_dbl _ _ _ _ _ _ _ _
    have hz : z = B.ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) x.toCols₁ u.toCols₁) *
        star (B.ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) x.toCols₂ u.toCols₂)) := by
      rw [GlobalTheory.DblVacLine.star_eq_neg B.ψ hψ1, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← hs]
    rw [hz, star_mul]
    ring

end GlobalTheory.DblLin
