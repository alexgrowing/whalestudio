import Formalism.LocalRingCardinality.SpanPowerMembership.ThetaFullColIsom
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.Inhab NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] Classical.propDecidable

variable (D : D7)

abbrev HG : Type := WithLp 2 (HR D × WithLp 2 (HC D × ℂ))

def rowJ (μ : D.what₂.Tup) (j : ℕ) : D.what₂.Mult μ j →ₗ[ℂ] HG D :=
  (WithLp.linearEquiv 2 ℂ (HR D × WithLp 2 (HC D × ℂ))).symm.toLinearMap.comp
    ((LinearMap.inl ℂ (HR D) (WithLp 2 (HC D × ℂ))).comp
      (lp.lsingle (𝕜 := ℂ) (E := fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) 2 ⟨μ, j⟩))

def rowQ (μ : D.what₂.Tup) (j : ℕ) : HG D →ₗ[ℂ] D.what₂.Mult μ j :=
  (lp.evalₗ (𝕜 := ℂ) (fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) 2 ⟨μ, j⟩).comp
    (WithLp.fstₗ 2 ℂ (HR D) (WithLp 2 (HC D × ℂ)))

def colJ (u : D.what₂.Word) : D.what₂.Mu u →ₗ[ℂ] HG D :=
  (WithLp.linearEquiv 2 ℂ (HR D × WithLp 2 (HC D × ℂ))).symm.toLinearMap.comp
    ((LinearMap.inr ℂ (HR D) (WithLp 2 (HC D × ℂ))).comp
      ((WithLp.linearEquiv 2 ℂ (HC D × ℂ)).symm.toLinearMap.comp
        ((LinearMap.inl ℂ (HC D) ℂ).comp (lp.lsingle (𝕜 := ℂ) (E := fun u : D.what₂.Word => D.what₂.Mu u) 2 u))))

def v0 : HG D := WithLp.toLp 2 (0, WithLp.toLp 2 (0, 1))

theorem v0_ne : v0 D ≠ 0 := fun h => by
  have := congrArg (fun x : HG D => x.snd.snd) h
  exact one_ne_zero this

theorem rowQ_rowJ (μ j) (x : D.what₂.Mult μ j) : rowQ D μ j (rowJ D μ j x) = x :=
  lp.single_apply_self (E := fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) 2 ⟨μ, j⟩ x

theorem inner_rowJ (μ j) (x : D.what₂.Mult μ j) (b : HG D) : inner ℂ (rowJ D μ j x) b = inner ℂ x (rowQ D μ j b) := by
  rw [WithLp.prod_inner_apply]
  show inner ℂ (lp.single (E := fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) 2 ⟨μ, j⟩ x) b.fst +
    inner ℂ (0 : WithLp 2 (HC D × ℂ)) b.snd = _
  rw [inner_zero_left, add_zero]
  exact lp.inner_single_left (G := fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) ⟨μ, j⟩ x b.fst

def toTopG {M : Type} [AddCommGroup M] [Module ℂ M] (f : M →ₗ[ℂ] HG D) : M →ₗ[ℂ] (⊤ : Submodule ℂ (HG D)) :=
  f.codRestrict ⊤ fun _ => Submodule.mem_top

def Zsp : HSp D := posSpace star_isIntegral 0

theorem ne_Zsp {V : HSp D} (h : 0 < V.rank) : V ≠ Zsp D := fun e => by
  rw [e] at h
  exact lt_irrefl 0 h

def thG (W : HSp D) : (HG D →ₗ[ℂ] HG D) →ₗ[ℂ] (⊤ : Submodule ℂ (HG D)) →ₗ[ℂ] HG D :=
  if W = Zsp D then 0 else LinearMap.lcomp ℂ (HG D) (⊤ : Submodule ℂ (HG D)).subtype

theorem thG_Z (Φ F) : thG D (Zsp D) Φ F = 0 := by
  unfold thG; rw [if_pos rfl]; rfl

theorem thG_pos {W : HSp D} (h : 0 < W.rank) (Φ F) : thG D W Φ F = Φ F := by
  unfold thG; rw [if_neg (ne_Zsp D h)]; rfl

def ysLow (t j : ℕ) : ℕ → HSp D
  | 0 => (tow D t).Ys j
  | _ + 1 => Zsp D

def thetaG : ThetaX D where
  AF := fun _ => HG D
  cusp := fun _ => ⊤
  pet := fun _ F G => inner ℂ F (G : HG D)
  pet_add_left := fun _ F F' G => inner_add_left _ _ _
  pet_smul_left := fun _ c F G => inner_smul_left _ _ _
  pet_right := fun _ F => ⟨fun G G' => inner_add_right _ _ _, fun c G => inner_smul_right _ _ _⟩
  pet_symm := fun _ F G => (inner_conj_symm (𝕜 := ℂ) (F : HG D) (G : HG D)).symm
  pet_pos := fun _ F hF => by
    have h1 : (F : HG D) ≠ 0 := fun h => hF (Subtype.ext h)
    show 0 < (inner ℂ (F : HG D) (F : HG D)).re
    have e := inner_self_eq_norm_sq (𝕜 := ℂ) (F : HG D)
    have e' : (inner ℂ (F : HG D) (F : HG D)).re = ‖(F : HG D)‖ ^ 2 := e
    rw [e']
    have := norm_pos_iff.mpr h1
    positivity
  actR := fun _ _ _ => 1
  actR_one := fun _ _ => rfl
  actR_mul := fun _ _ _ _ _ _ => (one_mul _).symm
  actR_cusp := fun _ _ _ _ _ _ => Submodule.mem_top
  Gf := fun _ => PUnit
  actF := fun _ => 1
  actF_cusp := fun _ _ _ _ => Submodule.mem_top
  actF_actR := fun _ _ _ _ => rfl
  Ksph := fun _ _ => ⊤
  Ksph_mono := fun _ _ _ _ => le_refl _
  typ := fun _ _ => ⊤
  Chr := Multiplicative (D.what₂.Tau → ℚ)
  infTy := fun χ τ => Multiplicative.toAdd χ τ
  infTy_mul := fun _ _ _ => rfl
  chrOf := fun _ j => Multiplicative.ofAdd (chrExp D j)
  chrOf_inf := fun _ j τ => by
    show chrExp D (j.1 + 1) τ = _
    unfold chrExp
    rw [dif_pos ⟨Nat.le_add_left _ _, j.2⟩]
    rfl
  etaT := Multiplicative.ofAdd fun _ => 1 / 2
  etaT_inf := fun _ => Or.inl rfl
  etaT_pos := fun _ => rfl
  Sch := fun _ _ => HG D →ₗ[ℂ] HG D
  fact := fun _ _ => Set.univ
  kfin := fun _ _ => ⊤
  th := fun _ W _ _ => thG D W
  Xs := fun t => (tow D t).Xs
  Xs_rank := fun t => (tow D t).Xs_rank
  Xs_sig := fun t => (tow D t).Xs_sig
  Ys := fun t => (tow D t).Ys
  Ys_rank := fun t => (tow D t).Ys_rank
  Ys_sig := fun t => (tow D t).Ys_sig
  iXYs := fun t => (tow D t).iXYs
  iXYs_isom := fun t => (tow D t).iXYs_isom
  iYXm := fun t => (tow D t).iYXm
  iYXm_isom := fun t => (tow D t).iYXm_isom
  YsLow := ysLow D
  YsLow_zero := fun _ _ => rfl
  Xs_rec := fun j _ => by rw [tow_rec]; rfl
  Ys_rec := fun j _ => by rw [tow_rec]; rfl
  conjAF := fun _ => cj (HG D)
  conjAF_add := fun _ => cj_add _
  conjAF_smul := fun _ => cj_smul _
  conjAF_conjAF := fun _ => cj_cj _
  conjAF_cusp := fun _ _ _ => Submodule.mem_top
  Pos := fun _ _ _ => PUnit
  FJd := fun _ _ _ => PUnit
  Bper := fun _ _ _ _ _ φ F => inner ℂ φ (F : HG D)
  Bper_right := fun _ _ _ _ _ φ => ⟨fun G G' => inner_add_right _ _ _, fun c G => inner_smul_right _ _ _⟩
  Bper_add_left := fun _ _ _ _ _ _ _ _ => inner_add_left _ _ _
  Bper_smul_left := fun _ _ _ _ _ _ _ _ => inner_smul_left _ _ _
  Bper_odd := fun _ _ _ _ _ _ _ _ _ => rfl
  Btop := fun _ _ _ φ F => inner ℂ φ (F : HG D)
  Btop_right := fun _ _ _ φ => ⟨fun G G' => inner_add_right _ _ _, fun c G => inner_smul_right _ _ _⟩
  Btop_add_left := fun _ _ _ _ _ _ => inner_add_left _ _ _
  Btop_smul_left := fun _ _ _ _ _ _ => inner_smul_left _ _ _
  pos1 := fun _ => PUnit.unit
  posSym := fun _ => PUnit.unit
  colAF := fun u _ _ => toTopG D (colJ D u)
  rowAF := fun μ j => toTopG D (rowJ D μ j)
  PhiY := fun μ j => (rowJ D μ j).comp ((D.what₂.io μ j).comp (rowQ D μ (j + 1)))
  PhiYup := fun _ _ => 0
  mY := fun _ _ => 1
  mY_pos := fun _ _ => one_pos
  adelicDataRowMeasureScale_trivialTuple := fun _ => rfl
  mY_zero := fun _ => rfl

theorem thetaG_mY (μ : D.what₂.Tup) (j : ℕ) : (((thetaG D).mY μ j : ℝ) : ℂ) = 1 := Complex.ofReal_one

theorem rankY_pos (t j : ℕ) (hj : j ≤ D.R.m) : 0 < ((tow D t).Ys j).rank := by
  rw [(tow D t).Ys_rank j hj]
  have := D.R.two_le_m
  unfold Ranks.r
  omega

theorem rankX_pos (t j : ℕ) (hj : j ≤ D.R.m) : 0 < ((tow D t).Xs j).rank := by
  rw [(tow D t).Xs_rank j hj]
  have := D.R.m_add_three_le_k
  omega

theorem spY_pos (j : ℕ) (hj : j ≤ D.R.m) : 0 < (D.sp.Y j).rank := by
  have := rankY_pos D D.R.t j hj
  rwa [tow_rec] at this

theorem spX_pos (j : ℕ) (hj : j ≤ D.R.m) : 0 < (D.sp.X j).rank := by
  have := rankX_pos D D.R.t j hj
  rwa [tow_rec] at this

theorem thetaG_row : (thetaG D).TieRowIsom := fun μ j _ x y => by
  unfold ThetaX.petY
  rw [thetaG_mY, one_mul]
  exact (inner_rowJ D μ j x (rowJ D μ j y)).trans (by rw [rowQ_rowJ])

theorem thetaG_io : (thetaG D).TieIo := fun μ j hj y x => by
  unfold ThetaX.petY ThetaX.dnY
  rw [thetaG_mY, thetaG_mY, one_mul, one_smul]
  show inner ℂ (thG D (D.sp.Y j) ((rowJ D μ j).comp ((D.what₂.io μ j).comp (rowQ D μ (j + 1))))
    (toTopG D (rowJ D μ (j + 1)) y)) (rowJ D μ j x) = _
  rw [thG_pos D (spY_pos D j hj.le)]
  show inner ℂ (rowJ D μ j (D.what₂.io μ j (rowQ D μ (j + 1) (rowJ D μ (j + 1) y)))) (rowJ D μ j x) = _
  rw [rowQ_rowJ, inner_rowJ, rowQ_rowJ]

theorem thetaG_rowTyp : Formalism.MainNotions.InnerProductFormulaField.TieRowTyp (thetaG D) := fun _ _ _ _ => trivial

theorem thetaG_typStable : Formalism.MainNotions.ZetaProductPairs.TypStable (thetaG D) := fun _ _ =>
  ⟨fun _ _ _ => trivial, fun _ _ _ _ _ => trivial⟩

theorem cj_ne {V : Type} [AddCommGroup V] [Module ℂ V] {v : V} (h : v ≠ 0) : cj V v ≠ 0 := fun e => h (by
  have := congrArg (cj V) e
  rw [cj_cj] at this
  rw [this]
  have h0 := cj_smul V 0 (0 : V)
  simpa using h0)

theorem inner_self_ne {v : HG D} (h : v ≠ 0) : inner ℂ v v ≠ 0 := inner_self_ne_zero.mpr h

theorem stableG (V : HSp D) (π : Submodule ℂ (HG D)) : (thetaG D).IsStable V π :=
  ⟨fun _ _ h => h, fun _ _ _ _ h => h⟩

def muOf (P : TPar D) (j : ℕ) : Multiplicative (D.what₂.Tau → ℚ) :=
  Multiplicative.ofAdd fun τ => if h : 1 ≤ j ∧ j ≤ D.R.m then -P.e τ ⟨j - 1, by omega⟩ else 0

theorem muOf_isMu (P : TPar D) : Formalism.MainNotions.CayleySignature.IsMu (thetaG D) P (muOf D P) := fun j τ => by
  show (if h : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ D.R.m then -P.e τ ⟨j.1 + 1 - 1, by omega⟩ else 0) = _
  rw [dif_pos ⟨Nat.le_add_left _ _, j.2⟩]
  rfl

theorem thetaFamily_admissible_one : Formalism.MainNotions.CayleySignature.RallisSiegelWeilFormula D (thetaG D) := fun P _ => by
  refine ⟨muOf D P, fun _ => Submodule.span ℂ {v0 D}, muOf_isMu D P, fun j _ => ⟨⟨stableG D _ _, ?_, ?_⟩,
    le_top, le_top⟩, fun j hj φ hφ => ?_⟩
  · exact (nonzero_span_atom (v0 D) (v0_ne D)).1
  · intro π' hle _
    rcases eq_or_lt_of_le hle with h | h
    · exact Or.inr h
    · exact Or.inl ((nonzero_span_atom (v0 D) (v0_ne D)).2 π' h)
  · refine ⟨1, fun _ => LinearMap.id, fun _ => ⟨φ, trivial⟩, fun _ => ⟨trivial, trivial, hφ⟩, ?_⟩
    rw [Fin.sum_univ_one]
    exact (thG_pos D (rankX_pos D P.t (j + 1) hj) LinearMap.id ⟨φ, trivial⟩).symm

theorem thetaFamily_admissible_two : Formalism.MainNotions.CayleySignature.LiftParameterConditions D (thetaG D) := fun P _ π hπ _ => by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff π).mp hπ.2.1
  exact ⟨φ, hφ, ⟨cj (HG D) φ, trivial⟩, trivial,
    Or.inr ⟨rfl, inner_self_ne D (cj_ne h0)⟩⟩

theorem perNZ_inner {t j : ℕ} {φ : HG D} {F : (⊤ : Submodule ℂ (HG D))}
    (h : Formalism.MainNotions.CayleySignature.PerNZ (thetaG D) t j φ F) : inner ℂ (cj (HG D) φ) (F : HG D) ≠ 0 := by
  rcases h with ⟨_, _, _, h⟩ | ⟨_, h⟩
  · exact h
  · exact h

theorem cj_zero (V : Type) [AddCommGroup V] [Module ℂ V] : cj V 0 = 0 := by
  have h0 := cj_smul V 0 (0 : V)
  simpa using h0

theorem key3 (W W' : HSp D) (hW' : 0 < W'.rank) (Φ' : HG D →ₗ[ℂ] HG D) (φ' F : (⊤ : Submodule ℂ (HG D)))
    (h1 : inner ℂ (cj (HG D) (thG D W Φ' φ')) (F : HG D) ≠ 0) :
    ∃ Φ : HG D →ₗ[ℂ] HG D, inner ℂ (cj (HG D) (φ' : HG D)) (thG D W' Φ F) ≠ 0 := by
  have hF : (F : HG D) ≠ 0 := fun e => h1 (by rw [e, inner_zero_right])
  have hφ : (φ' : HG D) ≠ 0 := fun e => h1 (by
    have e' : φ' = 0 := Subtype.ext e
    rw [e', map_zero, cj_zero, inner_zero_left])
  refine ⟨(innerₛₗ ℂ (F : HG D)).smulRight (cj (HG D) (φ' : HG D)), ?_⟩
  rw [thG_pos D hW']
  show inner ℂ (cj (HG D) (φ' : HG D)) (inner ℂ (F : HG D) (F : HG D) • cj (HG D) (φ' : HG D)) ≠ 0
  rw [inner_smul_right]
  exact mul_ne_zero (inner_self_ne D hF) (inner_self_ne D (cj_ne hφ))

theorem thetaFamily_admissible_three : Formalism.MainNotions.CayleySignature.ThetaUnfoldingFreeData D (thetaG D) := fun P _ μ _ j hj φ' Φ' _ _ _ F _ hN => by
  obtain ⟨Φ, hΦ⟩ := key3 D ((tow D P.t).Xs (j + 1)) ((tow D P.t).Ys j) (rankY_pos D P.t j hj.le) Φ' φ' F
    (perNZ_inner D hN)
  refine ⟨Φ, trivial, trivial, fun G hG => Or.inl ⟨hj, PUnit.unit, PUnit.unit, ?_⟩⟩
  have hG' : (G.1 : HG D) = thG D ((tow D P.t).Ys j) Φ F := hG
  show inner ℂ (cj (HG D) (φ'.1 : HG D)) (G.1 : HG D) ≠ 0
  rw [hG']
  exact hΦ

theorem thetaFamily_admissible_four : Formalism.MainNotions.CayleySignature.ThetaStablePeriodVanishing D (thetaG D) := fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial

theorem thetaFamily_admissible_five : Formalism.MainNotions.CayleySignature.RealThetaLiftDiscreteSeries D (thetaG D) := fun P _ μ _ =>
  ⟨fun _ _ _ _ _ _ _ => trivial, fun j _ i hi _ Φ F _ => by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    exact thG_Z D Φ F⟩

theorem thetaFamily_admissible_six : Formalism.MainNotions.CayleySignature.RealConstantNonvanishing D (thetaG D) := fun _ _ _ =>
  ⟨fun _ _ _ => trivial, fun _ _ _ _ _ => trivial⟩

theorem thetaFamily_admissible : Formalism.MainNotions.CayleySignature.AdmS D (thetaG D) :=
  ⟨thetaFamily_admissible_one D, thetaFamily_admissible_two D, thetaFamily_admissible_three D, thetaFamily_admissible_four D, thetaFamily_admissible_five D, thetaFamily_admissible_six D⟩

theorem thetaG_exists : ∃ X : ThetaX D, X.TieRowIsom ∧ X.TieIo ∧ Formalism.MainNotions.CayleySignature.AdmS D X ∧
    Formalism.MainNotions.InnerProductFormulaField.TieRowTyp X ∧ Formalism.MainNotions.ZetaProductPairs.TypStable X :=
  ⟨thetaG D, thetaG_row D, thetaG_io D, thetaFamily_admissible D, thetaG_rowTyp D, thetaG_typStable D⟩

end Formalism.BasicNotions.Examples₂.NZ
