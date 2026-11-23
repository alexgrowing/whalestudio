import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PowEqOneOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtInertiaAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtIneL
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsLieElementMiddleBlockPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLeOneOfIsIntegral

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem norm_le_one_of_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx

private theorem norm_unit {l : ℕ} [Fact l.Prime] (c : Coef l) {x : c.O} (hx : IsUnit x) :
    ‖algebraMap c.O (PadicAlgCl l) x‖ = 1 := by
  have hle : ∀ x : c.O, ‖algebraMap c.O (PadicAlgCl l) x‖ ≤ 1 := fun x =>
    norm_le_one_of_int l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map c.O.val)
  obtain ⟨u, rfl⟩ := hx
  have h1 : ‖algebraMap c.O (PadicAlgCl l) u‖ * ‖algebraMap c.O (PadicAlgCl l) (u⁻¹ : c.Oˣ)‖ = 1 := by
    rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  have h2 := hle u
  have h3 := hle (u⁻¹ : c.Oˣ)
  have h4 := norm_nonneg (algebraMap c.O (PadicAlgCl l) u)
  nlinarith

private theorem corner_det {R : Type} [CommRing R] (X : Matrix (Fin 3) (Fin 3) R) :
    (corner X).det = X 0 0 * X 2 2 - X 0 2 * X 2 0 := by
  rw [Matrix.det_fin_two]; rfl

private theorem tor_mat {R : Type} [CommRing R] (p : Rˣ) :
    (tor R p : Matrix (Fin 3) (Fin 3) R) = !![(p : R), 0, 0; 0, 1, 0; 0, 0, ((p⁻¹ : Rˣ) : R)] := by
  rw [tor_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wt1, Matrix.diagonal]

private theorem eval_block {k : Type} [Field k] (X : Matrix (Fin 3) (Fin 3) k) (p : kˣ)
    (h0 : X 0 1 = 0) (h2 : X 2 1 = 0) (hc : X.charpoly = (tor k p : Matrix (Fin 3) (Fin 3) k).charpoly) (t : k) :
    (t - X 1 1) * ((t - X 0 0) * (t - X 2 2) - X 0 2 * X 2 0) = (t - p) * (t - 1) * (t - (p⁻¹ : kˣ)) := by
  have := congrArg (Polynomial.eval t) hc
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly, tor_mat, Matrix.det_fin_three, Matrix.det_fin_three] at this
  simp [Matrix.scalar_apply, h0, h2] at this
  rw [Units.val_inv_eq_inv_val]
  linear_combination this

private theorem mid_eq_one {k : Type} [NormedField k] [IsUltrametricDist k] (X : Matrix (Fin 3) (Fin 3) k) (p : kˣ)
    (h0 : X 0 1 = 0) (h2 : X 2 1 = 0) (hc : X.charpoly = (tor k p : Matrix (Fin 3) (Fin 3) k).charpoly)
    (h1 : ‖X 1 1 - 1‖ < 1) (hp : ‖(p : k) - 1‖ = 1) (hp' : ‖(p : k)‖ = 1) : X 1 1 = 1 := by
  have := eval_block X p h0 h2 hc (X 1 1)
  rw [sub_self, zero_mul] at this
  rcases mul_eq_zero.1 this.symm with h | h
  · rcases mul_eq_zero.1 h with h | h
    · rw [sub_eq_zero.1 h, hp] at h1
      exact absurd h1 (lt_irrefl _)
    · exact sub_eq_zero.1 h
  · rw [sub_eq_zero.1 h] at h1
    have e : (p : k) * (((p⁻¹ : kˣ) : k) - 1) = -((p : k) - 1) := by rw [mul_sub, Units.mul_inv]; ring
    have e2 := congrArg norm e
    rw [norm_mul, norm_neg, hp, hp', one_mul] at e2
    rw [e2] at h1
    exact absurd h1 (lt_irrefl _)

private theorem det_near {k : Type} [NormedField k] [IsUltrametricDist k] (X : Matrix (Fin 3) (Fin 3) k) (p : kˣ)
    (hi : ∀ a b, ‖X a b‖ ≤ 1) (hr : ∀ a b, ‖X a b - (tor k p : Matrix (Fin 3) (Fin 3) k) a b‖ < 1)
    (hp' : ‖(p : k)‖ = 1) : ‖(corner X).det - 1‖ < 1 := by
  have h00 := hr 0 0
  have h22 := hr 2 2
  have h02 := hr 0 2
  rw [tor_mat] at h00 h22 h02
  change ‖X 0 0 - p‖ < 1 at h00
  change ‖X 2 2 - (p⁻¹ : kˣ)‖ < 1 at h22
  change ‖X 0 2 - 0‖ < 1 at h02
  rw [sub_zero] at h02
  have e : (corner X).det - 1 = ((X 0 0 - p) * X 2 2 + p * (X 2 2 - (p⁻¹ : kˣ))) + -(X 0 2 * X 2 0) := by
    rw [corner_det, mul_sub (p : k), Units.mul_inv]; ring
  rw [e]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt
    (lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)) ?_)
  · rw [norm_mul]; exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h00 (hi _ _)
  · rw [norm_mul, hp', one_mul]; exact h22
  · rw [norm_neg, norm_mul]; exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h02 (hi _ _)

private theorem bar_iff {O Γ : Type} [CommRing O] [IsLocalRing O] [Group Γ] (Ψ : Γ →* Oˣ) (g : Γ) :
    barChar O Ψ g = 1 ↔ ¬ IsUnit ((Ψ g : O) - 1) := by
  rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, map_sub, map_one,
    sub_eq_zero, Units.ext_iff]
  rfl

private noncomputable def midChar {G k : Type} [Group G] [Field k] (η : G →* ℤˣ) (r : G →* GG 3 k) (hm : HasMult η r)
    (hB : Block η r) : η.ker →* kˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => (r g).mat 1 1
      map_one' := by simp [GG.mat]
      map_mul' := fun g h => by
        have e : (r (g * h : η.ker)).mat = (r g).mat * (r h).mat :=
          congrArg Units.val ((glPart η r hm).map_mul g h)
        rw [e, Matrix.mul_apply, Fin.sum_univ_three, hB g g.2 1 0 (by decide), hB g g.2 1 2 (by decide)]
        ring }

private theorem W_facts {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [NormedField k]
    (η : Γ →* ℤˣ) (r : Γ →* GG 3 k) (cc : Γ) (hm : HasMult η r) (hc : η cc = -1) (hat : (r cc).mat = 1)
    (hII : TypeII η r) (hb : ∀ g ∈ η.ker, (corner (r g).mat).det = 1) (hct : Continuous (mats r))
    (hηc : IsLocallyConstant η) :
    ∃ W : Γ →* GL (Fin 2) k, (∀ g ∈ η.ker, (W g : Matrix (Fin 2) (Fin 2) k) = corner (r g).mat) ∧
      (W cc : Matrix (Fin 2) (Fin 2) k).trace = 0 ∧ Continuous W ∧ Af.IsIrr W ∧
      (∀ g, (W g : Matrix (Fin 2) (Fin 2) k) = Wfun r g) ∧
      ∀ g, (W g : Matrix (Fin 2) (Fin 2) k).det = ((η g : ℤˣ) : ℤ) := by
  obtain ⟨hB, hirr⟩ := hII
  obtain ⟨W, hW, hWd⟩ := exists_lieElement_middleBlockPart η r cc hm hc hat hB hb
  have hWk : ∀ g ∈ η.ker, (W g : Matrix (Fin 2) (Fin 2) k) = corner (r g).mat := fun g hg => by
    rw [hW, Wfun, if_pos ((hm g).trans hg)]
  have hWc : Continuous fun g => (W g : Matrix (Fin 2) (Fin 2) k) := by
    have e : (fun g => (W g : Matrix (Fin 2) (Fin 2) k)) = fun g => corner (r g).mat *
        (fun s : ℤˣ => if s = 1 then (1 : Matrix (Fin 2) (Fin 2) k) else Matrix.diagonal ![-1, 1]) (η g) := by
      funext g
      rw [hW, Wfun, hm g]
      dsimp only
      split_ifs <;> simp
    rw [e]
    exact (hct.matrix_submatrix _ _).matrix_mul
      (hηc.comp fun s : ℤˣ => if s = 1 then (1 : Matrix (Fin 2) (Fin 2) k) else Matrix.diagonal ![-1, 1]).continuous
  refine ⟨W, hWk, ?_, ?_, ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun V _ hV => hirr V fun g hg v hv => ?_⟩,
    hW, hWd⟩
  · rw [hW, Wfun, if_neg (by rw [hm, hc]; decide), hat]
    rw [Matrix.trace_fin_two, Matrix.mul_diagonal, Matrix.mul_diagonal]
    change (1 : k) * (-1) + 1 * 1 = 0
    ring
  · refine Units.continuous_iff.2 ⟨hWc, ?_⟩
    simp only [← map_inv]
    exact hWc.comp continuous_inv
  · have := hV g v hv
    rwa [hWk g hg] at this

theorem UpperTheory.V.U3.typeII_facts :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG 3 (PadicAlgCl l)} (h : D.IsPt U g₁ r),
      TypeII D.η r → (∀ g ∈ D.η.ker, (r g).mat 1 1 = 1) ∧ (∀ g ∈ D.η.ker, (corner (r g).mat).det = 1) ∧
        ∃ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l), D.IsExt r W ∧ Continuous W ∧ Af.IsIrr W ∧
          (∀ g, (W g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) = Wfun r g) ∧
          ∀ g, (W g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)).det = ((D.η g : ℤˣ) : ℤ) := by
  intro hC Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hM r h hII
  obtain ⟨hB, hirr⟩ := hII
  obtain ⟨-, -, -, hηc, -, -, -, -, -, -, habove⟩ := dat_facts D
  have h0 : ∀ g ∈ D.η.ker, (r g).mat 0 1 = 0 := fun g hg => hB g hg 0 1 (by decide)
  have h2 : ∀ g ∈ D.η.ker, (r g).mat 2 1 = 0 := fun g hg => hB g hg 2 1 (by decide)
  have hΨn : ∀ g, ‖((D.ΨQ g : (PadicAlgCl l)ˣ) : PadicAlgCl l)‖ = 1 := fun g => norm_unit c (D.Ψ g).isUnit
  have hcp : ∀ (A : ValuationSubring Ω), ∀ g ∈ D.η.ker, g ∈ Ine (F := ℚ) A →
      (r g).mat.charpoly = (tor _ (D.ΨQ g) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)).charpoly := by
    intro A g hg hA
    by_cases hl : A.valuation (l : Ω) < 1
    · exact (pt_inertia_above hC D hM h A hl).1 g hA
    · obtain ⟨M, hM'⟩ := pt_inertia_away D hM h A hl
      have e1 := hM' g hA hg
      have e2 : (r0 D.η D.ΨQ g).mat = (M : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) * (r g).mat *
          ((M⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) := by
        rw [e1, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      change _ = (r0 D.η D.ΨQ g).mat.charpoly
      rw [e2, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have hnear : ∀ g, ‖(r g).mat 1 1 - 1‖ < 1 := fun g => by
    have := h.red g 1 1
    change ‖_ - (tor _ (D.ΨQ g) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) 1 1‖ < 1 at this
    rw [tor_mat] at this
    exact this
  have hbar : ∀ g, barChar c.O D.Ψ g = 1 ↔ ¬ IsUnit ((D.Ψ g : c.O) - 1) := bar_iff D.Ψ
  have hfar : ∀ (A : ValuationSubring Ω), ∀ g ∈ D.η.ker, g ∈ Ine (F := ℚ) A → barChar c.O D.Ψ g ≠ 1 →
      (r g).mat 1 1 = 1 := by
    intro A g hg hA hb
    refine mid_eq_one _ _ (h0 g hg) (h2 g hg) (hcp A g hg hA) (hnear g) ?_ (hΨn g)
    have := norm_unit c (not_not.1 fun hn => hb ((hbar g).2 hn))
    rwa [map_sub, map_one] at this
  have hcm : ∀ a b, Continuous fun g => (r g).mat a b := fun a b => h.cont.matrix_elem a b
  have hκ : midChar D.η r h.mult hB = 1 := by
    refine char_eq_one D _ ((hcm 1 1).comp continuous_subtype_val) (fun g => hnear g) fun A g hA => ?_
    by_cases hb : barChar c.O D.Ψ g = 1
    · by_cases hl : A.valuation (l : Ω) < 1
      · obtain ⟨hle, s, hs, hu⟩ := habove A hl
        have hsb : barChar c.O D.Ψ s ≠ 1 := fun hn => (hbar s).1 hn
          (isUnit_of_mul_isUnit_left (y := (D.Ψ s : c.O) + 1) (by convert hu using 1; ring))
        have e1 : midChar D.η r h.mult hB ⟨s, hle hs⟩ = 1 := Units.ext (hfar A s (hle hs) hs hsb)
        have e2 : midChar D.η r h.mult hB (g * ⟨s, hle hs⟩) = 1 :=
          Units.ext (hfar A _ (g * ⟨s, hle hs⟩).2 (mul_mem hA hs) (by
            change barChar c.O D.Ψ (g * s) ≠ 1
            rwa [map_mul, hb, one_mul]))
        rwa [map_mul, e1, mul_one] at e2
      · have hk : (g : G ℚ Ω) ∈ D.Kill := ⟨A, hl, hA, by
          refine SemidirectProduct.ext ?_ g.2
          change tor _ (barChar c.O D.Ψ g) = 1
          rw [hb, map_one]⟩
        refine Units.ext ?_
        change (r g).mat 1 1 = 1
        rw [h.kill g hk]
        simp [GG.mat]
    · exact Units.ext (hfar A g g.2 hA hb)
  have ha : ∀ g ∈ D.η.ker, (r g).mat 1 1 = 1 := fun g hg => by
    have := congrArg Units.val (DFunLike.congr_fun hκ (⟨g, hg⟩ : D.η.ker))
    exact this
  have hdet : ∀ g ∈ D.η.ker, (r g).mat.det = (corner (r g).mat).det := fun g hg => by
    rw [corner_det, Matrix.det_fin_three, h0 g hg, h2 g hg, ha g hg]; ring
  have hδ : (Matrix.GeneralLinearGroup.det).comp (glPart D.η r h.mult) = 1 := by
    refine char_eq_one D _ (h.cont.matrix_det.comp continuous_subtype_val) (fun g => ?_) fun A g hA => ?_
    · change ‖(r g).mat.det - 1‖ < 1
      rw [hdet g g.2]
      exact det_near _ _ (h.int g) (h.red g) (hΨn g)
    · refine Units.ext ?_
      change (r g).mat.det = 1
      have := eval_block _ _ (h0 g g.2) (h2 g g.2) (hcp A g g.2 hA) 0
      rw [hdet g g.2, corner_det]
      rw [ha g g.2] at this
      linear_combination (D.ΨQ g).mul_inv - this
  have hb : ∀ g ∈ D.η.ker, (corner (r g).mat).det = 1 := fun g hg => by
    have := congrArg Units.val (DFunLike.congr_fun hδ (⟨g, hg⟩ : D.η.ker))
    exact (hdet g hg).symm.trans this
  obtain ⟨W, H1, H2, H3, H4, H5, H6⟩ := W_facts D.η r D.cc h.mult hM.ηc h.norm.atc ⟨hB, hirr⟩ hb h.cont hηc
  exact ⟨ha, hb, W, ⟨H1, H2⟩, H3, H4, H5, H6⟩
