import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.RedTheta
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharLem

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  have h0 : symplOH S T w 0 = 0 := by
    simp [symplOH, symplO, hO]
  simp [heisO, h0]

theorem redZero_holds : RedZero D := by
  intro ψ S T r C μ 𝓕 f
  simp only [Red, ellI, heisO_zero]

theorem symplOH_eq_zero_of (S T : HSp D) {x y : WO S T} (h : symplO S T x y = 0) : symplOH S T x y = 0 := by
  simp [symplOH, h]

theorem redPerp_holds : RedPerp D := by
  intro ψ S T r C μ 𝓕 w₀ _ f
  funext w
  simp only [Red, ellI, heisO]
  rw [← integral_const_mul]
  congr 1
  funext a
  simp only [Formalism.IndefR.Fin.symplOH_add_left, Formalism.IndefR.Fin.symplOH_add_right, AddChar.map_add_eq_mul, add_assoc]
  ring

theorem star_eq_sig (e : D.host.E) : star e = D.sp.cm.sig e := rfl

theorem hO_eq_zero_of (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E) (a : Mx D r S.rank)
    (y : WO S T) (hy : HMul.hMul (HMul.hMul (y.map (cA D)).transpose (Brg.GG T)) (C.map (incA D)) = 0) :
    hO S T (embI S T C a) y = 0 := by
  have hz : (y.map (cA D)).transpose * Brg.GG T * (C.map (incA D) * a) = 0 := by
    rw [← Matrix.mul_assoc, hy, Matrix.zero_mul]
  unfold hO embI
  refine Finset.sum_eq_zero fun i1 _ => Finset.sum_eq_zero fun i2 _ => ?_
  have e := congrFun (congrFun hz i2) i1
  generalize C.map (incA D) * a = X at e ⊢
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul,
    Matrix.zero_apply] at e

  have e2 : ∑ i3, ∑ i4, (cA D) (y i3 i2) * (incA D) (HSpace.gram T i3 i4) * X i4 i1 = 0 := by
    rw [Finset.sum_comm]
    exact e
  calc _ = (incA D) ((HSpace.gram S)⁻¹ i1 i2) *
        ∑ i3, ∑ i4, (cA D) (y i3 i2) * (incA D) (HSpace.gram T i3 i4) * X i4 i1 := by
        simp only [Finset.mul_sum, mul_assoc]
    _ = 0 := by rw [e2, mul_zero]

theorem symplO_embI_eq_zero_of (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E) (a : Mx D r S.rank)
    (y : WO S T) (hy : HMul.hMul (HMul.hMul (y.map (cA D)).transpose (Brg.GG T)) (C.map (incA D)) = 0) :
    symplO S T (embI S T C a) y = 0 := by
  unfold symplO
  rw [hO_eq_zero_of S T C a y hy]
  simp

theorem conj_ratW (S T : HSp D) (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (ratW T S x).map (cA D) = (x.map star).map (incA D) := by
  unfold ratW
  ext i j
  simp only [Matrix.map_apply]
  first
    | exact cA_incA D (x i j)
    | exact cA_incA (x i j)
    | simp [cA_incA]
    | simp [cA, incA, star_eq_sig, sigR_inclR]
    | simp [cA, incA, star_eq_sig, sigR, inclR]

theorem symplO_embI_perp (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    {x : Matrix (Fin T.rank) (Fin S.rank) D.host.E} (hx : IsPerpI S T C x) (a : Mx D r S.rank) :
    symplO S T (embI S T C a) (ratW T S x) = 0 := by
  apply symplO_embI_eq_zero_of
  rw [conj_ratW]

  have hG : Matrix.conjTranspose (HSpace.gram T) = HSpace.gram T := by
    ext i j
    rw [Matrix.conjTranspose_apply]
    unfold HSpace.gram
    first
      | exact T.herm (T.frame j) (T.frame i)
      | exact T.herm.eq (T.frame j) (T.frame i)
  have hx' : Matrix.conjTranspose C * HSpace.gram T * x = 0 := hx

  have h0 : Matrix.conjTranspose x * HSpace.gram T * C = 0 := by
    have h := congrArg Matrix.conjTranspose hx'
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using h
  have h1 : (x.map star).transpose * HSpace.gram T * C = 0 := h0
  have h2 : ((x.map star).transpose * HSpace.gram T * C).map (incA D) = 0 := by
    rw [h1]
    exact Matrix.map_zero _ (map_zero _)
  rw [Matrix.map_mul, Matrix.map_mul] at h2
  first
    | exact h2
    | (rw [Matrix.transpose_map] at h2; exact h2)

theorem symplO_embI_embI (S T : HSp D) {r : ℕ} {C : Matrix (Fin T.rank) (Fin r) D.host.E} (hC : IsIsoFrame T C)
    (a b : Mx D r S.rank) : symplO S T (embI S T C a) (embI S T C b) = 0 := by
  apply symplO_embI_eq_zero_of
  have hC' : Matrix.conjTranspose C * HSpace.gram T * C = 0 := by
    first
      | exact hC
      | exact hC.2.2
      | exact hC.1
  have hc : (C.map (incA D)).map (cA D) = (C.map star).map (incA D) := by
    ext i j
    simp only [Matrix.map_apply]
    first
      | simp [cA, incA, star_eq_sig, sigR_inclR]
      | simp [cA, incA, star_eq_sig, sigR, inclR]
  have h1 : (C.map star).transpose * HSpace.gram T * C = 0 := hC'
  have h2 : ((C.map star).transpose * HSpace.gram T * C).map (incA D) = 0 := by
    rw [h1]
    exact Matrix.map_zero _ (map_zero _)
  rw [Matrix.map_mul, Matrix.map_mul] at h2
  have h3 : ((C.map star).map (incA D)).transpose * Brg.GG T * C.map (incA D) = 0 := by
    first
      | exact h2
      | (rw [Matrix.transpose_map] at h2; exact h2)
  unfold embI
  rw [Matrix.map_mul, hc, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((C.map star).map (incA D)).transpose, h3, Matrix.mul_zero]

theorem red_quasi (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    {x : Matrix (Fin T.rank) (Fin S.rank) D.host.E} (hx : IsPerpI S T C x) (w : WO S T) :
    Red ψ S T C μ 𝓕 f (ratW T S x + w) = ψ (-(symplOH S T (ratW T S x) w)) * Red ψ S T C μ 𝓕 f w := by
  simp only [Red, ellI, heisO]
  rw [← integral_const_mul]
  congr 1
  funext a
  have hp := symplO_embI_perp S T C hx a
  have h2 := Formalism.IndefR.Fin.symplOH_two S T (embI S T C a) (ratW T S x)
  rw [hp] at h2
  have hsw := Formalism.IndefR.Fin.symplOH_swap S T (embI S T C a) (ratW T S x)
  rw [show embI S T C a + (ratW T S x + w) = ratW T S x + (embI S T C a + w) by abel, hf.quasi,
    Formalism.IndefR.Fin.symplOH_add_right, Formalism.IndefR.Fin.symplOH_add_right, hsw]
  have key : symplOH S T (embI S T C a) (ratW T S x) + symplOH S T (embI S T C a) w +
      -(-symplOH S T (embI S T C a) (ratW T S x) + symplOH S T (ratW T S x) w) =
      -symplOH S T (ratW T S x) w + symplOH S T (embI S T C a) w := by
    linear_combination h2
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, key, AddChar.map_add_eq_mul, mul_assoc]

theorem red_level (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ u ∈ U, IsPerpA S T C u →
      u.map (infPart D) = 0 → heisO ψ S T u (Red ψ S T C μ 𝓕 f) = Red ψ S T C μ 𝓕 f := by
  obtain ⟨U, hU, hUf⟩ := hf.level
  refine ⟨U, hU, fun u hu hperp hinf => ?_⟩
  rw [← redPerp_holds ψ S T r C μ 𝓕 u hperp f, hUf u hu hinf]

instance borelMx (m n : ℕ) : BorelSpace (Mx D m n) := ⟨rfl⟩

instance tagMx (m n : ℕ) : IsTopologicalAddGroup (Mx D m n) :=
  inferInstanceAs (IsTopologicalAddGroup (Fin m → Fin n → AE D))

instance measAddMx (m n : ℕ) : MeasurableAdd (Mx D m n) :=
  ⟨fun _ => (continuous_const.add continuous_id).measurable, fun _ => (continuous_id.add continuous_const).measurable⟩

theorem countable_ratMx (m n : ℕ) : Countable (ratMx D m n) := by
  haveI : Countable D.host.E :=
    Countable.of_equiv _ (Module.finBasis ℚ D.host.E).equivFun.symm.toEquiv
  haveI : Countable (Matrix (Fin m) (Fin n) D.host.E) :=
    inferInstanceAs (Countable (Fin m → Fin n → D.host.E))
  unfold ratMx
  have hs : Function.Surjective (fun x : Matrix (Fin m) (Fin n) D.host.E =>
      (⟨_, AddMonoidHom.mem_range.mpr ⟨x, rfl⟩⟩ :
        ((incA D).toAddMonoidHom.mapMatrix (m := Fin m) (n := Fin n)).range)) := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := AddMonoidHom.mem_range.mp hy
    exact ⟨x, rfl⟩
  exact hs.countable

theorem embI_add (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E) (a b : Mx D r S.rank) :
    embI S T C (a + b) = embI S T C a + embI S T C b := by
  unfold embI
  exact Matrix.mul_add _ _ _

theorem embI_rat (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (g : Matrix (Fin r) (Fin S.rank) D.host.E) : embI S T C (g.map (incA D)) = ratW T S (C * g) := by
  unfold embI ratW
  rw [Matrix.map_mul]

theorem f_embI_periodic (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {r : ℕ}
    {C : Matrix (Fin T.rank) (Fin r) D.host.E} (hC : IsIsoFrame T C) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (γ : ratMx D r S.rank) (a : Mx D r S.rank) : f (embI S T C (γ +ᵥ a)) = f (embI S T C a) := by
  obtain ⟨g, hg⟩ := γ.2
  have hγ : (γ : Mx D r S.rank) = g.map (incA D) := hg.symm
  show f (embI S T C ((γ : Mx D r S.rank) + a)) = f (embI S T C a)
  rw [embI_add, hγ, embI_rat S T C g, hf.quasi]
  have h0 : symplOH S T (ratW T S (C * g)) (embI S T C a) = 0 := by
    rw [← embI_rat S T C g]
    have h2 := Formalism.IndefR.Fin.symplOH_two S T (embI S T C (g.map (incA D))) (embI S T C a)
    rw [symplO_embI_embI S T hC] at h2
    rw [← one_smul D.host.F (symplOH S T _ _), ← inv_mul_cancel₀ (two_ne_zero (α := D.host.F)),
      mul_smul, two_smul, h2, smul_zero]
  rw [h0, neg_zero, AddChar.map_zero_eq_one, one_mul]

theorem ellIndep_holds : EllIndep D := by
  intro ψ _ S T r C hC μ 𝓕 𝓕' hμ h𝓕 h𝓕' f hf
  haveI := hμ
  haveI : Countable (ratMx D r S.rank) := countable_ratMx r S.rank
  unfold ellI
  exact h𝓕.setIntegral_eq h𝓕' (fun γ a => f_embI_periodic ψ S T hC hf γ a)

theorem setIntegral_add_right_periodic {m n : ℕ} (μ : Measure (Mx D m n)) [μ.IsAddHaarMeasure]
    {𝓕 : Set (Mx D m n)} (h𝓕 : IsAddFundamentalDomain (ratMx D m n) 𝓕 μ) (g : Mx D m n → ℂ)
    (hg : ∀ (γ : ratMx D m n) x, g (γ +ᵥ x) = g x) (a : Mx D m n) :
    ∫ x in 𝓕, g (x + a) ∂μ = ∫ x in 𝓕, g x ∂μ := by
  haveI : Countable (ratMx D m n) := countable_ratMx m n

  have hq : MeasureTheory.Measure.QuasiMeasurePreserving (fun x : Mx D m n => x + -a) μ μ :=
    (MeasureTheory.measurePreserving_add_right μ (-a)).quasiMeasurePreserving
  have h𝓕' : IsAddFundamentalDomain (ratMx D m n) ((fun x : Mx D m n => x + -a) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv hq (e := id) Function.bijective_id fun γ x => by
      change ((γ : Mx D m n) + x) + -a = (γ : Mx D m n) + (x + -a)
      exact add_assoc _ _ _

  have h1 : ∫ x in 𝓕, g (x + a) ∂μ = ∫ y in (fun x : Mx D m n => x + -a) ⁻¹' 𝓕, g y ∂μ := by
    have hpre : (fun x : Mx D m n => x + a) ⁻¹' ((fun x : Mx D m n => x + -a) ⁻¹' 𝓕) = 𝓕 := by
      ext x
      simp
    rw [← (MeasureTheory.measurePreserving_add_right μ a).setIntegral_preimage_emb
      (measurableEmbedding_addRight a) g ((fun x : Mx D m n => x + -a) ⁻¹' 𝓕), hpre]
  rw [h1]
  exact h𝓕'.setIntegral_eq h𝓕 hg

theorem redLeft_holds : RedLeft D := by
  intro ψ _ S T r C hC μ 𝓕 hμ h𝓕 f hf a w
  haveI := hμ
  have hiso : ∀ b c : Mx D r S.rank, symplOH S T (embI S T C b) (embI S T C c) = 0 := by
    intro b c
    have h2 := Formalism.IndefR.Fin.symplOH_two S T (embI S T C b) (embI S T C c)
    rw [symplO_embI_embI S T hC] at h2
    rw [← one_smul D.host.F (symplOH S T _ _), ← inv_mul_cancel₀ (two_ne_zero (α := D.host.F)),
      mul_smul, two_smul, h2, smul_zero]
  set g : Mx D r S.rank → ℂ := fun b => heisO ψ S T w f (embI S T C b) with hg
  have hper : ∀ (γ : ratMx D r S.rank) (b : Mx D r S.rank), g (γ +ᵥ b) = g b := by
    intro γ b
    obtain ⟨γ', hγ'⟩ := γ.2
    have hγ : (γ : Mx D r S.rank) = γ'.map (incA D) := hγ'.symm
    simp only [hg, heisO]
    show ψ (symplOH S T (embI S T C ((γ : Mx D r S.rank) + b)) w) *
        f (embI S T C ((γ : Mx D r S.rank) + b) + w) = _
    rw [embI_add, add_assoc, hγ, embI_rat S T C γ', hf.quasi, Formalism.IndefR.Fin.symplOH_add_left,
      Formalism.IndefR.Fin.symplOH_add_right, ← embI_rat S T C γ', hiso, zero_add, ← mul_assoc,
      ← AddChar.map_add_eq_mul]
    congr 2
    abel
  have hshift := setIntegral_add_right_periodic μ h𝓕 g hper a
  simp only [Red, ellI]
  rw [show (∫ b in 𝓕, heisO ψ S T w f (embI S T C b) ∂μ) = ∫ b in 𝓕, g (b + a) ∂μ from hshift.symm,
    ← integral_const_mul]
  congr 1
  funext b
  simp only [hg, heisO]
  rw [embI_add, Formalism.IndefR.Fin.symplOH_add_right, Formalism.IndefR.Fin.symplOH_add_left, hiso, zero_add, add_assoc,
    ← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  abel

end Formalism.IndefR.Eqv

end
