import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.NonEllFlag
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

namespace GlobalTheory.CompanionTheory.SplitTwo

section Generic

variable {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {n : ℕ}

def matProd : Matrix (Fin n) (Fin n) (B × C) ≃+* Matrix (Fin n) (Fin n) B × Matrix (Fin n) (Fin n) C where
  toFun M := (M.map Prod.fst, M.map Prod.snd)
  invFun p := Matrix.of fun i j => (p.1 i j, p.2 i j)
  left_inv M := by ext i j <;> rfl
  right_inv p := by ext i j <;> rfl
  map_mul' M N := by
    refine Prod.ext ?_ ?_ <;> ext i j <;> simp [Matrix.mul_apply, Prod.fst_sum, Prod.snd_sum]
  map_add' M N := by
    refine Prod.ext ?_ ?_ <;> ext i j <;> simp

def matQ (q : A ≃+* (B × B) × C) : Matrix (Fin n) (Fin n) A ≃+*
    (Matrix (Fin n) (Fin n) B × Matrix (Fin n) (Fin n) B) × Matrix (Fin n) (Fin n) C :=
  (q.mapMatrix).trans (matProd.trans (RingEquiv.prodCongr matProd (RingEquiv.refl _)))

theorem matQ_apply (q : A ≃+* (B × B) × C) (M : Matrix (Fin n) (Fin n) A) :
    matQ q M = ((M.map fun x => (q x).1.1, M.map fun x => (q x).1.2), M.map fun x => (q x).2) := rfl

theorem matQ_symm_apply (q : A ≃+* (B × B) × C)
    (p : (Matrix (Fin n) (Fin n) B × Matrix (Fin n) (Fin n) B) × Matrix (Fin n) (Fin n) C) :
    (matQ q).symm p = Matrix.of fun i j => q.symm ((p.1.1 i j, p.1.2 i j), p.2 i j) := rfl

variable [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]

def glQ (q : A ≃+* (B × B) × C) (hq : Continuous q) (hq' : Continuous q.symm) :
    GL (Fin n) A ≃ₜ* (GL (Fin n) B × GL (Fin n) B) × GL (Fin n) C where
  toMulEquiv := (Units.mapEquiv (matQ q).toMulEquiv).trans
    (MulEquiv.prodUnits.trans (MulEquiv.prodCongr MulEquiv.prodUnits (MulEquiv.refl _)))
  continuous_toFun := by
    have h : Continuous (matQ (n := n) q) := by
      simp only [funext (matQ_apply q)]
      refine Continuous.prodMk (Continuous.prodMk ?_ ?_) ?_ <;>
        exact continuous_matrix fun i j => by
          first
          | exact (continuous_fst.comp (continuous_fst.comp hq)).comp (continuous_id.matrix_elem i j)
          | exact (continuous_snd.comp (continuous_fst.comp hq)).comp (continuous_id.matrix_elem i j)
          | exact (continuous_snd.comp hq).comp (continuous_id.matrix_elem i j)
    have h1 := Continuous.units_map (matQ (n := n) q).toMulEquiv.toMonoidHom h
    exact ((Homeomorph.prodCongr Homeomorph.prodUnits (Homeomorph.refl _)).continuous.comp
      (Homeomorph.prodUnits.continuous.comp h1))
  continuous_invFun := by
    have h : Continuous (matQ (n := n) q).symm := by
      simp only [funext (matQ_symm_apply q)]
      refine continuous_matrix fun i j => hq'.comp ?_
      exact ((((continuous_fst.comp continuous_fst).matrix_elem i j).prodMk
        ((continuous_snd.comp continuous_fst).matrix_elem i j)).prodMk (continuous_snd.matrix_elem i j))
    have h1 := Continuous.units_map (matQ (n := n) q).symm.toMulEquiv.toMonoidHom h
    exact h1.comp (Homeomorph.prodUnits.symm.continuous.comp
      (Homeomorph.prodCongr Homeomorph.prodUnits (Homeomorph.refl _)).symm.continuous)

variable (q : A ≃+* (B × B) × C) (hq : Continuous q) (hq' : Continuous q.symm)

def q₁ : A →+* B := (RingHom.fst B B).comp ((RingHom.fst (B × B) C).comp q.toRingHom)
def q₂ : A →+* B := (RingHom.snd B B).comp ((RingHom.fst (B × B) C).comp q.toRingHom)
def q₃ : A →+* C := (RingHom.snd (B × B) C).comp q.toRingHom

theorem glQ_apply (g : GL (Fin n) A) : glQ q hq hq' g =
    ((GeneralLinearGroup.map (q₁ q) g, GeneralLinearGroup.map (q₂ q) g), GeneralLinearGroup.map (q₃ q) g) := by
  refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> exact Units.ext (by ext i j; rfl)

theorem map_thetaR {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (σ : R →+* R) (τ : S →+* S)
    (h : ∀ x, p (σ x) = τ (p x)) (g : GL (Fin n) R) :
    GeneralLinearGroup.map p (thetaR σ n g) = thetaR τ n (GeneralLinearGroup.map p g) := by
  refine Units.ext ?_
  ext i j
  have : (((GeneralLinearGroup.map p g)⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) j i =
      p (((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) j i) := by
    rw [← map_inv]; rfl
  change p (σ _) = τ _
  rw [this, h]

theorem glQ_thetaR (σ : A →+* A) (τ : B →+* B) (ρ : C →+* C)
    (h₁ : ∀ x, q₁ q (σ x) = τ (q₁ q x)) (h₂ : ∀ x, q₂ q (σ x) = τ (q₂ q x))
    (h₃ : ∀ x, q₃ q (σ x) = ρ (q₃ q x)) (g : GL (Fin n) A) : glQ q hq hq' (thetaR σ n g) =
      ((thetaR τ n (glQ q hq hq' g).1.1, thetaR τ n (glQ q hq hq' g).1.2), thetaR ρ n (glQ q hq hq' g).2) := by
  simp only [glQ_apply]
  rw [map_thetaR _ σ τ h₁, map_thetaR _ σ τ h₂, map_thetaR _ σ ρ h₃]

theorem map_twCent (σ : A →+* A) (τ : B →+* B) (ρ : C →+* C)
    (h₁ : ∀ x, q₁ q (σ x) = τ (q₁ q x)) (h₂ : ∀ x, q₂ q (σ x) = τ (q₂ q x))
    (h₃ : ∀ x, q₃ q (σ x) = ρ (q₃ q x)) (δ : GL (Fin n) A) :
    (twCent (thetaR σ n) δ).map (glQ q hq hq').toMonoidHom =
      ((twCent (thetaR τ n) (glQ q hq hq' δ).1.1).prod (twCent (thetaR τ n) (glQ q hq hq' δ).1.2)).prod
        (twCent (thetaR ρ n) (glQ q hq hq' δ).2) := by
  have key := fun g : GL (Fin n) A => glQ_thetaR q hq hq' σ τ ρ h₁ h₂ h₃ g
  have mem : ∀ g, g ∈ twCent (thetaR σ n) δ ↔ glQ q hq hq' g ∈
      ((twCent (thetaR τ n) (glQ q hq hq' δ).1.1).prod (twCent (thetaR τ n) (glQ q hq hq' δ).1.2)).prod
        (twCent (thetaR ρ n) (glQ q hq hq' δ).2) := by
    intro g
    change twConj _ g δ = δ ↔ ((twConj _ (glQ q hq hq' g).1.1 (glQ q hq hq' δ).1.1 = (glQ q hq hq' δ).1.1 ∧
      twConj _ (glQ q hq hq' g).1.2 (glQ q hq hq' δ).1.2 = (glQ q hq hq' δ).1.2) ∧
      twConj _ (glQ q hq hq' g).2 (glQ q hq hq' δ).2 = (glQ q hq hq' δ).2)
    rw [← (glQ q hq hq').injective.eq_iff]
    simp only [twConj, map_mul, map_inv, key]
    simp only [Prod.ext_iff, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (mem g).1 hg
  · intro hx
    refine ⟨(glQ q hq hq').symm x, (mem _).2 (by simpa using hx), (glQ q hq hq').apply_symm_apply x⟩

theorem gl_lc {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    [LocallyCompactSpace R] : LocallyCompactSpace (GL (Fin n) R) :=
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem gl_sc {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [SecondCountableTopology R] : SecondCountableTopology (GL (Fin n) R) :=
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology

end Generic

theorem haar_split {X P Q : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X]
    [BorelSpace X] [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P]
    [SecondCountableTopology P] [MeasurableSpace P] [BorelSpace P] [Group Q] [TopologicalSpace Q]
    [IsTopologicalGroup Q] [LocallyCompactSpace Q] [SecondCountableTopology Q] [MeasurableSpace Q] [BorelSpace Q]
    (e : X ≃ₜ* (P × P) × Q) (μ : Measure X) [μ.IsHaarMeasure] :
    ∃ (μ₁ : Measure P) (μ₂ : Measure Q), μ₁.IsHaarMeasure ∧ μ₂.IsHaarMeasure ∧
      μ.map e = (μ₁.prod μ₁).prod μ₂ := by
  let μ₁ : Measure P := Measure.haar
  let μ₃ : Measure Q := Measure.haar
  haveI : (μ.map e).IsHaarMeasure := e.isHaarMeasure_map μ
  have h := Measure.isMulLeftInvariant_eq_smul (μ.map e) ((μ₁.prod μ₁).prod μ₃)
  have hc := Measure.haarScalarFactor_pos_of_isHaarMeasure (μ.map e) ((μ₁.prod μ₁).prod μ₃)
  refine ⟨μ₁, Measure.haarScalarFactor (μ.map e) ((μ₁.prod μ₁).prod μ₃) • μ₃, inferInstance,
    Measure.IsHaarMeasure.nnreal_smul _ hc.ne', ?_⟩
  rw [Measure.prod_smul_right]
  exact h

section Field

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem continuous_infEq_symm : Continuous (infEq E).symm :=
  continuous_pi fun w => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
    (IsTotallyComplex.isComplex w)).continuous.comp (continuous_apply w)

theorem continuous_cV (v : InfinitePlace E) : Continuous (cV v) :=
  (continuous_apply v).comp (continuous_infEq_symm.comp continuous_fst)

theorem continuous_pFin : Continuous (pFin E) := continuous_snd

variable (v₁ v₂ : InfinitePlace E)

abbrev Oth : Type := {w : InfinitePlace E // w ≠ v₁ ∧ w ≠ v₂}

abbrev Rest : Type := (Oth v₁ v₂ → ℂ) × Af E

open Classical in

def glue (a b : ℂ) (c : Oth v₁ v₂ → ℂ) : Cinf E := fun w =>
  if h₁ : w = v₁ then a else if h₂ : w = v₂ then b else c ⟨w, h₁, h₂⟩

def qHom : Ad E →+* (ℂ × ℂ) × Rest v₁ v₂ :=
  ((cV v₁).prod (cV v₂)).prod ((Pi.ringHom fun w : Oth v₁ v₂ => cV w.1).prod (pFin E))

variable {v₁ v₂}

def qAd (h : v₁ ≠ v₂) : Ad E ≃+* (ℂ × ℂ) × Rest v₁ v₂ where
  toFun := qHom v₁ v₂
  invFun p := ((infEq E (glue v₁ v₂ p.1.1 p.1.2 p.2.1), p.2.2) : InfiniteAdeleRing E × Af E)
  left_inv x := by
    refine Prod.ext ?_ rfl
    have : glue v₁ v₂ (cV v₁ x) (cV v₂ x) (fun w => cV w.1 x) = pInf E x := by
      funext w
      unfold glue
      split_ifs with h₁ h₂
      · rw [h₁]; rfl
      · rw [h₂]; rfl
      · rfl
    change infEq E (glue v₁ v₂ (cV v₁ x) (cV v₂ x) (fun w => cV w.1 x)) = x.1
    rw [this]
    exact (infEq E).apply_symm_apply _
  right_inv p := by
    have hc : ∀ w, cV w (((infEq E (glue v₁ v₂ p.1.1 p.1.2 p.2.1), p.2.2) : InfiniteAdeleRing E × Af E) : Ad E) =
        glue v₁ v₂ p.1.1 p.1.2 p.2.1 w := fun w => by
      change (infEq E).symm (infEq E _) w = _
      rw [RingEquiv.symm_apply_apply]
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext (funext fun w => ?_) rfl)
    · change cV v₁ _ = _
      rw [hc]; simp [glue]
    · change cV v₂ _ = _
      rw [hc]; simp [glue, h.symm]
    · change cV w.1 _ = _
      rw [hc]; simp [glue, w.2.1, w.2.2]
  map_mul' := map_mul (qHom v₁ v₂)
  map_add' := map_add (qHom v₁ v₂)

theorem continuous_qAd (h : v₁ ≠ v₂) : Continuous (qAd h) := by
  change Continuous fun x : Ad E => (((cV v₁ x, cV v₂ x), ((fun w : Oth v₁ v₂ => cV w.1 x), pFin E x)) : (ℂ × ℂ) × Rest v₁ v₂)
  have h₃ : Continuous fun x : Ad E => (fun w : Oth v₁ v₂ => cV w.1 x) :=
    continuous_pi fun w : Oth v₁ v₂ => continuous_cV w.1
  exact ((continuous_cV v₁).prodMk (continuous_cV v₂)).prodMk (h₃.prodMk continuous_pFin)

theorem continuous_qAd_symm (h : v₁ ≠ v₂) : Continuous (qAd h).symm := by
  change Continuous fun p : (ℂ × ℂ) × Rest v₁ v₂ =>
    ((infEq E (glue v₁ v₂ p.1.1 p.1.2 p.2.1), p.2.2) : InfiniteAdeleRing E × Af E)
  refine ((continuous_infEq E).comp (continuous_pi fun w => ?_)).prodMk (continuous_snd.comp continuous_snd)
  unfold glue
  split_ifs with h₁ h₂
  · exact continuous_fst.comp continuous_fst
  · exact continuous_snd.comp continuous_fst
  · exact (continuous_apply _).comp (continuous_fst.comp continuous_snd)

variable (v₁ v₂) in

def conjRest : Rest v₁ v₂ →+* Rest v₁ v₂ :=
  RingHom.prodMap (starRingEnd (Oth v₁ v₂ → ℂ)) (conjFin (IsCMField.complexConj E).toRingEquiv)

theorem cV_conjAd (v : InfinitePlace E) (x : Ad E) : cV v (conjAd E x) = starRingEnd ℂ (cV v x) := by
  change (infEq E).symm (infEq E _) v = _
  rw [RingEquiv.symm_apply_apply]
  rfl

theorem q₃_conjAd (h : v₁ ≠ v₂) (x : Ad E) :
    q₃ (qAd h) (conjAd E x) = conjRest v₁ v₂ (q₃ (qAd h) x) :=
  Prod.ext (funext fun w => cV_conjAd w.1 x) rfl

theorem map_eval (f : InfinitePlace E → GL (Fin n) ℂ) (w : InfinitePlace E) :
    GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)
      (Units.map (Matrix.piRingEquiv (n := Fin n) (β := fun _ : InfinitePlace E => ℂ)).symm.toMonoidHom
        ((MulEquiv.piUnits (M := fun _ : InfinitePlace E => Matrix (Fin n) (Fin n) ℂ)).symm f)) = f w :=
  Units.ext (by ext i j; rfl)

theorem cV_sInf (w : InfinitePlace E) (x : Cinf E) : cV w (sInf E x) = x w := by
  change (infEq E).symm (infEq E x) w = _
  rw [RingEquiv.symm_apply_apply]

open Classical in
theorem map_cV_embInf (v w : InfinitePlace E) (y : GL (Fin n) ℂ) :
    GeneralLinearGroup.map (cV w) (embInf n v y) =
      (Pi.mulSingle v y : InfinitePlace E → GL (Fin n) ℂ) w := by
  have := map_cornerGL_of_hom (a := n) (sInf E) (cV w) (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)
    (fun x => cV_sInf w x)
  unfold embInf
  simp only [MonoidHom.comp_apply]
  rw [infGL, this]
  exact map_eval _ w

theorem map_pFin_embInf (v : InfinitePlace E) (y : GL (Fin n) ℂ) :
    GeneralLinearGroup.map (pFin E) (embInf n v y) = 1 := by
  unfold embInf
  simp only [MonoidHom.comp_apply]
  rw [infGL]
  exact map_cornerGL_of_zero _ _ (fun x => rfl) _

theorem map_cV_ratGL (v : InfinitePlace E) (d : GL (Fin n) E) :
    GeneralLinearGroup.map (cV v) (ratGL E n d) = PositivityTheory.Rg.BcB.D4.locGL v d :=
  Units.ext (by
    ext i j
    exact pInf_algebraMap _ v)

theorem q₁_qAd (h : v₁ ≠ v₂) : q₁ (qAd h) = cV v₁ := RingHom.ext fun _ => rfl

theorem q₂_qAd (h : v₁ ≠ v₂) : q₂ (qAd h) = cV v₂ := RingHom.ext fun _ => rfl

open Classical in
theorem q₃_embInf (h : v₁ ≠ v₂) {v : InfinitePlace E} (hv : v = v₁ ∨ v = v₂) (y : GL (Fin n) ℂ) :
    GeneralLinearGroup.map (q₃ (qAd h)) (embInf n v y) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  refine Prod.ext ?_ ?_
  · funext w
    have hw : w.1 ≠ v := by
      rcases hv with rfl | rfl
      · exact w.2.1
      · exact w.2.2
    have h₀ := map_cV_embInf v w.1 y
    rw [Pi.mulSingle_eq_of_ne hw] at h₀
    have h₁ := congrArg (fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ) i j) h₀
    have h₂ : ((1 : Matrix (Fin n) (Fin n) (Rest v₁ v₂)) i j).1 w = (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> rfl
    exact h₁.trans h₂.symm
  · have h₁ := congrArg (fun g : GL (Fin n) (Af E) => (g : Matrix (Fin n) (Fin n) (Af E)) i j)
      (map_pFin_embInf (n := n) v y)
    have h₂ : ((1 : Matrix (Fin n) (Fin n) (Rest v₁ v₂)) i j).2 = (1 : Matrix (Fin n) (Fin n) (Af E)) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> rfl
    exact h₁.trans h₂.symm

theorem t2Space_finiteAdeleRing_cmField : T2Space (Af E) := by
  haveI : T2Space (InfiniteAdeleRing E × Af E) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  have hinj : Function.Injective (fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E)) :=
    fun a b h => (Prod.ext_iff.1 h).2
  exact T2Space.of_injective_continuous hinj (continuous_const.prodMk continuous_id)

end Field

open Classical in

theorem splitAt2 : SplitAt2 := by
  intro E _ _ _ n v₁ v₂ hne _ _ μ _
  haveI : T2Space (Af E) := t2Space_finiteAdeleRing_cmField
  haveI : LocallyCompactSpace (Af E) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele E
  haveI : SecondCountableTopology (Af E) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele E
  haveI lc₁ : LocallyCompactSpace (GL (Fin n) ℂ) := gl_lc
  haveI sc₁ : SecondCountableTopology (GL (Fin n) ℂ) := gl_sc
  haveI lc₂ : LocallyCompactSpace (GL (Fin n) (Rest v₁ v₂)) := gl_lc
  haveI sc₂ : SecondCountableTopology (GL (Fin n) (Rest v₁ v₂)) := gl_sc
  letI m₁ : MeasurableSpace (GL (Fin n) ℂ) := borel _
  haveI b₁ : BorelSpace (GL (Fin n) ℂ) := ⟨rfl⟩
  letI m₂ : MeasurableSpace (GL (Fin n) (Rest v₁ v₂)) := borel _
  haveI b₂ : BorelSpace (GL (Fin n) (Rest v₁ v₂)) := ⟨rfl⟩
  obtain ⟨μ₁, μ₂, h₁, h₂, h₃⟩ := haar_split (glQ (n := n) (qAd hne) (continuous_qAd hne) (continuous_qAd_symm hne)) μ
  have t₁ : ∀ x, q₁ (qAd hne) (conjAd E x) = starRingEnd ℂ (q₁ (qAd hne) x) := fun x => by
    rw [q₁_qAd]; exact cV_conjAd v₁ x
  have t₂ : ∀ x, q₂ (qAd hne) (conjAd E x) = starRingEnd ℂ (q₂ (qAd hne) x) := fun x => by
    rw [q₂_qAd]; exact cV_conjAd v₂ x
  have t₃ := q₃_conjAd (E := E) hne
  refine ⟨GL (Fin n) (Rest v₁ v₂), inferInstance, inferInstance, inferInstance, lc₂, sc₂, m₂, b₂, m₁, b₁,
    glQ (n := n) (qAd hne) (continuous_qAd hne) (continuous_qAd_symm hne), μ₁, μ₂, thetaR (conjRest v₁ v₂) n,
    h₁, h₂, h₃, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    rw [glQ_apply, q₁_qAd, q₂_qAd]
  · intro y
    rw [glQ_apply, q₁_qAd, q₂_qAd, q₃_embInf hne (Or.inl rfl), map_cV_embInf, map_cV_embInf,
      Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hne.symm]
  · intro y
    rw [glQ_apply, q₁_qAd, q₂_qAd, q₃_embInf hne (Or.inr rfl), map_cV_embInf, map_cV_embInf,
      Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hne]
  · intro g
    exact glQ_thetaR _ _ _ _ _ _ t₁ t₂ t₃ g
  · intro d
    have key := map_twCent (n := n) (qAd hne) (continuous_qAd hne) (continuous_qAd_symm hne) (conjAd E)
      (starRingEnd ℂ) (conjRest v₁ v₂) t₁ t₂ t₃ (ratGL E n d)
    have a₁ : (glQ (n := n) (qAd hne) (continuous_qAd hne) (continuous_qAd_symm hne) (ratGL E n d)).1.1 =
        PositivityTheory.Rg.BcB.D4.locGL v₁ d := by
      rw [glQ_apply, q₁_qAd, map_cV_ratGL]
    have a₂ : (glQ (n := n) (qAd hne) (continuous_qAd hne) (continuous_qAd_symm hne) (ratGL E n d)).1.2 =
        PositivityTheory.Rg.BcB.D4.locGL v₂ d := by
      rw [glQ_apply, q₂_qAd, map_cV_ratGL]
    rw [a₁, a₂] at key
    exact key

end GlobalTheory.CompanionTheory.SplitTwo

end
