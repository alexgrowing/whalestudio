import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrysOfInertia
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private theorem isCr_comp {l : ℕ} [Fact l.Prime] {G A V : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A]
    [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (φ : G →* GQ l) (c : G →* G)
    (hc : Function.Surjective c) (ρ : Representation A G V) :
    IsCr (φ.comp c) (ρ.comp c : Representation A G V) ↔ IsCr φ ρ := by
  have hr : (φ.comp c).range = φ.range := by
    ext σ
    refine ⟨fun ⟨g, hg⟩ => ⟨c g, hg⟩, fun ⟨g, hg⟩ => ?_⟩
    obtain ⟨g, rfl⟩ := hc g
    exact ⟨g, hg⟩
  have hd : Dcr (φ.comp c) (resCoef ℚ_[l] (ρ.comp c : Representation A G V)) = Dcr φ (resCoef ℚ_[l] ρ) := by
    unfold Dcr
    exact hc.iInf_comp (fun g => LinearMap.ker (actC φ (resCoef ℚ_[l] ρ) g - LinearMap.id))
  unfold IsCr
  rw [hr, hd]

private theorem conj_left {B : Type} [CommRing B] (w : GG 3 B) (x y : GL (Fin 3) B)
    (h : GG.ofGL y = w * GG.ofGL x * w⁻¹) : y = w.left * sgnAct 3 B w.right x * w.left⁻¹ := by
  have := congrArg SemidirectProduct.left h
  have e : sgnAct 3 B w.right (sgnAct 3 B w.right w.left) = w.left := by
    rw [← MulAut.mul_apply, ← map_mul, Int.units_mul_self, map_one, MulAut.one_apply]
  simpa [e] using this

private theorem dot_inv {B : Type} [CommRing B] (a m : GL (Fin 3) B) (u x : Fin 3 → B) :
    dotProduct ((Jmat B 3 * ((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)).mulVec
      (((a * theta m * a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B).mulVec u))
      ((m : Matrix (Fin 3) (Fin 3) B).mulVec x) =
    dotProduct ((Jmat B 3 * ((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)).mulVec u) x := by
  have e : Jmat B 3 * ((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) *
      ((a * theta m * a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) =
      ((m⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B).transpose *
        (Jmat B 3 * ((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)) := by
    rw [Matrix.mul_assoc, ← Units.val_mul, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, Units.val_mul,
      theta_val]
    simp only [← Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.one_mul]
  rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec x, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem UpperTheory.conjugate_restriction_open_normal :
    ∀ {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] (H : Subgroup (GQ l)) [H.Normal], IsOpen (H : Set (GQ l)) → ∀ (ρ ρ' : ↥H →* GL (Fin 3) B), Continuous (fun g => (ρ g : Matrix (Fin 3) (Fin 3) B)) → ∀ (s : GQ l) (w : GG 3 B), (∀ g g' : H, (g' : GQ l) = s⁻¹ * g * s → GG.ofGL (ρ' g) = w * GG.ofGL (ρ g') * w⁻¹) → IsCr H.subtype (colRep ρ) → IsCr H.subtype (colRep ρ') := by
  intro l _ B _ _ _ _ _ _ H hN hH ρ ρ' hρ s w hw hcr
  have hψ : IsOpenEmbedding H.subtype := hH.isOpenEmbedding_subtypeVal
  let c : H →* H := (MulAut.conjNormal (H := H) s⁻¹).toMonoidHom
  have hc : ∀ g : H, (c g : GQ l) = s⁻¹ * g * s := fun g => by
    change ((MulAut.conjNormal (H := H) s⁻¹ g : H) : GQ l) = _
    rw [MulAut.conjNormal_apply, inv_inv]
  have hcc : Continuous c := by
    refine continuous_induced_rng.2 ?_
    have : Subtype.val ∘ c = fun g : H => s⁻¹ * (g : GQ l) * s := funext hc
    rw [this]
    fun_prop
  let σ : H →* GL (Fin 3) B := ρ.comp c
  have hσ : Continuous (fun g => (σ g : Matrix (Fin 3) (Fin 3) B)) := hρ.comp hcc
  have hσi : Continuous (fun g => (((σ g)⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)) := by
    simp only [← map_inv]
    exact hσ.comp continuous_inv
  have hσcr : IsCr H.subtype (colRep σ) := by
    have h1 := (isCr_comp H.subtype c (MulAut.conjNormal (H := H) s⁻¹).surjective (colRep ρ)).2 hcr
    have h2 : H.subtype.comp c = (MulAut.conj s⁻¹).toMonoidHom.comp H.subtype := by
      refine MonoidHom.ext fun g => ?_
      change (c g : GQ l) = s⁻¹ * g * s⁻¹⁻¹
      rw [hc, inv_inv]
    rw [h2] at h1
    exact (admissible_conjugate H.subtype hψ (colRep σ) s⁻¹).1.1 h1
  have he : ∀ g, ρ' g = w.left * sgnAct 3 B w.right (σ g) * w.left⁻¹ := fun g =>
    conj_left w _ _ (hw g (c g) (hc g))
  generalize w.left = a at he
  rcases Int.units_eq_one_or w.right with h | h
  · simp only [h, sgnAct_one] at he
    have hρ' : Continuous (fun g => (ρ' g : Matrix (Fin 3) (Fin 3) B)) := by
      simp only [he, Units.val_mul]
      exact (continuous_const.matrix_mul hσ).matrix_mul continuous_const
    refine ((isCrys_isDR_sub_quot H.subtype hψ (colRep σ) (colRep ρ') (contAction_colRep hσ) (contAction_colRep hρ')
      ((Matrix.toLin' (a : Matrix (Fin 3) (Fin 3) B)).restrictScalars ℚ_[l]) (fun g x => ?_)).2
      (fun v => ?_)).1 hσcr
    · simp only [LinearMap.restrictScalars_apply, Matrix.toLin'_apply, colRep_apply, Matrix.mulVec_mulVec, he,
        ← Units.val_mul, inv_mul_cancel_right]
    · refine ⟨((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B).mulVec v, ?_⟩
      simp only [LinearMap.restrictScalars_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  · simp only [h, sgnAct_neg_one] at he
    have hρ' : Continuous (fun g => (ρ' g : Matrix (Fin 3) (Fin 3) B)) := by
      simp only [he, Units.val_mul, theta_val]
      exact (continuous_const.matrix_mul ((continuous_const.matrix_mul hσi.matrix_transpose).matrix_mul
        continuous_const)).matrix_mul continuous_const
    have c1 : ContAction (chRep (1 : H →* Bˣ)) := contAction_chRep continuous_const
    have cr1 : IsCr H.subtype (chRep (1 : H →* Bˣ)) :=
      crUnr (A := ℚ_[l]) H.subtype hψ (resCoef ℚ_[l] (chRep (1 : H →* Bˣ))) c1 0
        (fun g _ x => by simp [resCoef, chRep])
    let N : Matrix (Fin 3) (Fin 3) B := Jmat B 3 * ((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)
    refine (isCrys_isDR_internalHom H.subtype hψ (colRep σ) (chRep (1 : H →* Bˣ)) (colRep ρ') (contAction_colRep hσ) c1
      (contAction_colRep hρ')
      (LinearMap.mk₂ ℚ_[l] (fun (u x : Fin 3 → B) => dotProduct (N.mulVec u) x)
        (fun _ _ _ => by rw [Matrix.mulVec_add, add_dotProduct])
        (fun _ _ _ => by rw [Matrix.mulVec_smul, smul_dotProduct])
        (fun _ _ _ => dotProduct_add _ _ _) (fun _ _ _ => dotProduct_smul _ _ _))
      (fun g u x => ?_) (fun u u' huu => ?_)).1 hσcr cr1
    · simp only [LinearMap.mk₂_apply, colRep_apply, chRep_apply, MonoidHom.one_apply, Units.val_one, one_mul]
      rw [he]
      exact dot_inv a (σ g) u x
    · have h1 : N.mulVec u = N.mulVec u' := by
        funext i
        have := LinearMap.congr_fun huu (Pi.single i 1)
        simpa only [LinearMap.mk₂_apply, dotProduct_single, mul_one] using this
      have h2 : ((a : Matrix (Fin 3) (Fin 3) B) * Jmat B 3) * N = 1 := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Jmat B 3), Jmat_mul_Jmat, Matrix.one_mul, Units.mul_inv]
      have h3 := congrArg ((a : Matrix (Fin 3) (Fin 3) B) * Jmat B 3).mulVec h1
      simpa only [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] using h3
