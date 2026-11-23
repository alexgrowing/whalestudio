import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmBilin
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MatrixExtendByZeroApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrysOfInertia
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc.DeformationPairing

private def extRep {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    (ρ : Representation A G V) (c : G → V) (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) :
    Representation A G (V × A) where
  toFun g := ((ρ g).comp (LinearMap.fst A V A) + (LinearMap.snd A V A).smulRight (c g)).prod (LinearMap.snd A V A)
  map_one' := by
    have h1 : c 1 = 0 := by simpa using hc 1 1
    refine LinearMap.ext fun x => ?_
    simp [h1]
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    simp [hc, add_assoc, add_comm, add_left_comm]

private theorem extRep_apply {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    (ρ : Representation A G V) (c : G → V) (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) (g : G) (x : V × A) :
    extRep ρ c hc g x = (ρ g x.1 + x.2 • c g, x.2) := rfl

private theorem contAction_sub {G A V : Type} [Group G] [TopologicalSpace G] [CommRing A] [AddCommGroup V]
    [Module A V] [TopologicalSpace V] (ρ : Representation A G V) (h : ContAction ρ) (H : Subgroup G) :
    ContAction (ρ.comp H.subtype : Representation A H V) :=
  h.comp (f := fun p : H × V => ((p.1 : G), p.2))
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

private noncomputable def pair (Q : Type) {E : Type} [Field Q] [Field E] [Algebra Q E] (n : ℕ) :
    (Matrix (Fin n) (Fin n) E × E) →ₗ[Q] (Fin n → E) →ₗ[Q] (Fin n → DualNumber E) :=
  LinearMap.mk₂ Q (fun w v i => (⟨w.2 * v i, (w.1.mulVec v) i⟩ : DualNumber E))
    (fun w w' v => by
      funext i; refine TrivSqZeroExt.ext ?_ ?_ <;> simp [add_mul, Matrix.add_mulVec] <;> rfl)
    (fun c w v => by
      funext i; refine TrivSqZeroExt.ext ?_ ?_ <;> simp [Matrix.smul_mulVec] <;> rfl)
    (fun w v v' => by
      funext i; refine TrivSqZeroExt.ext ?_ ?_ <;> simp [mul_add, Matrix.mulVec_add] <;> rfl)
    (fun c w v => by
      funext i; refine TrivSqZeroExt.ext ?_ ?_ <;> simp [Matrix.mulVec_smul] <;> rfl)

private theorem pair_fst (Q : Type) {E : Type} [Field Q] [Field E] [Algebra Q E] (n : ℕ)
    (w : Matrix (Fin n) (Fin n) E × E) (v : Fin n → E) (i : Fin n) : (pair Q n w v i).fst = w.2 * v i := rfl

private theorem pair_snd (Q : Type) {E : Type} [Field Q] [Field E] [Algebra Q E] (n : ℕ)
    (w : Matrix (Fin n) (Fin n) E × E) (v : Fin n → E) (i : Fin n) :
    (pair Q n w v i).snd = (w.1.mulVec v) i := rfl

private theorem mulVec_fst {E : Type} [Field E] {n : ℕ} (R S : Matrix (Fin n) (Fin n) E)
    (R' : Matrix (Fin n) (Fin n) (DualNumber E)) (h : ∀ i j, R' i j = ⟨R i j, S i j⟩)
    (w : Fin n → DualNumber E) (i : Fin n) :
    (R'.mulVec w i).fst = R.mulVec (fun j => (w j).fst) i := by
  have h1 : ∀ i j, (R' i j).fst = R i j := fun i j => by rw [h]; rfl
  simp [Matrix.mulVec, dotProduct, TrivSqZeroExt.fst_sum, h1]

private theorem mulVec_snd {E : Type} [Field E] {n : ℕ} (R S : Matrix (Fin n) (Fin n) E)
    (R' : Matrix (Fin n) (Fin n) (DualNumber E)) (h : ∀ i j, R' i j = ⟨R i j, S i j⟩)
    (w : Fin n → DualNumber E) (i : Fin n) :
    (R'.mulVec w i).snd = R.mulVec (fun j => (w j).snd) i + S.mulVec (fun j => (w j).fst) i := by
  have h1 : ∀ i j, (R' i j).fst = R i j := fun i j => by rw [h]; rfl
  have h2 : ∀ i j, (R' i j).snd = S i j := fun i j => by rw [h]; rfl
  simp [Matrix.mulVec, dotProduct, TrivSqZeroExt.snd_sum, h1, h2, Finset.sum_add_distrib]

private theorem ad_mulVec {G E : Type} [Group G] [Field E] {n : ℕ} (r : G →* GL (Fin n) E) (g : G)
    (X : Matrix (Fin n) (Fin n) E) (v : Fin n → E) :
    (adGL r g X).mulVec (colRep r g v) = colRep r g (X.mulVec v) := by
  change ((r g : Matrix (Fin n) (Fin n) E) * X * ((r g)⁻¹ : GL (Fin n) E)).mulVec
    (Matrix.toLin' (r g : Matrix (Fin n) (Fin n) E) v) = Matrix.toLin' (r g : Matrix (Fin n) (Fin n) E) _
  simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

end UpperTheory.V.Loc.DeformationPairing

open UpperTheory.V.Loc.DeformationPairing in
theorem UpperTheory.V.Loc.deformCr :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E] {n : ℕ} (r : G →* GL (Fin n) E), Continuous (fun g => (r g : Matrix (Fin n) (Fin n) E)) → ∀ y ∈ Z1 (adGL r), ∀ r' : G →* GL (Fin n) (DualNumber E), (∀ g i j, (r' g : Matrix (Fin n) (Fin n) (DualNumber E)) i j = ⟨(r g : Matrix (Fin n) (Fin n) E) i j, (y g * (r g : Matrix (Fin n) (Fin n) E)) i j⟩) → ∀ (H : Subgroup G) [H.Normal], IsOpen (H : Set G) → (CrOn φ (colRep r') H ↔ CrOn φ (colRep r) H ∧ y ∈ UpperTheory.V.Loc.finiteCocycles φ (adGL r)) := by
  intro l _ G _ _ _ φ hφ E _ _ _ _ _ _ n r hr y hy r' hr' H _ hH
  haveI : IsModuleTopology ℚ_[l] (DualNumber E) := inferInstanceAs (IsModuleTopology ℚ_[l] (E × E))
  haveI : FiniteDimensional ℚ_[l] (DualNumber E) := inferInstanceAs (FiniteDimensional ℚ_[l] (E × E))
  haveI : IsModuleTopology ℚ_[l] (Matrix (Fin n) (Fin n) E) :=
    inferInstanceAs (IsModuleTopology ℚ_[l] (Fin n → Fin n → E))
  have hψ : IsOpenEmbedding (φ.comp H.subtype) := hφ.comp hH.isOpenEmbedding_subtypeVal
  have cV : ContAction (colRep r) :=
    Continuous.matrix_mulVec (hr.comp continuous_fst) continuous_snd
  have hr'c : Continuous (fun g => (r' g : Matrix (Fin n) (Fin n) (DualNumber E))) := by
    refine continuous_matrix fun i j => ?_
    simp only [hr']
    exact (hr.matrix_elem i j).prodMk ((hy.1.matrix_mul hr).matrix_elem i j)
  have cW : ContAction (colRep r') :=
    Continuous.matrix_mulVec (hr'c.comp continuous_fst) continuous_snd
  have cM : ContAction (adGL r) := by
    have hi : Continuous (fun g => (((r g)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) := by
      simp only [← map_inv]
      exact hr.comp continuous_inv
    exact ((hr.comp continuous_fst).matrix_mul continuous_snd).matrix_mul (hi.comp continuous_fst)
  have cH : ContAction (extRep (adGL r) y hy.2) := by
    unfold ReciprocityTheory.Gal.ContAction
    simp only [extRep_apply]
    refine Continuous.prodMk (Continuous.add ?_ ?_) (continuous_snd.comp continuous_snd)
    · exact Continuous.comp (f := fun p : G × (Matrix (Fin n) (Fin n) E × E) => (p.1, p.2.1)) cM (by fun_prop)
    · exact (continuous_snd.comp continuous_snd).smul (hy.1.comp continuous_fst)
  have hb : ∀ g w v, pair ℚ_[l] n (extRep (adGL r) y hy.2 g w) (colRep r g v)
      = colRep r' g (pair ℚ_[l] n w v) := by
    intro g w v
    funext i
    have e' : colRep r' g (pair ℚ_[l] n w v)
      = (r' g : Matrix (Fin n) (Fin n) (DualNumber E)).mulVec (pair ℚ_[l] n w v) := rfl
    have e : ∀ u, colRep r g u = (r g : Matrix (Fin n) (Fin n) E).mulVec u := fun _ => rfl
    have e1 : (fun j => (pair ℚ_[l] n w v j).fst) = w.2 • v := rfl
    have e2 : (fun j => (pair ℚ_[l] n w v j).snd) = w.1.mulVec v := rfl
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [e', mulVec_fst _ _ _ (hr' g), e1, pair_fst, extRep_apply, Matrix.mulVec_smul, e]; rfl
    · rw [e', mulVec_snd _ _ _ (hr' g), e1, e2, pair_snd, extRep_apply, Matrix.add_mulVec, ad_mulVec, e, e,
        Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      rfl
  have crM : CrOn φ (colRep r) H → CrOn φ (adGL r) H := fun h =>
    (isCrys_isDR_internalHom (φ.comp H.subtype) hψ _ _ _ (contAction_sub _ cV H) (contAction_sub _ cV H) (contAction_sub _ cM H)
      (LinearMap.mk₂ ℚ_[l] (fun (X : Matrix (Fin n) (Fin n) E) (v : Fin n → E) => X.mulVec v)
        (fun _ _ _ => Matrix.add_mulVec _ _ _) (fun _ _ _ => Matrix.smul_mulVec _ _ _)
        (fun _ _ _ => Matrix.mulVec_add _ _ _) (fun _ _ _ => Matrix.mulVec_smul _ _ _))
      (fun g X v => ad_mulVec r g X v)
      (fun X Y hXY => Matrix.ext_iff_mulVec.2 fun v => LinearMap.congr_fun hXY v)).1 h h
  have cr1 : CrOn φ (chRep (1 : G →* Eˣ)) H :=
    crUnr (A := ℚ_[l]) (φ.comp H.subtype) hψ
      (resCoef ℚ_[l] ((chRep (1 : G →* Eˣ)).comp H.subtype : Representation E H E))
      (by
        unfold ReciprocityTheory.Gal.ContAction
        simpa [resCoef, chRep] using continuous_snd) 0
      (fun g _ x => by simp [resCoef, chRep])
  have htw : twist (1 : G →* Eˣ)⁻¹ (adGL r) = adGL r := by
    refine MonoidHom.ext fun g => ?_
    simp [twist]
  have key : CrOn φ (colRep r) H →
      (CrOn φ (extRep (adGL r) y hy.2) H ↔ y ∈ UpperTheory.V.Loc.finiteCocycles φ (adGL r)) := fun h => by
    have := crExt φ hφ (adGL r) (extRep (adGL r) y hy.2) cM cH 1 (LinearMap.inl E _ E) (LinearMap.snd E _ E)
      (0, 1) y LinearMap.inl_injective (Function.Exact.inl_snd) rfl
      (fun g x => by simp [extRep_apply]) (fun g => by simp [extRep_apply]) H hH (crM h) cr1
    rwa [htw] at this
  constructor
  · intro hW
    have hV : CrOn φ (colRep r) H := by
      refine ((isCrys_isDR_sub_quot (φ.comp H.subtype) hψ _ _ (contAction_sub _ cW H) (contAction_sub _ cV H)
        (((TrivSqZeroExt.fstHom ℚ_[l] E E).toLinearMap).compLeft (Fin n)) (fun g x => ?_)).2 (fun v => ?_)).1 hW
      · funext i
        exact mulVec_fst _ _ _ (hr' g) x i
      · exact ⟨fun i => TrivSqZeroExt.inl (v i), rfl⟩
    refine ⟨hV, ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : y = 0 := Subsingleton.elim _ _
      rw [this]; exact Submodule.zero_mem _
    · refine (key hV).1 ?_
      refine (isCrys_isDR_internalHom (A := ℚ_[l]) (φ.comp H.subtype) hψ
        (resCoef ℚ_[l] ((colRep r).comp H.subtype : Representation E H _))
        (resCoef ℚ_[l] ((colRep r').comp H.subtype : Representation (DualNumber E) H _))
        (resCoef ℚ_[l] ((extRep (adGL r) y hy.2).comp H.subtype : Representation E H _))
        (contAction_sub _ cV H) (contAction_sub _ cW H) (contAction_sub _ cH H) (pair ℚ_[l] n)
        (fun g w v => hb g w v) (fun w w' h => ?_)).1 hV hW
      refine Prod.ext (Matrix.ext_iff_mulVec.2 fun v => funext fun i => ?_) ?_
      · rw [← pair_snd ℚ_[l], ← pair_snd ℚ_[l], h]
      · have := pair_fst ℚ_[l] n w 1 ⟨0, hn⟩
        rw [h, pair_fst] at this
        simpa using this.symm
  · rintro ⟨hV, hy'⟩
    refine (admissible_of_bilinear_openSubgroup_galois (A := ℚ_[l]) (φ.comp H.subtype) hψ
        (resCoef ℚ_[l] ((extRep (adGL r) y hy.2).comp H.subtype : Representation E H _))
        (resCoef ℚ_[l] ((colRep r).comp H.subtype : Representation E H _))
        (resCoef ℚ_[l] ((colRep r').comp H.subtype : Representation (DualNumber E) H _))
        (contAction_sub _ cH H) (contAction_sub _ cV H) (contAction_sub _ cW H) (pair ℚ_[l] n)
        (fun g w v => hb g w v) ?_).1 ((key hV).2 hy') hV
    refine eq_top_iff.2 fun x _ => ?_
    have : x = pair ℚ_[l] n (0, 1) (fun i => (x i).fst) + pair ℚ_[l] n (1, 0) (fun i => (x i).snd) := by
      funext i
      refine TrivSqZeroExt.ext ?_ ?_ <;> simp [pair_fst, pair_snd]
    rw [this]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨(_, _), rfl⟩) (Submodule.subset_span ⟨(_, _), rfl⟩)
