import Development.WeilBound.ThetaLifts.LatticeBasics.HodgeTateFromSandwich
import Development.WeilBound.ThetaLifts.LatticeBasics.FdEqZero
import Development.WeilBound.ThetaLifts.LatticeBasics.EulerA
import Development.WeilBound.ThetaLifts.LatticeBasics.EulerB

noncomputable section

namespace GlobalTheory.ThK.Dbl.Euler

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section Cut

variable {S R k : Type} [CommRing S] [CommRing R] [Algebra S R] [Fintype k] [DecidableEq k] {e : S}

def cut (e : S) (A : Matrix k k R) : Matrix k k R := (1 - e) • 1 + e • A

theorem mix (he : e * e = e) (A B C D : Matrix k k R) :
    ((1 - e) • A + e • B) * ((1 - e) • C + e • D) = (1 - e) • (A * C) + e • (B * D) := by
  have h1 : (1 - e) * (1 - e) = 1 - e := by linear_combination he
  have h2 : (1 - e) * e = 0 := by linear_combination -he
  have h3 : e * (1 - e) = 0 := by linear_combination -he
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, h1, h2, h3, he, zero_smul, add_zero,
    zero_add]

theorem cut_mul (he : e * e = e) (A B : Matrix k k R) : cut e A * cut e B = cut e (A * B) := by
  rw [cut, cut, mix he, mul_one, cut]

theorem cut_sub (A : Matrix k k R) : cut e A - 1 = e • (A - 1) := by
  rw [cut, sub_smul, one_smul, smul_sub]; abel

theorem cut_eq {A : Matrix k k R} : cut e A = A ↔ e • (A - 1) = A - 1 := by rw [← cut_sub, sub_left_inj]

theorem cut_one : cut e (1 : Matrix k k R) = 1 := cut_eq.2 (by simp)

theorem cut_cut (he : e * e = e) (A : Matrix k k R) : cut e (cut e A) = cut e A :=
  cut_eq.2 (by rw [cut_sub, smul_smul, he])

theorem cut_form (he : e * e = e) (c : R →ₐ[S] R) {J A : Matrix k k R} (h : Aᵀ * J * A.map c = J) :
    (cut e A)ᵀ * J * (cut e A).map c = J := by
  have e1 : (cut e A).map c = (1 - e) • 1 + e • A.map c := by
    ext i j
    simp [cut, Matrix.one_apply, apply_ite c]
  have e2 : J = (1 - e) • J + e • J := by rw [← add_smul, sub_add_cancel, one_smul]
  rw [e1, cut, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one]
  conv_lhs => rw [e2]
  rw [mix he, mix he, h, one_mul, mul_one, ← e2]

end Cut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem lcsc_UA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    LocallyCompactSpace (UA σ J) ∧ SecondCountableTopology (UA σ J) ∧ T2Space (UA σ J) := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (AE F E) := e.secondCountableTopology
  have : T2Space (AE F E) := e.isEmbedding.t2Space
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AE F E))
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  have : LocallyCompactSpace (GL (Fin n) (AE F E)) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (GL (Fin n) (AE F E)) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  have : T2Space (GL (Fin n) (AE F E)) := Units.isEmbedding_embedProduct.t2Space
  have hs : Continuous (cA σ : AE F E → AE F E) :=
    IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hc : IsClosed (UG (cA σ) (incM F J) : Set (GL (Fin n) (AE F E))) := by
    have hv : Continuous fun g : GL (Fin n) (AE F E) => (g : Matrix (Fin n) (Fin n) (AE F E)) :=
      Units.continuous_val
    exact isClosed_eq ((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul (hv.matrix_map hs))
      continuous_const
  exact ⟨hc.isClosedEmbedding_subtypeVal.locallyCompactSpace, IsEmbedding.subtypeVal.secondCountableTopology,
    IsEmbedding.subtypeVal.t2Space⟩

variable {Y : Spc F E n} {v : Pl F}

theorem mm (g h : UA σ Y.J) : mat (g * h) = mat g * mat h := rfl

def prj (v : Pl F) : UA σ Y.J →* UA σ Y.J := MonoidHom.mk' (fun g => ⟨⟨cut (idem v) (mat g), cut (idem v) (mat g⁻¹),
    by rw [cut_mul (idem_sq v), ← mm, mul_inv_cancel]; exact cut_one, by rw [cut_mul (idem_sq v), ← mm, inv_mul_cancel]; exact cut_one⟩,
    cut_form (idem_sq v) _ g.2⟩) fun g h => Subtype.ext (Units.ext (cut_mul (idem_sq v) _ _).symm)

theorem mem_loc {g : UA σ Y.J} : g ∈ locGrp σ Y v ↔ prj v g = g := by
  have e : ∀ g : UA σ Y.J, g ∈ UAt σ Y (evFin F v) ↔ prj v g = g := fun g =>
    at_iff.trans (cut_eq.symm.trans ⟨fun h => Subtype.ext (Units.ext h), fun h => congrArg mat h⟩)
  refine ⟨fun h => ?_, fun h => Subgroup.subset_closure ((e g).2 h)⟩
  exact (Subgroup.closure_le ((prj v).eqLocus (MonoidHom.id _))).2 (fun g hg => (e g).1 hg) h

theorem prj_mem (g : UA σ Y.J) : prj v g ∈ locGrp σ Y v := mem_loc.2 (Subtype.ext (Units.ext (cut_cut (idem_sq v) _)))

theorem cont_mat : Continuous fun g : UA σ Y.J => mat g := Units.continuous_val.comp continuous_subtype_val

theorem cont_prj : Continuous (prj v : UA σ Y.J → UA σ Y.J) := by
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  have c1 : Continuous fun g : UA σ Y.J => cut (idem v) (mat g) := by
    have := cont_mat (σ := σ) (Y := Y)
    unfold cut
    refine continuous_matrix fun i j => ?_
    have := this.matrix_elem i j
    simp only [Matrix.add_apply, Matrix.smul_apply]
    fun_prop
  have c2 : Continuous fun g : UA σ Y.J => cut (idem v) (mat g⁻¹) := c1.comp continuous_inv
  exact Continuous.subtype_mk (Units.continuous_iff.2 ⟨c1, c2⟩) _

theorem off_of {g : UA σ Y.J} (h : prj v g = 1) : OffAt v g := by
  have e : idem v • (mat g - 1) = 0 := by rw [← cut_sub, show cut (idem v) (mat g) = 1 from congrArg mat h, sub_self]
  have c : ∀ x : AE F E, compFin F E v (idem v • x) = compFin F E v x := fun x => by
    rw [Algebra.smul_def, map_mul, show compFin F E v (algebraMap _ _ (idem v)) = evFin F v (idem v) ⊗ₜ 1 from rfl, ev_self]
    exact one_mul _
  rw [OffAt, ← Matrix.map_one (compFin F E v) (map_zero _) (map_one _)]
  ext i j
  have := c ((mat g - 1) i j)
  rw [show idem v • (mat g - 1) i j = 0 from congrFun (congrFun e i) j, map_zero, Matrix.sub_apply, map_sub] at this
  exact sub_eq_zero.1 this.symm

theorem at_mulVec (A : Matrix (Fin n) (Fin n) (AE F E)) {z : Fin n → AE F E} (h : At (evFin F v) z) : At (evFin F v) (A *ᵥ z) :=
  fun u hu => by rw [← Matrix.mulVec_smul, h u hu, Matrix.mulVec_zero]

theorem prj_mulVec (g : UA σ Y.J) {z : Fin n → AE F E} (h : At (evFin F v) z) : mat (prj v g) *ᵥ z = mat g *ᵥ z := by
  show cut (idem v) (mat g) *ᵥ z = _
  rw [cut, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_smul, one_smul, at_iff.1 h,
    at_iff.1 (at_mulVec _ h), sub_self, zero_add]

theorem int_prj {g : UA σ Y.J} : IntAt v (prj v g) ↔ IntAt v g :=
  forall₂_congr fun z _ => forall_congr' fun h => by rw [← map_inv, prj_mulVec _ h, prj_mulVec _ h]

theorem prj_ne {u : Pl F} (h : u ≠ v) {g : UA σ Y.J} (hg : g ∈ locGrp σ Y v) : prj u g = 1 := by
  refine Subtype.ext (Units.ext (sub_eq_zero.1 ((cut_sub (mat g)).trans ?_)))
  rw [← cut_eq.1 (congrArg mat (mem_loc.1 hg)), smul_smul, mul_idem (ev_ne h.symm), zero_smul]

theorem int_mul_ne {u : Pl F} (h : u ≠ v) {x : UA σ Y.J} (hx : x ∈ locGrp σ Y v) (g : UA σ Y.J) : IntAt u (x * g) ↔ IntAt u g := by
  rw [← int_prj, map_mul, prj_ne h hx, one_mul, int_prj]

variable (σ Y) in

def intGrp (v : Pl F) : Subgroup (UA σ Y.J) where
  carrier := {g | IntAt v g}
  one_mem' := fun z hz _ => by rw [inv_one, show mat (1 : UA σ Y.J) = 1 from rfl, Matrix.one_mulVec]; exact ⟨hz, hz⟩
  mul_mem' := fun ha hb z hz h => by
    rw [mul_inv_rev, mm, mm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ⟨(ha _ (hb z hz h).1 (at_mulVec _ h)).1, (hb _ (ha z hz h).2 (at_mulVec _ h)).2⟩
  inv_mem' := fun ha z hz h => by rw [inv_inv]; exact (ha z hz h).symm

theorem isClosed_int (hL : Y.L.IsLattice E) (v : Pl F) : IsClosed {g : UA σ Y.J | IntAt v g} := by
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  simp only [IntAt, Set.setOf_forall]
  exact isClosed_iInter fun z => isClosed_iInter fun _ => isClosed_iInter fun _ =>
    ((isClosed_latHat hL).preimage (cont_mat.matrix_mulVec continuous_const)).inter
      ((isClosed_latHat hL).preimage ((cont_mat.comp continuous_inv).matrix_mulVec continuous_const))

theorem isClosed_loc : IsClosed (locGrp σ Y v : Set (UA σ Y.J)) := by
  have := (lcsc_UA σ Y.J).2.2
  rw [show (locGrp σ Y v : Set (UA σ Y.J)) = {g | prj v g = g} from Set.ext fun _ => mem_loc]
  exact isClosed_eq cont_prj continuous_id

theorem lcsc_loc (v : Pl F) : LocallyCompactSpace (locGrp σ Y v) ∧ SecondCountableTopology (locGrp σ Y v) := by
  obtain ⟨a1, a2, a3⟩ := lcsc_UA σ Y.J
  exact ⟨isClosed_loc.isClosedEmbedding_subtypeVal.locallyCompactSpace, IsEmbedding.subtypeVal.secondCountableTopology⟩

theorem step (hL : Y.L.IsLattice E) {μ : Measure (UA σ Y.J)} (hμ : μ.IsHaarMeasure) {ν : Measure (locGrp σ Y v)}
    (hν : ν.IsHaarMeasure) (h1 : ν {g | IntAt v g.1} = 1) {f l : UA σ Y.J → ℂ} (hf : Integrable f μ)
    (hl : ∀ u ∈ locGrp σ Y v, ∀ g, OffAt v g → f (u * g) = l u * f g) (hl1 : ∀ u ∈ locGrp σ Y v, IntAt v u → l u = 1)
    {P : Set (Pl F)} (hv : v ∉ P) :
    ∫ g in {g | ∀ u ∈ P, IntAt u g}, f g ∂μ = (∫ u, l u.1 ∂ν) * ∫ g in {g | ∀ u ∈ insert v P, IntAt u g}, f g ∂μ := by
  obtain ⟨a1, a2, a3⟩ := lcsc_UA σ Y.J
  obtain ⟨b1, b2⟩ := lcsc_loc (σ := σ) (Y := Y) v
  have mA : MeasurableSet {g : UA σ Y.J | ∀ u ∈ P, IntAt u g} := by
    simp only [Set.setOf_forall]
    exact (isClosed_iInter fun u => isClosed_iInter fun _ => isClosed_int hL u).measurableSet
  rw [factor (ν := ν) (K := (intGrp σ Y v).subgroupOf (locGrp σ Y v)) (l := fun u => l u.1)
    ((isClosed_int hL v).preimage continuous_subtype_val).measurableSet h1 (locGrp σ Y v).subtype continuous_subtype_val
    (fun g => ⟨prj v g, prj_mem g⟩) (cont_prj.subtype_mk _)
    (fun u g => Subtype.ext ((map_mul _ _ _).trans (congrArg (· * prj v g) (mem_loc.1 u.2)))) hf
    (fun u g h => hl u u.2 g (off_of (congrArg Subtype.val h))) (fun u hu => hl1 u u.2 hu) mA
    (fun u g => forall₂_congr fun w hw => int_mul_ne (fun e : w = v => hv (e ▸ hw)) u.2 g)]
  congr 3
  ext g
  rw [Set.mem_setOf_eq, Set.forall_mem_insert, and_comm]
  exact and_congr_right' int_prj

theorem _root_.GlobalTheory.ThK.Dbl.eulerProd : EulerProd := by
  intro F E _ _ _ _ _ σ B n Y r s _ hY T μ hμ μl hl f fl hf h
  classical
  let A : Finset {v : Pl F // v ∉ T} → Set (UA σ Y.J) := fun S => {g | ∀ u ∈ {u | ∃ h : u ∉ T, ⟨u, h⟩ ∉ S}, IntAt u g}
  have e : ∀ S, (∏ v ∈ S, ∫ u, fl v.1 u.1 ∂μl v.1) * ∫ g in {g | ∀ v ∉ T, IntAt v g}, f g ∂μ = ∫ g in A S, f g ∂μ := fun S => by
    induction S using Finset.induction_on with
    | empty => simp [A]
    | insert v S hv ih =>
      rw [Finset.prod_insert hv, mul_assoc, ih]
      refine Eq.trans ?_ (step hY.lat hμ (hl v).1 (hl v).2 hf (h v v.2).1 (h v v.2).2.1
        (P := {u | ∃ h : u ∉ T, ⟨u, h⟩ ∉ insert v S}) (by rintro ⟨_, h'⟩; exact h' (Finset.mem_insert_self _ _))).symm
      congr 3
      ext g
      refine forall_congr' fun u => imp_congr_left ⟨fun ⟨h1, h2⟩ => ?_, ?_⟩
      · by_cases e : u = v.1
        · exact .inl e
        · exact .inr ⟨h1, fun h3 => (Finset.mem_insert.1 h3).elim (fun h4 => e (congrArg Subtype.val h4)) h2⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨v.2, hv⟩
        · exact ⟨h1, fun h3 => h2 (Finset.mem_insert_of_mem h3)⟩
  have u : ⋃ S, A S = Set.univ := Set.eq_univ_of_forall fun g => by
    have c := Filter.eventually_cofinite.1 ((ae_mulVec hY.lat (mat g)).and (ae_mulVec hY.lat (mat g⁻¹)))
    refine Set.mem_iUnion.2 ⟨c.toFinset.subtype _, fun u ⟨_, h2⟩ => ?_⟩
    rw [Finset.mem_subtype, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at h2
    exact fun z hz h3 => ⟨h2.1 z hz h3, h2.2 z hz h3⟩
  have := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  have := tendsto_setIntegral_of_monotone (s := A) (f := f) (μ := μ) (fun S => by
    simp only [A, Set.setOf_forall]
    exact (isClosed_iInter fun u => isClosed_iInter fun _ => isClosed_int hY.lat u).measurableSet)
    (fun S S' hS g hg u ⟨h1, h2⟩ => hg u ⟨h1, fun h3 => h2 (hS h3)⟩) hf.integrableOn
  simpa only [e, u, Measure.restrict_univ] using this

end GlobalTheory.ThK.Dbl.Euler

end
