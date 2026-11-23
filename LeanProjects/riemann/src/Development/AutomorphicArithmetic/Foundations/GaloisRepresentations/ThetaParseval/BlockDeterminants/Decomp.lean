import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Development.WeilBound.ThetaLifts.LatticeBasics.CommuteTheta
import Development.WeilBound.ThetaLifts.LatticeBasics.EulerProd
import Development.WeilBound.ThetaLifts.TowerModels.StabEx
import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.TracePiReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleEqZeroOfComp

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TP

open GlobalTheory.ThK.Dbl.Euler (cut cut_mul cut_form cut_sub cut_eq cut_one mm cont_mat prj)

section Cut

variable {S R k : Type} [CommRing S] [CommRing R] [Algebra S R] [Fintype k] [DecidableEq k]

private theorem cut_add {a b : S} (ha : a * a = a) (hb : b * b = b) (hab : a * b = 0) (A : Matrix k k R) :
    cut a A * cut b A = cut (a + b) A := by
  have h0 : b * a = 0 := by rw [mul_comm]; exact hab
  have h1 : (1 - b) * (1 - a) = 1 - (a + b) := by linear_combination hab
  have h2 : b * (1 - a) = b := by linear_combination -hab
  have h3 : (1 - b) * a = a := by linear_combination -hab
  simp only [cut, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, h0, h1, h2, h3, zero_smul, add_zero,
    Matrix.one_mul, Matrix.mul_one, add_smul]
  abel

private theorem cut_zero (A : Matrix k k R) : cut (0 : S) A = 1 := by simp [cut]

private theorem cut_self (A : Matrix k k R) : cut (1 : S) A = A := by simp [cut]

end Cut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {X : Spc F E n}

private def pr (e : AF F) (he : e * e = e) : UA σ X.J →* UA σ X.J :=
  MonoidHom.mk' (fun g => ⟨⟨cut e (mat g), cut e (mat g⁻¹),
    by rw [cut_mul he, ← mm, mul_inv_cancel]; exact cut_one, by rw [cut_mul he, ← mm, inv_mul_cancel]; exact cut_one⟩,
    cut_form he _ g.2⟩) fun g h => Subtype.ext (Units.ext (cut_mul he _ _).symm)

private theorem mat_pr {e : AF F} (he : e * e = e) (g : UA σ X.J) : mat (pr e he g) = cut e (mat g) := rfl

private theorem pr_eq {e : AF F} {he : e * e = e} {g : UA σ X.J} : pr e he g = g ↔ e • (mat g - 1) = mat g - 1 :=
  ⟨fun h => cut_eq.1 (congrArg mat h), fun h => Subtype.ext (Units.ext (cut_eq.2 h))⟩

private theorem pr_one {e : AF F} {he : e * e = e} {g : UA σ X.J} (h : e • (mat g - 1) = 0) : pr e he g = 1 := by
  refine Subtype.ext (Units.ext (sub_eq_zero.1 ?_))
  exact (cut_sub (mat g)).trans h

private theorem cont_pr {e : AF F} (he : e * e = e) : Continuous (pr e he : UA σ X.J → UA σ X.J) := by
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  have c1 : Continuous fun g : UA σ X.J => cut e (mat g) := by
    have := cont_mat (σ := σ) (Y := X)
    unfold cut
    refine continuous_matrix fun i j => ?_
    have := this.matrix_elem i j
    simp only [Matrix.add_apply, Matrix.smul_apply]
    fun_prop
  have c2 : Continuous fun g : UA σ X.J => cut e (mat g⁻¹) := c1.comp continuous_inv
  exact Continuous.subtype_mk (Units.continuous_iff.2 ⟨c1, c2⟩) _

private theorem closed_fix {e : AF F} (he : e * e = e) : IsClosed {g : UA σ X.J | e • (mat g - 1) = mat g - 1} := by
  have := (Euler.lcsc_UA σ X.J).2.2
  have e1 : {g : UA σ X.J | e • (mat g - 1) = mat g - 1} = {g | pr e he g = g} := Set.ext fun _ => pr_eq.symm
  rw [e1]
  exact isClosed_eq (cont_pr he) continuous_id

private theorem idem_mul_ne {u v : Pl F} (h : u ≠ v) : (Euler.idem u : AF F) * Euler.idem v = 0 :=
  Euler.mul_idem (Euler.ev_ne h.symm)

private theorem sum_fst (T : Finset (Pl F)) : (∑ v ∈ T, (Euler.idem v : AF F)).1 = 0 := by
  classical
  induction T using Finset.induction_on with
  | empty => rfl
  | insert v T hv ih =>
    rw [Finset.sum_insert hv]
    change (0 : Ainf F) + _ = 0
    rw [ih, add_zero]

private theorem idem_mul_sum {T : Finset (Pl F)} {v : Pl F} (h : v ∈ T) :
    (Euler.idem v : AF F) * ∑ u ∈ T, Euler.idem u = Euler.idem v := by
  classical
  rw [Finset.mul_sum, Finset.sum_eq_single v (fun u _ hu => idem_mul_ne hu.symm) (fun h' => absurd h h'), Euler.idem_sq]

private theorem idem_mul_sum_off {T : Finset (Pl F)} {v : Pl F} (h : v ∉ T) :
    (Euler.idem v : AF F) * ∑ u ∈ T, Euler.idem u = 0 := by
  rw [Finset.mul_sum]
  exact Finset.sum_eq_zero fun u hu => idem_mul_ne fun e => h (e ▸ hu)

private theorem sum_sq (T : Finset (Pl F)) :
    (∑ v ∈ T, (Euler.idem v : AF F)) * ∑ v ∈ T, (Euler.idem v : AF F) = ∑ v ∈ T, (Euler.idem v : AF F) := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun v hv => idem_mul_sum hv

private theorem eps_sq : realAd F 1 * realAd F 1 = realAd F 1 :=
  Prod.ext (by
    change (realAd F 1).1 * (realAd F 1).1 = (realAd F 1).1
    rw [PositivityTheory.ThKG.Loc.Bump.eps_fst, one_mul]) (by
    change (realAd F 1).2 * (realAd F 1).2 = (realAd F 1).2
    rw [PositivityTheory.ThKG.Loc.Bump.eps_snd, zero_mul])

private theorem eps_mul_sum (T : Finset (Pl F)) : realAd F 1 * ∑ v ∈ T, (Euler.idem v : AF F) = 0 :=
  Prod.ext (by
    change (realAd F 1).1 * (∑ v ∈ T, (Euler.idem v : AF F)).1 = 0
    rw [sum_fst, mul_zero]) (by
    change (realAd F 1).2 * (∑ v ∈ T, (Euler.idem v : AF F)).2 = 0
    rw [PositivityTheory.ThKG.Loc.Bump.eps_snd, zero_mul])

private theorem pr_sum_mem (H : Subgroup (UA σ X.J)) (g : UA σ X.J) (T : Finset (Pl F)) (h : ∀ v ∈ T, prj v g ∈ H) :
    pr (∑ v ∈ T, Euler.idem v) (sum_sq T) g ∈ H := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have : pr (∑ v ∈ (∅ : Finset (Pl F)), Euler.idem v) (sum_sq ∅) g = 1 :=
      Subtype.ext (Units.ext (show cut _ (mat g) = 1 by rw [Finset.sum_empty]; exact cut_zero _))
    rw [this]
    exact one_mem _
  | insert v T hv ih =>
    have : pr (∑ u ∈ insert v T, Euler.idem u) (sum_sq _) g = prj v g * pr (∑ u ∈ T, Euler.idem u) (sum_sq T) g :=
      Subtype.ext (Units.ext (by
        change cut _ (mat g) = cut (Euler.idem v) (mat g) * cut _ (mat g)
        rw [cut_add (Euler.idem_sq v) (sum_sq T) (idem_mul_sum_off hv), Finset.sum_insert hv]))
    rw [this]
    exact mul_mem (h v (Finset.mem_insert_self _ _)) (ih fun u hu => h u (Finset.mem_insert_of_mem hu))

private theorem mem_gInf {g : UA σ X.J} : g ∈ gInf σ X ↔ realAd F 1 • (mat g - 1) = mat g - 1 := by
  refine ⟨fun h => ?_, fun h => Subgroup.subset_closure (PositivityTheory.ThKG.Loc.Bump.at_iff.2 h)⟩
  have : gInf σ X ≤ (pr (σ := σ) (X := X) (realAd F 1) eps_sq).eqLocus (MonoidHom.id _) :=
    (Subgroup.closure_le _).2 fun g hg => pr_eq.2 (PositivityTheory.ThKG.Loc.Bump.at_iff.1 hg)
  exact pr_eq.1 (this h)

private theorem mem_gAt {S : Finset (Pl F)} {g : UA σ X.J} :
    g ∈ gAt σ X S ↔ (∑ v ∈ S, (Euler.idem v : AF F)) • (mat g - 1) = mat g - 1 := by
  constructor
  · intro h
    have : gAt σ X S ≤ (pr (σ := σ) (X := X) (∑ v ∈ S, Euler.idem v) (sum_sq S)).eqLocus (MonoidHom.id _) :=
      iSup₂_le fun v hv g hg => pr_eq.2 (by
        have e : Euler.idem v • (mat g - 1) = mat g - 1 := (pr_eq (he := Euler.idem_sq v)).1 (Euler.mem_loc.1 hg)
        rw [← e, smul_smul, mul_comm, idem_mul_sum hv])
    exact pr_eq.1 (this h)
  · intro h
    rw [← pr_eq (he := sum_sq S)] at h
    rw [← h]
    exact pr_sum_mem _ g S fun v hv => (le_iSup₂_of_le v hv le_rfl : locGrp σ X v ≤ gAt σ X S) (Euler.prj_mem g)

private theorem smul_off {v : Pl F} {g : UA σ X.J} (h : OffAt v g) : Euler.idem v • (mat g - 1) = 0 :=
  Matrix.ext fun i j => Bad.idem_off (by
    have := congrFun₂ h i j
    rw [Matrix.map_apply] at this
    simp [this, Matrix.one_apply, apply_ite (compFin F E v)])

private theorem eps_of_inf {g : UA σ X.J} (h : ∀ w : InfinitePlace F, (mat g).map (compInf F E w) = 1) :
    realAd F 1 • (mat g - 1) = 0 :=
  Matrix.ext fun i j => GlobalTheory.SWOpFin.tens_eq_zero_of_comp (fun v => PositivityTheory.ThKG.Loc.Bump.compFin_eps v _) fun w => by
    change compInf F E w (realAd F 1 • (mat g - 1) i j) = 0
    rw [PositivityTheory.ThKG.Loc.Bump.compInf_eps]
    have := congrFun₂ (h w) i j
    rw [Matrix.map_apply] at this
    simp [this, Matrix.one_apply, apply_ite (compInf F E w)]

private theorem inf_of_eps {g : UA σ X.J} (h : realAd F 1 • (mat g - 1) = 0) (w : InfinitePlace F) :
    (mat g).map (compInf F E w) = 1 := by
  ext i j
  have := PositivityTheory.ThKG.Loc.Bump.compInf_eps (E := E) w ((mat g - 1) i j)
  rw [show realAd F 1 • (mat g - 1) i j = 0 from congrFun₂ h i j, map_zero, Matrix.sub_apply, map_sub] at this
  rw [Matrix.map_apply, sub_eq_zero.1 this.symm]
  simp [Matrix.one_apply, apply_ite (compInf F E w)]

private theorem mem_gOff {S : Finset (Pl F)} {g : UA σ X.J} :
    g ∈ gOff σ X S ↔ (1 - realAd F 1 - ∑ v ∈ S, (Euler.idem v : AF F)) • (mat g - 1) = mat g - 1 := by
  set b := ∑ v ∈ S, (Euler.idem v : AF F) with hb
  have key : (1 - realAd F 1 - b) * (1 - realAd F 1 - b) = 1 - realAd F 1 - b := by
    have h1 := eps_sq (F := F)
    have h2 := sum_sq S
    have h3 := eps_mul_sum S
    rw [← hb] at h2 h3
    linear_combination h1 + h2 + 2 * h3
  constructor
  · intro h
    have : gOff σ X S ≤ (pr (σ := σ) (X := X) _ key).eqLocus (MonoidHom.id _) :=
      (Subgroup.closure_le _).2 fun g ⟨h1, h2⟩ => pr_eq.2 (by
        have e1 := eps_of_inf h1
        have e2 : b • (mat g - 1) = 0 := by
          rw [hb, Finset.sum_smul]
          exact Finset.sum_eq_zero fun v hv => smul_off (h2 v hv)
        rw [sub_smul, sub_smul, one_smul, e1, e2, sub_zero, sub_zero])
    exact pr_eq.1 (this h)
  · intro h
    refine Subgroup.subset_closure ⟨inf_of_eps ?_, fun v hv => ?_⟩
    · have h3 := eps_mul_sum (F := F) S
      have h4 := eps_sq (F := F)
      rw [← hb] at h3
      rw [← h, smul_smul, show realAd F 1 * (1 - realAd F 1 - b) = 0 by linear_combination -h3 - h4, zero_smul]
    · refine Euler.off_of (pr_one (he := Euler.idem_sq v) ?_)
      have h3 : (Euler.idem v : AF F) * realAd F 1 = 0 := by
        refine Prod.ext ?_ ?_
        · exact zero_mul _
        · exact mul_zero _
      have h4 := idem_mul_sum hv
      have h5 := Euler.idem_sq v
      rw [← hb] at h4
      rw [← h, smul_smul, show (Euler.idem v : AF F) * (1 - realAd F 1 - b) = 0 by linear_combination -h3 - h4, zero_smul]

private theorem pr_one_of {e f : AF F} {he : e * e = e} (h : e * f = 0) {g : UA σ X.J} (hg : f • (mat g - 1) = mat g - 1) :
    pr e he g = 1 :=
  pr_one (by rw [← hg, smul_smul, h, zero_smul])

private theorem inf_int {g : UA σ X.J} (h : g ∈ gInf σ X) : IntAll g := fun v => by
  have e : (Euler.idem v : AF F) * realAd F 1 = 0 := Prod.ext (zero_mul _) (mul_zero _)
  have : prj v g = 1 := pr_one_of (he := Euler.idem_sq v) e (mem_gInf.1 h)
  refine Euler.int_prj.1 ?_
  rw [this]
  exact one_mem (Euler.intGrp σ X v)

private theorem pr_fix {e : AF F} (he : e * e = e) (g : UA σ X.J) :
    e • (mat (pr e he g) - 1) = mat (pr e he g) - 1 := by
  rw [mat_pr, cut_sub, smul_smul, he]

private theorem prod_equiv {P Q R : Subgroup (UA σ X.J)} {a b c : AF F} (ha : a * a = a) (hb : b * b = b) (hc : c * c = c)
    (hab : a * b = 0) (hac : a * c = 0) (hbc : b * c = 0) (hs : a + b + c = 1) (hP : ∀ g, g ∈ P ↔ a • (mat g - 1) = mat g - 1)
    (hQ : ∀ g, g ∈ Q ↔ b • (mat g - 1) = mat g - 1) (hR : ∀ g, g ∈ R ↔ c • (mat g - 1) = mat g - 1) :
    ∃ j : P × Q × R ≃ₜ* UA σ X.J, ∀ x, j x = x.1.1 * x.2.1.1 * x.2.2.1 := by
  have hba : b * a = 0 := by rw [mul_comm]; exact hab
  have hca : c * a = 0 := by rw [mul_comm]; exact hac
  have hcb : c * b = 0 := by rw [mul_comm]; exact hbc
  have hd : (a + b) * (a + b) = a + b := by linear_combination ha + hb + 2 * hab
  have hdc : (a + b) * c = 0 := by linear_combination hac + hbc
  let φ : UA σ X.J ≃ₜ* P × Q × R :=
    { toFun := fun g => (⟨pr a ha g, (hP _).2 (pr_fix ha g)⟩, ⟨pr b hb g, (hQ _).2 (pr_fix hb g)⟩,
        ⟨pr c hc g, (hR _).2 (pr_fix hc g)⟩)
      invFun := fun x => x.1.1 * x.2.1.1 * x.2.2.1
      left_inv := fun g => Subtype.ext (Units.ext (show cut a (mat g) * cut b (mat g) * cut c (mat g) = mat g by
        rw [cut_add ha hb hab, cut_add hd hc hdc, hs, cut_self]))
      right_inv := fun x => by
        obtain ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩⟩ := x
        have p1 := (hP p).1 hp
        have q1 := (hQ q).1 hq
        have r1 := (hR r).1 hr
        refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
        · change pr a ha (p * q * r) = p
          rw [map_mul, map_mul, pr_eq.2 p1, pr_one_of hab q1, pr_one_of hac r1, mul_one, mul_one]
        · change pr b hb (p * q * r) = q
          rw [map_mul, map_mul, pr_eq.2 q1, pr_one_of hba p1, pr_one_of hbc r1, mul_one, one_mul]
        · change pr c hc (p * q * r) = r
          rw [map_mul, map_mul, pr_eq.2 r1, pr_one_of hca p1, pr_one_of hcb q1, one_mul, one_mul]
      map_mul' := fun g h => Prod.ext (Subtype.ext (map_mul _ _ _)) (Prod.ext (Subtype.ext (map_mul _ _ _))
        (Subtype.ext (map_mul _ _ _)))
      continuous_toFun := ((cont_pr ha).subtype_mk _).prodMk (((cont_pr hb).subtype_mk _).prodMk ((cont_pr hc).subtype_mk _))
      continuous_invFun := ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))).mul
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)) }
  exact ⟨φ.symm, fun x => rfl⟩

end UpperTheory.TP

theorem UpperTheory.TP.decomp :
    UpperTheory.TP.Tools → UpperTheory.TP.Decomp := by
  intro _ F E _ _ _ _ _ σ B n X hB hX S
  have h00 : min n 0 = 0 := by simp
  obtain ⟨K, -, -, hK, hKc, -, -⟩ := PositivityTheory.ThKG.Tow.stabEx F E σ B n X n 0 hB hX
  have eK : (K : Set (UA σ X.J)) = {g | IntAll g} := Set.ext fun g => Bad.stab_iff hB hX h00 hK
  have h1 := eps_sq (F := F)
  have h2 := sum_sq (F := F) S
  have h3 := eps_mul_sum (F := F) S
  have cI : IsClosed (gInf σ X : Set (UA σ X.J)) := by
    rw [show (gInf σ X : Set (UA σ X.J)) = {g | realAd F 1 • (mat g - 1) = mat g - 1} from Set.ext fun _ => mem_gInf]
    exact closed_fix h1
  have hc : (1 - realAd F 1 - ∑ v ∈ S, (Euler.idem v : AF F)) * (1 - realAd F 1 - ∑ v ∈ S, (Euler.idem v : AF F)) =
      1 - realAd F 1 - ∑ v ∈ S, (Euler.idem v : AF F) := by linear_combination h1 + h2 + 2 * h3
  refine ⟨prod_equiv h1 h2 hc h3 (by linear_combination -h3 - h1) (by linear_combination -h3 - h2) (by ring)
      (fun _ => mem_gInf) (fun _ => mem_gAt) (fun _ => mem_gOff),
    (eK ▸ hKc).of_isClosed_subset cI fun g hg => inf_int hg, ?_, ?_, eK ▸ hKc, ?_, fun g hg => inf_int hg, fun b hb => ?_, fun g => ?_⟩
  · rw [show (gAt σ X S : Set (UA σ X.J)) = {g | (∑ v ∈ S, (Euler.idem v : AF F)) • (mat g - 1) = mat g - 1} from
      Set.ext fun _ => mem_gAt]
    exact closed_fix h2
  · rw [show (gOff σ X S : Set (UA σ X.J)) =
      {g | (1 - realAd F 1 - ∑ v ∈ S, (Euler.idem v : AF F)) • (mat g - 1) = mat g - 1} from Set.ext fun _ => mem_gOff]
    exact closed_fix hc
  · rw [← eK]
    exact Subgroup.isOpen_of_mem_nhds K (g := 1) (by rw [eK]; exact Bad.int_nhds hX.lat)
  · refine ⟨fun v => Euler.prj v b, fun v => Euler.prj_mem b, fun v _ => Euler.off_of ?_, fun H hH => ?_⟩
    · rw [map_mul, map_inv, Euler.mem_loc.1 (Euler.prj_mem b), inv_mul_cancel]
    · have := pr_sum_mem H b S hH
      rwa [pr_eq.2 (mem_gAt.1 hb)] at this
  · exact (Filter.eventually_cofinite.1 ((Euler.ae_mulVec hX.lat (mat g)).and (Euler.ae_mulVec hX.lat (mat g⁻¹)))).subset
      fun v hv h => hv fun z hz h3 => ⟨h.1 z hz h3, h.2 z hz h3⟩
