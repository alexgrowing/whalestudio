import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneSubIdemQMulSelf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlaceOfSupportedStabilizer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.KOpen

variable {D : D7}

open Classical in

def indP (D : D7) (P : Pl D → Prop) : Af D.host.F :=
  ⟨fun v => if P v then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : P v
    · simp only [if_pos h]; exact one_mem (v.adicCompletionIntegers D.host.F)
    · simp only [if_neg h]; exact zero_mem (v.adicCompletionIntegers D.host.F)⟩

open Classical in
theorem evalV_indP (P : Pl D → Prop) (w : Pl D) : evalV D.host.F w (indP D P) = if P w then 1 else 0 := rfl

theorem indicatorAdele_integral (P : Pl D → Prop) : indP D P ∈ intAf D.host.F := fun w => by
  rw [evalV_indP]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem one_sub_indP_int (P : Pl D → Prop) : 1 - indP D P ∈ intAf D.host.F := fun w => by
  rw [map_sub, map_one, evalV_indP]
  split_ifs
  · rw [sub_self]; exact zero_mem _
  · rw [sub_zero]; exact one_mem _

open Classical in
theorem compFin_e (P : Pl D → Prop) (w : Pl D) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (indP D P ⊗ₜ[D.host.F] (1 : D.host.E)) = if P w then 1 else 0 := by
  change evalV D.host.F w (indP D P) ⊗ₜ[D.host.F] (1 : D.host.E) = _
  rw [evalV_indP]
  split_ifs
  · rfl
  · exact TensorProduct.zero_tmul _ _

theorem e_mul_of_supp (P : Pl D → Prop) (X : Af D.host.F ⊗[D.host.F] D.host.E)
    (h : ∀ w, ¬ P w → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w X = 0) :
    (indP D P ⊗ₜ[D.host.F] (1 : D.host.E)) * X = X := by
  refine GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun w => ?_
  change GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w _ = GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w _
  rw [map_mul, compFin_e]
  by_cases hw : P w
  · rw [if_pos hw, one_mul]
  · rw [h w hw, mul_zero]

theorem e_mul_fin {P : Pl D → Prop} {a : AE D} (ha : a ∈ idAt D P) :
    (indP D P ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D a = finPart D a :=
  e_mul_of_supp P _ ((mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D P a).1 ha).2

set_option maxHeartbeats 800000 in

theorem exists_latticeCompletion_cut_to_places_finiteReal (S : HSp D) (L : Lat S) (P : Pl D → Prop) {z : Fin S.rank → Af D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ latHat D.host.F D.host.E (L : Set (Fin S.rank → D.host.E))) :
    ∃ y ∈ latV S L P, (∀ i, infPart D (y i) = 0) ∧
      ∀ i, finPart D (y i) = (indP D P ⊗ₜ[D.host.F] (1 : D.host.E)) * z i := by
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      refine ⟨fun i => pairA D.host.F 0 (indP D P * a) ⊗ₜ[D.host.F] (1 * x i),
        AddSubgroup.subset_closure ⟨_, GlobalTheory.KStabBridge.intAf_mul (indicatorAdele_integral P) ha, fun w hw => ?_, 1, rfl, x, hx, rfl⟩,
        fun i => GlobalTheory.KStabBridge.infPart_pair _ _, fun i => ?_⟩
      · rw [map_mul, evalV_indP, if_neg hw, zero_mul]
      · rw [GlobalTheory.KStabBridge.finPart_pair, one_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    | zero =>
      refine ⟨0, zero_mem (latV S L P), fun i => (infPart D).map_zero, fun i => ?_⟩
      show finPart D 0 = (indP D P ⊗ₜ[D.host.F] (1 : D.host.E)) * 0
      rw [mul_zero]; exact (finPart D).map_zero
    | add z z' _ _ h h' =>
      obtain ⟨y, hy, h1, h2⟩ := h
      obtain ⟨y', hy', h1', h2'⟩ := h'
      exact ⟨y + y', add_mem hy hy', fun i => by rw [Pi.add_apply, (infPart D).map_add, h1, h1', add_zero],
        fun i => by rw [Pi.add_apply, (finPart D).map_add, h2, h2', Pi.add_apply, mul_add]⟩
    | neg z _ h =>
      obtain ⟨y, hy, h1, h2⟩ := h
      refine ⟨-y, neg_mem hy, fun i => ?_, fun i => ?_⟩
      · show infPart D (-(y i)) = 0
        rw [(infPart D).map_neg, h1, neg_zero]
      · show finPart D (-(y i)) = (indP D P ⊗ₜ[D.host.F] (1 : D.host.E)) * -(z i)
        rw [(finPart D).map_neg, h2, mul_neg]

theorem mem_idAt_of_fin (P : Pl D → Prop) {a : AE D} (h1 : infPart D a = 0) {z : Af D.host.F ⊗[D.host.F] D.host.E}
    (h2 : finPart D a = (indP D P ⊗ₜ[D.host.F] (1 : D.host.E)) * z) : a ∈ idAt D P := by
  refine (mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D P _).2 ⟨h1, fun w hw => ?_⟩
  change GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D a) = 0
  rw [h2, (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w).map_mul, compFin_e, if_neg hw, zero_mul]

theorem exists_lift_latV (S : HSp D) (L : Lat S) (P : Pl D → Prop) {z : Fin S.rank → Af D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ latHat D.host.F D.host.E (L : Set (Fin S.rank → D.host.E))) :
    ∃ y ∈ latV S L P, (∀ i, y i ∈ idAt D P) ∧
      ∀ i, finPart D (y i) = (indP D P ⊗ₜ[D.host.F] (1 : D.host.E)) * z i := by
  obtain ⟨y, hy, h1, h2⟩ := exists_latticeCompletion_cut_to_places_finiteReal S L P hz
  exact ⟨y, hy, fun i => mem_idAt_of_fin P (h1 i) (h2 i), h2⟩

theorem mem_latV_iff (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D) (hy : ∀ i, y i ∈ idAt D P) :
    y ∈ latV S L P ↔ (finPart D ∘ y) ∈ latHat D.host.F D.host.E (L : Set (Fin S.rank → D.host.E)) := by
  refine ⟨fun h => GlobalTheory.KStabBridge.fin_mem_latHat S L P h, fun h => ?_⟩
  obtain ⟨y', hy', h1, h2⟩ := exists_lift_latV S L P h
  have : y' = y := funext fun i => GlobalTheory.VacStabFixed.parts_ext
    (by rw [((mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D P _).1 (h1 i)).1, ((mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D P _).1 (hy i)).1])
    (by rw [h2]; exact e_mul_fin (hy i))
  rwa [← this]

theorem supp_mulVec (S : HSp D) (P : Pl D → Prop) (g : GA D S) {y : Fin S.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D P) : ∀ i, (Formalism.L2.Theta.mt S g *ᵥ y) i ∈ idAt D P := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem fin_mulVec (S : HSp D) (g : GA D S) (y : Fin S.rank → AE D) :
    finPart D ∘ (Formalism.L2.Theta.mt S g *ᵥ y) = (finMat D.sp.cm.sig S.gram g) *ᵥ (finPart D ∘ y) := by
  funext i
  exact RingHom.map_mulVec (finPart D) _ y i

theorem moves_of_levelOpen (S : HSp D) (L : Lat S) (hL : L.FG) (P : Pl D → Prop) {g : GA D S}
    (hg : g ∈ GlobalTheory.AdelicU.levelOpen D.sp.cm.sig S.gram L) : Moves S g L L P := by
  intro y hy
  rw [mem_latV_iff S L P y hy, mem_latV_iff S L P _ (supp_mulVec S P g hy), fin_mulVec]
  exact (GlobalTheory.AdelicU.mem_levelOpen_iff_latHat _ _ hL g).1 hg _

theorem keeps_of_core {R : Type} [CommRing R] {n : ℕ} (H : AddSubgroup (Fin n → R)) (e : R) (hee : e * e = e)
    (h1 : ∀ z ∈ H, e • z ∈ H) (h2 : ∀ z ∈ H, (1 - e) • z ∈ H) (M : Matrix (Fin n) (Fin n) R)
    (hN : ∀ i j, e * (M - 1) i j = (M - 1) i j)
    (hcore : ∀ z, e • z ∈ H ↔ M *ᵥ (e • z) ∈ H) (y : Fin n → R) : y ∈ H ↔ M *ᵥ y ∈ H := by
  have hsplit : ∀ z, z ∈ H ↔ e • z ∈ H ∧ (1 - e) • z ∈ H := fun z =>
    ⟨fun hz => ⟨h1 z hz, h2 z hz⟩, fun ⟨a, b⟩ => by
      have := add_mem a b
      rwa [← add_smul, add_sub_cancel, one_smul] at this⟩
  have hN' : (1 - e) • M = (1 - e) • (1 : Matrix (Fin n) (Fin n) R) := by
    ext i j
    have := hN i j
    rw [Matrix.sub_apply] at this
    simp only [Matrix.smul_apply, smul_eq_mul]
    linear_combination (-1 : R) * this
  have hoff : (1 - e) • (M *ᵥ y) = (1 - e) • y := by
    rw [← Matrix.smul_mulVec, hN', Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hsplit y, hsplit (M *ᵥ y), hoff, hcore, Matrix.mulVec_smul]

theorem fin_sub_one (S : HSp D) (g : GA D S) (i j : Fin S.rank) :
    finPart D ((Formalism.L2.Theta.mt S g - 1) i j) = (finMat D.sp.cm.sig S.gram g - 1) i j := by
  rw [Matrix.sub_apply, Matrix.sub_apply, (finPart D).map_sub]
  congr 1
  exact congrFun (congrFun (Matrix.map_one _ (map_zero (finPart D)) (map_one (finPart D))) i) j

theorem levelOpen_of_inK (S : HSp D) (L : Lat S) (hL : L.FG) (P : Pl D → Prop) {g : GA D S}
    (hg : InK S L P g) : g ∈ GlobalTheory.AdelicU.levelOpen D.sp.cm.sig S.gram L := by
  refine (GlobalTheory.AdelicU.mem_levelOpen_iff_latHat _ _ hL g).2 ?_
  have hI := (SetCut.mem_congGrp_iff S _ g).1 hg.1
  refine keeps_of_core (latHat D.host.F D.host.E (L : Set (Fin S.rank → D.host.E)))
    (indP D P ⊗ₜ[D.host.F] (1 : D.host.E))
    (e_mul_of_supp P _ fun w hw => by rw [compFin_e, if_neg hw])
    (fun z hz => GlobalTheory.KStabBridge.latHat_smul _ (indicatorAdele_integral P) hz) (fun z hz => ?_) _ (fun i j => ?_) (fun z => ?_)
  · have := GlobalTheory.KStabBridge.latHat_smul _ (one_sub_indP_int P) hz
    rwa [TensorProduct.sub_tmul, ← Algebra.TensorProduct.one_def] at this
  · rw [← fin_sub_one]; exact e_mul_fin (hI i j)
  · choose lift hl1 hl2 using GlobalTheory.KStabBridge.exists_fin_lift (D := D)
    let y : Fin S.rank → AE D := fun i => lift ((indP D P ⊗ₜ[D.host.F] (1 : D.host.E)) * z i)
    have hy : ∀ i, y i ∈ idAt D P := fun i => mem_idAt_of_fin P (hl1 _) (hl2 _)
    have hfy : finPart D ∘ y = (indP D P ⊗ₜ[D.host.F] (1 : D.host.E)) • z := funext fun i => hl2 _
    have h := hg.2 y hy
    rw [mem_latV_iff S L P y hy, mem_latV_iff S L P _ (supp_mulVec S P g hy), fin_mulVec, hfy] at h
    exact h

theorem compAt_eq (v : Pl D) (a : AE D) : compAt D v a = GlobalTheory.AdelicU.compFin D.host.F D.host.E v a := by
  induction a using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul x c => rfl
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, hx, hy]

theorem map_eq_one_iff {R R' : Type} [CommRing R] [CommRing R'] {n : ℕ} (f : R →+* R') (M : Matrix (Fin n) (Fin n) R) :
    M.map f = 1 ↔ ∀ i j, f ((M - 1) i j) = 0 := by
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.map_apply]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem mem_GfC_iff (S : HSp D) (g : GA D S) : g ∈ GfC S ↔ ∀ i j, infPart D ((Formalism.L2.Theta.mt S g - 1) i j) = 0 := by
  rw [← map_eq_one_iff]
  exact Units.ext_iff

theorem proj_eq_one_iff (S : HSp D) (v : Pl D) (g : GA D S) :
    GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram v g = 1 ↔ ∀ i j, compAt D v ((Formalism.L2.Theta.mt S g - 1) i j) = 0 := by
  simp only [compAt_eq]
  rw [← map_eq_one_iff]
  exact Subtype.ext_iff.trans Units.ext_iff

theorem mem_grpAt_iff (S : HSp D) (P : Pl D → Prop) (g : GA D S) :
    g ∈ grpAt S P ↔ g ∈ GfC S ∧ ∀ v, ¬ P v → GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram v g = 1 := by
  rw [grpAt, SetCut.mem_congGrp_iff, mem_GfC_iff]
  simp only [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere, proj_eq_one_iff]
  exact ⟨fun h => ⟨fun i j => (h i j).1, fun v hv i j => (h i j).2 v hv⟩, fun h i j => ⟨h.1 i j, fun v hv => h.2 v hv i j⟩⟩

theorem isClosed_grpAt (S : HSp D) (P : Pl D → Prop) : IsClosed (grpAt S P : Set (GA D S)) := by
  have e : (grpAt S P : Set (GA D S)) = (GlobalTheory.AdelicU.finPts D.sp.cm.sig S.gram : Set (GA D S)) ∩
      ⋂ v : {v : Pl D // ¬ P v}, (GlobalTheory.AdelicU.awayPts D.sp.cm.sig S.gram {v.1} : Set (GA D S)) := by
    ext g
    rw [SetLike.mem_coe, mem_grpAt_iff, Set.mem_inter_iff, Set.mem_iInter]
    refine and_congr Iff.rfl ⟨fun h v => GlobalTheory.AdelicU.mem_awayPts.2 fun u hu => ?_,
      fun h v hv => GlobalTheory.AdelicU.mem_awayPts.1 (h ⟨v, hv⟩) v (Finset.mem_singleton_self v)⟩
    rw [Finset.mem_singleton.1 hu]; exact h v.1 v.2
  rw [e]
  exact (GlobalTheory.AdelicU.isClosed_finPts _ _).inter (isClosed_iInter fun v => GlobalTheory.AdelicU.isClosed_awayPts _ _ _)

theorem exists_compact_open : ∀ (D : D7) (V : HSp D) (L : Lat V), IsSelfDualC V L → ∀ P : Pl D → Prop, ∃ K : Subgroup (GA D V), (∀ g, g ∈ K ↔ InK V L P g) ∧ IsCompact (K : Set (GA D V)) ∧ IsOpen ((K.subgroupOf (grpAt V P) : Subgroup _) : Set (grpAt V P)) := by
  intro D V L hL P
  haveI : Submodule.IsLattice D.host.E L := hL.1
  have hfg : L.FG := Submodule.IsLattice.fg (A := D.host.E)
  let U : Subgroup (GA D V) := GlobalTheory.AdelicU.levelOpen D.sp.cm.sig V.gram L
  have hU : IsOpen (U : Set (GA D V)) := GlobalTheory.AdelicU.isOpen_levelOpen D.sp.cm.sig V.gram L
  refine ⟨grpAt V P ⊓ U, fun g => ⟨fun h => ⟨h.1, moves_of_levelOpen V L hfg P h.2⟩,
    fun h => ⟨h.1, levelOpen_of_inK V L hfg P h⟩⟩, ?_, ?_⟩
  · refine (GlobalTheory.AdelicU.isCompact_levelFin D.sp.cm.sig V.gram L).of_isClosed_subset
      ((isClosed_grpAt V P).inter (U.isClosed_of_isOpen hU)) fun k hk => ?_
    exact GlobalTheory.AdelicU.mem_levelFin.2 ⟨((mem_grpAt_iff V P k).1 hk.1).1, GlobalTheory.AdelicU.mem_levelOpen.1 hk.2⟩
  · have e : (((grpAt V P ⊓ U).subgroupOf (grpAt V P) : Subgroup _) : Set (grpAt V P)) =
        Subtype.val ⁻¹' (U : Set (GA D V)) := by
      ext x
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [e]
    exact hU.preimage continuous_subtype_val

end GlobalTheory.FinPl.KOpen

end
