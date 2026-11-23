import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ArchCone
import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.FubGen

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKG.Fub

theorem ae_ring : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
theorem ae_smul : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) _
theorem ae_top : T2Space (AE F E) ∧ LocallyCompactSpace (AE F E) ∧ SecondCountableTopology (AE F E) := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  exact ⟨e.isEmbedding.t2Space, e.isClosedEmbedding.locallyCompactSpace, e.secondCountableTopology⟩
theorem ae_t2 : T2Space (AE F E) := ae_top.1
theorem ae_lc : LocallyCompactSpace (AE F E) := ae_top.2.1
theorem ae_sc : SecondCountableTopology (AE F E) := ae_top.2.2

attribute [local instance] ae_ring ae_smul ae_t2 ae_lc ae_sc

theorem units_top {A : Type} [Ring A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] [LocallyCompactSpace A]
    [SecondCountableTopology A] : LocallyCompactSpace Aˣ ∧ SecondCountableTopology Aˣ := by
  haveI : SecondCountableTopology Aᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : LocallyCompactSpace Aᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact ⟨Units.isClosedEmbedding_embedProduct.locallyCompactSpace, Units.isEmbedding_embedProduct.secondCountableTopology⟩

theorem ua_top {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : LocallyCompactSpace (UA σ J) ∧ SecondCountableTopology (UA σ J) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E)) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  obtain ⟨h1, h2⟩ := units_top (A := Matrix (Fin n) (Fin n) (AE F E))
  have hc : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have : IsClosed ((UG (cA σ) (incM F J) : Subgroup (GL (Fin n) (AE F E))) : Set (GL (Fin n) (AE F E))) :=
    isClosed_eq (((Units.continuous_val.matrix_transpose).matrix_mul continuous_const).matrix_mul
      (Units.continuous_val.matrix_map hc)) continuous_const
  exact ⟨this.locallyCompactSpace, TopologicalSpace.Subtype.secondCountableTopology _⟩

theorem af_ext_k {a b : AF F} (h1 : a.1 = b.1) (h2 : ∀ v, evFin F v a = evFin F v b) : a = b :=
  Prod.ext h1 (FiniteAdeleRing.ext _ h2)

theorem evFin_idem_self_k (v : Pl F) : evFin F v (idem F v) = 1 := evalV_singleFin_self v 1
theorem evFin_idem_ne_k {v u : Pl F} (h : u ≠ v) : evFin F u (idem F v) = 0 := evalV_singleFin_ne h 1
theorem real_fst : (realAd F 1).1 = 1 := by
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ (1 : ℝ)) = 1
  rw [map_one, map_one]
theorem evFin_real_k (v : Pl F) : evFin F v (realAd F 1) = 0 := map_zero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)

theorem mul_idem_zero {v : Pl F} {u : AF F} (h : evFin F v u = 0) : u * idem F v = 0 :=
  af_ext_k (mul_zero u.1) fun w => by
    rw [map_mul, map_zero]
    by_cases e : w = v
    · subst e; rw [h, zero_mul]
    · rw [evFin_idem_ne_k e, mul_zero]

theorem mul_real_zero {u : AF F} (h : u.1 = 0) : u * realAd F 1 = 0 :=
  af_ext_k (show u.1 * (realAd F 1).1 = 0 by rw [h, zero_mul]) fun w => by rw [map_mul, evFin_real_k, mul_zero, map_zero]

theorem idem_idem (v : Pl F) : idem F v * idem F v = idem F v := by
  have := mul_idem_zero (v := v) (u := 1 - idem F v) (by rw [map_sub, map_one, evFin_idem_self_k, sub_self])
  linear_combination -this

theorem real_idem : realAd F 1 * realAd F 1 = realAd F 1 := by
  have := mul_real_zero (u := 1 - realAd F 1) (show (1 : Ainf F) - (realAd F 1).1 = 0 by rw [real_fst, sub_self])
  linear_combination -this

theorem idem_orth {v u : Pl F} (h : v ≠ u) : idem F v * idem F u = 0 := mul_idem_zero (evFin_idem_ne_k h.symm)
theorem idem_real (v : Pl F) : idem F v * realAd F 1 = 0 := mul_real_zero rfl

theorem at_fin_iff {M : Type} [AddCommGroup M] [Module (AF F) M] {v : Pl F} {z : M} : At (evFin F v) z ↔ idem F v • z = z := by
  refine ⟨fun h => ?_, fun h u hu => by rw [← h, smul_smul, mul_idem_zero hu, zero_smul]⟩
  have := h (1 - idem F v) (by rw [map_sub, map_one, evFin_idem_self_k, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at this
  exact this.symm

theorem evI_zero_k {u : AF F} : evI F u = 0 ↔ u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff

theorem at_inf_iff {M : Type} [AddCommGroup M] [Module (AF F) M] {z : M} : At (evI F) z ↔ realAd F 1 • z = z := by
  refine ⟨fun h => ?_, fun h u hu => by rw [← h, smul_smul, mul_real_zero (evI_zero_k.1 hu), zero_smul]⟩
  have := h (1 - realAd F 1) (evI_zero_k.2 (show (1 : Ainf F) - (realAd F 1).1 = 0 by rw [real_fst, sub_self]))
  rw [sub_smul, one_smul, sub_eq_zero] at this
  exact this.symm

theorem fix_iff {R A : Type} [CommRing R] [Ring A] [Algebra R A] (a : R) (x : A) :
    a • (x - 1) = x - 1 ↔ a • x + (1 - a) • (1 : A) = x := by
  rw [smul_sub, sub_smul, one_smul]
  constructor <;> intro h
  · rw [sub_eq_iff_eq_add] at h; rw [h]; abel
  · conv_rhs => rw [← h]
    abel

def rest (T : Finset (Pl F)) : AF F := 1 - realAd F 1 - ∑ v ∈ T, idem F v

theorem rest_fst (T : Finset (Pl F)) : (rest T).1 = 0 := by
  have : ∀ a : AF F, a.1 = fstA F a := fun _ => rfl
  rw [this, rest, map_sub, map_sub, map_one, map_sum, ← this, real_fst, sub_self, zero_sub, neg_eq_zero]
  exact Finset.sum_eq_zero fun v _ => rfl

open Classical in
theorem evFin_rest (T : Finset (Pl F)) (v : Pl F) : evFin F v (rest T) = if v ∈ T then 0 else 1 := by
  rw [rest, map_sub, map_sub, map_one, map_sum, evFin_real_k, sub_zero]
  split_ifs with h
  · rw [Finset.sum_eq_single_of_mem v h fun u _ hu => evFin_idem_ne_k hu.symm, evFin_idem_self_k, sub_self]
  · rw [Finset.sum_eq_zero fun u hu => evFin_idem_ne_k (fun e : v = u => h (by rw [e]; exact hu)), sub_zero]

theorem rest_idem (T : Finset (Pl F)) : rest T * rest T = rest T :=
  af_ext_k (show (rest T).1 * (rest T).1 = (rest T).1 by rw [rest_fst, mul_zero]) fun v => by
    rw [map_mul, evFin_rest]; split_ifs <;> simp

theorem idem_rest {T : Finset (Pl F)} {v : Pl F} (h : v ∈ T) : idem F v * rest T = 0 := by
  rw [mul_comm]; exact mul_idem_zero (by rw [evFin_rest, if_pos h])

theorem real_rest (T : Finset (Pl F)) : realAd F 1 * rest T = 0 := by rw [mul_comm]; exact mul_real_zero (rest_fst T)

theorem sum_rest (T : Finset (Pl F)) : rest (∅ : Finset (Pl F)) = ∑ v ∈ T, idem F v + rest T := by
  simp [rest]

theorem real_add_rest : realAd F 1 + rest (∅ : Finset (Pl F)) = 1 := by simp [rest]

variable {n : ℕ}

variable (σ) in

def PU (J : Matrix (Fin n) (Fin n) E) (a : AF F) : UA σ J →* UA σ J :=
  ((unitP (A := Matrix (Fin n) (Fin n) (AE F E)) a).comp (Subgroup.subtype _)).codRestrict _ fun g => by
    by_cases h : a * a = a
    · show (unitP a g.1 : Matrix _ _ _)ᵀ * incM F J * (unitP a g.1 : Matrix _ _ _).map (cA σ) = incM F J
      have hg : (g.1 : Matrix _ _ _)ᵀ * incM F J * (g.1 : Matrix _ _ _).map (cA σ) = incM F J := g.2
      have e : (a • (g.1 : Matrix (Fin n) (Fin n) (AE F E)) + (1 - a) • (1 : Matrix (Fin n) (Fin n) (AE F E))).map (cA σ) =
          a • (g.1 : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) + (1 - a) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
        ext i j
        simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add, map_smul, Matrix.one_apply]
        split_ifs <;> simp
      have h1 : a * (1 - a) = 0 := by linear_combination -h
      have h2 : (1 - a) * a = 0 := by linear_combination -h
      have h3 : (1 - a) * (1 - a) = 1 - a := by linear_combination h
      rw [coe_unitP h, e]
      simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, Matrix.add_mul, Matrix.mul_add,
        Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, h, h1, h2, h3, zero_smul, Matrix.one_mul, Matrix.mul_one, hg,
        add_zero, zero_add]
      rw [← add_smul]; simp
    · unfold unitP; rw [dif_neg h]; exact Subgroup.one_mem _

theorem mat_PU {J : Matrix (Fin n) (Fin n) E} {a : AF F} (h : a * a = a) (g : UA σ J) :
    mat (PU σ J a g) = a • mat g + (1 - a) • (1 : Matrix _ _ (AE F E)) := coe_unitP h g.1

def Gd (a : AF F) : Prop := a * a = a ∧ (a.1 = 0 ∨ a.1 = 1)

theorem piInf_alg {w : InfinitePlace F} (τ : EmbOver E w) {a b : AF F} (h : a.1 = b.1) (x : AE F E) :
    piInf τ (a • x) = piInf τ (b • x) := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul]
  congr 1
  show infEmb τ (GlobalTheory.AutFunCompare.evW w a.1 ⊗ₜ[F] (1 : E)) = infEmb τ (GlobalTheory.AutFunCompare.evW w b.1 ⊗ₜ[F] (1 : E))
  rw [h]

theorem smul_latHat (X : Spc F E n) {a : AF F} (h : a * a = a) {z} (hz : z ∈ latHat X) : a • z ∈ latHat X := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, hv, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a * b, evI_zero_k.2 (show a.1 * b.1 = 0 by rw [evI_zero_k.1 hb, mul_zero]), fun v => ?_, x, hx,
      smul_smul _ _ _⟩
    rw [map_mul]
    refine mul_mem ?_ (hv v)
    have : IsIdempotentElem (evFin F v a) := by show _ * _ = _; rw [← map_mul, h]
    rcases IsIdempotentElem.iff_eq_zero_or_one.1 this with e | e <;> rw [e]
    exacts [zero_mem _, one_mem _]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem PU_mem {B : Base F E} {X : Spc F E n} {K : Subgroup (UA σ X.J)} (hK : IsStab B K) {a : AF F} (ha : Gd a) {g} (hg : g ∈ K) :
    PU σ X.J a g ∈ K := by
  obtain ⟨h1, h2⟩ := (hK g).1 hg
  have ha' : (1 - a) * (1 - a) = 1 - a := by linear_combination ha.1
  have key : ∀ g : UA σ X.J, ∀ z ∈ latHat X, mat g *ᵥ z ∈ latHat X → mat (PU σ X.J a g) *ᵥ z ∈ latHat X := fun g z hz h => by
    rw [mat_PU ha.1, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact add_mem (smul_latHat X ha.1 h) (smul_latHat X ha' hz)
  refine (hK _).2 ⟨fun w => ?_, fun z hz => ⟨key g z hz (h2 z hz).1, by rw [← map_inv]; exact key _ z hz (h2 z hz).2⟩⟩
  rcases ha.2 with e | e
  · have : (mat (PU σ X.J a g)).map (piInf (B.emb w)) = 1 := by
      rw [mat_PU ha.1, ← Matrix.map_one (piInf (B.emb w)) (map_zero _) (map_one _)]
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add]
      rw [piInf_alg _ (b := 0) e, piInf_alg _ (a := 1 - a) (b := 1) (show (1 : Ainf F) - a.1 = 1 by rw [e, sub_zero])]
      simp
    rw [this]; exact Commute.one_left _
  · have : (mat (PU σ X.J a g)).map (piInf (B.emb w)) = (mat g).map (piInf (B.emb w)) := by
      rw [mat_PU ha.1]
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add]
      rw [piInf_alg _ (b := 1) e, piInf_alg _ (a := 1 - a) (b := 0) (show (1 : Ainf F) - a.1 = 0 by rw [e, sub_self])]
      simp
    rw [this]; exact h1 w

theorem Gd.add {a b : AF F} (ha : Gd a) (hb : Gd b) (h : a * b = 0) : Gd (a + b) := by
  refine ⟨idem_add ha.1 hb.1 h, ?_⟩
  have h' : a.1 * b.1 = 0 := congrArg Prod.fst h
  show a.1 + b.1 = 0 ∨ a.1 + b.1 = 1
  rcases ha.2 with e | e
  · rw [e, zero_add]; exact hb.2
  · rw [e, one_mul] at h'; rw [e, h', add_zero]; exact Or.inr rfl

theorem gd_idem (v : Pl F) : Gd (idem F v) := ⟨idem_idem v, Or.inl rfl⟩
theorem gd_real : Gd (realAd F 1) := ⟨real_idem, Or.inr real_fst⟩
theorem gd_rest (T : Finset (Pl F)) : Gd (rest T) := ⟨rest_idem T, Or.inl (rest_fst T)⟩

theorem borelUA (J : Matrix (Fin n) (Fin n) E) : BorelSpace (UA σ J) := ⟨rfl⟩

theorem sysU {B : Base F E} {X : Spc F E n} {K : Subgroup (UA σ X.J)} (hK : IsStab B K) (hc : IsCompact (K : Set (UA σ X.J))) :
    Sys (PU σ X.J) K Set.univ Gd where
  cont a ha := ((unitInvariant_continuous ha.1).comp continuous_subtype_val).subtype_mk _
  comp a b ha hb g := Subtype.ext (unitInvariant_comp ha.1 hb.1 g.1)
  zero g := Subtype.ext (unitInvariant_zero g.1)
  add a b ha hb h := ⟨ha.add hb h, fun g => Subtype.ext (unitInvariant_add ha.1 hb.1 h g.1)⟩
  idem a ha := ha.1
  cK := hc.isClosed
  mK a ha g hg := PU_mem hK ha hg
  mU := MeasurableSet.univ
  one := trivial
  mul _ _ _ _ := trivial
  pU _ _ _ _ := trivial

theorem kAt_eq {X : Spc F E n} (K : Subgroup (UA σ X.J)) {R : Type} [Zero R] (ev : AF F → R) {a : AF F} (h : a * a = a)
    (hat : ∀ z : Matrix (Fin n) (Fin n) (AE F E), At ev z ↔ a • z = z) : kAt K ev = part (PU σ X.J) K a := by
  have : UAt σ X ev = ((PU σ X.J a).eqLocus (MonoidHom.id _) : Set _) := Set.ext fun g => by
    show At ev (mat g - 1) ↔ PU σ X.J a g = g
    rw [hat, fix_iff, ← mat_PU h]
    exact ⟨fun e => Subtype.ext (Units.ext e), fun e => congrArg mat e⟩
  rw [kAt, this, Subgroup.closure_eq, part]

theorem co_U {B : Base F E} {X : Spc F E n} {K : Subgroup (UA σ X.J)} (hK : IsStab B K) (hc : IsCompact (K : Set (UA σ X.J)))
    {a : AF F} (ha : Gd a) : CO (PU σ X.J) K Set.univ a := by
  haveI := (ua_top (σ := σ) X.J).1
  haveI := (ua_top (σ := σ) X.J).2
  haveI := borelUA (σ := σ) X.J
  haveI : CompactSpace (part (PU σ X.J) K a) :=
    isCompact_iff_compactSpace.1 (hc.of_isClosed_subset ((sysU hK hc).closed ha) fun _ h => h.1)
  exact ⟨isCompact_univ, isOpen_univ⟩

theorem stab_compact (hS : StabEx) {B : Base F E} {X : Spc F E n} {r s : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s)
    {K : Subgroup (UA σ X.J)} (hK : IsStab B K) : IsCompact (K : Set (UA σ X.J)) := by
  obtain ⟨K', -, -, h1, h2, -⟩ := hS F E σ B n X r s hB hX
  have : K = K' := Subgroup.ext fun g => (hK g).trans (h1 g).symm
  exact this ▸ h2

def ext0 {G : Type} [Group G] (S : Subgroup G) (f : S → ℂ) : G → ℂ := Function.extend Subtype.val f 0

theorem extendByZeroOnSubset_apply_coe {G : Type} [Group G] {S : Subgroup G} (f : S → ℂ) (x : S) : ext0 S f x = f x :=
  Subtype.val_injective.extend_apply _ _ _

theorem extendByZero_restrict_alt {G : Type} [Group G] {S : Subgroup G} (f : S → ℂ) : (fun x : S => ext0 S f x) = f := funext (extendByZeroOnSubset_apply_coe f)

theorem kFub_of (hS : StabEx) : KFub := by
  classical
  intro F E _ _ _ _ _ σ B n X r s hB hX K m μK hK hm hμ
  haveI := (ua_top (σ := σ) X.J).1
  haveI := (ua_top (σ := σ) X.J).2
  haveI := borelUA (σ := σ) X.J
  have hc := stab_compact hS hB hX hK
  have sy := sysU hK hc
  have ei := kAt_eq K (evI F) real_idem fun _ => at_inf_iff
  have ef := fun v => kAt_eq K (evFin F v) (idem_idem v) fun _ => at_fin_iff
  have e1 : K = part (PU σ X.J) K (realAd F 1 + rest ∅) := by
    rw [real_add_rest]; exact Subgroup.ext fun g => ⟨fun h => ⟨h, Subtype.ext (unitInvariant_one g.1)⟩, fun h => h.1⟩
  have sp := sy.split gd_real (gd_rest ∅) (real_rest ∅)
  obtain ⟨μ', m1, -, m3⟩ := transport e1 _ BorelSpace.measurable_eq μK
  obtain ⟨α, a1, -, a3⟩ := transport ei _ BorelSpace.measurable_eq m.ki
  choose γ g1 g2 g3 using fun v => transport (ef v) _ BorelSpace.measurable_eq (m.kf v)
  have hex := fun T => exists_haar _ (sy.closed (gd_rest T)) Set.univ trivial (co_U hK hc (gd_rest T)).1 (co_U hK hc (gd_rest T)).2
  choose β hβ using hex
  haveI := m1 hμ; haveI := a1 hm.ki; haveI := (hβ ∅).1
  obtain ⟨c, c0, c1, -⟩ := sp.fub μ' α (β ∅)
  refine ⟨fun k => ⟨PU σ X.J _ k, ei ▸ sp.mA _ (e1 ▸ k.2)⟩, fun v k => ⟨PU σ X.J (idem F v) k, (ef v) ▸
    ⟨sy.mK _ (gd_idem v) _ k.2, by show PU σ X.J _ (PU σ X.J _ _) = _; rw [sy.comp _ _ (gd_idem v) (gd_idem v), idem_idem]; rfl⟩⟩,
    c, by exact_mod_cast c0, fun k => ⟨mat_PU real_idem _, fun v => mat_PU (idem_idem v) _⟩, fun T hi h i1 i2 => ?_⟩
  have hu : β T Set.univ = 1 := (hβ T).2
  haveI : IsFiniteMeasure (β T) := ⟨hu.trans_lt ENNReal.one_lt_top⟩
  obtain ⟨p1, p2⟩ := sy.prod (idem F) gd_idem (fun _ _ => idem_orth) (rest T) (gd_rest T) γ
    (fun v => ⟨g1 v (hm.kf v).1, (g2 v Set.univ).trans (hm.kf v).2⟩) (β T) (hβ T) T (fun v => idem_rest)
    (fun T' h => co_U hK hc (sy.good_sum _ gd_idem (fun _ _ => idem_orth) _ (gd_rest T) T' fun v hv => idem_rest (h hv)))
    _ (sum_rest T) (β ∅) (hβ ∅) (fun v => ext0 _ (h v)) (fun _ => 1)
    (fun v hv => (g3 v _).1.2 (by rw [extendByZero_restrict_alt]; exact i2 v hv)) (integrable_const _)
  obtain ⟨q1, q2⟩ := c1 (ext0 _ hi) (fun y => (∏ v ∈ T, ext0 _ (h v) (PU σ X.J (idem F v) y)) * 1) ((a3 _).1.2 (by rw [extendByZero_restrict_alt]; exact i1)) p1
  have hb : ∫ _ : part (PU σ X.J) K (rest T), (1 : ℂ) ∂(β T) = 1 := by
    rw [integral_const, Measure.real, hu]; simp
  rw [p2, hb, (a3 _).2, extendByZero_restrict_alt] at q2
  simp only [fun v => (g3 v (ext0 _ (h v))).2, extendByZero_restrict_alt] at q2
  have hr : ∀ v, idem F v * rest ∅ = idem F v := fun v => by
    rw [rest, Finset.sum_empty, sub_zero, mul_sub, idem_real, mul_one, sub_zero]
  have := m3 fun x => ext0 _ hi (PU σ X.J (realAd F 1) x) *
    ((∏ v ∈ T, ext0 _ (h v) (PU σ X.J (idem F v) (PU σ X.J (rest ∅) x))) * 1)
  rw [this.1] at q1
  rw [this.2] at q2
  simp only [fun v x => sy.comp _ _ (gd_idem v) (gd_rest ∅) x, hr, mul_one] at q1 q2
  simp only [← extendByZeroOnSubset_apply_coe hi, ← fun v => extendByZeroOnSubset_apply_coe (h v)]
  refine ⟨q1, q2.trans ?_⟩
  simp only [extendByZeroOnSubset_apply_coe]; ring

end PositivityTheory.ThKG.Loc.Cone

end
