import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocFieldLP
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamePartRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalingOpenSubgroupsFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateOpenSubgroupsFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatPartitionOfUnity
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.LiftPair
open scoped Matrix TensorProduct Topology

noncomputable section

namespace GlobalTheory.PureAtPlace

variable {F : Type} [Field F] [NumberField F] (v : Pl F) {κ : Type}

theorem lc_Fv : LocallyCompactSpace (Fv F v) := by
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hC : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
  exact IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup hC (x := 0) (hO.mem_nhds (zero_mem _))

theorem exists_compact_clopen {H : Type} [TopologicalSpace H] [LocallyCompactSpace H] [T2Space H]
    [TotallyDisconnectedSpace H] {x : H} {U : Set H} (hU : U ∈ 𝓝 x) :
    ∃ B, IsClopen B ∧ IsCompact B ∧ x ∈ B ∧ B ⊆ U := by
  obtain ⟨K, hK, hKU, hKc⟩ := local_compact_nhds hU
  obtain ⟨B, hB, hxB, hBK⟩ := loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 hK
  exact ⟨B, hB, hKc.of_isClosed_subset hB.isClosed hBK, hxB, hBK.trans hKU⟩

def evT (y : κ → Af F) : κ → Fv F v := fun i => evalV F v (y i)

def sgT (a : κ → Fv F v) : κ → Af F := fun i => singleFin v (a i)

def prT (y : κ → Af F) : κ → Af F := y - sgT v (evT v y)

theorem evT_add (y y' : κ → Af F) : evT v (y + y') = evT v y + evT v y' := funext fun i => map_add _ _ _

theorem sgT_add (a b : κ → Fv F v) : sgT v (a + b) = sgT v a + sgT v b := funext fun i => map_add _ _ _

theorem sgT_zero : sgT v (0 : κ → Fv F v) = 0 := funext fun i => map_zero _

theorem evT_prT (y : κ → Af F) : evT v (prT v y) = 0 := by
  rw [prT, show y - sgT v (evT v y) = y + (-sgT v (evT v y)) from sub_eq_add_neg _ _]
  funext i
  simp [evT, sgT, evalV_singleFin_self]

theorem prT_prT (y : κ → Af F) : prT v (prT v y) = prT v y := by
  conv_lhs => rw [prT]
  rw [evT_prT, sgT_zero, sub_zero]

theorem sgT_add_prT (y : κ → Af F) : sgT v (evT v y) + prT v y = y := by
  rw [prT]; abel

theorem prT_add (y y' : κ → Af F) : prT v (y + y') = prT v y + prT v y' := by
  simp only [prT, evT_add, sgT_add]; abel

theorem continuous_evT : Continuous (evT v : (κ → Af F) → κ → Fv F v) :=
  continuous_pi fun i => (GlobalTheory.BoxCosetSum.continuous_evalV' v).comp (continuous_apply i)

theorem continuous_sgT : Continuous (sgT v : (κ → Fv F v) → κ → Af F) :=
  continuous_pi fun i => (continuous_singleFin v).comp (continuous_apply i)

theorem continuous_prT : Continuous (prT v : (κ → Af F) → κ → Af F) :=
  continuous_id.sub ((continuous_sgT v).comp (continuous_evT v))

attribute [local instance] GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField

theorem mem_SB_prod {a : (κ → Fv F v) → ℂ} {b : (κ → Af F) → ℂ} (ha : a ∈ SB (κ → Fv F v)) (hb : b ∈ SB (κ → Af F)) :
    (fun y => a (evT v y) * b (prT v y)) ∈ SB (κ → Af F) := by
  refine ⟨(ha.1.comp_continuous (continuous_evT v)).mul (hb.1.comp_continuous (continuous_prT v)), ?_⟩
  have hK : IsCompact ((fun p : (κ → Fv F v) × (κ → Af F) => sgT v p.1 + p.2) '' (tsupport a ×ˢ tsupport b)) :=
    (IsCompact.prod ha.2 hb.2).image (((continuous_sgT v).comp continuous_fst).add continuous_snd)
  refine HasCompactSupport.intro' hK hK.isClosed fun y hy => ?_
  by_contra h
  apply hy
  have h' := mul_ne_zero_iff.1 h
  exact ⟨(evT v y, prT v y), ⟨subset_tsupport _ h'.1, subset_tsupport _ h'.2⟩, sgT_add_prT v y⟩

variable (κ) in

def Sp : Submodule ℂ ((κ → Af F) → ℂ) :=
  Submodule.span ℂ {s | ∃ a b, a ∈ SB (κ → Fv F v) ∧ b ∈ SB (κ → Af F) ∧ s = fun y => a (evT v y) * b (prT v y)}

def Good (W : Set (κ → Af F)) : Prop := ∀ s ∈ Sp v κ, W.indicator s ∈ Sp v κ

theorem good_of_gen {W : Set (κ → Af F)}
    (hW : ∀ a b, a ∈ SB (κ → Fv F v) → b ∈ SB (κ → Af F) →
      W.indicator (fun y => a (evT v y) * b (prT v y)) ∈ Sp v κ) : Good v W := by
  intro s hs
  induction hs using Submodule.span_induction with
  | mem x hx => obtain ⟨a, b, ha, hb, rfl⟩ := hx; exact hW a b ha hb
  | zero => simp
  | add x y _ _ hx hy =>
    have e : W.indicator (x + y) = W.indicator x + W.indicator y := by
      funext z; by_cases hz : z ∈ W <;> simp [hz]
    rw [e]; exact add_mem hx hy
  | smul c x _ hx =>
    have e : W.indicator (c • x) = c • W.indicator x := by
      funext z; by_cases hz : z ∈ W <;> simp [hz]
    rw [e]; exact Submodule.smul_mem _ c hx

theorem good_empty : Good v (∅ : Set (κ → Af F)) := fun s _ => by
  rw [Set.indicator_empty]; exact (Sp v κ).zero_mem

theorem good_compl {W : Set (κ → Af F)} (h : Good v W) : Good v Wᶜ := by
  intro s hs
  have e : Wᶜ.indicator s = s - W.indicator s := by
    funext z; by_cases hz : z ∈ W <;> simp [hz]
  rw [e]; exact sub_mem hs (h s hs)

theorem indicator_union_eq {W₁ W₂ : Set (κ → Af F)} (s : (κ → Af F) → ℂ) :
    (W₁ ∪ W₂).indicator s = W₁.indicator s + W₁ᶜ.indicator (W₂.indicator s) := by
  funext z; by_cases h1 : z ∈ W₁ <;> by_cases h2 : z ∈ W₂ <;> simp [h1, h2]

theorem good_union {W₁ W₂ : Set (κ → Af F)} (h₁ : Good v W₁) (h₂ : Good v W₂) : Good v (W₁ ∪ W₂) := by
  intro s hs
  rw [indicator_union_eq]
  exact add_mem (h₁ s hs) (good_compl v h₁ _ (h₂ s hs))

theorem good_box {B₁ : Set (κ → Fv F v)} {B₂ : Set (κ → Af F)} (h₁ : IsClopen B₁) (h₂ : IsClopen B₂) :
    Good v {y | evT v y ∈ B₁ ∧ prT v y ∈ B₂} := by
  refine good_of_gen v fun a b ha hb => Submodule.subset_span
    ⟨B₁.indicator a, B₂.indicator b, GlobalTheory.CoverSB.indicator_mem_SB h₁ ha, GlobalTheory.CoverSB.indicator_mem_SB h₂ hb, ?_⟩
  funext y
  by_cases e1 : evT v y ∈ B₁ <;> by_cases e2 : prT v y ∈ B₂ <;> simp [Set.indicator, e1, e2]

theorem mem_Sp [Finite κ] {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) : g ∈ Sp v κ := by
  haveI := lc_Fv v
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI := GlobalTheory.TamePartR.totallyDisconnected_finiteAdele F
  haveI := GlobalTheory.TamePartR.td_adic v
  have hcl : IsClosed (Function.support g) := by
    have : Function.support g = (g ⁻¹' {0})ᶜ := by ext; simp
    rw [this]; exact (hg.1.isOpen_fiber 0).isClosed_compl
  have hcpt : IsCompact (Function.support g) := by
    have := hg.2
    rw [HasCompactSupport, tsupport, hcl.closure_eq] at this
    exact this
  let p : Set (κ → Af F) → Prop := fun T => ∃ W, Good v W ∧ T ⊆ W ∧ W.indicator g ∈ Sp v κ
  have hp : p (Function.support g) := by
    refine hcpt.induction_on ?_ ?_ ?_ ?_
    · exact ⟨∅, good_empty v, subset_rfl, by rw [Set.indicator_empty]; exact (Sp v κ).zero_mem⟩
    · rintro s t hst ⟨W, hW, htW, h⟩
      exact ⟨W, hW, hst.trans htW, h⟩
    · rintro s t ⟨W₁, hW₁, hs, h₁⟩ ⟨W₂, hW₂, ht, h₂⟩
      refine ⟨W₁ ∪ W₂, good_union v hW₁ hW₂, Set.union_subset_union hs ht, ?_⟩
      rw [indicator_union_eq]
      exact add_mem h₁ (good_compl v hW₁ _ h₂)
    · intro x _
      let Φ : (κ → Fv F v) × (κ → Af F) → κ → Af F := fun q => sgT v q.1 + prT v q.2
      have hΦc : Continuous Φ :=
        ((continuous_sgT v).comp continuous_fst).add ((continuous_prT v).comp continuous_snd)
      have hΦ : ∀ y, Φ (evT v y, prT v y) = y := fun y => by
        simp only [Φ, prT_prT]; exact sgT_add_prT v y
      have hU : Φ ⁻¹' {y | g y = g x} ∈ 𝓝 (evT v x, prT v x) := by
        refine hΦc.continuousAt.preimage_mem_nhds ?_
        rw [hΦ]; exact (hg.1.isOpen_fiber (g x)).mem_nhds rfl
      obtain ⟨u, hu, t, ht, hut⟩ := mem_nhds_prod_iff.1 hU
      obtain ⟨B₁, hB₁, hB₁c, hx₁, hB₁u⟩ := exists_compact_clopen hu
      obtain ⟨B₂, hB₂, hB₂c, hx₂, hB₂t⟩ := exists_compact_clopen ht
      have hWo : IsOpen {y | evT v y ∈ B₁ ∧ prT v y ∈ B₂} :=
        (hB₁.isOpen.preimage (continuous_evT v)).inter (hB₂.isOpen.preimage (continuous_prT v))
      refine ⟨_, mem_nhdsWithin_of_mem_nhds (hWo.mem_nhds ⟨hx₁, hx₂⟩), _, good_box v hB₁ hB₂, subset_rfl, ?_⟩
      have e : {y | evT v y ∈ B₁ ∧ prT v y ∈ B₂}.indicator g =
          g x • fun y => B₁.indicator (1 : (κ → Fv F v) → ℂ) (evT v y) * B₂.indicator 1 (prT v y) := by
        funext y
        by_cases e1 : evT v y ∈ B₁ <;> by_cases e2 : prT v y ∈ B₂
        · have hy : g y = g x := by
            have := hut (show (evT v y, prT v y) ∈ u ×ˢ t from ⟨hB₁u e1, hB₂t e2⟩)
            rw [Set.mem_preimage, hΦ] at this
            exact this
          simp [Set.indicator, e1, e2, hy]
        all_goals simp [Set.indicator, e1, e2]
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _,
        GlobalTheory.LocalBoxIndicator.indicator_mem_SB hB₁ hB₁c, GlobalTheory.LocalBoxIndicator.indicator_mem_SB hB₂ hB₂c, rfl⟩)
  obtain ⟨W, -, hW, h⟩ := hp
  rwa [Set.indicator_eq_self.2 hW] at h

end GlobalTheory.PureAtPlace

namespace GlobalTheory.PureAtPlace

variable {F : Type} [Field F] [NumberField F] (v : Pl F) {κ : Type}

theorem sub_single_mul (w : Af F) : (1 - singleFin v 1) * w = w - singleFin v (evalV F v w) := by
  refine af_ext fun u => ?_
  by_cases h : u = v
  · subst h; simp [evalV_singleFin_self]
  · simp [evalV_singleFin_ne h]

def restF (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (b : (κ → Af F) → ℂ) : (κ → AF F) → ℂ :=
  pureA F f (fun y => b (prT v y))

theorem tens_restF (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (b : (κ → Af F) → ℂ) (φ : (κ → Fv F v) → ℂ) :
    tens (evFin F v) φ (restF v f b) = pureA F f (fun y => φ (evT v y) * b (prT v y)) := by
  funext x
  simp only [tens, restF, pureA]
  have : (fun i => evFin F v (x i)) = evT v (fun i => (x i).2) := rfl
  rw [this]; ring

theorem restF_add_at (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (b : (κ → Af F) → ℂ) (x z : κ → AF F)
    (hz : At (evFin F v) z) : restF v f b (x + z) = restF v f b x := by
  let u : AF F := ((1 : Ainf F), 1 - singleFin v 1)
  have hu : evFin F v u = 0 := by
    show evalV F v (1 - singleFin v 1) = 0
    rw [map_sub, map_one, evalV_singleFin_self, sub_self]
  have h0 := hz u hu
  have h1 : ∀ i, (z i).1 = 0 := fun i => by
    have e : (u * z i).1 = 0 := congrArg Prod.fst (congrFun h0 i)
    have e' : (u * z i).1 = 1 * (z i).1 := rfl
    rw [e', one_mul] at e; exact e
  have h2 : prT v (fun i => (z i).2) = 0 := by
    funext i
    have e : (u * z i).2 = 0 := congrArg Prod.snd (congrFun h0 i)
    have e' : (u * z i).2 = (1 - singleFin v 1) * (z i).2 := rfl
    rw [e', sub_single_mul] at e
    exact e
  have ea : (fun i => ((x + z) i).1) = fun i => (x i).1 := funext fun i => by
    show (x i).1 + (z i).1 = _; rw [h1, add_zero]
  have eb : (fun i => ((x + z) i).2) = (fun i => (x i).2) + (fun i => (z i).2) := rfl
  simp only [restF, pureA]
  rw [eb, prT_add, h2, add_zero]
  congr 2
  funext i
  rw [show ((x + z) i).1 = (x i).1 from congrFun ea i]

end GlobalTheory.PureAtPlace

namespace GlobalTheory.PureAtPlace

theorem schA_le_span_tens : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ],
    schA F κ ≤ Submodule.span ℂ {Φ | ∃ (φ : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ), φ ∈ SB (κ → Fv F v) ∧
      (∀ φ' ∈ SB (κ → Fv F v), Rest (evFin F v) φ' r) ∧ Φ = tens (evFin F v) φ r} := by
  intro F _ _ v κ _
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, g, hg, rfl⟩
  have hgS := mem_Sp v hg
  clear hg
  induction hgS using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨a, b, ha, hb, rfl⟩ := hs
    refine Submodule.subset_span ⟨a, restF v f b, ha, fun φ' hφ' => ⟨fun x z hz => restF_add_at v f b x z hz, ?_⟩,
      (tens_restF v f b a).symm⟩
    rw [tens_restF]
    exact Submodule.subset_span ⟨f, _, mem_SB_prod v hφ' hb, rfl⟩
  | zero =>
    have e : pureA F f 0 = 0 := by funext x; simp [pureA]
    rw [e]; exact zero_mem _
  | add x y _ _ hx hy =>
    have e : pureA F f (x + y) = pureA F f x + pureA F f y := by funext z; simp [pureA, mul_add]
    rw [e]; exact add_mem hx hy
  | smul c x _ hx =>
    have e : pureA F f (c • x) = c • pureA F f x := by funext z; simp [pureA]; ring
    rw [e]; exact Submodule.smul_mem _ c hx

end GlobalTheory.PureAtPlace
