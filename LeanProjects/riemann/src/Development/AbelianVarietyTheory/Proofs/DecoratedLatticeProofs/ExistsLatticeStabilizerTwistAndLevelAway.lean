import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepFiniteIntegralCollapseTwistPlaceAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

namespace GlobalTheory.CellLevels

variable {D : D7}

private theorem congGrp_mono' (V : HSp D) {I J : Ideal (AE D)} (h : I ≤ J) : congGrp V I ≤ congGrp V J := by
  intro g hg
  unfold congGrp at hg ⊢
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hg ⊢
  rw [← Ideal.Quotient.factor_comp_mk h, Matrix.GeneralLinearGroup.map_comp, MonoidHom.comp_apply, hg, map_one]

private theorem idAt_mono_decorated_lattice {P P' : Pl D → Prop} (h : ∀ v, P v → P' v) : idAt D P ≤ idAt D P' := by
  intro x hx
  unfold idAt at hx ⊢
  rw [Ideal.mem_inf, Submodule.mem_iInf] at hx ⊢
  exact ⟨hx.1, fun w => hx.2 ⟨w.1, fun hp => w.2 (h _ hp)⟩⟩

theorem grpAt_le_of_imp (V : HSp D) {P P' : Pl D → Prop} (h : ∀ v, P v → P' v) : grpAt V P ≤ grpAt V P' := by
  unfold grpAt
  exact congGrp_mono' V (idAt_mono_decorated_lattice h)

def commProd {G : Type*} [Group G] (A B : Subgroup G) (h : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b) : Subgroup G where
  carrier := {g | ∃ a ∈ A, ∃ b ∈ B, g = a * b}
  one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
    rw [mul_assoc, ← mul_assoc b, h b hb a' ha']; simp only [mul_assoc]
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, by rw [_root_.mul_inv_rev, h _ (B.inv_mem hb) _ (A.inv_mem ha)]⟩

private theorem idAt_inf_le_idAt_and (P P' : Pl D → Prop) : idAt D P ⊓ idAt D P' ≤ idAt D (fun p => P p ∧ P' p) := by
  intro x hxx
  have hx := (Ideal.mem_inf.1 hxx).1
  have hx' := (Ideal.mem_inf.1 hxx).2
  unfold idAt at hx hx' ⊢
  rw [Ideal.mem_inf, Submodule.mem_iInf] at hx hx' ⊢
  refine ⟨hx.1, fun w => ?_⟩
  by_cases hp : P w.1
  · exact hx'.2 ⟨w.1, fun h' => w.2 ⟨hp, h'⟩⟩
  · exact hx.2 ⟨w.1, hp⟩

private theorem congGrp_inf_le_congGrp_inf (V : HSp D) (I J : Ideal (AE D)) : congGrp V I ⊓ congGrp V J ≤ congGrp V (I ⊓ J) := by
  intro g hg
  have hI := (Subgroup.mem_inf.1 hg).1
  have hJ := (Subgroup.mem_inf.1 hg).2
  unfold congGrp at hI hJ ⊢
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hI hJ ⊢
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have eI := (Matrix.GeneralLinearGroup.ext_iff _ _).1 hI i j
  have eJ := (Matrix.GeneralLinearGroup.ext_iff _ _).1 hJ i j
  simp only [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply] at eI eJ ⊢
  split_ifs at eI eJ ⊢ with hij
  · rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq] at eI eJ ⊢
    exact Ideal.mem_inf.2 ⟨eI, eJ⟩
  · rw [Ideal.Quotient.eq_zero_iff_mem] at eI eJ ⊢
    exact Ideal.mem_inf.2 ⟨eI, eJ⟩

private theorem mem_grpAt_and_of_mem_grpAt (V : HSp D) {P P' : Pl D → Prop} {g : GA D V} (h : g ∈ grpAt V P) (h' : g ∈ grpAt V P') :
    g ∈ grpAt V (fun p => P p ∧ P' p) := by
  unfold grpAt at h h' ⊢
  exact congGrp_mono' V (idAt_inf_le_idAt_and P P') (congGrp_inf_le_congGrp_inf V _ _ ⟨h, h'⟩)

private theorem inK_congr_of_iff {V : HSp D} {L : Lat V} {P P' : Pl D → Prop} (h : ∀ p, P p ↔ P' p) (κ : GA D V) :
    InK V L P κ ↔ InK V L P' κ := by
  rw [show P = P' from funext fun p => propext (h p)]

private theorem mem_grpAt_of_inK {V : HSp D} {L : Lat V} {P : Pl D → Prop} {κ : GA D V} (h : InK V L P κ) : κ ∈ grpAt V P := by
  unfold InK at h
  exact h.1

theorem levels : ∀ (D : D7) (V : HSp D) (L : Lat V) (gP Q : Finset (Pl D)) (JG : Subgroup (GA D V)), IsSelfDualC V L → Disjoint Q gP → JG ≤ grpAt V (· ∈ gP) → IsCompact (JG : Set (GA D V)) → IsOpen (((JG.subgroupOf (grpAt V (· ∈ gP))) : Subgroup _) : Set (grpAt V (· ∈ gP))) → ∃ K₁ K₂ : Subgroup (GA D V), (∀ g, g ∈ K₁ ↔ InK V L (· ∈ Q) g) ∧ K₁ ≤ grpAt V (· ∈ Q) ∧ K₂ ≤ grpAt V (· ∉ Q) ∧ IsCompact (K₁ : Set (GA D V)) ∧ IsCompact (K₂ : Set (GA D V)) ∧ IsOpen ((K₁.subgroupOf (grpAt V (· ∈ Q)) : Subgroup _) : Set (grpAt V (· ∈ Q))) ∧ IsOpen ((K₂.subgroupOf (grpAt V (· ∉ Q)) : Subgroup _) : Set (grpAt V (· ∉ Q))) ∧ (∀ g, g ∈ K₂ ↔ ∃ κ, InK V L (fun p => p ∉ gP ∧ p ∉ Q) κ ∧ ∃ k ∈ JG, g = κ * k) ∧ ∀ g, (∃ a ∈ K₁, ∃ b ∈ K₂, g = a * b) ↔ ∃ κ, InK V L (· ∉ gP) κ ∧ ∃ k ∈ JG, g = κ * k := by
  intro D V L gP Q JG hL hdisj hJle hJc hJo
  obtain ⟨-, -, -, hQcle, -, -, -, -, hKQ, -⟩ := GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D V Q
  obtain ⟨-, -, -, -, hPcomm, ⟨e, he⟩, -, -, -, -⟩ := GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D V gP
  have hQP : ∀ p, p ∈ Q → p ∉ gP := fun p hp => Finset.disjoint_left.mp hdisj hp

  obtain ⟨⟨K₁, hK₁, hK₁c, hK₁o⟩, -⟩ := hKQ L hL (· ∈ Q)

  obtain ⟨⟨K₃, hK₃, hK₃c, hK₃o⟩, -⟩ := hKQ L hL (fun p => p ∉ gP ∧ p ∉ Q)
  have hpq : ∀ p, (p ∉ gP ∧ p ∈ Q) ↔ p ∈ Q := fun p => ⟨And.right, fun h => ⟨hQP p h, h⟩⟩

  have hsplit : ∀ κ, InK V L (· ∉ gP) κ ↔
      ∃ a b, InK V L (· ∈ Q) a ∧ InK V L (fun p => p ∉ gP ∧ p ∉ Q) b ∧ κ = a * b := by
    intro κ
    refine ((hKQ L hL (· ∉ gP)).2 κ).trans ⟨?_, ?_⟩
    · rintro ⟨a, b, ha, hb, rfl⟩
      exact ⟨a, b, (inK_congr_of_iff (P := fun p => p ∉ gP ∧ p ∈ Q) (P' := (· ∈ Q)) hpq a).1 ha, hb, rfl⟩
    · rintro ⟨a, b, ha, hb, rfl⟩
      exact ⟨a, b, (inK_congr_of_iff (P := fun p => p ∉ gP ∧ p ∈ Q) (P' := (· ∈ Q)) hpq a).2 ha, hb, rfl⟩
  have hK₁le : K₁ ≤ grpAt V (· ∈ Q) := fun g hg => mem_grpAt_of_inK ((hK₁ g).1 hg)
  have hK₃le : K₃ ≤ grpAt V (fun p => p ∉ gP ∧ p ∉ Q) := fun g hg => mem_grpAt_of_inK ((hK₃ g).1 hg)
  have hJQ : grpAt V (· ∈ gP) ≤ grpAt V (· ∉ Q) := grpAt_le_of_imp V fun p hp hq => hQP p hq hp

  have hc : ∀ b ∈ JG, ∀ a ∈ K₃, b * a = a * b := fun b hb a ha =>
    hPcomm b (hJle hb) a (grpAt_le_of_imp V (fun p hp => hp.1) (hK₃le ha))
  have hmem : ∀ g, g ∈ commProd K₃ JG hc ↔ ∃ a ∈ K₃, ∃ b ∈ JG, g = a * b := fun g => Iff.rfl
  refine ⟨K₁, commProd K₃ JG hc, hK₁, hK₁le, ?_, hK₁c, ?_, hK₁o, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := (hmem g).1 hg
    exact mul_mem (grpAt_le_of_imp V (fun p hp => hp.2) (hK₃le ha)) (hJQ (hJle hb))
  · have hset : (commProd K₃ JG hc : Set (GA D V)) =
        (fun p : GA D V × GA D V => p.1 * p.2) '' ((K₃ : Set (GA D V)) ×ˢ (JG : Set (GA D V))) := by
      ext g
      rw [SetLike.mem_coe, hmem, Set.mem_image]
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
      · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
        exact ⟨a, ha, b, hb, rfl⟩
    rw [hset]
    exact (hK₃c.prod hJc).image continuous_mul
  ·
    obtain ⟨φ, hφc, hφ, hφ1⟩ : ∃ φ : grpAt V (· ∉ Q) → grpAt V (· ∈ gP) × grpAt V (· ∉ gP),
        Continuous φ ∧ (∀ g : grpAt V (· ∉ Q), (g : GA D V) = ((φ g).1 : GA D V) * (φ g).2) ∧ φ 1 = 1 := by
      refine ⟨fun g => e.symm ⟨g, hQcle g.2⟩, ?_, ?_, ?_⟩
      · exact e.symm.continuous.comp (continuous_subtype_val.subtype_mk _)
      · intro g
        rw [← he, Homeomorph.apply_symm_apply]
      · rw [Homeomorph.symm_apply_eq]
        apply Subtype.ext
        rw [he]
        simp

    have h3 : ∀ g : grpAt V (· ∉ Q), ((φ g).2 : GA D V) ∈ grpAt V (fun p => p ∉ gP ∧ p ∉ Q) := by
      intro g
      have e2 : ((φ g).2 : GA D V) = ((φ g).1 : GA D V)⁻¹ * g := by
        rw [hφ g, inv_mul_cancel_left]
      refine mem_grpAt_and_of_mem_grpAt V (φ g).2.2 ?_
      rw [e2]
      exact mul_mem (inv_mem (hJQ (φ g).1.2)) g.2
    obtain ⟨ψ, hψc, hψ⟩ : ∃ ψ : grpAt V (· ∉ Q) → grpAt V (fun p => p ∉ gP ∧ p ∉ Q),
        Continuous ψ ∧ ∀ g : grpAt V (· ∉ Q), (ψ g : GA D V) = (φ g).2 :=
      ⟨fun g => ⟨(φ g).2, h3 g⟩, (continuous_subtype_val.comp (continuous_snd.comp hφc)).subtype_mk _, fun _ => rfl⟩
    apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
    have hU : ψ ⁻¹' ((K₃.subgroupOf (grpAt V (fun p => p ∉ gP ∧ p ∉ Q)) : Subgroup _) :
        Set (grpAt V (fun p => p ∉ gP ∧ p ∉ Q))) ∩
        (fun g => (φ g).1) ⁻¹' ((JG.subgroupOf (grpAt V (· ∈ gP)) : Subgroup _) : Set (grpAt V (· ∈ gP))) ∈
        nhds (1 : grpAt V (· ∉ Q)) := by
      refine IsOpen.mem_nhds ((hK₃o.preimage hψc).inter (hJo.preimage (continuous_fst.comp hφc))) ⟨?_, ?_⟩
      · rw [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf, hψ, hφ1]
        exact K₃.one_mem
      · rw [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf, hφ1]
        exact JG.one_mem
    refine Filter.mem_of_superset hU ?_
    rintro g ⟨h1, h2⟩
    rw [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf, hψ] at h1
    rw [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf] at h2
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, hmem]
    refine ⟨(φ g).2, h1, (φ g).1, h2, ?_⟩
    rw [hφ g]
    exact hPcomm _ (φ g).1.2 _ (φ g).2.2
  · intro g
    rw [hmem]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, (hK₃ a).1 ha, b, hb, rfl⟩
    · rintro ⟨κ, hκ, k, hk, rfl⟩
      exact ⟨κ, (hK₃ κ).2 hκ, k, hk, rfl⟩
  · intro g
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      obtain ⟨κ, hκ, k, hk, rfl⟩ := (hmem b).1 hb
      exact ⟨a * κ, (hsplit _).2 ⟨a, κ, (hK₁ a).1 ha, (hK₃ κ).1 hκ, rfl⟩, k, hk, (mul_assoc a κ k).symm⟩
    · rintro ⟨κ, hκ, k, hk, rfl⟩
      obtain ⟨a, b, ha, hb, rfl⟩ := (hsplit κ).1 hκ
      exact ⟨a, (hK₁ a).2 ha, b * k, (hmem _).2 ⟨b, (hK₃ b).2 hb, k, hk, rfl⟩, mul_assoc a b k⟩

end GlobalTheory.CellLevels
