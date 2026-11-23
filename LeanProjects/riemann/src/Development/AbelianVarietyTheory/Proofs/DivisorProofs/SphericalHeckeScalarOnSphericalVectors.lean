import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Formalism.LocalToGlobal.IndefiniteReal.PartsRow
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeCombinationsCommuteFixedVectorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTranslatesEqDoubleCosetAverageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeAleph0SmoothIrreducibleUnitaryAdelicStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.SphScalar

open GlobalTheory.SphLabelOps

section Abstract

variable {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M]

theorem avg (ρ : G →* Module.End ℂ M) (K : Subgroup G) {ι : Type} (s : Finset ι) (a : ι → G) (R : ι → Finset G)
    (w : ι → M)
    (hR : ∀ i ∈ s, (∀ γ ∈ R i, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * a i * k₂) ∧
      ∀ x : G, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a i * k₂) → ∃! γ, γ ∈ R i ∧ γ⁻¹ * x ∈ K)
    (hw : ∀ i ∈ s, ∀ k ∈ K, ρ k (w i) = w i)
    (hm : ∀ k ∈ K, ρ k (∑ i ∈ s, ρ (a i) (w i)) = ∑ i ∈ s, ρ (a i) (w i)) :
    ∑ i ∈ s, ρ (a i) (w i) = ∑ i ∈ s, ((R i).card : ℂ)⁻¹ • ∑ γ ∈ R i, ρ γ (w i) :=
  GlobalTheory.T.sum_translates_eq_doubleCoset_average ρ K s a R w hR hw hm

def fixS (ρ : G →* Module.End ℂ M) (S : Submodule ℂ M) (K : Subgroup G) : Submodule ℂ M where
  carrier := {x | x ∈ S ∧ ∀ k ∈ K, ρ k x = x}
  add_mem' := fun {x y} hx hy => ⟨S.add_mem hx.1 hy.1, fun k hk => by rw [map_add, hx.2 k hk, hy.2 k hk]⟩
  zero_mem' := ⟨S.zero_mem, fun k _ => map_zero _⟩
  smul_mem' := fun c x hx => ⟨S.smul_mem c hx.1, fun k hk => by rw [map_smul, hx.2 k hk]⟩

theorem fixS_simple (ρ : G →* Module.End ℂ M) (S : Submodule ℂ M) (hS : ∀ g, ∀ x ∈ S, ρ g x ∈ S)
    (hirr : ∀ S' : Submodule ℂ M, S' ≤ S → (∀ g, ∀ x ∈ S', ρ g x ∈ S') → S' = ⊥ ∨ S' = S)
    (K : Subgroup G) (Loc Away : Set G) (hdec : ∀ g, ∃ a ∈ Loc, ∃ b ∈ Away, g = a * b)
    (R : G → Finset G) (hR : ∀ a ∈ Loc, Reps K a (R a))
    (W : Submodule ℂ M) (hW : W ≤ fixS ρ S K) (hW0 : W ≠ ⊥)
    (hWR : ∀ a ∈ Loc, ∀ x ∈ W, ∑ γ ∈ R a, ρ γ x ∈ W)
    (hWb : ∀ b ∈ Away, ∀ x ∈ W, ρ b x ∈ W) : W = fixS ρ S K := by
  obtain ⟨w0, hw0W, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  refine le_antisymm hW fun m hm => ?_
  set O : Submodule ℂ M := Submodule.span ℂ (Set.range fun g => ρ g w0) with hOdef
  have hOS : O ≤ S := Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact hS g w0 (hW hw0W).1)
  have hOst : ∀ g, ∀ x ∈ O, ρ g x ∈ O := by
    intro g x hx
    have : O.map (ρ g) ≤ O := by
      rw [hOdef, Submodule.map_span_le]
      rintro _ ⟨h, rfl⟩
      exact Submodule.subset_span ⟨g * h, by show ρ (g * h) w0 = ρ g (ρ h w0); rw [map_mul, Module.End.mul_apply]⟩
    exact this (Submodule.mem_map_of_mem hx)
  have hO : O = S := by
    rcases hirr O hOS hOst with h | h
    · exfalso
      apply hw0
      have : w0 ∈ O := Submodule.subset_span ⟨1, by show ρ 1 w0 = w0; rw [map_one, Module.End.one_apply]⟩
      rw [h] at this
      exact (Submodule.mem_bot ℂ).1 this
    · exact h
  have hmO : m ∈ O := hO ▸ hm.1
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmO
  choose! aa haa bb hbb hab using hdec
  have key : m = ∑ g ∈ c.support, ρ (aa g) (c g • ρ (bb g) w0) := by
    rw [← hc, Finsupp.sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, ← hab g]
  have hwW : ∀ g, c g • ρ (bb g) w0 ∈ W := fun g => W.smul_mem _ (hWb _ (hbb g) _ hw0W)
  have hwK : ∀ g ∈ c.support, ∀ k ∈ K, ρ k (c g • ρ (bb g) w0) = c g • ρ (bb g) w0 := fun g _ k hk =>
    (hW (hwW g)).2 k hk
  have hmK : ∀ k ∈ K, ρ k (∑ g ∈ c.support, ρ (aa g) (c g • ρ (bb g) w0)) =
      ∑ g ∈ c.support, ρ (aa g) (c g • ρ (bb g) w0) := by
    rw [← key]; exact hm.2
  have e := avg ρ K c.support aa (fun g => R (aa g)) (fun g => c g • ρ (bb g) w0) (fun g _ => hR _ (haa g)) hwK hmK
  rw [key, e]
  exact W.sum_mem fun g _ => W.smul_mem _ (hWR _ (haa g) _ (hwW g))

theorem abs_scalar (ρ : G →* Module.End ℂ M) (S : Submodule ℂ M) (hS : ∀ g, ∀ x ∈ S, ρ g x ∈ S)
    (hirr : ∀ S' : Submodule ℂ M, S' ≤ S → (∀ g, ∀ x ∈ S', ρ g x ∈ S') → S' = ⊥ ∨ S' = S)
    (hrank : Module.rank ℂ S ≤ Cardinal.aleph0)
    (K : Subgroup G) (Loc Away : Set G) (hdec : ∀ g, ∃ a ∈ Loc, ∃ b ∈ Away, g = a * b)
    (hcomm : ∀ k ∈ K, ∀ b ∈ Away, k * b = b * k)
    (R : G → Finset G) (hR : ∀ a ∈ Loc, Reps K a (R a))
    (T : M →ₗ[ℂ] M)
    (hTS : ∀ x ∈ fixS ρ S K, T x ∈ fixS ρ S K)
    (hTb : ∀ b ∈ Away, ∀ x ∈ fixS ρ S K, T (ρ b x) = ρ b (T x))
    (hTR : ∀ a ∈ Loc, ∀ x ∈ fixS ρ S K, T (∑ γ ∈ R a, ρ γ x) = ∑ γ ∈ R a, ρ γ (T x)) :
    ∃ c : ℂ, ∀ x ∈ fixS ρ S K, T x = c • x := by
  classical
  set F := fixS ρ S K with hFdef
  have hRF : ∀ a ∈ Loc, ∀ x ∈ F, ∑ γ ∈ R a, ρ γ x ∈ F := by
    intro a ha x hx
    refine ⟨S.sum_mem fun γ _ => hS γ x hx.1, fun k hk => ?_⟩
    rw [map_sum]
    have := (hR a ha).sum_eq (hR a ha) hk (fun g => ρ g x)
      (fun y l hl => by rw [map_mul, Module.End.mul_apply, hx.2 l hl])
    simpa only [map_mul, Module.End.mul_apply] using this
  have hbF : ∀ b ∈ Away, ∀ x ∈ F, ρ b x ∈ F := fun b hb x hx =>
    ⟨hS b x hx.1, fun k hk => by
      rw [← Module.End.mul_apply, ← map_mul, hcomm k hk b hb, map_mul, Module.End.mul_apply, hx.2 k hk]⟩
  have stab : ∀ W : Submodule ℂ M, W ≤ F → (∀ a ∈ Loc, ∀ x ∈ W, ∑ γ ∈ R a, ρ γ x ∈ W) →
      (∀ b ∈ Away, ∀ x ∈ W, ρ b x ∈ W) → W = ⊥ ∨ W = F := fun W h1 h2 h3 => by
    by_cases h0 : W = ⊥
    · exact Or.inl h0
    · exact Or.inr (fixS_simple ρ S hS hirr K Loc Away hdec R hR W h1 h0 h2 h3)
  have hrankF : Module.rank ℂ F ≤ Cardinal.aleph0 :=
    (Submodule.rank_mono (fun x (hx : x ∈ F) => hx.1)).trans hrank
  by_cases hF : Nontrivial F
  swap
  · refine ⟨0, fun x hx => ?_⟩
    rw [not_nontrivial_iff_subsingleton] at hF
    have : (⟨x, hx⟩ : F) = 0 := Subsingleton.elim _ _
    have hx0 : x = 0 := congrArg Subtype.val this
    rw [hx0, map_zero, smul_zero]
  let TF : Module.End ℂ F := T.restrict hTS
  obtain ⟨c, hc⟩ := GlobalTheory.LocGL.exists_not_isUnit_sub hrankF TF
  have hTF : ∀ y : F, ((TF - algebraMap ℂ (Module.End ℂ F) c) y : M) = T y - c • (y : M) := fun y => rfl
  refine ⟨c, ?_⟩
  let W1 : Submodule ℂ M :=
    { carrier := {x | x ∈ F ∧ T x = c • x}
      add_mem' := fun {x y} hx hy => ⟨F.add_mem hx.1 hy.1, by rw [map_add, hx.2, hy.2, smul_add]⟩
      zero_mem' := ⟨F.zero_mem, by rw [map_zero, smul_zero]⟩
      smul_mem' := fun a x hx => ⟨F.smul_mem a hx.1, by rw [map_smul, hx.2, smul_comm]⟩ }
  let W2 : Submodule ℂ M :=
    { carrier := {x | ∃ y ∈ F, x = T y - c • y}
      add_mem' := by
        rintro _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
        exact ⟨y + y', F.add_mem hy hy', by rw [map_add, smul_add]; abel⟩
      zero_mem' := ⟨0, F.zero_mem, by rw [map_zero, smul_zero, sub_zero]⟩
      smul_mem' := by
        rintro a _ ⟨y, hy, rfl⟩
        exact ⟨a • y, F.smul_mem a hy, by rw [map_smul, smul_sub, smul_comm a c]⟩ }
  have hW1 : W1 = ⊥ ∨ W1 = F := by
    refine stab W1 (fun x hx => hx.1) (fun a ha x hx => ⟨hRF a ha x hx.1, ?_⟩) (fun b hb x hx => ⟨hbF b hb x hx.1, ?_⟩)
    · rw [hTR a ha x hx.1, hx.2]
      simp only [map_smul, Finset.smul_sum]
    · rw [hTb b hb x hx.1, hx.2, map_smul]
  rcases hW1 with h1 | h1
  swap
  · intro x hx
    have : x ∈ W1 := h1 ▸ hx
    exact this.2
  exfalso
  have hinj : ∀ y ∈ F, T y - c • y = 0 → y = 0 := by
    intro y hy e
    have : y ∈ W1 := ⟨hy, sub_eq_zero.1 e⟩
    rw [h1] at this
    exact (Submodule.mem_bot ℂ).1 this
  have hW2 : W2 = ⊥ ∨ W2 = F := by
    refine stab W2 ?_ ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact F.sub_mem (hTS y hy) (F.smul_mem c hy)
    · rintro a ha _ ⟨y, hy, rfl⟩
      refine ⟨∑ γ ∈ R a, ρ γ y, hRF a ha y hy, ?_⟩
      rw [hTR a ha y hy]
      simp only [map_sub, map_smul, Finset.sum_sub_distrib, Finset.smul_sum]
    · rintro b hb _ ⟨y, hy, rfl⟩
      refine ⟨ρ b y, hbF b hb y hy, ?_⟩
      rw [hTb b hb y hy, map_sub, map_smul]
  apply hc
  rw [Module.End.isUnit_iff]
  constructor
  · intro y y' e
    have e' : ((TF - algebraMap ℂ (Module.End ℂ F) c) (y - y') : M) = 0 := by
      rw [map_sub, e, sub_self]; rfl
    rw [hTF] at e'
    exact sub_eq_zero.1 (Subtype.ext (hinj _ (y - y').2 e'))
  · intro z
    rcases hW2 with h2 | h2
    · exfalso
      obtain ⟨y, hy⟩ := exists_ne (0 : F)
      have : (T y - c • (y : M)) ∈ W2 := ⟨y, y.2, rfl⟩
      rw [h2] at this
      exact hy (Subtype.ext (hinj _ y.2 ((Submodule.mem_bot ℂ).1 this)))
    · have : (z : M) ∈ W2 := by rw [h2]; exact z.2
      obtain ⟨y, hy, e⟩ := this
      exact ⟨⟨y, hy⟩, Subtype.ext (by rw [hTF]; exact e.symm)⟩

end Abstract

section Concrete

variable {D : D7} {V : HSp D} {n : ℕ}

theorem countRank {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (π : Formalism.L2.NG.FinTyp L n) :
    Module.rank ℂ π.S ≤ Cardinal.aleph0 :=
  GlobalTheory.T.rank_le_aleph0_smooth_irreducible_unitaryAdelic π

def rtHom (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) :
    Formalism.AUTREP.GAf L n →* Module.End ℂ (Formalism.AUTREP.GAf L n → ℂ) where
  toFun h := Formalism.L2.NG.rt L n h
  map_one' := LinearMap.ext fun f => principalLevelFrame.rt_one f
  map_mul' g h := LinearMap.ext fun f => (principalLevelFrame.rt_rt g h f).symm

theorem rtHom_apply (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (h : Formalism.AUTREP.GAf L n)
    (f : Formalism.AUTREP.GAf L n → ℂ) : rtHom L n h f = Formalism.L2.NG.rt L n h f := rfl

def rtA (V : HSp D) : GA D V →* Module.End ℂ (GA D V → ℂ) where
  toFun g := { toFun := fun F x => F (x * g), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  map_one' := by ext F x; simp
  map_mul' g h := by ext F x; simp [mul_assoc]

theorem rtA_apply (V : HSp D) (g : GA D V) (F : GA D V → ℂ) (x : GA D V) : rtA V g F x = F (x * g) := rfl

theorem pre_psi (Q : principalLevelFrame.RowPsi V n) (h : Formalism.AUTREP.GAf D.host.E n) : principalLevelFrame.pre Q (Q.ψ h) = h := by
  have hx : ∃ x, Q.ψ x = Q.ψ h := ⟨h, rfl⟩
  unfold principalLevelFrame.pre
  rw [dif_pos hx]
  exact Q.inj hx.choose_spec

open Classical in

def ext0 (Q : principalLevelFrame.RowPsi V n) : (Formalism.AUTREP.GAf D.host.E n → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun x g := if ∃ y, Q.ψ y = g then x (principalLevelFrame.pre Q g) else 0
  map_add' x y := by
    funext g
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c x := by
    funext g
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

theorem extendByZeroThroughUnitaryFrame_psi (Q : principalLevelFrame.RowPsi V n) (x : Formalism.AUTREP.GAf D.host.E n → ℂ) (h : Formalism.AUTREP.GAf D.host.E n) :
    ext0 Q x (Q.ψ h) = x h := by
  simp only [ext0, LinearMap.coe_mk, AddHom.coe_mk]
  rw [if_pos ⟨h, rfl⟩, pre_psi]

theorem extendByZeroThroughUnitaryFrame_right_translate (Q : principalLevelFrame.RowPsi V n) (x : Formalism.AUTREP.GAf D.host.E n → ℂ) (h : Formalism.AUTREP.GAf D.host.E n) :
    ext0 Q (Formalism.L2.NG.rt D.host.E n h x) = rtA V (Q.ψ h) (ext0 Q x) := by
  funext g
  by_cases hg : ∃ y, Q.ψ y = g
  · obtain ⟨y, rfl⟩ := hg
    rw [rtA_apply, ← map_mul, extendByZeroThroughUnitaryFrame_psi, extendByZeroThroughUnitaryFrame_psi, principalLevelFrame.rt_apply]
  · have hg' : ¬ ∃ y, Q.ψ y = g * Q.ψ h := fun ⟨y, hy⟩ =>
      hg ⟨y * h⁻¹, by rw [map_mul, hy, map_inv, mul_inv_cancel_right]⟩
    rw [rtA_apply]
    simp only [ext0, LinearMap.coe_mk, AddHom.coe_mk]
    rw [if_neg hg, if_neg hg']

theorem extendByZeroThroughUnitaryFrame_injective (Q : principalLevelFrame.RowPsi V n) {x x' : Formalism.AUTREP.GAf D.host.E n → ℂ} (H : ext0 Q x = ext0 Q x') :
    x = x' := funext fun h => by
  have := congrFun H (Q.ψ h)
  rwa [extendByZeroThroughUnitaryFrame_psi, extendByZeroThroughUnitaryFrame_psi] at this

theorem extendByZeroThroughUnitaryFrame_hecke (Q : principalLevelFrame.RowPsi V n) (R : Finset (GA D V)) (hR : ∀ γ ∈ R, ∃ y, Q.ψ y = γ)
    (x : Formalism.AUTREP.GAf D.host.E n → ℂ) :
    ext0 Q (principalLevelFrame.Hecke₃ Q R x) = ∑ γ ∈ R, rtA V γ (ext0 Q x) := by
  unfold principalLevelFrame.Hecke₃
  rw [principalLevelFrame.heckeG_apply, map_sum]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  obtain ⟨y, rfl⟩ := hR γ hγ
  rw [pre_psi, extendByZeroThroughUnitaryFrame_right_translate]

theorem opOf_single {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)
    (d : List ℤ) (u : M) : GlobalTheory.Hk3.opOf π P (Finsupp.single d 1) u = ∑ γ ∈ GlobalTheory.Hk3.rep V P d, π γ u := by
  unfold GlobalTheory.Hk3.opOf
  rw [Finsupp.sum_single_index (by rw [zero_smul]), one_smul, LinearMap.sum_apply]

theorem reps_comap {G H : Type} [Group G] [Group H] [DecidableEq G] (ψ : G →* H) (hinj : Function.Injective ψ)
    (K : Subgroup H) (hK : ∀ k ∈ K, ∃ g, ψ g = k) (pre : H → G) (hpre : ∀ g, pre (ψ g) = g) {a : G}
    {R : Finset H} (hR : ∀ γ ∈ R, ∃ g, ψ g = γ) (h : Reps K (ψ a) R) : Reps (K.comap ψ) a (R.image pre) := by
  refine ⟨fun γ' hγ' => ?_, fun x hx => ?_⟩
  · obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hγ'
    obtain ⟨g, rfl⟩ := hR γ hγ
    obtain ⟨k1, hk1, k2, hk2, e⟩ := h.1 _ hγ
    obtain ⟨g1, rfl⟩ := hK k1 hk1
    obtain ⟨g2, rfl⟩ := hK k2 hk2
    refine ⟨g1, hk1, g2, hk2, ?_⟩
    rw [hpre]
    apply hinj
    rw [e, map_mul, map_mul]
  · obtain ⟨k1, hk1, k2, hk2, rfl⟩ := hx
    obtain ⟨γ, ⟨hγ, hγK⟩, huniq⟩ := h.2 (ψ k1 * ψ a * ψ k2) ⟨_, hk1, _, hk2, rfl⟩
    obtain ⟨g, rfl⟩ := hR γ hγ
    refine ⟨g, ⟨Finset.mem_image.2 ⟨ψ g, hγ, hpre g⟩, ?_⟩, ?_⟩
    · rw [Subgroup.mem_comap, map_mul, map_inv, map_mul, map_mul]
      exact hγK
    · rintro g' ⟨hg', hg'K⟩
      obtain ⟨γ', hγ', rfl⟩ := Finset.mem_image.1 hg'
      obtain ⟨g'', rfl⟩ := hR γ' hγ'
      rw [hpre] at hg'K ⊢
      rw [Subgroup.mem_comap, map_mul, map_inv, map_mul, map_mul] at hg'K
      exact hinj (huniq (ψ g'') ⟨hγ', hg'K⟩)

theorem sphOp_facts {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} {Kv : Subgroup (GA D V)} {d : List ℤ}
    {R : Finset (GA D V)} (hef : IsPrimeIdem P e f) (hK : hyp V P = Kv) (hR : SphOp V P d R) :
    (∀ γ ∈ R, γ ∈ GfC V ∧ SuppF V f γ) ∧ ∃ α, Reps Kv α R := by
  obtain ⟨e', f', ϖ, α, -, h', -, -, -, -, -, -, -, hs, hc⟩ := hR
  obtain ⟨-, rfl⟩ := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e f hef).2.2.2.1 e' f' h'
  have hK' : {k | k ∈ KsphC V ∅ ∧ SuppF V f' k} = (Kv : Set (GA D V)) := (GlobalTheory.SphLabelOps.hyp_eq hef).symm.trans hK
  rw [IsCosetRep, hK'] at hc
  exact ⟨fun γ hγ => ⟨(hc.1 γ hγ).1, hs γ hγ⟩, α, fun γ hγ => (hc.1 γ hγ).2, hc.2⟩

end Concrete

section Main

open GlobalTheory.IdemSupport

theorem spherical_scalar : ∀ {D : D7} {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E)
    (Q : principalLevelFrame.RowPsi V n), StdPsi hF Q → ∀ (π : Formalism.L2.NG.FinTyp D.host.E n) Pr d B, SphOp V Pr d B →
      ∃ a : ℂ, ∀ x ∈ π.S, (∀ κ, Q.ψ κ ∈ hyp V Pr → Formalism.L2.NG.rt D.host.E n κ x = x) →
        principalLevelFrame.Hecke₃ Q B x = a • x := by
  intro D V n hF Q _ π Pr d B hB
  classical
  have SG := supported_group_and_prime_idempotents V
  obtain ⟨Kv, hKv⟩ := GlobalTheory.SphLabelOps.exists_hyp V Pr
  obtain ⟨e, f, hef⟩ := SG.2.1 Pr
  obtain ⟨hff, hcf, hfG, -, -⟩ := SG.2.2.1 Pr e f hef
  obtain ⟨-, hsplit, hcomm0⟩ := SG.1 f hff hcf
  have hf0 : f * (1 - f) = 0 := by rw [mul_sub, mul_one, hff, sub_self]
  have hKvG : ∀ k ∈ Kv, k ∈ GfC V := fun k hk => by
    have : k ∈ hyp V Pr := by rw [hKv]; exact hk
    exact this.1.1
  have hKvS : ∀ k ∈ Kv, SuppF V f k := fun k hk => by
    have : k ∈ hyp V Pr := by rw [hKv]; exact hk
    rw [GlobalTheory.SphLabelOps.hyp_eq hef] at this
    exact this.2
  have hon : ∀ g ∈ GfC V, ∃ y, Q.ψ y = g := fun g hg => Q.onto g hg
  let K : Subgroup (Formalism.AUTREP.GAf D.host.E n) := Kv.comap Q.ψ
  let Loc : Set (Formalism.AUTREP.GAf D.host.E n) := {h | SuppF V f (Q.ψ h)}
  let Away : Set (Formalism.AUTREP.GAf D.host.E n) := {h | SuppF V (1 - f) (Q.ψ h)}
  have hdec : ∀ g, ∃ a ∈ Loc, ∃ b ∈ Away, g = a * b := by
    intro g
    obtain ⟨g1, g2, h1, h2, hg⟩ := hsplit (Q.ψ g)
    obtain ⟨a, rfl⟩ := hon g1 (hfG g1 h1)
    have hg2 : g2 ∈ GfC V := by
      have : g2 = (Q.ψ a)⁻¹ * Q.ψ g := by rw [hg, inv_mul_cancel_left]
      rw [this]
      exact (GfC V).mul_mem ((GfC V).inv_mem (Q.into a)) (Q.into g)
    obtain ⟨b, rfl⟩ := hon g2 hg2
    exact ⟨a, h1, b, h2, Q.inj (by rw [hg, map_mul])⟩
  have hcomm : ∀ k ∈ K, ∀ b ∈ Away, k * b = b * k := fun k hk b hb =>
    Q.inj (by rw [map_mul, map_mul]; exact (hcomm0 (1 - f) _ _ hf0 (hKvS _ hk) hb).eq)

  have hlab : ∀ a ∈ Loc, ∃ dd, IsLab V Pr dd ∧
      ∀ γ ∈ GlobalTheory.Hk3.rep V Pr dd, ∃ k₁ ∈ hyp V Pr, ∃ k₂ ∈ hyp V Pr, γ = k₁ * Q.ψ a * k₂ := fun a ha => by
    obtain ⟨dd, h1, h2, -⟩ := (GlobalTheory.SphLabelOps.label_operators V Pr).2.2.2.2 e f (Q.ψ a) hef ha
    exact ⟨dd, h1, h2⟩
  choose! dd hdd1 hdd2 using hlab
  have hsph : ∀ a ∈ Loc, SphOp V Pr (dd a) (GlobalTheory.Hk3.rep V Pr (dd a)) := fun a ha => by
    have h := hdd1 a ha
    unfold GlobalTheory.Hk3.rep
    rw [dif_pos h]
    exact h.choose_spec
  have hrepG : ∀ a ∈ Loc, ∀ γ ∈ GlobalTheory.Hk3.rep V Pr (dd a), ∃ y, Q.ψ y = γ := fun a ha γ hγ =>
    hon γ ((sphOp_facts hef hKv (hsph a ha)).1 γ hγ).1
  have hrepsV : ∀ a ∈ Loc, Reps Kv (Q.ψ a) (GlobalTheory.Hk3.rep V Pr (dd a)) := by
    intro a ha
    obtain ⟨-, α, hα⟩ := sphOp_facts hef hKv (hsph a ha)
    obtain ⟨γ0, ⟨hγ0, -⟩, -⟩ := hα.2 α ⟨1, one_mem _, 1, one_mem _, by group⟩
    obtain ⟨k1, hk1, k2, hk2, e1⟩ := hα.1 γ0 hγ0
    obtain ⟨k1', hk1', k2', hk2', e2⟩ := hdd2 a ha γ0 hγ0
    rw [hKv] at hk1' hk2'
    have hαe : α = (k1⁻¹ * k1') * Q.ψ a * (k2' * k2⁻¹) := by
      rw [e1] at e2
      calc α = k1⁻¹ * (k1 * α * k2) * k2⁻¹ := by group
        _ = _ := by rw [e2]; group
    rw [hαe] at hα
    exact Reps.of_dc (mul_mem (inv_mem hk1) hk1') (mul_mem hk2' (inv_mem hk2)) hα
  let R : Formalism.AUTREP.GAf D.host.E n → Finset (Formalism.AUTREP.GAf D.host.E n) :=
    fun a => (GlobalTheory.Hk3.rep V Pr (dd a)).image (principalLevelFrame.pre Q)
  have hR : ∀ a ∈ Loc, Reps K a (R a) := fun a ha =>
    reps_comap Q.ψ Q.inj Kv (fun k hk => hon k (hKvG k hk)) (principalLevelFrame.pre Q) (pre_psi Q) (hrepG a ha) (hrepsV a ha)
  have hsumR : ∀ a ∈ Loc, ∀ x : Formalism.AUTREP.GAf D.host.E n → ℂ,
      ∑ γ ∈ R a, rtHom D.host.E n γ x = principalLevelFrame.Hecke₃ Q (GlobalTheory.Hk3.rep V Pr (dd a)) x := by
    intro a ha x
    unfold principalLevelFrame.Hecke₃
    rw [principalLevelFrame.heckeG_apply, Finset.sum_image]
    · rfl
    · intro γ hγ γ' hγ' e
      obtain ⟨y, rfl⟩ := hrepG a ha γ hγ
      obtain ⟨y', rfl⟩ := hrepG a ha γ' hγ'
      rw [pre_psi, pre_psi] at e
      rw [e]

  obtain ⟨hBG, -⟩ := sphOp_facts hef hKv hB
  have hBr : ∀ γ ∈ B, ∃ y, Q.ψ y = γ := fun γ hγ => hon γ (hBG γ hγ).1

  have hfixA : ∀ x : Formalism.AUTREP.GAf D.host.E n → ℂ, (∀ k ∈ K, rtHom D.host.E n k x = x) →
      ∀ k ∈ hyp V Pr, rtA V k (ext0 Q x) = ext0 Q x := by
    intro x hx k hk
    have hk' : k ∈ Kv := by rw [hKv] at hk; exact hk
    obtain ⟨κ, rfl⟩ := hon k (hKvG k hk')
    rw [← extendByZeroThroughUnitaryFrame_right_translate]
    exact congrArg _ (hx κ hk')
  have hfixBack : ∀ x : Formalism.AUTREP.GAf D.host.E n → ℂ, (∀ k ∈ hyp V Pr, rtA V k (ext0 Q x) = ext0 Q x) →
      ∀ k ∈ K, rtHom D.host.E n k x = x := by
    intro x hx k hk
    apply extendByZeroThroughUnitaryFrame_injective Q
    rw [rtHom_apply, extendByZeroThroughUnitaryFrame_right_translate]
    exact hx _ (by rw [hKv]; exact hk)
  have hBop : ∀ x : Formalism.AUTREP.GAf D.host.E n → ℂ, (∀ k ∈ K, rtHom D.host.E n k x = x) →
      ext0 Q (principalLevelFrame.Hecke₃ Q B x) = GlobalTheory.Hk3.opOf (rtA V) Pr (Finsupp.single d 1) (ext0 Q x) := by
    intro x hx
    rw [extendByZeroThroughUnitaryFrame_hecke Q B hBr]
    exact ((GlobalTheory.SphLabelOps.label_operators V Pr).1 d B hB).2 _ (rtA V) _ (hfixA x hx)
  have hRop : ∀ a ∈ Loc, ∀ x : Formalism.AUTREP.GAf D.host.E n → ℂ,
      ext0 Q (principalLevelFrame.Hecke₃ Q (GlobalTheory.Hk3.rep V Pr (dd a)) x) =
        GlobalTheory.Hk3.opOf (rtA V) Pr (Finsupp.single (dd a) 1) (ext0 Q x) := by
    intro a ha x
    rw [extendByZeroThroughUnitaryFrame_hecke Q _ (hrepG a ha), opOf_single]
  have hopfix : ∀ c, ∀ x : Formalism.AUTREP.GAf D.host.E n → ℂ, (∀ k ∈ K, rtHom D.host.E n k x = x) →
      ∀ k ∈ hyp V Pr, rtA V k (GlobalTheory.Hk3.opOf (rtA V) Pr c (ext0 Q x)) = GlobalTheory.Hk3.opOf (rtA V) Pr c (ext0 Q x) :=
    fun c x hx => (GlobalTheory.SphLabelOps.label_operators V Pr).2.1 c _ (rtA V) _ (hfixA x hx)

  have hTB : ∀ x : Formalism.AUTREP.GAf D.host.E n → ℂ, principalLevelFrame.Hecke₃ Q B x = ∑ γ ∈ B, rtHom D.host.E n (principalLevelFrame.pre Q γ) x := by
    intro x
    unfold principalLevelFrame.Hecke₃
    rw [principalLevelFrame.heckeG_apply]
    rfl
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ x ∈ fixS (rtHom D.host.E n) π.S K, principalLevelFrame.Hecke₃ Q B x = c • x := by
    refine abs_scalar (rtHom D.host.E n) π.S (fun g x hx => π.stable g x hx) π.irr (countRank π)
      K Loc Away hdec hcomm R hR (principalLevelFrame.Hecke₃ Q B) ?_ ?_ ?_
    ·
      intro x hx
      refine ⟨?_, ?_⟩
      · rw [hTB]
        exact π.S.sum_mem fun γ _ => π.stable _ x hx.1
      · apply hfixBack
        rw [hBop x hx.2]
        exact hopfix _ x hx.2
    ·
      intro b hb x _
      rw [hTB, hTB, map_sum]
      refine Finset.sum_congr rfl fun γ hγ => ?_
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      obtain ⟨y, rfl⟩ := hBr γ hγ
      rw [pre_psi]
      exact Q.inj (by rw [map_mul, map_mul]; exact (hcomm0 (1 - f) _ _ hf0 (hBG _ hγ).2 hb).eq)
    ·
      intro a ha x hx
      rw [hsumR a ha, hsumR a ha]
      apply extendByZeroThroughUnitaryFrame_injective Q
      have hx' : ∀ k ∈ K, rtHom D.host.E n k (principalLevelFrame.Hecke₃ Q (GlobalTheory.Hk3.rep V Pr (dd a)) x) =
          principalLevelFrame.Hecke₃ Q (GlobalTheory.Hk3.rep V Pr (dd a)) x := by
        apply hfixBack
        rw [hRop a ha]
        exact hopfix _ x hx.2
      have hx'' : ∀ k ∈ K, rtHom D.host.E n k (principalLevelFrame.Hecke₃ Q B x) = principalLevelFrame.Hecke₃ Q B x := by
        apply hfixBack
        rw [hBop x hx.2]
        exact hopfix _ x hx.2
      rw [hBop _ hx', hRop a ha, hRop a ha, hBop x hx.2]
      exact GlobalTheory.T.sphericalHeckeCombinations_commute_fixedVectors V Pr _ _ _ (rtA V) _ (hfixA x hx.2)

  exact ⟨c, fun x hx hfx => hc x ⟨hx, fun k hk => hfx k (by rw [hKv]; exact hk)⟩⟩

end Main

end GlobalTheory.SphScalar

end
