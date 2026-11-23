import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SobSympl
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocGl

open GlobalTheory.FinPl (grpAt grpOff idAt intAt latV Lat InK Moves SplitPt)
open GlobalTheory.IwaPlace (hermAt)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

theorem idem_eq : q.e + cA D q.e = GlobalTheory.FinPlLoc.idem D (· = q.v) := by
  obtain ⟨ε, ⟨α, rfl, h1, h0⟩, h⟩ := q.above
  have : α = GlobalTheory.FinPlLoc.ePl D (· = q.v) := RestrictedProduct.ext _ _ fun w => by
    change evalV D.host.F w α = evalV D.host.F w (GlobalTheory.FinPlLoc.ePl D (· = q.v))
    rw [GlobalTheory.FinPlLoc.evalV_ePl]
    split_ifs with hw
    · subst hw; exact h1
    · exact h0 w hw
  rw [h, this]; rfl

variable {V : HSp D}

theorem supp_iff (x : GA D V) : SuppAt q.e V x ↔ x ∈ grpAt V (· = q.v) := by
  unfold GlobalTheory.FinPl.grpAt
  rw [GlobalTheory.FinPlLoc.mem_congGrp]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [GlobalTheory.FinPlLoc.mem_idAt_iff, ← idem_eq]; rfl

theorem entry_eq {z : AE D} (hz : (q.e + cA D q.e) * z = z) : z = q.sec (q.pr z) + cA D (q.sec (q.pr (cA D z))) := by
  rw [q.sec_pr, q.sec_pr, RingHom.map_mul, cA_cA, ← add_mul, hz]

variable {Y : Type} [Fintype Y] [DecidableEq Y] {F : Frame k V.rank Y} {gl : GL Y k →* GA D V}

theorem map_one' {n : ℕ} : (1 : Matrix (Fin n) (Fin n) (AE D)).map q.pr = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem continuous_mt_gl (h : ∀ g, (ofSplit q).IsLoc F (gl g) g) : Continuous fun g => Formalism.L2.Theta.mt V (gl g) := by
  haveI := (Formalism.IndefR.Eqv.ae_facts D).1
  have h2 : ∀ g, (Formalism.L2.Theta.mt V (gl g)).map q.pr = F.β * g.val * F.γ := fun g => (h g).2
  have e1 : ∀ g, (Formalism.L2.Theta.mt V (gl g) - 1).map q.pr = F.β * g.val * F.γ - 1 := fun g => by
    rw [Matrix.map_sub _ (map_sub q.pr), map_one', h2]
  have e2 : ∀ g, (adj (Formalism.L2.Theta.mt V (gl g) - 1)).map q.pr =
      (gA V).map q.pr * (F.β * (g⁻¹).val * F.γ) * (giA V).map q.pr - 1 := fun g => by
    have inv : adj (Formalism.L2.Theta.mt V (gl g)) = gA V * Formalism.L2.Theta.mt V (gl g)⁻¹ * giA V := by
      rw [GlobalTheory.MixModel.mt_inv, gA_giA_cancel, Matrix.mul_assoc, gA_mul_giA, Matrix.mul_one]
    rw [adj_sub, adj_one, Matrix.map_sub _ (map_sub q.pr), map_one', inv, Matrix.map_mul, Matrix.map_mul, ← map_inv, h2]
  have c1 : Continuous fun g : GL Y k => F.β * g.val * F.γ - 1 :=
    ((continuous_const.matrix_mul Units.continuous_val).matrix_mul continuous_const).sub continuous_const
  have c2 : Continuous fun g : GL Y k => (gA V).map q.pr * (F.β * (g⁻¹).val * F.γ) * (giA V).map q.pr - 1 :=
    ((continuous_const.matrix_mul ((continuous_const.matrix_mul Units.continuous_coe_inv).matrix_mul
      continuous_const)).matrix_mul continuous_const).sub continuous_const
  refine continuous_matrix fun i j => ?_
  have c3 := (continuous_const (y := (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)).add
    ((q.cont_sec.comp (c1.matrix_elem i j)).add
      ((Formalism.IndefR.Eqv.continuous_cA (D := D)).comp (q.cont_sec.comp (c2.matrix_elem j i))))
  refine c3.congr fun g => ?_
  have e3 := entry_eq q ((h g).1 i j)
  simp only [Function.comp, Pi.add_apply]
  rw [← e1, ← e2]
  change _ + (q.sec (q.pr ((Formalism.L2.Theta.mt V (gl g) - 1) i j)) +
    cA D (q.sec (q.pr (cA D ((Formalism.L2.Theta.mt V (gl g) - 1) i j))))) = _
  rw [← e3, Matrix.sub_apply, add_sub_cancel]

theorem continuous_gl (h : ∀ g, (ofSplit q).IsLoc F (gl g) g) : Continuous gl := by
  refine Continuous.subtype_mk (f := fun g => matHom V (gl g)) (Units.continuous_iff.2 ⟨continuous_mt_gl q h, ?_⟩) _
  refine ((continuous_mt_gl q h).comp continuous_inv).congr fun g => ?_
  simp only [Function.comp]
  rw [map_inv]; rfl

variable (F) in

def comp (x : GA D V) : GL Y k :=
  have key : ∀ x y : GA D V, x * y = 1 →
      F.γ * (Formalism.L2.Theta.mt V x).map q.pr * F.β * (F.γ * (Formalism.L2.Theta.mt V y).map q.pr * F.β) = 1 := fun x y h => by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F.β, F.βγ, Matrix.one_mul, ← Matrix.mul_assoc ((Formalism.L2.Theta.mt V x).map q.pr), ← Matrix.map_mul,
      ← GlobalTheory.MixModel.mt_mul, h, GlobalTheory.MixModel.mt_one, map_one', Matrix.one_mul, F.γβ]
  ⟨F.γ * (Formalism.L2.Theta.mt V x).map q.pr * F.β, F.γ * (Formalism.L2.Theta.mt V x⁻¹).map q.pr * F.β,
    key x x⁻¹ (mul_inv_cancel x), key x⁻¹ x (inv_mul_cancel x)⟩

theorem continuous_comp : Continuous (comp q F) := by
  haveI := (Formalism.IndefR.Eqv.ga_facts D V).1
  have c0 : Continuous (Formalism.L2.Theta.mt V) := Units.continuous_val.comp continuous_subtype_val
  have c : Continuous fun x : GA D V => F.γ * (Formalism.L2.Theta.mt V x).map q.pr * F.β :=
    (continuous_const.matrix_mul (c0.matrix_map q.cont_pr)).matrix_mul continuous_const
  exact Units.continuous_iff.2 ⟨c, c.comp continuous_inv⟩

theorem comp_gl (h : ∀ g, (ofSplit q).IsLoc F (gl g) g) (g : GL Y k) : comp q F (gl g) = g := by
  have h2 : (Formalism.L2.Theta.mt V (gl g)).map q.pr = F.β * g.val * F.γ := (h g).2
  refine Units.ext ?_
  change F.γ * (Formalism.L2.Theta.mt V (gl g)).map q.pr * F.β = _
  rw [h2]
  simp only [Matrix.mul_assoc]
  rw [F.γβ, Matrix.mul_one, ← Matrix.mul_assoc, F.γβ, Matrix.one_mul]

theorem isClosedEmbedding_gl (h : ∀ g, (ofSplit q).IsLoc F (gl g) g) : Topology.IsClosedEmbedding gl := by
  haveI := (Formalism.IndefR.Eqv.ga_facts D V).2.1
  exact Function.LeftInverse.isClosedEmbedding (f := comp q F) (comp_gl q h) (continuous_comp q) (continuous_gl q h)

theorem gl_mem (h : ∀ g, (ofSplit q).IsLoc F (gl g) g) (g : GL Y k) : gl g ∈ grpAt V (· = q.v) :=
  (supp_iff q _).1 (h g).1

theorem range_gl (h : ∀ g, (ofSplit q).IsLoc F (gl g) g) : gl.range = grpAt V (· = q.v) := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨g, rfl⟩
    exact gl_mem q h g
  · obtain ⟨g, hg⟩ := GlobalTheory.LocGrp.exists_of_supp (ofSplit q) F ((supp_iff q x).2 hx)
    exact ⟨g, GlobalTheory.LocGrp.isLoc_unique (ofSplit q) (h g) hg⟩

theorem existsUnique_comp (h : ∀ g, (ofSplit q).IsLoc F (gl g) g) (x : GA D V) :
    ∃! g, x * (gl g)⁻¹ ∈ grpOff V (· = q.v) := by
  obtain ⟨p1, p2, p3⟩ := GlobalTheory.FinPlLoc.part_grp (· = q.v) V
  obtain ⟨a, ha, b, hb, rfl⟩ := p1 x
  have hab := p2 a ha b hb
  rw [← range_gl q h] at ha
  obtain ⟨g, rfl⟩ := ha
  have hg : gl g * b * (gl g)⁻¹ ∈ grpOff V (· = q.v) := by rwa [hab, mul_inv_cancel_right]
  refine ⟨g, hg, fun g' hg' => ?_⟩
  have h1 : gl g * (gl g')⁻¹ ∈ grpAt V (· = q.v) ⊓ grpOff V (· = q.v) := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (gl_mem q h g) (inv_mem (gl_mem q h g')), ?_⟩
    have e : gl g * (gl g')⁻¹ = (gl g * b * (gl g)⁻¹)⁻¹ * (gl g * b * (gl g')⁻¹) := by group
    rw [e]
    exact mul_mem (inv_mem hg) hg'
  rw [p3, Subgroup.mem_bot, mul_inv_eq_one] at h1
  exact ((isClosedEmbedding_gl q h).injective h1).symm

theorem mem_KO_iff (g : GL Y k) : g ∈ KO k Y ↔ (∀ i j, g.val i j ∈ 𝒪[k]) ∧ ∀ i j, (g⁻¹).val i j ∈ 𝒪[k] := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨fun i j => (u.val i j).2, fun i j => ((u⁻¹).val i j).2⟩
  · rintro ⟨h1, h2⟩
    have hi : Function.Injective (RingHom.mapMatrix (m := Y) (algebraMap 𝒪[k] k)) :=
      Matrix.map_injective Subtype.val_injective
    refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
    · rw [map_mul, map_one]; exact g.mul_inv
    · rw [map_mul, map_one]; exact g.inv_mul

theorem hermAt_eq (x y : Fin V.rank → AE D) : hermAt V x y = (fun i => cA D (y i)) ⬝ᵥ (gA V *ᵥ x) := by
  simp only [hermAt, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hermAt_unitary (g : GA D V) (x y : Fin V.rank → AE D) :
    hermAt V (Formalism.L2.Theta.mt V g *ᵥ x) (Formalism.L2.Theta.mt V g *ᵥ y) = hermAt V x y := by
  have h : (fun i => cA D ((Formalism.L2.Theta.mt V g *ᵥ y) i)) = (fun i => cA D (y i)) ᵥ* adj (Formalism.L2.Theta.mt V g) := by
    funext i
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, RingHom.map_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hermAt_eq, h, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, mt_unitary,
    hermAt_eq]

theorem hermAt_smul (a : AE D) (x y : Fin V.rank → AE D) : hermAt V (cA D a • x) y = hermAt V x (a • y) := by
  unfold hermAt
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, RingHom.map_mul]
  ring

theorem act_half (h : ∀ g, (ofSplit q).IsLoc F (gl g) g) (g : GL Y k) (y : Fin V.rank → AE D) :
    q.e • (Formalism.L2.Theta.mt V (gl g) *ᵥ y) = fun i => q.sec ((F.β *ᵥ (g.val *ᵥ (F.γ *ᵥ fun j => q.pr (y j)))) i) := by
  have h2 : (Formalism.L2.Theta.mt V (gl g)).map q.pr = F.β * g.val * F.γ := (h g).2
  funext i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← h2, Pi.smul_apply, smul_eq_mul, ← q.sec_pr]
  exact congrArg q.sec (RingHom.map_mulVec q.pr _ y i)

theorem act_sec (h : ∀ g, (ofSplit q).IsLoc F (gl g) g) (g : GL Y k) (z : Y → k) :
    Formalism.L2.Theta.mt V (gl g) *ᵥ (fun i => q.sec ((F.β *ᵥ z) i)) = fun i => q.sec ((F.β *ᵥ (g.val *ᵥ z)) i) := by
  have e : (fun i => q.sec ((F.β *ᵥ z) i)) = q.e • fun i => q.sec ((F.β *ᵥ z) i) :=
    funext fun i => (GlobalTheory.FinPl.LatIndHalf.e_mul_sec q _).symm
  rw [e, Matrix.mulVec_smul, act_half q h]
  simp only [q.pr_sec]
  change (fun i => q.sec ((F.β *ᵥ (g.val *ᵥ (F.γ *ᵥ (F.β *ᵥ z)))) i)) = _
  rw [Matrix.mulVec_mulVec z, F.γβ, Matrix.one_mulVec]

theorem mulVec_int {M : Matrix Y Y k} (hM : ∀ i j, M i j ∈ 𝒪[k]) {z : Y → k} (hz : ∀ i, z i ∈ 𝒪[k]) (i : Y) :
    (M *ᵥ z) i ∈ 𝒪[k] :=
  sum_mem fun j _ => mul_mem (hM i j) (hz j)

variable {L : Lat V}

theorem half_mem (h : ∀ g, (ofSplit q).IsLoc F (gl g) g)
    (hL : ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ latV V L (· = q.v))
    {g : GL Y k} (hg : g ∈ KO k Y) {y : Fin V.rank → AE D} (hy : y ∈ latV V L (· = q.v)) :
    q.e • (Formalism.L2.Theta.mt V (gl g) *ᵥ y) ∈ latV V L (· = q.v) := by
  have he : finPart D q.e ∈ intAE D := by
    rw [← GlobalTheory.FinPl.LatIndHalf.sec_one]; exact (q.int_iff 1).1 (one_mem _)
  rw [act_half q h]
  refine (hL _).1 (mulVec_int ((mem_KO_iff g).1 hg).1 ((hL _).2 ?_))
  rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
  simp only [q.sec_pr]
  exact GlobalTheory.FinPl.LatIndHalf.mul_mem_latV he hy

theorem act_mem (h : ∀ g, (ofSplit q).IsLoc F (gl g) g) (hsd : IsSelfDualC V L)
    (hL : ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ latV V L (· = q.v))
    {g : GL Y k} (hg : g ∈ KO k Y) {y : Fin V.rank → AE D} (hy : y ∈ latV V L (· = q.v)) :
    Formalism.L2.Theta.mt V (gl g) *ᵥ y ∈ latV V L (· = q.v) := by
  obtain ⟨s1, -, s2⟩ := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V L q.v hsd
  have hs := GlobalTheory.IwaPlace.mulVec_mem_idAt (Formalism.L2.Theta.mt V (gl g)) (s1 y hy)
  have e : Formalism.L2.Theta.mt V (gl g) *ᵥ y =
      q.e • (Formalism.L2.Theta.mt V (gl g) *ᵥ y) + cA D q.e • (Formalism.L2.Theta.mt V (gl g) *ᵥ y) := by
    rw [← add_smul, idem_eq]
    exact funext fun i => ((GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (hs i)).symm
  rw [e]
  refine add_mem (half_mem q h hL hg hy) ((s2 _ fun i => Ideal.mul_mem_left _ _ (hs i)).2 fun x hx => ?_)
  have e2 : q.e • x = Formalism.L2.Theta.mt V (gl g) *ᵥ (q.e • (Formalism.L2.Theta.mt V (gl g⁻¹) *ᵥ x)) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← GlobalTheory.MixModel.mt_mul, ← map_mul, mul_inv_cancel, map_one,
      GlobalTheory.MixModel.mt_one, Matrix.one_mulVec]
  change hermAt V (cA D q.e • (Formalism.L2.Theta.mt V (gl g) *ᵥ y)) x ∈ _
  rw [hermAt_smul, e2, hermAt_unitary]
  exact (s2 y (s1 y hy)).1 hy _ (half_mem q h hL (inv_mem hg) hx)

theorem mem_KO_iff_inK (h : ∀ g, (ofSplit q).IsLoc F (gl g) g) (hsd : IsSelfDualC V L)
    (hL : ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ latV V L (· = q.v))
    (g : GL Y k) : g ∈ KO k Y ↔ InK V L (· = q.v) (gl g) := by
  constructor
  · refine fun hg => ⟨gl_mem q h g, fun y _ => ⟨act_mem q h hsd hL hg, fun hy => ?_⟩⟩
    have := act_mem q h hsd hL (inv_mem hg) hy
    rwa [Matrix.mulVec_mulVec, ← GlobalTheory.MixModel.mt_mul, ← map_mul, inv_mul_cancel, map_one, GlobalTheory.MixModel.mt_one,
      Matrix.one_mulVec] at this
  · rintro ⟨-, hm⟩
    have key : ∀ z : Y → k, (∀ i, z i ∈ 𝒪[k]) ↔ ∀ i, (g.val *ᵥ z) i ∈ 𝒪[k] := fun z => by
      rw [hL, hL, ← act_sec q h]
      refine hm _ fun i => ?_
      rw [← GlobalTheory.FinPl.LatIndHalf.e_mul_sec]
      exact Ideal.mul_mem_right _ _ (GlobalTheory.FinPl.LatIndHalf.e_mem_idAt q)
    have hs : ∀ j i : Y, (Pi.single j 1 : Y → k) i ∈ 𝒪[k] := fun j i => by
      rw [Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    refine (mem_KO_iff g).2 ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa using (key _).1 (hs j) i
    · have := (key ((g⁻¹).val *ᵥ Pi.single j 1)).2 (by
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]; exact hs j) i
      rwa [Matrix.mulVec_single_one] at this

theorem local_group : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k V.rank Y) (gl : GL Y k →* GA D V), (∀ g, (ofSplit q).IsLoc F (gl g) g) → Topology.IsClosedEmbedding gl ∧ gl.range = GlobalTheory.FinPl.grpAt V (· = q.v) ∧ (∀ x : GA D V, ∃! g, x * (gl g)⁻¹ ∈ GlobalTheory.FinPl.grpOff V (· = q.v)) ∧ (∀ g, ∀ y ∈ GlobalTheory.FinPl.grpOff V (· = q.v), gl g * y = y * gl g) ∧ ∀ L : GlobalTheory.FinPl.Lat V, IsSelfDualC V L → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV V L (· = q.v)) → ∀ g, g ∈ KO k Y ↔ GlobalTheory.FinPl.InK V L (· = q.v) (gl g) := by
  intro D k _ _ _ _ q V Y _ _ F gl h
  exact ⟨isClosedEmbedding_gl q h, range_gl q h, existsUnique_comp q h,
    fun g y hy => (GlobalTheory.FinPlLoc.part_grp (· = q.v) V).2.1 _ (gl_mem q h g) y hy,
    fun L hsd hL => mem_KO_iff_inK q h hsd hL⟩

end GlobalTheory.LocGl

end
