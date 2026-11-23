import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceSplitsHyperbolicPlusCore
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPointWeilCharConductorOneOfUnits

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV MonoAt idAt intAt colMul Lat SplitPt Pl)
open GlobalTheory.IwaPlace GlobalTheory.IwaDecomp GlobalTheory.FinPl.FrameLat

noncomputable section
namespace GlobalTheory.JacMono

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem conj_herm (S : HSp D) (x y : Fin S.rank → AE D) : cA D (hermAt S x y) = hermAt S y x := by
  have hg : ∀ i j, cA D (gA S i j) = gA S j i := fun i j => congrFun (congrFun (adj_gA S) j) i
  simp only [hermAt, map_sum, RingHom.map_mul, cA_cA, hg]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem herm_smul_right (S : HSp D) (t : AE D) (x y : Fin S.rank → AE D) :
    hermAt S x (t • y) = cA D t * hermAt S x y := by
  rw [← conj_herm, hermAt_smul_left, RingHom.map_mul, conj_herm]

variable (q : SplitPt D k)

theorem conj_eps : cA D (q.e + cA D q.e) = q.e + cA D q.e := by rw [RingHom.map_add, cA_cA, add_comm]

theorem conj_idAt {a : AE D} (ha : a ∈ idAt D (· = q.v)) : cA D a ∈ idAt D (· = q.v) := by
  rw [idem_iff, ← conj_eps, ← RingHom.map_mul, (idem_iff q a).1 ha]

theorem conj_intAt {a : AE D} (ha : a ∈ intAt D (· = q.v)) : cA D a ∈ intAt D (· = q.v) :=
  ⟨conj_idAt q ha.1, (cA_int_iff a).2 ha.2⟩

theorem colMul_smul {m n : ℕ} (M : Mx D m n) (i : Fin n) (a b : AE D) : a • colMul M i b = colMul M i (a * b) := by
  funext r; simp only [colMul, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem colMul_add {m n : ℕ} (M : Mx D m n) (i : Fin n) (a b : AE D) :
    colMul M i (a + b) = colMul M i a + colMul M i b := by
  funext r; simp only [colMul, Pi.add_apply, add_mul]

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}

theorem line_eps (hL : IsSelfDualC S L) (M : Mx D S.rank ρ) (i : Fin ρ) (h1 : colMul M i q.e ∈ latV S L (· = q.v))
    (h2 : ∀ x ∈ latV S L (· = q.v), q.e * ((adj M * gA S) *ᵥ x) i ∈ intAt D (· = q.v)) :
    colMul M i (q.e + cA D q.e) ∈ latV S L (· = q.v) := by
  rw [colMul_add]
  refine add_mem h1 ?_
  refine ((LocSD.isSDAt_latV D S L q.v hL).2.2 (colMul M i (cA D q.e)) fun r => Ideal.mul_mem_right _ _ (conj_idAt q (e_mem_idAt q))).2 fun x hx => ?_
  rw [← conj_herm, hermAt_colMul, cA_cA]
  exact conj_intAt q (h2 x hx)

theorem line_mem (hL : IsSelfDualC S L) (M M' : Mx D S.rank ρ) (i : Fin ρ)
    (h1 : colMul M i (q.e + cA D q.e) ∈ latV S L (· = q.v)) (h2 : colMul M' i (q.e + cA D q.e) ∈ latV S L (· = q.v))
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = q.v)) :
    colMul M i (((adj M' * gA S) *ᵥ y) i) ∈ latV S L (· = q.v) := by
  have hs : ((adj M' * gA S) *ᵥ y) i ∈ idAt D (· = q.v) := mulVec_mem_idAt _ (latV_supp hy) i
  have h3 := ((LocSD.isSDAt_latV D S L q.v hL).2.2 y (latV_supp hy)).1 hy _ h2
  rw [hermAt_colMul, conj_eps, (idem_iff q _).1 hs] at h3
  have h4 := smul_mem hL h1 h3
  rwa [colMul_smul, mul_comm, (idem_iff q _).1 hs] at h4

theorem monoAt_of_half (hL : IsSelfDualC S L) (hL₀ : IsSelfDualC S₀ L₀)
    (hp : ∀ x ∈ latV S L (· = q.v), (∀ i, q.e * (d.pX *ᵥ x) i ∈ intAt D (· = q.v)) ∧
      (∀ i, q.e * (d.pY *ᵥ x) i ∈ intAt D (· = q.v)) ∧ q.e • (d.p0 *ᵥ x) ∈ latV S₀ L₀ (· = q.v))
    (hX : ∀ i, colMul d.jX i q.e ∈ latV S L (· = q.v)) (hY : ∀ i, colMul d.jY i q.e ∈ latV S L (· = q.v))
    (h0 : ∀ w ∈ latV S₀ L₀ (· = q.v), q.e • (d.j0 *ᵥ w) ∈ latV S L (· = q.v)) : MonoAt d L L₀ q.v := by
  have sd := (LocSD.isSDAt_latV D S L q.v hL).2.2
  have sd₀ := (LocSD.isSDAt_latV D S₀ L₀ q.v hL₀).2.2
  have hX' : ∀ i, colMul d.jX i (q.e + cA D q.e) ∈ latV S L (· = q.v) := fun i =>
    line_eps q hL d.jX i (hX i) fun x hx => by rw [← d.pY_eq]; exact (hp x hx).2.1 i
  have hY' : ∀ i, colMul d.jY i (q.e + cA D q.e) ∈ latV S L (· = q.v) := fun i =>
    line_eps q hL d.jY i (hY i) fun x hx => by rw [← d.pX_eq]; exact (hp x hx).1 i
  have h0' : ∀ w ∈ latV S₀ L₀ (· = q.v), d.j0 *ᵥ w ∈ latV S L (· = q.v) := by
    intro w hw
    have hs : ∀ r, (d.j0 *ᵥ w) r ∈ idAt D (· = q.v) := mulVec_mem_idAt _ (latV_supp hw)
    have e1 : d.j0 *ᵥ w = q.e • (d.j0 *ᵥ w) + cA D q.e • (d.j0 *ᵥ w) := by
      funext r
      rw [← add_smul, Pi.smul_apply, smul_eq_mul, (idem_iff q _).1 (hs r)]
    rw [e1]
    refine add_mem (h0 w hw) ((sd (cA D q.e • (d.j0 *ᵥ w)) fun r => Ideal.mul_mem_left _ _ (hs r)).2 fun x hx => ?_)
    rw [hermAt_smul_left, adelicHermitianForm_wittCoreInclusion_left, ← herm_smul_right]
    exact (sd₀ w (latV_supp hw)).1 hw _ (hp x hx).2.2
  intro y
  constructor
  · intro hy
    refine ⟨fun i => ?_, fun i => ?_, ?_⟩
    · rw [d.pX_eq]; exact line_mem q hL _ _ i (hX' i) (hY' i) hy
    · rw [d.pY_eq]; exact line_mem q hL _ _ i (hY' i) (hX' i) hy
    · refine (sd₀ _ (mulVec_mem_idAt _ (latV_supp hy))).2 fun w hw => ?_
      rw [← conj_herm, ← adelicHermitianForm_wittCoreInclusion_left, conj_herm]
      exact (sd y (latV_supp hy)).1 hy _ (h0' w hw)
  · rintro ⟨h1, h2, h3⟩
    rw [decomp_vec d y, mulVec_eq_sum_colMul d.jX, mulVec_eq_sum_colMul d.jY]
    exact add_mem (add_mem (sum_mem fun i _ => h1 i) (h0' _ h3)) (sum_mem fun i _ => h2 i)

section Frames

variable {Y Y₀ : Type} [Fintype Y] [DecidableEq Y] [Fintype Y₀] [DecidableEq Y₀]

def colAt {N : ℕ} (F : Frame k N Y) (c : Y) : Fin N → AE D := fun r => q.sec (F.β r c)

theorem colAt_mem {F : Frame k S.rank Y} (h : IntIn q S F L) (c : Y) : colAt q F c ∈ latV S L (· = q.v) := by
  have h1 := (h (Pi.single c 1)).1 fun i => by
    by_cases hi : i = c
    · subst hi; rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne hi]; exact zero_mem _
  rw [Matrix.mulVec_single_one] at h1
  exact h1

theorem expand (hL : IsSelfDualC S L) {F : Frame k S.rank Y} (h : IntIn q S F L) {x : Fin S.rank → AE D}
    (hx : x ∈ latV S L (· = q.v)) {m : ℕ} (M : Mx D m S.rank) :
    ∃ a : Y → AE D, (∀ c, a c ∈ intAt D (· = q.v)) ∧ q.e • (M *ᵥ x) = ∑ c, a c • (M *ᵥ colAt q F c) := by
  have h1 : F.β *ᵥ (F.γ *ᵥ fun r => q.pr (x r)) = fun r => q.pr (x r) := by
    rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
  have h2 : (fun r => q.sec ((F.β *ᵥ (F.γ *ᵥ fun r => q.pr (x r))) r)) = q.e • x := by
    rw [h1]; funext r; exact q.sec_pr _
  have h3 := (h (F.γ *ᵥ fun r => q.pr (x r))).2 (by rw [h2]; exact smul_mem hL hx (e_mem_intAt q))
  refine ⟨fun c => q.sec ((F.γ *ᵥ fun r => q.pr (x r)) c), fun c => sec_mem_intAt q _ (h3 c), ?_⟩
  simp only [← Matrix.mulVec_smul]
  rw [← Matrix.mulVec_sum, ← h2]
  congr 1
  generalize (F.γ *ᵥ fun r => q.pr (x r)) = y
  funext r
  simp only [Matrix.mulVec, dotProduct, map_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, colAt, sec_mul]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem mulVec_colMul {l m n : ℕ} (M : Mx D l m) (N : Mx D m n) (i : Fin n) (a : AE D) :
    M *ᵥ colMul N i a = colMul (M * N) i a := by
  funext r
  simp only [colMul, Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem colMul_zero {m n : ℕ} (i : Fin n) (a : AE D) : colMul (0 : Mx D m n) i a = 0 := by
  funext r; simp only [colMul, Matrix.zero_apply, mul_zero, Pi.zero_apply]

theorem colMul_one {n : ℕ} {v : Pl D} (i j : Fin n) {a : AE D} (ha : a ∈ intAt D (· = v)) :
    colMul (1 : Mx D n n) i a j ∈ intAt D (· = v) := by
  simp only [colMul, Matrix.one_apply]
  split_ifs
  · rwa [mul_one]
  · rw [mul_zero]; exact intAt_zero'

theorem unit_line (hL : IsSelfDualC S L) (M : Mx D S.rank ρ) (i : Fin ρ) {t : k} (ht : valuation k t = 1)
    (h : colMul M i (q.sec t) ∈ latV S L (· = q.v)) : colMul M i q.e ∈ latV S L (· = q.v) := by
  have h0 : t ≠ 0 := fun h => by rw [h, map_zero] at ht; exact zero_ne_one ht
  have h1 : t⁻¹ ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 (by rw [map_inv₀, ht, inv_one])
  have h2 := smul_mem hL h (sec_mem_intAt q _ h1)
  rwa [colMul_smul, ← sec_mul, inv_mul_cancel₀ h0, sec_one] at h2

theorem monoAt_of_cols (hL : IsSelfDualC S L) (hL₀ : IsSelfDualC S₀ L₀) {F : Frame k S.rank Y} {F₀ : Frame k S₀.rank Y₀}
    (h : IntIn q S F L) (h₀ : IntIn q S₀ F₀ L₀)
    (cover : ∀ c, (∃ a, colAt q F c = d.j0 *ᵥ colAt q F₀ a) ∨
      (∃ i t, valuation k t = 1 ∧ colAt q F c = colMul d.jX i (q.sec t)) ∨
      ∃ i t, valuation k t = 1 ∧ colAt q F c = colMul d.jY i (q.sec t))
    (c0 : ∀ a, ∃ c, colAt q F c = d.j0 *ᵥ colAt q F₀ a)
    (cX : ∀ i, ∃ c t, valuation k t = 1 ∧ colAt q F c = colMul d.jX i (q.sec t))
    (cY : ∀ i, ∃ c t, valuation k t = 1 ∧ colAt q F c = colMul d.jY i (q.sec t)) : MonoAt d L L₀ q.v := by
  have hu : ∀ t : k, valuation k t = 1 → q.sec t ∈ intAt D (· = q.v) := fun t ht =>
    sec_mem_intAt q t ((Valuation.mem_integer_iff _ _).2 ht.le)
  have hc : ∀ c, (∀ i, (d.pX *ᵥ colAt q F c) i ∈ intAt D (· = q.v)) ∧ (∀ i, (d.pY *ᵥ colAt q F c) i ∈ intAt D (· = q.v)) ∧
      d.p0 *ᵥ colAt q F c ∈ latV S₀ L₀ (· = q.v) := by
    intro c
    rcases cover c with ⟨a, e⟩ | ⟨i, t, ht, e⟩ | ⟨i, t, ht, e⟩ <;> rw [e]
    · simp only [Matrix.mulVec_mulVec]
      rw [d.pX_j0, d.pY_j0, d.p0_j0, Matrix.zero_mulVec, Matrix.one_mulVec]
      exact ⟨fun _ => intAt_zero', fun _ => intAt_zero', colAt_mem q h₀ a⟩
    · simp only [mulVec_colMul]
      rw [d.pX_jX, d.pY_jX, d.p0_jX, colMul_zero, colMul_zero]
      exact ⟨fun _ => colMul_one _ _ (hu t ht), fun _ => intAt_zero', zero_mem _⟩
    · simp only [mulVec_colMul]
      rw [d.pX_jY, d.pY_jY, d.p0_jY, colMul_zero, colMul_zero]
      exact ⟨fun _ => intAt_zero', fun _ => colMul_one _ _ (hu t ht), zero_mem _⟩
  refine monoAt_of_half q d hL hL₀ (fun x hx => ⟨fun i => ?_, fun i => ?_, ?_⟩) (fun i => ?_) (fun i => ?_) fun w hw => ?_
  · obtain ⟨a, ha, e⟩ := expand q hL h hx d.pX
    have e' := congrFun e i
    rw [Finset.sum_apply] at e'
    change q.e * _ = _ at e'
    rw [e']
    exact intAt_sum' _ _ fun c _ => intAt_mul' (ha c) ((hc c).1 i)
  · obtain ⟨a, ha, e⟩ := expand q hL h hx d.pY
    have e' := congrFun e i
    rw [Finset.sum_apply] at e'
    change q.e * _ = _ at e'
    rw [e']
    exact intAt_sum' _ _ fun c _ => intAt_mul' (ha c) ((hc c).2.1 i)
  · obtain ⟨a, ha, e⟩ := expand q hL h hx d.p0
    rw [e]
    exact sum_mem fun c _ => smul_mem hL₀ (hc c).2.2 (ha c)
  · obtain ⟨c, t, ht, e⟩ := cX i
    exact unit_line q hL _ i ht (e ▸ colAt_mem q h c)
  · obtain ⟨c, t, ht, e⟩ := cY i
    exact unit_line q hL _ i ht (e ▸ colAt_mem q h c)
  · obtain ⟨a, ha, e⟩ := expand q hL₀ h₀ hw d.j0
    rw [e]
    refine sum_mem fun c _ => smul_mem hL ?_ (ha c)
    obtain ⟨c', e'⟩ := c0 c
    exact e' ▸ colAt_mem q h c'

theorem colAt_line {N n : ℕ} {F : Frame k N Y} {c : Y} (M : Matrix (Fin N) (Fin n) D.host.E) (i : Fin n) {t : k}
    (h : ∀ r, F.β r c = t * (ofSplit q).pr (M r i)) : colAt q F c = colMul (rat M) i (q.sec t) := by
  funext r
  change q.sec (F.β r c) = q.sec t * incA D (M r i)
  rw [h, sec_mul_right]; rfl

theorem colAt_core {N n : ℕ} {F : Frame k N Y} {F₀ : Frame k n Y₀} {c : Y} (M : Matrix (Fin N) (Fin n) D.host.E) (a : Y₀)
    (h : ∀ r, F.β r c = (M.map (ofSplit q).pr * F₀.β) r a) : colAt q F c = (rat M : Mx D N n) *ᵥ colAt q F₀ a := by
  funext r
  change q.sec (F.β r c) = ∑ l, incA D (M r l) * q.sec (F₀.β l a)
  rw [h, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm (incA D _), sec_mul_right, mul_comm]; rfl

theorem monoAt_of_jacFrame (hU : q.UnitAA) (J : JacLev D ρ) {L : Lat J.W} {L₀ : Lat J.W₀} (hL : IsSelfDualC J.W L)
    (hL₀ : IsSelfDualC J.W₀ L₀) {c : ℕ} {F : Frame k J.W.rank (Y₀ ⊕ Fin c)} {F₀ : Frame k J.W₀.rank Y₀} {s hh : k}
    (hs : valuation k s = 1) (hz : valuation k hh = 1) (hF : (ofSplit q).IsJacFrame J s hh F₀ F)
    (h : IntIn q J.W F L) (h₀ : IntIn q J.W₀ F₀ L₀) : MonoAt J.d L L₀ q.v := by
  have hξ : valuation k (ofSplit q).xi = 1 := GlobalTheory.SplitWeilChar.valuation_pr_incA_xi0_eq_one_of_unitAA q hU
  obtain ⟨rfl, h1, h2, h3⟩ := hF
  have hX : ∀ (i : Fin ρ) (j : Fin (2 * ρ)), j.val = i.val →
      ∃ t, valuation k t = 1 ∧ colAt q F (Sum.inr j) = colMul J.d.jX i (q.sec t) := fun i j hj =>
    ⟨_, by rw [map_mul, map_pow, hs, hξ, one_pow, one_mul], colAt_line q J.d.e i (h2 i j hj)⟩
  have hY : ∀ (i : Fin ρ) (j : Fin (2 * ρ)), j.val + i.val + 1 = 2 * ρ →
      ∃ t, valuation k t = 1 ∧ colAt q F (Sum.inr j) = colMul J.d.jY i (q.sec t) := fun i j hj =>
    ⟨_, by rw [map_mul, map_mul, map_pow, map_div₀, map_div₀, Valuation.map_neg, map_one, hs, hz, hξ]; simp,
      colAt_line q J.d.e' i (h3 i j hj)⟩
  refine monoAt_of_cols q J.d hL hL₀ h h₀ ?_ (fun a => ⟨Sum.inl a, colAt_core q J.d.i₀ a fun r => h1 r a⟩)
    (fun i => ⟨Sum.inr ⟨i.val, by omega⟩, hX i _ rfl⟩)
    (fun i => ⟨Sum.inr ⟨2 * ρ - 1 - i.val, by omega⟩, hY i _ (by change 2 * ρ - 1 - i.val + i.val + 1 = _; omega)⟩)
  rintro (a | j)
  · exact Or.inl ⟨a, colAt_core q J.d.i₀ a fun r => h1 r a⟩
  · by_cases hj : j.val < ρ
    · exact Or.inr (Or.inl ⟨⟨j.val, hj⟩, hX _ j rfl⟩)
    · exact Or.inr (Or.inr ⟨⟨2 * ρ - 1 - j.val, by omega⟩, hY _ j (by change j.val + (2 * ρ - 1 - j.val) + 1 = _; omega)⟩)

end Frames

theorem monoAt_jacLevel : ∀ (D : D7) (c : Comm D) (v : VCom c) (k₀ : Type) [Field k₀] [ValuativeRel k₀] [TopologicalSpace k₀] [IsNonarchimedeanLocalField k₀] (ι : Type) (o : TDat c k₀ ι) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (ψk : AddChar k Circle) (s : ℕ) (hs : s + 1 + 1 = D.R.m) (X : ℕ → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] (Z : Type) [Fintype Z] [DecidableEq Z] (FX : ∀ j, j ≤ s + 1 → Frame k (c.X j).rank (X j)) (FT : Frame k c.T.rank Z) (FM : Frame k (c.X (s + 1 + 1)).rank (Z ⊕ Unit)) (FY : ∀ j d, j + d = s + 1 → Frame k (c.V j).rank (X j ⊕ Fin d)) (sc : ℕ → k) (z₀ : Fin c.Lz.rank → k), c.Is → q.UnitAA → (ofSplit q).IsChar c.ψ ψk → HasConductor ψk 1 → (∀ j, valuation k (sc j) = 1) → (∀ j, sc (j + 1 + 1) = sc j * (ofSplit q).xi) → (∀ j ρ h, valuation k ((ofSplit q).hz (c.B j ρ h)) = 1) → (∀ j ρ h d (hd : j + d = s + 1), (ofSplit q).IsBesFrame (c.B j ρ h) (sc j) (FX j (by omega)) (FY j d hd)) → (∀ j ρ h d (hd : j + 1 + d = s + 1), (ofSplit q).IsJacFrame (c.J j ρ h) (sc j) ((ofSplit q).hz (c.B j ρ h)) (FX (j + 1) (by omega)) (FY (j + 1) d hd)) → FM.β = fromCols ((c.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr * FT.β) (Matrix.of fun r _ => ((c.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀) r) → (∀ h, (v.τ s h).map (ofSplit q).pr *ᵥ z₀ = (-((ofSplit q).xi * sc s)) • fun i => (ofSplit q).pr ((c.bes s 0 h).ζ i)) → (∀ j h, (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram) → (∀ j hj, IntIn q (c.X j) (FX j hj) (c.x j).L) → IntIn q (c.X (s + 1 + 1)) FM (c.x (s + 1 + 1)).L → IntIn q c.T FT v.NT → IsSelfDualC c.T v.NT → (∀ j d hd, IsSelfDualC (c.V j) (v.N j) ∧ IntIn q (c.V j) (FY j d hd) (v.N j)) → (∀ j ρ h (hj : j ≤ s + 1), IsSelfDualC (c.bes j ρ h).V₀ (o.M j ρ h) ∧ ∃ F₀, (ofSplit q).IsCoreFrame (c.B j ρ h) (sc j) (FX j hj) F₀ ∧ IntIn q (c.bes j ρ h).V₀ F₀ (o.M j ρ h)) → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.MonoAt (c.J j ρ h).d (v.N (j + 1)) (c.x (j + 1)).L q.v := by
  intro D c v k₀ _ _ _ _ ι o k _ _ _ _ q ψk s hs X _ _ Z _ _ FX FT FM FY sc z₀ h1 h2 _ _ h5 _ h7 _ h9 _ _ _ h13 _ _ _ h17 _ j ρ h
  have hd : j + 1 + 2 * ρ = s + 1 := by omega
  exact monoAt_of_jacFrame q h2 (c.J j ρ h) (h17 (j + 1) _ hd).1 (h1.x (j + 1) (by omega)).sd (h5 j) (h7 j ρ h)
    (h9 j ρ h _ hd) (h17 (j + 1) _ hd).2 (h13 (j + 1) (by omega))

end GlobalTheory.JacMono
