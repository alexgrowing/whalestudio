import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntOfKeeps
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmulOfMemFlagSubOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartTraceCharacterIdempotentInverseDiffere

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Matrix ValuativeRel IsLocalRing
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.FinPlLoc GlobalTheory.IwaPlace NumberField Filter
open GlobalTheory.GoodPos
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.MiTop.Scale.Glue

open GlobalTheory.FinPl.FrameLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_mem_of_intAt (p : SplitPt D k) {a : AE D} (ha : finPart D a ∈ intAE D) : p.pr a ∈ 𝒪[k] := by
  rw [p.int_iff, p.sec_pr, RingHom.map_mul]
  exact mul_mem_intAE (e_mem_intAt p).2 ha

theorem eq_sec_add (p : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = p.v)) :
    a = p.sec (p.pr a) + cA D (p.sec (p.pr (cA D a))) := by
  rw [p.sec_pr, p.sec_pr, RingHom.map_mul, cA_cA, ← add_mul, (idem_iff p a).1 ha]

theorem mem_intAt_iff (p : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = p.v)) :
    a ∈ intAt D (· = p.v) ↔ p.pr a ∈ 𝒪[k] ∧ p.pr (cA D a) ∈ 𝒪[k] := by
  refine ⟨fun h => ⟨pr_mem_of_intAt p h.2, pr_mem_of_intAt p ((cA_int_iff a).2 h.2)⟩, fun h => ⟨ha, ?_⟩⟩
  rw [eq_sec_add p ha, RingHom.map_add]
  exact add_mem ((p.int_iff _).1 h.1) ((cA_int_iff _).2 ((p.int_iff _).1 h.2))

theorem single_mem_glued_iff {n : Type} [DecidableEq n] (q : Unif k) (P : Pair k n) (t : k) :
    (Pi.single (Sum.inr 0) t : n ⊕ Fin 1 → k) ∈ gluedS q 1 P.ker P.vec ↔ t ∈ 𝒪[k] := by
  have h0 : (Pi.single (Sum.inr 0) t : n ⊕ Fin 1 → k) ∘ Sum.inl = 0 := by
    funext j
    simp
  rw [GlobalTheory.LevelUnfold.mem_gluedS, h0]
  constructor
  · rintro ⟨s, h1, h2⟩
    have h3 := (h2 0).1 rfl
    rw [Pi.single_eq_same] at h3
    rw [zero_sub, neg_mem_iff, Pair.mem_ker] at h1
    have h4 := (P.hasVal_vec.smul s).unique h1
    rw [mul_one, IsLocalRing.residue_eq_zero_iff, q.mem_max_iff] at h4
    obtain ⟨c, rfl⟩ := h4
    rw [h3, Unif.inv, Subring.coe_mul, ← mul_assoc, inv_mul_cancel₀ q.ne_zero, one_mul]
    exact c.2
  · intro ht
    refine ⟨q.1 * ⟨t, ht⟩, ?_, fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩
    · rw [zero_sub]
      exact neg_mem (Pair.smul_mem_ker (Ideal.mul_mem_right _ _ q.mem_max) P.hasVal_vec.mem)
    · obtain rfl : i = 0 := Subsingleton.elim _ _
      rw [Pi.single_eq_same, Unif.inv, Subring.coe_mul, ← mul_assoc, inv_mul_cancel₀ q.ne_zero, one_mul]

theorem pair_sumFrame {p : SplitPt D k} {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) {n : Type} [Fintype n]
    [DecidableEq n] {β : Frame p A n} {β₀ : Frame p S (n ⊕ Fin 1)} (hs : IsSumFrame o ζ β β₀) (x : n ⊕ Fin 1 → k) (t : k) :
    ∑ i, ∑ j, (β₀.b *ᵥ x) i * p.pr (cA D (incA D (S.gram i j))) * (t * p.pr (incA D (star (vecB o ζ j)))) =
      t * (p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)) * x (Sum.inr 0)) := by
  let f : D.host.E →+* k := p.pr.comp (incA D)
  let r : Fin S.rank → D.host.E := star (vecB o ζ) ᵥ* S.gram
  have hr : ∀ i, r i = ∑ j, star (S.gram i j) * star (vecB o ζ j) := fun i => by
    simp only [r, vecMul, dotProduct, Pi.star_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm, ← conjTranspose_apply, gram_conjTranspose]
  have h1 : ∑ i, ∑ j, (β₀.b *ᵥ x) i * p.pr (cA D (incA D (S.gram i j))) * (t * p.pr (incA D (star (vecB o ζ j)))) =
      t * ((f ∘ r) ⬝ᵥ β₀.b *ᵥ x) := by
    simp only [dotProduct, Function.comp_apply, hr, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    change _ * f (star (S.gram i j)) * (t * f (star (vecB o ζ j))) = _
    ring
  have hA : r ᵥ* o.iA = 0 := by
    simp only [r, vecB, star_mulVec, vecMul_vecMul, o.orth, vecMul_zero]
  have hB : r ⬝ᵥ vecB o ζ = star ζ ⬝ᵥ L.gram *ᵥ ζ := by
    rw [← o.isoB]
    simp only [r, vecB, star_mulVec, vecMul_vecMul, dotProduct_mulVec]
  have hA' : (f ∘ r) ᵥ* o.jA.map p.pr = 0 := by
    funext i
    have := RingHom.map_vecMul f o.iA r i
    rw [hA, Pi.zero_apply, map_zero] at this
    exact this.symm
  have hB' : (f ∘ r) ⬝ᵥ (fun i => p.pr (ratV (vecB o ζ) i)) = p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)) := by
    rw [← hB]
    exact (RingHom.map_dotProduct f r (vecB o ζ)).symm
  rw [h1, hs, dotProduct_mulVec, vecMul_fromCols, ← vecMul_vecMul, hA', zero_vecMul, ← hB']
  congr 1
  simp [dotProduct, vecMul, Fintype.sum_sum_type]

theorem line_of_glued {p : SplitPt D k} {ρ : ℕ} {B : BesLev D ρ} {M : Lat B.V₀} {q : Unif k} {n : Type} [Fintype n] [DecidableEq n]
    {β : Frame p B.A n} {β₀ : Frame p B.V₀ (n ⊕ Fin 1)} {P : Pair k n} (hM : IsSelfDualC B.V₀ M) (hg : GluedCore B M q β β₀ P)
    {a : AE D} (ha : a ∈ idAt D (· = p.v)) :
    a • ratV (vecB B.o B.ζ) ∈ latV B.V₀ M (· = p.v) ↔ a ∈ intAt D (· = p.v) := by
  have hdec : a • ratV (vecB B.o B.ζ) = (fun i => p.sec ((β₀.b *ᵥ (Pi.single (Sum.inr 0) (p.pr a) : n ⊕ Fin 1 → k)) i)) +
      fun i => cA D (p.sec (p.pr (cA D a) * p.pr (incA D (star (vecB B.o B.ζ i))))) := by
    funext i
    have e := eq_sec_add p (Ideal.mul_mem_right (incA D (vecB B.o B.ζ i)) _ ha)
    rw [RingHom.map_mul, RingHom.map_mul (cA D), RingHom.map_mul, cA_incA] at e
    refine e.trans ?_
    rw [Pi.add_apply, mulVec_single, hg.sum]
    congr 2
    exact mul_comm _ _
  have hq : valuation k ((q.1 : 𝒪[k]) : k) ≠ 0 := by simpa using q.ne_zero
  have hu : valuation k (p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)) * q.inv) = 1 := by
    rw [map_mul, hg.norm, Unif.inv, map_inv₀, mul_inv_cancel₀ hq]
  rw [hdec, decomp hM, ← hg.lat, single_mem_glued_iff, mem_intAt_iff p ha, csec_mem_iff hM]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h x hx => ?_⟩
  · have h1 := h _ ((hg.lat _).1 (GlobalTheory.LevelUnfold.mem_gluedS.2 ⟨1, (by simp : Sum.elim P.vec (fun _ => q.inv) ∘ Sum.inl - (1 : 𝒪[k]) • P.vec ∈ P.ker),
      fun i => ⟨fun _ => by simp, fun hi => absurd hi (by omega)⟩⟩))
    rw [pair_sumFrame B.o B.ζ hg.sum, Sum.elim_inr, Valuation.mem_integer_iff, map_mul, hu, mul_one] at h1
    exact h1
  · have hx' : x = β₀.b *ᵥ (β₀.b' *ᵥ x) := by rw [mulVec_mulVec, β₀.bb', one_mulVec]
    rw [hx'] at hx
    obtain ⟨s, -, hs⟩ := GlobalTheory.LevelUnfold.mem_gluedS.1 ((hg.lat _).2 hx)
    rw [hx', pair_sumFrame B.o B.ζ hg.sum, (hs 0).1 rfl, ← mul_assoc _ q.inv]
    exact mul_mem h (mul_mem ((Valuation.mem_integer_iff _ _).2 hu.le) s.2)

end GlobalTheory.MiTop.Scale.Glue

namespace GlobalTheory.MiTop.Scale

variable {D : D7}

theorem isU_of_val {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    {t : D.host.E} (h : valuation k (p.pr (incA D t)) = 1) (h' : valuation k (p.pr (incA D (star t))) = 1) : IsU p.v (incA D t) := by
  intro a ha
  rw [Glue.mem_intAt_iff p ha, Glue.mem_intAt_iff p (Ideal.mul_mem_left _ _ ha), RingHom.map_mul (cA D),
    FrameLat.cA_incA]
  simp only [Valuation.mem_integer_iff, map_mul, h, h', one_mul]

theorem prim_line {ψ : AddChar (AF D.host.F) ℂ} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} (hL : IsSelfDualC S L) {x : Pl D}
    (hp : PrimAt ψ d L x) {cc b : (AE D)ˣ} (hψ : ∀ s ∈ idAt D (· = x), (∀ o ∈ intAt D (· = x), psiE ψ (s * o) = 1) ↔
      ((cc⁻¹ : (AE D)ˣ) : AE D) * s ∈ intAt D (· = x)) {i j : Fin ρ} (hij : j.1 = i.1 + 1)
    (hj : ∀ a ∈ idAt D (· = x), colMul d.jX j a ∈ latV S L (· = x) ↔ ((b⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) :
    ∀ a ∈ idAt D (· = x), colMul d.jX i a ∈ latV S L (· = x) ↔ (((cc * b)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := fun a ha => by
  have he := idem_mem_intAt (D := D) (· = x)
  have hs := Ideal.mul_mem_left _ ((b⁻¹ : (AE D)ˣ) : AE D) ha
  rw [mul_inv, Units.val_mul, mul_assoc, ← hψ _ hs, ← hp i j hij _ hs]
  refine ⟨fun h t ht => ?_, fun h => ?_⟩
  · have := GlobalTheory.IwaPlace.SDStable.smul_mem D S x _ (LocSD.isSDAt_latV D S L x hL) _ ((hj t (colMul_id d j (latV_idAt ht))).1 ht) _ h
    rwa [smul_colMul, mul_right_comm] at this
  · have := h _ ((hj _ (Ideal.mul_mem_left _ (b : AE D) he.1)).2 (by rwa [Units.inv_mul_cancel_left]))
    rwa [mul_mul_mul_comm, Units.inv_mul, one_mul, mul_comm, (mem_idAt_iff _ a).1 ha] at this

theorem iso_step {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ}
    {LV : Lat B.V} {LV₀ : Lat B.V₀} {LW : Lat J.W} {LW₀ : Lat J.W₀} {LV' : Lat B'.V} {LV₀' : Lat B'.V₀} {x : Pl D} {α m cc : (AE D)ˣ}
    (hα : ∀ (S : HSp D) (L : Lat S) y, y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x))
    (hψ : ∀ s ∈ idAt D (· = x), (∀ o ∈ intAt D (· = x), psiE ψ (s * o) = 1) ↔ ((cc⁻¹ : (AE D)ˣ) : AE D) * s ∈ intAt D (· = x))
    (h₁ : GoodBF ψ B J LV LV₀ LW LW₀ x) (h₂ : AdaptFB ψ J B' LW LW₀ LV' LV₀' x)
    (hz : ∀ a ∈ idAt D (· = x), a • ratV (vecB B'.o B'.ζ) ∈ latV B'.V₀ LV₀' (· = x) ↔
      ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) (n : ℕ) :
    ∀ i : Fin (σ + 1), i.1 + n = σ → ∀ a ∈ idAt D (· = x), colMul B.d.jX i a ∈ latV B.V LV (· = x) ↔
      (((cc ^ n * (α * (α * m)))⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  induction n with
  | zero =>
    intro i hi a ha
    obtain rfl : i = Fin.last σ := Fin.ext hi
    have e : ∀ t : AE D, colMul (xLast B'.d (vecB B'.o B'.ζ)) (Fin.last σ) t = B'.d.j0 *ᵥ (t • ratV (vecB B'.o B'.ζ)) := fun t => by
      funext k
      simp only [colMul, xLast, Matrix.of_apply, Fin.snoc_last, mulVec_smul, Pi.smul_apply, smul_eq_mul]
    have e0 : ∀ (M : Mx D B'.V.rank σ) i, colMul M i 0 = 0 := fun M i => funext fun k => zero_mul _
    have ha' := Ideal.mul_mem_left _ ((α⁻¹ : (AE D)ˣ) : AE D) ha
    rw [h₁.cols _ a ha, hα, smul_colMul, xZero, h₂.cols _ _ ha', hα, smul_colMul, e, h₂.monoW, mulVec_mulVec, mulVec_mulVec,
      mulVec_mulVec, B'.d.pX_j0, B'.d.pY_j0, B'.d.p0_j0, zero_mulVec, one_mulVec, hz _ (Ideal.mul_mem_left _ _ ha'), pow_zero, one_mul,
      mul_inv, mul_inv, Units.val_mul, Units.val_mul]
    simp only [Pi.zero_apply, e0, zero_mem, implies_true, true_and]
    exact iff_of_eq (congrArg (· ∈ _) (by ring))
  | succ n ih =>
    intro i hi
    rw [pow_succ', mul_assoc]
    exact prim_line B.d h₁.sdV h₁.prim hψ (j := ⟨i.1 + 1, by omega⟩) rfl (ih _ (by simp only; omega))

section Com

variable {c : Comm D} {v : VCom c} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type} {o : TDat c k ι}

theorem core_line_all (hc : c.Is) (hs : ShapeOff v o) (hp : TopPrim v o) (hr : ∀ j, j + 2 * 0 + 2 = D.R.m → 0 < (c.X (j + 1)).rank)
    {lam : D.host.E} (hlam : lam ≠ 0) (hτ : ∀ j h, v.τ j h *ᵥ o.ζ₀ = lam • (c.bes j 0 h).ζ) {x : Pl D} {α : (AE D)ˣ}
    (hα : ∀ (S : HSp D) (L : Lat S) y, y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x)) (ρ j : ℕ)
    (h : j + 2 * ρ + 2 = D.R.m) : ∀ a ∈ idAt D (· = x),
      a • ratV (vecB (c.bes j ρ h).o (c.bes j ρ h).ζ) ∈ latV (c.bes j ρ h).V₀ (o.M j ρ h) (· = x) ↔
        ((((α * (xiU D * cU α)⁻¹) ^ (ρ + 1) * inU lam hlam)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  by_cases hx : x ∈ v.tP
  swap
  · exact core_line hc hs hp hr hlam hτ hx hα ρ j h
  obtain ⟨i, rfl⟩ := (hs.pre.tP x).1 hx
  intro a ha
  have hU := (hs.pre.char i).2
  obtain ⟨l, h1, h2⟩ := hs.pre.lam (j + 2 * ρ) h
  obtain ⟨r, -, hr0⟩ := line_coord (c.bes (j + 2 * ρ) 0 h).line
  obtain rfl : lam = l := mul_right_cancel₀ hr0 (congrFun ((hτ _ h).symm.trans h1) r)
  have u1 := isU_alpha hU hs.pre.line hα
  have u2 : IsU (o.p i).v ((xiU D * cU α : (AE D)ˣ) : AE D) := (isU_xi hU).mul u1.conj
  have u3 : IsU (o.p i).v ((α * (xiU D * cU α)⁻¹ : (AE D)ˣ) : AE D) := u1.mul (u2.inv (Units.mul_inv _))
  have u4 : IsU (o.p i).v (((α * (xiU D * cU α)⁻¹) ^ (ρ + 1) * inU lam hlam : (AE D)ˣ) : AE D) := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val]
    exact (u3.pow _).mul (isU_of_val _ (h2 i).1 (h2 i).2)
  exact (Glue.line_of_glued ((hs.good (o.p i).v).bf j ρ h).sdV₀ (hs.glued j ρ h i) ha).trans
    (u4.inv (Units.mul_inv _) a ha)

theorem iso_line_all (hc : c.Is) (hs : ShapeOff v o) (hp : TopPrim v o) (hr : ∀ j, j + 2 * 0 + 2 = D.R.m → 0 < (c.X (j + 1)).rank)
    {lam : D.host.E} (hlam : lam ≠ 0) (hτ : ∀ j h, v.τ j h *ᵥ o.ζ₀ = lam • (c.bes j 0 h).ζ) {x : Pl D} {α : (AE D)ˣ}
    (hα : ∀ (S : HSp D) (L : Lat S) y, y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x))
    (hψ : ∀ s ∈ idAt D (· = x), (∀ o ∈ intAt D (· = x), psiE c.ψ (s * o) = 1) ↔
      (((xiU D * α * cU α)⁻¹ : (AE D)ˣ) : AE D) * s ∈ intAt D (· = x)) (ρ j : ℕ) (h : j + 2 * ρ + 2 = D.R.m) (i : Fin ρ) :
    ∀ a ∈ idAt D (· = x), colMul (c.bes j ρ h).d.jX i a ∈ latV (c.V j) (v.N j) (· = x) ↔
      ((((xiU D * α * cU α) ^ (ρ - i.1) * ((α * (xiU D * cU α)⁻¹) ^ (ρ + 1) * inU lam hlam))⁻¹ : (AE D)ˣ) : AE D) * a ∈
        intAt D (· = x) := by
  obtain ⟨σ, rfl⟩ : ∃ σ, ρ = σ + 1 := ⟨ρ - 1, by have := i.2; omega⟩
  have hi := i.2
  have e : (xiU D * α * cU α) ^ (σ + 1 - i.1) * ((α * (xiU D * cU α)⁻¹) ^ (σ + 1 + 1) * inU lam hlam) =
      (xiU D * α * cU α) ^ (σ - i.1) * (α * (α * ((α * (xiU D * cU α)⁻¹) ^ (σ + 1) * inU lam hlam))) := by
    rw [show σ + 1 - i.1 = σ - i.1 + 1 by omega, pow_succ _ (σ - i.1), pow_succ' _ (σ + 1), mul_right_comm (xiU D) α]
    generalize xiU D * cU α = t
    generalize (α * t⁻¹) ^ (σ + 1) = w
    rw [mul_assoc, mul_assoc (α * t⁻¹), mul_comm t α, mul_comm α t⁻¹, mul_assoc α t, mul_assoc t⁻¹, mul_inv_cancel_left]
  rw [e]
  exact iso_step hα hψ ((hs.good x).bf j (σ + 1) h) ((hs.good x).fb j σ h) (core_line_all hc hs hp hr hlam hτ hα σ _ (idx_step h))
    (σ - i.1) i (by omega)

end Com

end GlobalTheory.MiTop.Scale

namespace GlobalTheory.MiTop

open Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links GlobalTheory.MiS GlobalTheory.Core.Mi GlobalTheory.Fam GlobalTheory.MiTop.Scale

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} {f : FamCh W u}
  {B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)}

theorem topPrim_iff {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    (v : VCom c) (o : TDat c k ι) : TopPrim v o ↔ PrimTop (c := c) v.tP o.ζ₀ :=
  ⟨fun h => h _ rfl, fun h _ e => by subst e; exact h⟩

theorem placedPrim_iff : PlacedPrim f B ↔ PlacedP f B := by
  unfold PlacedPrim PlacedP
  simp only [topPrim_iff]

theorem two_rS (D : D7) : 0 + 2 * D.R.rS + 2 = D.R.m := by
  have := D.R.two_le_m
  obtain ⟨c, hc⟩ := D.R.m_even
  unfold Ranks.rS
  omega

theorem rank_pos (f : FamCh W u) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) : 0 < (f.c.X (j + 1)).rank := by
  refine lt_of_lt_of_eq ?_ (Formalism.L2.Forms.rankN D (j + 1) (by omega)).symm
  unfold Ranks.N
  positivity

theorem mem_moved {v : VCom f.c} (ht : VTie f v) {x : GlobalTheory.FinPl.Pl D} (hg : ∀ PP ∈ (pk W).Pg, x ≠ PP.under (𝓞 D.host.F))
    {y : Fin (Yc D 0).rank → AE D} (hy : ∀ i, y i ∈ idAt D (· = x)) :
    mt (Yc D 0) (f.g.b 0)⁻¹ *ᵥ y ∈ latV (Yc D 0) ((pk W).ΛY 0) (· = x) ↔ y ∈ latV (Yc D 0) (v.N 0) (· = x) := by
  have h0 := two_rS D
  refine (ht.moves 0 (by omega) (· = x) (fun p hp h => ?_) _ (mulVec_mem_idAt _ hy)).trans ?_
  · obtain ⟨PP, h1, h2⟩ := (ht.gP p).1 h
    exact hg PP h1 (hp.symm.trans h2)
  · rw [mulVec_mulVec, ← GlobalTheory.MixModel.mt_mul, mul_inv_cancel, GlobalTheory.MixModel.mt_one, one_mulVec]

end GlobalTheory.MiTop

end
