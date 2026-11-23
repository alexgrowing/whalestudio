import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHeckeSplitPlaceSetIffDoubleCoset
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

namespace UpperTheory.Gal.CongruenceSubgroupGeneration

section Val

variable {F Γ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ] (v : Valuation F Γ) {a : ℕ}

private def Mt (c : Γ) : Set (Matrix (Fin a) (Fin a) F) := {A | ∀ i j, v (A i j) ≤ c}

variable {v}

private theorem Mt_mono {c d : Γ} (h : c ≤ d) {A : Matrix (Fin a) (Fin a) F} (hA : A ∈ Mt v c) : A ∈ Mt v d :=
  fun i j => (hA i j).trans h

private theorem Mt_zero (c : Γ) : (0 : Matrix (Fin a) (Fin a) F) ∈ Mt v c := fun i j => by simp

private theorem Mt_add {c : Γ} {A B : Matrix (Fin a) (Fin a) F} (hA : A ∈ Mt v c) (hB : B ∈ Mt v c) :
    A + B ∈ Mt v c := fun i j => by
  rw [Matrix.add_apply]
  exact v.map_add_le (hA i j) (hB i j)

private theorem Mt_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin a) (Fin a) F) {c : Γ}
    (h : ∀ i ∈ s, f i ∈ Mt v c) : ∑ i ∈ s, f i ∈ Mt v c := fun p q => by
  rw [Matrix.sum_apply]
  exact v.map_sum_le fun i hi => h i hi p q

private theorem Mt_mul {c d : Γ} {A B : Matrix (Fin a) (Fin a) F} (hA : A ∈ Mt v c) (hB : B ∈ Mt v d) :
    A * B ∈ Mt v (c * d) := fun i j => by
  rw [Matrix.mul_apply]
  refine v.map_sum_le fun k _ => ?_
  rw [map_mul]
  exact mul_le_mul' (hA i k) (hB k j)

private theorem Mt_one : (1 : Matrix (Fin a) (Fin a) F) ∈ Mt v (1 : Γ) := fun i j => by
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

private theorem Mt_of_sub {c : Γ} (hc : c ≤ 1) {A : Matrix (Fin a) (Fin a) F} (hA : A - 1 ∈ Mt v c) :
    A ∈ Mt v (1 : Γ) := by
  have e : A = (A - 1) + 1 := by simp
  rw [e]
  exact Mt_add (Mt_mono hc hA) Mt_one

private theorem Mt_mul_sub {c : Γ} (hc : c ≤ 1) {A B : Matrix (Fin a) (Fin a) F} (hA : A - 1 ∈ Mt v c)
    (hB : B - 1 ∈ Mt v c) : A * B - 1 ∈ Mt v c := by
  have e : A * B - 1 = (A - 1) * (B - 1) + ((A - 1) + (B - 1)) := by noncomm_ring
  rw [e]
  exact Mt_add (Mt_mono (mul_le_of_le_one_left' hc) (Mt_mul hA hB)) (Mt_add hA hB)

private theorem Mt_conj {c : Γ} {G H X : Matrix (Fin a) (Fin a) F} (hG : G ∈ Mt v (1 : Γ)) (hH : H ∈ Mt v (1 : Γ))
    (hGH : G * H = 1) (hX : X - 1 ∈ Mt v c) : G * X * H - 1 ∈ Mt v c := by
  have e : G * X * H - 1 = G * (X - 1) * H := by
    rw [mul_sub, sub_mul, mul_one, hGH]
  rw [e]
  simpa using Mt_mul (Mt_mul hG hX) hH

variable (v)

private noncomputable def Jc (c : Γ) (hc : c ≤ 1) : Subgroup (GL (Fin a) F) where
  carrier := {g | g.val - 1 ∈ Mt v c ∧ (g⁻¹).val - 1 ∈ Mt v c}
  one_mem' := by simp [Mt_zero]
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨by simpa using Mt_mul_sub hc hx hy, ?_⟩
    rw [_root_.mul_inv_rev]
    simpa using Mt_mul_sub hc hy' hx'
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    exact ⟨hx', by simpa using hx⟩

variable {v}

private theorem mem_Jc {c : Γ} {hc : c ≤ 1} {g : GL (Fin a) F} :
    g ∈ Jc v c hc ↔ g.val - 1 ∈ Mt v c ∧ (g⁻¹).val - 1 ∈ Mt v c := Iff.rfl

private theorem Jc_anti {c d : Γ} {hc : c ≤ 1} {hd : d ≤ 1} (h : c ≤ d) : Jc (a := a) v c hc ≤ Jc v d hd :=
  fun _ hg => ⟨Mt_mono h hg.1, Mt_mono h hg.2⟩

private theorem Jc_normal {c d : Γ} {hc : c ≤ 1} {hd : d ≤ 1} {g x : GL (Fin a) F} (hg : g ∈ Jc v d hd)
    (hx : x ∈ Jc v c hc) : g * x * g⁻¹ ∈ Jc v c hc := by
  have h1 := Mt_of_sub hd hg.1
  have h2 := Mt_of_sub hd hg.2
  refine ⟨?_, ?_⟩
  · simpa using Mt_conj h1 h2 (by simp) hx.1
  · have e : (g * x * g⁻¹)⁻¹ = g * x⁻¹ * g⁻¹ := by group
    rw [e]
    simpa using Mt_conj h1 h2 (by simp) hx.2

private theorem pow_sub_mem {c r : Γ} {hc : c ≤ 1} (hcr : c ≤ r) {l : ℕ} (hl : v (l : F) ≤ r)
    {x : GL (Fin a) F} (hx : x ∈ Jc v c hc) : (x ^ l).val - 1 ∈ Mt v (r * c) := by
  have hi : ∀ i, x.val ^ i - 1 ∈ Mt v c := fun i => by
    have := ((Jc v c hc).pow_mem hx i).1
    simpa using this
  have key : (x ^ l).val - 1 =
      ((∑ i ∈ Finset.range l, (x.val ^ i - 1)) + (l : Matrix (Fin a) (Fin a) F)) * (x.val - 1) := by
    rw [Units.val_pow_eq_pow_val, ← geom_sum_mul]
    congr 1
    rw [Finset.sum_sub_distrib]
    simp
  have hL : (l : Matrix (Fin a) (Fin a) F) ∈ Mt v r := fun i j => by
    rw [← Matrix.diagonal_natCast]
    by_cases h : i = j
    · subst h; simpa using hl
    · simp [Matrix.diagonal_apply_ne _ h]
  rw [key]
  exact Mt_mul (Mt_add (Mt_mono hcr (Mt_sum _ _ fun i _ => hi i)) hL) hx.1

private theorem Jc_pow {c r : Γ} {hc : c ≤ 1} {hrc : r * c ≤ 1} (hcr : c ≤ r) {l : ℕ} (hl : v (l : F) ≤ r)
    {x : GL (Fin a) F} (hx : x ∈ Jc v c hc) : x ^ l ∈ Jc v (r * c) hrc := by
  refine ⟨pow_sub_mem hcr hl hx, ?_⟩
  rw [← inv_pow]
  exact pow_sub_mem hcr hl ((Jc v c hc).inv_mem hx)

end Val

end UpperTheory.Gal.CongruenceSubgroupGeneration

namespace UpperTheory.Gal.CongruenceSubgroupGeneration

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {a : ℕ}

private theorem isOpen_ball {d : w.adicCompletion E} (hd : d ≠ 0) :
    IsOpen {y : w.adicCompletion E | Valued.v y ≤ Valued.v d} := by
  have e : {y : w.adicCompletion E | Valued.v y ≤ Valued.v d} = {y | Valued.v.restrict y ≤ Valued.v.restrict d} := by
    ext y
    simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff]
  rw [e]
  exact Valued.isOpen_closedBall _ (by simp [hd])

private theorem isOpen_Jc {d : w.adicCompletion E} (hd : d ≠ 0) (hc : Valued.v d ≤ 1) :
    IsOpen (Jc (a := a) (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))) (Valued.v d) hc : Set (GL (Fin a) (w.adicCompletion E))) := by
  have e : (Jc (a := a) (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))) (Valued.v d) hc : Set (GL (Fin a) (w.adicCompletion E))) =
      (⋂ i, ⋂ j, {g : GL (Fin a) (w.adicCompletion E) | Valued.v (g.val i j -
        (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ Valued.v d}) ∩
      (⋂ i, ⋂ j, {g : GL (Fin a) (w.adicCompletion E) | Valued.v ((g⁻¹).val i j -
        (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ Valued.v d}) := by
    ext g
    simp only [SetLike.mem_coe, mem_Jc, Mt, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Matrix.sub_apply]
  rw [e]
  refine IsOpen.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
  · exact (isOpen_ball w hd).preimage ((Units.continuous_val.matrix_elem i j).sub continuous_const)
  · exact (isOpen_ball w hd).preimage ((Units.continuous_coe_inv.matrix_elem i j).sub continuous_const)

private theorem Jc_le_KGL {c : WithZero (Multiplicative ℤ)} (hc : c ≤ 1) :
    Jc (a := a) (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))) c hc ≤ GlobalTheory.LFun.KGL w a := by
  intro g hg
  have h1 := Mt_of_sub hc hg.1
  have h2 := Mt_of_sub hc hg.2
  refine GlobalTheory.TSetDoubleCoset.mem_GLint_of_entries (Formalism.UG.Ov E w) g (fun i j => ?_) (fun i j => ?_)
  · change (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))) _ ≤ 1
    exact h1 i j
  · change (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))) _ ≤ 1
    exact h2 i j

private theorem eq_one_of_forall {r : WithZero (Multiplicative ℤ)} (hr : r < 1) {g : GL (Fin a) (w.adicCompletion E)}
    (h : ∀ n : ℕ, g.val - 1 ∈ Mt (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))) (r ^ (n + 1))) : g = 1 := by
  refine Units.ext (sub_eq_zero.1 (Matrix.ext fun i j => ?_))
  by_contra hne
  have hv : Valued.v ((g.val - 1) i j) ≠ 0 := (Valuation.ne_zero_iff _).2 hne
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hr (Units.mk0 _ hv)
  have h1 : Valued.v ((g.val - 1) i j) ≤ r ^ (n + 1) := h n i j
  have h2 : r ^ (n + 1) ≤ r ^ n := pow_le_pow_right_of_le_one' hr.le (Nat.le_succ n)
  exact absurd (h1.trans h2) (not_le.2 hn)

end UpperTheory.Gal.CongruenceSubgroupGeneration

open UpperTheory.Gal.CongruenceSubgroupGeneration in
theorem UpperTheory.Gal.Gen.congSub_pf :
    UpperTheory.Gal.Gen.CongSub := by
  intro E _ _ w a l hl hmem
  set F := w.adicCompletion E with hF
  have e : ((l : ℕ) : F) = algebraMap E F ((l : ℕ) : E) := by simp
  have hl0 : ((l : ℕ) : F) ≠ 0 := by
    have : ((l : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
    rw [e]
    exact (map_ne_zero _).2 this
  have hr : Valued.v ((l : ℕ) : F) < 1 := by
    have h1 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w _).2 hmem
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation] at h1
    simpa using h1
  set r := Valued.v ((l : ℕ) : F) with hrdef
  have hp : ∀ n : ℕ, r ^ n ≤ 1 := fun n => pow_le_one' hr.le n
  let J : ℕ → Subgroup (GL (Fin a) F) := fun n => Jc Valued.v (r ^ (n + 1)) (hp _)
  have hopen : ∀ n, IsOpen (J n : Set (GL (Fin a) F)) := fun n => by
    have hd : ((l : ℕ) : F) ^ (n + 1) ≠ 0 := pow_ne_zero _ hl0
    have hv : Valued.v (((l : ℕ) : F) ^ (n + 1)) = r ^ (n + 1) := map_pow _ _ _
    have := isOpen_Jc (a := a) w hd (hv.le.trans (hp _))
    simp only [hv] at this
    exact this
  have hcomp : ∀ n, IsCompact (J n : Set (GL (Fin a) F)) := fun n =>
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.of_isClosed_subset
      (Subgroup.isClosed_of_isOpen _ (hopen n)) (Jc_le_KGL w (hp _))
  have hanti : Antitone J := fun m n hmn =>
    Jc_anti (pow_le_pow_right_of_le_one' hr.le (Nat.succ_le_succ hmn))
  refine ⟨J, ⟨hopen, hcomp, hanti, fun n g hg x hx => Jc_normal hg hx, ?_⟩, fun n x hx => ?_⟩
  · intro N hN
    by_contra hcon
    push_neg at hcon
    have hclosed : ∀ n, IsClosed ((J n : Set (GL (Fin a) F)) \ interior N) := fun n =>
      (Subgroup.isClosed_of_isOpen _ (hopen n)).sdiff isOpen_interior
    obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun n => (J n : Set (GL (Fin a) F)) \ interior N)
      (fun n => Set.diff_subset_diff_left (hanti (Nat.le_succ n)))
      (fun n => by
        obtain ⟨x, hx, hxN⟩ := Set.not_subset.1 (hcon n)
        exact ⟨x, hx, fun h => hxN (interior_subset h)⟩)
      ((hcomp 0).diff isOpen_interior) hclosed
    have hg' := Set.mem_iInter.1 hg
    have h1 : g = 1 := eq_one_of_forall w hr fun n => (hg' n).1.1
    exact (hg' 0).2 (h1 ▸ mem_interior_iff_mem_nhds.2 hN)
  · have hcr : r ^ (n + 1) ≤ r := by
      simpa using pow_le_pow_right_of_le_one' hr.le (Nat.succ_le_succ (Nat.zero_le n))
    have := Jc_pow (hc := hp (n + 1)) (hrc := by rw [← pow_succ']; exact hp _) hcr (l := l) le_rfl hx
    simpa only [J, pow_succ'] using this
