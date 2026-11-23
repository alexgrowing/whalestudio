import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImageStableDegreeBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyReductionModuloHighDegreeStatement
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.DegreeRaise
open GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds

theorem mem_degrees {e : ℕ} {Sig : Finset (ZMod e)} {c : ZMod e} {m m' i : ℕ} :
    i ∈ degrees Sig c m m' ↔ ∃ c' ∈ Sig, ∃ n, (m ≤ n ∧ n < m') ∧ (c - c').val + n * e = i := by
  simp only [degrees, Finset.mem_image, Finset.mem_product, Finset.mem_Ico, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, b, ⟨ha, hb⟩, rfl⟩

theorem bounds_of_mem {e : ℕ} [NeZero e] {Sig : Finset (ZMod e)} {c : ZMod e} {m m' i : ℕ}
    (h : i ∈ degrees Sig c m m') : m * e ≤ i ∧ i < m' * e := by
  obtain ⟨c', -, n, ⟨h1, h2⟩, rfl⟩ := mem_degrees.1 h
  have := ZMod.val_lt (c - c')
  constructor <;> nlinarith

theorem rootPoly_monic (T : Finset ℕ) : (rootPoly T).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

theorem mem_roots_rootPoly {T : Finset ℕ} {x : ℤ} (h : x ∈ (rootPoly T).roots) : ∃ i ∈ T, x = i := by
  rw [Polynomial.mem_roots (rootPoly_monic T).ne_zero, Polynomial.IsRoot, rootPoly, Polynomial.eval_prod,
    Finset.prod_eq_zero_iff] at h
  obtain ⟨i, hi, h⟩ := h
  exact ⟨i, hi, by simpa [sub_eq_zero] using h⟩

theorem card_degrees_le {e : ℕ} (Sig : Finset (ZMod e)) (c : ZMod e) (m m' : ℕ) :
    (degrees Sig c m m').card ≤ Sig.card * (m' - m) :=
  Finset.card_image_le.trans (by simp [Finset.card_product])

theorem degreeBounds {e : ℕ} [NeZero e] (Sig : Finset (ZMod e)) (c : ZMod e) (A' : ℕ) :
    DegreeBounds Sig c A' where
  lt_of_mem₁ i hi := by have := bounds_of_mem hi; nlinarith
  mem_Ico₂ j hj := by have := bounds_of_mem hj; constructor <;> nlinarith
  monic₁ := rootPoly_monic _
  monic₂ := rootPoly_monic _
  disjoint_roots := by
    rw [Multiset.disjoint_left]
    intro x h1 h2
    obtain ⟨i, hi, rfl⟩ := mem_roots_rootPoly h1
    obtain ⟨j, hj, hij⟩ := mem_roots_rootPoly h2
    have := bounds_of_mem hi
    have := bounds_of_mem hj
    have : i = j := by exact_mod_cast hij
    omega
  card₁ := (card_degrees_le _ _ _ _).trans (by simp)
  card₂ := (card_degrees_le _ _ _ _).trans (by rw [show 2 * A' - A' = A' by omega])

theorem climb {R S V : Type} [Ring R] [Ring S] [AddCommGroup V] [Module R V] [Module S V]
    (f : Module.End S V) (W : ℕ → Submodule R V) (m : ℕ) :
    ∀ k (T : Finset ℕ), (∀ i ∈ T, ∀ x ∈ W i, f x - i • x ∈ W (i + 1)) →
      (∀ i, m ≤ i → i < m + k → i ∉ T → W i ≤ W (i + 1)) → T ⊆ Finset.Ico m (m + k) →
      ∀ x ∈ W m, Polynomial.aeval f (rootPoly T) x ∈ W (m + k) := by
  intro k
  induction k with
  | zero =>
    intro T _ _ hT x hx
    have : T = ∅ := Finset.subset_empty.1 (by simpa using hT)
    subst this
    simpa [rootPoly] using hx
  | succ k ih =>
    intro T hstep hskip hT x hx
    by_cases hj : m + k ∈ T
    · have hT' : T.erase (m + k) ⊆ Finset.Ico m (m + k) := fun i hi => by
        have h1 := Finset.mem_erase.1 hi
        have h2 := Finset.mem_Ico.1 (hT h1.2)
        exact Finset.mem_Ico.2 ⟨h2.1, by omega⟩
      have hy := ih (T.erase (m + k)) (fun i hi => hstep i (Finset.mem_of_mem_erase hi))
        (fun i h1 h2 h3 => hskip i h1 (by omega) fun h => h3 (Finset.mem_erase.2 ⟨by omega, h⟩)) hT' x hx
      have hP : rootPoly T = (Polynomial.X - Polynomial.C ((m + k : ℕ) : ℤ)) * rootPoly (T.erase (m + k)) :=
        (Finset.mul_prod_erase T _ hj).symm
      rw [hP, map_mul, Module.End.mul_apply]
      have := hstep _ hj _ hy
      rw [← add_assoc]
      convert this using 1
      simp [Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_add_neg]
      rw [add_smul]
      abel
    · have hT' : T ⊆ Finset.Ico m (m + k) := fun i hi => by
        have h2 := Finset.mem_Ico.1 (hT hi)
        refine Finset.mem_Ico.2 ⟨h2.1, ?_⟩
        rcases Nat.lt_or_ge i (m + k) with h | h
        · exact h
        · exact absurd (show i = m + k by omega ▸ hi) hj
      exact hskip (m + k) (by omega) (by omega) hj
        (ih T hstep (fun i h1 h2 h3 => hskip i h1 (by omega) h3) hT' x hx)

section Main

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a] {ι : Type} [Fintype ι] [DecidableEq ι] {η H : ℕ}

theorem actD_red (D : BKDat O K l e a ι η H) (c : ZMod e) (i : ℕ) (y : Vec K a ι)
    (hx : (X : K⟦X⟧) ^ i • y ∈ D.desc.isotypic c) (ζ : rootsOfUnity e K) (τ : ZMod a) :
    D.desc.actD (TameGal.inertia ζ) (red y) τ =
      (TameGal.inertia ζ : TameGal K l e a).root τ ^ (c - (i : ZMod e)).val • red y τ := by
  have h1 := hx ζ τ
  have h2 : D.desc.act (TameGal.inertia ζ) ((X : K⟦X⟧) ^ i • y) =
      ringAct (TameGal.inertia ζ) ((fun _ => X) ^ i) • D.desc.act (TameGal.inertia ζ) y :=
    D.desc.act_smul_tot _ _ y
  rw [map_pow, ringAct_X] at h2
  rw [h2] at h1
  have hr0 := (TameGal.inertia ζ : TameGal K l e a).root_ne_zero τ
  have hre := (TameGal.inertia ζ : TameGal K l e a).root_pow τ
  have hmod : ((c - (i : ZMod e)).val + i) % e = c.val := by
    rw [← ZMod.val_natCast, Nat.cast_add, ZMod.natCast_zmod_val, sub_add_cancel]
  ext j
  have h3 := congrFun h1 j
  simp only [Pi.smul_apply', Pi.pow_apply, Pi.smul_apply, smul_eq_mul] at h3
  rw [← D.desc.red_act]
  simp only [red_apply, powerSeriesVecReduceModU_apply, Pi.smul_apply, smul_eq_mul]
  generalize (TameGal.inertia ζ : TameGal K l e a).root τ = r at h3 hr0 hre ⊢
  have hpow (n : ℕ) : r ^ n = r ^ (n % e) := by
    conv_lhs => rw [← Nat.mod_add_div n e, pow_add, pow_mul, hre, one_pow, mul_one]
  have hc : r ^ c.val = r ^ (c - (i : ZMod e)).val * r ^ i := by
    rw [← pow_add, hpow ((c - (i : ZMod e)).val + i), hmod]
  have h4 : (X : K⟦X⟧) ^ i * (C (r ^ i) * D.desc.act (TameGal.inertia ζ) y τ j) =
      X ^ i * (C (r ^ c.val) * y τ j) := by
    rw [smul_eq_C_mul, mul_pow, ← map_pow] at h3
    linear_combination h3
  have h5 := congrArg constantCoeff (mul_left_cancel₀ (pow_ne_zero i PowerSeries.X_ne_zero) h4)
  simp only [map_mul, constantCoeff_C] at h5
  apply mul_left_cancel₀ (pow_ne_zero i hr0)
  rw [h5, hc]
  ring

theorem vL_eq (P : PhiMod O K l e a ι) (n : ℕ) : vL P n = uL P (e * n) := by
  show mulL P ((X ^ e) ^ n) = mulL P (X ^ (e * n))
  rw [pow_mul]

theorem graded (D : BKDat O K l e a ι η H) (Sig : Finset (ZMod e))
    (hch : ∀ τ, D.desc.chars τ ⊆ (Sig : Set (ZMod e))) (c : ZMod e) (i : ℕ)
    (hi : ¬ ∃ c' ∈ Sig, ∃ n : ℕ, i = (c - c').val + n * e) :
    part (D.desc.isotypic c) (uL D.toPhiMod i) ≤ uL D.toPhiMod (i + 1) := by
  intro x hx
  obtain ⟨hxL, hxW⟩ := Submodule.mem_inf.1 hx
  obtain ⟨y, hy, rfl⟩ := mem_mulL.1 hxL
  have hred : red y = 0 := by
    by_contra hne
    obtain ⟨τ, hτ⟩ : ∃ τ, red y τ ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (funext h)
    have hmem : c - (i : ZMod e) ∈ D.desc.chars τ := ⟨red y, hτ, fun ζ => actD_red D c i y hxW ζ τ⟩
    refine hi ⟨_, hch τ hmem, i / e, ?_⟩
    rw [sub_sub_cancel, ZMod.val_natCast]
    exact (Nat.mod_add_div' i e).symm
  have hw : ∀ τ, ∃ w ∈ D.toPhiMod.Lcomp τ, y τ = (X : K⟦X⟧) • w := by
    intro τ
    have hyτ : y τ ∈ D.toPhiMod.Lcomp τ := mem_tot.1 hy τ
    have h0 : (⟨y τ, hyτ⟩ : D.toPhiMod.Lcomp τ) ∈ D.toPhiMod.uL τ :=
      D.toPhiMod.mem_uL_iff.2 (by simpa using congrFun hred τ)
    rw [PhiMod.uL, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h0
    obtain ⟨w, -, hw⟩ := h0
    refine ⟨w, w.2, ?_⟩
    rw [show y τ = ((⟨y τ, hyτ⟩ : D.toPhiMod.Lcomp τ) : ι → K⟦X⟧) from rfl, ← hw, Submodule.coe_smul,
      Subalgebra.smul_def, coe_uIn]
  choose w hwL hwy using hw
  have hy' : y = (X : K⟦X⟧) • (fun τ => w τ) := funext hwy
  refine mem_mulL.2 ⟨fun τ => w τ, mem_tot.2 hwL, ?_⟩
  rw [hy', pow_succ, mul_smul]

theorem step {P : PhiMod O K l e a ι} {W : Submodule K (Vec K a ι)} (hM : ModHigh P W) (i : ℕ)
    (hi : i < l * e) (x : Vec K a ι) (hx : x ∈ part W (uL P i) ⊔ part W (MMHigh P)) :
    P.conn x - i • x ∈ part W (uL P (i + 1)) ⊔ part W (MMHigh P) := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  have h1 := hM.conn_graded i hi y hy
  have h2 : P.conn z - i • z ∈ part W (MMHigh P) :=
    sub_mem (hM.conn_high z hz) (Submodule.smul_of_tower_mem _ i hz)
  have : P.conn (y + z) - i • (y + z) = (P.conn y - i • y) + (P.conn z - i • z) := by
    rw [map_add, smul_add]
    abel
  rw [this]
  exact add_mem h1 (Submodule.mem_sup_right h2)

theorem raisesDegree (hR : Reduction O K l e a) (Sig : Finset (ZMod e)) (c : ZMod e) (A' : ℕ)
    (hA : 2 * A' ≤ l) (D : BKDat O K l e a ι η H)
    (hch : ∀ τ, D.desc.chars τ ⊆ (Sig : Set (ZMod e))) : RaisesDegree D.desc Sig c A' := by
  have hM := (hR.2.1 ι η H D).2.2 c
  have hl := (Fact.out : l.Prime).two_le
  have he := NeZero.pos e
  have hAl : A' < l := by omega
  set W := D.desc.isotypic c
  let V : ℕ → Submodule O (Vec K a ι) := fun i => part W (uL D.toPhiMod i) ⊔ part W (MMHigh D.toPhiMod)
  have hskip (i : ℕ) (hi : ¬ ∃ c' ∈ Sig, ∃ n : ℕ, i = (c - c').val + n * e) : V i ≤ V (i + 1) :=
    sup_le_sup_right (le_inf (graded D Sig hch c i hi) inf_le_right) _
  refine ⟨fun i hi => graded D Sig hch c i hi, fun x hx => ?_, fun x hx => ?_⟩
  · have hx0 : x ∈ V 0 := Submodule.mem_sup_left (Submodule.mem_inf.2
      ⟨mem_mulL.2 ⟨x, (Submodule.mem_inf.1 hx).1, by simp⟩, (Submodule.mem_inf.1 hx).2⟩)
    have h := climb D.toPhiMod.conn V 0 (e * A') (D₁ Sig c A')
      (fun i hi y hy => step hM i (by have := bounds_of_mem hi; nlinarith) y hy)
      (fun i _ h2 h3 => hskip i fun ⟨c', hc', n, hn⟩ => h3 (mem_degrees.2 ⟨c', hc', n,
        ⟨Nat.zero_le _, by have := ZMod.val_lt (c - c'); nlinarith⟩, hn.symm⟩))
      (fun i hi => by have := bounds_of_mem hi; exact Finset.mem_Ico.2 ⟨Nat.zero_le _, by nlinarith⟩) x hx0
    rw [zero_add] at h
    refine (sup_le_sup (inf_le_left.trans (le_of_eq (vL_eq _ _).symm)) inf_le_left) h
  · have hx0 : x ∈ V (e * A') := Submodule.mem_sup_left (by rwa [← vL_eq])
    have h := climb D.toPhiMod.conn V (e * A') (e * A') (D₂ Sig c A')
      (fun i hi y hy => step hM i (by have := bounds_of_mem hi; nlinarith) y hy)
      (fun i h1 h2 h3 => hskip i fun ⟨c', hc', n, hn⟩ => h3 (mem_degrees.2 ⟨c', hc', n,
        ⟨by have := ZMod.val_lt (c - c'); nlinarith, by nlinarith⟩, hn.symm⟩))
      (fun i hi => by have := bounds_of_mem hi; exact Finset.mem_Ico.2 ⟨by nlinarith, by nlinarith⟩) x hx0
    rw [show e * A' + e * A' = e * (2 * A') by ring] at h
    refine (sup_le_sup (inf_le_left.trans (le_of_eq (vL_eq _ _).symm)) inf_le_left) h

theorem degrees_of_reduction (hR : Reduction O K l e a) : Degrees O K l e a :=
  fun Sig c A' hA => ⟨degreeBounds Sig c A', fun ι _ _ η H D hch => raisesDegree hR Sig c A' hA D hch⟩

end Main

theorem main : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
    [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
    [TameDescentExponentData K l e a], GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.Degrees O K l e a :=
  fun O K _ _ _ _ _ _ l e a _ _ _ _ _ => degrees_of_reduction (GlobalTheory.T.monodromy_reduction_modulo_high_degree O K l e a)

end GlobalTheory.DegreeRaise
