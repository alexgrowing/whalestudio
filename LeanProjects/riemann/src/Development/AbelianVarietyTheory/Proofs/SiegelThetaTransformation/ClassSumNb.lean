import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteClsAndStab
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NeBotOfNorm

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

namespace NbAvg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def nbIn (M : ℕ) (P : Ideal (𝓞 E)) (A B : Lt E n) : Set (Lt E n) :=
  {X | X ∈ Nb M P A ∧ ∃ h ∈ DH E n M, Moves h B X}

def carry (M : ℕ) (P : Ideal (𝓞 E)) (A B : Lt E n) : Set (Matrix (Fin n) (Fin n) E) :=
  {h | h ∈ DH E n M ∧ ∃ X ∈ Nb M P A, Moves h B X}

theorem moves_unique {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1) {B X Y : Lt E n}
    (h1 : Moves h B X) (h2 : Moves h B Y) : X = Y := by
  have hu' : h * ccT h = 1 := mul_eq_one_comm.1 hu
  ext w
  have hw : h *ᵥ (ccT h *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, hu', Matrix.one_mulVec]
  have key := (h1 (ccT h *ᵥ w)).symm.trans (h2 (ccT h *ᵥ w))
  rwa [hw] at key

private theorem one_mem_UJset' {M : ℕ} : (1 : Matrix (Fin n) (Fin n) E) ∈ DH E n M := by
  refine ⟨?_, 1, one_pos, Nat.coprime_one_left _, 0, fun k i => ?_, by simp⟩
  · have h1 : ccT (1 : Matrix (Fin n) (Fin n) E) = 1 := by
      unfold ccT
      rw [Matrix.map_one _ (by simp [cc]) (by simp [cc]), Matrix.transpose_one]
    rw [h1, mul_one]
  · rw [Matrix.zero_apply]
    exact isIntegral_zero

private theorem eq_one_of_mem_DH_zero {h : Matrix (Fin n) (Fin n) E} (hh : h ∈ DH E n 0) : h = 1 := by
  obtain ⟨-, s, -, hs, y, -, e⟩ := hh
  rw [(Nat.coprime_zero_right _).1 hs] at e
  simpa [sub_eq_zero] using e

private theorem eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq {M : ℕ} {g : Matrix (Fin n) (Fin n) E} (hg : g ∈ DH E n M) :
    ccT g ∈ DH E n M ∧ ∀ h ∈ DH E n M, g * h ∈ DH E n M := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · obtain rfl := eq_one_of_mem_DH_zero hg
    refine ⟨?_, fun h hh => by rw [one_mul]; exact hh⟩
    have hc := hg.1
    rw [mul_one] at hc
    rw [hc]
    exact hg
  · exact (finite_cls_and_stab E n M hM).2.2.2.1.2 g hg

theorem transporter_eq {M : ℕ} {g : Matrix (Fin n) (Fin n) E} (hg : g ∈ DH E n M) {B X : Lt E n}
    (m : Moves g B X) :
    {h ∈ DH E n M | Moves h B X} = (fun h => g * h) '' {h ∈ DH E n M | Moves h B B} := by
  have hgg : g * ccT g = 1 := mul_eq_one_comm.1 hg.1
  ext h
  constructor
  · rintro ⟨hh, mh⟩
    refine ⟨ccT g * h, ⟨(eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq (eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq hg).1).2 h hh, fun v => ?_⟩, ?_⟩
    · rw [mh v, m ((ccT g * h) *ᵥ v), Matrix.mulVec_mulVec, ← mul_assoc, hgg, one_mul]
    · show g * (ccT g * h) = h
      rw [← mul_assoc, hgg, one_mul]
  · rintro ⟨k, ⟨hk, mk⟩, rfl⟩
    refine ⟨(eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq hg).2 k hk, fun v => ?_⟩
    show v ∈ B ↔ (g * k) *ᵥ v ∈ X
    rw [mk v, m (k *ᵥ v), Matrix.mulVec_mulVec]

theorem mul_inj {g : Matrix (Fin n) (Fin n) E} (hu : ccT g * g = 1) :
    Function.Injective fun h : Matrix (Fin n) (Fin n) E => g * h := by
  intro a b hab
  have key := congrArg (fun x => ccT g * x) hab
  simpa only [← mul_assoc, hu, one_mul] using key

theorem ncard_carry {M : ℕ} {P : Ideal (𝓞 E)} {A B : Lt E n} (hN : (Nb M P A).Finite)
    (hB : {h ∈ DH E n M | Moves h B B}.Finite) :
    (carry M P A B).ncard = (nbIn M P A B).ncard * {h ∈ DH E n M | Moves h B B}.ncard := by
  classical
  have memC : ∀ h, h ∈ carry M P A B ↔ h ∈ DH E n M ∧ ∃ X ∈ Nb M P A, Moves h B X :=
    fun _ => Iff.rfl
  have memN : ∀ X, X ∈ nbIn M P A B ↔ X ∈ Nb M P A ∧ ∃ h ∈ DH E n M, Moves h B X :=
    fun _ => Iff.rfl
  have hex : ∀ X ∈ nbIn M P A B, ∃ g ∈ DH E n M, Moves g B X := fun X hX => ((memN X).1 hX).2
  choose! g hg hgm using hex
  have hmv : ∀ X ∈ nbIn M P A B, ∀ k, Moves k B B → Moves (g X * k) B X := by
    intro X hX k mk v
    rw [mk v, hgm X hX (k *ᵥ v), Matrix.mulVec_mulVec]
  let F : Lt E n × Matrix (Fin n) (Fin n) E → Matrix (Fin n) (Fin n) E := fun p => g p.1 * p.2
  have himg : F '' (nbIn M P A B ×ˢ {h ∈ DH E n M | Moves h B B}) = carry M P A B := by
    ext h
    constructor
    · rintro ⟨⟨X, k⟩, ⟨hX, hk, mk⟩, rfl⟩
      exact (memC _).2 ⟨(eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq (hg X hX)).2 k hk, X, ((memN X).1 hX).1, hmv X hX k mk⟩
    · intro hh
      obtain ⟨hh, X, hXN, mh⟩ := (memC h).1 hh
      have hX : X ∈ nbIn M P A B := (memN X).2 ⟨hXN, h, hh, mh⟩
      obtain ⟨k, hk, rfl⟩ :=
        (Set.ext_iff.1 (transporter_eq (hg X hX) (hgm X hX)) h).1 ⟨hh, mh⟩
      exact ⟨(X, k), ⟨hX, hk⟩, rfl⟩
  have hinj : Set.InjOn F (nbIn M P A B ×ˢ {h ∈ DH E n M | Moves h B B}) := by
    rintro ⟨X, k⟩ ⟨hX, hk, mk⟩ ⟨Y, k'⟩ ⟨hY, hk', mk'⟩ e
    have e' : g X * k = g Y * k' := e
    have m1 := hmv X hX k mk
    have m2 := hmv Y hY k' mk'
    rw [e'] at m1
    have hXY : X = Y := moves_unique ((eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq (hg Y hY)).2 k' hk').1 m1 m2
    subst hXY
    exact Prod.ext rfl (mul_inj (hg X hX).1 e')
  rw [← himg, hinj.ncard_image, Set.ncard_prod]

theorem ccT_mem_carry {M q : ℕ} {P : Ideal (𝓞 E)} (hM : 0 < M) (hP : GoodPrime M q P)
    {A B : Lt E n} (hA : A ∈ Vset E n M) (hB : B ∈ Vset E n M) {h : Matrix (Fin n) (Fin n) E}
    (hh : h ∈ carry M P A B) : ccT h ∈ carry M (conjI P) B A := by
  obtain ⟨hh, X, hXN, mh⟩ := hh
  have hh' : h * ccT h = 1 := mul_eq_one_comm.1 hh.1
  have hc : ccT h ∈ DH E n M := (eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq hh).1
  obtain ⟨Y, -, mY⟩ := (finite_cls_and_stab E n M hM).2.2.2.2 (ccT h) hc A hA
  have hX : X ∈ Vset E n M := hXN.1
  obtain ⟨hgc, -, hnb⟩ := neighbours E n M q P hM hP
  have hAX : A ∈ Nb M (conjI P) X := ((hnb A hA).2.2.1 X hX).1 hXN
  have hequiv := ((neighbours E n M q (conjI P) hM hgc).2.2 X hX).2.2.2.2.2
  have hmXB : Moves (ccT h) X B := Nbr.move_inv hh' mh
  show ccT h ∈ DH E n M ∧ ∃ Y ∈ Nb M (conjI P) B, Moves (ccT h) A Y
  exact ⟨hc, Y, (hequiv (ccT h) hc B hB hmXB A Y mY).1 hAX, mY⟩

theorem ncard_carry_symm {M q : ℕ} {P : Ideal (𝓞 E)} (hM : 0 < M) (hP : GoodPrime M q P)
    {A B : Lt E n} (hA : A ∈ Vset E n M) (hB : B ∈ Vset E n M) :
    (carry M (conjI P) B A).ncard = (carry M P A B).ncard := by
  have hcc : ∀ k : Matrix (Fin n) (Fin n) E, ccT (ccT k) = k := by
    intro k
    ext i j
    simp [ccT, Nbr.cc_cc]
  have hgc : GoodPrime M q (conjI P) := Nbr.good_conj hP
  have himg : (ccT : Matrix (Fin n) (Fin n) E → Matrix (Fin n) (Fin n) E) '' carry M P A B =
      carry M (conjI P) B A := by
    ext k
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ccT_mem_carry hM hP hA hB hh
    · intro hk
      refine ⟨ccT k, ?_, hcc k⟩
      have key := ccT_mem_carry hM hgc hB hA hk
      rwa [Nbr.conjI_conjI] at key
  rw [← himg, Set.ncard_image_of_injective _ (Function.LeftInverse.injective hcc)]

theorem wt_mul_nbIn {M q : ℕ} {P : Ideal (𝓞 E)} (hM : 0 < M) (hP : GoodPrime M q P)
    {A B : Lt E n} (hA : A ∈ Vset E n M) (hB : B ∈ Vset E n M) :
    (wt M A : ℂ) * (nbIn M P A B).ncard = (wt M B : ℂ) * (nbIn M (conjI P) B A).ncard := by
  obtain ⟨-, -, hstab, -, -⟩ := finite_cls_and_stab E n M hM
  obtain ⟨hgc, -, hnb⟩ := neighbours E n M q P hM hP
  have hnb' := (neighbours E n M q (conjI P) hM hgc).2.2
  have h1 := ncard_carry (P := P) (A := A) (B := B) (hnb A hA).1 (hstab B hB).1
  have h2 := ncard_carry (P := conjI P) (A := B) (B := A) (hnb' B hB).1 (hstab A hA).1
  have h3 := ncard_carry_symm hM hP hA hB
  have key : (nbIn M P A B).ncard * {h ∈ DH E n M | Moves h B B}.ncard =
      (nbIn M (conjI P) B A).ncard * {h ∈ DH E n M | Moves h A A}.ncard := by
    rw [← h1, ← h2, h3]
  have hne : ∀ Λ ∈ Vset E n M, (({h ∈ DH E n M | Moves h Λ Λ}.ncard : ℕ) : ℂ) ≠ 0 := by
    intro Λ hΛ h0
    have hw := (hstab Λ hΛ).2
    norm_cast at h0
    simp only [wt, h0] at hw
    simp at hw
  simp only [wt]
  push_cast
  rw [inv_mul_eq_div, inv_mul_eq_div, div_eq_div_iff (hne A hA) (hne B hB)]
  exact_mod_cast key

private theorem exists_moves_of_cls_eq {M : ℕ} {a b : Vset E n M}
    (e : (Quot.mk _ a : Cls E n M) = Quot.mk _ b) : ∃ h ∈ DH E n M, Moves h a.1 b.1 := by
  have hq := Quot.eqvGen_exact e
  clear e
  induction hq with
  | rel x y hxy => exact hxy
  | refl x => exact ⟨1, one_mem_UJset', fun v => by rw [Matrix.one_mulVec]⟩
  | symm x y _ ih =>
    obtain ⟨h, hh, m⟩ := ih
    exact ⟨ccT h, (eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq hh).1, Nbr.move_inv (mul_eq_one_comm.1 hh.1) m⟩
  | trans x y z _ _ ih1 ih2 =>
    obtain ⟨h, hh, m⟩ := ih1
    obtain ⟨k, hk, m'⟩ := ih2
    exact ⟨k * h, (eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq hk).2 h hh, fun v => by rw [m v, m' (h *ᵥ v), Matrix.mulVec_mulVec]⟩

theorem sum_nb {M : ℕ} [Fintype (Cls E n M)] {P : Ideal (𝓞 E)} {A : Lt E n}
    (hN : (Nb M P A).Finite) {f : Lt E n → ℂ} (hf : IsClassFn M f) :
    ∑ᶠ X ∈ Nb M P A, f X =
      ∑ c : Cls E n M, ((nbIn M P A (Quot.out c).1).ncard : ℂ) * f (Quot.out c).1 := by
  classical
  rcases isEmpty_or_nonempty (Cls E n M) with hE | hE
  · have h0 : Nb M P A = ∅ := by
      ext X
      simp only [Set.mem_empty_iff_false, iff_false]
      exact fun hX => hE.false (Quot.mk _ ⟨X, hX.1⟩)
    simp [h0]
  let cl : Lt E n → Cls E n M := fun X =>
    if hX : X ∈ Vset E n M then Quot.mk _ ⟨X, hX⟩ else hE.some
  have hcl : ∀ X (hX : X ∈ Vset E n M), cl X = Quot.mk _ ⟨X, hX⟩ := fun X hX => dif_pos hX
  rw [finsum_mem_eq_finite_toFinset_sum _ hN,
    ← Finset.sum_fiberwise_of_maps_to (s := hN.toFinset) (t := Finset.univ) (g := cl)
      (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hset : ((hN.toFinset.filter fun X => cl X = c : Finset (Lt E n)) : Set (Lt E n)) =
      nbIn M P A (Quot.out c).1 := by
    ext X
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, nbIn]
    constructor
    · rintro ⟨hX, hc⟩
      exact ⟨hX, exists_moves_of_cls_eq ((Quot.out_eq c).trans ((hcl X hX.1).symm.trans hc).symm)⟩
    · rintro ⟨hX, h, hh, m⟩
      refine ⟨hX, ?_⟩
      rw [hcl X hX.1]
      exact (Quot.sound (⟨h, hh, m⟩ : ∃ h ∈ DH E n M, Moves h (Quot.out c).1 X)).symm.trans
        (Quot.out_eq c)
  have hval : ∀ X ∈ hN.toFinset.filter (fun X => cl X = c), f X = f (Quot.out c).1 := by
    intro X hX
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hX
    obtain ⟨h, hh, m⟩ := exists_moves_of_cls_eq ((Quot.out_eq c).trans ((hcl X hX.1.1).symm.trans hX.2).symm)
    exact hf h hh _ (Quot.out c).2 X hX.1.1 m
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul, ← Set.ncard_coe_finset, hset]

end NbAvg

open NbAvg in

theorem classSum_nb :
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n M q : ℕ) (P : Ideal (𝓞 E)), 0 < M → GoodPrime M q P → ∀ f : Lt E n → ℂ, (∀ h ∈ DH E n M, ∀ Λ ∈ Vset E n M, ∀ Λ' ∈ Vset E n M, Moves h Λ Λ' → f Λ' = f Λ) → ((q : ℂ) - 1) * classSum M (fun Λ => ∑ᶠ Λ' ∈ Nb M P Λ, f Λ') = ((q : ℂ) ^ n - 1) * classSum M f := by
  intro E _ _ _ n M q P hM hP f hf
  obtain ⟨hcls, -, -, -, -⟩ := finite_cls_and_stab E n M hM
  let _ : Fintype (Cls E n M) := Fintype.ofFinite _
  obtain ⟨hgc, -, hnb⟩ := neighbours E n M q P hM hP
  have hnb' := (neighbours E n M q (conjI P) hM hgc).2.2
  have hf' : IsClassFn M f := hf
  have hone : IsClassFn M (fun _ : Lt E n => (1 : ℂ)) := fun _ _ _ _ _ _ _ => rfl
  have hcount : ∀ d : Cls E n M, ((q : ℂ) - 1) *
      ∑ c : Cls E n M, ((nbIn M (conjI P) (Quot.out d).1 (Quot.out c).1).ncard : ℂ) =
      (q : ℂ) ^ n - 1 := by
    intro d
    obtain ⟨hfin, hcnt, -⟩ := hnb' _ (Quot.out d).2
    have hs := NbAvg.sum_nb hfin hone
    simp only [mul_one] at hs
    have h1 : ∑ᶠ X ∈ Nb M (conjI P) (Quot.out d).1, (1 : ℂ) =
        ((Nb M (conjI P) (Quot.out d).1).ncard : ℂ) := by
      rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const, nsmul_eq_mul, mul_one,
        Set.ncard_eq_toFinset_card _ hfin]
    rw [h1] at hs
    rw [← hs]
    have hq1 : 1 ≤ q := hP.1.one_lt.le
    have hqn : 1 ≤ q ^ n := Nat.one_le_pow _ _ hP.1.pos
    have hc := congrArg (fun x : ℕ => (x : ℂ)) hcnt
    simp only [Nat.cast_mul, Nat.cast_sub hq1, Nat.cast_sub hqn, Nat.cast_pow, Nat.cast_one] at hc
    linear_combination hc
  have hsum : ∀ c : Cls E n M, ∑ᶠ X ∈ Nb M P (Quot.out c).1, f X =
      ∑ d : Cls E n M, ((nbIn M P (Quot.out c).1 (Quot.out d).1).ncard : ℂ) * f (Quot.out d).1 :=
    fun c => NbAvg.sum_nb (hnb _ (Quot.out c).2).1 hf'
  simp only [classSum, finsum_eq_sum_of_fintype, hsum]
  calc _ = ∑ c : Cls E n M, ∑ d : Cls E n M, ((q : ℂ) - 1) * ((wt M (Quot.out d).1 : ℂ) *
        ((nbIn M (conjI P) (Quot.out d).1 (Quot.out c).1).ncard : ℂ)) * f (Quot.out d).1 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [← wt_mul_nbIn hM hP (Quot.out c).2 (Quot.out d).2]
        ring
    _ = ∑ d : Cls E n M, ∑ c : Cls E n M, ((q : ℂ) - 1) * ((wt M (Quot.out d).1 : ℂ) *
        ((nbIn M (conjI P) (Quot.out d).1 (Quot.out c).1).ncard : ℂ)) * f (Quot.out d).1 :=
        Finset.sum_comm
    _ = ∑ d : Cls E n M, ((wt M (Quot.out d).1 : ℂ) * f (Quot.out d).1) * (((q : ℂ) - 1) *
        ∑ c : Cls E n M, ((nbIn M (conjI P) (Quot.out d).1 (Quot.out c).1).ncard : ℂ)) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring
    _ = ((q : ℂ) ^ n - 1) * ∑ d : Cls E n M, (wt M (Quot.out d).1 : ℂ) * f (Quot.out d).1 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [hcount d]
        ring

end GlobalTheory.SW
