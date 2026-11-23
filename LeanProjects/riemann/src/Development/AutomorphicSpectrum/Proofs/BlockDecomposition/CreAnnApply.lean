import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnEqZeroOfDegreeZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverByAcyclicPair

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.PairMult.COU

open GlobalTheory.CompanionTheory.PairMult
open GlobalTheory.CompanionTheory.RealMult.CovR (FiltR)
open CompanionTheory.D.LK (Pos key)
open Formalism.REAL (GlRel)

variable {n : ℕ}

section Acyc

variable {V : Type} [AddCommGroup V] [Module ℂ V]
theorem cre_ann_apply (i : Lt n) (x : Cq n V) (A : Finset (Lt n)) :
    creq i (annq i x) A = if i ∈ A then x A else 0 := by
  by_cases h : i ∈ A
  · simp [cre_apply, ann_apply, h, sg_erase i h, tw_self, smul_smul, sg_mul_self, insert_erase h]
  · simp [cre_apply, h]

theorem ann_mem {Q : Submodule ℂ V} {x : Cq n V} (h : ∀ A, x A ∈ Q) (i : Lt n) (A : Finset (Lt n)) :
    annq i x A ∈ Q := by
  rw [ann_apply]; split_ifs
  · exact Q.zero_mem
  · exact Q.smul_mem _ (h _)

theorem cre_mem {Q : Submodule ℂ V} {x : Cq n V} (h : ∀ A, x A ∈ Q) (i : Lt n) (A : Finset (Lt n)) :
    creq i x A ∈ Q := by
  rw [cre_apply]; split_ifs
  · exact Q.smul_mem _ (h _)
  · exact Q.zero_mem

theorem supp_sub {P : Lt n → Prop} {x y : Cq n V} (hx : SuppQ P x) (hy : SuppQ P y) : SuppQ P (x - y) :=
  Submodule.sub_mem (supSub V _) hx hy

theorem deg_sub {j : ℕ} {x y : Cq n V} (hx : DegQ j x) (hy : DegQ j y) : DegQ j (x - y) :=
  Submodule.sub_mem (supSub V _) hx hy

theorem supp_of {P : Lt n → Prop} {x y : Cq n V} (hx : SuppQ P x) (h : ∀ A, x A = 0 → y A = 0) : SuppQ P y :=
  fun A hA => hx A fun h0 => hA (h A h0)

theorem deg_of (j : ℕ) {x y : Cq n V} (hx : DegQ j x) (h : ∀ A, x A = 0 → y A = 0) : DegQ j y :=
  fun A hA => hx A fun h0 => hA (h A h0)

end Acyc

section Acyc2

variable {Z : Type} [AddCommGroup Z] [Module ℂ Z]

theorem acycQ (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ Z) (a d : Lt n → Module.End ℂ Z)
    (Fil : ℕ → Submodule ℂ Z) (hE : PairRel E1 E2) (hF : FiltR (Tl E1 E2) a d Fil) (j : ℕ) (x : Cq n Z)
    (hxs : SuppQ (inUL lev) x) (hxd : DegQ (j + 1) x) (hcyc : bdq E1 E2 x = 0) :
    ∃ t : Cq n Z, SuppQ (inUL lev) t ∧ DegQ (j + 2) t ∧ bdq E1 E2 t = x := by
  let I := {i : Lt n // inUL lev i}
  have hS : bdq E1 E2 * bdq E1 E2 = 0 := bdq_sq hE
  let H : Module.End ℂ (Cq n Z) := ∑ i : I, (liftq n (d i.1) : Module.End ℂ (Cq n Z)) * creq i.1
  let Da : Module.End ℂ (Cq n Z) := ∑ i : I, (liftq n (a i.1) : Module.End ℂ (Cq n Z)) * annq i.1
  let N : Module.End ℂ Z := ∑ i : I, a i.1 * d i.1
  let G : ℕ → Submodule ℂ Z := fun k => Nat.casesOn k ⊥ Fil
  have hda : ∀ i j : I, d i.1 * a j.1 - a j.1 * d i.1 = if i = j then 1 else 0 := fun i j => by
    rw [hF.da i.1 j.1]; simp only [Subtype.ext_iff (a1 := i)]
  have hdG : ∀ i k, ∀ z ∈ G (k + 1), d i z ∈ G k := fun i k z hz => by
    cases k with
    | zero => exact hF.d_zero i z hz
    | succ k => exact hF.d_mem i k z hz
  have hNG : ∀ k, ∀ z ∈ G k, N z ∈ G k := fun k z hz => by
    cases k with
    | zero => obtain rfl : z = 0 := hz; simp
    | succ k =>
      rw [LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun i _ => ?_
      cases k with
      | zero => rw [Module.End.mul_apply, hF.d_zero _ z hz, map_zero]; exact Submodule.zero_mem _
      | succ k => exact hF.a_mem _ k _ (hF.d_mem _ k z hz)
  have hrG : ∀ i k, ∀ z ∈ G k, Tl E1 E2 i z - a i z ∈ G k := fun i k z hz => by
    cases k with
    | zero => obtain rfl : z = 0 := hz; simp
    | succ k => exact hF.r_mem i k z hz
  have hGf : ∀ k, G k ≤ GlobalTheory.CompanionTheory.DSICKoszul.filt (fun i : I => d i.1) k := fun k => by
    induction k with
    | zero => exact bot_le
    | succ k ih => exact fun z hz => (GlobalTheory.CompanionTheory.DSICKoszul.mem_filt_succ _ _ _).2 fun i => ih (hdG _ k z hz)
  have hGm : ∀ k, G k ≤ G (k + 1) := fun k => by
    cases k with
    | zero => exact bot_le
    | succ k => exact hF.mono (Nat.le_succ k)
  have hH : ∀ (y : Cq n Z) A, H y A = ∑ i : I, d i.1 (creq i.1 y A) := fun y A => by
    simp only [H, LinearMap.sum_apply, Finset.sum_apply]; rfl
  have hHG : ∀ k (y : Cq n Z), (∀ A, y A ∈ G (k + 1)) → ∀ A, H y A ∈ G k := fun k y hy A => by
    rw [hH]; exact Submodule.sum_mem _ fun i _ => hdG _ k _ (cre_mem hy _ _)
  have hρ : ∀ k (y : Cq n Z), (∀ A, y A ∈ G k) → SuppQ (inUL lev) y → ∀ A, (bdq E1 E2 y - Da y) A ∈ G k :=
      fun k y hy hys A => by
    have e : Da y A = ∑ i : Lt n, if inUL lev i then a i (annq i y A) else 0 := by
      rw [← Finset.sum_filter, Finset.sum_subtype (p := inUL lev) _ (by simp)]
      simp only [Da, LinearMap.sum_apply, Finset.sum_apply]; rfl
    have e2 : bdq E1 E2 y A = ∑ i : Lt n, Tl E1 E2 i (annq i y A) +
        (1 / 2 : ℂ) • ∑ i : Lt n, ∑ j : Lt n, ∑ k : Lt n, cq i j k • creq k (annq j (annq i y)) A := by
      rw [bd_apply]
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, lift_apply]
    rw [Pi.sub_apply, e2, e, add_sub_right_comm, ← Finset.sum_sub_distrib]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => ?_) (Submodule.smul_mem _ _
      (Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (cre_mem (ann_mem (ann_mem hy _) _) _ _)))
    by_cases hi : inUL lev i
    · rw [if_pos hi]
      exact hrG i _ _ (ann_mem hy _ _)
    · have e0 : annq i y A = 0 := by
        by_contra h0
        exact hi (hys _ (ann_ne h0).2 i (mem_insert_self _ _))
      rw [if_neg hi, e0]
      simp
  have hom : Da * H + H * Da =
      ∑ i : I, (liftq n (a i.1) : Module.End ℂ (Cq n Z)) * liftq n (d i.1) + ∑ i : I, creq i.1 * annq i.1 := by
    refine GlobalTheory.CompanionTheory.DSICKoszul.homotopy_ring (fun i : I => (liftq n (a i.1) : Module.End ℂ (Cq n Z))) (fun i => liftq n (d i.1))
      (fun i => annq i.1) (fun i => creq i.1) (fun i j => (lift_ann _ _).symm)
      (fun i j => (lift_cre _ _).symm) (fun i j => ?_) (fun i j => ?_)
    · refine LinearMap.ext fun y => funext fun A => ?_
      have e := congrArg (fun T : Module.End ℂ Z => T (y A)) (hda i j)
      by_cases h : i = j
      · simpa [h, lift_apply] using e
      · simpa [h, lift_apply] using e
    · rw [ann_cre]; simp only [Subtype.ext_iff (a1 := i)]
  have hHs : ∀ y : Cq n Z, SuppQ (inUL lev) y → DegQ (j + 1) y →
      SuppQ (inUL lev) (H y) ∧ DegQ (j + 2) (H y) := fun y hys hyd => by
    have key : ∀ A, H y A ≠ 0 → ∃ i : I, i.1 ∈ A ∧ y (A.erase i.1) ≠ 0 := fun A hA => by
      rw [hH] at hA
      obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero hA
      exact ⟨i, cre_ne (fun h => hi (by rw [h, map_zero]) : creq i.1 y A ≠ 0)⟩
    refine ⟨fun A hA l hl => ?_, fun A hA => ?_⟩
    · obtain ⟨i, h1, h2⟩ := key A hA
      by_cases e : l = i.1
      · exact e ▸ i.2
      · exact hys _ h2 l (mem_erase.2 ⟨e, hl⟩)
    · obtain ⟨i, h1, h2⟩ := key A hA
      have := hyd _ h2
      have h3 := card_erase_add_one h1
      omega
  have hΔ : ∀ y : Cq n Z, SuppQ (inUL lev) y → DegQ (j + 1) y → bdq E1 E2 y = 0 → ∀ A,
      bdq E1 E2 (H y) A =
      N (y A) + ((j + 1 : ℕ) : ℂ) • y A + ((bdq E1 E2 (H y) - Da (H y)) A + H (bdq E1 E2 y - Da y) A) := by
    intro y hys hyd hc A
    have e := congrArg (fun T : Module.End ℂ (Cq n Z) => T y A) hom
    simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.sum_apply, Finset.sum_apply,
      cre_ann_apply, lift_apply] at e
    have e2 : (∑ i : I, if i.1 ∈ A then y A else 0) = ((j + 1 : ℕ) : ℂ) • y A := by
      by_cases h : y A = 0
      · simp [h]
      · rw [← hyd A h, ← Finset.sum_subtype (univ.filter (inUL lev)) (p := inUL lev) (by simp)
          (fun i => if i ∈ A then y A else 0), ← Finset.sum_filter, Finset.sum_const, Nat.cast_smul_eq_nsmul]
        congr 2
        ext i
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨fun h' => h'.2, fun h' => ⟨hys A h i h', h'⟩⟩
    have e3 : N (y A) = ∑ i : I, a i.1 (d i.1 (y A)) := by simp only [N, LinearMap.sum_apply]; rfl
    rw [e3, ← e2, ← e, hc, zero_sub, map_neg, Pi.sub_apply, Pi.neg_apply]
    abel
  have main : ∀ k (y : Cq n Z), (∀ A, y A ∈ G k) → SuppQ (inUL lev) y → DegQ (j + 1) y →
      bdq E1 E2 y = 0 →
      ∃ t : Cq n Z, SuppQ (inUL lev) t ∧ DegQ (j + 2) t ∧ bdq E1 E2 t = y := by
    intro k
    induction k with
    | zero =>
      exact fun y hy _ _ _ => ⟨0, fun _ h => absurd rfl h, fun _ h => absurd rfl h, by
        rw [map_zero]; exact (funext hy).symm⟩
    | succ k ihk =>
      have inner : ∀ m (y : Cq n Z), (∀ A, y A ∈ G (k + 1)) →
          (∀ A, y A ∈ GlobalTheory.CompanionTheory.DSICKoszul.filt (fun i : I => d i.1) m ⊔ G k) →
          SuppQ (inUL lev) y → DegQ (j + 1) y → bdq E1 E2 y = 0 →
          ∃ t : Cq n Z, SuppQ (inUL lev) t ∧ DegQ (j + 2) t ∧ bdq E1 E2 t = y := by
        intro m
        induction m with
        | zero => exact fun y _ hy => ihk y fun A => by simpa [GlobalTheory.CompanionTheory.DSICKoszul.filt] using hy A
        | succ m ih =>
          intro y hy1 hy2 hs hd hc
          have hne : ((m : ℂ) + (j + 1 : ℕ)) ≠ 0 := by exact_mod_cast (by omega : m + (j + 1) ≠ 0)
          have hHy := hHs y hs hd
          have hbs : SuppQ (inUL lev) (bdq E1 E2 y) := bd_supp E1 E2 (cq_closed (inUL_sub lev)) hs
          have hL : ∀ A, (bdq E1 E2 (H y) - Da (H y)) A + H (bdq E1 E2 y - Da y) A ∈ G k := fun A =>
            Submodule.add_mem _ (hρ k _ (hHG k y hy1) hHy.1 A) (hHG k _ (hρ (k + 1) y hy1 hs) A)
          have hw : ∀ A, (bdq E1 E2 (H y) - ((m : ℂ) + (j + 1 : ℕ)) • y) A =
              (N (y A) - (m : ℂ) • y A) + ((bdq E1 E2 (H y) - Da (H y)) A + H (bdq E1 E2 y - Da y) A) :=
              fun A => by
            rw [Pi.sub_apply, hΔ y hs hd hc A, Pi.smul_apply, add_smul]
            abel
          have hsm : ∀ c : ℂ, ∀ A, y A = 0 → (c • y) A = 0 := fun c A h => by simp [h]
          obtain ⟨t, ht, ht2, hbt⟩ := ih (bdq E1 E2 (H y) - ((m : ℂ) + (j + 1 : ℕ)) • y)
            (fun A => by
              rw [hw]
              exact Submodule.add_mem _ (Submodule.sub_mem _ (hNG (k + 1) _ (hy1 A)) (Submodule.smul_mem _ _ (hy1 A)))
                (hGm k (hL A)))
            (fun A => by
              rw [hw]
              obtain ⟨u, hu, g, hg, e⟩ := Submodule.mem_sup.1 (hy2 A)
              refine Submodule.add_mem _ ?_ (Submodule.mem_sup_right (hL A))
              rw [← e, map_add, smul_add, add_sub_add_comm]
              exact Submodule.add_mem_sup
                (GlobalTheory.CompanionTheory.DSICKoszul.euler_filt (fun i : I => a i.1) _ (fun i j => hF.d_comm _ _) hda m u hu)
                (Submodule.sub_mem _ (hNG _ _ hg) (Submodule.smul_mem _ _ hg)))
            (supp_sub (bd_supp E1 E2 (cq_closed (inUL_sub lev)) hHy.1) (supp_of hs (hsm _)))
            (deg_sub (bd_deg E1 E2 hHy.2) (deg_of _ hd (hsm _)))
            (by
              rw [map_sub, map_smul, hc, smul_zero, sub_zero]
              exact LinearMap.congr_fun hS _)
          have hsub : ∀ A, (H y - t) A = 0 → (((m : ℂ) + (j + 1 : ℕ))⁻¹ • (H y - t)) A = 0 := fun A h => by
            simp [h]
          refine ⟨((m : ℂ) + (j + 1 : ℕ))⁻¹ • (H y - t), supp_of (supp_sub hHy.1 ht) hsub,
            deg_of _ (deg_sub hHy.2 ht2) hsub, ?_⟩
          rw [map_smul, map_sub, hbt, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hne, one_smul]
      exact fun y hy => inner (k + 1) y hy fun A => Submodule.mem_sup_left (hGf _ (hy A))
  choose f hf using hF.exh
  exact main ((univ.sup fun A => f (x A)) + 1) x
    (fun A => hF.mono (Finset.le_sup (f := fun A => f (x A)) (mem_univ A)) (hf _)) hxs hxd hcyc

end Acyc2

section Free

theorem freeQ (n : ℕ) : ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (P1 P2 : Fin n → Fin n → Module.End ℂ W)
    (χ : W →ₗ[ℂ] ℂ) (w₀ : W) (a d : Lt n → Module.End ℂ W) (Fil : ℕ → Submodule ℂ W),
    PairRel P1 P2 ∧ χ w₀ = 1 ∧ (∀ c e w, χ (P1 c e w) = 0) ∧ (∀ c e w, χ (P2 c e w) = 0) ∧
      FiltR (Tl P1 P2) a d Fil := by
  obtain ⟨W, _, _, P1, P2, χ, w₀, a, d, Fil, hP, h1, h01, h02, hF⟩ := GlobalTheory.CompanionTheory.RealMult.CovR.freeR n
  let al : Bool → ℂ := fun s => if s then 0 else -2
  let be : Bool → ℂ := fun s => if s then 1 else 0
  let ga : Bool → ℂ := fun s => if s then 1 / 2 else -1 / 2
  let a' : Lt n → Module.End ℂ W := fun l => a (true, l.2) + al l.1 • a (false, l.2)
  let d' : Lt n → Module.End ℂ W := fun l => be l.1 • d (true, l.2) + ga l.1 • d (false, l.2)
  refine ⟨W, inferInstance, inferInstance, P1, P2, χ, w₀, a', d', Fil, ⟨hP.gl1, hP.gl2, fun a b c e => hP.comm a b c e⟩,
    h1, h01, h02, ⟨?_, ?_, ?_, hF.mono, hF.exh, ?_, ?_, ?_, ?_⟩⟩
  · exact fun i j => ((hF.a_comm _ _).add_right ((hF.a_comm _ _).smul_right _)).add_left
      (((hF.a_comm _ _).add_right ((hF.a_comm _ _).smul_right _)).smul_left _)
  · exact fun i j => ((((hF.d_comm _ _).smul_right _).smul_left _).add_right (((hF.d_comm _ _).smul_right _).smul_left _)).add_left
      ((((hF.d_comm _ _).smul_right _).smul_left _).add_right (((hF.d_comm _ _).smul_right _).smul_left _))
  · rintro ⟨s, p⟩ ⟨t, q⟩
    have hD : ∀ u v : Bool, d (u, p) * a (v, q) = a (v, q) * d (u, p) + if (u, p) = (v, q) then 1 else 0 := fun u v => by
      rw [← hF.da (u, p) (v, q)]; abel
    simp only [a', d', add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hD, smul_add]
    by_cases h : p = q
    · subst h
      cases s <;> cases t <;> simp [al, be, ga] <;> module
    · cases s <;> cases t <;> simp [al, be, ga, h] <;> module
  · exact fun i k z hz => Submodule.add_mem _ (hF.a_mem _ k z hz) (Submodule.smul_mem _ _ (hF.a_mem _ k z hz))
  · rintro ⟨s, p⟩ k z hz
    have e : Tl P1 P2 (s, p) z - a' (s, p) z = (GlobalTheory.CompanionTheory.RealMult.rl P1 P2 (true, p) z - a (true, p) z) +
        al s • (GlobalTheory.CompanionTheory.RealMult.rl P1 P2 (false, p) z - a (false, p) z) := by
      cases s <;> simp [Tl, Ts, GlobalTheory.CompanionTheory.RealMult.rl, a', al] <;> module
    rw [e]
    exact Submodule.add_mem _ (hF.r_mem _ k z hz) (Submodule.smul_mem _ _ (hF.r_mem _ k z hz))
  · exact fun i k z hz => Submodule.add_mem _ (Submodule.smul_mem _ _ (hF.d_mem _ k z hz))
      (Submodule.smul_mem _ _ (hF.d_mem _ k z hz))
  · intro i z hz
    simp [d', hF.d_zero _ z hz]

open scoped TensorProduct in

theorem coverQ (lev : Fin n → ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V)
    (hE : PairRel E1 E2) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (F1 F2 : Fin n → Fin n → Module.End ℂ Y) (π : Y →ₗ[ℂ] V),
      PairRel F1 F2 ∧ Function.Surjective π ∧ (∀ a b y, π (F1 a b y) = E1 a b (π y)) ∧
      (∀ a b y, π (F2 a b y) = E2 a b (π y)) ∧
      ∀ (j : ℕ) (x : Cq n Y), SuppQ (inUL lev) x → DegQ (j + 1) x → bdq F1 F2 x = 0 →
        ∃ t : Cq n Y, SuppQ (inUL lev) t ∧ DegQ (j + 2) t ∧ bdq F1 F2 t = x := by
  obtain ⟨W, _, _, P1, P2, χ, w₀, a, d, Fil, hP, h1, h01, h02, hF⟩ := freeQ n
  let F1 : Fin n → Fin n → Module.End ℂ (V ⊗[ℂ] W) := fun c e => (E1 c e).rTensor W + (P1 c e).lTensor V
  let F2 : Fin n → Fin n → Module.End ℂ (V ⊗[ℂ] W) := fun c e => (E2 c e).rTensor W + (P2 c e).lTensor V
  have hPair : PairRel F1 F2 := by
    refine ⟨fun a' b c e => CompanionTheory.D.LK.kRel_tens (ε := CompanionTheory.D.LK.allT n) (fun a b c d _ _ => hE.1 a b c d) hP.1
        a' b c e rfl rfl, fun a' b c e => CompanionTheory.D.LK.kRel_tens (ε := CompanionTheory.D.LK.allT n)
        (fun a b c d _ _ => hE.2.1 a b c d) hP.2.1 a' b c e rfl rfl, fun a' b c e => ?_⟩
    show _ * _ = _ * _
    apply TensorProduct.ext'
    intro v w
    have e1 := LinearMap.congr_fun (hE.2.2 a' b c e).eq v
    have e2 := LinearMap.congr_fun (hP.2.2 a' b c e).eq w
    simp only [Module.End.mul_apply] at e1 e2
    simp only [F1, F2, Module.End.mul_apply, LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      map_add, e1, e2, TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel
  let S : ℕ → Set (V ⊗[ℂ] W) := fun k => {t | ∃ v z, z ∈ Fil k ∧ t = v ⊗ₜ z}
  have hin : ∀ {k : ℕ} (v : V) {z : W}, z ∈ Fil k → v ⊗ₜ[ℂ] z ∈ Submodule.span ℂ (S k) :=
    fun v _ hz => Submodule.subset_span ⟨_, _, hz, rfl⟩
  have hmap : ∀ (T : Module.End ℂ (V ⊗[ℂ] W)) (k : ℕ) (Q : Submodule ℂ (V ⊗[ℂ] W)),
      (∀ v z, z ∈ Fil k → T (v ⊗ₜ z) ∈ Q) → ∀ t ∈ Submodule.span ℂ (S k), T t ∈ Q := by
    intro T k Q h
    refine fun t ht => (Submodule.span_le (p := Q.comap T)).2 ?_ ht
    rintro _ ⟨v, z, hz, rfl⟩
    exact h v z hz
  have hm : Monotone fun k => Submodule.span ℂ (S k) := fun k l hkl =>
    Submodule.span_mono (by rintro _ ⟨v, z, hz, rfl⟩; exact ⟨v, z, hF.mono hkl hz, rfl⟩)
  have hFY : FiltR (Tl F1 F2) (fun i => (a i).lTensor V) (fun i => (d i).lTensor V)
      (fun k => Submodule.span ℂ (S k)) := by
    refine ⟨?_, ?_, ?_, hm, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun i j => (hF.a_comm i j).map (Module.End.lTensorAlgHom ℂ W V)
    · exact fun i j => (hF.d_comm i j).map (Module.End.lTensorAlgHom ℂ W V)
    · intro i j
      have := congrArg (Module.End.lTensorAlgHom ℂ W V) (hF.da i j)
      rw [map_sub, map_mul, map_mul, apply_ite (Module.End.lTensorAlgHom ℂ W V), map_one, map_zero] at this
      exact this
    · intro t
      induction t using TensorProduct.induction_on with
      | zero => exact ⟨0, Submodule.zero_mem _⟩
      | tmul v z =>
        obtain ⟨k, hk⟩ := hF.exh z
        exact ⟨_, hin v hk⟩
      | add p q hp hq =>
        obtain ⟨k, hk⟩ := hp
        obtain ⟨l, hl⟩ := hq
        exact ⟨max k l, Submodule.add_mem _ (hm (le_max_left _ _) hk) (hm (le_max_right _ _) hl)⟩
    · exact fun i k => hmap _ k _ fun v z hz => hin v (hF.a_mem i _ z hz)
    · intro i k
      refine hmap (Tl F1 F2 i - (a i).lTensor V) k _ fun v z hz => ?_
      have e : (Tl F1 F2 i - (a i).lTensor V : Module.End ℂ (V ⊗[ℂ] W)) (v ⊗ₜ z) =
          Tl E1 E2 i v ⊗ₜ z + v ⊗ₜ (Tl P1 P2 i z - a i z) := by
        obtain ⟨s, p⟩ := i
        cases s <;> simp only [Tl, Ts, F1, F2, Bool.false_eq_true, if_false, if_true, LinearMap.sub_apply,
          LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.tmul_sub,
          TensorProduct.add_tmul, TensorProduct.sub_tmul, TensorProduct.tmul_add, TensorProduct.tmul_sub] <;> abel
      rw [e]
      exact Submodule.add_mem _ (hin _ hz) (hin _ (hF.r_mem i _ z hz))
    · exact fun i k => hmap _ _ _ fun v z hz => hin v (hF.d_mem i _ z hz)
    · exact fun i => hmap _ _ ⊥ fun v z hz => by simp [hF.d_zero i z hz]
  refine ⟨V ⊗[ℂ] W, inferInstance, inferInstance, F1, F2,
    (TensorProduct.rid ℂ V).toLinearMap ∘ₗ χ.lTensor V, hPair, fun v => ⟨v ⊗ₜ w₀, by simp [h1]⟩,
    fun c e t => ?_, fun c e t => ?_, fun j x hs hx hc =>
      acycQ lev F1 F2 _ _ _ hPair hFY j x hs hx hc⟩
  · induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul v f => simp [F1, h01]
    | add p q hp hq => simp only [map_add, hp, hq]
  · induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul v f => simp [F2, h02]
    | add p q hp hq => simp only [map_add, hp, hq]

end Free

end GlobalTheory.CompanionTheory.PairMult.COU
