import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionAction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPermOfMapEq

open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.KostL

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open GlobalTheory.CompanionTheory.RealMult.Kost
open CompanionTheory.D.LK (Pos Cn Sup Wt bd lift allT Ft InN ev evK evd Ref key sg ann cre cpt wt om)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
open Formalism.REAL (GlRel KHighest IsWeight etr)

variable {n : ℕ}

def embK : Pos n ↪ Lt n := ⟨fun i => (false, i), fun _ _ h => (Prod.mk.inj h).2⟩

def kpart (S : Finset (Lt n)) : Finset (Pos n) := univ.filter fun i => ((false, i) : Lt n) ∈ S

abbrev ppart (S : Finset (Lt n)) : Finset (Lt n) := S.filter fun l => l.1 = true

theorem mem_map_embK {A : Finset (Pos n)} {b : Bool} {i : Pos n} : (b, i) ∈ A.map embK ↔ b = false ∧ i ∈ A := by
  simp only [mem_map]
  constructor
  · rintro ⟨j, hj, e⟩
    obtain ⟨h1, h2⟩ := Prod.mk.inj e
    exact ⟨h1.symm, h2 ▸ hj⟩
  · rintro ⟨rfl, h⟩
    exact ⟨i, h, rfl⟩

theorem mem_kpart {S : Finset (Lt n)} {i : Pos n} : i ∈ kpart S ↔ ((false, i) : Lt n) ∈ S := by
  simp [kpart]

theorem kpart_insert (i : Pos n) (S : Finset (Lt n)) :
    kpart (insert ((false, i) : Lt n) S) = insert i (kpart S) := by
  ext j
  simp [kpart]

theorem kpart_erase (i : Pos n) (S : Finset (Lt n)) :
    kpart (S.erase ((false, i) : Lt n)) = (kpart S).erase i := by
  ext j
  simp [kpart]

theorem ppart_insert (i : Pos n) (S : Finset (Lt n)) :
    ppart (insert ((false, i) : Lt n) S) = ppart S := by
  ext l
  simp only [mem_filter, mem_insert]
  constructor
  · rintro ⟨rfl | h, h2⟩
    · simp at h2
    · exact ⟨h, h2⟩
  · rintro ⟨h, h2⟩
    exact ⟨Or.inr h, h2⟩

theorem ppart_erase (i : Pos n) (S : Finset (Lt n)) :
    ppart (S.erase ((false, i) : Lt n)) = ppart S := by
  ext l
  simp only [mem_filter, mem_erase]
  constructor
  · rintro ⟨⟨-, h⟩, h2⟩
    exact ⟨h, h2⟩
  · rintro ⟨h, h2⟩
    refine ⟨⟨?_, h⟩, h2⟩
    rintro rfl
    simp at h2

theorem kpart_emb {B : Finset (Lt n)} (hB : ∀ l ∈ B, l.1 = true) (A : Finset (Pos n)) :
    kpart (A.map embK ∪ B) = A := by
  ext i
  simp only [mem_kpart, mem_union, mem_map]
  constructor
  · rintro (⟨j, hj, e⟩ | h)
    · have : j = i := (Prod.mk.inj e).2
      exact this ▸ hj
    · simpa using hB _ h
  · exact fun h => Or.inl ⟨i, h, rfl⟩

theorem ppart_emb {B : Finset (Lt n)} (hB : ∀ l ∈ B, l.1 = true) (A : Finset (Pos n)) :
    ppart (A.map embK ∪ B) = B := by
  ext l
  simp only [mem_filter, mem_union, mem_map]
  constructor
  · rintro ⟨⟨j, -, rfl⟩ | h, h2⟩
    · simp [embK] at h2
    · exact h
  · exact fun h => ⟨Or.inr h, hB l h⟩

theorem emb_split (S : Finset (Lt n)) : (kpart S).map embK ∪ ppart S = S := by
  ext ⟨b, i⟩
  simp only [mem_union, mem_map_embK, mem_filter, mem_kpart]
  cases b <;> simp

theorem key_lt (i : Pos n) : key i < n * n := by
  have h1 := i.1.1.2
  have h2 := i.1.2.2
  have : (i.1.1 : ℕ) * n + n ≤ n * n := by nlinarith
  simp only [key]
  omega

theorem sgL_false (i : Pos n) (S : Finset (Lt n)) : sgL ((false, i) : Lt n) S = sg i (kpart S) := by
  have e : S.filter (fun m => keyL m < keyL ((false, i) : Lt n)) = ((kpart S).filter fun j => key j < key i).map embK := by
    ext ⟨b, j⟩
    cases b
    · simp only [mem_filter, mem_map_embK, mem_kpart, keyL]
      simp
    · have := key_lt i
      simp only [mem_filter, mem_map_embK, keyL]
      simp
      omega
  unfold sgL sg
  rw [e, card_map]

theorem card_split (P : Pos n → Prop) [DecidablePred P] (S : Finset (Lt n)) :
    (S.filter fun l => P l.2).card = ((kpart S).filter P).card + ((ppart S).filter fun l => P l.2).card := by
  have e : (S.filter fun l => P l.2) = ((kpart S).filter P).map embK ∪ (ppart S).filter fun l => P l.2 := by
    ext ⟨b, i⟩
    simp only [mem_union, mem_map_embK, mem_filter, mem_kpart]
    cases b <;> simp
  rw [e, card_union_of_disjoint, card_map]
  rw [Finset.disjoint_left]
  rintro ⟨b, i⟩ h1 h2
  simp only [mem_map, mem_filter] at h1 h2
  obtain ⟨j, -, e⟩ := h1
  have : b = false := (Prod.mk.inj e).1.symm
  simp [this] at h2

theorem card_parts (S : Finset (Lt n)) : S.card = (kpart S).card + (ppart S).card := by
  have := card_split (fun _ : Pos n => True) S
  simpa using this

theorem wtL_split (S : Finset (Lt n)) (c : Fin n) : wtL S c = wt (kpart S) c + wtL (ppart S) c := by
  have h1 := card_split (fun i : Pos n => i.1.1 = c) S
  have h2 := card_split (fun i : Pos n => i.1.2 = c) S
  simp only [wtL, wt, h1, h2]
  push_cast
  ring

section Chains

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def frC (B : Finset (Lt n)) : Cn n V →ₗ[ℂ] Cq n V where
  toFun y := fun S => if ppart S = B then y (kpart S) else 0
  map_add' x y := by
    funext S
    by_cases h : ppart S = B <;> simp [h]
  map_smul' c x := by
    funext S
    by_cases h : ppart S = B <;> simp [h]

def toC (B : Finset (Lt n)) (x : Cq n V) : Cn n V := fun A => x (A.map embK ∪ B)

theorem frC_apply (B : Finset (Lt n)) (y : Cn n V) (S : Finset (Lt n)) :
    frC B y S = if ppart S = B then y (kpart S) else 0 := rfl

theorem toC_frC {B : Finset (Lt n)} (hB : ∀ l ∈ B, l.1 = true) (y : Cn n V) : toC B (frC B y) = y := by
  funext A
  simp only [toC, frC_apply, ppart_emb hB, kpart_emb hB, if_true]

theorem frC_toC {B : Finset (Lt n)} {x : Cq n V} (hx : PartL B x) : frC B (toC B x) = x := by
  funext S
  rw [frC_apply]
  split_ifs with h
  · simp only [toC]
    rw [← h, emb_split]
  · by_contra hne
    exact h (hx S (Ne.symm hne))

theorem frC_ann (B : Finset (Lt n)) (i : Pos n) (y : Cn n V) :
    frC B (ann i y) = annL ((false, i) : Lt n) (frC B y) := by
  funext S
  show (if ppart S = B then (if i ∈ kpart S then 0 else sg i (kpart S) • y (insert i (kpart S))) else 0) =
    if ((false, i) : Lt n) ∈ S then 0 else sgL ((false, i) : Lt n) S • frC B y (insert ((false, i) : Lt n) S)
  rw [frC_apply, ppart_insert, kpart_insert, sgL_false]
  by_cases h : ppart S = B <;> by_cases h2 : ((false, i) : Lt n) ∈ S <;> simp [h, h2, mem_kpart]

theorem frC_cre (B : Finset (Lt n)) (i : Pos n) (y : Cn n V) :
    frC B (cre i y) = creL ((false, i) : Lt n) (frC B y) := by
  funext S
  show (if ppart S = B then (if i ∈ kpart S then sg i (kpart S) • y ((kpart S).erase i) else 0) else 0) =
    if ((false, i) : Lt n) ∈ S then sgL ((false, i) : Lt n) S • frC B y (S.erase ((false, i) : Lt n)) else 0
  rw [frC_apply, ppart_erase, kpart_erase, sgL_false]
  by_cases h : ppart S = B <;> by_cases h2 : ((false, i) : Lt n) ∈ S <;> simp [h, h2, mem_kpart]

theorem frC_lift (B : Finset (Lt n)) (T : Module.End ℂ V) (y : Cn n V) :
    frC B (lift n T y) = liftL n T (frC B y) := by
  funext S
  show (if ppart S = B then T (y (kpart S)) else 0) = T (if ppart S = B then y (kpart S) else 0)
  split_ifs <;> simp

theorem bdL_isK (E1 E2 : Fin n → Fin n → Module.End ℂ V) :
    bdL isK E1 E2 = (∑ i : Pos n, (liftL n (kA E1 E2 i.1.1 i.1.2) : Module.End ℂ (Cq n V)) * annL ((false, i) : Lt n)) +
      ∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
        if i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then
          creL ((false, k) : Lt n) * annL ((false, j) : Lt n) * annL ((false, i) : Lt n) else 0 := by
  unfold bdL
  congr 1
  · simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    simp [isK, xL]
  · simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    simp [isK]

theorem frC_bd (B : Finset (Lt n)) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (y : Cn n V) :
    frC B (bd (allT n) (kA E1 E2) y) = bdL isK E1 E2 (frC B y) := by
  rw [bdL_isK]
  simp only [bd, cpt, true_and, if_true, LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum,
    Module.End.mul_apply]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [frC_lift, frC_ann]
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    split_ifs
    · simp only [Module.End.mul_apply, frC_cre, frC_ann]
    · simp

theorem part_frC (B : Finset (Lt n)) (y : Cn n V) : PartL B (frC B y) := fun S h => by
  by_contra h2
  exact h (by rw [frC_apply, if_neg h2])

theorem deg_frC {B : Finset (Lt n)} {j : ℕ} {y : Cn n V} (hy : Sup (allT n) ∅ j y) : DegL (j + B.card) (frC B y) := by
  intro S h
  have h1 : ppart S = B := part_frC B y S h
  rw [frC_apply, if_pos h1] at h
  have h2 := (hy _ h).2
  rw [Finset.filter_true_of_mem (fun _ _ => rfl)] at h2
  rw [card_parts S, h2, h1]

theorem sup_toC {B : Finset (Lt n)} (hB : ∀ l ∈ B, l.1 = true) {j : ℕ} {x : Cq n V} (hx : DegL (j + B.card) x) :
    Sup (allT n) ∅ j (toC B x) := by
  intro A h
  refine ⟨by simp [cpt], ?_⟩
  have h1 := hx _ h
  rw [card_parts, kpart_emb hB, ppart_emb hB] at h1
  rw [Finset.filter_true_of_mem (fun _ _ => rfl)]
  omega

theorem wt_toC {B : Finset (Lt n)} (hB : ∀ l ∈ B, l.1 = true) (E1 E2 : Fin n → Fin n → Module.End ℂ V)
    {τ : Fin n → ℝ} {x : Cq n V} (hx : WtL E1 E2 τ x) : Wt (allT n) (kA E1 E2) (τ - wtL B) (toC B x) := by
  intro c
  funext A
  have h := congrFun (hx c) (A.map embK ∪ B)
  change kA E1 E2 c c (x (A.map embK ∪ B)) + (wtL (A.map embK ∪ B) c : ℂ) • x (A.map embK ∪ B) =
    (τ c : ℂ) • x (A.map embK ∪ B) at h
  rw [wtL_split, kpart_emb hB, ppart_emb hB] at h
  change kA E1 E2 c c (x (A.map embK ∪ B)) + (wt (A.filter (cpt (allT n))) c : ℂ) • x (A.map embK ∪ B) =
    (((τ - wtL B) c : ℝ) : ℂ) • x (A.map embK ∪ B)
  rw [Finset.filter_true_of_mem (fun _ _ => rfl), Pi.sub_apply, Complex.ofReal_sub, sub_smul, eq_sub_iff_add_eq, add_assoc,
    ← add_smul, ← Complex.ofReal_add, h]

theorem wt_frC {B : Finset (Lt n)} (E1 E2 : Fin n → Fin n → Module.End ℂ V)
    {τ : Fin n → ℝ} {y : Cn n V} (hy : Wt (allT n) (kA E1 E2) (τ - wtL B) y) : WtL E1 E2 τ (frC B y) := by
  intro c
  funext S
  change kA E1 E2 c c (frC B y S) + (wtL S c : ℂ) • frC B y S = (τ c : ℂ) • frC B y S
  rw [frC_apply]
  split_ifs with h
  · have h1 := congrFun (hy c) (kpart S)
    change kA E1 E2 c c (y (kpart S)) + (wt ((kpart S).filter (cpt (allT n))) c : ℂ) • y (kpart S) =
      (((τ - wtL B) c : ℝ) : ℂ) • y (kpart S) at h1
    rw [Finset.filter_true_of_mem (fun _ _ => rfl), Pi.sub_apply, Complex.ofReal_sub, sub_smul, eq_sub_iff_add_eq,
      add_assoc, ← add_smul, ← Complex.ofReal_add] at h1
    rw [wtL_split, h]
    exact h1
  · simp

end Chains

def bPairs (B : Finset (Lt n)) : Finset (Fin n × Fin n) := B.image fun l => l.2.1

theorem wtB_bPairs {B : Finset (Lt n)} (hB : ∀ l ∈ B, l.1 = true) : wtB (bPairs B) = wtL B := by
  have hinj : Set.InjOn (fun l : Lt n => l.2.1) (B : Set (Lt n)) := by
    rintro ⟨b, i⟩ h1 ⟨c, k⟩ h2 e
    have e1 : b = true := hB _ h1
    have e2 : c = true := hB _ h2
    have e3 : i = k := Subtype.ext e
    rw [e1, e2, e3]
  funext c
  have h (f : Lt n → Fin n × Fin n) (hf : f = fun l => l.2.1) (P : Fin n × Fin n → Prop) [DecidablePred P] :
      ((bPairs B).filter P).card = (B.filter fun l => P l.2.1).card := by
    subst hf
    rw [bPairs, Finset.filter_image, Finset.card_image_of_injOn (hinj.mono fun x hx => by simp at hx; exact hx.1)]
  simp only [wtB, wtL, h _ rfl]

theorem isN2_of_gelfand_values_eq (lam : Fin n → ℤ) (lev : Fin n → ℕ) (B : Finset (Fin n × Fin n)) (hB : B.Nonempty)
    (hBl : ∀ p ∈ B, lev p.1 < lev p.2) (ν : Fin n → ℝ) (hdom : ∀ c d : Fin n, c < d → ν d ≤ ν c)
    (hm : ∀ k, GlobalTheory.Dec.gelfVal (chiHW ν) k = GlobalTheory.Dec.gelfVal (chiOf (muQ lam lev + (2 : ℝ) • rhoV n - wtB B)) k) :
    IsSecondTypeWeight lam lev ν := by
  classical
  obtain ⟨w, hw⟩ := exists_perm_of_map_eq _ _ (GlobalTheory.GelfandInj.gelfVal_multiset_eq n _ _ fun k => hm (k + 1))
  refine ⟨B, hB, hBl, fun c d hcd => ?_, w, ?_⟩
  · have h1 := hdom c d hcd
    have h2 : ((c : ℕ) : ℝ) < (d : ℕ) := by exact_mod_cast hcd
    simp only [Pi.add_apply, rhoV]
    linarith
  · funext a
    have h1 : ν a + rhoV n a = (muQ lam lev + (2 : ℝ) • rhoV n - wtB B) (w a) - rhoV n (w a) := by
      have := hw a
      simp only [chiOf, chiHW] at this
      exact (Complex.ofReal_injective this).symm
    simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [h1]
    ring

open CompanionTheory.D.LK (LocFin) in

theorem van_cn {lam : Fin n → ℤ} {lev : Fin n → ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {E1 E2 : Fin n → Fin n → Module.End ℂ V} (h : AdmFor lam lev E1 E2) (B : Finset (Fin n × Fin n)) (hB : B.Nonempty)
    (hBl : ∀ p ∈ B, lev p.1 < lev p.2) (j : ℕ) (z : Cn n V) (hz : Sup (allT n) ∅ j z)
    (hwt : Wt (allT n) (kF E1 E2) (muQ lam lev + (2 : ℝ) • rhoV n - wtB B) z)
    (hb : bd (allT n) (kF E1 E2) z = 0) :
    ∃ t : Cn n V, Sup (allT n) ∅ (j + 1) t ∧ Wt (allT n) (kF E1 E2) (muQ lam lev + (2 : ℝ) • rhoV n - wtB B) t ∧
      bd (allT n) (kF E1 E2) t = z := by
  have hE : GlRel (kF E1 E2) := fun a b c d => by
    have e1 := h.gl1 a b c d
    have e2 := h.gl2 a b c d
    have c1 := h.comm a b c d
    have c2 := h.comm c d a b
    have e3 : kF E1 E2 a b * kF E1 E2 c d - kF E1 E2 c d * kF E1 E2 a b =
        (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
      simp only [kF, add_mul, mul_add]
      rw [c1, ← c2]
      abel
    rw [e3, e1, e2]
    simp only [kF]
    split_ifs <;> abel
  have hU : KUnit (allT n) (kF E1 E2) := fun a b _ x y => h.unitK a b x y
  have hF : LocFin (allT n) (kF E1 E2) := fun x => by
    obtain ⟨S, h1, h2, h3⟩ := h.locFin x
    exact ⟨S, h1, fun a b _ w hw => h3 a b w hw, h2⟩
  set τ : Fin n → ℝ := muQ lam lev + (2 : ℝ) • rhoV n - wtB B with hτ
  have hbad : ∀ (ν : Fin n → ℝ) (y : V), y ≠ 0 → KHighest (allT n) (kF E1 E2) ν y →
      ∃ m s, s ≠ GlobalTheory.Dec.gelfVal (chiOf τ) m ∧ etr (kF E1 E2) m y = s • y := by
    intro ν y hy0 hy
    by_contra hc
    push Not at hc
    have hm : ∀ k, GlobalTheory.Dec.gelfVal (chiHW ν) k = GlobalTheory.Dec.gelfVal (chiOf τ) k := fun k => by
      by_contra hne
      exact hc k _ hne (etr_hw _ hE ν y hy k)
    have hdom : ∀ c d : Fin n, c < d → ν d ≤ ν c := fun c d hcd => by
      have h2 := GlobalTheory.CompanionTheory.KWeightMajor.norm_identity (ε := allT n) (a := c) (b := d) (k_of_glRel hE) hU rfl hy.1
      rw [hy.2 c d hcd rfl, norm_zero] at h2
      have h3 : 0 < ‖y‖ ^ 2 := by positivity
      by_contra h4
      have h5 : 0 < (ν d - ν c) * ‖y‖ ^ 2 := mul_pos (by linarith [not_le.1 h4]) h3
      nlinarith [sq_nonneg ‖kF E1 E2 d c y‖]
    have hbot := h.no_second_type_weight ν (isN2_of_gelfand_values_eq lam lev B hB hBl ν hdom hm)
    have hmem : y ∈ hwSp E1 E2 ν := hy
    rw [hbot] at hmem
    exact hy0 ((Submodule.mem_bot ℂ).1 hmem)
  choose S hS hSt hmem using hF
  let W : Submodule ℂ V := ⨆ A, S (z A)
  haveI : ∀ A, FiniteDimensional ℂ (S (z A)) := fun A => hS _
  have hWs : KStab (allT n) (kF E1 E2) W := fun a b h v hv =>
    (iSup_le fun A y hy => Submodule.mem_iSup_of_mem A (hSt _ a b h y hy) : W ≤ W.comap (kF E1 E2 a b)) hv
  obtain ⟨L, hL, hkill⟩ := kill_list (kF E1 E2) hE hU _ hbad W inferInstance hWs
  obtain ⟨κ, w, hκ, hw1, hw2⟩ := chain_list (kF E1 E2) hE j τ z hz hwt hb L hL
  have h0 : lift n (L.map fun p => etr (kF E1 E2) p.1 - p.2 • (1 : Module.End ℂ V)).prod z = 0 := by
    funext A
    exact hkill _ (Submodule.mem_iSup_of_mem A (hmem _))
  rw [h0] at hw2
  have h1 : bd (allT n) (kF E1 E2) (-κ⁻¹ • w) = z := by
    have e : bd (allT n) (kF E1 E2) w = -(κ • z) := eq_neg_of_add_eq_zero_right hw2.symm
    rw [map_smul, e, smul_neg, neg_smul, neg_neg, smul_smul, inv_mul_cancel₀ hκ, one_smul]
  obtain ⟨t, ht1, ht2, ht3⟩ := GlobalTheory.CompanionTheory.LKWtProj.wtProj n (allT n) (allT n) V (kF E1 E2) (k_of_glRel hE) hU
    (fun x => ⟨S x, hS x, hSt x, hmem x⟩) (bd (allT n) (kF E1 E2))
    (CompanionTheory.D.LK.differential_commutes_weight_operator n _ _ V _ (fun _ _ _ => rfl) (k_of_glRel hE)) τ _ (h1.symm ▸ hwt)
  exact ⟨t, CompanionTheory.D.LK.sup_of_supp (sup_smul _ hw1) fun A h => ht3 A (by simpa using h), ht1, ht2.trans h1⟩

theorem vanKL : VanKL := by
  intro n lam _ lev _ V _ _ E1 E2 h B j z hB hBl hP hD hW hb
  have hBt : ∀ l ∈ B, l.1 = true := fun l hl => (hBl l hl).1
  by_cases hj : B.card ≤ j
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + B.card := ⟨j - B.card, by omega⟩
    have hwB : wtB (bPairs B) = wtL B := wtB_bPairs hBt
    have hbz : bd (allT n) (kF E1 E2) (toC B z) = 0 := by
      have e : frC B (bd (allT n) (kA E1 E2) (toC B z)) = 0 := by
        rw [frC_bd, frC_toC hP, hb]
      have e2 := toC_frC hBt (bd (allT n) (kA E1 E2) (toC B z))
      rw [e] at e2
      rw [show kF E1 E2 = kA E1 E2 from rfl, ← e2]
      rfl
    obtain ⟨t, ht1, ht2, ht3⟩ := van_cn h (bPairs B) (hB.image _)
      (fun p hp => by
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hp
        exact (hBl l hl).2) j' (toC B z) (sup_toC hBt hD)
      (by rw [hwB]; exact wt_toC hBt E1 E2 hW) hbz
    rw [hwB] at ht2
    refine ⟨frC B t, part_frC B t, ?_, wt_frC E1 E2 ht2, ?_⟩
    · have := deg_frC (B := B) ht1
      rwa [show j' + 1 + B.card = j' + B.card + 1 by omega] at this
    · rw [← frC_bd, show kA E1 E2 = kF E1 E2 from rfl, ht3, frC_toC hP]
  · have hz : z = 0 := by
      funext S
      by_contra hne
      have h1 := hP S hne
      have h2 := hD S hne
      have h3 : B.card ≤ S.card := by
        rw [← h1]
        exact Finset.card_filter_le _ _
      omega
    subst hz
    refine ⟨0, fun A h => absurd rfl h, fun A h => absurd rfl h, fun c => ?_, map_zero _⟩
    simp

end GlobalTheory.CompanionTheory.KostL
