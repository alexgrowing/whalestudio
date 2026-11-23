import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerIsometry
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.FlagEich

open GlobalTheory.HL.Eichler

theorem prod_update {G : Type*} [Group G] : ∀ {r : ℕ} (f : Fin r → G) (M : Fin r) (x : G),
    (∀ i, i ≤ M → f i = 1) → (List.ofFn (Function.update f M x)).prod = x * (List.ofFn f).prod := by
  intro r
  induction r with
  | zero => intro f M; exact M.elim0
  | succ r ih =>
    intro f M x hf
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    have hf0 : f 0 = 1 := hf 0 (Fin.le_iff_val_le_val.mpr (Nat.zero_le _))
    cases M using Fin.cases with
    | zero =>
      have : (fun i : Fin r => Function.update f 0 x i.succ) = fun i => f i.succ := by
        funext i; rw [Function.update_apply, if_neg (Fin.succ_ne_zero i)]
      rw [this, hf0]; simp
    | succ M' =>
      have : (fun i : Fin r => Function.update f M'.succ x i.succ) =
          Function.update (fun i => f i.succ) M' x := by
        funext i; simp only [Function.update_apply, Fin.succ_inj]
      rw [this, ih (fun i => f i.succ) M' x (fun i hi => hf _ (Fin.succ_le_succ_iff.mpr hi))]
      have h0 : Function.update f M'.succ x 0 = 1 := by
        rw [Function.update_apply, if_neg (Fin.succ_ne_zero M').symm]; exact hf0
      rw [h0, hf0]; simp

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem mem_gen {g : Fin (r + 1) → S.V} {j : ℕ} (hj : j ≤ r) {y : S.V}
    (hy : y ∈ g '' {i | (i : ℕ) < j}) : ∃ c : Fin r, (c : ℕ) < j ∧ y = g c.castSucc := by
  obtain ⟨i, hi, rfl⟩ := hy
  have hi' : (i : ℕ) < j := hi
  exact ⟨⟨i, by omega⟩, hi', rfl⟩

theorem gen_mem (g : Fin (r + 1) → S.V) {j : ℕ} (c : Fin r) (hc : (c : ℕ) < j) :
    g c.castSucc ∈ S.spanTo g j :=
  Submodule.subset_span ⟨c.castSucc, (by simpa using hc : ((c.castSucc : Fin (r + 1)) : ℕ) < j), rfl⟩

theorem spanTo_mono (g : Fin (r + 1) → S.V) {j j' : ℕ} (h : j ≤ j') : S.spanTo g j ≤ S.spanTo g j' :=
  Submodule.span_mono (Set.image_mono (fun i (hi : (i : ℕ) < j) => (lt_of_lt_of_le hi h : (i : ℕ) < j')))

theorem pairL {g : Fin (r + 1) → S.V} {j : ℕ} (hj : j ≤ r) (y : S.V)
    (h : ∀ c : Fin r, (c : ℕ) < j → hf L S.Hm (g c.castSucc) y = 0) :
    ∀ x ∈ S.spanTo g j, hf L S.Hm x y = 0 := by
  intro x hx
  unfold Frames.spanTo at hx
  induction hx using Submodule.span_induction with
  | mem z hz => obtain ⟨c, hc, rfl⟩ := mem_gen S hj hz; exact h c hc
  | zero => simp [hf]
  | add a b _ _ ha hb => rw [hf_add_l, ha, hb, add_zero]
  | smul c a _ ha => rw [hf_smul_l, ha, mul_zero]

theorem pairR {g : Fin (r + 1) → S.V} {j : ℕ} (hj : j ≤ r) (x : S.V)
    (h : ∀ c : Fin r, (c : ℕ) < j → hf L S.Hm x (g c.castSucc) = 0) :
    ∀ y ∈ S.spanTo g j, hf L S.Hm x y = 0 := by
  intro y hy
  unfold Frames.spanTo at hy
  induction hy using Submodule.span_induction with
  | mem z hz => obtain ⟨c, hc, rfl⟩ := mem_gen S hj hz; exact h c hc
  | zero => simp [hf]
  | add a b _ _ ha hb => rw [hf_add_r, ha, hb, add_zero]
  | smul c a _ ha => rw [hf_smul_r, ha, mul_zero]

theorem hf_sum_l {ι : Type*} (s : Finset ι) (x : ι → S.V) (y : S.V) :
    hf L S.Hm (∑ a ∈ s, x a) y = ∑ a ∈ s, hf L S.Hm (x a) y :=
  let φ : S.V →ₗ[E] E :=
    { toFun := fun z => hf L S.Hm z y
      map_add' := fun a b => hf_add_l L S.Hm a b y
      map_smul' := fun c a => by simp only [hf_smul_l, RingHom.id_apply, smul_eq_mul] }
  map_sum φ x s

theorem expand {g : Fin (r + 1) → S.V} {gs : Fin r → S.V}
    (H1 : ∀ (a : Fin (r + 1)) (j : Fin r), hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (x : S.V) (hx : x ∈ S.spanTo g r) : x = ∑ a : Fin r, hf L S.Hm x (gs a) • g a.castSucc := by
  unfold Frames.spanTo at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, -, rfl⟩ := mem_gen S le_rfl hz
    simp [H1, Fin.castSucc_inj, ite_smul]
  | zero => simp [hf]
  | add a b _ _ ha hb =>
    rw [Finset.sum_congr rfl (fun i _ => by rw [hf_add_l, add_smul]), Finset.sum_add_distrib, ← ha, ← hb]
  | smul c a _ ha =>
    rw [Finset.sum_congr rfl (fun i _ => by rw [hf_smul_l, mul_smul]), ← Finset.smul_sum, ← ha]

theorem zero_of {g : Fin (r + 1) → S.V} {gs : Fin r → S.V}
    (H1 : ∀ (a : Fin (r + 1)) (j : Fin r), hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (x : S.V) (hx : x ∈ S.spanTo g r) (h : ∀ a, hf L S.Hm x (gs a) = 0) : x = 0 := by
  rw [expand S H1 x hx]; simp [h]

theorem mem_Nof {g : Fin (r + 1) → S.V} {n : S.GLV} : n ∈ S.Nof g ↔ n ∈ isomG L S.Hm ∧
    (∀ j : Fin r, n ∈ unipOn (S.spanTo g ((j : ℕ) + 1)) (S.spanTo g j)) ∧
    n ∈ unipOn (perp L S.Hm (S.spanTo g r)) (S.spanTo g r) := by
  simp only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf, and_assoc]

end

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem gsg {g : Fin (r + 1) → S.V} {gs : Fin r → S.V}
    (H1 : ∀ (a : Fin (r + 1)) (j : Fin r), hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (a c : Fin r) : hf L S.Hm (gs a) (g c.castSucc) = if c = a then 1 else 0 := by
  rw [← hf_cj L S.herm.1 (g c.castSucc) (gs a), H1]
  simp only [Fin.castSucc_inj]
  split_ifs <;> simp

theorem eich_step {g : Fin (r + 1) → S.V}
    (H0 : ∀ a b : Fin r, hf L S.Hm (g a.castSucc) (g b.castSucc) = 0) (i : Fin r) (w : S.V) (t : E)
    (hw : ∀ j : Fin r, j ≤ i → hf L S.Hm w (g j.castSucc) = 0) :
    (∀ j : Fin r, ∀ v ∈ S.spanTo g ((j : ℕ) + 1),
      eich L S.Hm (g i.castSucc) w t v - v ∈ S.spanTo g j) ∧
    (∀ v ∈ perp L S.Hm (S.spanTo g r), eich L S.Hm (g i.castSucc) w t v - v ∈ S.spanTo g r) := by
  have hd : ∀ v, eich L S.Hm (g i.castSucc) w t v - v =
      hf L S.Hm v w • g i.castSucc - hf L S.Hm v (g i.castSucc) • (w + t • g i.castSucc) := by
    intro v; unfold eich; abel
  constructor
  · intro j v hv
    have hj := j.2
    have hx : hf L S.Hm v (g i.castSucc) = 0 :=
      pairL S (by omega : (j : ℕ) + 1 ≤ r) _ (fun c _ => H0 c i) v hv
    rw [hd, hx, zero_smul, sub_zero]
    by_cases hij : (i : ℕ) < j
    · exact Submodule.smul_mem _ _ (gen_mem S g i hij)
    · have : hf L S.Hm v w = 0 := pairL S (by omega) _ (fun c hc => by
        rw [← hf_cj L S.herm.1 w (g c.castSucc), hw c (Fin.le_iff_val_le_val.mpr (by omega)), map_zero]) v hv
      rw [this, zero_smul]; exact Submodule.zero_mem _
  · intro v hv
    have hv' : ∀ y ∈ S.spanTo g r, hf L S.Hm v y = 0 := hv
    have hx : hf L S.Hm v (g i.castSucc) = 0 := hv' _ (gen_mem S g i i.2)
    rw [hd, hx, zero_smul, sub_zero]
    exact Submodule.smul_mem _ _ (gen_mem S g i i.2)

theorem X_iso {g : Fin (r + 1) → S.V}
    (H0 : ∀ a b : Fin r, hf L S.Hm (g a.castSucc) (g b.castSucc) = 0) :
    S.spanTo g r ≤ perp L S.Hm (S.spanTo g r) := by
  intro x hx
  show ∀ y ∈ S.spanTo g r, hf L S.Hm x y = 0
  intro y hy
  exact pairL S le_rfl y (fun c _ => pairR S le_rfl (g c.castSucc) (fun d _ => H0 c d) y hy) x hx

theorem eich_mem {g : Fin (r + 1) → S.V}
    (H0 : ∀ a b : Fin r, hf L S.Hm (g a.castSucc) (g b.castSucc) = 0) (i : Fin r) (u : S.V) (s : E)
    (e : S.GLV) (hu : ∀ j : Fin r, j ≤ i → hf L S.Hm u (g j.castSucc) = 0)
    (hs : s + L.cj s = hf L S.Hm u u) (he : ∀ v, e v = eich L S.Hm (g i.castSucc) u s v) :
    e ∈ S.Nof g := by
  have hxx := H0 i i
  have hux := hu i le_rfl
  have hinv : ∀ v, eich L S.Hm (g i.castSucc) (-u) (L.cj s) (e v) = v := fun v => by
    rw [he]; exact eich_inv L S.herm.1 _ u s hxx hux hs v
  have hneg : ∀ j : Fin r, j ≤ i → hf L S.Hm (-u) (g j.castSucc) = 0 := fun j hj => by
    rw [hf_neg_l, hu j hj, neg_zero]
  obtain ⟨P1, P2⟩ := eich_step S H0 i u s hu
  obtain ⟨Q1, Q2⟩ := eich_step S H0 i (-u) (L.cj s) hneg
  rw [mem_Nof]
  refine ⟨?_, fun j => ?_, ?_⟩
  · show ∀ x y, hf L S.Hm (e x) (e y) = hf L S.Hm x y
    intro v w; rw [he, he]; exact eich_isom L S.herm.1 _ u s hxx hux hs v w
  · show (∀ v, e v ∈ S.spanTo g ((j : ℕ) + 1) ↔ v ∈ S.spanTo g ((j : ℕ) + 1)) ∧
      ∀ v ∈ S.spanTo g ((j : ℕ) + 1), e v - v ∈ S.spanTo g j
    have hle := spanTo_mono S g (Nat.le_succ (j : ℕ))
    refine ⟨fun v => ⟨fun hv => ?_, fun hv => ?_⟩, fun v hv => ?_⟩
    · have h1 := Q1 j (e v) hv
      rw [hinv] at h1
      have h2 := Submodule.add_mem _ (hle h1) hv
      rwa [sub_add_cancel] at h2
    · have h1 := P1 j v hv
      rw [← he] at h1
      have h2 := Submodule.add_mem _ (hle h1) hv
      rwa [sub_add_cancel] at h2
    · rw [he]; exact P1 j v hv
  · show (∀ v, e v ∈ perp L S.Hm (S.spanTo g r) ↔ v ∈ perp L S.Hm (S.spanTo g r)) ∧
      ∀ v ∈ perp L S.Hm (S.spanTo g r), e v - v ∈ S.spanTo g r
    have hle := X_iso S H0
    refine ⟨fun v => ⟨fun hv => ?_, fun hv => ?_⟩, fun v hv => ?_⟩
    · have h1 := Q2 (e v) hv
      rw [hinv] at h1
      have h2 := Submodule.add_mem _ (hle h1) hv
      rwa [sub_add_cancel] at h2
    · have h1 := P2 v hv
      rw [← he] at h1
      have h2 := Submodule.add_mem _ (hle h1) hv
      rwa [sub_add_cancel] at h2
    · rw [he]; exact P2 v hv

theorem fix_next {g : Fin (r + 1) → S.V} {gs : Fin r → S.V}
    (H1 : ∀ (a : Fin (r + 1)) (j : Fin r), hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (n : S.GLV) (hn : n ∈ S.Nof g) (m : Fin r)
    (hfix : ∀ a : Fin r, a < m → n (g a.castSucc) = g a.castSucc ∧ n (gs a) = gs a) :
    n (g m.castSucc) = g m.castSucc := by
  rw [mem_Nof] at hn
  obtain ⟨hiso, hj, -⟩ := hn
  have hiso' : ∀ x y, hf L S.Hm (n x) (n y) = hf L S.Hm x y := hiso
  have hB : n (g m.castSucc) - g m.castSucc ∈ S.spanTo g m := (hj m).2 _ (gen_mem S g m (Nat.lt_succ_self _))
  have hX : n (g m.castSucc) - g m.castSucc ∈ S.spanTo g r := spanTo_mono S g m.2.le hB
  refine sub_eq_zero.mp (zero_of S H1 _ hX fun a => ?_)
  by_cases ham : a < m
  · have := hiso' (g m.castSucc) (gs a)
    rw [(hfix a ham).2] at this
    rw [hf_sub_l, this, sub_self]
  · refine pairL S m.2.le (gs a) (fun c hc => ?_) _ hB
    rw [H1, if_neg]
    intro h
    rw [Fin.castSucc_inj] at h
    subst h
    exact ham (Fin.lt_def.mpr hc)

theorem eq_one {g : Fin (r + 1) → S.V} {gs : Fin r → S.V}
    (H1 : ∀ (a : Fin (r + 1)) (j : Fin r), hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (n : S.GLV) (hn : n ∈ S.Nof g)
    (hfix : ∀ a : Fin r, n (g a.castSucc) = g a.castSucc ∧ n (gs a) = gs a) : n = 1 := by
  rw [mem_Nof] at hn
  obtain ⟨hiso, -, hp⟩ := hn
  have hiso' : ∀ x y, hf L S.Hm (n x) (n y) = hf L S.Hm x y := hiso
  refine LinearEquiv.ext fun v => ?_
  show n v = v
  obtain ⟨w, hw⟩ : ∃ w, w = v - ∑ a : Fin r, hf L S.Hm v (g a.castSucc) • gs a := ⟨_, rfl⟩
  have hwp : w ∈ perp L S.Hm (S.spanTo g r) := by
    show ∀ y ∈ S.spanTo g r, hf L S.Hm w y = 0
    refine pairR S le_rfl w (fun c _ => ?_)
    rw [hw, hf_sub_l, hf_sum_l]
    simp only [hf_smul_l, gsg S H1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, sub_self]
  have ht : n w - w ∈ S.spanTo g r := hp.2 w hwp
  have h0 : n w - w = 0 := zero_of S H1 _ ht (fun a => by
    have := hiso' w (gs a)
    rw [(hfix a).2] at this
    rw [hf_sub_l, this, sub_self])
  have hnw : n w = w := sub_eq_zero.mp h0
  have hv : v = w + ∑ a : Fin r, hf L S.Hm v (g a.castSucc) • gs a := by rw [hw, sub_add_cancel]
  conv_lhs => rw [hv]
  rw [map_add, map_sum, hnw]
  simp only [map_smul, (hfix _).2]
  exact hv.symm

end

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem step {g : Fin (r + 1) → S.V} {gs : Fin r → S.V}
    (H0 : ∀ a b : Fin r, hf L S.Hm (g a.castSucc) (g b.castSucc) = 0)
    (H1 : ∀ (a : Fin (r + 1)) (j : Fin r), hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (H2 : ∀ i j, hf L S.Hm (gs i) (gs j) = 0)
    (n : S.GLV) (hn : n ∈ S.Nof g) (m : Fin r)
    (hfix : ∀ a : Fin r, a < m → n (g a.castSucc) = g a.castSucc ∧ n (gs a) = gs a) :
    ∃ (u : S.V) (s : E) (e : S.GLV),
      ((∀ j : Fin r, j ≤ m → hf L S.Hm u (g j.castSucc) = 0 ∧ hf L S.Hm u (gs j) = 0) ∧
        s + L.cj s = hf L S.Hm u u ∧ ∀ v, e v = eich L S.Hm (g m.castSucc) u s v) ∧
      e ∈ S.Nof g ∧ ∀ a : Fin r, a ≤ m → (e⁻¹ * n) (g a.castSucc) = g a.castSucc ∧
        (e⁻¹ * n) (gs a) = gs a := by
  have hiso' : ∀ x y, hf L S.Hm (n x) (n y) = hf L S.Hm x y := ((mem_Nof S).mp hn).1
  have hnx := fix_next S H1 n hn m hfix
  have hfixle : ∀ j : Fin r, j ≤ m → n (g j.castSucc) = g j.castSucc := fun j hj =>
    (lt_or_eq_of_le hj).elim (fun h => (hfix j h).1) (fun h => h ▸ hnx)
  obtain ⟨y, hy⟩ : ∃ y, y = n (gs m) := ⟨_, rfl⟩
  have hyg : ∀ j : Fin r, j ≤ m → hf L S.Hm y (g j.castSucc) = hf L S.Hm (gs m) (g j.castSucc) := by
    intro j hj
    have := hiso' (gs m) (g j.castSucc)
    rw [hfixle j hj] at this
    rw [hy]; exact this
  have hgsm : hf L S.Hm (gs m) (g m.castSucc) = 1 := by rw [gsg S H1]; simp
  have hgm : hf L S.Hm (g m.castSucc) (gs m) = 1 := by rw [H1]; simp
  have hyx : hf L S.Hm y (g m.castSucc) = 1 := by rw [hyg m le_rfl, hgsm]
  have hys : ∀ j : Fin r, j < m → hf L S.Hm y (gs j) = 0 := by
    intro j hj
    have := hiso' (gs m) (gs j)
    rw [(hfix j hj).2] at this
    rw [hy, this, H2]
  have hyy : hf L S.Hm y y = 0 := by rw [hy, hiso', H2]
  obtain ⟨s, hs⟩ : ∃ s, s = -hf L S.Hm y (gs m) := ⟨_, rfl⟩
  have hP : hf L S.Hm y (gs m) = -s := by rw [hs, neg_neg]
  obtain ⟨u, hu⟩ : ∃ u, u = gs m - y - s • g m.castSucc := ⟨_, rfl⟩
  have hug : ∀ j : Fin r, j ≤ m → hf L S.Hm u (g j.castSucc) = 0 := by
    intro j hj
    rw [hu, hf_sub_l, hf_sub_l, hf_smul_l, hyg j hj, H0, mul_zero, sub_self, sub_zero]
  have hugs : ∀ j : Fin r, j ≤ m → hf L S.Hm u (gs j) = 0 := by
    intro j hj
    rw [hu, hf_sub_l, hf_sub_l, hf_smul_l, H2]
    rcases lt_or_eq_of_le hj with h | h
    · rw [hys j h, H1, if_neg (by rw [Fin.castSucc_inj]; exact (ne_of_lt h).symm)]; simp
    · subst h; rw [hgm, hP]; ring
  have e1 : hf L S.Hm (gs m) y = L.cj (hf L S.Hm y (gs m)) := (hf_cj L S.herm.1 _ _).symm
  have e2 : hf L S.Hm (g m.castSucc) y = L.cj (hf L S.Hm y (g m.castSucc)) := (hf_cj L S.herm.1 _ _).symm
  have hs' : s + L.cj s = hf L S.Hm u u := by
    rw [hu]
    simp only [hf_sub_l, hf_sub_r, hf_smul_l, hf_smul_r, H2, e1, e2, hyx, hyy, H0, hgsm, hgm, hP,
      map_one, map_neg]
    ring
  obtain ⟨e, -, he, hei⟩ := eichler_isometry L S.Hm S.herm (g m.castSucc) u s (H0 m m) (hug m le_rfl) hs'
  have heq : eich L S.Hm (g m.castSucc) u s (gs m) = y := by
    unfold eich
    rw [← hf_cj L S.herm.1 u (gs m), hugs m le_rfl, map_zero, hgsm, zero_smul, one_smul, add_zero, hu]
    abel
  refine ⟨u, s, e, ⟨fun j hj => ⟨hug j hj, hugs j hj⟩, hs', he⟩,
    eich_mem S H0 m u s e (fun j hj => hug j hj) hs' he, fun a ha => ?_⟩
  show e⁻¹ (n (g a.castSucc)) = g a.castSucc ∧ e⁻¹ (n (gs a)) = gs a
  rw [hei, hei, hfixle a ha]
  have hua : hf L S.Hm (g a.castSucc) (-u) = 0 := by
    rw [hf_neg_r, ← hf_cj L S.herm.1 u (g a.castSucc), hug a ha, map_zero, neg_zero]
  refine ⟨?_, ?_⟩
  · unfold eich; rw [hua, H0]; simp
  · rcases lt_or_eq_of_le ha with h | h
    · rw [(hfix a h).2]
      have hus : hf L S.Hm (gs a) (-u) = 0 := by
        rw [hf_neg_r, ← hf_cj L S.herm.1 u (gs a), hugs a ha, map_zero, neg_zero]
      have hsx : hf L S.Hm (gs a) (g m.castSucc) = 0 := by
        rw [gsg S H1, if_neg (ne_of_lt h).symm]
      unfold eich; rw [hus, hsx]; simp
    · subst h
      rw [← hy, ← heq]
      exact eich_inv L S.herm.1 _ u s (H0 a a) (hug a le_rfl) hs' (gs a)

end

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem desc {g : Fin (r + 1) → S.V} {gs : Fin r → S.V}
    (H0 : ∀ a b : Fin r, hf L S.Hm (g a.castSucc) (g b.castSucc) = 0)
    (H1 : ∀ (a : Fin (r + 1)) (j : Fin r), hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (H2 : ∀ i j, hf L S.Hm (gs i) (gs j) = 0) :
    ∀ d m : ℕ, m + d = r → ∀ n ∈ S.Nof g,
      (∀ a : Fin r, (a : ℕ) < m → n (g a.castSucc) = g a.castSucc ∧ n (gs a) = gs a) →
      ∃ (u : Fin r → S.V) (s : Fin r → E) (e : Fin r → S.GLV),
        (∀ i, (∀ j, j ≤ i → hf L S.Hm (u i) (g j.castSucc) = 0 ∧ hf L S.Hm (u i) (gs j) = 0) ∧
          s i + L.cj (s i) = hf L S.Hm (u i) (u i) ∧
          ∀ v, e i v = eich L S.Hm (g i.castSucc) (u i) (s i) v) ∧
        (∀ i : Fin r, (i : ℕ) < m → e i = 1) ∧ n = (List.ofFn e).prod := by
  intro d
  induction d with
  | zero =>
    intro m hm n hn hfix
    have h1 : n = 1 := eq_one S H1 n hn (fun a => hfix a (by omega))
    refine ⟨fun _ => 0, fun _ => 0, fun _ => 1, fun i => ⟨fun j _ => ⟨by simp [hf], by simp [hf]⟩,
      by simp [hf], fun v => by simp [eich, hf]⟩, fun _ _ => rfl, ?_⟩
    rw [h1]; simp
  | succ d ih =>
    intro m hm n hn hfix
    have hmr : m < r := by omega
    obtain ⟨u0, s0, E0, hc0, hE0, hfix2⟩ := step S H0 H1 H2 n hn ⟨m, hmr⟩
      (fun a ha => hfix a (Fin.lt_def.mp ha))
    have hn' : E0⁻¹ * n ∈ S.Nof g := Subgroup.mul_mem _ (Subgroup.inv_mem _ hE0) hn
    obtain ⟨u', s', e', hc', h1', hp'⟩ := ih (m + 1) (by omega) (E0⁻¹ * n) hn'
      (fun a ha => hfix2 a (Fin.le_iff_val_le_val.mpr (by simp; omega)))
    refine ⟨Function.update u' ⟨m, hmr⟩ u0, Function.update s' ⟨m, hmr⟩ s0,
      Function.update e' ⟨m, hmr⟩ E0, fun i => ?_, fun i hi => ?_, ?_⟩
    · by_cases hi : i = ⟨m, hmr⟩
      · subst hi; simp only [Function.update_apply, if_true]; exact hc0
      · simp only [Function.update_apply, if_neg hi]; exact hc' i
    · have hi' : i ≠ ⟨m, hmr⟩ := fun h => by rw [h] at hi; simp at hi
      rw [Function.update_apply, if_neg hi']; exact h1' i (by omega)
    · rw [prod_update e' ⟨m, hmr⟩ E0 (fun i hi => h1' i (by rw [Fin.le_iff_val_le_val] at hi; simp at hi; omega)),
        ← hp', mul_inv_cancel_left]

end

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (g : Fin (r + 1) → S.V) (gs : Fin r → S.V), (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es') → ∀ n : S.GLV, n ∈ S.Nof g ↔ ∃ (u : Fin r → S.V) (s : Fin r → E) (e : Fin r → S.GLV), (∀ i, (∀ j, j ≤ i → S.h (u i) (g j.castSucc) = 0 ∧ S.h (u i) (gs j) = 0) ∧ s i + L.cj (s i) = S.h (u i) (u i) ∧ ∀ v, e i v = eich L S.Hm (g i.castSucc) (u i) (s i) v) ∧ n = (List.ofFn e).prod := by
  intro F _ _ _ _ _ E _ _ _ L r k S g gs hg n
  have H0 : ∀ a b : Fin r, hf L S.Hm (g a.castSucc) (g b.castSucc) = 0 := by
    intro a b
    rcases hg with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · rw [S.gram, if_neg (fun h => Fin.castSucc_ne_last a h.1)]
    · rw [S.gram', if_neg (fun h => Fin.castSucc_ne_last a h.1)]
  have H1 : ∀ (a : Fin (r + 1)) (j : Fin r), hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0 := by
    rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact S.dual
    · exact S.dual'
  have H2 : ∀ i j, hf L S.Hm (gs i) (gs j) = 0 := by
    rcases hg with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact S.iso
    · exact S.iso'
  simp only [Frames.h]
  constructor
  · intro hn
    obtain ⟨u, s, e, hc, -, hp⟩ := desc S H0 H1 H2 r 0 (by simp) n hn (fun a ha => absurd ha (Nat.not_lt_zero _))
    exact ⟨u, s, e, hc, hp⟩
  · rintro ⟨u, s, e, hc, rfl⟩
    apply Subgroup.list_prod_mem
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact eich_mem S H0 i (u i) (s i) (e i) (fun j hj => ((hc i).1 j hj).1) (hc i).2.1 (hc i).2.2

end GlobalTheory.FlagEich
