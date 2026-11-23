import Formalism.LocalToGlobal.Columns.ChainTwCst

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwAnGen

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

def TwAnIntMap {N M : ℕ} (P : HeightOneSpectrum (𝓞 E)) (f : Sp E N →ₗ[E] Sp E M) : Prop :=
  ∀ v : Sp E N, (∀ l, IntAt P (v l)) → ∀ l, IntAt P (f v l)

theorem twAn_single_int {N : ℕ} (s : Fin N) (l : Fin N) : IntAt P ((Pi.single s (1 : E) : Sp E N) l) := by
  by_cases h : l = s
  · subst h
    rw [Pi.single_eq_same]
    exact ⟨1, 1, one_notMem P, by simp⟩
  · rw [Pi.single_eq_of_ne h]
    exact ⟨0, 1, one_notMem P, by simp⟩

theorem twAn_intMap_of_entries {N M : ℕ} (f : Sp E N →ₗ[E] Sp E M) (h : ∀ s l, IntAt P (f (Pi.single s 1) l)) :
    TwAnIntMap P f := by
  intro v hv l
  have e : f v l = ∑ s, v s * f (Pi.single s 1) l := by
    rw [LinearMap.pi_apply_eq_sum_univ f v, Finset.sum_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    have : (fun j => if s = j then (1 : E) else 0) = Pi.single s 1 := by
      funext j
      rw [Pi.single_apply]
      by_cases hj : j = s
      · subst hj; simp
      · rw [if_neg (Ne.symm hj), if_neg hj]
    rw [this]
    rfl
  rw [e]
  exact Finset.sum_induction _ (IntAt P) (fun _ _ ha hb => ha.add hb) ⟨0, 1, one_notMem P, by simp⟩
    (fun s _ => (hv s).mul (h s l))

theorem twAn_phiQ_int (q : ℕ) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ r c' n' c n : ℕ} (hk' : k₀ ≤ n') (hk : k₀ ≤ n)
    (x : HomE E (n' + c') (n + c)) (h : LocE.PhiQ (P := P) q ξ k₀ r c' n' c n x ≠ 0) (s : Fin (n' + c')) (l : Fin (n + c)) :
    IntAt P (x (Pi.single s 1) l) := by
  unfold LocE.PhiQ at h
  split_ifs at h with hc
  · have h1 := hc.1 (LocE.fPos k₀ c n l.1) (LocE.fPos k₀ c' n' s.1) (framePos_lt hk l.2) (framePos_lt hk' s.2)
    unfold LocE.entB at h1
    rw [frameIndex_framePos hk l.2, frameIndex_framePos hk' s.2, basisVec_eq_single s.2] at h1
    unfold Loc.atN at h1
    rw [dif_pos l.2] at h1
    have e0 : ∀ (N : ℕ) (p : ℕ), LocE.scE N (0 : ℕ → ℕ) p = 0 := fun N p => by
      unfold LocE.scE
      split_ifs <;> rfl
    rw [e0, e0, sub_self, zpow_zero, mul_one] at h1
    exact h1
  · exact absurd rfl h

theorem integral_of_firstUnfolding_ne_zero {n' c' n c : ℕ} (Ψ : Loc.SF E K (n' + c') (n + c)) (a : ℕ) (qq : E)
    (hsupp : ∀ y, Ψ y ≠ 0 → ∀ s l, IntAt P (qq ^ a * y (Pi.single s 1) l))
    (psi : E → K) (vals : Finset E) (wt : K) (xj : (Fin n' → E) →ₗ[E] (Fin n → E))
    (h : Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi vals wt Ψ xj ≠ 0) (s : Fin n') (l : Fin n) :
    IntAt P (qq ^ a * xj (Pi.single s 1) l) := by
  unfold Loc.E1 at h
  have h1 := right_ne_zero_of_mul h
  obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  have h2 := left_ne_zero_of_mul ht
  have h3 := hsupp _ h2 (Fin.castAdd c' s) (Fin.castAdd c l)
  have e : Loc.xx1 xj t (Pi.single (Fin.castAdd c' s) 1) (Fin.castAdd c l) = xj (Pi.single s 1) l := by
    unfold Loc.xx1
    rw [← LinearMap.toMatrix'_apply, LinearMap.toMatrix'_toLin', Matrix.of_apply]
    have hf : ¬ Loc.IsFree n' n c (Fin.castAdd c l).1 (Fin.castAdd c' s).1 := fun hf => absurd s.2 (not_lt.2 hf.1)
    rw [dif_neg hf, dif_pos (show (Fin.castAdd c' s).1 < n' from s.2), dif_pos (show (Fin.castAdd c l).1 < n from l.2),
      LinearMap.toMatrix'_apply]
    rfl
  rw [e] at h3
  exact h3

theorem twAn_phiQ_congr (q : ℕ) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0)
    {k₀ r c' n' c n : ℕ} (x x' : HomE E (n' + c') (n + c)) (hrn : r ≤ n + c) (hrn' : r ≤ n' + c')
    (hD : ∀ p p', p < n + c → p' < n' + c' → ∃ d, IntAt P d ∧
      LocE.entB q k₀ c' n' c n 0 0 x' p p' = LocE.entB q k₀ c' n' c n 0 0 x p p' + q * d) :
    LocE.PhiQ (P := P) q ξ k₀ r c' n' c n x' = LocE.PhiQ (P := P) q ξ k₀ r c' n' c n x := by
  set M := LocE.entB q k₀ c' n' c n 0 0 x with hM
  set M' := LocE.entB q k₀ c' n' c n 0 0 x' with hM'
  have k1 : ∀ p p', p < n + c → p' < n' + c' → (IntAt P (M' p p') ↔ IntAt P (M p p')) := by
    intro p p' hp hp'
    obtain ⟨d, hd, he⟩ := hD p p' hp hp'
    rw [he]
    exact ciIntAt_add_iff ((ciIntAt_q (q := q)).mul hd)
  have k2 : ∀ p p', p < n + c → p' < n' + c' → (IntAt P (M' p p' / q) ↔ IntAt P (M p p' / q)) := by
    intro p p' hp hp'
    obtain ⟨d, hd, he⟩ := hD p p' hp hp'
    rw [he, add_div, mul_div_cancel_left₀ _ hq0]
    exact ciIntAt_add_iff hd
  have k3 : ∀ p p', p < n + c → p' < n' + c' → redP P (M' p p') = redP P (M p p') := by
    intro p p' hp hp'
    obtain ⟨d, hd, he⟩ := hD p p' hp hp'
    rw [he]
    exact redP_add_natCast_mul hq hd
  have hc : ((∀ p p', p < n + c → p' < n' + c' → IntAt P (M' p p')) ∧
      (∀ p p', r ≤ p → p < n + c → p' < r → IntAt P (M' p p' / q))) ↔
      ((∀ p p', p < n + c → p' < n' + c' → IntAt P (M p p')) ∧
      (∀ p p', r ≤ p → p < n + c → p' < r → IntAt P (M p p' / q))) := by
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun p p' hp hp' => (k1 p p' hp hp').1 (h1 p p' hp hp'),
        fun p p' h0 hp hp' => (k2 p p' hp (by omega)).1 (h2 p p' h0 hp hp')⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun p p' hp hp' => (k1 p p' hp hp').2 (h1 p p' hp hp'),
        fun p p' h0 hp hp' => (k2 p p' hp (by omega)).2 (h2 p p' h0 hp hp')⟩
  simp only [LocE.PhiQ]
  rw [← hM, ← hM']
  by_cases hC : (∀ p p', p < n + c → p' < n' + c' → IntAt P (M p p')) ∧
      (∀ p p', r ≤ p → p < n + c → p' < r → IntAt P (M p p' / q))
  · rw [if_pos (hc.2 hC), if_pos hC]
    apply ciUnitV_congr
    rw [redP_det (Matrix.of fun s t : Fin r => M' s.1 t.1) (fun s t => (hc.2 hC).1 s.1 t.1 (by omega) (by omega)),
      redP_det (Matrix.of fun s t : Fin r => M s.1 t.1) (fun s t => hC.1 s.1 t.1 (by omega) (by omega))]
    congr 1
    ext s t
    exact k3 s.1 t.1 (by omega) (by omega)
  · rw [if_neg (fun h => hC (hc.1 h)), if_neg hC]

theorem frameEntry_unscaled_eq_coord (q : ℕ) {k₀ c' n' c n : ℕ} (hk' : k₀ ≤ n') (hk : k₀ ≤ n) (x : HomE E (n' + c') (n + c)) {p p' : ℕ}
    (hp : p < n + c) (hp' : p' < n' + c') :
    LocE.entB q k₀ c' n' c n 0 0 x p p' =
      x (Pi.single (⟨LocE.fIdx k₀ c' n' p', symFIdx_lt hk' hp'⟩ : Fin (n' + c')) 1) ⟨LocE.fIdx k₀ c n p, symFIdx_lt hk hp⟩ := by
  unfold LocE.entB
  rw [basisVec_eq_single (symFIdx_lt hk' hp')]
  unfold Loc.atN
  rw [dif_pos (symFIdx_lt hk hp)]
  have e0 : ∀ (N : ℕ) (p : ℕ), LocE.scE N (0 : ℕ → ℕ) p = 0 := fun N p => by
    unfold LocE.scE
    split_ifs <;> rfl
  rw [e0, e0, sub_self, zpow_zero, mul_one]

theorem twAn_joinCol_castAdd {n' c' n c : ℕ} (x₀ : HomE E n' n) (y' : Sp E n) (s : Fin n') :
    joinCol (c' := c') (c := c) x₀ y' (Pi.single (Fin.castAdd c' s) (1 : E)) = Loc.inX E n c (x₀ (Pi.single s 1)) := by
  unfold joinCol
  have h1 : LinearMap.funLeft E E (Fin.castAdd c') (Pi.single (Fin.castAdd c' s) (1 : E)) = Pi.single s 1 := by
    funext i
    rw [LinearMap.funLeft_apply]
    by_cases h : i = s
    · subst h; simp
    · rw [Pi.single_eq_of_ne (fun e => h (Fin.castAdd_injective _ _ e)), Pi.single_eq_of_ne h]
  have h2 : atNL E (n' + c') n' (Pi.single (Fin.castAdd c' s) (1 : E)) = 0 := by
    unfold atNL
    split_ifs with h
    · show (Pi.single (Fin.castAdd c' s) (1 : E) : Fin (n' + c') → E) ⟨n', h⟩ = 0
      rw [Pi.single_eq_of_ne]
      intro e
      have := congrArg Fin.val e
      simp at this
      omega
    · rfl
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply, h1, h2, zero_smul, add_zero]

theorem twAn_joinCol {n' c' n c : ℕ} (hc : 1 ≤ c') (x₀ : HomE E n' n) (y' : Sp E n) :
    joinCol (c' := c') (c := c) x₀ y' (Pi.single (⟨n', by omega⟩ : Fin (n' + c')) (1 : E)) = Loc.inX E n c y' := by
  unfold joinCol
  have h1 : LinearMap.funLeft E E (Fin.castAdd c') (Pi.single (⟨n', by omega⟩ : Fin (n' + c')) (1 : E)) = 0 := by
    funext i
    rw [LinearMap.funLeft_apply, Pi.single_eq_of_ne]
    · rfl
    · intro e
      have := congrArg Fin.val e
      simp at this
      omega
  have h2 : atNL E (n' + c') n' (Pi.single (⟨n', by omega⟩ : Fin (n' + c')) (1 : E)) = 1 := by
    unfold atNL
    rw [dif_pos (by omega)]
    show (Pi.single (⟨n', by omega⟩ : Fin (n' + c')) (1 : E) : Fin (n' + c') → E) ⟨n', by omega⟩ = 1
    exact Pi.single_eq_same _ _
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply, h1, h2, map_zero, one_smul, zero_add]

theorem twAn_joinCol_sub_y {n' c' n c : ℕ} (x₀ : HomE E n' n) (y' z : Sp E n) (v : Sp E (n' + c')) :
    joinCol (c' := c') (c := c) x₀ (y' + z) v - joinCol (c' := c') (c := c) x₀ y' v = Loc.inX E n c (atNL E (n' + c') n' v • z) := by
  unfold joinCol
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply, smul_add, map_add]
  abel

theorem joinColumn_add_sub {n' c' n c : ℕ} (x₀ z : HomE E n' n) (y' : Sp E n) (v : Sp E (n' + c')) :
    joinCol (c' := c') (c := c) (x₀ + z) y' v - joinCol (c' := c') (c := c) x₀ y' v =
      Loc.inX E n c (z (LinearMap.funLeft E E (Fin.castAdd c') v)) := by
  unfold joinCol
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply, map_add]
  abel

theorem columns_twAn_fact {n' c' n c : ℕ} (xj xj' : (Fin n' → E) →ₗ[E] (Fin n → E)) (t : Loc.FC n' c' n c → E)
    (s : Fin (n' + c')) (hs : n' ≤ s.1) (l : Fin (n + c)) :
    Loc.xx1 xj t (Pi.single s 1) l = Loc.xx1 xj' t (Pi.single s 1) l := by
  unfold Loc.xx1
  rw [← LinearMap.toMatrix'_apply, LinearMap.toMatrix'_toLin', Matrix.of_apply, ← LinearMap.toMatrix'_apply,
    LinearMap.toMatrix'_toLin', Matrix.of_apply]
  split_ifs with h1 h2 <;> first | rfl | exact absurd h2 (by omega)

theorem unipotentExtension_add_sub {n' c' n c : ℕ} (xj z : (Fin n' → E) →ₗ[E] (Fin n → E)) (t : Loc.FC n' c' n c → E)
    (s : Fin (n' + c')) (l : Fin (n + c)) :
    Loc.xx1 (xj + z) t (Pi.single s 1) l - Loc.xx1 xj t (Pi.single s 1) l =
      if hs : s.1 < n' then (if hl : l.1 < n then z (Pi.single ⟨s.1, hs⟩ 1) ⟨l.1, hl⟩ else 0) else 0 := by
  unfold Loc.xx1
  rw [← LinearMap.toMatrix'_apply, LinearMap.toMatrix'_toLin', Matrix.of_apply, ← LinearMap.toMatrix'_apply,
    LinearMap.toMatrix'_toLin', Matrix.of_apply]
  by_cases hs : s.1 < n'
  · have hf : ¬ Loc.IsFree n' n c l.1 s.1 := fun hf => absurd hs (not_lt.2 hf.1)
    rw [dif_neg hf, dif_neg hf, dif_pos hs, dif_pos hs, dif_pos hs]
    by_cases hl : l.1 < n
    · rw [dif_pos hl, dif_pos hl, dif_pos hl, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply, LinearMap.add_apply, Pi.add_apply]
      ring
    · rw [dif_neg hl, dif_neg hl, dif_neg hl, sub_self]
  · rw [dif_neg hs]
    split_ifs <;> simp

theorem charArg_unipotentExtension_indep {n' c' n c : ℕ} (xj xj' : (Fin n' → E) →ₗ[E] (Fin n → E)) (t : Loc.FC n' c' n c → E) :
    Loc.chArg (Loc.xx1 xj t) = Loc.chArg (Loc.xx1 xj' t) := by
  unfold Loc.chArg
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : n' + i + 1 < n' + c'
  · rw [basisVec_eq_single h]
    unfold Loc.atN
    split_ifs with hl
    · exact columns_twAn_fact xj xj' t _ (by show n' ≤ n' + i + 1; omega) _
    · rfl
  · have e : Loc.eN E (n' + c') (n' + i + 1) = 0 := by
      funext l
      unfold Loc.eN
      rw [if_neg (by omega)]
      rfl
    rw [e, map_zero, map_zero]

theorem twAn_atNL_int {N : ℕ} (k : ℕ) (s : Fin N) : IntAt P (atNL E N k (Pi.single s (1 : E))) := by
  unfold atNL
  split_ifs
  · exact twAn_single_int s _
  · show IntAt P 0
    exact ⟨0, 1, one_notMem P, by simp⟩

theorem twAn_funLeft_int {n' c' : ℕ} (s : Fin (n' + c')) (l : Fin n') :
    IntAt P (LinearMap.funLeft E E (Fin.castAdd c') (Pi.single s (1 : E)) l) := by
  rw [LinearMap.funLeft_apply]
  exact twAn_single_int s _

theorem unipotentExtension_freeCoord {n' c' n c : ℕ} (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) (t : Loc.FC n' c' n c → E) (f : Loc.FC n' c' n c) :
    Loc.xx1 xj t (Pi.single f.1.2 1) f.1.1 = t f := by
  unfold Loc.xx1
  rw [← LinearMap.toMatrix'_apply, LinearMap.toMatrix'_toLin', Matrix.of_apply, dif_pos f.2]

theorem xx1_add_sub_xx1_single_eq_dite {n' c' n c : ℕ} (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) (t δ : Loc.FC n' c' n c → E)
    (s : Fin (n' + c')) (l : Fin (n + c)) :
    Loc.xx1 xj (t + δ) (Pi.single s 1) l - Loc.xx1 xj t (Pi.single s 1) l =
      if hf : Loc.IsFree n' n c l.1 s.1 then δ ⟨(l, s), hf⟩ else 0 := by
  unfold Loc.xx1
  rw [← LinearMap.toMatrix'_apply, LinearMap.toMatrix'_toLin', Matrix.of_apply, ← LinearMap.toMatrix'_apply,
    LinearMap.toMatrix'_toLin', Matrix.of_apply]
  by_cases hf : Loc.IsFree n' n c l.1 s.1
  · rw [dif_pos hf, dif_pos hf, dif_pos hf, Pi.add_apply]
    ring
  · rw [dif_neg hf, dif_neg hf, dif_neg hf, sub_self]

theorem twAn_chArg_term {n' c' n c : ℕ} (x : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)) (i : ℕ) :
    Loc.atN (x (Loc.eN E (n' + c') (n' + i + 1))) (n + i) =
      if h : n' + i + 1 < n' + c' ∧ n + i < n + c then x (Pi.single ⟨n' + i + 1, h.1⟩ 1) ⟨n + i, h.2⟩ else 0 := by
  by_cases h1 : n' + i + 1 < n' + c'
  · rw [basisVec_eq_single h1]
    unfold Loc.atN
    by_cases h2 : n + i < n + c
    · rw [dif_pos h2, dif_pos ⟨h1, h2⟩]
    · rw [dif_neg h2, dif_neg (fun h => h2 h.2)]
  · have e : Loc.eN E (n' + c') (n' + i + 1) = 0 := by
      funext l
      unfold Loc.eN
      rw [if_neg (by omega)]
      rfl
    rw [e, map_zero, dif_neg (fun h => h1 h.1)]
    unfold Loc.atN
    split_ifs <;> rfl

end TwAnGen

section TwAnSum

variable {E K : Type} [Field E] [CharZero E] [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

def twAnPhi (q A i : ℕ) : E := (i : E) / (q : E) ^ A

theorem twAnPhi_inj {q A : ℕ} (hq : (q : E) ≠ 0) : Function.Injective (twAnPhi (E := E) q A) := by
  intro i j h
  unfold twAnPhi at h
  have := (div_left_inj' (pow_ne_zero A hq)).1 h
  exact_mod_cast this

theorem twAn_sum_valsQ {q A B : ℕ} (hq : (q : E) ≠ 0) (G : (ι → E) → K) :
    ∑ t ∈ Fintype.piFinset (fun _ : ι => LocE.valsQ E q A B), G t =
      ∑ k : ι → Fin (q ^ (A + B)), G (fun f => twAnPhi q A (k f)) := by
  classical
  symm
  apply Finset.sum_bij (fun k _ => fun f => twAnPhi (E := E) q A (k f))
  · intro k _
    rw [Fintype.mem_piFinset]
    intro f
    exact Finset.mem_image.2 ⟨k f, Finset.mem_range.2 (k f).2, rfl⟩
  · intro k _ k' _ h
    funext f
    exact Fin.ext (twAnPhi_inj hq (congrFun h f))
  · intro t ht
    rw [Fintype.mem_piFinset] at ht
    have hc : ∀ f, ∃ i : Fin (q ^ (A + B)), twAnPhi (E := E) q A i = t f := fun f => by
      obtain ⟨i, hi, he⟩ := Finset.mem_image.1 (ht f)
      exact ⟨⟨i, Finset.mem_range.1 hi⟩, he⟩
    exact ⟨fun f => (hc f).choose, Finset.mem_univ _, funext fun f => (hc f).choose_spec⟩
  · intro k _
    rfl

theorem twAn_sumA {q A B : ℕ} (hq : (q : E) ≠ 0) (G : (ι → E) → K)
    (hvan : ∀ k : ι → ℕ, (∃ f, ¬ q ∣ k f) → G (fun f => twAnPhi q (A + 1) (k f)) = 0) :
    ∑ k : ι → Fin (q ^ (A + 1 + B)), G (fun f => twAnPhi q (A + 1) (k f)) =
      ∑ k : ι → Fin (q ^ (A + B)), G (fun f => twAnPhi q A (k f)) := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero (fun h => hq (by rw [h, Nat.cast_zero]))
  have hlt : ∀ i : Fin (q ^ (A + B)), q * i.1 < q ^ (A + 1 + B) := fun i => by
    have : q ^ (A + 1 + B) = q * q ^ (A + B) := by rw [show A + 1 + B = (A + B) + 1 by omega, pow_succ']
    rw [this]
    exact Nat.mul_lt_mul_of_pos_left i.2 hq0
  symm
  apply Fintype.sum_of_injective (fun k f => (⟨q * (k f).1, hlt (k f)⟩ : Fin (q ^ (A + 1 + B))))
  · intro k k' h
    funext f
    have := congrArg Fin.val (congrFun h f)
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left hq0 this)
  · intro k hk
    apply hvan
    by_contra hall
    push Not at hall
    apply hk
    refine ⟨fun f => ⟨(k f).1 / q, ?_⟩, ?_⟩
    · have e : q ^ (A + 1 + B) = q * q ^ (A + B) := by rw [show A + 1 + B = (A + B) + 1 by omega, pow_succ']
      have h1 : (k f).1 < q * q ^ (A + B) := lt_of_lt_of_eq (k f).2 e
      exact (Nat.div_lt_iff_lt_mul hq0).2 (by rw [mul_comm]; exact h1)
    · funext f
      exact Fin.ext (Nat.mul_div_cancel' (hall f))
  · intro k
    congr 1
    funext f
    unfold twAnPhi
    push_cast
    rw [pow_succ]
    field_simp

theorem twAn_sumB {q A B : ℕ} (hq : (q : E) ≠ 0) (G : (ι → E) → K)
    (hinv : ∀ a b : ι → ℕ, G (fun f => twAnPhi q A (a f + q ^ (A + B) * b f)) = G (fun f => twAnPhi q A (a f))) :
    ∑ k : ι → Fin (q ^ (A + B + 1)), G (fun f => twAnPhi q A (k f)) =
      (q ^ Fintype.card ι : K) * ∑ k : ι → Fin (q ^ (A + B)), G (fun f => twAnPhi q A (k f)) := by
  have hM : q * q ^ (A + B) = q ^ (A + B + 1) := by rw [pow_succ']
  let e : Fin q × Fin (q ^ (A + B)) ≃ Fin (q ^ (A + B + 1)) := finProdFinEquiv.trans (finCongr hM)
  have he : ∀ x : Fin q × Fin (q ^ (A + B)), (e x).1 = x.2.1 + q ^ (A + B) * x.1.1 := fun x => by
    simp [e, finProdFinEquiv]
  let e' : (ι → Fin q) × (ι → Fin (q ^ (A + B))) ≃ (ι → Fin (q ^ (A + B + 1))) :=
    (Equiv.arrowProdEquivProdArrow _ _ _).symm.trans (Equiv.arrowCongr (Equiv.refl ι) e)
  have he' : ∀ x f, (e' x f).1 = (x.2 f).1 + q ^ (A + B) * (x.1 f).1 := fun x f => he (x.1 f, x.2 f)
  rw [← Fintype.sum_equiv e' (fun x => G (fun f => twAnPhi q A ((x.2 f).1 + q ^ (A + B) * (x.1 f).1)))
    (fun k => G (fun f => twAnPhi q A (k f))) (fun x => by simp only [he'])]
  rw [Fintype.sum_prod_type]
  simp only [hinv (fun f => _) (fun f => _)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rfl

theorem twAn_deep_abs {q : ℕ} (hq : (q : E) ≠ 0) (hqK : (q : K) ≠ 0) (G : (ι → E) → K) {A0 B0 : ℕ}
    (hvan : ∀ A, A0 ≤ A → ∀ k : ι → ℕ, (∃ f, ¬ q ∣ k f) → G (fun f => twAnPhi q (A + 1) (k f)) = 0)
    (hinv : ∀ A B, B0 ≤ B → ∀ a b : ι → ℕ, G (fun f => twAnPhi q A (a f + q ^ (A + B) * b f)) = G (fun f => twAnPhi q A (a f)))
    {A B A' B' : ℕ} (hA : A0 ≤ A) (hB : B0 ≤ B) (hAA : A ≤ A') (hBB : B ≤ B') :
    (((q : K) ^ B')⁻¹) ^ Fintype.card ι * ∑ t ∈ Fintype.piFinset (fun _ : ι => LocE.valsQ E q A' B'), G t =
      (((q : K) ^ B)⁻¹) ^ Fintype.card ι * ∑ t ∈ Fintype.piFinset (fun _ : ι => LocE.valsQ E q A B), G t := by
  rw [twAn_sum_valsQ hq, twAn_sum_valsQ hq]
  have stepA : ∀ A'', A ≤ A'' → ∀ B'', ∑ k : ι → Fin (q ^ (A'' + B'')), G (fun f => twAnPhi q A'' (k f)) =
      ∑ k : ι → Fin (q ^ (A + B'')), G (fun f => twAnPhi q A (k f)) := by
    intro A'' hA'' B''
    induction A'', hA'' using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      rw [← ih]
      have := twAn_sumA (B := B'') hq G (hvan n (le_trans hA hn))
      rw [show n + 1 + B'' = (n + 1) + B'' from rfl] at this
      exact this
  have stepB : ∀ B'', B ≤ B'' → (((q : K) ^ B'')⁻¹) ^ Fintype.card ι * ∑ k : ι → Fin (q ^ (A' + B'')), G (fun f => twAnPhi q A' (k f)) =
      (((q : K) ^ B)⁻¹) ^ Fintype.card ι * ∑ k : ι → Fin (q ^ (A' + B)), G (fun f => twAnPhi q A' (k f)) := by
    intro B'' hB''
    induction B'', hB'' using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      rw [← ih]
      have h1 := twAn_sumB (A := A') (B := n) hq G (hinv A' n (le_trans hB hn))
      have h2 : ∑ k : ι → Fin (q ^ (A' + (n + 1))), G (fun f => twAnPhi q A' (k f)) =
          ∑ k : ι → Fin (q ^ (A' + n + 1)), G (fun f => twAnPhi q A' (k f)) := rfl
      rw [h2, h1, ← mul_assoc]
      congr 1
      rw [pow_succ, mul_inv, mul_pow, mul_assoc, ← mul_pow, inv_mul_cancel₀ hqK, one_pow, mul_one]
  rw [stepB B' hBB, stepA A' hAA B]

end TwAnSum

section TwAnX

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

theorem twAn_lam_mem {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) (v : Sp X.E (R.N j + cOf R j)) :
    v ∈ lamYat (Pr := Pr) (R := R) j P ↔ ∀ l, IntAt P (v l) := by
  have e : lamYat (Pr := Pr) (R := R) j P = LocE.lamY P (qOf P) (R.N j) (cOf R j) 0 := by
    unfold lamYat
    rw [if_neg hP]
  rw [e]
  unfold LocE.lamY
  rw [ciMem_sclLat]
  have h0 : ∀ l : ℕ, LocE.scE (R.N j) 0 l = 0 := fun l => by
    unfold LocE.scE
    split_ifs <;> rfl
  simp only [h0, zpow_zero, inv_one, one_mul]

theorem twAn_bdd_inv {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) {h : AutY X R j} (hb : TwBdd (Pr := Pr) j P h) :
    TwAnIntMap P (h⁻¹ : AutY X R j).toLinearMap := fun v hv =>
  (twAn_lam_mem hP _).1 ((hb v ((twAn_lam_mem hP v).2 hv)).1)

theorem twAn_bdd_q {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) {h : AutY X R j} (hb : TwBdd (Pr := Pr) j P h)
    (v : Sp X.E (R.N j + cOf R j)) (hv : ∀ l, IntAt P (v l)) (l : Fin (R.N j + cOf R j)) : IntAt P ((qOf P : X.E) ^ j * h v l) := by
  have := (twAn_lam_mem hP _).1 ((hb v ((twAn_lam_mem hP v).2 hv)).2) l
  simpa [Pi.smul_apply, smul_eq_mul] using this

theorem twAn_k_le (j : ℕ) : R.k ≤ R.N j := by
  unfold Ranks.N
  omega

theorem twAn_omPhi_supp {i : ℕ} (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) (hal : AutY X R i) (hbe : AutY X R (i + 1))
    (hba : TwBdd (Pr := Pr) i P.1 hal) (hbb : TwBdd (Pr := Pr) (i + 1) P.1 hbe) (y : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1)))
    (h : omPhi Ch sel mu cst i P hal hbe y ≠ 0) (s : Fin (R.N i + cOf R i)) (l : Fin (R.N (i + 1) + cOf R (i + 1))) :
    IntAt P.1 ((qOf P.1 : X.E) ^ (i + 1) * y (Pi.single s 1) l) := by
  unfold omPhi Loc.om at h
  have h1 := right_ne_zero_of_mul h
  unfold PhiAt at h1
  rw [if_neg hP] at h1
  have hz := twAn_intMap_of_entries _ (twAn_phiQ_int (qOf P.1) _ (twAn_k_le i) (twAn_k_le (i + 1)) _ h1)
  have hw := twAn_bdd_inv hP hba (Pi.single s 1) (fun l => twAn_single_int s l)
  have h2 := twAn_bdd_q hP hbb _ (hz _ hw) l
  have e : hbe ((hbe.symm.toLinearMap ∘ₗ y ∘ₗ hal.toLinearMap) ((hal⁻¹ : AutY X R i) (Pi.single s 1))) = y (Pi.single s 1) := by
    show hbe (hbe.symm (y (hal (hal.symm (Pi.single s 1))))) = _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have e' : hbe ((hbe.symm.toLinearMap ∘ₗ y ∘ₗ hal.toLinearMap) ((hal⁻¹ : AutY X R i).toLinearMap (Pi.single s 1))) =
      y (Pi.single s 1) := e
  rw [e'] at h2
  exact h2

theorem twAn_qpow_int (P : HeightOneSpectrum (𝓞 X.E)) (n : ℕ) : IntAt P ((qOf P : X.E) ^ n) := by
  have := IntAt.coe P ((qOf P : 𝓞 X.E) ^ n)
  simpa using this

theorem twAn_qpow_mul {P : HeightOneSpectrum (𝓞 X.E)} {a b : ℕ} (hab : a ≤ b) {z : X.E} (h : IntAt P ((qOf P : X.E) ^ a * z)) :
    IntAt P ((qOf P : X.E) ^ b * z) := by
  have e : (qOf P : X.E) ^ b * z = (qOf P : X.E) ^ (b - a) * ((qOf P : X.E) ^ a * z) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hab]
  rw [e]
  exact (twAn_qpow_int P _).mul h

theorem twAn_r_le {i : ℕ} (hi : i + 1 ≤ R.m) : R.r ≤ R.N i + cOf R i := by
  unfold Ranks.r Ranks.N cOf
  have : i * (R.t + 1) = i * R.t + i := by ring
  omega

theorem twAn_scal {E : Type} [Field E] {q : E} (hq0 : q ≠ 0) {B i : ℕ} (h : i ≤ B) : q ^ (B - i) * ((q ^ B)⁻¹ * q ^ i) = 1 := by
  have e : q ^ B = q ^ (B - i) * q ^ i := by rw [← pow_add, Nat.sub_add_cancel h]
  rw [e]
  field_simp

theorem twAn_omPhi_congr {i : ℕ} (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) (hq : (qOf P.1).Prime) (hi : i + 2 ≤ R.m)
    (hal : AutY X R i) (hbe : AutY X R (i + 1)) (hba : TwBdd (Pr := Pr) i P.1 hal) (hbb : TwBdd (Pr := Pr) (i + 1) P.1 hbe)
    {B : ℕ} (hB : i + 1 ≤ B) (y y' : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1)))
    (hyy : ∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ B)⁻¹ * (y' (Pi.single s 1) l - y (Pi.single s 1) l))) :
    omPhi Ch sel mu cst i P hal hbe y' = omPhi Ch sel mu cst i P hal hbe y := by
  have hq0 : (qOf P.1 : X.E) ≠ 0 := by exact_mod_cast hq.ne_zero
  unfold omPhi Loc.om
  congr 1
  unfold PhiAt
  rw [if_neg hP]
  apply twAn_phiQ_congr (qOf P.1) _ (ciQ_mem P.1) hq0 _ _ (twAn_r_le (by omega)) (twAn_r_le (by omega))
  intro p p' hp hp'
  rw [frameEntry_unscaled_eq_coord _ (twAn_k_le i) (twAn_k_le (i + 1)) _ hp hp', frameEntry_unscaled_eq_coord _ (twAn_k_le i) (twAn_k_le (i + 1)) _ hp hp']
  set es : Sp X.E (R.N i + cOf R i) := Pi.single (⟨LocE.fIdx R.k (cOf R i) (R.N i) p', symFIdx_lt (twAn_k_le i) hp'⟩ : Fin _) 1 with hes
  set l : Fin (R.N (i + 1) + cOf R (i + 1)) := ⟨LocE.fIdx R.k (cOf R (i + 1)) (R.N (i + 1)) p, symFIdx_lt (twAn_k_le (i + 1)) hp⟩
  set q : X.E := (qOf P.1 : X.E) with hqd

  let D : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1)) := ((q ^ B)⁻¹) • (y' - y)
  have hDint : TwAnIntMap P.1 D := twAn_intMap_of_entries D fun s l => by
    show IntAt P.1 (((q ^ B)⁻¹ • (y' - y)) (Pi.single s 1) l)
    simpa [LinearMap.smul_apply, LinearMap.sub_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] using hyy s l
  let v : Sp X.E (R.N i + cOf R i) := (q ^ i) • hal es
  have hv : ∀ l, IntAt P.1 (v l) := fun l => by
    have := twAn_bdd_q hP hba es (fun l => twAn_single_int _ l) l
    simpa [v, Pi.smul_apply, smul_eq_mul] using this
  have hg := twAn_bdd_inv hP hbb (D v) (hDint v hv)
  have key : hbe.symm (y' (hal es)) - hbe.symm (y (hal es)) = q ^ (B - i) • (hbe⁻¹ : AutY X R (i + 1)) (D v) := by
    have e1 : (hbe⁻¹ : AutY X R (i + 1)) (D v) = ((q ^ B)⁻¹ * q ^ i) • (hbe.symm (y' (hal es)) - hbe.symm (y (hal es))) := by
      show hbe.symm ((((q ^ B)⁻¹) • (y' - y)) ((q ^ i) • hal es)) = _
      rw [LinearMap.smul_apply, map_smul, map_smul, map_smul, LinearMap.sub_apply, map_sub, smul_smul]
    rw [e1, smul_smul, twAn_scal hq0 (by omega), one_smul]
  refine ⟨q ^ (B - i - 1) * ((hbe⁻¹ : AutY X R (i + 1)) (D v) l), (twAn_qpow_int P.1 _).mul (hg l), ?_⟩
  have kl := congrFun key l
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at kl
  show hbe.symm (y' (hal es)) l = hbe.symm (y (hal es)) l + q * _
  have e2 : q * (q ^ (B - i - 1) * (hbe⁻¹ : AutY X R (i + 1)) (D v) l) = q ^ (B - i) * (hbe⁻¹ : AutY X R (i + 1)) (D v) l := by
    rw [← mul_assoc, ← pow_succ']
    congr 2
    omega
  rw [e2, ← kl]
  ring

theorem twAn_xiSupp {m2 : ℕ} (hA : ∀ i, i < m2 → i + 1 ≤ cst.A) :
    ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ (hal : AutY X R i) (hbe : AutY X R (i + 1)),
      TwBdd (Pr := Pr) i P.1 hal → TwBdd (Pr := Pr) (i + 1) P.1 hbe → ∀ x : HomE X.E (R.N i) (R.N (i + 1)),
        XiAt Ch sel mu cst i P hal hbe x ≠ 0 → ∀ s l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.A * x (Pi.single s 1) l) := by
  intro i hi P hP hal hbe hba hbb x h s l
  unfold XiAt at h
  have h1 := right_ne_zero_of_mul h
  unfold E1at at h1
  have h2 := integral_of_firstUnfolding_ne_zero (omPhi Ch sel mu cst i P hal hbe) (i + 1) (qOf P.1 : X.E)
    (fun y hy s l => twAn_omPhi_supp P hP hal hbe hba hbb y hy s l) _ _ _ x h1 s l
  exact twAn_qpow_mul (hA i hi) h2

theorem twAn_psiSupp {m2 : ℕ} (hm : R.m = m2 + 2) (hM : m2 + 1 ≤ cst.M) :
    ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ hal : AutY X R m2, TwBdd (Pr := Pr) m2 P.1 hal →
      ∀ (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1))), PsiAt Ch sel mu cst m2 P hal x₀ y' ≠ 0 →
        ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y' i) := by
  intro P hP hal hba x₀ y' h i
  have hc : 1 ≤ cOf R m2 := by unfold cOf; omega
  unfold PsiAt at h
  have h2 := twAn_omPhi_supp P hP hal 1 hba (twBdd_one _ _) _ h ⟨R.N m2, by omega⟩ (Fin.castAdd _ i)
  rw [twAn_joinCol hc, ciInX_castAdd] at h2
  exact twAn_qpow_mul hM h2

theorem twAn_psiSuppX {m2 : ℕ} (hA : m2 + 1 ≤ cst.A) :
    ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ hal : AutY X R m2, TwBdd (Pr := Pr) m2 P.1 hal →
      ∀ (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1))), PsiAt Ch sel mu cst m2 P hal x₀ y' ≠ 0 →
        ∀ s l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.A * x₀ (Pi.single s 1) l) := by
  intro P hP hal hba x₀ y' h s l
  unfold PsiAt at h
  have h2 := twAn_omPhi_supp P hP hal 1 hba (twBdd_one _ _) _ h (Fin.castAdd _ s) (Fin.castAdd _ l)
  rw [twAn_joinCol_castAdd, ciInX_castAdd] at h2
  exact twAn_qpow_mul hA h2

theorem twAn_zero_int (P : HeightOneSpectrum (𝓞 X.E)) : IntAt P (0 : X.E) := ⟨0, 1, one_notMem P, by simp⟩

theorem twAn_psiInv {m2 : ℕ} (hm : R.m = m2 + 2) (hM : m2 + 1 ≤ cst.M) (hd : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1) :
    ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ hal : AutY X R m2, TwBdd (Pr := Pr) m2 P.1 hal →
      ∀ (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' z : Sp X.E (R.N (m2 + 1))), (∀ i, IntAt P.1 (((qOf P.1 : X.E) ^ cst.M)⁻¹ * z i)) →
        PsiAt Ch sel mu cst m2 P hal x₀ (y' + z) = PsiAt Ch sel mu cst m2 P hal x₀ y' := by
  intro P hP hal hba x₀ y' z hz
  unfold PsiAt
  apply twAn_omPhi_congr P hP (hd P hP).1 (by omega) hal 1 hba (twBdd_one _ _) hM
  intro s l
  have e := congrFun (twAn_joinCol_sub_y (c := cOf R (m2 + 1)) x₀ y' z (Pi.single s 1)) l
  rw [Pi.sub_apply] at e
  rw [e, ciInX_apply]
  split_ifs with hl
  · rw [Pi.smul_apply, smul_eq_mul, mul_left_comm]
    exact (twAn_atNL_int _ s).mul (hz _)
  · rw [mul_zero]
    exact twAn_zero_int P.1

theorem twAn_psiInvX {m2 : ℕ} (hm : R.m = m2 + 2) (hB : m2 + 1 ≤ cst.B) (hd : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1) :
    ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ hal : AutY X R m2, TwBdd (Pr := Pr) m2 P.1 hal →
      ∀ (x₀ z : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1))),
        (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.B)⁻¹ * z (Pi.single s 1) l)) →
          PsiAt Ch sel mu cst m2 P hal (x₀ + z) y' = PsiAt Ch sel mu cst m2 P hal x₀ y' := by
  intro P hP hal hba x₀ z y' hz
  unfold PsiAt
  apply twAn_omPhi_congr P hP (hd P hP).1 (by omega) hal 1 hba (twBdd_one _ _) hB
  intro s l
  have e := congrFun (joinColumn_add_sub (c := cOf R (m2 + 1)) x₀ z y' (Pi.single s 1)) l
  rw [Pi.sub_apply] at e
  rw [e, ciInX_apply]
  split_ifs with hl
  · have hZ : TwAnIntMap P.1 ((((qOf P.1 : X.E) ^ cst.B)⁻¹) • z) := twAn_intMap_of_entries _ fun s l => by
      simpa [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul] using hz s l
    have := hZ _ (fun l => twAn_funLeft_int s l) ⟨l.1, hl⟩
    simpa [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul] using this
  · rw [mul_zero]
    exact twAn_zero_int P.1

theorem twAn_xiInv {m2 : ℕ} (hm : R.m = m2 + 2) (hB : ∀ i, i < m2 → i + 1 ≤ cst.B)
    (hd : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1) :
    ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ (hal : AutY X R i) (hbe : AutY X R (i + 1)),
      TwBdd (Pr := Pr) i P.1 hal → TwBdd (Pr := Pr) (i + 1) P.1 hbe → ∀ x z : HomE X.E (R.N i) (R.N (i + 1)),
        (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.B)⁻¹ * z (Pi.single s 1) l)) →
          XiAt Ch sel mu cst i P hal hbe (x + z) = XiAt Ch sel mu cst i P hal hbe x := by
  intro i hi P hP hal hbe hba hbb x z hz
  have hsum : ∀ t, omPhi Ch sel mu cst i P hal hbe (Loc.xx1 (x + z) t) * cst.psi P (-Loc.chArg (Loc.xx1 (x + z) t)) =
      omPhi Ch sel mu cst i P hal hbe (Loc.xx1 x t) * cst.psi P (-Loc.chArg (Loc.xx1 x t)) := fun t => by
    rw [charArg_unipotentExtension_indep (x + z) x t]
    congr 1
    apply twAn_omPhi_congr P hP (hd P hP).1 (by omega) hal hbe hba hbb (hB i hi)
    intro s l
    rw [unipotentExtension_add_sub]
    split_ifs with hs hl
    · exact hz _ _
    · rw [mul_zero]
      exact twAn_zero_int P.1
    · rw [mul_zero]
      exact twAn_zero_int P.1
  simp only [XiAt, E1at, Loc.E1, hsum]

theorem twAn_dvd_of_div {P : HeightOneSpectrum (𝓞 X.E)} (hq : (qOf P).Prime) (k : ℕ) (h : IntAt P ((k : X.E) / (qOf P : X.E))) :
    qOf P ∣ k := by
  have hq0 : (qOf P : X.E) ≠ 0 := by exact_mod_cast hq.ne_zero
  have h3 : redP P (((k : ℤ) : X.E)) = 0 := by
    have e : (((k : ℤ) : X.E)) = (qOf P : X.E) * ((k : X.E) / (qOf P : X.E)) := by push_cast; field_simp
    rw [e, reduction_mul (ciIntAt_q (P := P) (q := qOf P)) h, redP_natCast_eq_zero (ciQ_mem P), zero_mul]
  rw [redP_intCast] at h3
  have h4 := (owedC_intCast_eq_iff (A := 𝓞 X.E ⧸ P.asIdeal) hq (ciCard P) (k : ℤ) 0).1 (by rw [h3, Int.cast_zero])
  rw [sub_zero] at h4
  exact_mod_cast h4

theorem twAn_deep {m2 : ℕ} (hm : R.m = m2 + 2) (hd : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1) (hc : cst.Ok)
    (hA : ∀ i, i < m2 → i + 1 ≤ cst.A) (hB : ∀ i, i < m2 → i + 1 ≤ cst.B)
    (hD : ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → i + 1 ≤ cst.D P)
    (hqK : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → (qOf P.1 : X.K) ≠ 0) :
    ∀ A' B', cst.A ≤ A' → cst.B ≤ B' → ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs →
      ∀ (hal : AutY X R i) (hbe : AutY X R (i + 1)), TwBdd (Pr := Pr) i P.1 hal → TwBdd (Pr := Pr) (i + 1) P.1 hbe →
        E1at Ch sel mu { cst with A := A', B := B' } i P hal hbe = E1at Ch sel mu cst i P hal hbe := by
  intro A' B' hA' hB' i hi P hP hal hbe hba hbb
  funext xj
  obtain ⟨hq, hu⟩ := hd P hP
  have hq0 : (qOf P.1 : X.E) ≠ 0 := by exact_mod_cast hq.ne_zero
  let G : (Loc.FC (R.N i) (cOf R i) (R.N (i + 1)) (cOf R (i + 1)) → X.E) → X.K := fun t =>
    omPhi Ch sel mu cst i P hal hbe (Loc.xx1 xj t) * cst.psi P (-Loc.chArg (Loc.xx1 xj t))
  have hvan : ∀ A, i + 1 ≤ A → ∀ k : Loc.FC (R.N i) (cOf R i) (R.N (i + 1)) (cOf R (i + 1)) → ℕ, (∃ f, ¬ qOf P.1 ∣ k f) →
      G (fun f => twAnPhi (qOf P.1) (A + 1) (k f)) = 0 := by
    intro A hA0 k ⟨f, hf⟩
    by_contra hG
    have hΦ := left_ne_zero_of_mul hG
    have hs := twAn_omPhi_supp P hP hal hbe hba hbb _ hΦ f.1.2 f.1.1
    rw [unipotentExtension_freeCoord] at hs
    have h2 := twAn_qpow_mul hA0 hs
    have e : (qOf P.1 : X.E) ^ A * twAnPhi (qOf P.1) (A + 1) (k f) = (k f : X.E) / (qOf P.1 : X.E) := by
      unfold twAnPhi
      rw [pow_succ, mul_div_assoc']
      exact mul_div_mul_left _ _ (pow_ne_zero A hq0)
    rw [e] at h2
    exact hf (twAn_dvd_of_div hq (k f) h2)
  have hinv : ∀ A B, i + 1 ≤ B → ∀ a b : Loc.FC (R.N i) (cOf R i) (R.N (i + 1)) (cOf R (i + 1)) → ℕ,
      G (fun f => twAnPhi (qOf P.1) A (a f + (qOf P.1) ^ (A + B) * b f)) = G (fun f => twAnPhi (qOf P.1) A (a f)) := by
    intro A B hB0 a b
    set t : Loc.FC (R.N i) (cOf R i) (R.N (i + 1)) (cOf R (i + 1)) → X.E := fun f => twAnPhi (qOf P.1) A (a f) with ht
    set δ : Loc.FC (R.N i) (cOf R i) (R.N (i + 1)) (cOf R (i + 1)) → X.E := fun f => (qOf P.1 : X.E) ^ B * (b f : X.E) with hδ
    have htd : (fun f => twAnPhi (E := X.E) (qOf P.1) A (a f + (qOf P.1) ^ (A + B) * b f)) = t + δ := by
      funext f
      simp only [ht, hδ, Pi.add_apply, twAnPhi]
      push_cast
      rw [pow_add, add_div, mul_assoc, mul_div_cancel_left₀ _ (pow_ne_zero _ hq0)]
    have hδint : ∀ f, IntAt P.1 (((qOf P.1 : X.E) ^ (i + 1))⁻¹ * δ f) := fun f => by
      have e : ((qOf P.1 : X.E) ^ (i + 1))⁻¹ * δ f = (qOf P.1 : X.E) ^ (B - (i + 1)) * (b f : X.E) := by
        simp only [hδ]
        have : (qOf P.1 : X.E) ^ B = (qOf P.1 : X.E) ^ (B - (i + 1)) * (qOf P.1 : X.E) ^ (i + 1) := by
          rw [← pow_add, Nat.sub_add_cancel hB0]
        rw [this]
        field_simp
      rw [e]
      exact (twAn_qpow_int P.1 _).mul (by exact_mod_cast ciIntAt_intCast (P := P.1) (b f : ℤ))
    rw [htd]
    have hΦ : omPhi Ch sel mu cst i P hal hbe (Loc.xx1 xj (t + δ)) = omPhi Ch sel mu cst i P hal hbe (Loc.xx1 xj t) := by
      apply twAn_omPhi_congr P hP hq (by omega) hal hbe hba hbb (le_refl (i + 1))
      intro s l
      rw [xx1_add_sub_xx1_single_eq_dite]
      split_ifs with hf
      · exact hδint _
      · rw [mul_zero]
        exact twAn_zero_int P.1
    show omPhi Ch sel mu cst i P hal hbe (Loc.xx1 xj (t + δ)) * cst.psi P (-Loc.chArg (Loc.xx1 xj (t + δ))) =
      omPhi Ch sel mu cst i P hal hbe (Loc.xx1 xj t) * cst.psi P (-Loc.chArg (Loc.xx1 xj t))
    rw [hΦ]
    by_cases h0 : omPhi Ch sel mu cst i P hal hbe (Loc.xx1 xj t) = 0
    · rw [h0, zero_mul, zero_mul]
    congr 1
    have hsupp := twAn_omPhi_supp P hP hal hbe hba hbb _ h0
    have hDi := hD i hi P hP

    have hdiff : IntAt P.1 (Loc.chArg (Loc.xx1 xj (t + δ)) - Loc.chArg (Loc.xx1 xj t)) := by
      unfold Loc.chArg
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_induction _ (IntAt P.1) (fun _ _ ha hb => ha.add hb) (twAn_zero_int P.1) fun j _ => ?_
      rw [twAn_chArg_term, twAn_chArg_term]
      split_ifs with hj
      · rw [xx1_add_sub_xx1_single_eq_dite]
        split_ifs with hf
        · exact (twAn_qpow_int P.1 B).mul (by exact_mod_cast ciIntAt_intCast (P := P.1) (b _ : ℤ))
        · exact twAn_zero_int P.1
      · rw [sub_self]
        exact twAn_zero_int P.1
    have hcD : IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * Loc.chArg (Loc.xx1 xj t)) := by
      unfold Loc.chArg
      rw [Finset.mul_sum]
      refine Finset.sum_induction _ (IntAt P.1) (fun _ _ ha hb => ha.add hb) (twAn_zero_int P.1) fun j _ => ?_
      rw [twAn_chArg_term]
      split_ifs with hj
      · exact twAn_qpow_mul hDi (hsupp _ _)
      · rw [mul_zero]
        exact twAn_zero_int P.1
    have e : -Loc.chArg (Loc.xx1 xj (t + δ)) = -Loc.chArg (Loc.xx1 xj t) + -(Loc.chArg (Loc.xx1 xj (t + δ)) - Loc.chArg (Loc.xx1 xj t)) := by
      ring
    rw [e, hc.psi_add P _ _ (by rw [mul_neg]; exact ciIntAt_neg hcD)
      (by rw [mul_neg]; exact ciIntAt_neg ((twAn_qpow_int P.1 _).mul hdiff)),
      hc.psi_int P _ (ciIntAt_neg hdiff), mul_one]
  have H := twAn_deep_abs (ι := Loc.FC (R.N i) (cOf R i) (R.N (i + 1)) (cOf R (i + 1))) hq0 (hqK P hP) G hvan hinv
    (hA i hi) (hB i hi) hA' hB'
  unfold E1at Loc.E1
  exact H

theorem twAnQ_of {m2 : ℕ} (hm : R.m = m2 + 2) (hd : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1) (hc : cst.Ok)
    (hA : m2 + 1 ≤ cst.A) (hB : m2 + 1 ≤ cst.B) (hM : m2 + 1 ≤ cst.M) (hD : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → m2 ≤ cst.D P)
    (hqK : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → (qOf P.1 : X.K) ≠ 0) : TwAnQ Ch sel mu cst m2 where
  deep := twAn_deep hm hd hc (fun i hi => by omega) (fun i hi => by omega) (fun i hi P hP => by have := hD P hP; omega) hqK
  psiSupp := twAn_psiSupp hm hM
  psiInv := twAn_psiInv hm hM hd
  xiSupp := twAn_xiSupp (fun i hi => by omega)
  xiInv := twAn_xiInv hm (fun i hi => by omega) hd
  psiSuppX := twAn_psiSuppX hA
  psiInvX := twAn_psiInvX hm hB hd

theorem twAnQ_twCst {G : ChGlob X R.m} {m2 : ℕ} (hm : R.m = m2 + 2) (hPr : Pr.Ok) (hCh : Ch.Ok) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1)
    (hK : TwCstQ (Pr := Pr) sel mu G) (hd : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1) :
    TwAnQ Ch sel mu (twCst Ch sel mu G) m2 := by
  have h2 := R.two_le_m
  refine twAnQ_of hm hd (twCst_ok hPr hCh h4 hK) (by show m2 + 1 ≤ R.m + 1; omega) (by show m2 + 1 ≤ R.m + 1; omega)
    (by show m2 + 1 ≤ R.m; omega) (fun P hP => by rw [twCst_D_Q hP]; omega) (fun P hP => ?_)
  exact_mod_cast (hd P hP).1.ne_zero

end TwAnX

end Formalism.L2.Col
