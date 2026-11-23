import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.HomGMonomial

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf.ColF

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt Formalism.MainNotions.LemmaBAlt.B2 Formalism.MainNotions.ColumnSystems.Pf.Col Formalism.MainNotions.ColumnSystems.Pf.GenusGluing

section

variable {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {O : Type} [CommRing O] [IsDomain O]
  {β : GlobalTheory X} (j : Fin (numSeg X.TT)) (ka : Fin (2 * segS X.TT j + 1 + 1) → Fin X.m → ℤ)

theorem ioD_X (v : BVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X v) =
      (MvPolynomial.X (symVar C0 CE1 CE2 X j v) : RHH O X) ^ symLev X.p C0 CE1 CE2 X j v := by
  unfold ioD ioA
  exact aeval_X _ _

theorem ioD_chain (a : Fin (2 * segS X.TT j + 1)) (b : Fin X.m) :
    ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (MvPolynomial.X (a, b))) =
      monomial (Finsupp.single (phiS X j (a.succ, Fin.natAdd 1 b)) (PS X j a.succ)) 1 := by
  rw [phiS_succ X j C0 CE1 CE2 a b,
    show PS X j a.succ = symLev X.p C0 CE1 CE2 X j (Sum.inl (a.castSucc, b)) from lev_succ X j C0 CE1 CE2 a b,
    ← X_pow_eq_monomial, rename_X]
  exact ioD_X j _

private theorem ringHom_Kcol_eq_KG {R P : Type} [CommRing R] [CommRing P] {N n : ℕ}
    (f : MvPolynomial (Fin N × Fin n) R →+* P) (ka : Fin (N + 1) → Fin n → ℤ) (c : ℤ) :
    ∀ t, t ≤ N → ∀ J, f (Kcol R ka c t J) = KG c (hsOf ka c) (fun a b => f (xOf R N n a b)) t J := by
  intro t
  induction t with
  | zero =>
    intro _ J
    show f (extOne J) = extOne J
    exact extOne_map f J
  | succ t ih =>
    intro ht J
    have htN : t < N := ht
    rw [Joints.Kcol_succ R ka c t htN]
    show _ = colStep c (hsOf ka c t) (hsOf ka c (t + 1)) (fun b => f (xOf R N n t b))
      (KG c (hsOf ka c) (fun a b => f (xOf R N n a b)) t) J
    rw [colStep_map]
    have h1 : hsOf ka c t = colH (ka (⟨t, htN⟩ : Fin N).castSucc) c := by
      unfold hsOf
      congr 2
      apply Fin.ext
      show min t N = t
      omega
    have h2 : hsOf ka c (t + 1) = colH (ka (⟨t, htN⟩ : Fin N).succ) c := by
      unfold hsOf
      congr 2
      apply Fin.ext
      show min (t + 1) N = t + 1
      omega
    rw [h1, h2]
    congr 1
    · funext b
      simp [xOf, letVec, htN]
    · funext J'
      exact (ih (le_of_lt htN) J')

theorem tan_eq_KG (c : ℤ) (J : Finset (Fin X.m)) :
    ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kcol (KK O) ka c (2 * segS X.TT j + 1) J)) =
      KG c (hsOf ka c) (fun a b => ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _)
        (xOf (KK O) (2 * segS X.TT j + 1) X.m a b))) (2 * segS X.TT j + 1) J := by
  exact ringHom_Kcol_eq_KG ((ioD O C0 CE1 CE2 mu X β j).toRingHom.comp (rename (chainEmb _ X.m _)).toRingHom)
    ka c _ le_rfl J

private theorem homG_monomial_mul_of_homG {σ R : Type} [CommRing R] (φ : (σ →₀ ℕ) →+ ℕ) (M : σ →₀ ℕ) (d : ℕ)
    (Q : MvPolynomial σ R) (hQ : HomG φ d Q) : HomG φ (φ M + d) (monomial M 1 * Q) := by
  classical
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
  rw [map_add, Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ha), hQ b hb]

theorem sg_hom (φ : MonH X →+ ℕ) (wt : Fin (2 * segS X.TT j + 1) → ℕ)
    (hwt : ∀ a b, φ (Finsupp.single (phiS X j (a.succ, Fin.natAdd 1 b)) 1) = wt a) (c : ℤ) (J : Finset (Fin X.m)) :
    HomW φ (φ (plS C0 CE1 CE2 mu X β j c) + ∑ a : Fin (2 * segS X.TT j + 1),
        if colH (ka a.castSucc) c = colH (ka a.succ) c then 0 else PS X j a.succ * wt a)
      ((monomial (plS C0 CE1 CE2 mu X β j c) 1 : RHH O X) *
        ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kcol (KK O) ka c (2 * segS X.TT j + 1) J))) := by
  have hx : ∀ (a : ℕ) (b : Fin X.m), HomG φ
      (if h : a < 2 * segS X.TT j + 1 then PS X j (⟨a, h⟩ : Fin _).succ * wt ⟨a, h⟩ else 0)
      (ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (xOf (KK O) (2 * segS X.TT j + 1) X.m a b))) := by
    intro a b
    by_cases h : a < 2 * segS X.TT j + 1
    · rw [dif_pos h]
      have e : xOf (KK O) (2 * segS X.TT j + 1) X.m a b = MvPolynomial.X (⟨a, h⟩, b) := by
        simp [xOf, h]
      rw [e, ioD_chain]
      have hm := homG_monomial φ
        (Finsupp.single (phiS X j ((⟨a, h⟩ : Fin _).succ, Fin.natAdd 1 b)) (PS X j (⟨a, h⟩ : Fin _).succ)) (1 : KK O)
      rwa [phi_single, hwt] at hm
    · have e : xOf (KK O) (2 * segS X.TT j + 1) X.m a b = 0 := by
        simp [xOf, h]
      rw [e, map_zero, map_zero]
      intro m hm
      simp at hm
  have hK := KG_hom φ c (hsOf ka c) _ _ hx (2 * segS X.TT j + 1) J
  have hK' : HomG φ (∑ a ∈ Finset.range (2 * segS X.TT j + 1), if hsOf ka c a = hsOf ka c (a + 1) then 0 else
        (if h : a < 2 * segS X.TT j + 1 then PS X j (⟨a, h⟩ : Fin _).succ * wt ⟨a, h⟩ else 0))
      (ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kcol (KK O) ka c (2 * segS X.TT j + 1) J))) := by
    rw [tan_eq_KG]
    exact hK
  have hS : (∑ a ∈ Finset.range (2 * segS X.TT j + 1), if hsOf ka c a = hsOf ka c (a + 1) then 0 else
        (if h : a < 2 * segS X.TT j + 1 then PS X j (⟨a, h⟩ : Fin _).succ * wt ⟨a, h⟩ else 0)) =
      ∑ a : Fin (2 * segS X.TT j + 1),
        if colH (ka a.castSucc) c = colH (ka a.succ) c then 0 else PS X j a.succ * wt a := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun a _ => ?_
    have ha := a.isLt
    rw [dif_pos a.isLt]
    have e1 : hsOf ka c a = colH (ka a.castSucc) c := by
      unfold hsOf
      congr 2
      apply Fin.ext
      show min (a : ℕ) _ = a
      omega
    have e2 : hsOf ka c (a + 1) = colH (ka a.succ) c := by
      unfold hsOf
      congr 2
      apply Fin.ext
      show min ((a : ℕ) + 1) _ = a + 1
      omega
    simp only [e1, e2, Fin.eta]
  rw [hS] at hK'
  exact homG_monomial_mul_of_homG φ _ _ _ hK'

end

section

variable {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {O : Type} [CommRing O] [IsDomain O]
  {β : GlobalTheory X} (j : Fin (numSeg X.TT)) (ka : Fin (2 * segS X.TT j + 1 + 1) → Fin X.m → ℤ)
  {vecc : Fin (2 * segS X.TT j + 1) → Bool} {B : Fin (2 * segS X.TT j + 1) → ℕ}

theorem nd_single (v : VarH X) : ndHom X (Finsupp.single v 1) = wN X v := by
  show degUS (hhLetters X.TT) 1 (Finsupp.single v 1) = wN X v
  rw [degUS, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same]
  simp [wN, hhLetters]

private theorem colH_mono_of_forall_le {n : ℕ} {u v : Fin n → ℤ} (huv : ∀ b, u b ≤ v b) (c : ℤ) :
    colH u c ≤ colH v c := by
  unfold colH
  apply Finset.card_le_card
  intro b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
  exact le_trans hb (huv b)

private theorem colH_eq_zero_of_forall_lt {n : ℕ} {u : Fin n → ℤ} (c : ℤ) (hu : ∀ b, u b < c) : colH u c = 0 := by
  unfold colH
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro b _
  exact not_le.mpr (hu b)

private theorem PH_ka_le_nu {N K : ℕ} {vecc : Fin N → Bool} {B : Fin N → ℕ} {ka : Fin (N + 1) → Fin K → ℤ}
    {nu : ℕ → ℤ} (h : PH vecc B ka nu) : ∀ (i : Fin (N + 1)) (b : Fin K), ka i b ≤ nu i := by
  intro i
  induction i using Fin.induction with
  | zero =>
    intro b
    rw [h.ka0]
    simp [h.nu0]
  | succ a ih =>
    intro b
    have hm := h.numono a
    have hs := h.kastep a
    rw [Fin.val_succ]
    by_cases hv : vecc a = true
    · exact h.C a hv b
    · rw [if_neg hv] at hs
      have h1 := hs.1 b
      have h2 := ih b
      rw [Fin.coe_castSucc] at h2
      omega

private theorem colH_muP_zero_castSucc_and_succ_of_PH {N K : ℕ} {vecc : Fin N → Bool} {B : Fin N → ℕ} {ka : Fin (N + 1) → Fin K → ℤ}
    {nu : ℕ → ℤ} (h : PH vecc B ka nu) (c : ℤ) :
    colH (muP nu ka (0 : Fin (N + 1)).castSucc) c = (if c ≤ nu 0 then 1 else 0) + (if c ≤ 0 then K else 0) ∧
    colH (muP nu ka (0 : Fin (N + 1)).succ) c = (if c ≤ nu 1 then 1 else 0) + (if c ≤ 0 then K else 0) := by
  constructor
  · rw [Fin.castSucc_zero]
    exact H0 nu ka c
  · rw [HS, h.ka0, colH_zero]
    simp

private theorem colH_muP_succ_castSucc_and_succ_succ {N K : ℕ} {ka : Fin (N + 1) → Fin K → ℤ} {nu : ℕ → ℤ} (c : ℤ) (a : Fin N) :
    colH (muP nu ka a.succ.castSucc) c = (if c ≤ nu (↑a + 1) then 1 else 0) + colH (ka a.castSucc) c ∧
    colH (muP nu ka a.succ.succ) c = (if c ≤ nu (↑a + 1 + 1) then 1 else 0) + colH (ka a.succ) c := by
  constructor
  · rw [← Fin.succ_castSucc, HS]
    simp
  · rw [HS]
    simp

private theorem colH_ka_eq_zero_of_PH_of_nu_lt {N K : ℕ} {vecc : Fin N → Bool} {B : Fin N → ℕ} {ka : Fin (N + 1) → Fin K → ℤ}
    {nu : ℕ → ℤ} (h : PH vecc B ka nu) (c : ℤ) (a : Fin N) (hc : nu (↑a + 1) < c) :
    (vecc a = true → colH (ka a.castSucc) c = 0 ∧ colH (ka a.succ) c = 0) ∧
    (vecc a = false → colH (ka a.castSucc) c = 0) := by
  have hI := PH_ka_le_nu h
  have hm := h.numono ↑a
  constructor
  · intro hv
    have hs := h.kastep a
    rw [if_pos hv] at hs
    constructor
    · apply colH_eq_zero_of_forall_lt c
      intro b
      have h1 := hs.1 b
      have h2 := h.C a hv b
      omega
    · apply colH_eq_zero_of_forall_lt c
      intro b
      have h2 := h.C a hv b
      omega
  · intro _
    apply colH_eq_zero_of_forall_lt c
    intro b
    have h1 := hI a.castSucc b
    rw [Fin.coe_castSucc] at h1
    omega

private theorem colH_ka_le_by_vecc_of_PH {N K : ℕ} {vecc : Fin N → Bool} {B : Fin N → ℕ} {ka : Fin (N + 1) → Fin K → ℤ}
    {nu : ℕ → ℤ} (h : PH vecc B ka nu) (c : ℤ) (a : Fin N) :
    (vecc a = true → colH (ka a.castSucc) c ≤ colH (ka a.succ) c) ∧
    (vecc a = false → colH (ka a.succ) c ≤ colH (ka a.castSucc) c ∧ nu (↑a + 1 + 1) = nu (↑a + 1)) := by
  have hs := h.kastep a
  constructor
  · intro hv
    rw [if_pos hv] at hs
    exact colH_mono_of_forall_le hs.1 c
  · intro hv
    rw [if_neg (by simp [hv])] at hs
    exact ⟨colH_mono_of_forall_le hs.1 c, h.nucov a hv⟩

private theorem wN_phiS_castAdd_zero_eq_ite_lamS (X : Loc) (j : Fin (numSeg X.TT)) (t : Fin (2 * segS X.TT j + 1 + 1)) :
    wN X (Formalism.MainNotions.ColumnSystems.Pf.phiS X j (t, Fin.castAdd X.m 0)) = if (lamS X j t).2 = false then 1 else 0 := by
  simp [wN, Formalism.MainNotions.ColumnSystems.Pf.phiS]

private theorem wN_phiS_succ_natAdd_eq_ite_lamS (X : Loc) (j : Fin (numSeg X.TT)) (a : Fin (2 * segS X.TT j + 1)) (b : Fin X.m) :
    wN X (Formalism.MainNotions.ColumnSystems.Pf.phiS X j (a.succ, Fin.natAdd 1 b)) = if (lamS X j a.succ).2 = true then 1 else 0 := by
  simp [wN, Formalism.MainNotions.ColumnSystems.Pf.phiS]

theorem colHomC (h : PH vecc B ka (nuS C0 CE1 CE2 mu X β j)) (hvec : ∀ a, vecc a = (lamS X j a.succ).2) (c : ℤ)
    (J : Finset (Fin X.m)) :
    HomW (ndHom X) (oCS C0 CE1 CE2 mu X β j ka c)
      ((monomial (plS C0 CE1 CE2 mu X β j c) 1 : RHH O X) *
        ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kcol (KK O) ka c (2 * segS X.TT j + 1) J))) := by
  have hg := sg_hom (C0 := C0) (CE1 := CE1) (CE2 := CE2) (mu := mu) (β := β) (O := O) j ka (ndHom X)
    (fun a => if vecc a = true then 1 else 0)
    (fun a b => by rw [nd_single, wN_phiS_succ_natAdd_eq_ite_lamS, ← hvec a]) c J
  have hD : ndHom X (plS C0 CE1 CE2 mu X β j c) + ∑ a : Fin (2 * segS X.TT j + 1),
      (if colH (ka a.castSucc) c = colH (ka a.succ) c then 0 else PS X j a.succ * (if vecc a = true then 1 else 0)) =
      oCS C0 CE1 CE2 mu X β j ka c := by
    rw [phi_plS]
    simp only [nd_single, wN_phiS_castAdd_zero_eq_ite_lamS]
    unfold oCS oc
    rw [Fin.sum_univ_succ (n := 2 * segS X.TT j + 1), Fin.sum_univ_succ (n := 2 * segS X.TT j + 1),
      add_assoc, ← Finset.sum_add_distrib]
    congr 1
    · have hc := colH_muP_zero_castSucc_and_succ_of_PH h c
      have hm : nuS C0 CE1 CE2 mu X β j 0 ≤ nuS C0 CE1 CE2 mu X β j 1 := h.numono 0
      have h0 := h.nu0
      have hiff : IsCostly (muP (nuS C0 CE1 CE2 mu X β j) ka) c 0 ↔
          ((if c ≤ nuS C0 CE1 CE2 mu X β j 0 then 1 else 0) + (if c ≤ 0 then X.m else 0) <
            (if c ≤ nuS C0 CE1 CE2 mu X β j 1 then 1 else 0) + (if c ≤ 0 then X.m else 0) ∧
            1 ≤ (if c ≤ nuS C0 CE1 CE2 mu X β j 0 then 1 else 0) + (if c ≤ 0 then X.m else 0) ∨
          (if c ≤ nuS C0 CE1 CE2 mu X β j 1 then 1 else 0) + (if c ≤ 0 then X.m else 0) <
            (if c ≤ nuS C0 CE1 CE2 mu X β j 0 then 1 else 0) + (if c ≤ 0 then X.m else 0) ∧
            (if c ≤ nuS C0 CE1 CE2 mu X β j 0 then 1 else 0) + (if c ≤ 0 then X.m else 0) ≤ 1) := by
        unfold IsCostly
        rw [hc.1, hc.2]
      simp only [hiff, lamS_zero, Bool.true_eq_false, ↓reduceIte, mul_zero, ite_self, Fin.val_zero, zero_add]
      split_ifs <;> omega
    · refine Finset.sum_congr rfl fun a _ => ?_
      have hc := colH_muP_succ_castSucc_and_succ_succ (nu := nuS C0 CE1 CE2 mu X β j) (ka := ka) c a
      have hm := h.numono (↑a + 1)
      have h6 := colH_ka_eq_zero_of_PH_of_nu_lt h c a
      have h7 := colH_ka_le_by_vecc_of_PH h c a
      have hiff : IsCostly (muP (nuS C0 CE1 CE2 mu X β j) ka) c a.succ ↔
          ((if c ≤ nuS C0 CE1 CE2 mu X β j (↑a + 1) then 1 else 0) + colH (ka a.castSucc) c <
            (if c ≤ nuS C0 CE1 CE2 mu X β j (↑a + 1 + 1) then 1 else 0) + colH (ka a.succ) c ∧
            1 ≤ (if c ≤ nuS C0 CE1 CE2 mu X β j (↑a + 1) then 1 else 0) + colH (ka a.castSucc) c ∨
          (if c ≤ nuS C0 CE1 CE2 mu X β j (↑a + 1 + 1) then 1 else 0) + colH (ka a.succ) c <
            (if c ≤ nuS C0 CE1 CE2 mu X β j (↑a + 1) then 1 else 0) + colH (ka a.castSucc) c ∧
            (if c ≤ nuS C0 CE1 CE2 mu X β j (↑a + 1) then 1 else 0) + colH (ka a.castSucc) c ≤ 1) := by
        unfold IsCostly
        rw [hc.1, hc.2]
      simp only [hiff, ← hvec a, Fin.val_succ]
      by_cases hv : vecc a = true
      · have hAB := h7.1 hv
        simp only [hv, Bool.true_eq_false, ↓reduceIte, mul_zero, mul_one, ite_self]
        by_cases hcn : nuS C0 CE1 CE2 mu X β j (↑a + 1) < c
        · obtain ⟨z1, z2⟩ := (h6 hcn).1 hv
          split_ifs <;> omega
        · split_ifs <;> omega
      · have hv' : vecc a = false := by simpa using hv
        obtain ⟨hBA, hnu⟩ := h7.2 hv'
        simp only [hv', Bool.false_eq_true, ↓reduceIte, mul_zero, mul_one]
        by_cases hcn : nuS C0 CE1 CE2 mu X β j (↑a + 1) < c
        · have z1 := (h6 hcn).2 hv'
          split_ifs <;> omega
        · split_ifs <;> omega
  rw [hD] at hg
  exact hg

theorem colPolC (h : PH vecc B ka (nuS C0 CE1 CE2 mu X β j)) (c : ℤ) (J : Finset (Fin X.m)) :
    (monomial (plS C0 CE1 CE2 mu X β j c) 1 : RHH O X) *
        ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kcol (KK O) ka c (2 * segS X.TT j + 1) J)) ∈
      Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgCS C0 CE1 CE2 mu X β j ka c) := by
  unfold Pol
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  simp only [Set.mem_setOf_eq]
  intro l
  have hg := sg_hom (C0 := C0) (CE1 := CE1) (CE2 := CE2) (mu := mu) (β := β) (O := O) j ka
    { toFun := fun m => multideg m l, map_zero' := by simp [multideg],
      map_add' := fun a b => multideg_add a b l }
    (fun a => if lamS X j a.succ = l then 1 else 0)
    (fun a b => by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [Formalism.MainNotions.ColumnSystems.Pf.phiS, md_single]) c J m hm
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hg
  rw [hg, md_plS]
  unfold dgCS
  rw [Fin.sum_univ_succ (n := 2 * segS X.TT j + 1), Fin.sum_univ_succ (n := 2 * segS X.TT j + 1),
    add_assoc, ← Finset.sum_add_distrib]
  congr 1
  · have hc := colH_muP_zero_castSucc_and_succ_of_PH h c
    have hm : nuS C0 CE1 CE2 mu X β j 0 ≤ nuS C0 CE1 CE2 mu X β j 1 := h.numono 0
    have hiff : IsUsed (muP (nuS C0 CE1 CE2 mu X β j) ka) c 0 ↔
        (if c ≤ nuS C0 CE1 CE2 mu X β j 0 then 1 else 0) + (if c ≤ 0 then X.m else 0) ≠
          (if c ≤ nuS C0 CE1 CE2 mu X β j 1 then 1 else 0) + (if c ≤ 0 then X.m else 0) := by
      unfold IsUsed
      rw [hc.1, hc.2]
    simp only [dgS, hiff, PS, Fin.val_zero, zero_add]
    split_ifs <;> omega
  · refine Finset.sum_congr rfl fun a _ => ?_
    have ha := a.isLt
    have hc := colH_muP_succ_castSucc_and_succ_succ (nu := nuS C0 CE1 CE2 mu X β j) (ka := ka) c a
    have hm := h.numono (↑a + 1)
    have h6 := colH_ka_eq_zero_of_PH_of_nu_lt h c a
    have h7 := colH_ka_le_by_vecc_of_PH h c a
    have hiff : IsUsed (muP (nuS C0 CE1 CE2 mu X β j) ka) c a.succ ↔
        (if c ≤ nuS C0 CE1 CE2 mu X β j (↑a + 1) then 1 else 0) + colH (ka a.castSucc) c ≠
          (if c ≤ nuS C0 CE1 CE2 mu X β j (↑a + 1 + 1) then 1 else 0) + colH (ka a.succ) c := by
      unfold IsUsed
      rw [hc.1, hc.2]
    simp only [dgS, hiff, PS, Fin.val_succ]
    by_cases hv : vecc a = true
    · have hAB := h7.1 hv
      by_cases hcn : nuS C0 CE1 CE2 mu X β j (↑a + 1) < c
      · obtain ⟨z1, z2⟩ := (h6 hcn).1 hv
        split_ifs <;> omega
      · split_ifs <;> omega
    · have hv' : vecc a = false := by simpa using hv
      obtain ⟨hBA, hnu⟩ := h7.2 hv'
      by_cases hcn : nuS C0 CE1 CE2 mu X β j (↑a + 1) < c
      · have z1 := (h6 hcn).2 hv'
        split_ifs <;> omega
      · split_ifs <;> omega

end

end Formalism.MainNotions.ColumnSystems.Pf.ColF
