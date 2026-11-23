import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CardStabilizerForgetFr
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa
import Formalism.LocalToGlobal.Columns.LevGCount
import Formalism.LocalToGlobal.Columns.RowFormsLemmas
import Formalism.LocalToGlobal.Columns.ColFormsLemmas

noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.TopStep

section Diag

variable {κ K : Type} [CommRing κ] [Field K] {N n : ℕ}

theorem lev_ext {l l' : Lev κ K n} (e : l.H = l'.H) (e' : ∀ a h h', l.lam ⟨a, h⟩ = l'.lam ⟨a, h'⟩) : l = l' := by
  obtain ⟨H, lam⟩ := l
  obtain ⟨H', lam'⟩ := l'
  obtain rfl : H = H' := e
  obtain rfl : lam = lam' := MonoidHom.ext fun a => e' a.1 a.2 a.2
  rfl

def levDiag (h : n ≤ N) (l : Lev κ K n) : Lev κ K N where
  H := l.H.map (diagEmb κ h)
  lam := l.lam.comp (l.H.equivMapOfInjective _ (diagEmb_injective h)).symm.toMonoidHom

variable (h : n ≤ N) (l : Lev κ K n)

theorem mem_levDiag (a : GL (Fin N) κ) : a ∈ (levDiag h l).H ↔ ∃ g ∈ l.H, diagEmb κ h g = a := Iff.rfl

theorem diagEmb_mem_levDiag (g : GL (Fin n) κ) : diagEmb κ h g ∈ (levDiag h l).H ↔ g ∈ l.H :=
  Subgroup.mem_map_iff_mem (diagEmb_injective h)

theorem levDiag_lam {a : GL (Fin N) κ} {g : GL (Fin n) κ} (e : a = diagEmb κ h g) (ha : a ∈ (levDiag h l).H) (hg : g ∈ l.H) :
    (levDiag h l).lam ⟨a, ha⟩ = l.lam ⟨g, hg⟩ := by
  subst e
  exact congrArg l.lam ((l.H.equivMapOfInjective _ (diagEmb_injective h)).symm_apply_apply ⟨g, hg⟩)

theorem firstBlock_diagEmb_eq {r : ℕ} (hr : r ≤ n) (bl : List ℕ) (g : GL (Fin n) κ) (hg : g ∈ blockUT n κ r bl)
    (hg' : diagEmb κ h g ∈ blockUT N κ r bl) : blk0 N κ (hr.trans h) bl ⟨_, hg'⟩ = blk0 n κ hr bl ⟨g, hg⟩ := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact diagMat_of_lt (g : Matrix (Fin n) (Fin n) κ) (i := Fin.castLE (hr.trans h) i) (j := Fin.castLE (hr.trans h) j)
    (lt_of_lt_of_le i.2 hr) (lt_of_lt_of_le j.2 hr)

theorem diagEmb_mem_blockUT' {r : ℕ} (bl : List ℕ) {g : GL (Fin n) κ} (hg : g ∈ blockUT n κ r bl) :
    diagEmb κ h g ∈ blockUT N κ r bl := by
  refine mem_btG.2 fun i j hij => ?_
  have hne : i ≠ j := fun e => by rw [e] at hij; omega
  rw [diagEmb_val]
  by_cases hi : i.1 < n
  · by_cases hj : j.1 < n
    · rw [diagMat_of_lt _ hi hj]
      exact mem_btG.1 hg ⟨i.1, hi⟩ ⟨j.1, hj⟩ hij
    · rw [diagMat_of_not_right _ _ hj, Matrix.one_apply_ne hne]
  · rw [diagMat_of_not_left _ _ hi, Matrix.one_apply_ne hne]

theorem levDiag_HPar {r t m : ℕ} (hN : N = n + 1) (hn : n = r + m * t) (hr : r ≤ n) (hr' : r ≤ N) (H₀ : Subgroup (GL (Fin r) κ))
    (lam₀ : H₀ →* Kˣ) (χ : ℕ → κˣ →* Kˣ) :
    levDiag h (⟨HPar n κ hr (List.replicate m t) H₀, lamPar hr _ lam₀ χ⟩ : Lev κ K n) =
      ⟨HPar N κ hr' (List.replicate m t) H₀ ⊓ fixCol N κ (r + m * t),
        (lamPar hr' _ lam₀ χ).comp (Subgroup.inclusion inf_le_left)⟩ := by
  subst hN hn
  have hc : ∀ i, r + m * t ≤ i → coarse r (List.replicate m t) i = m + 1 := fun i hi => by
    rw [coarse_of_le (by omega), blkIdx_replicate_of_le t m _ (by omega)]
  refine lev_ext (Subgroup.ext fun M => ⟨?_, ?_⟩) ?_
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨h1, h2⟩ := mem_HPar.1 hg
    exact ⟨mem_HPar.2 ⟨diagEmb_mem_blockUT' h _ h1, by rwa [firstBlock_diagEmb_eq h hr _ g h1]⟩, diagEmb_mem_fixCol _ le_rfl g⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨h3, h4⟩ := mem_HPar.1 h1
    obtain ⟨g, rfl, hge⟩ := exists_diagEmb M h2 fun j hj => mem_btG.1 h3 _ j (by
      rw [Fin.val_last, hc _ le_rfl]
      by_cases c : j.1 < r
      · rw [coarse_of_lt c]; omega
      · have := blkIdx_replicate_lt t m (j.1 - r) (by omega)
        rw [coarse_of_le (by omega)]; omega)
    have h5 : g ∈ blockUT _ κ r (List.replicate m t) := mem_btG.2 fun i j hij => by
      rw [hge]; exact mem_btG.1 h3 i.castSucc j.castSucc hij
    exact ⟨g, mem_HPar.2 ⟨h5, by rwa [firstBlock_diagEmb_eq h hr _ g h5] at h4⟩, rfl⟩
  · rintro a ha ha'
    obtain ⟨g, hg, rfl⟩ := id ha
    rw [levDiag_lam h _ rfl ha hg]
    have h1 := HPar_le hr _ H₀ hg
    have h2 := diagEmb_mem_blockUT' h _ h1
    show lam₀ (HPar0 hr _ H₀ ⟨g, hg⟩) * detChar χ _ r _ ⟨g, h1⟩ =
      lam₀ (HPar0 hr' _ H₀ ⟨_, ha'.1⟩) * detChar χ _ r _ ⟨_, h2⟩
    congr 1
    · exact congrArg lam₀ (Subtype.ext (firstBlock_diagEmb_eq h hr _ g h1 h2).symm)
    · rw [detChar_apply, detChar_apply]
      refine Finset.prod_congr rfl fun c hc' => ?_
      rw [blkDet_diagEmb h _ (c + 1) (fun i hi => by
        have := Finset.mem_range.1 hc'
        rw [List.length_replicate] at this
        rw [hc i hi]; omega) g h1]

end Diag

section Cong

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {N n : ℕ}

variable (hN : N = n + 1) (P : HeightOneSpectrum (𝓞 E)) (c : ℕ) (l : Lev (𝓞 E ⧸ P.asIdeal) K n)

theorem sup_prinCong_le : (levRed P l).H.map (extI hN P) ⊔ prinCong N P (c + 1) ≤ (levRed P (levDiag (by omega : n ≤ N) l)).H := by
  refine sup_le ?_ fun k hk => ?_
  · rintro _ ⟨j, hj, rfl⟩
    rw [mem_levRed, redGL_extI, diagEmb_mem_levDiag]
    exact hj
  · rw [mem_levRed, redGL_of_prinCong c.succ_pos hk]
    exact one_mem _

def levCong : LevI E K N P where
  H := (levRed P l).H.map (extI hN P) ⊔ prinCong N P (c + 1)
  lam := (levRed P (levDiag (by omega : n ≤ N) l)).lam.comp (Subgroup.inclusion (sup_prinCong_le hN P c l))

variable {P}

theorem mem_levCong (k : GLint E N P) :
    k ∈ (levCong hN P c l).H ↔ ∃ j ∈ (levRed P l).H, (extI hN P j)⁻¹ * k ∈ prinCong N P (c + 1) := by
  show k ∈ (((levRed P l).H.map (extI hN P) ⊔ prinCong N P (c + 1) : Subgroup _) : Set _) ↔ _
  rw [Subgroup.mul_normal]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, b, hb, rfl⟩
    exact ⟨j, hj, by simpa using hb⟩
  · rintro ⟨j, hj, hb⟩
    exact ⟨_, ⟨j, hj, rfl⟩, _, hb, mul_inv_cancel_left _ _⟩

theorem inv_mul_mem_prinCong (a k : GLint E N P) : a⁻¹ * k ∈ prinCong N P c ↔
    ∀ x ∈ stdAt E N P, ((qOf P : E) ^ c)⁻¹ • (k.1 x - a.1 x) ∈ stdAt E N P := by
  refine forall₂_congr fun x _ => ?_
  have e : (a⁻¹ * k).1 x - x = (a⁻¹).1 (k.1 x - a.1 x) := by
    rw [map_sub]
    exact congrArg _ (LinearEquiv.symm_apply_apply a.1 x).symm
  rw [e, ← map_smul]
  exact (a⁻¹).2 _

theorem mem_levCong_iff (k : GLint E N P) :
    k ∈ (levCong hN P c l).H ↔ ∃ j ∈ (levRed P l).H,
      ∀ x ∈ stdAt E N P, ((qOf P : E) ^ (c + 1))⁻¹ • (k.1 x - sumE hN j.1 1 x) ∈ stdAt E N P := by
  simp only [mem_levCong, inv_mul_mem_prinCong, extI_val]

theorem prinCong_le_levCong : prinCong N P (c + 1) ≤ (levCong hN P c l).H := le_sup_right

theorem extI_mem_levCong (j : GLint E n P) : extI hN P j ∈ (levCong hN P c l).H ↔ j ∈ (levRed P l).H := by
  refine ⟨fun h => ?_, fun h => (mem_levCong hN c l _).2 ⟨j, h, by simpa using one_mem _⟩⟩
  have := sup_prinCong_le hN P c l h
  rwa [mem_levRed, redGL_extI, diagEmb_mem_levDiag] at this

theorem levCong_lam {k : GLint E N P} (hk : k ∈ (levCong hN P c l).H) {j : GLint E n P} (hj : j ∈ (levRed P l).H)
    (h : (extI hN P j)⁻¹ * k ∈ prinCong N P (c + 1)) : (levCong hN P c l).lam ⟨k, hk⟩ = (levRed P l).lam ⟨j, hj⟩ := by
  have e := redGL_of_prinCong c.succ_pos h
  rw [map_mul, map_inv, inv_mul_eq_one, redGL_extI] at e
  exact levDiag_lam _ l e.symm (sup_prinCong_le hN P c l hk) hj

theorem levCong_lam_extI {j : GLint E n P} (hk : extI hN P j ∈ (levCong hN P c l).H) (hj : j ∈ (levRed P l).H) :
    (levCong hN P c l).lam ⟨_, hk⟩ = (levRed P l).lam ⟨j, hj⟩ := levCong_lam hN c l hk hj (by simpa using one_mem _)

theorem levCong_lam_prinCong {k : GLint E N P} (h : k ∈ prinCong N P (c + 1)) :
    (levCong hN P c l).lam ⟨k, prinCong_le_levCong hN c l h⟩ = 1 :=
  (levCong_lam hN c l _ (one_mem _) (by simpa using h)).trans (map_one _)

theorem levCong_last {k : GLint E N P} (hk : k ∈ (levCong hN P c l).H) {x : Sp E N} (hx : x ∈ stdAt E N P) :
    IntAt P (((qOf P : E) ^ (c + 1))⁻¹ * (k.1 x (Br.iL hN) - x (Br.iL hN))) := by
  obtain ⟨j, -, h⟩ := (mem_levCong_iff hN c l k).1 hk
  have := mem_stdAt.1 (h x hx) (Br.iL hN)
  rwa [Pi.smul_apply, Pi.sub_apply, sumE_last, Units.val_one, one_mul] at this

instance levCong_finiteIndex : (levCong hN P c l).H.FiniteIndex := Subgroup.finiteIndex_of_le (prinCong_le_levCong hN c l)

theorem levCong_root : ∃ m : ℕ, 0 < m ∧ ∀ k, (levCong hN P c l).lam k ^ m = 1 := by
  obtain ⟨m, hm, h⟩ := levRed_root P (levDiag (by omega : n ≤ N) l)
  exact ⟨m, hm, fun k => h _⟩

end Cong

theorem pref_prefRep {G D : Type} [Group G] [MulAction G D] (pref : D → Prop) {p : D} (hp : pref p) :
    pref (prefRep pref (Quotient.mk (MulAction.orbitRel G D) p)) := by
  have h : ∃ p', Quotient.mk (MulAction.orbitRel G D) p' = Quotient.mk (MulAction.orbitRel G D) p ∧ pref p' := ⟨p, rfl, hp⟩
  rw [prefRep, dif_pos h]
  exact h.choose_spec.2

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (P : LevFam X.E X.K R.r Pr.vGs)

theorem N_succ_of_eq {j : ℕ} (h : j = R.m) : R.N j = (R.N R.m - 1) + 1 := h ▸ N_m_succ R

def levGTop : LevFam X.E X.K (R.N R.m) Pr.vGs := fun w => levDiag (Nat.sub_le _ 1) (rowTyG Ch P w)

variable (R) in

def levQTop (c : ℕ) : LevQFam X.E X.K (R.N R.m) (QE sel (mu : Chr X.F X.E X.K)) := fun Q =>
  levCong (N_m_succ R) Q.1 c (rowTyQ R (mu : Chr X.F X.E X.K) (QE sel (mu : Chr X.F X.E X.K)) Q)

open Classical in

def topLevAt (c : ℕ) : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K)) where
  levG j := if h : j = R.m then fun w => levDiag (by have := N_succ_of_eq h; omega) (rowTyG Ch P w) else fun _ => ⟨⊤, 1⟩
  levQ j := if h : j = R.m then
      fun Q => levCong (N_succ_of_eq h) Q.1 c (rowTyQ R (mu : Chr X.F X.E X.K) (QE sel (mu : Chr X.F X.E X.K)) Q)
    else LevQFam.top X.E X.K (R.N j) _
  pref u j p := ∀ h : j = R.m, ∃ d : XPt Pr R sel mu, p = tilFr (N_succ_of_eq h) (Pr.piT u) d

variable (R) in

def topDep (M : ℕ) : ℕ := max (4 * R.m) (2 * R.m + 2 * M - 1)

variable (R) in

theorem topDep_succ (M : ℕ) : topDep R M + 1 = max (4 * R.m + 1) (2 * R.m + 2 * M) := by
  have := R.two_le_m
  unfold topDep
  omega

variable (R) in

theorem topDep_succ_eq_default (M : ℕ) : topDep R M + 1 = (default : TopDepth R M).1 := topDep_succ R M

variable (R) in

theorem two_mul_le_topDep (M : ℕ) : 2 * M ≤ topDep R M := by
  have := R.two_le_m
  unfold topDep
  omega

def topLev : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K)) := topLevAt Ch sel mu P (topDep R cst.M)

theorem topLevAt_levG_m (c : ℕ) : (topLevAt Ch sel mu P c).levG R.m = levGTop Ch P := dif_pos rfl

theorem topLevAt_levQ_m (c : ℕ) : (topLevAt Ch sel mu P c).levQ R.m = levQTop R sel mu c := dif_pos rfl

theorem topLevAt_finiteIndex (c j : ℕ) (Q : QE sel (mu : Chr X.F X.E X.K)) : ((topLevAt Ch sel mu P c).levQ j Q).H.FiniteIndex := by
  by_cases h : j = R.m
  · subst h
    rw [topLevAt_levQ_m]
    exact levCong_finiteIndex _ _ _
  · rw [show (topLevAt Ch sel mu P c).levQ j = LevQFam.top X.E X.K (R.N j) _ from dif_neg h]
    exact ⟨fun e => one_ne_zero (Subgroup.index_top.symm.trans e)⟩

theorem topLevAt_root (c j : ℕ) (Q : QE sel (mu : Chr X.F X.E X.K)) :
    ∃ m : ℕ, 0 < m ∧ ∀ k, ((topLevAt Ch sel mu P c).levQ j Q).lam k ^ m = 1 := by
  by_cases h : j = R.m
  · subst h
    rw [topLevAt_levQ_m]
    exact levCong_root _ _ _
  · rw [show (topLevAt Ch sel mu P c).levQ j = LevQFam.top X.E X.K (R.N j) _ from dif_neg h]
    exact ⟨1, one_pos, fun _ => pow_one _⟩

theorem topLev_levG_m : (topLev Ch sel mu cst P).levG R.m = levGTop Ch P := dif_pos rfl

theorem topLev_levQ_m : (topLev Ch sel mu cst P).levQ R.m = levQTop R sel mu (topDep R cst.M) := dif_pos rfl

theorem topLev_pref_m (u : Pr.Word) (p : ChPt (R := R) sel mu u R.m) :
    (topLev Ch sel mu cst P).pref u R.m p ↔ ∃ d, p = tilF sel mu u d := ⟨fun h => h rfl, fun h _ => h⟩

theorem topLev_pref_ne (u : Pr.Word) {j : ℕ} (h : j ≠ R.m) (p : ChPt (R := R) sel mu u j) : (topLev Ch sel mu cst P).pref u j p :=
  fun h' => absurd h' h

theorem topLev_finiteIndex (j : ℕ) (Q : QE sel (mu : Chr X.F X.E X.K)) : ((topLev Ch sel mu cst P).levQ j Q).H.FiniteIndex :=
  topLevAt_finiteIndex Ch sel mu P _ j Q

theorem topLev_root (j : ℕ) (Q : QE sel (mu : Chr X.F X.E X.K)) :
    ∃ m : ℕ, 0 < m ∧ ∀ k, ((topLev Ch sel mu cst P).levQ j Q).lam k ^ m = 1 := topLevAt_root Ch sel mu P _ j Q

theorem mem_levGTop (w : Pr.vGs) (a : GL (Fin (R.N R.m)) (𝓞 X.E ⧸ w.1.asIdeal)) :
    a ∈ (levGTop Ch P w).H ↔ ∃ g ∈ (rowTyG Ch P w).H, diagEmb _ (Nat.sub_le _ 1) g = a := Iff.rfl

theorem mem_levGTop_grp (a : GLG X.E (R.N R.m) Pr.vGs) :
    a ∈ (levGTop Ch P).grp ↔ ∃ h ∈ (rowTyG Ch P).grp, extGH (N_m_succ R) h = a := by
  constructor
  · intro ha
    choose g hg e using fun w => (mem_levGTop Ch P w _).1 (ha w (Set.mem_univ w))
    exact ⟨g, fun w _ => hg w, funext fun w => (extGH_apply _ g w).trans (e w)⟩
  · rintro ⟨h, hh, rfl⟩ w -
    exact ⟨h w, hh w (Set.mem_univ w), (extGH_apply _ h w).symm⟩

theorem levGTop_eq (w : Pr.vGs) : levGTop Ch P w =
    ⟨HPar (R.N R.m) _ ((r_le_X' R).trans (Nat.sub_le _ 1)) (List.replicate R.m R.t) (P w).H ⊓ fixCol _ _ (R.r + R.m * R.t),
      (lamPar _ _ (P w).lam (chiAt Ch w)).comp (Subgroup.inclusion inf_le_left)⟩ :=
  levDiag_HPar _ (N_m_succ R) (rank_X'_eq R) _ _ _ _ _

theorem levGTop_PsymF (w : Pr.vGs) : levGTop Ch (rPsymF Ch) w =
    ⟨HXmsym _ (R.N R.m) R.k R.r R.t R.m R.rS ((r_le_X' R).trans (Nat.sub_le _ 1)),
      lamXmsym (Ch.psi0 w) (chiAt Ch w) (R.N R.m) R.k R.r R.t R.m R.rS _⟩ := levGTop_eq Ch _ w

variable {sel mu} in

theorem mem_levQTop (c : ℕ) (Q : QE sel (mu : Chr X.F X.E X.K)) (k : GLint X.E (R.N R.m) Q.1) :
    k ∈ (levQTop R sel mu c Q).H ↔ ∃ h ∈ (levQX R sel mu Q).H, ∀ x ∈ stdAt X.E (R.N R.m) Q.1,
      ((qOf Q.1 : X.E) ^ (c + 1))⁻¹ • (k.1 x - sumE (N_m_succ R) h.1 1 x) ∈ stdAt X.E (R.N R.m) Q.1 := mem_levCong_iff _ _ _ k

variable {sel mu} in

theorem levQTop_lam (c : ℕ) (Q : QE sel (mu : Chr X.F X.E X.K)) (k : (levQTop R sel mu c Q).H) (h : (levQX R sel mu Q).H)
    (e : ∀ x ∈ stdAt X.E (R.N R.m) Q.1,
      ((qOf Q.1 : X.E) ^ (c + 1))⁻¹ • (k.1.1 x - sumE (N_m_succ R) h.1.1 1 x) ∈ stdAt X.E (R.N R.m) Q.1) :
    (levQTop R sel mu c Q).lam k = (levQX R sel mu Q).lam h :=
  levCong_lam _ c _ k.2 h.2 ((inv_mul_mem_prinCong (c + 1) (extI (N_m_succ R) Q.1 h.1) k.1).2 e)

variable {sel mu} in

theorem extQ_mem_levQTop (c : ℕ) (a : GLQ X.E (R.N R.m - 1) (QE sel (mu : Chr X.F X.E X.K))) :
    extQ X.E (N_m_succ R) _ a ∈ (levQTop R sel mu c).grp ↔ a ∈ (levQX R sel mu).grp :=
  forall₂_congr fun Q _ => extI_mem_levCong (N_m_succ R) c _ (a Q)

variable (R) in

theorem levQTop_eq_topLevQ' {c c' : ℕ} (e : c + 1 = c') (hc : 0 < c') : levQTop R sel mu c = topLevQ R sel mu hc := by
  subst e
  rfl

theorem topLev_levG_m_eq : (topLev Ch sel mu cst P).levG R.m = topLevG Ch P := topLev_levG_m Ch sel mu cst P

theorem topLev_levQ_m_eq : (topLev Ch sel mu cst P).levQ R.m = topLevQ R sel mu (default : TopDepth R cst.M).pos :=
  (topLev_levQ_m Ch sel mu cst P).trans (levQTop_eq_topLevQ' R sel mu (topDep_succ_eq_default R cst.M) _)

section Ok

variable (hPr : Pr.Ok) (hQ : ∀ (u : Pr.Word) (Q : QE sel (mu : Chr X.F X.E X.K)), Pr.piT u ∉ Q.1.asIdeal)
include hPr hQ

theorem topLevAt_ok (c : ℕ) : (topLevAt Ch sel mu P c).Ok where
  idx := topLevAt_finiteIndex Ch sel mu P c
  root j Q g := by
    obtain ⟨m, h, h'⟩ := topLevAt_root Ch sel mu P c j Q
    exact ⟨m, h, h' g⟩
  levG_top a ha := by
    rw [topLevAt_levG_m] at ha
    obtain ⟨h, -, e⟩ := (mem_levGTop_grp Ch P a).1 ha
    exact ⟨h, e⟩
  levQ_last Q k hk x hx := by
    rw [topLevAt_levQ_m] at hk
    obtain ⟨g, -, e⟩ := sup_prinCong_le _ _ _ _ hk
    have h2 := congrFun (redV_redGL k hx) (Br.iL (N_m_succ R))
    rw [← e] at h2
    refine h2.trans ?_
    simp only [Matrix.mulVec, dotProduct, diagEmb_val]
    have hh : ¬ (Br.iL (N_m_succ R)).1 < R.N R.m - 1 := lt_irrefl (R.N R.m - 1)
    simp only [diagMat_of_not_left _ _ hh]
    simp [Matrix.one_apply, redV]
  levQ_ini Q k hk i := by
    rw [topLevAt_levQ_m] at hk
    obtain ⟨g, -, e⟩ := sup_prinCong_le _ _ _ _ hk
    have h2 := congrFun (redV_redGL k (single_mem_stdAt (Br.iL (N_m_succ R)))) (Br.iC (N_m_succ R) i)
    rw [← e, redV_single, Matrix.mulVec_single_one] at h2
    refine h2.trans ?_
    show diagMat _ _ _ _ _ = 0
    have hh : ¬ (Br.iL (N_m_succ R)).1 < R.N R.m - 1 := lt_irrefl (R.N R.m - 1)
    rw [diagMat_of_not_right _ _ hh, Matrix.one_apply_ne]
    exact fun h => absurd (congrArg Fin.val h) i.2.ne
  pref_off u j h p := fun h' => absurd h' h
  pref_top u p h := by
    obtain ⟨d, rfl⟩ : ∃ d, p = tilF sel mu u d := h rfl
    exact ⟨d.deco, tilF_deco sel mu hPr u (hQ u) d⟩

theorem topLev_ok : (topLev Ch sel mu cst P).Ok := topLevAt_ok Ch sel mu P hPr hQ _

end Ok

theorem extGH_mem_topLev (h : (rowTyG Ch P).grp) : extGH (N_m_succ R) h.1 ∈ ((topLev Ch sel mu cst P).levG R.m).grp := by
  rw [topLev_levG_m]
  exact (mem_levGTop_grp Ch P _).2 ⟨h.1, h.2, rfl⟩

theorem extQ_mem_topLev (c : (levQX R sel mu).grp) : extQ X.E (N_m_succ R) _ c.1 ∈ ((topLev Ch sel mu cst P).levQ R.m).grp := by
  rw [topLev_levQ_m]
  exact (extQ_mem_levQTop _ _).2 c.2

abbrev TopG : Type := FrmG ((topLev Ch sel mu cst P).levG R.m) ((topLev Ch sel mu cst P).levQ R.m)

def extTop : FrmG (rowTyG Ch P) (levQX R sel mu) →* TopG Ch sel mu cst P :=
  (extUH (N_m_succ R)).prodMap
    ((((extGH (N_m_succ R)).comp (Subgroup.subtype _)).codRestrict _ (extGH_mem_topLev Ch sel mu cst P)).prodMap
      (((extQ X.E (N_m_succ R) _).comp (Subgroup.subtype _)).codRestrict _ (extQ_mem_topLev Ch sel mu cst P)))

theorem incl_extTop (g : FrmG (rowTyG Ch P) (levQX R sel mu)) : FrmG.incl _ _ (extTop Ch sel mu cst P g) =
    (extUH (N_m_succ R) g.1, extGH (N_m_succ R) g.2.1.1, extQ X.E (N_m_succ R) _ g.2.2.1) := rfl

theorem extTop_injective : Function.Injective (extTop Ch sel mu cst P) := by
  intro a b h
  have e := congrArg (FrmG.incl _ _) h
  rw [incl_extTop, incl_extTop, Prod.mk.injEq, Prod.mk.injEq] at e
  refine Prod.ext (Subtype.ext (sumE_inj (N_m_succ R) (t := 1) ?_)) (Prod.ext (Subtype.ext (funext fun w => ?_))
    (Subtype.ext (extQ_injective _ e.2.2)))
  · rw [← extUH_val, ← extUH_val, e.1]
  · have := congrFun e.2.1 w
    rw [extGH_apply, extGH_apply] at this
    exact diagEmb_injective _ this

theorem chrG_extTop (g : FrmG (rowTyG Ch P) (levQX R sel mu)) :
    ((topLev Ch sel mu cst P).levG R.m).chr (extTop Ch sel mu cst P g).2.1 = (rowTyG Ch P).chr g.2.1 := by
  rw [LevFam.chr_apply, LevFam.chr_apply]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hg := g.2.1.2 w (Set.mem_univ w)
  have h := (diagEmb_mem_levDiag (Nat.sub_le _ 1) (rowTyG Ch P w) _).2 hg
  exact (lev_lam_congr (congrFun (topLev_levG_m Ch sel mu cst P) w) (extGH_apply (N_m_succ R) g.2.1.1 w) _ h).trans
    (levDiag_lam _ _ rfl h hg)

theorem chrQ_extTop (g : FrmG (rowTyG Ch P) (levQX R sel mu)) :
    ((topLev Ch sel mu cst P).levQ R.m).chr (extTop Ch sel mu cst P g).2.2 = (levQX R sel mu).chr g.2.2 := by
  have key : ∀ (Θ : LevQFam X.E X.K (R.N R.m) (QE sel (mu : Chr X.F X.E X.K))) (_ : Θ = levQTop R sel mu (topDep R cst.M))
      (h : extQ X.E (N_m_succ R) _ g.2.2.1 ∈ Θ.grp), Θ.chr ⟨_, h⟩ = (levQX R sel mu).chr g.2.2 := by
    rintro _ rfl h
    rw [levQ_chr_apply, levQ_chr_apply]
    exact Finset.prod_congr rfl fun Q _ => levCong_lam_extI _ _ _ (h Q (Set.mem_univ Q)) (g.2.2.2 Q (Set.mem_univ Q))
  exact key _ (topLev_levQ_m Ch sel mu cst P) _

theorem chr_extTop (g : FrmG (rowTyG Ch P) (levQX R sel mu)) :
    ((topLev Ch sel mu cst P).levG R.m).chr (extTop Ch sel mu cst P g).2.1 *
      ((topLev Ch sel mu cst P).levQ R.m).chr (extTop Ch sel mu cst P g).2.2 = (stepX Ch sel mu P).chr () g := by
  rw [chrG_extTop, chrQ_extTop]
  rfl

section Til

variable (hPr : Pr.Ok) (u : Pr.Word) (hQ : ∀ Q : QE sel (mu : Chr X.F X.E X.K), Pr.piT u ∉ Q.1.asIdeal)
include hPr hQ

theorem tilF_extTop (g : FrmG (rowTyG Ch P) (levQX R sel mu)) (p : XPt Pr R sel mu) :
    tilF sel mu u (g • p) = extTop Ch sel mu cst P g • tilF sel mu u p := tilF_smul sel mu hPr u hQ (FrmG.incl _ _ g) p

end Til

variable (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

theorem levGAt_of_le (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) {j : ℕ} (h : R.m ≤ j) (b : Idx sel mu L j) :
    levGAt sel mu L Tp j b = Tp.levG j := by
  obtain ⟨_ | b, hb⟩ := b
  · rfl
  · exact absurd (hb.1 rfl) (by omega)

theorem levQAt_of_le (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) {j : ℕ} (h : R.m ≤ j) (b : Idx sel mu L j) :
    levQAt sel mu L Tp j b = Tp.levQ j := by
  obtain ⟨_ | b, hb⟩ := b
  · rfl
  · exact absurd (hb.1 rfl) (by omega)

example (u : Pr.Word) : ∃ p, (topLev Ch sel mu cst P).pref u R.m p :=
  ⟨_, (topLev_pref_m Ch sel mu cst P u _).2 ⟨DecoF.base _ _ _ _ _, rfl⟩⟩

example (c : ℕ) (Q : QE sel (mu : Chr X.F X.E X.K)) (h : (levQX R sel mu Q).H)
    (hk : extI (N_m_succ R) Q.1 h.1 ∈ (levQTop R sel mu c Q).H) :
    (levQTop R sel mu c Q).lam ⟨_, hk⟩ *
      lamQP (mu : Chr X.F X.E X.K) Q.1 (R.N R.m - 1) R.r (R.m * R.t) ⟨redGL _ Q.1 h.1, h.2⟩ = 1 := by
  rw [show (levQTop R sel mu c Q).lam ⟨_, hk⟩ = (levQX R sel mu Q).lam h from levCong_lam_extI _ _ _ hk h.2]
  exact inv_mul_cancel _

example (w : Pr.vGs) : ((topLev Ch sel mu cst P).levG R.m w).H ≤ fixCol _ _ (R.r + R.m * R.t) := by
  rw [topLev_levG_m, levGTop_eq]
  exact inf_le_right

example (Q : QE sel (mu : Chr X.F X.E X.K)) (k : GLint X.E (R.N R.m) Q.1) (hk : k ∈ ((topLev Ch sel mu cst P).levQ R.m Q).H)
    (x : Sp X.E (R.N R.m)) (hx : x ∈ stdAt X.E (R.N R.m) Q.1) :
    IntAt Q.1 (((qOf Q.1 : X.E) ^ max (4 * R.m + 1) (2 * R.m + 2 * cst.M))⁻¹ * (k.1 x (Br.iL (N_m_succ R)) - x (Br.iL (N_m_succ R)))) := by
  rw [topLev_levQ_m] at hk
  rw [← topDep_succ]
  exact levCong_last _ _ _ hk hx

example (h : R.m = 2) : topDep R 1 + 1 = 9 ∧ topDep R 5 + 1 = 14 := by
  rw [topDep_succ, topDep_succ, h]
  exact ⟨rfl, rfl⟩

example (hPr : Pr.Ok) (cst : LocCst X (rowSG Pr sel (mu0 X.F X.E X.K S))) : (topLev Ch sel (mu0 X.F X.E X.K S) cst P).Ok :=
  topLev_ok Ch sel _ cst P hPr fun u Q => by
    obtain ⟨Q, hQ⟩ := Q
    rw [twistPrimes_trivialTuple_empty] at hQ
    simp at hQ

end Top

end GlobalTheory.Mem.Col2
