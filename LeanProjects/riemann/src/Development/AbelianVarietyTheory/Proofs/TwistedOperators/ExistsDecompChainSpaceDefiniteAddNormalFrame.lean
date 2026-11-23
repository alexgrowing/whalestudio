import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ChainMatrices
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
open scoped TensorProduct

namespace GlobalTheory.StdFrames

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices GlobalTheory.IdemSupport Formalism.IndefR.Datum Formalism.L2.NTheta GlobalTheory.NormSum.AdLattice Formalism.L2.Herm

theorem exists_decomp {K X Y : Type} [Field K] [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    [FiniteDimensional K X] [FiniteDimensional K Y] (ι : X →ₗ[K] Y) (hι : Function.Injective ι) {c : ℕ}
    (hd : Module.finrank K Y = Module.finrank K X + c) (a : Fin c → Y) (φ : Fin c → Y →ₗ[K] K)
    (h0 : ∀ n x, φ n (ι x) = 0) (h1 : ∀ n n', n ≠ n' → φ n (a n') = 0) (h2 : ∀ n, φ n (a n) ≠ 0) (y : Y) :
    ∃ (x : X) (t : Fin c → K), y = ι x + ∑ n, t n • a n := by
  let Ψ : (X × (Fin c → K)) →ₗ[K] Y := ι.coprod (Fintype.linearCombination K a)
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, t⟩ h
    have h' : ι x + ∑ n, t n • a n = 0 := h
    have ht : t = 0 := funext fun n => by
      have := congrArg (φ n) h'
      rw [map_add, h0, zero_add, map_sum, map_zero, Finset.sum_eq_single n
        (fun n' _ hn => by rw [map_smul, h1 n n' hn.symm, smul_zero]) (by simp), map_smul, smul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_right (h2 n)
    subst ht
    have : ι x = ι 0 := by simpa using h'
    rw [hι this]
    rfl
  obtain ⟨⟨x, t⟩, rfl⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hd])).1 hinj y
  exact ⟨x, t, rfl⟩

variable {D : D7}

theorem rank_Y {j : ℕ} (hj : j < D.R.m) : (D.sp.Y j).rank = (D.sp.X j).rank + nAux D j ∧ D.R.k ≤ (D.sp.X j).rank := by
  have h1 := D.sp.X_rank j hj.le
  have h2 := D.sp.Y_rank j hj.le
  have h4 : j * (D.R.t + 1) = j * D.R.t + j := by ring
  simp only [Ranks.N, Ranks.rankY, Ranks.r] at h1 h2
  unfold nAux
  generalize j * D.R.t = u at *
  omega

theorem exists_decomp_chainSpace_definite_add_normalFrame {j : ℕ} (hj : j < D.R.m) {E Ev : ℕ → (D.sp.Y j).V} {z : (D.sp.Y j).V} (hA : IsAuxiliaryHeckeCharacter D j E Ev z)
    (y : (D.sp.Y j).V) :
    ∃ (x : (D.sp.X j).V) (t : Fin (nAux D j) → D.host.E), y = D.sp.iXY j x + ∑ n, t n • normalFr D j E Ev z n := by
  obtain ⟨h1, h2, h3⟩ := hA
  unfold HSpace.hD at h1 h2 h3
  have sym : ∀ x y, (D.sp.Y j).hT x y = 0 → (D.sp.Y j).hT y x = 0 := fun x y h => by
    rw [← (D.sp.Y j).herm.eq x y, h, map_zero]
  have hT : (D.sp.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 D.sp.T_prime.ne_zero
  have hpar : (Even j → nAux D j = 2 * (nAux D j / 2) + 1) ∧ (¬ Even j → nAux D j = 2 * (nAux D j / 2)) := by
    obtain ⟨a, ha⟩ := D.R.m_even
    rw [Nat.even_iff]
    unfold nAux
    omega
  have h4 : ∀ i < nAux D j / 2, ∀ l < nAux D j / 2, (D.sp.Y j).hT (E i) (Ev l) = if i = l then 1 else 0 := by
    intro i hi l hl
    rw [← (D.sp.Y j).herm.eq, (h1 i hi l hl).2.2]
    split_ifs <;> simp
  let b : ℕ → (D.sp.Y j).V := fun n =>
    if n < nAux D j / 2 then Ev n else if Even j ∧ n = nAux D j / 2 then z else E (nAux D j - 1 - n)
  have hlt : ∀ n < nAux D j, ¬ n < nAux D j / 2 → ¬ (Even j ∧ n = nAux D j / 2) → nAux D j - 1 - n < nAux D j / 2 := by
    intro n hn a1 a2
    by_cases he : Even j
    · have := hpar.1 he
      have : n ≠ nAux D j / 2 := fun h => a2 ⟨he, h⟩
      omega
    · have := hpar.2 he
      omega
  refine exists_decomp (D.sp.iXY j) ?_ ?_ (fun n : Fin (nAux D j) => normalFr D j E Ev z n)
    (fun n => (D.sp.Y j).hT (b n)) (fun n x => ?_) (fun n n' hn => ?_) (fun n => ?_) y
  · rw [injective_iff_map_eq_zero]
    intro x hx
    refine (D.sp.X j).nondeg.1 x fun x' => ?_
    rw [← D.sp.iXY_isom j hj, hx, map_zero, LinearMap.zero_apply]
  · rw [(D.sp.Y j).rank_eq, (D.sp.X j).rank_eq, (rank_Y hj).1]
  · refine sym _ _ ?_
    simp only [b]
    split_ifs with a1 a2
    · exact (h2 _ a1 x).2
    · exact (h3 a2.1).2.1 x
    · exact (h2 _ (hlt _ n.2 a1 a2) x).1
  · have hne : (n : ℕ) ≠ n' := fun h => hn (Fin.ext h)
    have l1 := n.2
    have l2 := n'.2
    simp only [b, normalFr]
    by_cases a1 : (n : ℕ) < nAux D j / 2
    · rw [if_pos a1]
      by_cases c1 : (n' : ℕ) < nAux D j / 2
      · rw [if_pos c1, (h1 _ c1 _ a1).2.2, if_neg hne.symm]
      rw [if_neg c1]
      by_cases c2 : Even j ∧ (n' : ℕ) = nAux D j / 2
      · rw [if_pos c2]
        exact sym _ _ ((h3 c2.1).2.2 _ a1).2
      · rw [if_neg c2, map_smul, (h1 _ (hlt _ l2 c1 c2) _ a1).2.1, smul_zero]
    rw [if_neg a1]
    by_cases a2 : Even j ∧ (n : ℕ) = nAux D j / 2
    · rw [if_pos a2]
      by_cases c1 : (n' : ℕ) < nAux D j / 2
      · rw [if_pos c1]
        exact ((h3 a2.1).2.2 _ c1).1
      rw [if_neg c1]
      by_cases c2 : Even j ∧ (n' : ℕ) = nAux D j / 2
      · exact absurd (a2.2.trans c2.2.symm) hne
      · rw [if_neg c2, map_smul, ((h3 a2.1).2.2 _ (hlt _ l2 c1 c2)).2, smul_zero]
    · rw [if_neg a2]
      by_cases c1 : (n' : ℕ) < nAux D j / 2
      · rw [if_pos c1]
        exact (h1 _ c1 _ (hlt _ l1 a1 a2)).1
      rw [if_neg c1]
      by_cases c2 : Even j ∧ (n' : ℕ) = nAux D j / 2
      · rw [if_pos c2]
        exact sym _ _ ((h3 c2.1).2.2 _ (hlt _ l1 a1 a2)).1
      · rw [if_neg c2, map_smul, h4 _ (hlt _ l1 a1 a2) _ (hlt _ l2 c1 c2),
          if_neg (show ¬ nAux D j - 1 - (n : ℕ) = nAux D j - 1 - (n' : ℕ) by omega), smul_zero]
  · have l1 := n.2
    simp only [b, normalFr]
    by_cases a1 : (n : ℕ) < nAux D j / 2
    · rw [if_pos a1, if_pos a1, (h1 _ a1 _ a1).2.2, if_pos rfl]
      exact one_ne_zero
    rw [if_neg a1, if_neg a1]
    by_cases a2 : Even j ∧ (n : ℕ) = nAux D j / 2
    · rw [if_pos a2, if_pos a2, (h3 a2.1).1]
      exact neg_ne_zero.2 hT
    · rw [if_neg a2, if_neg a2, map_smul, h4 _ (hlt _ l1 a1 a2) _ (hlt _ l1 a1 a2), if_pos rfl, smul_eq_mul, mul_one]
      split_ifs
      · exact neg_ne_zero.2 hT
      · exact hT

theorem isUnit_of_cols {K A : Type} [Field K] [CommRing A] (φ : K →+* A) {n p c : ℕ} (M : Matrix (Fin n) (Fin n) A)
    (P : Matrix (Fin n) (Fin p) K) (γ : GL (Fin p) A) (a : Fin c → Fin n → K)
    (h1 : ∀ b, ∃ d, ∀ i, M i d = (P.map φ * γ.val) i b)
    (h2 : ∀ b, ∃ d, ∃ s : K, s ≠ 0 ∧ ∀ i, M i d = φ (s * a b i))
    (h3 : ∀ y : Fin n → K, ∃ (x : Fin p → K) (t : Fin c → K), y = P *ᵥ x + ∑ b, t b • a b) : IsUnit M := by
  rw [← Matrix.mulVec_surjective_iff_isUnit]
  let R := LinearMap.range M.mulVecLin
  have hc : ∀ d, (fun i => M i d) ∈ R := fun d => ⟨Pi.single d 1, by
    rw [Matrix.mulVecLin_apply, mulVec_single_one]; rfl⟩
  have r1 : ∀ v, P.map φ *ᵥ v ∈ R := fun v => by
    have : P.map φ *ᵥ v = ∑ b, ((γ⁻¹).val *ᵥ v) b • fun i => (P.map φ * γ.val) i b := by
      conv_lhs => rw [← one_mulVec v, ← γ.mul_inv, ← mulVec_mulVec, mulVec_mulVec _ (P.map φ)]
      funext i
      simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [this]
    refine sum_mem fun b _ => R.smul_mem _ ?_
    obtain ⟨d, hd⟩ := h1 b
    exact funext hd ▸ hc d
  have r2 : ∀ b, (fun i => φ (a b i)) ∈ R := fun b => by
    obtain ⟨d, s, hs, hd⟩ := h2 b
    have : (fun i => φ (a b i)) = φ s⁻¹ • fun i => M i d := by
      funext i
      rw [Pi.smul_apply, hd, smul_eq_mul, ← map_mul, inv_mul_cancel_left₀ hs]
    rw [this]
    exact R.smul_mem _ (hc d)
  have r3 : ∀ y : Fin n → K, (fun i => φ (y i)) ∈ R := fun y => by
    obtain ⟨x, t, rfl⟩ := h3 y
    have : (fun i => φ ((P *ᵥ x + ∑ b, t b • a b) i)) =
        P.map φ *ᵥ (fun i => φ (x i)) + ∑ b, φ (t b) • fun i => φ (a b i) := by
      funext i
      simp [mulVec, dotProduct, Finset.sum_apply]
    rw [this]
    exact add_mem (r1 _) (sum_mem fun b _ => R.smul_mem _ (r2 b))
  intro v
  have : v = ∑ i, v i • fun l => φ ((Pi.single i 1 : Fin n → K) l) := by
    funext l
    simp [Finset.sum_apply, Pi.single_apply, apply_ite φ]
  have hv : v ∈ R := this ▸ sum_mem fun i _ => R.smul_mem _ (r3 _)
  exact hv

theorem isUnit_chainMat {j : ℕ} (hj : j < D.R.m) (γ : GL (Fin (D.sp.X j).rank) (Ef D)) {E Ev : ℕ → (D.sp.Y j).V}
    {z : (D.sp.Y j).V} (hA : IsAuxiliaryHeckeCharacter D j E Ev z) {s : ℕ} (hs : s ≠ 0) : IsUnit (chainMat D j γ E Ev z s) := by
  obtain ⟨hr, hk⟩ := rank_Y hj
  refine isUnit_of_cols (eToEAf D) _ (frameMat (D.sp.Y j) (D.sp.X j) (D.sp.iXY j)) γ
    (fun (b : Fin (nAux D j)) => (D.sp.Y j).frame.repr (normalFr D j E Ev z b)) (fun b => ?_) (fun b => ?_) (fun y => ?_)
  · have hb := b.2
    by_cases h : (b : ℕ) < D.R.k
    · refine ⟨⟨b, by omega⟩, fun i => ?_⟩
      unfold chainMat colX
      rw [if_pos h, dif_pos hb]
      rfl
    · refine ⟨⟨b + nAux D j, by omega⟩, fun i => ?_⟩
      unfold chainMat colX
      dsimp only
      rw [if_neg (by omega), if_neg (by omega)]
      simp only [Nat.add_sub_cancel, dif_pos hb]
      rfl
  · have hb := b.2
    refine ⟨⟨D.R.k + b, by omega⟩, (s : D.host.E) ^ ((b : ℕ) + 1), pow_ne_zero _ (Nat.cast_ne_zero.2 hs), fun i => ?_⟩
    unfold chainMat
    dsimp only
    rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
  · obtain ⟨x, t, h⟩ := exists_decomp_chainSpace_definite_add_normalFrame hj hA ((D.sp.Y j).frame.equivFun.symm y)
    refine ⟨(D.sp.X j).frame.repr x, t, ?_⟩
    unfold frameMat
    rw [LinearMap.toMatrix_mulVec_repr, ← (D.sp.Y j).frame.equivFun.apply_symm_apply y, h, map_add, map_sum]
    simp only [map_smul]
    rfl

theorem not_mem_of_coprime {p q : ℕ} (h : p.Coprime q) {Q : Pl D.host.E} (hp : (p : 𝓞 D.host.E) ∈ Q.asIdeal) :
    (q : 𝓞 D.host.E) ∉ Q.asIdeal := fun hq => by
  have h1 : IsCoprime (p : 𝓞 D.host.E) (q : 𝓞 D.host.E) := Nat.Coprime.cast h
  obtain ⟨a, b, e⟩ := h1
  exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (e ▸ add_mem (Q.asIdeal.mul_mem_left _ hp) (Q.asIdeal.mul_mem_left _ hq)))

theorem eq_of_g_mem {l l' : Fin 2} {Q : Pl D.host.E} (h : (D.host.g l : 𝓞 D.host.E) ∈ Q.asIdeal)
    (h' : (D.host.g l' : 𝓞 D.host.E) ∈ Q.asIdeal) : l = l' := by
  by_contra hne
  refine not_mem_of_coprime ((Nat.coprime_primes (D.host.g_prime l) (D.host.g_prime l')).2 ?_) h h'
  have := D.host.g_ne
  fin_cases l <;> fin_cases l' <;> simp_all [eq_comm]

theorem emb_star (t : D.host.E) : D.host.φ₀ (star t) = starRingEnd ℂ (D.host.φ₀ t) :=
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ t

theorem conj_eq_star (t : D.host.E) : D.host.conj t = star t := by
  apply D.host.φ₀.injective
  rw [emb_star, ← D.embE_φ₀, RingHom.comp_apply, RingHom.comp_apply, D.embE_conj, D.starLL_cx]

theorem not_div_cP (P : Formalism.L2.Host.PiBar D.host) {l l' : Fin 2} {Q : Pl D.host.E} (h : P.Div l Q) :
    ¬ P.Div l' (cP Q) := fun h' => by
  obtain rfl : l = l' := eq_of_g_mem (P.overP h) ((natCast_mem_cP Q _).1 (P.overP h'))
  refine (((GlobalTheory.Mem.Chr.splitsC_main D.R D.host _ (D.host.g_prime l) (D.nd.g_split l) Q (P.overP h)).2.2.2 (P.pb l)
    (P.pb_over l) (cP Q) ?_).2.1 h) h'
  refine (GlobalTheory.Mem.Chr.conjPl_iff_mem _ _ _).2 fun x y hxy => ?_
  have h1 : y = cO D x := RingOfIntegers.ext (hxy.trans (conj_eq_star _))
  rw [mem_cP, h1, cO_cO]

theorem exists_idem_div (P : Formalism.L2.Host.PiBar D.host) {l : Fin 2} {Q : Pl D.host.E} (h : P.Div l Q) :
    ∃ e : AE D, IsIdemAt e Q :=
  exists_isIdemAt fun e => not_div_cP P h (l' := l) (e.symm ▸ h)

theorem g_not_mem {Q : Finset (Pl D.host.E)} (h : Formalism.IndefR.Lev.IsTwistPlaces D.host.g Q) {P : Pl D.host.E}
    (hP : P ∈ Q) : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  obtain ⟨⟨q, hq, hc, -, hne⟩, -⟩ := h P hP
  have h1 : (q : 𝓞 D.host.E) ∈ P.asIdeal := by
    have := Ideal.absNorm_mem P.asIdeal
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply, show Nat.card (𝓞 D.host.E ⧸ P.asIdeal) = q from hc] at this
  exact not_mem_of_coprime (Nat.Coprime.mul_right ((Nat.coprime_primes hq (D.host.g_prime 0)).2 (hne 0))
    ((Nat.coprime_primes hq (D.host.g_prime 1)).2 (hne 1))) h1

theorem agreeAt_of_loc {P : Pl D.host.E} {e : AE D} (he : IsIdemAt e P) {n : ℕ} {β M : GL (Fin n) (Ef D)}
    (h : loc P β = loc P M) : AgreeAt P β.val M.val :=
  agreeAt_of he fun i j => congrArg (fun g => g.val i j) h

theorem exists_frame_Y {T : Type} (L : LevCh D T) (hQ : ∀ t, Formalism.IndefR.Lev.IsTwistPlaces D.host.g (L.Q t)) {j : ℕ}
    (hj : j < D.R.m) (γ : GL (Fin (D.sp.X j).rank) (Ef D)) (E Ev : ℕ → (D.sp.Y j).V) (z : (D.sp.Y j).V) :
    ∃ β Λ, IsSDFrame (D.sp.Y j) β Λ (D.host.g 0 * D.host.g 1) ∧ (IsAuxiliaryHeckeCharacter D j E Ev z → ShapeY L j γ E Ev z β) := by
  obtain ⟨β₀, h₀⟩ := exists_base (D.sp.Y j)
  by_cases hA : IsAuxiliaryHeckeCharacter D j E Ev z
  swap
  · exact ⟨β₀, _, GlobalTheory.LevelChoices.isSDFrame_of_one (isSD_one h₀) _, fun h => absurd h hA⟩
  obtain ⟨M₀, e₀⟩ := isUnit_chainMat hj γ hA (D.host.g_prime 0).ne_zero
  obtain ⟨M₁, e₁⟩ := isUnit_chainMat hj γ hA (D.host.g_prime 1).ne_zero
  obtain ⟨M, e⟩ := isUnit_chainMat hj γ hA one_ne_zero
  obtain ⟨f, hf, -, f1, f0⟩ := exists_idem {Q | L.C.P.Div 0 Q}
  obtain ⟨β, Λ, h1, h2, h3⟩ := exists_frame (D.sp.Y j) (N := D.host.g 0 * D.host.g 1)
    (mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) β₀ h₀ {Q | ∃ l, L.C.P.Div l Q}
    {Q | (∃ t, Q ∈ L.Q t) ∧ SpansAt Q (D.sp.Y j) M.val} (by
      rintro Q ⟨l, hl⟩
      refine ⟨?_, fun ⟨l', hl'⟩ => not_div_cP _ hl hl'⟩
      have := L.C.P.overP hl
      rw [Nat.cast_mul]
      fin_cases l
      · exact Q.asIdeal.mul_mem_right _ this
      · exact Q.asIdeal.mul_mem_left _ this) (mixGL hf M₀ M₁) M
    fun Q ⟨⟨t, ht⟩, hs⟩ => ⟨g_not_mem (hQ t) ht, leAt_of_spansAt h₀ hs⟩
  refine ⟨β, Λ, h1, fun _ => ⟨fun l P hP => ?_, fun t P hP hs => ?_⟩⟩
  · obtain ⟨δ, hδ⟩ := exists_idem_div _ hP
    have h4 := h2 P ⟨l, hP⟩
    obtain rfl | rfl : l = 0 ∨ l = 1 := by fin_cases l <;> simp
    · rw [← e₀]
      exact agreeAt_of_loc hδ (h4.trans (map_mixGL_one _ _ _ _ (f1 P hP)))
    · rw [← e₁]
      exact agreeAt_of_loc hδ (h4.trans (map_mixGL_zero _ _ _ _ (f0 P fun h =>
        absurd (eq_of_g_mem (L.C.P.overP h) (L.C.P.overP hP)) (by decide))))
  · rw [← e] at hs ⊢
    obtain ⟨δ, hδ, -⟩ := id hs
    exact agreeAt_of_loc hδ (h3 P ⟨⟨t, hP⟩, hs⟩)

theorem exists_frame_top {j : ℕ} (hj : j = D.R.m) (βX : GL (Fin D.sp.X'.rank) (Ef D)) :
    ∃ β Λ, TopTie j β Λ βX := by
  subst hj
  have hr : (D.sp.Y D.R.m).rank = D.sp.X'.rank := by
    rw [D.sp.Y_rank _ le_rfl, D.sp.X'_rank]
    rfl
  obtain ⟨β, hβ⟩ := exists_push hr (ratM (frameMat (D.sp.Y D.R.m) D.sp.X' D.sp.eYm.toLinearMap))
    (ratM (frameMat D.sp.X' (D.sp.Y D.R.m) D.sp.eYm.symm.toLinearMap)) (by
      unfold ratM frameMat
      rw [← Matrix.map_mul, ← LinearMap.toMatrix_comp, LinearEquiv.comp_symm, LinearMap.toMatrix_id,
        Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]) βX
  exact ⟨β, _, isFrame_lat β, _, HEq.rfl, hβ⟩

theorem crdLat_std {V : HSp D} (h : IsStdSpace V) : crdLat V V.L0 = lat (1 : GL (Fin V.rank) (Ef D)) := by
  ext x
  rw [mem_lat_one, ← h.2, ← GlobalTheory.LevelChoices.coe_crdLat]
  rfl

theorem exists_frame_std (V : HSp D) : ∃ β, IsSDFrame V β (crdLat V V.L0) 1 ∧ (IsStdSpace V → β = 1) := by
  by_cases h : IsStdSpace V
  · exact ⟨1, isSD_one (crdLat_std h), fun _ => rfl⟩
  · obtain ⟨β, hβ⟩ := exists_base V
    exact ⟨β, isSD_one hβ, fun h' => absurd h' h⟩

theorem sum_star_mul_ne {n : ℕ} (x : Fin n → D.host.E) : ∑ i, star (x i) * x i ≠ -1 := fun h => by
  have h1 := congrArg (fun t => (D.host.φ₀ t).re) h
  simp only [map_sum, map_mul, emb_star, ← Complex.normSq_eq_conj_mul_self, Complex.re_sum, Complex.ofReal_re, map_neg,
    map_one, Complex.neg_re, Complex.one_re] at h1
  have : 0 ≤ ∑ i, Complex.normSq (D.host.φ₀ (x i)) := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  linarith

theorem exists_frame_ortho (V : HSp D) (b : Bool)
    (h : Formalism.HermitianLatticesTheory.IsOrthoLattice (if b then -V.hT else V.hT) V.L0 V.rank) :
    ∃ β, IsSDFrame V β (crdLat V V.L0) 1 ∧ (∃ B : Matrix (Fin V.rank) (Fin V.rank) D.host.E, β.val = ratM B ∧
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B * V.gram * B = if b then -1 else 1) ∧
      (IsStdSpace V → β = 1) := by
  obtain ⟨e, hli, hsp, hL, hon⟩ := h
  by_cases hs : IsStdSpace V
  · refine ⟨1, isSD_one (crdLat_std hs), ⟨1, (Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)).symm, ?_⟩,
      fun _ => rfl⟩
    rw [cT_one', hs.1, one_mul, one_mul]
    cases b
    · rfl
    · ext i j
      exfalso
      have h1 : -V.hT (e i) (e i) = 1 := by simpa using hon i i
      rw [hT_crd D.sp.cm, hs.1, hform_one, neg_eq_iff_eq_neg] at h1
      exact sum_star_mul_ne _ h1
  · let b' := (Module.Basis.mk hli hsp.ge).map (crd V)
    have hb : ∀ a, b' a = crd V (e a) := fun a => by simp [b']
    obtain ⟨β, h1, h2⟩ := span_eq_lat (F := D.host.F) b'
    refine ⟨β, isSD_one ?_, ⟨_, h1, ?_⟩, fun h => absurd h hs⟩
    · rw [← h2]
      conv_lhs => rw [hL]
      unfold crdLat
      rw [Submodule.map_span, ← Set.range_comp]
      congr 2
      exact funext fun a => (hb a).symm
    · refine Matrix.ext fun a a' => ?_
      have h3 : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (Matrix.of fun i a => b' a i) * V.gram *
          (Matrix.of fun i a => b' a i)) a a' = V.hT (e a) (e a') := by
        rw [hT_crd D.sp.cm, ← hb, ← hb, Formalism.UG.hform, Finset.sum_comm]
        simp only [Matrix.mul_apply, Finset.sum_mul]
        rfl
      rw [h3]
      have h4 := hon a a'
      cases b
      · simpa [Matrix.one_apply] using h4
      · rw [if_pos rfl, Matrix.neg_apply, Matrix.one_apply, ← h4]
        simp

theorem exists_inertPlace_seesawW_scalar_frame (Pg : Finset (Pl D.host.E)) (hP : ∀ P ∈ Pg, ∃ e : AE D, IsIdemAt e P) {i : ℕ} (h1 : 1 ≤ i)
    (h2 : i ≤ D.R.m) {j : ℕ} (hj : j = 0) {β : GL (Fin (D.sp.Y j).rank) (Ef D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin (D.sp.Y j).rank → D.host.E)} {N : ℕ} (hβ : IsSDFrame (D.sp.Y j) β Λ N) :
    ∃ βW, IsSDFrame (D.sp.W i) βW (crdLat _ (D.sp.W i).L0) 1 ∧ Transport Pg (D.sp.W i) (D.sp.Y j) βW β := by
  subst hj
  obtain ⟨e, g, hg⟩ := D.sp.baseSpace_isometric_graded i h1 h2
  have hr : (D.sp.Y 0).rank = (D.sp.W i).rank := by simpa using Fintype.card_congr e
  let x : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.W i).rank) (Ef D) := g.val.submatrix e id
  have hx : mulM x ((g⁻¹).val.submatrix id e) = 1 := by
    unfold mulM
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Units.mul_inv, Matrix.submatrix_one_equiv]
  have hJ : HMul.hMul (HMul.hMul (Formalism.UG.cT (sg D) x) (ratM (D.sp.Y 0).gram)) x = ratM (D.sp.W i).gram := by
    refine Eq.trans ?_ hg
    ext a b
    simp only [Matrix.mul_apply]
    refine Fintype.sum_equiv e _ _ fun c => ?_
    congr 1
    refine Fintype.sum_equiv e _ _ fun d => ?_
    simp only [Matrix.map_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rfl
  obtain ⟨γ, hγ, hxγ⟩ := exists_pull (OA D) (sg D) hr _ _ x _ hx hJ β (unimod_of_isSD hβ)
  obtain ⟨k, hk, hL⟩ := exists_unitary (D.sp.W i) γ hγ
  have hid : ∀ a b : ℕ, IsIntM (idM (Ef D) a b) := fun a b c d => by
    unfold idM
    rw [Matrix.of_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  refine ⟨k⁻¹ * γ, isSD_one hL, mulM x k.val, idM _ _ _, idM _ _ _, ?_, ?_, hid _ _, hid _ _, idM_mul hr, idM_mul hr.symm,
    fun P h => ?_⟩
  · refine Eq.trans ?_ hk
    unfold mulM adjM gramOf
    rw [cT_mul', ← hJ]
    simp only [Matrix.mul_assoc]
  · unfold mulM
    rw [← hxγ, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel_left]
  · obtain ⟨δ, hδ⟩ := hP P h
    exact ⟨δ, hδ, fun _ _ => rfl⟩

theorem framesStdExist : FramesStdExist := by
  intro D T L hP hQ γ E Ev z _
  obtain ⟨βX, hX, hX'⟩ := exists_frame_std D.sp.X'
  have hY : ∀ j, ∃ β Λ, (j < D.R.m → IsSDFrame (Yc D j) β Λ (D.host.g 0 * D.host.g 1) ∧
      (IsAuxiliaryHeckeCharacter D (min j D.R.m) (E _) (Ev _) (z _) → ShapeY L (min j D.R.m) (γ _) (E _) (Ev _) (z _) β)) ∧
      (D.R.m ≤ j → TopTie (min j D.R.m) β Λ βX) := by
    intro j
    by_cases hj : j < D.R.m
    · obtain ⟨β, Λ, h⟩ := exists_frame_Y L hQ (min_lt_of_left_lt hj : min j D.R.m < D.R.m) (γ _) (E _) (Ev _) (z _)
      exact ⟨β, Λ, fun _ => h, fun h => absurd hj (not_lt.2 h)⟩
    · obtain ⟨β, Λ, h⟩ := exists_frame_top (min_eq_right (not_lt.1 hj)) βX
      exact ⟨β, Λ, fun h => absurd h hj, fun _ => h⟩
  choose βY ΛY hY hY' using hY
  have hm : 0 < D.R.m := lt_of_lt_of_le two_pos D.R.two_le_m
  choose βV hV hV' hV'' using fun i : Fin D.R.m => exists_frame_ortho (Vc D i) (D.sp.Vneg ((i : ℕ) + 1)) (by
    rw [D.sp.V_rank _ (Nat.le_add_left _ _) i.2]
    exact D.sp.V_std _ (Nat.le_add_left _ _) i.2)
  choose βW hW hW' using fun i : Fin D.R.m => exists_inertPlace_seesawW_scalar_frame L.Pg
    (fun P h => ((hP P).1 h).elim fun _ hl => exists_idem_div _ hl) (Nat.le_add_left 1 i) i.2
    (Nat.zero_min D.R.m) (hY 0 hm).1
  exact ⟨{ L with
      ΛY := ΛY, ΛX := _, ΛV := fun i => crdLat _ (Vc D i).L0, ΛW := fun i => crdLat _ (Wc D i).L0,
      βY := βY, βX := βX, βV := βV, βW := βW },
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨fun j hj => (hY j hj).1, hX, hV, hW⟩,
    fun j hj => (hY j hj).2, hY', hX', fun i => ⟨hV' i, hV'' i⟩, hW'⟩

end GlobalTheory.StdFrames

end
