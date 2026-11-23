import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.PtMatIsUnit
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Unfold.Inter

section Gen
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

lemma hsymm (x y : S.V) : S.hT x y = star (S.hT y x) := by
  have := S.herm.eq y x
  exact this.symm

lemma zhat_swap (F : FlagG S r T) (F' : FlagG S r T') : Zhat F' F = (Zhat F F').conjTranspose := by
  ext a b
  simp only [Zhat, brS, Matrix.conjTranspose_apply]
  exact hsymm _ _

lemma dl_swap (F : FlagG S r T) (F' : FlagG S r T') (l : ℕ) : Dl F' F l = star (Dl F F' l) := by
  unfold Dl leadMinorE
  split_ifs with h
  · rw [zhat_swap F F', ← Matrix.det_conjTranspose, Matrix.conjTranspose_submatrix]
  · simp

lemma dl_top (F : FlagG S r T) (F' : FlagG S r T') : Dl F F' (r + 1) = (Zhat F F').det := by
  unfold Dl leadMinorE
  rw [dif_pos le_rfl]
  congr 1

lemma dl_adj (F : FlagG S r T) (F' : FlagG S r T') :
    (Zhat F F').adjugate (Fin.last r) (Fin.last r) = Dl F F' r := by
  unfold Dl leadMinorE
  rw [dif_pos (Nat.le_succ r), Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  rw [Even.neg_one_pow ⟨_, rfl⟩, one_mul]
  congr 1

def comb (F : FlagG S r T) : (Fin (r + 1) → E) →ₗ[E] S.V := Fintype.linearCombination E F.fvec

def pair (F : FlagG S r T) : S.V →ₗ[E] (Fin (r + 1) → E) := LinearMap.pi fun a => S.hT (F.fvec a)

lemma pair_apply (F : FlagG S r T) (x : S.V) (a) : pair F x a = S.hT (F.fvec a) x := rfl

lemma pair_comb (F : FlagG S r T) (F' : FlagG S r T') (c : Fin (r + 1) → E) :
    pair F (comb F' c) = (Zhat F F').mulVec c := by
  ext a
  simp [pair_apply, comb, Fintype.linearCombination_apply, map_sum, Matrix.mulVec, dotProduct, Zhat, brS,
    mul_comm]

lemma fvec_cast (F : FlagG S r T) (a : Fin r) : F.fvec a.castSucc = F.e a := by simp [FlagG.fvec]
lemma fvec_last (F : FlagG S r T) : F.fvec (Fin.last r) = F.z := by simp [FlagG.fvec]

lemma pair_comb_self (F : FlagG S r T) (c : Fin (r + 1) → E) :
    pair F (comb F c) = Pi.single (Fin.last r) (-(c (Fin.last r) * T)) := by
  have hz : ∀ a, S.hT F.z (F.e a) = 0 := fun a => by rw [hsymm, F.z_orth]; simp
  ext a
  refine Fin.lastCases ?_ (fun a => ?_) a
  · simp [pair_apply, comb, Fintype.linearCombination_apply, Fin.sum_univ_castSucc, fvec_cast, fvec_last,
      map_sum, hz, F.z_norm]
  · simp [pair_apply, comb, Fintype.linearCombination_apply, Fin.sum_univ_castSucc, fvec_cast, fvec_last,
      map_sum, F.e_iso, F.z_orth, Fin.castSucc_ne_last]

lemma cramer_last (F : FlagG S r T) (F' : FlagG S r T') (c c' : Fin (r + 1) → E)
    (h : pair F (comb F c + comb F' c') = 0) :
    (Zhat F F').det • c' = fun b => (Zhat F F').adjugate b (Fin.last r) * (c (Fin.last r) * T) := by
  rw [map_add, pair_comb_self, pair_comb] at h
  have h2 : (Zhat F F').mulVec c' = Pi.single (Fin.last r) (c (Fin.last r) * T) := by
    rw [eq_neg_of_add_eq_zero_right h, ← Pi.single_neg, neg_neg]
  have h3 := congrArg ((Zhat F F').adjugate.mulVec) h2
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at h3
  rw [h3]
  ext b
  simp [Matrix.mulVec_single]

lemma gram_inj (F : FlagG S r T) (F' : FlagG S r T') (hD : (Zhat F F').det ≠ 0) (hG : Gflag F F' ≠ 0)
    (c c' : Fin (r + 1) → E) (h : pair F (comb F c + comb F' c') = 0)
    (h' : pair F' (comb F c + comb F' c') = 0) : c = 0 ∧ c' = 0 := by
  have e1 := cramer_last F F' c c' h
  have e2 := cramer_last F' F c' c (by rw [add_comm (comb F' c')]; exact h')
  have hD' : (Zhat F' F).det ≠ 0 := by
    rw [zhat_swap F F', Matrix.det_conjTranspose]; exact star_ne_zero.mpr hD
  have f1 := congrFun e1 (Fin.last r)
  have f2 := congrFun e2 (Fin.last r)
  simp only [Pi.smul_apply, smul_eq_mul, dl_adj] at f1 f2
  rw [← dl_top] at f1 f2
  rw [dl_swap F F', dl_swap F F'] at f2
  have hc : c (Fin.last r) = 0 := by
    have : c (Fin.last r) * Gflag F F' = 0 := by
      unfold Gflag
      linear_combination (Dl F F' (r + 1)) * f2 + star (Dl F F' r) * T' * f1
    exact (mul_eq_zero.mp this).resolve_right hG
  have hc' : c' = 0 := by
    rw [hc] at e1
    simp only [zero_mul, mul_zero] at e1
    exact (smul_eq_zero.mp e1).resolve_left hD
  refine ⟨?_, hc'⟩
  rw [hc'] at e2
  simp only [Pi.zero_apply, zero_mul, mul_zero] at e2
  exact (smul_eq_zero.mp e2).resolve_left hD'

def Msp (F : FlagG S r T) (F' : FlagG S r T') : Submodule E S.V :=
  LinearMap.range ((comb F).coprod (comb F'))

def Wsp (F : FlagG S r T) (F' : FlagG S r T') : Submodule E S.V :=
  LinearMap.ker ((pair F).prod (pair F'))

lemma isCompl_MW (F : FlagG S r T) (F' : FlagG S r T') (hD : (Zhat F F').det ≠ 0) (hG : Gflag F F' ≠ 0) :
    IsCompl (Msp F F') (Wsp F F') := by
  set Φ := ((pair F).prod (pair F')) ∘ₗ ((comb F).coprod (comb F')) with hΦ
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨c, c'⟩ hc
    have := gram_inj F F' hD hG c c' (congrArg Prod.fst hc) (congrArg Prod.snd hc)
    rw [this.1, this.2]; rfl
  have hsurj : Function.Surjective Φ := LinearMap.injective_iff_surjective.mp hinj
  constructor
  · rw [Submodule.disjoint_def]
    rintro _ ⟨c, rfl⟩ hx
    have : c = 0 := hinj (by rw [map_zero]; exact hx)
    rw [this, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    obtain ⟨c, hc⟩ := hsurj (((pair F).prod (pair F')) v)
    refine Submodule.mem_sup.mpr ⟨_, ⟨c, rfl⟩, v - ((comb F).coprod (comb F')) c, ?_, by abel⟩
    rw [Wsp, LinearMap.mem_ker, map_sub, ← hc]
    exact sub_self _

def Stab (s : S.V ≃ₗ[E] S.V) (F : FlagG S r T) : Prop :=
  ∀ a : Fin (r + 1), s (F.fvec a) - F.fvec a ∈ F.Xa a.val

lemma Xa_le_X (F : FlagG S r T) (j : ℕ) : F.Xa j ≤ F.X :=
  Submodule.span_mono (Set.image_subset_range _ _)

lemma Xa_mono (F : FlagG S r T) {i j : ℕ} (h : i ≤ j) : F.Xa i ≤ F.Xa j :=
  Submodule.span_mono (Set.image_mono fun _ ha => lt_of_lt_of_le ha h)

lemma fvec_mem (F : FlagG S r T) (a) : F.fvec a ∈ LinearMap.range (comb F) :=
  ⟨Pi.single a 1, by simp [comb]⟩

lemma X_le_range (F : FlagG S r T) : F.X ≤ LinearMap.range (comb F) := by
  rw [FlagG.X, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  rw [← fvec_cast]; exact fvec_mem F _

lemma range_le_M (F : FlagG S r T) (F' : FlagG S r T') : LinearMap.range (comb F) ≤ Msp F F' := by
  rintro _ ⟨c, rfl⟩; exact ⟨(c, 0), by simp⟩

lemma range_le_M' (F : FlagG S r T) (F' : FlagG S r T') : LinearMap.range (comb F') ≤ Msp F F' := by
  rintro _ ⟨c, rfl⟩; exact ⟨(0, c), by simp⟩

lemma Stab.sub_Xa {s : S.V ≃ₗ[E] S.V} {F : FlagG S r T} (hs : Stab s F) (j : ℕ) (x : S.V)
    (hx : x ∈ F.Xa (j + 1)) : s x - x ∈ F.Xa j := by
  have : F.Xa (j + 1) ≤ (F.Xa j).comap ((s : S.V →ₗ[E] S.V) - LinearMap.id) := by
    rw [FlagG.Xa, Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    have h1 := hs a.castSucc
    rw [fvec_cast] at h1
    exact Xa_mono F (Nat.lt_succ_iff.mp ha) h1
  exact this hx

lemma Stab.sub_comb {s : S.V ≃ₗ[E] S.V} {F : FlagG S r T} (hs : Stab s F) (x : S.V)
    (hx : x ∈ LinearMap.range (comb F)) : s x - x ∈ F.X := by
  obtain ⟨c, rfl⟩ := hx
  simp only [comb, Fintype.linearCombination_apply, map_sum, map_smul, ← Finset.sum_sub_distrib, ← smul_sub]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Xa_le_X F _ (hs a))

lemma surj_of_stable (s : S.V ≃ₗ[E] S.V) (U : Submodule E S.V) (hU : ∀ u ∈ U, s u ∈ U) :
    ∀ u ∈ U, ∃ u0 ∈ U, s u0 = u := by
  have hle : U.map (s : S.V →ₗ[E] S.V) ≤ U := by
    rintro _ ⟨u, hu, rfl⟩; exact hU u hu
  have := Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq s U)
  intro u hu
  rw [← this] at hu
  exact hu

lemma Stab.map_X {s : S.V ≃ₗ[E] S.V} {F : FlagG S r T} (hs : Stab s F) : ∀ x ∈ F.X, s x ∈ F.X := by
  intro x hx
  have := F.X.add_mem (hs.sub_comb x (X_le_range F hx)) hx
  rwa [sub_add_cancel] at this

lemma map_M {s : S.V ≃ₗ[E] S.V} {F : FlagG S r T} {F' : FlagG S r T'} (hs : Stab s F) (hs' : Stab s F') :
    ∀ m ∈ Msp F F', s m ∈ Msp F F' := by
  rintro _ ⟨⟨c, c'⟩, rfl⟩
  have h1 := hs.sub_comb _ ⟨c, rfl⟩
  have h2 := hs'.sub_comb _ ⟨c', rfl⟩
  have e : s (((comb F).coprod (comb F')) (c, c')) = (s (comb F c) - comb F c) + (s (comb F' c') - comb F' c')
      + ((comb F).coprod (comb F')) (c, c') := by
    simp only [LinearMap.coprod_apply, map_add]; abel
  rw [e]
  exact add_mem (add_mem (range_le_M F F' (X_le_range F h1)) (range_le_M' F F' (X_le_range F' h2))) ⟨_, rfl⟩

lemma orth_comb (F : FlagG S r T) (w : S.V) (hw : pair F w = 0) (c) : S.hT (comb F c) w = 0 := by
  simp only [comb, Fintype.linearCombination_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  have : S.hT (F.fvec a) w = 0 := congrFun hw a
  rw [this, smul_zero]

lemma mem_W (F : FlagG S r T) (F' : FlagG S r T') (w : S.V) :
    w ∈ Wsp F F' ↔ ∀ m ∈ Msp F F', S.hT m w = 0 := by
  constructor
  · rintro hw _ ⟨⟨c, c'⟩, rfl⟩
    have h1 : pair F w = 0 := congrArg Prod.fst hw
    have h2 : pair F' w = 0 := congrArg Prod.snd hw
    rw [LinearMap.coprod_apply, map_add, LinearMap.add_apply, orth_comb F w h1, orth_comb F' w h2, add_zero]
  · intro h
    refine Prod.ext (funext fun a => ?_) (funext fun a => ?_)
    · exact h _ (range_le_M F F' (fvec_mem F a))
    · exact h _ (range_le_M' F F' (fvec_mem F' a))

lemma mapsTo_twoFlagFramesOrthogonal_of_isometry {s : S.V ≃ₗ[E] S.V} (hi : s ∈ Formalism.HermitianLatticesTheory.isom S.hT) {F : FlagG S r T} {F' : FlagG S r T'}
    (hM : ∀ m ∈ Msp F F', s m ∈ Msp F F') : ∀ w ∈ Wsp F F', s w ∈ Wsp F F' := by
  intro w hw
  rw [mem_W] at hw ⊢
  intro m hm
  obtain ⟨m0, hm0, rfl⟩ := surj_of_stable s _ hM m hm
  rw [hi m0 w]; exact hw m0 hm0

lemma X_orth_comb (F : FlagG S r T) (x : S.V) (hx : x ∈ F.X) (c) : S.hT x (comb F c) = 0 := by
  have : F.X ≤ LinearMap.ker (S.hT.flip (comb F c)) := by
    rw [FlagG.X, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have := congrFun (pair_comb_self F c) a.castSucc
    rw [pair_apply, fvec_cast] at this
    simpa [Fin.castSucc_ne_last] using this
  exact this hx

lemma half {s : S.V ≃ₗ[E] S.V} (hi : s ∈ Formalism.HermitianLatticesTheory.isom S.hT) {F : FlagG S r T} {F' : FlagG S r T'}
    (hD : (Zhat F F').det ≠ 0) (hs : Stab s F) (hs' : Stab s F') (c c' : Fin (r + 1) → E)
    (ho : ∀ x ∈ F.X, S.hT x (comb F c + comb F' c') = 0) :
    s (comb F c + comb F' c') - (comb F c + comb F' c') ∈ F.X := by
  have h1 : ∀ x ∈ F.X, S.hT x (comb F' c') = 0 := fun x hx => by
    have := ho x hx
    rwa [map_add, X_orth_comb F x hx, zero_add] at this
  have h2 : ∀ x ∈ F.X, S.hT x (s (comb F' c')) = 0 := fun x hx => by
    obtain ⟨x0, hx0, rfl⟩ := surj_of_stable s _ hs.map_X x hx
    rw [hi]; exact h1 x0 hx0
  obtain ⟨d, hd⟩ := X_le_range F' (hs'.sub_comb _ ⟨c', rfl⟩)
  have h3 : (Zhat F F').mulVec d = 0 := by
    rw [← pair_comb, hd]
    ext a
    have h4 := h2 _ (Xa_le_X F _ (hs a))
    rw [map_sub, LinearMap.sub_apply, hi] at h4
    rw [pair_apply, map_sub, Pi.zero_apply]
    linear_combination -h4
  have h5 : d = 0 := Matrix.eq_zero_of_mulVec_eq_zero hD h3
  rw [h5, map_zero] at hd
  have e : s (comb F c + comb F' c') - (comb F c + comb F' c') =
      (s (comb F c) - comb F c) + (s (comb F' c') - comb F' c') := by
    rw [map_add]; abel
  rw [e, ← hd, add_zero]
  exact hs.sub_comb _ ⟨c, rfl⟩

def Fix (F : FlagG S r T) (F' : FlagG S r T') (h : S.V ≃ₗ[E] S.V) : Prop :=
  h ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧ (∀ a, h (F.fvec a) = F.fvec a) ∧ ∀ a, h (F'.fvec a) = F'.fvec a

def Unip (F : FlagG S r T) (n : S.V ≃ₗ[E] S.V) : Prop :=
  n ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧ (∀ j : ℕ, ∀ x ∈ F.Xa (j + 1), n x - x ∈ F.Xa j) ∧
    ∀ x ∈ orth S F.X, n x - x ∈ F.X

lemma mem_orth (U : Submodule E S.V) (x : S.V) : x ∈ orth S U ↔ ∀ u ∈ U, S.hT u x = 0 := by
  simp [orth, Submodule.mem_iInf]

lemma Fix.onM {F : FlagG S r T} {F' : FlagG S r T'} {h : S.V ≃ₗ[E] S.V} (hh : Fix F F' h) :
    ∀ m ∈ Msp F F', h m = m := by
  rintro _ ⟨⟨c, c'⟩, rfl⟩
  simp [comb, Fintype.linearCombination_apply, map_sum, hh.2.1, hh.2.2]

lemma unip_of {s h : S.V ≃ₗ[E] S.V} (hi : s ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hh : h ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    {F : FlagG S r T} (hs : Stab s F) (M W : Submodule E S.V) (hc : IsCompl M W) (hX : F.X ≤ M)
    (hM : ∀ m ∈ M, h m = m) (hW : ∀ w ∈ W, h w = s w) (hMW : ∀ w ∈ W, ∀ m ∈ M, S.hT m w = 0)
    (hh2 : ∀ m ∈ M, (∀ x ∈ F.X, S.hT x m = 0) → s m - m ∈ F.X) : Unip F (h⁻¹ * s) := by
  have hM' : ∀ m ∈ M, h⁻¹ m = m := fun m hm => by
    rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_eq, hM m hm]
  refine ⟨mul_mem (inv_mem hh) hi, fun j x hx => ?_, fun x hx => ?_⟩
  · rw [LinearEquiv.mul_apply, hM' _ (hX (hs.map_X x (Xa_le_X F _ hx)))]
    exact hs.sub_Xa j x hx
  · rw [mem_orth] at hx
    have : x ∈ M ⊔ W := by rw [hc.sup_eq_top]; trivial
    obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.mp this
    have hm2 : ∀ u ∈ F.X, S.hT u m = 0 := fun u hu => by
      have := hx u hu
      rwa [map_add, hMW w hw u (hX hu), add_zero] at this
    have h3 := hh2 m hm hm2
    have h4 : s m ∈ M := by
      have := M.add_mem (hX h3) hm
      rwa [sub_add_cancel] at this
    have h5 : h⁻¹ (s w) = w := by
      rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_eq, hW w hw]
    rw [LinearEquiv.mul_apply, map_add, map_add, hM' _ h4, h5, add_sub_add_right_eq_sub]
    exact h3

theorem inter_gen (F : FlagG S r T) (F' : FlagG S r T') (hD : (Zhat F F').det ≠ 0) (hG : Gflag F F' ≠ 0)
    (s : S.V ≃ₗ[E] S.V) (hi : s ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hs : Stab s F) (hs' : Stab s F') :
    ∃! h, Fix F F' h ∧ Unip F (h⁻¹ * s) ∧ Unip F' (h⁻¹ * s) := by
  have hc := isCompl_MW F F' hD hG
  have hD' : (Zhat F' F).det ≠ 0 := by
    rw [zhat_swap F F', Matrix.det_conjTranspose]; exact star_ne_zero.mpr hD
  have hsW := mapsTo_twoFlagFramesOrthogonal_of_isometry hi (map_M hs hs')
  have hdec : ∀ x, ∃ m ∈ Msp F F', ∃ w ∈ Wsp F F', m + w = x := fun x =>
    Submodule.mem_sup.mp (by rw [hc.sup_eq_top]; trivial)
  have hMW : ∀ w ∈ Wsp F F', ∀ m ∈ Msp F F', S.hT m w = 0 := fun w hw => (mem_W F F' w).mp hw
  have hWM : ∀ w ∈ Wsp F F', ∀ m ∈ Msp F F', S.hT w m = 0 := fun w hw m hm => by
    rw [hsymm, hMW w hw m hm, star_zero]
  have hXM : F.X ≤ Msp F F' := (X_le_range F).trans (range_le_M F F')
  have hXM' : F'.X ≤ Msp F F' := (X_le_range F').trans (range_le_M' F F')
  let h0 : S.V →ₗ[E] S.V :=
    LinearMap.ofIsCompl hc (Msp F F').subtype ((s : S.V →ₗ[E] S.V) ∘ₗ (Wsp F F').subtype)
  have h0M : ∀ m ∈ Msp F F', h0 m = m := fun m hm => LinearMap.ofIsCompl_apply_left hc ⟨m, hm⟩
  have h0W : ∀ w ∈ Wsp F F', h0 w = s w := fun w hw => LinearMap.ofIsCompl_apply_right hc ⟨w, hw⟩
  have hiso : ∀ x y, S.hT (h0 x) (h0 y) = S.hT x y := by
    intro x y
    obtain ⟨m, hm, w, hw, rfl⟩ := hdec x
    obtain ⟨m', hm', w', hw', rfl⟩ := hdec y
    simp only [map_add, LinearMap.add_apply, h0M _ hm, h0M _ hm', h0W _ hw, h0W _ hw', hi w w',
      hMW _ hw' _ hm, hMW _ (hsW _ hw') _ hm, hWM _ hw _ hm', hWM _ (hsW _ hw) _ hm']
  have hinj : Function.Injective h0 := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    refine S.nondeg.1 x fun y => ?_
    rw [← hiso, hx]; simp
  let h : S.V ≃ₗ[E] S.V := LinearEquiv.ofInjectiveEndo h0 hinj
  have hh : h ∈ Formalism.HermitianLatticesTheory.isom S.hT := hiso
  refine ⟨h, ⟨⟨hh, fun a => h0M _ (range_le_M F F' (fvec_mem F a)),
    fun a => h0M _ (range_le_M' F F' (fvec_mem F' a))⟩, ?_, ?_⟩, ?_⟩
  · refine unip_of hi hh hs _ _ hc hXM h0M h0W hMW ?_
    rintro _ ⟨⟨c, c'⟩, rfl⟩ ho
    exact half hi hD hs hs' c c' ho
  · refine unip_of hi hh hs' _ _ hc hXM' h0M h0W hMW ?_
    rintro _ ⟨⟨c, c'⟩, rfl⟩ ho
    rw [LinearMap.coprod_apply, add_comm (comb F c)] at ho ⊢
    exact half hi hD' hs' hs c' c ho
  · rintro g ⟨hg, hn, -⟩
    ext x
    obtain ⟨m, hm, w, hw, rfl⟩ := hdec x
    have hgM : ∀ m ∈ Msp F F', g⁻¹ m = m := fun m hm => by
      rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_eq, hg.onM m hm]
    have h1 : g⁻¹ (s w) ∈ Wsp F F' :=
      mapsTo_twoFlagFramesOrthogonal_of_isometry (inv_mem hg.1) (fun m hm => by rw [hgM m hm]; exact hm) _ (hsW w hw)
    have h2 : g⁻¹ (s w) - w ∈ F.X := hn.2.2 w ((mem_orth _ _).mpr fun u hu => hMW w hw u (hXM hu))
    have h3 : g⁻¹ (s w) - w = 0 := Submodule.disjoint_def.mp hc.disjoint _ (hXM h2) (sub_mem h1 hw)
    rw [sub_eq_zero, LinearEquiv.coe_inv, LinearEquiv.symm_apply_eq] at h3
    show g (m + w) = h0 (m + w)
    rw [map_add, map_add, h0M m hm, h0W w hw, hg.onM m hm, h3]

lemma det_ne_of_om {Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : (ZhatOM Z).det ≠ 0) : Z.det ≠ 0 := by
  intro h0
  apply h
  have : ZhatOM Z = Matrix.of fun a b => (fun b : Fin (r + 1) => (-1 : E) ^ (r - b.val)) b * Z a b := rfl
  rw [this, Matrix.det_mul_row, h0, mul_zero]

end Gen

theorem common_stabiliser : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ s, Adapt s F F → Adapt s F' F' → ∃! h, h ∈ H0 F F' ∧ h⁻¹ * s ∈ NRat F ∧ h⁻¹ * s ∈ NRat F' := by
  intro D X Y u u' F F' w hZ hG s hs hs'
  exact inter_gen F.fl F'.fl (det_ne_of_om (by rw [hZ]; exact Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_det w)) hG s hs.1 hs.2 hs'.2

end GlobalTheory.Unfold.Inter
