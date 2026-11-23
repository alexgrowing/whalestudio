import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompOfOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftFormLvlOp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFrameUnitaryDivisorSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrivOutsideListProd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitReductionStandardFrameConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetOneAddVecMulVecSingle
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOrIsConjPlaceOfOverSplitPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitPlaceWPlGw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeCongruenceInLevelCharacterOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyConjunctionMono
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PinOfNTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CentralOfTameCoupled
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProvisionalRowsFurtherCompatibilitiesAtState
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CenFrame

section Mat

variable {k : Type} [CommRing k] {n n' r t : ℕ}

theorem blkOf_eq (h : n = r + t) (ht : 0 < t) : blkOf (n := n) r t = blk2 r := by
  funext a
  unfold blkOf blk2
  split_ifs with ha
  · rfl
  · have := a.2
    rw [Nat.div_eq_of_lt (by omega)]

theorem mem_twoBlockTriangular_of_blockTriangular {x : GL (Fin n) k} (h : ∀ a c : Fin n, r ≤ (a : ℕ) → (c : ℕ) < r → x.val a c = 0) : x ∈ blockTri (blk2 r) := by
  refine mem_blockTri.2 fun a c hac => ?_
  unfold blk2 at hac
  by_cases ha : (a : ℕ) < r <;> by_cases hc : (c : ℕ) < r <;> simp [ha, hc] at hac
  exact h a c (by omega) hc

theorem colMat_blocks (hn : n' = n) (h : n = r + t) (ht : 0 < t) (hr : r ≤ n') (x : GL (Fin n') k) (m : Fin n) (v : Fin n → k)
    (hm : r ≤ (m : ℕ)) (hv : v m = 0) (hx : ∀ a c, x.val (Fin.cast hn.symm a) (Fin.cast hn.symm c) = colMat v m a c) :
    x ∈ blockTri (blkOf r t) ∧ dBlk (blkOf r t) 1 x = 1 ∧ upperLeftBlock hr x = 1 := by
  subst hn
  have hx' : ∀ a c, x.val a c = (if a = c then 1 else 0) + v a * (if c = m then 1 else 0) := fun a c => by
    have := hx a c
    simpa [colMat, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.single_apply] using this
  have hb : x ∈ blockTri (blk2 r) := mem_twoBlockTriangular_of_blockTriangular fun a c ha hc => by
    rw [hx', if_neg (by rintro rfl; omega), if_neg (by rintro rfl; omega)]; simp
  rw [blkOf_eq h ht]
  refine ⟨hb, Units.ext ?_, Units.ext ?_⟩
  · rw [diag_block_det_val 1 hb]
    have hm1 : blk2 r m = 1 := by unfold blk2; rw [if_neg (by omega)]
    have e : (x : Matrix (Fin n') (Fin n') k).submatrix (Subtype.val : {a : Fin n' // blk2 r a = 1} → Fin n') Subtype.val =
        1 + Matrix.replicateCol Unit (fun a : {a : Fin n' // blk2 r a = 1} => v a.1) *
          Matrix.replicateRow Unit (Pi.single (⟨m, hm1⟩ : {a : Fin n' // blk2 r a = 1}) (1 : k)) := by
      ext a c
      simp [hx', Matrix.one_apply, Matrix.mul_apply, Pi.single_apply, Subtype.ext_iff]
    rw [e, Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp [hv]
  · rw [upper_block_val_submatrix hr hb]
    ext a c
    have hc : Fin.castLE hr c ≠ m := by
      rintro rfl
      have := c.2
      simp at hm
      omega
    simp [hx', hc, Matrix.one_apply]

theorem conj_blocks (hn : n' = n) (h : n = r + t) (ht : 0 < t) (hr : r ≤ n) (hr' : r ≤ n') (b : GL (Fin n) k)
    (hb : ∀ a c : Fin n, r ≤ (a : ℕ) → (c : ℕ) < r → b.val a c = 0) (g : GL (Fin r) k) (e : GL (Fin n) k)
    (he : ∀ a c : Fin n, e.val a c = if hac : (a : ℕ) < r ∧ (c : ℕ) < r then g.val ⟨a, hac.1⟩ ⟨c, hac.2⟩ else if a = c then 1 else 0)
    (x : GL (Fin n') k) (hx : ∀ a c, x.val (Fin.cast hn.symm a) (Fin.cast hn.symm c) = (b * e * b⁻¹).val a c) :
    x ∈ blockTri (blkOf r t) ∧ dBlk (blkOf r t) 1 x = 1 ∧ upperLeftBlock hr' x = upperLeftBlock hr b * g * (upperLeftBlock hr b)⁻¹ := by
  subst hn
  obtain rfl : x = b * e * b⁻¹ := Units.ext (Matrix.ext fun a c => hx a c)
  have hb' : b ∈ blockTri (blk2 r) := mem_twoBlockTriangular_of_blockTriangular hb
  have he' : e ∈ blockTri (blk2 r) := mem_twoBlockTriangular_of_blockTriangular fun a c ha hc => by
    rw [he, dif_neg (by omega), if_neg (by rintro rfl; omega)]
  have hd : dBlk (blk2 r) 1 e = 1 := by
    refine Units.ext ?_
    rw [diag_block_det_val 1 he']
    have e1 : (e : Matrix (Fin n') (Fin n') k).submatrix (Subtype.val : {a : Fin n' // blk2 r a = 1} → Fin n') (Subtype.val : {a : Fin n' // blk2 r a = 1} → Fin n') = 1 := by
      ext a c
      have ha : ¬ ((a.1 : ℕ) < r) := fun h' => by
        have := a.2
        unfold blk2 at this
        rw [if_pos h'] at this
        omega
      rw [Matrix.submatrix_apply, he, dif_neg (fun h' => ha h'.1)]
      simp [Matrix.one_apply, Subtype.ext_iff]
    rw [e1]
    simp
  have hg : upperLeftBlock hr e = g := by
    refine Units.ext ?_
    rw [upper_block_val_submatrix hr he']
    ext a c
    rw [Matrix.submatrix_apply, he, dif_pos ⟨a.2, c.2⟩]
    rfl
  rw [blkOf_eq h ht]
  refine ⟨mul_mem (mul_mem hb' he') (inv_mem hb'), ?_, ?_⟩
  · rw [diag_block_det_mul (mul_mem hb' he') (inv_mem hb'), diag_block_det_mul hb' he', hd, mul_one, ← diag_block_det_mul hb' (inv_mem hb'), mul_inv_cancel]
    exact blockDiagonalExtendByOnePrimeField_one _ _
  · rw [← hg]
    exact (extendMatrixByIdentityAlongIndices_mul _ (mul_mem hb' he') (inv_mem hb')).trans
      (congrArg₂ (· * ·) (extendMatrixByIdentityAlongIndices_mul _ hb' he') (extendOne_inv _ hb'))

end Mat

section Loc

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem exists_isCompOf (s : ReciprocityTheory.Aut.SplitPlace L) {κ : Formalism.AUTREP.GAf L n} (h : κ ∈ ReciprocityTheory.Aut.Umax L n) :
    ∃ y, IsCompOf s κ y := by
  have h1 : s.loc n κ ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := by
    rw [GlobalTheory.HeckeStdFacts.mem_GLint_iff, ← map_inv]
    exact ⟨fun i j => GlobalTheory.HeckeStdFacts.proj_mem s (h i j), fun i j => GlobalTheory.HeckeStdFacts.proj_mem s (inv_mem h i j)⟩
  obtain ⟨y, hy⟩ := h1
  exact ⟨y, fun a c => congrArg (fun g : GL (Fin n) _ => g.val a c) hy⟩

theorem mem_Umax_of_isCompOf (s : ReciprocityTheory.Aut.SplitPlace L) {κ : Formalism.AUTREP.GAf L n} (ht : ReciprocityTheory.Aut.TrivOutside {s.v} κ)
    {y : GL (Fin n) (Os s)} (h : IsCompOf s κ y) : κ ∈ ReciprocityTheory.Aut.Umax L n :=
  (GlobalTheory.HeckeStdFacts.loc_mem_GLint_iff s ht).1 ⟨y, Units.ext (Matrix.ext fun a c => h a c)⟩

theorem red_of_isLiftAt (s : ReciprocityTheory.Aut.SplitPlace L) {k : Type} [CommRing k] {φ : Os s →+* k} (hφ : IsResidue s φ) {r p : ℕ}
    (hp : p.Prime) (iso : ZMod p →+* k) (g : GL (Fin r) (ZMod p)) {κ : Formalism.AUTREP.GAf L n} {y : GL (Fin n) (Os s)}
    (hy : IsCompOf s κ y) (hl : GlobalTheory.PendOf.IsLiftAt s r p g (s.loc n κ)) (a c : Fin n) :
    (Matrix.GeneralLinearGroup.map φ y).val a c =
      if hac : (a : ℕ) < r ∧ (c : ℕ) < r then (Formalism.UG.bc iso g).val ⟨a, hac.1⟩ ⟨c, hac.2⟩ else if a = c then 1 else 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h := hl a c
  show φ (y.val a c) = _
  by_cases hac : (a : ℕ) < r ∧ (c : ℕ) < r
  · rw [dif_pos hac] at h ⊢
    rw [← hy a c] at h
    have h2 : φ (y.val a c - ((g.val ⟨a, hac.1⟩ ⟨c, hac.2⟩).val : Os s)) = 0 := (hφ.ker _).2 (by
      have e : ((y.val a c - ((g.val ⟨a, hac.1⟩ ⟨c, hac.2⟩).val : Os s) : Os s) : s.v.adicCompletion (maximalRealSubfield L)) =
          (y.val a c : s.v.adicCompletion (maximalRealSubfield L)) - ((g.val ⟨a, hac.1⟩ ⟨c, hac.2⟩).val : ℕ) :=
        (map_sub (s.v.adicCompletionIntegers (maximalRealSubfield L)).subtype _ _).trans
          (congrArg _ (map_natCast (s.v.adicCompletionIntegers (maximalRealSubfield L)).subtype _))
      rw [e]; exact h)
    rw [map_sub, sub_eq_zero, map_natCast] at h2
    rw [h2]
    show _ = iso (g.val ⟨a, hac.1⟩ ⟨c, hac.2⟩)
    rw [← map_natCast iso, ZMod.natCast_zmod_val]
  · rw [dif_neg hac] at h ⊢
    rw [← hy a c] at h
    by_cases e : a = c
    · rw [if_pos e] at h ⊢
      rw [show y.val a c = 1 from Subtype.ext h, map_one]
    · rw [if_neg e] at h ⊢
      rw [show y.val a c = 0 from Subtype.ext h, map_zero]

end Loc

section Lev

variable {D : D7}

theorem lev_of_red (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Ld : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (hs : Ld.s = 1) (κ : GA D V)
    (hSt : finE V κ ∈ Formalism.L2.DIV.St β) (hQ : ∀ PP ∈ Ld.Q, redFn β PP (finE V κ) = 1)
    (hP : ∀ PP ∈ Ld.Pg, redFn β PP (finE V κ) ∈ blockTri (blkOf Ld.r Ld.t) ∧ dBlk (blkOf Ld.r Ld.t) 1 (redFn β PP (finE V κ)) = 1) :
    finE V κ ∈ parLev D.sp.cm V.gram β Ld ∧
      levChi V β Ld κ = ((ext1 Ld.P.H Ld.P.chi (rTup β Ld (finE V κ)) : ℂˣ) : ℂ) := by
  refine ⟨mem_parLev.2 ⟨GlobalTheory.LevFinCong.finE_mem_UA V κ, hSt, fun PP h => (hP PP h).1, fun PP h => ?_⟩, ?_⟩
  · rw [hQ PP h]; exact one_mem _
  · unfold levChi levFn
    rw [Finset.prod_eq_one, Finset.prod_eq_one, mul_one, mul_one]
    · intro PP h
      rw [hQ PP h, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
    · intro PP h
      rw [hs, Finset.prod_range_one, zero_add, (hP PP h).2, map_one]

theorem exists_overPl (PP : Formalism.L2.DIV.Pl D.host.E) : ∃ v, NG.OverPl PP v := ⟨PP.under _, rfl⟩

theorem nat_mem_of_overPl {P P' : Formalism.L2.DIV.Pl D.host.E} {v} (h : NG.OverPl P v) (h' : NG.OverPl P' v) {p : ℕ}
    (hp : (p : 𝓞 D.host.E) ∈ P.asIdeal) : (p : 𝓞 D.host.E) ∈ P'.asIdeal := by
  have h1 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ v.asIdeal := by
    rw [← h, Ideal.mem_comap, map_natCast]; exact hp
  rw [← h', Ideal.mem_comap, map_natCast] at h1
  exact h1

theorem twist_off {T : Type} {Lc : Formalism.IndefR.Links.LevCh D T} {μ0 : T} (hL : Lc.Is μ0) (t : T) {PP} (hPP : PP ∈ Lc.Q t) {v}
    (hv : NG.OverPl PP v) : v ∉ GlobalTheory.PendOf.gPl D := by
  rintro ⟨kv, hkv⟩
  obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := hL.Q_pl t PP hPP
  exact GlobalTheory.MtIn.Under.not_both (D.host.g_prime kv.1) hq1 (hq4 kv.1)
    (nat_mem_of_overPl hkv hv (D.naut.plGw_over kv.1 kv.2)) (GlobalTheory.MtIn.Under.q_mem hq2)

theorem fixed_eq (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (kv kv' : Σ k : Fin 2, D.nd.PlG k) (hs : s.w = D.naut.plGw kv.1 kv.2)
    (h : NG.OverPl (D.naut.plGw kv'.1 kv'.2) s.v) : s.w = D.naut.plGw kv'.1 kv'.2 := by
  rcases GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s _ h with e | e
  · exact e
  · obtain ⟨k, v⟩ := kv
    obtain ⟨k', v'⟩ := kv'
    by_cases hk : k' = k
    · subst hk
      rw [hs] at e
      exact absurd e (D.naut.plGw_nconj _ _ _)
    · have hne : D.host.g k' ≠ D.host.g k := by
        have := D.host.g_ne
        fin_cases k <;> fin_cases k' <;> first | exact absurd rfl hk | exact this | exact this.symm
      refine (GlobalTheory.MtIn.Under.not_both (D.host.g_prime k) (D.host.g_prime k') hne ?_
        (nat_mem_of_overPl h s.w_under (D.naut.plGw_over k' v'))).elim
      rw [hs]
      exact D.naut.plGw_over k v

end Lev

section Core

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem rank_V (i : Fin D.R.m) : (Vc D i).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) i.2

theorem t_pos (D : D7) : 0 < D.R.t := by have := D.R.rank_add_five_le; omega

theorem two_le_r (D : D7) : 2 ≤ D.R.r := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; unfold Ranks.r; omega

theorem r_lt_nV (D : D7) : D.R.r < D.R.nV := by have := t_pos D; unfold Ranks.nV; omega

set_option maxHeartbeats 1000000 in

theorem local_red (hL : R.toLevCh.Is A.μ0) (hPg : ∀ PP ∈ R.Pg, ∃ kv : (Σ k : Fin 2, D.nd.PlG k), PP = D.naut.plGw kv.1 kv.2)
    (i : Fin D.R.m) (t : T) (Pl : LevelP R.Pg D.R.r ℂ) {hF : D.host.F = maximalRealSubfield D.host.E}
    (P : principalLevelFrame.RowPsi (Vc D i) D.R.nV) (hP : R3.StdFrame hF P) {W : Type} [AddCommGroup W] [Module ℂ W]
    (f : Formalism.AUTREP.GAf D.host.E D.R.nV → W) (hf : f ≠ 0) (J : Subgroup (Formalism.AUTREP.GAf D.host.E D.R.nV)) (χ : J →* ℂˣ)
    (hJ : ∀ (κ : J) x, f (x * κ) = ((χ κ : ℂˣ) : ℂ) • f x)
    (hlev : ∀ κ, P.ψ κ ∈ levS (Vc D i) (R.βV i) (datVP R i t Pl) → ∀ x, f (x * κ) = levChi (Vc D i) (R.βV i) (datVP R i t Pl) (P.ψ κ) • f x)
    (kv : Σ k : Fin 2, D.nd.PlG k) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (hs : s.w = D.naut.plGw kv.1 kv.2)
    (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ)
    (h0 : NG.IsPsi0 s ψ₀) (hu : NG.LevelUni J χ s D.R.r ψ₀ ξ) (PP : Formalism.L2.DIV.Pl D.host.E) (hPP : s.w = PP)
    (iso : ZMod (D.host.g kv.1) →+* kP PP) :
    ∃ u : GL (Fin D.R.r) (kP PP), ∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV, ∀ g : GL (Fin D.R.r) (ZMod (D.host.g kv.1)),
      GlobalTheory.PendOf.IsLiftAt s D.R.r (D.host.g kv.1) g (s.loc D.R.nV κ) →
      redFn (R.βV i) PP (finE (Vc D i) (P.ψ κ)) ∈ blockTri (blkOf D.R.r D.R.t) ∧
        dBlk (blkOf D.R.r D.R.t) 1 (redFn (R.βV i) PP (finE (Vc D i) (P.ψ κ))) = 1 ∧
        upperLeftBlock (r_le_V i) (redFn (R.βV i) PP (finE (Vc D i) (P.ψ κ))) = u * Formalism.UG.bc iso g * u⁻¹ := by
  subst hPP
  obtain ⟨c, hβ⟩ := hL.βV i
  rw [one_pow] at hβ
  obtain ⟨φ, b, hφ, hb⟩ := GlobalTheory.FrameRedSplit.frameRed_exists D (Vc D i) D.R.nV (rank_V i) hF P (R.βV i) _ hP hβ s
  have hpar : ∀ a c : Fin D.R.nV, D.R.r ≤ (a : ℕ) → (c : ℕ) < D.R.r → b.val a c = 0 := by
    refine GlobalTheory.ParaForce.para_of_colMat_fixed D.host.E D.R.nV D.R.r s (kP s.w) φ (Field.toIsField _) hφ (two_le_r D) (r_lt_nV D) W f hf J χ ψ₀ ξ h0 hu hJ b ?_
    intro κ y ht hy m v hm hv he x
    have hU := mem_Umax_of_isCompOf s ht hy
    obtain ⟨hSt, hoff⟩ := GlobalTheory.FrameOff.stdFrame_stab_red D (Vc D i) D.R.nV hF P (R.βV i) _ hP hβ κ hU
    have hall : ∀ PP ∈ R.Pg, redFn (R.βV i) PP (finE (Vc D i) (P.ψ κ)) ∈ blockTri (blkOf D.R.r D.R.t) ∧
        dBlk (blkOf D.R.r D.R.t) 1 (redFn (R.βV i) PP (finE (Vc D i) (P.ψ κ))) = 1 ∧
        upperLeftBlock (r_le_V i) (redFn (R.βV i) PP (finE (Vc D i) (P.ψ κ))) = 1 := by
      intro PP hPP
      by_cases e : s.w = PP
      · subst e
        exact colMat_blocks (rank_V i) rfl (t_pos D) (r_le_V i) _ m v hm hv fun a c => (hb κ hU y hy a c).trans (by rw [he])
      · obtain ⟨v', hv'⟩ := exists_overPl PP
        have hne : v' ∉ ({s.v} : Set _) := by
          rintro rfl
          obtain ⟨kv', rfl⟩ := hPg PP hPP
          exact e (fixed_eq s kv kv' hs hv')
        rw [hoff _ v' PP ht hv' hne]
        exact ⟨one_mem _, blockDiagonalExtendByOnePrimeField_one _ _, blockDiagonalExtendByOnePrimeField_one _ _⟩
    have hQ : ∀ PP ∈ R.Q t, redFn (R.βV i) PP (finE (Vc D i) (P.ψ κ)) = 1 := by
      intro PP hPP
      obtain ⟨v', hv'⟩ := exists_overPl PP
      refine hoff _ v' PP ht hv' ?_
      rintro rfl
      exact twist_off hL t hPP hv' ⟨kv, hs ▸ s.w_under⟩
    obtain ⟨h1, h2⟩ := lev_of_red (Vc D i) (R.βV i) (datVP R i t Pl) rfl (P.ψ κ) hSt hQ fun PP h => ⟨(hall PP h).1, (hall PP h).2.1⟩
    have h3 : rTup (R.βV i) (datVP R i t Pl) (finE (Vc D i) (P.ψ κ)) = 1 := funext fun PP => (hall PP.1 PP.2).2.2
    rw [h3, blockDiagonalExtendByOnePrimeField_one] at h2
    have h4 : P.ψ κ ∈ levS (Vc D i) (R.βV i) (datVP R i t Pl) := ⟨P.into κ, h1, by rw [h3]; exact one_mem _⟩
    rw [hlev κ h4 x, h2]
    simp
  refine ⟨upperLeftBlock (r_lt_nV D).le b, fun κ hU g hg => ?_⟩
  obtain ⟨y, hy⟩ := exists_isCompOf s hU
  exact conj_blocks (rank_V i) rfl (t_pos D) (r_lt_nV D).le (r_le_V i) b hpar _ _
    (red_of_isLiftAt s hφ (D.host.g_prime kv.1) iso g hy hg) _ (hb κ hU y hy)

theorem coeff_conj {H : Type} [Group H] (z : Subalgebra.center ℂ (MonoidAlgebra ℂ H)) (u g : H) :
    (z : MonoidAlgebra ℂ H).coeff (u⁻¹ * g * u) = (z : MonoidAlgebra ℂ H).coeff g := by
  have hc := (Subalgebra.mem_center_iff.1 z.2) (MonoidAlgebra.single u 1)
  have := congrArg (fun z => z.coeff (g * u)) hc
  simp only [MonoidAlgebra.single_mul_apply, MonoidAlgebra.mul_single_apply, one_mul, mul_one, mul_inv_cancel_right] at this
  rw [mul_assoc]
  exact this

end Core

section Main

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

set_option maxHeartbeats 2000000 in

theorem cen_used (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (hB : R.toRealDat.BaseW F.lv2)
    (hK : Keep (A3 := A3) R.toRealDat F.lv2 cG) (hO : A3.A.fam.Ok 1) (hC : CenRead Y cG) (M : MtFam D) (ad : MtAd Y M)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (i : Fin D.R.m) (h1 : 1 ≤ (i : ℕ) + 1) (h2 : (i : ℕ) + 1 ≤ D.R.m)
    (hu : ∀ (k : Fin 2) (v : D.nd.PlG k) (s : ReciprocityTheory.Aut.SplitPlace D.host.E), s.w = D.naut.plGw k v →
      ∃ ψ₀ ξ, NG.IsPsi0 s ψ₀ ∧ NG.LevelUni (M μ ((i : ℕ) + 1) h1 h2).J (M μ ((i : ℕ) + 1) h1 h2).χ s D.R.r ψ₀ ξ) :
    ∃ L : G0g D.nd → Formalism.AUTREP.GAf D.host.E D.R.nV, GlobalTheory.PendOf.IsTypeGroupBlockLift D D.R.nV L ∧
      ∀ (z : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) (x : D.what₂.Mt μ ((i : ℕ) + 1)),
        (M μ ((i : ℕ) + 1) h1 h2).real (D.ntypes.cenMt μ ((i : ℕ) + 1) z x) =
          GlobalTheory.PendOf.actSum D L (z : MonoidAlgebra ℂ (G0g D.nd)) ((M μ ((i : ℕ) + 1) h1 h2).real x) := by
  obtain ⟨t, rfl⟩ : ∃ t, Y.tup t = μ := ⟨_, Y.tupTie μ hμ⟩
  obtain ⟨Lf, hLf, hU⟩ := GlobalTheory.LiftStandardGroup.main D D.R.nV (r_lt_nV D).le
  refine ⟨Lf, hLf, fun z x => ?_⟩
  have hread := ad.read _ hμ i
  by_cases hx : (M (Y.tup t) ((i : ℕ) + 1) h1 h2).real x = 0
  · have hx0 : x = 0 := (M (Y.tup t) ((i : ℕ) + 1) h1 h2).real_inj (hx.trans (map_zero _).symm)
    rw [hx0, map_zero, map_zero]
    simp [GlobalTheory.PendOf.actSum, Finsupp.sum]
  obtain ⟨plg, iso, hpl, -, -, hiso⟩ := hK.grp
  have hPg : ∀ PP ∈ R.Pg, ∃ kv : (Σ k : Fin 2, D.nd.PlG k), PP = D.naut.plGw kv.1 kv.2 := fun PP h =>
    ⟨plg.symm ⟨PP, h⟩, by rw [← hpl, Equiv.apply_symm_apply]⟩
  have hty : (M (Y.tup t) ((i : ℕ) + 1) h1 h2).real x ∈ NG.TypeSp _ _ _ :=
    (M (Y.tup t) ((i : ℕ) + 1) h1 h2).real_range ▸ LinearMap.mem_range_self _ x
  have hloc : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ∃ u : GL (Fin D.R.r) (kP (plg kv).1), ∀ g : G0g D.nd,
      redFn (R.βV i) (plg kv).1 (finE (Vc D i) ((ad.PV i).ψ (Lf g))) ∈ blockTri (blkOf D.R.r D.R.t) ∧
        dBlk (blkOf D.R.r D.R.t) 1 (redFn (R.βV i) (plg kv).1 (finE (Vc D i) ((ad.PV i).ψ (Lf g)))) = 1 ∧
        upperLeftBlock (r_le_V i) (redFn (R.βV i) (plg kv).1 (finE (Vc D i) ((ad.PV i).ψ (Lf g)))) =
          u * Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (g kv) * u⁻¹ := by
    intro kv
    obtain ⟨s, hs⟩ := GlobalTheory.FixedPlaceOverType.exists_splitPlace_w_plGw D kv.1 kv.2
    obtain ⟨ψ₀, ξ, h0, hl⟩ := hu kv.1 kv.2 s hs
    obtain ⟨u, hu'⟩ := local_red (R := R.toRealDat) hB.lev hPg i (Y.tupT (Y.tup t)) (R.toRealDat.levR F.lv2 false) (ad.PV i) (ad.std i) _ hx _ _
      (fun κ y => congrFun (hty.2 κ) y)
      (fun κ hκ y => (ad.eW _ hμ i).injective (by
        rw [map_smul, hread, hread, map_mul]
        exact (Y.IL.jMt _ hμ i x).2.2 _ hκ _))
      kv s hs ψ₀ ξ h0 hl (plg kv).1 (hs.trans (hpl kv).symm) (iso kv)
    exact ⟨u, fun g => hu' _ (hU g) _ ((hLf g).2 kv s hs)⟩
  choose u hu' using hloc
  obtain ⟨c, hβ⟩ := hB.lev.βV i
  rw [one_pow] at hβ
  obtain ⟨û, hû⟩ : ∃ û : G, ∀ kv, R.eG û (plg kv) = u kv := by
    let u' : G0 R.Pg D.R.r := (Equiv.piCongrLeft (fun PP : R.Pg => GL (Fin D.R.r) (kP PP.1)) plg) u
    exact ⟨R.eG.symm u', fun kv => by rw [MulEquiv.apply_symm_apply]; exact Equiv.piCongrLeft_apply_apply _ _ _ _⟩
  have key : ∀ g : G0g D.nd,
      IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG (û * (R.eG.trans cG).symm g * û⁻¹)) ((ad.PV i).ψ (Lf g)) ∧
        levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) ((ad.PV i).ψ (Lf g)) = 1 := by
    intro g
    obtain ⟨hSt, hoff⟩ := GlobalTheory.FrameOff.stdFrame_stab_red D (Vc D i) D.R.nV Y.hF (ad.PV i) (R.βV i) _ (ad.std i) hβ _ (hU g)
    have hQ : ∀ PP ∈ R.Q t, redFn (R.βV i) PP (finE (Vc D i) ((ad.PV i).ψ (Lf g))) = 1 := by
      intro PP hPP
      obtain ⟨v', hv'⟩ := exists_overPl PP
      exact hoff _ v' PP (hLf g).1 hv' (twist_off hB.lev t hPP hv')
    have hP : ∀ PP ∈ R.Pg, redFn (R.βV i) PP (finE (Vc D i) ((ad.PV i).ψ (Lf g))) ∈ blockTri (blkOf D.R.r D.R.t) ∧
        dBlk (blkOf D.R.r D.R.t) 1 (redFn (R.βV i) PP (finE (Vc D i) ((ad.PV i).ψ (Lf g)))) = 1 := by
      intro PP hPP
      obtain ⟨kv, e⟩ := plg.surjective ⟨PP, hPP⟩
      obtain rfl : (plg kv).1 = PP := congrArg Subtype.val e
      exact ⟨(hu' kv g).1, (hu' kv g).2.1⟩
    refine ⟨⟨(ad.PV i).into _, (lev_of_red (Vc D i) (R.βV i) (R.datVt i t) rfl _ hSt hQ hP).1, funext fun PP => ?_⟩, ?_⟩
    · obtain ⟨kv, rfl⟩ := plg.surjective PP
      refine (hu' kv g).2.2.trans ?_
      rw [map_mul, map_mul, map_inv, Pi.mul_apply, Pi.mul_apply, Pi.inv_apply, hû, hiso, MulEquiv.apply_symm_apply]
    · rw [(lev_of_red (Vc D i) (R.βV i) (flagL (R.datVt i t)) rfl _ hSt hQ hP).2,
        extendOne_of_mem (P := (flagL (R.datVt i t)).P.H) _ (Subgroup.mem_top _)]
      rfl
  let e : G ≃ G0g D.nd := (MulAut.conj û⁻¹).toEquiv.trans (R.eG.trans cG).toEquiv
  have he : ∀ g, û * (R.eG.trans cG).symm (e g) * û⁻¹ = g := fun g => by
    show û * (R.eG.trans cG).symm ((R.eG.trans cG) (û⁻¹ * g * û⁻¹⁻¹)) * û⁻¹ = g
    rw [MulEquiv.symm_apply_apply]; group
  have hact := GlobalTheory.CenTranslate.main D G Pl0 I0 T A3 Ks R.toRealDat F.lv2 X0 Y cG hB hO hC i t hμ (fun g => (ad.PV i).ψ (Lf (e g)))
    (fun g => by have := (key (e g)).1; rwa [he] at this) z x
  funext y
  refine (ad.eW _ hμ i).injective ?_
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv G e
  rw [hread, hact, GlobalTheory.PendOf.actSum, Finsupp.sum_fintype _ _ (by intro _; exact zero_smul _ _), Finset.sum_apply, map_sum, ← e.sum_comp]
  refine Finset.sum_congr rfl fun g _ => ?_
  have hz : (z : MonoidAlgebra ℂ (G0g D.nd)).coeff (e g) = (z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g) := by
    show (z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) (û⁻¹ * g * û⁻¹⁻¹)) = _
    rw [inv_inv, map_mul (R.eG.trans cG), map_mul (R.eG.trans cG), map_inv (R.eG.trans cG), coeff_conj]
  rw [(key (e g)).2, inv_one, mul_one, Pi.smul_apply, map_smul, hz, ← map_mul (ad.PV i).ψ, ← hread]
  rfl

theorem cen_twisted (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (hB : R.toRealDat.BaseW F.lv2)
    (hK : Keep (A3 := A3) R.toRealDat F.lv2 cG) (hO : A3.A.fam.Ok 1) (hC : CenRead Y cG) (M : MtFam D) (ad : MtAd Y M)
    {tup : D.what₂.Tup → Fin D.R.m → Formalism.L2.Host.HChar D.host.E} {Q} (mt : MtInput D M tup Q) (w : D.what₂.places.Pl)
    (hw : D.what₂.muAt w ≠ D.what₂.mu0) (μ : D.what₂.Tup) (hμ : μ = D.what₂.muTw w) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    ∃ L : G0g D.nd → Formalism.AUTREP.GAf D.host.E D.R.nV, GlobalTheory.PendOf.IsTypeGroupBlockLift D D.R.nV L ∧
      ∀ (z : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) (x : D.what₂.Mt μ j),
        (M μ j h1 h2).real (D.ntypes.cenMt μ j z x) =
          GlobalTheory.PendOf.actSum D L (z : MonoidAlgebra ℂ (G0g D.nd)) ((M μ j h1 h2).real x) := by
  subst hμ
  obtain ⟨i, rfl⟩ : ∃ i : Fin D.R.m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  refine cen_used Y cG hB hK hO hC M ad _ (Or.inr ⟨w, ((D.what₂.muAt_or _).resolve_left hw).symm⟩) i h1 h2 fun k v s hs => ?_
  obtain ⟨ψ₀, ξ, h0, -, hl⟩ := mt.uni w i k v s hs
  exact ⟨ψ₀, ξ, h0, hl⟩

end Main

end GlobalTheory.CenFrame

namespace GlobalTheory.SerThird

open Formalism.MainNotions.N Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting.Up GlobalTheory.CenFrame
attribute [local instance] GlobalTheory.TypeRec.factG

theorem cen_heq {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] {O : Type} [CommRing O] {φ : O →+* ℂ}
    {σ : K →+* ℂ} {τ : Type} (mL : τ → Mat1 K G) (s : τ → Sp1 O φ G) (tL : ∀ μ, Tie1 σ (mL μ) (s μ)) {μ μ' : τ} (hμ : μ = μ')
    {m' : Mat1 K G} (h : mL μ' = m') (e : (Fin m'.n → K) → Fin (mL μ).n → K) (he : ∀ x, HEq (e x) x)
    (z : Subalgebra.center ℂ (MonoidAlgebra ℂ G)) (a : MonoidAlgebra K G)
    (ha : ∀ g, σ (a.coeff g) = (z : MonoidAlgebra ℂ G).coeff g) (x : Fin m'.n → K) :
    (s μ).act z ((tL μ).j (e x)) = (tL μ).j (e ((m'.op a).mulVec x)) := by
  subst hμ; subst h
  rw [eq_of_heq (he _), eq_of_heq (he _)]
  exact (tL μ).cen z a ha x

open Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Cx GlobalTheory.Mem.R3.Tr in
set_option maxHeartbeats 4000000 in

theorem cenRead_state {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) :
    CenRead x.r.Y x.m.z.cG := by
  intro i t z a ha v
  have hc := x.fits.cen _ (GlobalTheory.Mem.R3.Rw.Ties.stdIso_dat x.m.z)
  let z' : Subalgebra.center ℂ (MonoidAlgebra ℂ (Gc B w.px)) := Bare.cenPull (x.m.z.R.eG.trans x.m.z.cG) z
  have hz := Bare.coeff_cenPull (x.m.z.R.eG.trans x.m.z.cG) z
  have ha' : ∀ g, (w.st x.o.Z).toD7.what₂.embLL (a.coeff g) = (z' : MonoidAlgebra ℂ (Gc B w.px)).coeff g :=
    fun g => (ha g).trans (hz g).symm
  have h1 := hc.mt (x.r.Y.tup t) ((i : ℕ) + 1) ((by with_unfolding_all exact (z :))) z' ((by with_unfolding_all exact (hz :)))
    ((P.q.p.tL (x.r.Y.tup t) ((i : ℕ) + 1)).j ((by with_unfolding_all exact ((x.r.Y.eMt i t v) :))))
  have h2 := cen_heq (fun a => P.q.p.mL a ((i : ℕ) + 1)) (fun a => P.q.p.sL a ((i : ℕ) + 1)) (fun a => P.q.p.tL a ((i : ℕ) + 1))
    (congrFun x.r.tup t) (x.m.t.hL i t) (fun y => (by with_unfolding_all exact ((x.r.Y.eMt i t ((y))) : _))) ((by with_unfolding_all exact ((x.r.eMt i t) :))) z' ((by with_unfolding_all exact (a :))) ((by with_unfolding_all exact (ha' :))) ((by with_unfolding_all exact (v :)))
  exact (by with_unfolding_all exact ((h1.trans h2) :))

set_option maxHeartbeats 4000000 in

theorem cenLoc_third {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} (x : St P) (l : LC hL x) (Lc : LocAll (lay0 (Dof x))) : CenLoc (withLoc Lc) (mtL Lc l.mt.M) := by
  intro i
  have h := cen_twisted x.r.Y x.m.z.cG x.m.z.pins.char.base x.m.z.pins.keep x.m.intersectionNumber_baseChange.ok.ok2 (cenRead_state x) l.mt.M l.mt.ad l.mt.mt
    ((withLoc Lc).nd.w i) ((withLoc Lc).nd.w_tw i) ((withLoc Lc).nd.mu i) ((withLoc Lc).nd.mu_w i) ((withLoc Lc).nd.j i)
    ((withLoc Lc).nd.j_range i).1 ((withLoc Lc).nd.j_range i).2
  exact (by with_unfolding_all exact (h :))

set_option maxHeartbeats 4000000 in

theorem pin_withLoc (hL : GlobalTheory.Published.LocalLanglandsGL) (hP : PrN) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
    {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : LC hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ)
    (L : LocAll (lay0 (Dof x))) (hB : GlobalTheory.CoefDuty.Built l.a.A l.mt.M l.c.ch l.c.tp.tup big L) :
    ∃ Q : GlobalTheory.NPin.Pin hL (withLoc L), Q.M = mtL L l.mt.M := by
  obtain ⟨Sp, ⟨Au⟩, ss⟩ := hB
  have hmt : MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
    have key : ∀ (xi : (Dof x).what₂.Tup → HChar (Dof x).host.E) (Q : (Dof x).what₂.places.Pl → Finset (PlE (Dof x).host)),
        MtInput (Dof x) l.mt.M (fun μ j => (cfOf x).mu0 j * xi μ) Q → l.c.tp.xi = xi → l.c.ch.Q = Q →
          MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
      intro xi Q h hx hQ
      subst hx hQ
      exact h
    exact key _ _ l.mt.mt l.c.xi_eq l.c.Q_eq
  let nt : NTrue hL (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp) :=
    { D := Dof x, cf := cfOf x, jE := l.a.jE, A := l.a.A, cg := l.a.cg, au := l.a.au, rep := repOf x.r.Y, row := l.a.row,
      low := lowAll (Dof x), Pq := l.Pq, S := l.rat.S, hL := l.rat.In.hL, eig := l.rat.In.eig, θ := l.rat.In.θ, Bs := l.b.Bs,
      M := l.mt.M, C := l.c.ch, tp := l.c.tp, ch := l.c.side, mt := hmt, big := big, L := L, Sp := Sp, Au := Au, ss := ss,
      eq := rfl, pack := rfl }
  have hval : ValLL0 (withLoc L) (cfL L (cfOf x)) :=
    ⟨l.a.val.mu0, l.a.val.eta, l.a.val.chiPsi, l.a.val.del, l.a.val.del'⟩
  obtain ⟨Q, -, -, -, -, h5⟩ := GlobalTheory.NPin.pin_of_nTrue hL _ _ _ _ nt hval
    (fun σ σ' h => x.r.Y.eFT.injective (Formalism.IndefR.principalLevelFrame.rowRepR_inj _ _ _ h)) l.a.elem.star l.a.elem.int l.a.elem.split
    (GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb _)
  exact ⟨Q, eq_of_heq h5⟩

set_option maxHeartbeats 2000000 in

theorem labTie_withLoc {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
    (x : St P) (Lc : LocAll (lay0 (Dof x))) :
    GlobalTheory.SerSys.LabTie (withLoc Lc) fun k => GlobalTheory.Mem.TypePl.labDat ((withLoc Lc).host.g k) :=
  fun k => ⟨(x.fits.grp.teich k).symm, x.fits.grp.ser k⟩

set_option maxHeartbeats 2000000 in

theorem tame_withLoc {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} (x : St P) (l : LC hL x) (Lc : LocAll (lay0 (Dof x))) :
    ∀ k v, ∃ κ : IsLocalRing.ResidueField ((withLoc Lc).nd.plOm.1 ((withLoc Lc).naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar ((withLoc Lc).host.g k),
      Formalism.L2.NT.TameCoupled ((withLoc Lc).nd.plOm.1 ((withLoc Lc).naut.plGw k v)) κ ((withLoc Lc).ntypes.tg k v)
        (GlobalTheory.Mem.TypePl.labDat ((withLoc Lc).host.g k)).gen :=
  fun k v => ⟨l.a.A.grp.kv k v, by
    have h := l.a.A.grp.tg_tame k v
    rw [l.a.zeta k] at h
    exact h⟩

set_option maxHeartbeats 4000000 in

theorem main : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, PrN → AllSt fun _ _ _ _ _ _ x =>
    ∀ l : LC hL x, GlobalTheory.CoefDuty.EvO l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → GlobalTheory.TypeLeaf.SerLoc D' := by
  intro hL hP
  refine StepW.of_all ?_
  intro K B f T w _ _ _ P x l
  refine ⟨fun _ => ∅, fun Lc hB _ => ?_⟩
  obtain ⟨Pn, hM⟩ := pin_withLoc hL hP x l _ Lc hB
  exact GlobalTheory.SerSys.Assembly.serLoc_concrete hP.what₂ hP.green hP.zel hP.dz hL (withLoc Lc) Pn _ (labTie_withLoc x Lc) (tame_withLoc x l Lc)
    (hM ▸ cenLoc_third x l Lc)

end GlobalTheory.SerThird

end
