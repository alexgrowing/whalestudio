import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountP
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PcIntGen

noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Tau1Cut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def ZZOrbT : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w → ∀ p,
    ∃ l ρ l' ρ' : MatP D p, TieN.IntLow (Zd.M p) l ∧ TieN.IntUp (Zd.M p) ρ ∧ TieN.IntLow (Zd.M p) l' ∧
      TieN.IntUp (Zd.M p) ρ' ∧
      (locH Zd p).ZZplus (tLoc Zd p γ) = l * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (zT γ) * LsDatumB.sgnP p) * ρ ∧
      CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (zT γ) * LsDatumB.sgnP p = l' * (locH Zd p).ZZplus (tLoc Zd p γ) * ρ'

def ClsSgn : Prop :=
  ∀ (p : PlF D) (Y : MatP D p) (s : (D.s.atP p).Ep),
    clsOf (Zd.M p) (Y * LsDatumB.sgnP p + cornE p s) = clsOf (Zd.M p) (Y + cornE p s)

variable {Zd u u' F0 what₂}

theorem ptT_eq (hN : PairVal.NormRepExists D u u' F0 what₂) (hrows : IsRowReps D F0 what₂)
    {γ : TermDef.Term D u u' F0 what₂} {w : Point D.host.E (D.R.rS + 1)} (hγ : EligAt γ w) : ptT γ = w := by
  have hrel := eligRel_holds γ w hγ
  obtain ⟨⟨hgen, -⟩, hat⟩ := hγ
  obtain ⟨y, hy⟩ := hN γ w hat hrel hgen
  have hex : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 := ⟨(w, y), hy⟩
  have hn : nrep γ = some hex.choose := dif_pos hex
  obtain ⟨hRep, -, hL, hU, e⟩ := hex.choose_spec
  obtain ⟨F₁, hR₁, -, hc₁⟩ := hat
  have hw : w = hex.choose.1 := pt_eq_of_cells cell_point_uniqueness (Formalism.L2.SG.Closed.TermFun_holds D u u') hrows γ
    hR₁ hRep hc₁ ⟨_, _, hL, hU, e⟩
  unfold ptT; rw [hn, hw]

theorem tauOne_of_orbit_and_sign (hN : PairVal.NormRepExists D u u' F0 what₂) (hrows : IsRowReps D F0 what₂)
    (hZ : ZZOrbT Zd u u' F0 what₂) (hS : ClsSgn Zd) : Tau1 Zd u u' F0 what₂ := by
  intro γ w hγ p
  have hpt := ptT_eq hN hrows hγ
  obtain ⟨l, ρ, l', ρ', hl, hρ, hl', hρ', e1, e2⟩ := hZ γ w hγ p
  unfold thT thL
  rw [hpt]
  show clsOf (Zd.M p) (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (zT γ) +
      cornE p (cornerSh Zd.δ (D.mem u).A.T (D.mem u').A.T p w)) = _
  rw [← hS p, clsOf_orb hl hρ hl' hρ' e1 e2]

theorem tauOne_of_orbit_sign (hZ : CtxP u u' F0 what₂ → ZZOrbT Zd u u' F0 what₂) (hS : ClsSgn Zd) : TauOneReduction Zd u u' F0 what₂ :=
  fun h => tauOne_of_orbit_and_sign (normRepExists_ctx h) h.2.1 (hZ h) hS

end Tau1Cut

section SgnCls

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}

theorem permSign_mul_self₂ (p : PlF D) : LsDatumB.sgnP p * LsDatumB.sgnP p = (1 : MatP D p) := by
  unfold LsDatumB.sgnP
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

theorem sgnP_mem (p : PlF D) (a b : Fin (D.R.rS + 1)) : LsDatumB.sgnP p a b ∈ (M p).R := by
  unfold LsDatumB.sgnP
  rw [Matrix.diagonal_apply]
  split_ifs
  · exact pow_mem (neg_mem (one_mem _)) _
  · exact zero_mem _

theorem clsOf_mul_sgn (p : PlF D) (Y : MatP D p) :
    clsOf (M p) (Y * LsDatumB.sgnP p) = clsOf (M p) Y := by
  set S := LsDatumB.sgnP (D := D) p with hSdef
  have hSS : S * S = 1 := permSign_mul_self₂ p
  have hSu : IsUnit S.det := Matrix.isUnit_det_of_right_inverse hSS
  have hYS : Y * S * S = Y := by rw [Matrix.mul_assoc, hSS, Matrix.mul_one]
  have hSR : ∀ a b, S a b ∈ (M p).R := sgnP_mem (M := M) p
  have key0 : ∀ X : MatP D p, (∀ a b, X a b ∈ (M p).R) → ∀ a b, (X * S) a b ∈ (M p).R := by
    intro X hX a b
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun c _ => mul_mem (hX a c) (hSR c b)
  have hint : (∀ a b, (Y * S) a b ∈ (M p).R) ↔ (∀ a b, Y a b ∈ (M p).R) :=
    ⟨fun h => hYS ▸ key0 _ h, key0 Y⟩
  have hdet : IsUnit (Y * S).det ↔ IsUnit Y.det := by
    rw [Matrix.det_mul, IsUnit.mul_iff]; exact ⟨And.left, fun h => ⟨h, hSu⟩⟩
  unfold clsOf
  by_cases hc : (∀ a b, Y a b ∈ (M p).R) ∧ IsUnit Y.det
  · have hc' : (∀ a b, (Y * S) a b ∈ (M p).R) ∧ IsUnit (Y * S).det := ⟨hint.2 hc.1, hdet.2 hc.2⟩
    rw [dif_pos hc, dif_pos hc']
    congr 1
    apply Eq.symm
    apply Quotient.sound
    have hSS' : toR (M := M) S hSR * toR S hSR = 1 := by
      apply Matrix.map_injective (f := ((M p).R.subtype : (M p).R → _)) Subtype.val_injective
      dsimp only
      rw [Matrix.map_mul, toR_map, hSS, Matrix.map_one _ (map_zero _) (map_one _)]
    have hρu : IsUnit (toR (M := M) S hSR).det := Matrix.isUnit_det_of_right_inverse hSS'
    have hinv : ((toR (M := M) S hSR).map (M p).R.subtype)⁻¹ = S := by
      rw [toR_map]; exact Matrix.inv_eq_left_inv hSS
    have hρe : ∀ b, ((toR (M := M) S hSR).map (M p).R.subtype)⁻¹ (Fin.last D.R.rS) b =
        if b = Fin.last D.R.rS then 1 else 0 := by
      intro b
      rw [hinv, hSdef]
      unfold LsDatumB.sgnP
      rw [Matrix.diagonal_apply]
      by_cases hb : b = Fin.last D.R.rS
      · subst hb; simp
      · rw [if_neg (Ne.symm hb), if_neg hb]
    refine ⟨?_⟩
    have key := isoLR (M p) ⟨Matrix.of fun a b => ⟨Y a b, hc.1 a b⟩, by
        have : (Matrix.of fun a b => (⟨Y a b, hc.1 a b⟩ : (M p).R)).map (M p).R.subtype = Y := rfl
        rw [this]; exact hc.2⟩ 1 (toR S hSR) (by rw [Matrix.det_one]; exact isUnit_one) hρu
      (Matrix.one_mulVec _) hρe
    have hZ : (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (M p).R) * toR (M := M) Y hc.1 * toR S hSR =
        toR (Y * S) hc'.1 := by
      apply Matrix.map_injective (f := ((M p).R.subtype : (M p).R → _)) Subtype.val_injective
      dsimp only
      rw [Matrix.map_mul, Matrix.map_mul, toR_map, toR_map, toR_map, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.one_mul]
    refine cast ?_ key
    congr 1
    unfold matLR
    congr 1
  · have hc' : ¬ ((∀ a b, (Y * S) a b ∈ (M p).R) ∧ IsUnit (Y * S).det) := by
      rintro ⟨h1', h2'⟩; exact hc ⟨hint.1 h1', hdet.1 h2'⟩
    rw [dif_neg hc, dif_neg hc']

theorem clsSgn_holds (Zd : LocDat D) : ClsSgn Zd := by
  intro p Y s
  have h : Y * LsDatumB.sgnP p + cornE p s = (Y + cornE p s) * LsDatumB.sgnP p := by
    rw [Matrix.add_mul]
    congr 1
    ext a b
    simp only [cornE, LsDatumB.sgnP, Matrix.mul_diagonal, Matrix.of_apply]
    split_ifs with hab
    · obtain ⟨-, rfl⟩ := hab; simp
    · simp
  rw [h, clsOf_mul_sgn]

end SgnCls

theorem tauOne_of_orbit {D : Formalism.BasicNotions.D7} {Zd : LocDat D} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (hZ : CtxP u u' F0 what₂ → ZZOrbT Zd u u' F0 what₂) :
    TauOneReduction Zd u u' F0 what₂ :=
  tauOne_of_orbit_sign hZ (clsSgn_holds Zd)

section InvR

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {n : ℕ}

theorem det_mem_R (A : Matrix (Fin n) (Fin n) E) (h : ∀ i j, A i j ∈ M.R) : A.det ∈ M.R := by
  rw [Matrix.det_apply]
  refine Subring.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (Subring.prod_mem _ fun i _ => h _ _) _

theorem adj_mem_R (A : Matrix (Fin n) (Fin n) E) (h : ∀ i j, A i j ∈ M.R) (a b : Fin n) :
    A.adjugate a b ∈ M.R := by
  rw [Matrix.adjugate_apply]
  refine det_mem_R _ fun i j => ?_
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · exact h _ _

theorem intUp_inv {ρ : Matrix (Fin n) (Fin n) E} (h : TieN.IntUp M ρ) : TieN.IntUp M ρ⁻¹ := by
  have hU : IsUp ρ := ⟨h.1, fun a b hab => h.2.1 b a hab⟩
  have hi := isUp_inv hU
  refine ⟨hi.1, fun a b hab => hi.2 b a hab, fun a b => ?_⟩
  rw [Matrix.inv_def, det_up' hU, Ring.inverse_one, one_smul]
  exact adj_mem_R _ h.2.2 a b

theorem intLow_inv {l : Matrix (Fin n) (Fin n) E} (h : TieN.IntLow M l) : TieN.IntLow M l⁻¹ := by
  have hL : IsLo l := ⟨h.1, h.2.1⟩
  have hi := isLo_inv hL
  refine ⟨hi.1, hi.2, fun a b => ?_⟩
  rw [Matrix.inv_def, det_lo' hL, Ring.inverse_one, one_smul]
  exact adj_mem_R _ h.2.2 a b

end InvR

section SplitAlg

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {r : ℕ}

theorem zzPlus_first_projection {g : Loc.SplitG M.L} (hM : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (Loc.HermSp.ZZplusOf M Zh T T').map (p1 g.e) =
      (g.q : F)⁻¹ • Zh.map (p1 g.e) + (T / (g.q : F)) • (Ecorner r : Matrix (Fin (r + 1)) (Fin (r + 1)) F) := by
  ext a b
  simp only [Loc.HermSp.ZZplusOf, hM, Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Ecorner, map_sub, fst_proj_symm, apply_ite (p1 g.e)]
  split_ifs <;> simp only [fst_proj_symm, map_zero, adeleInfiniteComponent_apply] <;> ring

theorem zzPlus_second_projection {g : Loc.SplitG M.L} (hM : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (Loc.HermSp.ZZplusOf M Zh T T').map (p2 g.e) =
      -((g.q : F)⁻¹ • (Zh.map (p2 g.e)).transpose) -
        (T' / (g.q : F)) • (Ecorner r : Matrix (Fin (r + 1)) (Fin (r + 1)) F) := by
  ext a b
  simp only [Loc.HermSp.ZZplusOf, hM, Matrix.map_apply, Matrix.of_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, Ecorner, map_sub, snd_proj_symm, apply_ite (p2 g.e)]
  split_ifs <;> simp only [snd_proj_symm, map_zero, adele_ext_components] <;> ring

theorem zzplusOf_mul_up {g : Loc.SplitG M.L} (hM : M.split = some g) (Zh V : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (T T' : F) (hV : IsUp V) :
    Loc.HermSp.ZZplusOf M (Zh * V) T T' =
      glue g.e 1 (V.map (p2 g.e)).transpose * Loc.HermSp.ZZplusOf M Zh T T' * glue g.e (V.map (p1 g.e)) 1 := by
  have hV1 : IsUp (V.map (p1 g.e)) := isUp_map (p1 g.e) hV
  have hV2 : IsLo (V.map (p2 g.e)).transpose := isLo_transpose (isUp_map (p2 g.e) hV)
  have h1L : IsLo (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) F) :=
    ⟨fun a => Matrix.one_apply_eq a, fun a b h => Matrix.one_apply_ne (ne_of_lt h)⟩
  have h1U : IsUp (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) F) :=
    ⟨fun a => Matrix.one_apply_eq a, fun a b h => Matrix.one_apply_ne (ne_of_gt h)⟩
  have c1 : (Ecorner r : Matrix (Fin (r + 1)) (Fin (r + 1)) F) * V.map (p1 g.e) = Ecorner r := by
    have := lo_corner_up h1L hV1; rwa [Matrix.one_mul] at this
  have c2 : (V.map (p2 g.e)).transpose * (Ecorner r : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = Ecorner r := by
    have := lo_corner_up hV2 h1U; rwa [Matrix.mul_one] at this
  apply mat_eq g.e
  · rw [Matrix.map_mul, Matrix.map_mul, glue_map_fst, glue_map_fst, zzPlus_first_projection hM, zzPlus_first_projection hM, Matrix.one_mul, Matrix.map_mul,
      Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, c1]
  · rw [Matrix.map_mul, Matrix.map_mul, glue_map_snd, glue_map_snd, zzPlus_second_projection hM, zzPlus_second_projection hM, Matrix.mul_one, Matrix.map_mul,
      Matrix.transpose_mul, Matrix.mul_sub, Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_smul, c2]

end SplitAlg

section VcDef

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def cInv (Zd : LocDat D) (p : PlF D) (k : Fin (D.R.rS + 1)) : (D.s.atP p).Ep :=
  TermLoc.sgnP' D p k * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (yP Zd p ^ (D.R.rS - k.val))

theorem c_cInv (Zd : LocDat D) (p : PlF D) (k : Fin (D.R.rS + 1)) :
    (TermLoc.sgnP' D p k * frFac Zd.δ p k) * cInv Zd p k = 1 := by
  have hs := TermLoc.sgnP'_sq (D := D) p k
  have hy : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((yP Zd p)⁻¹ ^ (D.R.rS - k.val)) *
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (yP Zd p ^ (D.R.rS - k.val)) = 1 := by
    rw [← map_mul, ← mul_pow, inv_mul_cancel₀ (yP_ne Zd p), one_pow, map_one]
  rw [cInv, frFac_eq]
  linear_combination (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((yP Zd p)⁻¹ ^ (D.R.rS - k.val)) *
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (yP Zd p ^ (D.R.rS - k.val))) * hs + hy

def vc (Zd : LocDat D) (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) : MatP D p :=
  Matrix.of fun k b => (TermLoc.sgnP' D p b * frFac Zd.δ p b) * cInv Zd p k *
    (D.s.atP p).ιE ((((admXi D γ.lam (lf D F0) (repF γ))⁻¹).map (algebraMap (𝓞 D.host.E) D.host.E)) k b)

theorem zhat_vc (Zd : LocDat D) (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) :
    (locH Zd p).Zhat (tLoc Zd p γ).f (tLoc Zd p γ).f' =
      (locH Zd p).Zhat (tLoc Zd p γ).f (locF' Zd p (repF γ)) * vc Zd p γ := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [tLoc]
  rw [zhat_loc, Matrix.mul_apply, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [zhat_locF', vc, Matrix.of_apply, map_mul (D.s.atP p).ιE]
  linear_combination (-((TermLoc.sgnP' D p b * frFac Zd.δ p b) *
    (D.s.atP p).cj (TermLoc.sgnP D p a * frFac Zd.δ p a) * (D.s.atP p).ιE (ZhatL (lf D F0) (repF γ) a k) *
    (D.s.atP p).ιE ((((admXi D γ.lam (lf D F0) (repF γ))⁻¹).map (algebraMap (𝓞 D.host.E) D.host.E)) k b))) *
    c_cInv Zd p k

theorem vc_up (Zd : LocDat D) (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) : IsUp (vc Zd p γ) := by
  obtain ⟨h0, h1⟩ := inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2
  refine ⟨fun k => ?_, fun k b hkb => ?_⟩
  · simp only [vc, Matrix.of_apply, Matrix.map_apply, h1 k, map_one, mul_one]
    exact c_cInv Zd p k
  · simp only [vc, Matrix.of_apply, Matrix.map_apply, h0 b k hkb, map_zero, mul_zero]

end VcDef

section VcCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def VolumeConstantAgreement : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w → ∀ p,
    match (Zd.M p).split with
    | none => ∀ k b, vc Zd p γ k b ∈ (Zd.M p).R
    | some g => ∀ k b, k ≠ b →
        (∃ x ∈ 𝒪[(D.s.atP p).Fp], p1 g.e (vc Zd p γ k b) = (g.q : (D.s.atP p).Fp) * x) ∧
        (∃ x ∈ 𝒪[(D.s.atP p).Fp], p2 g.e (vc Zd p γ k b) = (g.q : (D.s.atP p).Fp) * x)

variable {Zd u u' F0 what₂}

theorem zzOrbT_of (hN : PairVal.NormRepExists D u u' F0 what₂) (hrows : IsRowReps D F0 what₂)
    (hV : VolumeConstantAgreement Zd u u' F0 what₂) : ZZOrbT Zd u u' F0 what₂ := by
  intro γ w hγ p
  have hz : zT γ = ZhatL (lf D F0) (repF γ) := (repF_cell hN hrows hγ).1
  have hX : Loc.HermSp.ZZplusOf (Zd.M p) ((locH Zd p).Zhat (tLoc Zd p γ).f (locF' Zd p (repF γ)))
      (tLoc Zd p γ).T (tLoc Zd p γ).T' = CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (zT γ) * LsDatumB.sgnP p := by
    rw [hz]; exact zzplus_locF' Zd u u' p γ.lam (lf D F0) (repF γ) (repF γ) ⊥
  have hY : (locH Zd p).ZZplus (tLoc Zd p γ) = Loc.HermSp.ZZplusOf (Zd.M p)
      ((locH Zd p).Zhat (tLoc Zd p γ).f (locF' Zd p (repF γ)) * vc Zd p γ) (tLoc Zd p γ).T (tLoc Zd p γ).T' := by
    unfold Loc.HermSp.ZZplus; rw [zhat_vc]
  have hup := vc_up Zd p γ
  have hVp := hV γ w hγ p
  rw [hY, ← hX]
  generalize (locH Zd p).Zhat (tLoc Zd p γ).f (locF' Zd p (repF γ)) = Zh
  generalize (tLoc Zd p γ).T = T
  generalize (tLoc Zd p γ).T' = T'
  generalize vc Zd p γ = V at hup hVp
  rcases hM : (Zd.M p).split with _ | g
  · simp only [hM] at hVp
    have hρ : TieN.IntUp (Zd.M p) V := ⟨hup.1, fun a b hab => hup.2 b a hab, hVp⟩
    have e : ∀ Y : MatP D p, Loc.HermSp.ZZplusOf (Zd.M p) Y T T' = Y := fun Y => by
      simp only [Loc.HermSp.ZZplusOf, hM]
    rw [e, e]
    refine ⟨1, V, 1, V⁻¹, intLow_one p, hρ, intLow_one p, intUp_inv hρ, by rw [Matrix.one_mul], ?_⟩
    rw [Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (by rw [det_up' hup]; exact isUnit_one),
      Matrix.mul_one]
  · simp only [hM] at hVp
    have key := zzplusOf_mul_up hM Zh V T T' hup
    have hV2 : IsLo (V.map (p2 g.e)).transpose := isLo_transpose (isUp_map (p2 g.e) hup)
    have h1L : IsLo (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Fp) :=
      ⟨fun a => Matrix.one_apply_eq a, fun a b h => Matrix.one_apply_ne (ne_of_lt h)⟩
    have h1U : IsUp (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Fp) :=
      ⟨fun a => Matrix.one_apply_eq a, fun a b h => Matrix.one_apply_ne (ne_of_gt h)⟩
    have hLlo := isLo_glue g.e h1L hV2
    have hUup := isUp_glue g.e (isUp_map (p1 g.e) hup) h1U
    have hLi : TieN.IntLow (Zd.M p) (glue g.e 1 (V.map (p2 g.e)).transpose) := by
      refine ⟨hLlo.1, hLlo.2, fun a b => ?_⟩
      rw [IntegralGeneration.mem_R_of_split hM]
      simp only [glue, Matrix.of_apply, AlgEquiv.apply_symm_apply, Matrix.transpose_apply, Matrix.map_apply]
      by_cases hab : a = b
      · subst hab
        rw [Matrix.one_apply_eq, hup.1 a, map_one]
        exact ⟨one_mem _, one_mem _, 0, zero_mem _, by ring⟩
      · obtain ⟨x, hx, hxe⟩ := (hVp b a (Ne.symm hab)).2
        rw [Matrix.one_apply_ne hab, hxe]
        exact ⟨zero_mem _, mul_mem g.q.2 hx, -x, neg_mem hx, by ring⟩
    have hUi : TieN.IntUp (Zd.M p) (glue g.e (V.map (p1 g.e)) 1) := by
      refine ⟨hUup.1, fun a b hab => hUup.2 b a hab, fun a b => ?_⟩
      rw [IntegralGeneration.mem_R_of_split hM]
      simp only [glue, Matrix.of_apply, AlgEquiv.apply_symm_apply, Matrix.map_apply]
      by_cases hab : a = b
      · subst hab
        rw [Matrix.one_apply_eq, hup.1 a, map_one]
        exact ⟨one_mem _, one_mem _, 0, zero_mem _, by ring⟩
      · obtain ⟨x, hx, hxe⟩ := (hVp a b hab).1
        rw [Matrix.one_apply_ne hab, hxe]
        exact ⟨mul_mem g.q.2 hx, zero_mem _, x, hx, by ring⟩
    have hLu : IsUnit (glue g.e 1 (V.map (p2 g.e)).transpose).det := by rw [det_lo' hLlo]; exact isUnit_one
    have hUu : IsUnit (glue g.e (V.map (p1 g.e)) 1).det := by rw [det_up' hUup]; exact isUnit_one
    refine ⟨_, _, _, _, hLi, hUi, intLow_inv hLi, intUp_inv hUi, key, ?_⟩
    rw [key]
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hLu, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hUu, Matrix.mul_one]

theorem tauOne_of_vector (hV : CtxP u u' F0 what₂ → VolumeConstantAgreement Zd u u' F0 what₂) : TauOneReduction Zd u u' F0 what₂ :=
  tauOne_of_orbit fun h => zzOrbT_of (normRepExists_ctx h) h.2.1 (hV h)

end VcCut

section XiCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def XiTyped : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    ∀ (p : PlF D) (g : Loc.SplitG (Zd.M p).L), (Zd.M p).split = some g → ∀ k b : Fin (D.R.rS + 1), k < b →
      (∃ x ∈ 𝒪[(D.s.atP p).Fp], p1 g.e ((D.s.atP p).ιE ((((admXi D γ.lam (lf D F0) (repF γ))⁻¹).map
          (algebraMap (𝓞 D.host.E) D.host.E)) k b)) = (g.q : (D.s.atP p).Fp) * x) ∧
      (∃ x ∈ 𝒪[(D.s.atP p).Fp], p2 g.e ((D.s.atP p).ιE ((((admXi D γ.lam (lf D F0) (repF γ))⁻¹).map
          (algebraMap (𝓞 D.host.E) D.host.E)) k b)) = (g.q : (D.s.atP p).Fp) * x)

variable (D) in

def UInt : Prop := ∀ p : PlF D, (D.s.atP p).ιF ((uP p : ℚ) : D.host.F) ∈ 𝒪[(D.s.atP p).Fp]

variable {Zd u u' F0 what₂}

theorem sc_mem (hU : UInt D) (p : PlF D) {k b : Fin (D.R.rS + 1)} (hkb : k ≤ b) :
    (TermLoc.sgnP' D p b * frFac Zd.δ p b) * cInv Zd p k ∈ (Zd.M p).L.O := by
  have hy : yP Zd p ∈ 𝒪[(D.s.atP p).Fp] := mul_mem (LocModel.LM.delta_mem (Zd.agree p)) (hU p)
  have hsg : ∀ c, TermLoc.sgnP' D p c ∈ (Zd.M p).L.O := fun c =>
    Formalism.MainNotions.LocalModelPeriodLattices.mem_O_of_quad (Zd.M p).L _ 0 (-1) (by
      have := TermLoc.sgnP'_sq (D := D) p c
      simp [this])
  have hexp : D.R.rS - k.val = (D.R.rS - b.val) + (b.val - k.val) := by
    have h1 := b.isLt; have h2 : k.val ≤ b.val := hkb; omega
  have e : (TermLoc.sgnP' D p b * frFac Zd.δ p b) * cInv Zd p k =
      (TermLoc.sgnP' D p b * TermLoc.sgnP' D p k) *
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (yP Zd p ^ (b.val - k.val)) := by
    have hpow : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((yP Zd p)⁻¹ ^ (D.R.rS - b.val)) *
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (yP Zd p ^ (D.R.rS - k.val)) =
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (yP Zd p ^ (b.val - k.val)) := by
      rw [← map_mul, hexp, pow_add, ← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ (yP_ne Zd p)), one_mul]
    rw [cInv, frFac_eq]
    linear_combination (TermLoc.sgnP' D p b * TermLoc.sgnP' D p k) * hpow
  rw [e]
  exact mul_mem (mul_mem (hsg b) (hsg k)) (Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O (Zd.M p).L ⟨_, pow_mem hy _⟩)

theorem vcTied_of (hX : XiTyped Zd u u' F0 what₂) (hU : UInt D) : VolumeConstantAgreement Zd u u' F0 what₂ := by
  intro γ w hγ p
  have hO : (Zd.M p).L.O = (D.s.atP p).O := (Zd.agree p).2.2.2.1
  obtain ⟨h0, -⟩ := inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2
  have hzero : ∀ k b : Fin (D.R.rS + 1), b < k → vc Zd p γ k b = 0 := fun k b h => by
    simp only [vc, Matrix.of_apply, Matrix.map_apply, h0 k b h, map_zero, mul_zero]
  have hsplit : ∀ k b : Fin (D.R.rS + 1), vc Zd p γ k b = ((TermLoc.sgnP' D p b * frFac Zd.δ p b) * cInv Zd p k) *
      (D.s.atP p).ιE ((((admXi D γ.lam (lf D F0) (repF γ))⁻¹).map (algebraMap (𝓞 D.host.E) D.host.E)) k b) :=
    fun k b => rfl
  have hint : ∀ k b : Fin (D.R.rS + 1), (D.s.atP p).ιE ((((admXi D γ.lam (lf D F0) (repF γ))⁻¹).map
      (algebraMap (𝓞 D.host.E) D.host.E)) k b) ∈ (Zd.M p).L.O := fun k b => by
    rw [hO, Matrix.map_apply]; exact LocModel.LM.ιE_int_mem_O p _
  rcases hM : (Zd.M p).split with _ | g
  · intro k b
    have hR : (Zd.M p).R = (Zd.M p).L.O := by simp only [Loc.Model.R, hM]
    rw [hR]
    rcases le_or_gt k b with hkb | hkb
    · rw [hsplit]; exact mul_mem (sc_mem hU p hkb) (hint k b)
    · rw [hzero k b hkb]; exact zero_mem _
  · intro k b hne
    rcases lt_or_gt_of_ne hne with hkb | hkb
    · obtain ⟨⟨x, hx, hxe⟩, ⟨x', hx', hxe'⟩⟩ := hX γ w hγ p g hM k b hkb
      have hs := sc_mem (Zd := Zd) hU p (le_of_lt hkb)
      refine ⟨⟨p1 g.e ((TermLoc.sgnP' D p b * frFac Zd.δ p b) * cInv Zd p k) * x,
        mul_mem (IntegralGeneration.fst_mem (g := g) hs) hx, ?_⟩,
        ⟨p2 g.e ((TermLoc.sgnP' D p b * frFac Zd.δ p b) * cInv Zd p k) * x',
        mul_mem (IntegralGeneration.snd_mem (g := g) hs) hx', ?_⟩⟩
      · rw [hsplit, map_mul, hxe]; ring
      · rw [hsplit, map_mul, hxe']; ring
    · rw [hzero k b hkb, map_zero, map_zero]
      exact ⟨⟨0, zero_mem _, by ring⟩, ⟨0, zero_mem _, by ring⟩⟩

theorem tauOne_of_xi (hX : CtxP u u' F0 what₂ → XiTyped Zd u u' F0 what₂) (hU : UInt D) : TauOneReduction Zd u u' F0 what₂ :=
  tauOne_of_vector fun h => vcTied_of (hX h) hU

end XiCut

section UIntPf

variable {D : Formalism.BasicNotions.D7}

theorem natPrime_notMem (p : PlF D) {l : ℕ} (hl : l.Prime) (hne : l ≠ Loc.resChar p) :
    ((l : ℤ) : 𝓞 D.host.F) ∉ p.asIdeal := by
  intro h
  haveI := p.isPrime
  have h0 : ((l : ℕ) : 𝓞 D.host.F ⧸ p.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]; exact_mod_cast h
  have hd := ringChar.dvd h0
  rcases hl.eq_one_or_self_of_dvd _ hd with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · exact hne (by unfold Loc.resChar; exact h1.symm)

theorem uInt_holds : UInt D := by
  intro p
  have h0 := D.host.g_prime 0
  have h1 := D.host.g_prime 1
  have hne := D.host.g_ne
  have h0q : ((D.host.g 0 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast h0.ne_zero
  have h1q : ((D.host.g 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast h1.ne_zero
  have key : ∀ n : ℤ, (n : 𝓞 D.host.F) ∉ p.asIdeal →
      (D.s.atP p).ιF ((((n : ℚ))⁻¹ : ℚ) : D.host.F) ∈ 𝒪[(D.s.atP p).Fp] := by
    intro n hn
    rw [Rat.cast_inv, map_inv₀, Rat.cast_intCast]
    exact LocModel.LM.inv_intCast_mem p n hn
  unfold uP gpart Lat.gS
  split_ifs with ha hb
  · have e : (((D.host.g 0 : ℕ) : ℚ)) / (((D.host.g 0 * D.host.g 1 : ℕ)) : ℚ) =
        ((((D.host.g 1 : ℕ) : ℤ) : ℚ))⁻¹ := by
      push_cast; field_simp
    rw [e]
    exact key _ (natPrime_notMem p h1 (by rw [ha]; exact Ne.symm hne))
  · have e : (((D.host.g 1 : ℕ) : ℚ)) / (((D.host.g 0 * D.host.g 1 : ℕ)) : ℚ) =
        ((((D.host.g 0 : ℕ) : ℤ) : ℚ))⁻¹ := by
      push_cast; field_simp
    rw [e]
    exact key _ (natPrime_notMem p h0 (by rw [hb]; exact hne))
  · have e : (((1 : ℕ) : ℚ)) / (((D.host.g 0 * D.host.g 1 : ℕ)) : ℚ) =
        ((((D.host.g 0 * D.host.g 1 : ℕ) : ℤ) : ℚ))⁻¹ := by
      push_cast; field_simp
    rw [e]
    refine key _ fun hm => ?_
    haveI := p.isPrime
    push_cast at hm
    rcases p.isPrime.mem_or_mem hm with hm | hm
    · exact natPrime_notMem p h0 (Ne.symm ha) (by exact_mod_cast hm)
    · exact natPrime_notMem p h1 (Ne.symm hb) (by exact_mod_cast hm)

theorem tauOne_of_typed {Zd : LocDat D} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (hX : CtxP u u' F0 what₂ → XiTyped Zd u u' F0 what₂) :
    TauOneReduction Zd u u' F0 what₂ :=
  tauOne_of_xi hX uInt_holds

end UIntPf

end Formalism.L2.SG.Pf.PCount
