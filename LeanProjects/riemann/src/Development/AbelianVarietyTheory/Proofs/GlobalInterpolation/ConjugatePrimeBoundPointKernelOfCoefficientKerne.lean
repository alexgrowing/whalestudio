import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainSharpColumnValuationOfPointKernelLiftL

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

noncomputable section

namespace GlobalTheory.LvT.Built.BarPass

variable {D : D7} {u : D.what₂.Word}

theorem valB_smul_eq {X : Ch D u} {i : ℕ} {M : PtModel X i} (Co : M.Coord) (w : D.what₂.places.Pl) (V : Finset X.A.vT)
    (g : M.G) (hg : ∀ v, M.loc v g = 1) (p : M.Pt) : Co.valB w V (g • p) = Co.valB w V p := by
  have h : ∀ v, (g • p).2 v = p.2 v := by
    intro v
    have h1 := M.smul_snd g p v
    rw [hg v] at h1
    apply Subtype.ext
    apply LocF.Raw.ext
    · ext x
      simpa using (h1 x).1
    · funext x
      simpa using (h1 x).2
  unfold PtModel.Coord.valB
  simp only [h]

variable {B : Built.Dat D u} {i : ℕ}

theorem ev_smul (c : D.what₂.LL) (F : B.V i) : B.ev i (c • F) = D.what₂.embLL c • B.ev i F :=
  LinearMap.map_smulₛₗ (evV B.emb (1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) B.E) (B.lam i) D.what₂.embLL) c F

theorem isIntegral_torsion {L : Type} [Field L] (ζ : CommGroup.torsion Lˣ) : IsIntegral ℤ ((ζ.1 : Lˣ) : L) := by
  obtain ⟨n, hn, h⟩ := (isOfFinOrder_iff_pow_eq_one).1 ((CommGroup.mem_torsion _).1 ζ.2)
  refine IsIntegral.of_pow hn ?_
  rw [← Units.val_pow_eq_pow_val, h]
  exact isIntegral_one

theorem act_zeta_mem {sp : Split (B.J.A i) B.J.T} {M : PtModel B.ch i} (R : B.Real i sp M) {Co : M.Coord}
    (hV : R.ValIs Co) {w : D.what₂.places.Pl} (hw : OverT B.ch w) (b) (d : (B.I.S i).D b) (ζ) (y : M.Val)
    (hy : y ∈ Co.valB w ∅ (R.pt b d)) : M.act (R.zeta ζ) y ∈ Co.valB w ∅ (R.pt b d) := by
  obtain ⟨F, hF, hyF⟩ := (hV.dual w hw b d y).1 hy
  refine (hV.dual w hw b d _).2 ⟨((ζ.1 : (D.what₂.LL)ˣ) : D.what₂.LL) • F, ?_, ?_⟩
  · exact (B.valAt w i _).smul_mem (⟨_, isIntegral_torsion ζ⟩ : 𝓞 D.what₂.LL) hF
  · rw [R.act_zeta, ev_smul, ← hyF]
    rfl

theorem intBar_of_kerBar : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (Co : M.Coord) (Co' : M'.Coord) (K : KerPt M M'), K.TgtEq → Built.Dat.KerIs R R' K k → Co.Ok → Co'.Ok → R.ValIs Co → R'.ValIs Co' → Built.Dat.KerBar k → K.IntBar Co Co' := by
  intro D u B i sp sp' M M' R R' k Co Co' K hT hK _ _ hV hV' hb w hw hs p p' y hy
  obtain ⟨ζ, b, d, rfl⟩ := R.surj p
  obtain ⟨ζ', b', d', rfl⟩ := R'.surj p'
  rw [valB_smul_eq Co w ∅ _ (R.loc_zeta ζ)] at hy
  rw [valB_smul_eq Co' w ∅ _ (R'.loc_zeta ζ')]
  have hy0 := act_zeta_mem R hV hw b d ζ⁻¹ y hy
  have hyy : y = M.act (R.zeta ζ) (M.act (R.zeta ζ⁻¹) y) := by
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, Module.End.one_apply]
  generalize M.act (R.zeta ζ⁻¹) y = y₀ at hy0 hyy
  obtain ⟨F, hF, hyF⟩ := (hV.dual w hw b d y₀).1 hy0
  obtain ⟨F', hF', hk⟩ := hb w hw hs b b' d d' F hF
  have hm : B.ev (i + 1) F' ∈ M'.Val := by
    rw [R'.val_eq]
    exact evV_mem_ValC B.emb 1 _ D.what₂.embLL F'
  have h1 : (⟨_, hm⟩ : M'.Val) ∈ Co'.valB w ∅ (R'.pt b' d') := (hV'.dual w hw b' d' _).2 ⟨F', hF', rfl⟩
  refine ⟨_, act_zeta_mem R' hV' hw b' d' ζ' _ h1, ?_⟩
  rw [hyy, K.src, hT, ← map_smul]
  congr 1
  apply Subtype.ext
  rw [hK b b' d d' F y₀ hyF, hk, ev_smul, map_pow, map_natCast]
  rfl

end GlobalTheory.LvT.Built.BarPass
