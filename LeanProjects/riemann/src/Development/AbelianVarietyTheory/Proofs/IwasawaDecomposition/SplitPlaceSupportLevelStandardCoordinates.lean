import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.Columns.MtHeckeSum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitHeckeElementLabelZerosThenNegOnes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharEqOneInertPrimeOffLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPrimeIdemOfInert
import Formalism.LocalToGlobal.Columns.RecLevelLocP
import Formalism.LocalToGlobal.Columns.DecoFin
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

set_option maxHeartbeats 2000000

namespace GlobalTheory.Mem.R3.LiftBrg.SplitLoc

theorem castGL_mem_St {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m n : ℕ}
    (h : m = n) (y : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    castGL h y ∈ Formalism.L2.DIV.St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ↔ y ∈ Formalism.L2.DIV.St 1 := by
  subst h
  have : castGL (rfl : m = m) y = y := by
    ext i j
    simp [castGL]
  rw [this]

theorem castGL_symm_apply {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (y : GL (Fin n) R) :
    castGL h (castGL h.symm y) = y := by
  subst h
  ext i j
  simp [castGL]

theorem bc_castGL {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m n : ℕ} (h : m = n) (y : GL (Fin m) R) :
    Formalism.UG.bc φ (castGL h y) = castGL h (Formalism.UG.bc φ y) := by
  subst h
  ext i j
  simp [castGL, Formalism.UG.bc]

theorem castGL_eq_one_iff {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (y : GL (Fin m) R) :
    castGL h y = 1 ↔ y = 1 := by
  rw [← map_one (castGL (R := R) h)]
  exact (castGL h).injective.eq_iff

end GlobalTheory.Mem.R3.LiftBrg.SplitLoc

namespace GlobalTheory.Mem.R3.LiftBrg.SplitLoc

theorem prV_swap {D : D7} (w : HeightOneSpectrum (𝓞 D.host.F))
    (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    Formalism.UG.prV (E := D.host.E) w (swapAE D z) =
      Algebra.TensorProduct.comm D.host.F (w.adicCompletion D.host.F) D.host.E
        (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F w) (AlgHom.id D.host.F D.host.E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => rw [RingHom.map_add (swapAE D), RingHom.map_add, hx, hy, map_add, map_add]

theorem bc_prV_swap_eq_one_iff {D : D7} {m : ℕ} (w : HeightOneSpectrum (𝓞 D.host.F))
    (M : GL (Fin m) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) :
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) (Formalism.UG.bc (swapAE D) M) = 1 ↔
      (M : Matrix (Fin m) (Fin m) _).map
        (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F w) (AlgHom.id D.host.F D.host.E)) = 1 := by
  set τ := Algebra.TensorProduct.comm D.host.F (w.adicCompletion D.host.F) D.host.E
  have hτ : Function.Injective τ := τ.injective
  rw [← Units.val_eq_one]
  have e : ((Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) (Formalism.UG.bc (swapAE D) M)) : Matrix (Fin m) (Fin m) _) =
      ((M : Matrix (Fin m) (Fin m) _).map
        (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F w) (AlgHom.id D.host.F D.host.E))).map τ := by
    ext i j
    simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact prV_swap w _
  rw [e]
  constructor
  · intro h
    ext i j
    have := congrFun (congrFun h i) j
    rw [Matrix.map_apply, Matrix.one_apply] at this
    rw [Matrix.one_apply]
    apply hτ
    rw [this]
    split_ifs <;> simp
  · intro h
    rw [h]
    ext i j
    rw [Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

end GlobalTheory.Mem.R3.LiftBrg.SplitLoc

namespace GlobalTheory.Mem.R3.LiftBrg.SplitLoc

theorem isLocEnv_iff {D : D7} (V : HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ)
    (x : Bridge.Gf V) (hs : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) (pl i.1).asIdeal ≠ (pl i.1).asIdeal) :
    isLocEnv V pl ok i x ↔ GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V ((pl i.1).under (𝓞 D.host.F)) x := by
  constructor
  · intro h
    exact GlobalTheory.Mem.R3.LiftInertChi.locAt_of_isLocElt V _ x ((GlobalTheory.Hk3Split.isLabElt_of_isTEnv V pl ok i x).2.1 h)
  · intro h
    obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt (D := D) (pl i.1) hs
    obtain ⟨α, hα, hfin⟩ := GlobalTheory.HeckeRowsCompare.fin_lift V x
    have hI : IsPrimeIdem (pl i.1) e (e + cA D e) := Or.inl ⟨he, rfl⟩
    obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
    obtain ⟨-, ε, hε, hf⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ hI
    refine ⟨e, α, he, hα, ?_, ?_⟩
    · show SuppF V (e + cA D e) α
      rw [hf, GlobalTheory.HeckeRowsCompare.suppF_iff V hε hα, hfin, GlobalTheory.HeckeRowsCompare.mem_locGrp]
      exact h
    · rw [← hfin]
      rfl

end GlobalTheory.Mem.R3.LiftBrg.SplitLoc

namespace GlobalTheory.Mem.R3.LiftBrg.SplitLoc

theorem mem_levJ_iff {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (x : Bridge.Gf V) (v : HeightOneSpectrum (𝓞 D.host.F)) (hloc : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V v x)
    (hU : Formalism.UG.bc (swapAE D) (x : GL (Fin V.rank) _) ∈ UA D.sp.cm V.gram)
    (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP.under (𝓞 D.host.F) ≠ v) :
    x ∈ (levEnv V β L).J ↔ Formalism.UG.bc (swapAE D) (x : GL (Fin V.rank) _) ∈ Formalism.L2.DIV.St β := by
  constructor
  · intro h
    exact Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev h)
  · intro hS
    set y := Formalism.UG.bc (swapAE D) (x : GL (Fin V.rank) _) with hy
    have hred : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → Formalism.L2.DIV.redFn β PP y = 1 :=
      fun PP hPP => GlobalTheory.Mem.R3.LiftInertChi.redFn_eq_one_of_locAt β x hS v hloc PP (hoff PP hPP)
    have hpar : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ∀ b, y ∈ Formalism.L2.DIV.parah β PP b := by
      intro PP hPP b
      refine ⟨⟨y, hS⟩, ?_, rfl⟩
      show Formalism.L2.DIV.redAt β PP ⟨y, hS⟩ ∈ Formalism.L2.DIV.blockTri b
      have := hred PP hPP
      rw [Formalism.L2.DIV.redFn, Formalism.L2.DIV.extendOne_of_mem _ hS] at this
      rw [this]
      exact one_mem _
    show y ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flag1L L)
    refine ⟨⟨⟨⟨hU, hS⟩, ?_⟩, ?_⟩, ?_⟩
    · exact Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hPP => hpar PP (Or.inl hPP) _
    · exact Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hPP => hpar PP (Or.inr hPP) _
    · have hr1 : Formalism.L2.DIV.rTup β (flag1L L) y = 1 := by
        funext PP
        show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn _ PP.1 _) = 1
        rw [hred PP.1 (Or.inl PP.2)]
        exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
      rw [hr1]
      exact one_mem _

end GlobalTheory.Mem.R3.LiftBrg.SplitLoc

namespace GlobalTheory.Mem.R3.LiftBrg.SplitLoc

theorem conj_eq_one_iff {G : Type} [Group G] (a u : G) : a * u * a⁻¹ = 1 ↔ u = 1 := by
  constructor
  · intro h
    have : u = a⁻¹ * (a * u * a⁻¹) * a := by group
    rw [this, h]; group
  · rintro rfl; group

theorem conj_mem_iff {G : Type} [Group G] (H : Subgroup G) {a : G} (ha : a ∈ H) (u : G) : a * u * a⁻¹ ∈ H ↔ u ∈ H := by
  constructor
  · intro h
    have : u = a⁻¹ * (a * u * a⁻¹) * a := by group
    rw [this]
    exact H.mul_mem (H.mul_mem (H.inv_mem ha) h) ha
  · intro h
    exact H.mul_mem (H.mul_mem ha h) (H.inv_mem ha)

theorem mem_mhlKv_iff_St {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {v : HeightOneSpectrum (𝓞 F)} (u : Formalism.L2.Col.UAd hc n)
    (h1 : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
      Formalism.UG.bc (Formalism.UG.prV (E := E) w) (u : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1) :
    u ∈ Formalism.L2.Col.mhlKv hc n v ↔ (u : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ Formalism.L2.DIV.St 1 := by
  constructor
  · intro hK
    rw [Formalism.L2.Col.mhl_eq_put u.2 h1]
    exact Formalism.L2.Col.rll_put_mem_St n v hK.2
  · intro hS
    refine ⟨h1, ?_⟩
    rw [Formalism.L2.Col.St_one] at hS
    exact Formalism.L2.DIV.lc_stab_loc v (Formalism.L2.Col.stdLat E n) _ hS

end GlobalTheory.Mem.R3.LiftBrg.SplitLoc

namespace GlobalTheory.Mem.R3.LiftBrg.SplitLoc

theorem loc_iff : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (hF : FrameOK X I U i t A k) (x : (famR X I hX U Xg tr).A.ok t × ℕ) (v : HeightOneSpectrum (𝓞 X.toD7.host.F)) (Pb : HeightOneSpectrum (𝓞 X.toD7.host.E)) (hPb : Formalism.L2.Col.conjPrime₂ Pb = x.1.1.1) (hv : Formalism.L2.Col.IsOver v Pb) (g : Bridge.Gf (Vc X.toD7 i)) (u : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) (hg : castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((g : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = A * k * (u : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹),
    ((envL X I hX U Xg tr L cV i t).isLoc x g ↔
      ∀ w : HeightOneSpectrum (𝓞 X.toD7.host.F), w ≠ v →
        Formalism.UG.bc (Formalism.UG.prV (E := X.toD7.host.E) w) (u : GL (Fin X.B.R.nV) (EA X)) = 1) ∧
    ((envL X I hX U Xg tr L cV i t).isLoc x g →
      (g ∈ (envL X I hX U Xg tr L cV i t).lev.J ↔ u ∈ Formalism.L2.Col.mhlKv X.toD7.sp.cm X.B.R.nV v)) := by
  intro X px I hX U Xg tr L hI hV hL cV i t A k hF x v Pb hPb hv g u hg
  set P : HeightOneSpectrum (𝓞 X.toD7.host.E) := x.1.1.1 with hPdef
  have hoffset : P ∈ Formalism.L2.DIV.offSet ∅ (sgL X I U t) ∅ := x.1.2
  have hP : Formalism.L2.Col.IsOver v P := by
    rw [← hPb]
    exact Formalism.L2.Col.IsOver.conj X.toD7.sp.cm hv
  have hunder : P.under (𝓞 X.toD7.host.F) = v := HeightOneSpectrum.ext hP.symm

  have hA1 : (envL X I hX U Xg tr L cV i t).isLoc x g ↔ GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt (Vc X.toD7 i) v g := by
    rw [← hunder]
    exact isLocEnv_iff (Vc X.toD7 i) (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) _ x g hoffset.1
  have hcomp : ∀ w : HeightOneSpectrum (𝓞 X.toD7.host.F),
      (Units.val ((g : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank)
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F ⊗[X.toD7.host.F] X.toD7.host.E))).map
        (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV X.toD7.host.F w) (AlgHom.id X.toD7.host.F X.toD7.host.E)) = 1 ↔
      Formalism.UG.bc (Formalism.UG.prV (E := X.toD7.host.E) w) (u : GL (Fin X.B.R.nV) (EA X)) = 1 := by
    intro w
    rw [← bc_prV_swap_eq_one_iff, ← castGL_eq_one_iff (rkEq X i).symm, ← bc_castGL, hg, map_mul, map_mul, map_inv,
      conj_eq_one_iff]
  have hA2 : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt (Vc X.toD7 i) v g ↔ ∀ w : HeightOneSpectrum (𝓞 X.toD7.host.F), w ≠ v →
      Formalism.UG.bc (Formalism.UG.prV (E := X.toD7.host.E) w) (u : GL (Fin X.B.R.nV) (EA X)) = 1 :=
    forall₂_congr fun w _ => hcomp w
  refine ⟨hA1.trans hA2, fun hloc => ?_⟩
  have hL1 := hA1.1 hloc
  have hu1 := hA2.1 hL1

  have hk := hF.2.2.2.1
  have hkuk : k * (u : GL (Fin X.B.R.nV) (EA X)) * k⁻¹ ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV :=
    mul_mem (mul_mem hk u.2) (inv_mem hk)
  have hU := (hF.2.2.1 _).1 hkuk
  have e1 : castGL (rkEq X i) (A * (k * (u : GL (Fin X.B.R.nV) (EA X)) * k⁻¹) * A⁻¹) =
      Formalism.UG.bc (swapAE X.toD7) ((g : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _) := by
    rw [show A * (k * (u : GL (Fin X.B.R.nV) (EA X)) * k⁻¹) * A⁻¹ = A * k * (u : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹ by group,
      ← hg, castGL_symm_apply]
  rw [e1] at hU

  have hsg : ∀ PP ∈ sgL X I U t, PP.under (𝓞 X.toD7.host.F) ≠ v := by
    intro PP hPP hu
    have hov : Formalism.L2.Col.IsOver v PP := by rw [← hu]; rfl
    rcases Formalism.L2.Col.mhl_over_eq X.toD7.sp.cm hv PP hov with h | h
    · subst h
      refine hoffset.2.2 PP (Or.inr hPP) ?_
      rw [Formalism.L2.Col.conjIdeal_asIdeal, ← hPb, Formalism.L2.Col.conjPrime_conjPrime]
    · rw [hPb] at h
      subst h
      exact hoffset.2.1 (Or.inr hPP)
  have hoff : ∀ PP, PP ∈ (L.datVt i t).Pg ∨ PP ∈ (L.datVt i t).Q → PP.under (𝓞 X.toD7.host.F) ≠ v := by
    intro PP hPP
    refine hsg PP ?_
    rcases hPP with hPP | hPP
    · rw [show (L.datVt i t).Pg = L.Pg from rfl, hL.Pg] at hPP
      classical
      exact Finset.mem_union.2 (Or.inl hPP)
    · rw [show (L.datVt i t).Q = L.Q t from rfl, hL.Q t] at hPP
      have e4 : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel t.1 := by
        simp only [ColIn.Q, tup_ixOf]
      rw [e4] at hPP
      classical
      exact Finset.mem_union.2 (Or.inr hPP)
  show g ∈ (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J ↔ _
  rw [mem_levJ_iff (Vc X.toD7 i) (L.βV i) (L.datVt i t) g v hL1 hU hoff, hL.beta.1 i, mem_mhlKv_iff_St u hu1,
    ← castGL_mem_St (rkEq X i).symm, hg, conj_mem_iff _ (mul_mem hF.2.1 hF.2.2.2.2.1)]

end GlobalTheory.Mem.R3.LiftBrg.SplitLoc
