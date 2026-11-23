import Formalism.LocalToGlobal.ProjectiveLattices.ValuedUnif
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
import Formalism.LocalToGlobal.ProjectiveLattices.PtOfSInst
import Formalism.LocalToGlobal.ProjectiveLattices.ComplPf
import Formalism.LocalToGlobal.ProjectiveLattices.CoreProofs
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem wchar_nsmul {S : Type} [CommRing S] (e : Ix Dw → ℕ) (t : Ix Dw → Sˣ) (k : ℕ) :
    wchar (k • e) t = wchar e t ^ k := by
  unfold wchar
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_comm, pow_mul]

theorem wchar_ne_zero {S : Type} [Field S] (e : Ix Dw → ℕ) (t : Ix Dw → Sˣ) : wchar e t ≠ 0 := by
  unfold wchar
  exact Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (t i).ne_zero

end Weights

variable {D : D7} {T : Top D}

theorem exponent_base_weight_zero (j : ℕ) : ex (T.Q.Dw j) (wtA (wt0 D j)) (wt0 D j).n = 0 := by
  funext i
  cases i <;> simp [ex, wtA, wt0, wscalar, ext0]

theorem ex_addL {j : ℕ} (wL : WeightFamilies.Wt D j) (k : ℕ) :
    ex (T.Q.Dw j) (wtA (addL (wt0 D j) wL k)) (addL (wt0 D j) wL k).n = k • ex (T.Q.Dw j) (wtA wL) wL.n := by
  induction k with
  | zero => rw [addL_zero, exponent_base_weight_zero, zero_smul]
  | succ k ih => rw [← wadd_addL, wtA_wadd, n_wadd, ex_add, ih, succ_nsmul, add_comm]

variable (j : ℕ)

def evIHom {Tc : CDVR} {io : T.Q.c.F →+* Tc.Fr} (y : IntFr (T.Q.Xo j) T.Q.c Tc io) : T.R j →+* Tc.Fr where
  toFun := evI y
  map_one' := by
    letI := io.toAlgebra
    exact evalAt_one _ _ y.1 y.2.1
  map_mul' := evI_mul y
  map_zero' := by
    letI := io.toAlgebra
    exact evalAt_zero _ _ y.1
  map_add' := evI_add y

def chiI {Tc : CDVR} {io : T.Q.c.F →+* Tc.Fr} (y : IntFr (T.Q.Xo j) T.Q.c Tc io) :
    AddMonoidAlgebra (T.R j) (Deg D j) →+* Tc.Fr :=
  AddMonoidAlgebra.liftNCRingHom (evIHom j y) (1 : Multiplicative (Deg D j) →* Tc.Fr) (fun _ _ => Commute.all _ _)

theorem chiI_single {Tc : CDVR} {io : T.Q.c.F →+* Tc.Fr} (y : IntFr (T.Q.Xo j) T.Q.c Tc io) (d : Deg D j) (r : T.R j) :
    chiI j y (AddMonoidAlgebra.single d r) = evI y r := by
  unfold chiI
  rw [AddMonoidAlgebra.liftNCRingHom_single]
  simp only [MonoidHom.one_apply, mul_one]
  rfl

theorem chiI_smul {Tc : CDVR} {io : T.Q.c.F →+* Tc.Fr} (y : IntFr (T.Q.Xo j) T.Q.c Tc io) (a : T.Q.c.F)
    (f : AddMonoidAlgebra (T.R j) (Deg D j)) : chiI j y (a • f) = io a * chiI j y f := by
  refine AddMonoidAlgebra.induction_linear f ?_ ?_ ?_
  · rw [smul_zero, map_zero, mul_zero]
  · intro f g hf hg
    rw [smul_add, map_add, map_add, hf, hg, mul_add]
  · intro d r
    rw [show a • AddMonoidAlgebra.single d r = AddMonoidAlgebra.single d (a • r) from AddMonoidAlgebra.smul_single a d r,
      chiI_single, chiI_single, evI_smul]

theorem chiI_inc (h : LawsP T) {Tc : CDVR} {io : T.Q.c.F →+* Tc.Fr} (y : IntFr (T.Q.Xo j) T.Q.c Tc io) (w : WeightFamilies.Wt D j)
    (F : (recB h.toLawsCore).Cusp j w) : chiI j y (incG deg (cutR T.C j) w F) = evI y (F : T.R j) := by
  rw [incG_apply, chiI_single]

section Main

variable {D : D7} {T : Top D}

theorem evR_eq_of_map {j : ℕ}
    (hWD : EvalWD (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z))
    {f : T.R j} (hf : IsNatural (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) f)
    {S : Type} [CommRing S] [Algebra T.Q.c.F S] (w : FrPt (T.Q.Xo j) T.Q.c S) (p : TRing T.Q.c.F)
    (φ : p.R →ₐ[T.Q.c.F] S) (y : FrPt (T.Q.Xo j) T.Q.c p.R) (h : FrMap φ y w) :
    evR (T.Q.Xo j) T.Q.c f w = φ (f p y) := by
  have hT : FromTest (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) w := ⟨p, φ, y, h⟩
  unfold evR evalAt
  rw [dif_pos hT]
  exact hWD f hf S _ _ _ _ _ _ w hT.choose_spec.choose_spec.choose_spec h

def RealPtNZSt (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO))
    (hU : IsUnif (OsK (recPlus h j hj) la G.w) (unifO (recPlus h j hj) la G.N)) [∀ ζ : PtsG G la, IsDVRAt ζ] : Prop :=
  ∀ ζ : PtsG G la, ∃ (y : (extAll h j hj).Pt' la) (Tc : CDVR) (ι : Loc ζ →+* Tc.V) (_ : IsLocalHom ι)
    (hunr : ∃ ϖ : Loc ζ, Irreducible ϖ ∧ Irreducible (ι ϖ)) (ev : Rp (recPlus h j hj) la G.N →+* Tc.Fr)
    (hu : IsUnit (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0))),
    (∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), (extAll h j hj).vAt' la y ((recPJ h j hj).inc w F) =
      nval Tc.V (ep (unifO (recPlus h j hj) la G.N) ζ) (ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)))) ∧
    (∀ x : ↥(Frac0 (recPlus h j hj) la G.w),
      IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0) hu (x : Lw (recPlus h j hj) la G.w) =
        phiAt ζ Tc.Fr ι hU (addVal_map_of_unr ι hunr) (toOsK (recPlus h j hj) la G.w x)) ∧
    ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), NZAt hG (F : T.R j) →
      ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)) ≠ 0

theorem realPtSt_of_NZ {h : LawsP T} {j : ℕ} {hj : InR D j} {hG : GenFrEx (T.Q.Xo j) T.Q.c} {ka wL wF : WeightFamilies.Wt D j}
    {G : GlobalFamilyData (recPlus h j hj) ka wL wF} {la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)}
    {hU : IsUnif (OsK (recPlus h j hj) la G.w) (unifO (recPlus h j hj) la G.N)} [∀ ζ : PtsG G la, IsDVRAt ζ]
    (hR : RealPtNZSt h j hj hG G la hU) :
    @RealPtSt D (recB h.toLawsCore) T.G.P j (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj) ka wL wF G la hU
      ‹∀ ζ : PtsG G la, IsDVRAt ζ› := by
  intro ζ
  obtain ⟨y, Tc, ι, hl, hunr, ev, hu, hv, hdeg, -⟩ := hR ζ
  exact ⟨y, Tc, ι, hl, hunr, ev, hu, hv, hdeg⟩

end Main

end Formalism.L2.Pj
