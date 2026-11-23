import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndVerb
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpAct
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTieAlg
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.HarmInvB
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.HarmInvC

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
  Formalism.L2.Pj CIndFrFix
open ReciprocityTheory.ChartRestriction.G.TB.LogPf (logOf)

def HarmKillJetSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l)
    (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (k n D : ℕ)
    (g g' : Fin n → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (β : Matrix (Fin (dL Dw)) (Fin (dL Dw)) S),
    (∀ i j, β i j ≠ 0 → ((ltIdx Dw).symm j).1 = ComplexEmbedding.conjugate ((ltIdx Dw).symm i).1) →
    (∀ b, psJet D (g' b) =
      psJet D (g b * PowerSeries.subst ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) β) (PowerSeries.exp S))) →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
      (∀ m ∈ P.support, m.degree ≤ D) →
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g' b) (colOf m b) =
        ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g b) (colOf m b)

namespace HarmInvPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

theorem tie_val (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : IsExpOf C.B.G.F C.uvec φ) (k : ℕ) {n : ℕ} (f : Fin n → MvPowerSeries (Fin 1 × Fin C.d) S)
    (P : MvPolynomial (LtN Dw n) c.F) :
    chartVal C k f P = ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
      ∏ b, expVal (compL φ (f b * FB.expS S ((k : S) • C.B.hL S C.h H.w0))) (colOf m b) := by

  have hFK : C.B.FK S = C.B.G.F := by
    funext i
    first
      | simp [FB.FK, FGLaw.mapF]
      | (ext n; simp [FB.FK, FGLaw.mapF, MvPowerSeries.coeff_map])
  have hφ' : IsExpOf (C.B.FK S) C.uvec φ := by
    rw [hFK]
    exact hφ
  unfold chartVal
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun b _ => ?_
  exact tie_alg (C.B.FK S) C.uvec φ hφ' (colOf m b) _

theorem cc_diagL {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB S d O) (w0 : O) (cc : Fin d → Fin d → S) :
    MvPowerSeries.constantCoeff (diagL B w0 cc) = 0 := by

  have hpt : ∀ {n : ℕ} (j : Fin n) (i : Fin d), MvPowerSeries.constantCoeff (pt S d j i) = 0 := by
    intro n j i
    simp [pt]

  have hlg : ∀ (j : Fin 2) (i : Fin d), MvPowerSeries.constantCoeff (lg B.G j i) = 0 := by
    intro j i
    exact ReciprocityTheory.ChartRestriction.G.TB.LogPf.constantCoeff_ev
      (fun j' i' => by
        fin_cases j'
        first
          | exact hpt j i'
          | simp [pt])
      ((HarmInvB.logOf_props B.G).1 i)
  unfold diagL
  refine ReciprocityTheory.ChartRestriction.G.TB.LogPf.constantCoeff_ev ?_ ?_
  · intro j i
    fin_cases j
    · first
        | exact hpt 0 i
        | simp [pt]
    · exact ReciprocityTheory.ChartRestriction.G.TB.LogPf.constantCoeff_ev
        (fun j' i' => by
          fin_cases j'
          first
            | exact hpt 0 i'
            | simp [pt])
        (B.A.const w0 i)
  · unfold bilL
    rw [map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    first
      | simp [hlg]
      | simp [hlg, MvPowerSeries.smul_eq_C_mul]
      | (rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_smul,
            MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, hlg]
         simp)

end HarmInvPf

open HarmInvPf in

theorem harmInv_of_kill (hK : HarmKillJetSt) (hA : ExpActOfSt) : HarmInvSt := by
  intro E _ _ _ H Dw l Xo c _ hs S _ _ _ y C cc hsym hbal k n D f f' hj a P hP hD
  obtain ⟨h0, h1, hadd⟩ := HarmInvB.logOf_props C.B.G
  obtain ⟨ε, hinv, htr⟩ := ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.formal_exp_law S C.d C.B.G (fun i => logOf C.B.G i) h0 h1 hadd
  have hφ := isExpOf_expPhi C.B.G C.uvec (fun i => logOf C.B.G i) ε h1 hinv htr
  set φ := ExpOf.expPhi C.uvec ε with hφdef
  set t : Fin 1 × Fin (dL Dw) → S := fun q => algebraMap c.F S (embK c ((ltIdx Dw).symm q.2).1 H.w0) with ht
  have hta : ∀ q, MvPowerSeries.constantCoeff
      (t q • (MvPowerSeries.X q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S)) = 0 :=
    fun q => by rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_X, mul_zero]
  have hact : ∀ j, MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act H.w0 j) =
      MvPowerSeries.subst (fun q => t q • (MvPowerSeries.X q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S)) (φ j) :=
    fun j => hA E H Dw l Xo c S y C φ hφ H.w0 j
  have hcd : MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (diagL C.B H.w0 cc) =
      ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) (HarmInvB.qβ cc C.uvec t) := by
    have e := HarmInvB.compL_diagL C.B H.w0 cc C.uvec ε hinv _ hta hact
    rw [HarmInvB.quad_form] at e
    exact e
  have hφs : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin C.d => φ p.2) :=
    HarmInvB.hasSubst0 fun p => hφ.const p.2
  have hccd : MvPowerSeries.constantCoeff ((k : S) • diagL C.B H.w0 cc) = 0 := by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, cc_diagL, mul_zero]
  set EL := FB.expS S ((k : S) • C.B.hL S C.h H.w0) with hEL
  have hjet : ∀ b, psJet D (compL φ (f' b * EL)) = psJet D (compL φ (f b * EL) *
      PowerSeries.subst ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) (HarmInvB.qβ cc C.uvec t))
        (PowerSeries.exp S)) := by
    intro b
    have e1 : psJet D (f' b * EL) = psJet D (f b * expP ((k : S) • diagL C.B H.w0 cc) * EL) := by
      rw [FBIdJet.psJet_mul, hj b, ← FBIdJet.psJet_mul]
    have e2 := HarmInvA.psJet_subst_congr D (fun p : Fin 1 × Fin C.d => φ p.2) (fun p => hφ.const p.2) e1
    have e3 : MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2)
        (f b * expP ((k : S) • diagL C.B H.w0 cc) * EL) = compL φ (f b * EL) *
          PowerSeries.subst ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) (HarmInvB.qβ cc C.uvec t))
            (PowerSeries.exp S) := by
      rw [MvPowerSeries.subst_mul hφs, MvPowerSeries.subst_mul hφs, expP,
        HarmInvA.subst_exp _ (fun p => hφ.const p.2) _ hccd, MvPowerSeries.subst_smul hφs, hcd, compL,
        MvPowerSeries.subst_mul hφs]
      ring
    exact e2.trans (congrArg (psJet D) e3)
  have hβ : ∀ i j, HarmInvB.qβ cc C.uvec t i j ≠ 0 →
      ((ltIdx Dw).symm j).1 = ComplexEmbedding.conjugate ((ltIdx Dw).symm i).1 := by
    intro i j hne
    refine hbal ((ltIdx Dw).symm i) ((ltIdx Dw).symm j) fun h0' => hne ?_
    have e : HarmInvB.qβ cc C.uvec t i j = (∑ a, ∑ b, cc a b * C.uvec ((ltIdx Dw).symm i) a *
        C.uvec ((ltIdx Dw).symm j) b) * t (0, j) := by
      simp only [HarmInvB.qβ, Finset.sum_mul]
    rw [e, h0', zero_mul]
  rw [tie_val C φ hφ k f' P, tie_val C φ hφ k f P]
  exact hK E H Dw l c S k n D (fun b => compL φ (f b * EL)) (fun b => compL φ (f' b * EL))
    (HarmInvB.qβ cc C.uvec t) hβ hjet a P hP hD

theorem harmInv_of (hA : ExpActOfSt) : HarmInvSt :=
  harmInv_of_kill (fun _ _ _ _ _ _ _ c _ _ _ _ k n D g g' β hβ hj a P hP hD =>
    HarmInvC.harm_kill_jet c k n D g g' β hβ hj a P hP hD) hA

end Formalism.MainNotions.ModuliIntegralCharts.H1
