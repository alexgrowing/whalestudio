import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.OrdStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndTop
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrderGerm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

set_option maxHeartbeats 1000000 in

theorem jetD_twist {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] [StarRing (𝓞 E)] (y : FrPt Xo c S)
    (C : ChartAt Xo c y) (e' : ∀ m, FrTy y C.d C.x m) (m : ℕ) (cc : Fin C.d → Fin C.d → S)
    (he : ∃ u : (Jet S (Fin 2 × Fin C.d) m)ˣ,
      (u : Jet S (Fin 2 × Fin C.d) m) = psJet m (expP (-bilL C.B.G cc)) ∧
        LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (scaleGen (Xo := Xo) _ _ (unitΓ u) (C.e m)))
    (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (f : MvPowerSeries (Fin 1 × Fin C.d) S)
    (hf : JetD y C.d C.x C.B.A.act C.e C.wP k F m f) :
    JetD y C.d C.x C.B.A.act e' C.wP k F m (f * expP ((k : S) • diagL C.B H.w0 cc)) := by
  have hL := Xo.univ.t.PP.isLB
  obtain ⟨F₁, τ₁, hP₁, hC₁, hV₁⟩ := hf
  obtain ⟨u, hu, hCe⟩ := he
  have h1 := corr_pull_scale _ _ (e' m) (C.e m) (unitΓ u) (homAt y.x (GermD.sL m (C.B.A.act H.w0))).left hCe
  rw [FBIdLB.unitΓ_homAt] at h1
  have hEL : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (eL y C.d C.x C.B.A.act e' C.wP m)
      (scaleGen _ _ (unitΓ (Units.map (GermD.sL m (C.B.A.act H.w0)).toMonoidHom u))
        (eL y C.d C.x C.B.A.act C.e C.wP m)) := by
    have h2 := ReciprocityTheory.ChartRestriction.G.DVR.corr_mulGen
      (ExpTieGerm.corr_refl (L := Xo.univ.t.PP.L) (LB.pullGen Xo.univ.t.PP.L _ _ C.wP (C.x m).left)) h1
    rw [mulGen_scale_right] at h2
    exact h2
  set U : (Jet S (Fin 1 × Fin C.d) m)ˣ := Units.map (GermD.sL m (C.B.A.act H.w0)).toMonoidHom u with hU
  set w : Γ(Sp (Jet S (Fin 1 × Fin C.d) m), ⊤)ˣ := unitΓ U with hw
  have hG : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (genPow _ _ (eL y C.d C.x C.B.A.act e' C.wP m) k)
      (scaleGen _ _ (w ^ k) (genPow _ _ (eL y C.d C.x C.B.A.act C.e C.wP m) k)) := by
    have := ExpTieGerm.corr_genPow hEL k
    rwa [genPow_scale] at this
  have h3 := ExpTieGerm.corr_scale hC₁ (w ^ k)
  have hC' := ReciprocityTheory.ChartRestriction.G.DVR.corr_trans hL h3 (ReciprocityTheory.ChartRestriction.G.DVR.corr_symm hG)
  have hV' := isValueAt_scale hV₁ (w ^ k)
  have hprod := unit_jet C.B H.w0 cc m k u hu
  have hinv : psJet m (expP ((k : S) • diagL C.B H.w0 cc)) = ↑((U ^ k)⁻¹) := by
    set X := psJet m (expP ((k : S) • diagL C.B H.w0 cc)) with hX
    calc X = X * ((↑(U ^ k) : Jet S (Fin 1 × Fin C.d) m) * ↑((U ^ k)⁻¹)) := by
          rw [Units.mul_inv, _root_.mul_one]
      _ = (X * ↑(U ^ k)) * ↑((U ^ k)⁻¹) := (_root_.mul_assoc _ _ _).symm
      _ = ↑((U ^ k)⁻¹) := by rw [hprod, _root_.one_mul]
  have hw' : ((w ^ k)⁻¹ : Γ(Sp (Jet S (Fin 1 × Fin C.d) m), ⊤)ˣ) = unitΓ ((U ^ k)⁻¹) := by
    simp [hw, unitΓ, map_pow, map_inv]
  refine ⟨F₁, _, hP₁, hC', ?_⟩
  have hv : toΓ _ (psJet m (f * expP ((k : S) • diagL C.B H.w0 cc))) =
      toΓ _ (psJet m f) * (((w ^ k)⁻¹ : Γ(Sp (Jet S (Fin 1 × Fin C.d) m), ⊤)ˣ) :
        Γ(Sp (Jet S (Fin 1 × Fin C.d) m), ⊤)) := by
    rw [hw']
    show _ = toΓ _ _ * toΓ _ _
    rw [← map_mul, FBIdJet.psJet_mul, hinv]
  rw [hv]
  exact hV'

theorem jetD_unique {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (d : ℕ)
    (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (e : ∀ m, FrTy y d x m) (wP : PrimTy H Xo) (k : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (D : ℕ) (f g : MvPowerSeries (Fin 1 × Fin d) S)
    (hf : JetD y d x act e wP k F D f) (hg : JetD y d x act e wP k F D g) : psJet D f = psJet D g := by
  have hL := Xo.univ.t.PP.isLB
  obtain ⟨F₁, τ₁, hP₁, hC₁, hV₁⟩ := hf
  obtain ⟨F₂, τ₂, hP₂, hC₂, hV₂⟩ := hg
  have hF := GermFun.pull_unique _ _ _ _ _ _ _ _ hP₁ hP₂
  subst hF
  have hτ := GermFun.gen_eq_of_corr _ hL _ _ _ _ _ _ _ hC₁ hC₂
  subst hτ
  exact GermFun.toΓ_injective _ (GermFun.value_unique _ _ hL _ _ _ _ _ _ hV₁ hV₂)

theorem ord_holds : OrdStatement := by
  intro E _ _ _ H Dw l Xo c _ nab hnab S _ _ _ y C k n D F f hf a P hP hD
  have hs := hnab.1
  obtain ⟨C₀, hex, hpin⟩ := hnab.2 S y
  choose f₀ hf₀ using fun b => hex k (F b)
  obtain ⟨e', hfr, hrig, cc, hT, -, hsym, hbal, hu⟩ :=
    frFixB_of (frTruncFix_of frRatio_holds) linEigSt_holds E H Dw l Xo c hs S y C
  have hgerm : ∀ b, ∃ g, IsGerm y C.d C.x C.B.A.act e' C.wP k (F b) g := fun b => by
    obtain ⟨g, hg⟩ := germSt_holds E H Xo.X Xo.univ.t S y.x C.d C.B.G.F C.B.A.act (Lt1 Dw)
      (fun ℓ => y.u ℓ.1 ℓ.2) C.uvec C.x C.B.ph1 C.B.ph2 C.B.sy C.B.ad e' C.wP
      ((isChart_iff y C.d _ _ _ _).1 C.chart) ((isFrame_iff y C.d _ _ _ _ _ _ _ _).1 hfr) ((isPrim_iff _).1 C.prim)
      (fun m => hT m) k (F b)
    exact ⟨g, (isGerm_iff y C.d _ _ _ _ _ _ _).2 hg⟩
  choose g hg using hgerm
  have h₁ : chartVal C k g P = chartVal C k f P :=
    harmInv_of (expActOf_of linEigSt_holds) E H Dw l Xo c hs S y C (cc D) (hsym D) (hbal D) k n D f g
      (fun b => jetD_unique y C.d C.x C.B.A.act e' C.wP k (F b) D _ _ (hg b D)
        (jetD_twist y C e' D (cc D) (hu D) k (F b) (f b) (hf b))) a P hP hD
  have h₂ := chartIndep2_of_glob GlobalTheory.SemiRigid.globalFns E H Dw l Xo c hs S y
    { C with e := e', frame := hfr, rig0 := hrig } C₀ k n F g f₀ hg hf₀ a P hP
  refine h₁.symm.trans (h₂.trans ?_)
  refine Finset.sum_congr rfl fun m _ => congrArg _ (Finset.prod_congr rfl fun b _ => ?_)
  exact (hpin k (F b) (f₀ b) (hf₀ b) (colOf m b)).symm

end GlobalTheory.OrderGerm
