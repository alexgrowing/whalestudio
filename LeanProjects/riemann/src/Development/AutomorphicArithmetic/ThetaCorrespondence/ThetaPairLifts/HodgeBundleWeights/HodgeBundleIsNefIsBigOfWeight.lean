import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChoiceFreeSectionConstruction
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.BaseWeightLineBundleIsNef
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HodgeBundleAmpleOnRegularLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChoiceFreeSectionConstructionStatement

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
namespace GlobalTheory.HSApp
theorem hodge_bundle_nef_and_big : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice TF.X Z U P) (ω : CanId R.toModif) (x : ℝ) (D : D7) (V : (c.F →+* ℂ) → TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), FnAlgClosed Xo c → WtBig P → IsNef c.F (h.geo f₁ f₂ th k).LA ∧ IsBig c.F (h.geo f₁ f₂ th k).LA := by
  intro hP hN hS hC hL E _ _ _ H Dw l Xo c TF Z r U P R ω x D V dict h f₁ f₂ th k hF hW
  obtain ⟨hsm, hpr, hgc⟩ := GlobalTheory.VarFlag.isVariety₀_flag E H Dw l Xo c TF Z hF
  have hsm' : Smooth (str₀ TF.X Z) := SmoothOfRelativeDimension.smooth (dimFlag Dw) (str₀ TF.X Z)
  haveI : IsIntegral (Y₀ TF.X Z) := isIntegral_of_smooth_of_geometricallyConnected (str₀ TF.X Z)
  set la : AllWt.Weight Dw := P.u₂ + dimFlag Dw • P.u₁ with hla
  have hg₁ := (GlobalTheory.HSApp.gaps_of_wtBig E H Dw P hW P.u₁ (by simp)).1
  have hg₂ := (GlobalTheory.HSApp.gaps_of_wtBig E H Dw P hW P.u₂ (by simp)).1
  have hgla : GapGe 1 la := by
    intro τ k hk
    have a₁ := hg₁ τ k hk
    have a₂ := hg₂ τ k hk
    simp only [hla, Pi.add_apply, Pi.smul_apply, gap_add, gap_nsmul]
    nlinarith
  letI := algebraΓOfHom (str₀ TF.X Z)
  have hf₀ : ∀ r : c.F, algebraMap c.F Γ(Y₀ TF.X Z, ⊤) r =
      (str₀ TF.X Z).appTop ((Scheme.ΓSpecIso (.of c.F)).inv r) := fun _ => rfl
  have hs₀ : strHom c.F (Y₀ TF.X Z) = str₀ TF.X Z := strHom_eq hf₀
  have hp₀ : IsProjOver (strHom c.F (Y₀ TF.X Z)) := hs₀ ▸ hpr
  obtain ⟨hprop₀, H₀, hH₀⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hpr
  have nef : ∀ w : AllWt.Weight Dw, GapGe 0 w → IsNef c.F (L₀ TF.X Z w) :=
    fun w hw => _root_.GlobalTheory.T.base_weight_line_bundle_is_nef hP hN hL E H Dw l Xo c TF Z hF w hw
  have nef₀ : IsNef c.F (L₀ TF.X Z la) := nef la (hgla.mono (by norm_num))
  have big₀ : IsBig c.F (L₀ TF.X Z la) := by
    obtain ⟨y₀⟩ : Nonempty (Y₀ TF.X Z) := by
      obtain ⟨z⟩ : Nonempty (Sp c.F) := inferInstance
      obtain ⟨y, -⟩ := (str₀ TF.X Z).surjective z
      exact ⟨y⟩
    have hne : (U₀ TF.X Z : Set (Y₀ TF.X Z)).Nonempty := (dense_U₀ TF.X Z).nonempty
    obtain ⟨y, hy⟩ := hne
    obtain ⟨mu, hmu0, m, hm, hA⟩ := _root_.GlobalTheory.T.hodge_bundle_ample_on_regular_locus hP hN hS hC E H Dw l Xo c TF Z hF la hgla y hy
    obtain ⟨m', Aa, s, hm', hAa, hAamp, hys⟩ := hA
    have hNn := isLB_L₀ TF.X Z (m • la - mu)
    have hdiv : (LB.div (lbPow (L₀ TF.X Z (m • la - mu)) m') Aa).IsLB := Semi.LB.isLB_div (isLB_lbPow hNn m') hAa
    have nefmu := nef mu hmu0
    have hB := (nefmu.pow hAamp m').isBig_tens_ample hN hp₀ hAamp
    have hcls0 : cls (L₀ TF.X Z 0) (isLB_L₀ TF.X Z 0) = 0 := by
      have h := cls_common_add (common₀ TF.X Z) 0 0
      simp only [add_zero] at h
      exact left_eq_add.1 h
    have hnsmul : ∀ n : ℕ, cls (L₀ TF.X Z (n • la)) (isLB_L₀ TF.X Z _) = n • cls (L₀ TF.X Z la) (isLB_L₀ TF.X Z la) := by
      intro n
      induction n with
      | zero => simpa only [zero_nsmul] using hcls0
      | succ n ih => rw [succ_nsmul, cls_common_add (common₀ TF.X Z), ih, succ_nsmul]
    have h1 := cls_common_add (common₀ TF.X Z) (m • la - mu) mu
    rw [sub_add_cancel] at h1
    have hP' := isLB_lbPow (isLB_L₀ TF.X Z la) (m * m')
    have e : cls (lbPow (L₀ TF.X Z la) (m * m')) hP' = cls _ hB.isLB + cls _ hdiv := by
      rw [cls_lbPow (isLB_L₀ TF.X Z la), cls_tens (isLB_lbPow nefmu.isLB m') hAa, cls_div (isLB_lbPow hNn m') hAa,
        cls_lbPow nefmu.isLB, cls_lbPow hNn, mul_nsmul, ← hnsmul m, h1, smul_add]
      abel
    have hbigP : IsBig c.F (lbPow (L₀ TF.X Z la) (m * m')) :=
      hB.of_cls_eq_add hf₀ hpr hdiv ⟨s, sec_ne_zero_of_mem hys⟩ hP' e
    exact hbigP.of_pow (isLB_L₀ TF.X Z la) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hm.ne' hm'.ne'))
      (fun j => finite_coh_zero_twist_of_isProjOver hf₀ hpr (isLB_lbPow (isLB_L₀ TF.X Z la) j))
  have bigpull : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (g : Y ⟶ X), IsProjOver (g ≫ p) → topologicalKrullDim Y = topologicalKrullDim X → Dense (Set.range g) → ∀ N : LB X, (letI := algebraΓOfHom p; IsBig k N) → (letI := algebraΓOfHom (g ≫ p); IsBig k (N.pull g)) := fun k _ X Y _ p g hp hd hg N hN => GlobalTheory.BigPull.isBig_pull k X Y p g hp hd hg N hN
  obtain ⟨hprop₁, H₁, hH₁⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB _).1 R.proj
  haveI : IsProper (strHom c.F (Y₀ TF.X Z)) := hs₀ ▸ hprop₀
  haveI : IsProper (R.σ ≫ str₀ TF.X Z) := hprop₁
  haveI : IsProper R.σ := IsProper.of_comp R.σ (str₀ TF.X Z)
  have hcl : IsClosedMap R.σ := Scheme.Hom.isClosedMap R.σ
  haveI : Nonempty R.X := by
    obtain ⟨z⟩ : Nonempty (Sp c.F) := inferInstance
    haveI : GeometricallyConnected R.str := h.conn
    obtain ⟨y, -⟩ := R.str.surjective z
    exact ⟨y⟩
  haveI : Nonempty (Y₀ TF.X Z) := ⟨R.σ (Classical.arbitrary R.X)⟩
  have hdim : topologicalKrullDim R.X = topologicalKrullDim (Y₀ TF.X Z) := by
    rw [GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth R.str (dimFlag Dw) R.smooth,
      GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth (str₀ TF.X Z) (dimFlag Dw) hsm]
  have hdense : Dense (Set.range R.σ) := by
    refine (dense_U₀ TF.X Z).mono fun y hy => ?_
    have := R.iso
    obtain ⟨x, hx⟩ := (R.σ ∣_ U₀ TF.X Z).surjective ⟨y, hy⟩
    refine ⟨(R.σ ⁻¹ᵁ U₀ TF.X Z).ι x, ?_⟩
    have e := congrArg (fun q => q x) (morphismRestrict_ι R.σ (U₀ TF.X Z))
    simp only [Scheme.Hom.comp_apply] at e
    rw [← e, hx]
    rfl
  letI := algebraΓOfHom R.str
  change IsNef c.F ((L₀ TF.X Z la).pull R.σ) ∧ IsBig c.F ((L₀ TF.X Z la).pull R.σ)
  exact ⟨GlobalTheory.PosBaseChange.isNef_pull nef₀ hH₀ hH₁ R.σ hcl,
    bigpull c.F (Y₀ TF.X Z) R.X (str₀ TF.X Z) R.σ R.proj hdim hdense _ big₀⟩
end GlobalTheory.HSApp
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_bundle_isNef_isBig_of_weight : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice TF.X Z U P) (ω : CanId R.toModif) (x : ℝ) (D : D7) (V : (c.F →+* ℂ) → TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), FnAlgClosed Xo c → WtBig P → IsNef c.F (h.geo f₁ f₂ th k).LA ∧ IsBig c.F (h.geo f₁ f₂ th k).LA := by
  first | exact @_root_.GlobalTheory.HSApp.hodge_bundle_nef_and_big | exact _root_.GlobalTheory.HSApp.hodge_bundle_nef_and_big | (intros; apply _root_.GlobalTheory.HSApp.hodge_bundle_nef_and_big <;> assumption)
end
