import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCoverFormsMulComponentFunction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CurveOverOfRayIn
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalApprox
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsDetRootFinPartOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrincipalRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicCompletionIntegersLeIntAE

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistRat

theorem curveOver_of_rayIn : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (Q : Par D), Q.PinHost → ∀ (N : ℕ), 3 ≤ N → ∀ (Fc : IntermediateField ℚ ℂ) (σ : Fc →+* ℂ), RayIn D N σ.fieldRange → GlobalTheory.CompRat.CurveOver Q.H Fc N := GlobalTheory.TwistRat.Field.curveOver_of_rayIn

theorem twist_mem_fieldRange : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ g, dd g ∈ σ.fieldRange := GlobalTheory.TwistValues.mem_fieldRange

theorem twist_eq_of_finHom : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ h h' : GA D V, finHom V h = finHom V h' → dd h = dd h' := GlobalTheory.TwistFinPart.twist_eq_of_finHom

theorem twist_mul_left : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ γ ∈ GQ V, ∀ h : GA D V, dd (γ * h) = dd h := GlobalTheory.TwistLeft.twist_left

theorem twist_mul_right : ∀ (D : D7) (V : HSp D) (M pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsAuxiliarySplitSquarefreeLevel D M pd → IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ u : GA D V, Formalism.L2.Pj.gLat V u = ↑(Formalism.L2.Pj.latHat V) → GlobalTheory.Member.FinCong V (M * pd) u → ∀ h : GA D V, dd (h * u) = dd h := GlobalTheory.TwistRat.Right.dd_mul_right

theorem muVal_cast {D : D7} {V W : HSp D} (h : V = W) (χ : (AE D)ˣ →* Circle) (dd : GA D W → ℂ) (hd : MuVal W χ dd) :
    MuVal V χ (castDict h.symm dd) := by
  subst h; exact hd

theorem castDict_mul {D : D7} {V W : HSp D} (h : V = W) (dd : GA D W → ℂ) (φ : GA D V → ℂ) :
    castDict h (fun g => castDict h.symm dd g * φ g) = fun g => dd g * castDict h φ g := by
  subst h; rfl

theorem isRat_twist : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i), GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV →
    ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) R.Q (labLL D)
        (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
    ∀ u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) →
      ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GoodCover T R i C (κ i).n →
      ∀ (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist C.d.pd C.σ₂ δ δc →
      ∀ dd : GA D (Wc D i) → ℂ, MuVal (Wc D i) δc dd ∨ MuVal (Wc D i) δc⁻¹ dd →
      ∀ φ : GA D (Wc D i) → ℂ, IsRat T i hV C (κ i) φ → IsRat T i hV C (κ i) (fun g => dd g * φ g) := by
  intro hRF D G _ _ Pl0 T0 A T _ R F κ v₀ hL hLev hGrp hFam hMod hThP hTie i hV hFP gramR c0R c0L hFT u hu C hGC δ δc hTw dd hdd φ hφ
  obtain ⟨hU, -, hAux, -, hRay⟩ := hGC
  obtain ⟨φ', hφ', rfl⟩ := hφ
  have hlev : C.d.l₂.M = T.Q.l.M * C.d.pd := hU.1.2.1
  have hpd : 0 < C.d.pd := hAux.1.pos
  have hN3 : 3 ≤ T.Q.l.M * C.d.pd := le_trans T.Q.l.three_le (Nat.le_mul_of_pos_right _ hpd)
  have hcurve : GlobalTheory.CompRat.CurveOver T.Q.H C.d.c₂.F (T.Q.l.M * C.d.pd) :=
    curveOver_of_rayIn hRF D T.Q hL.pins.1 _ hN3 C.d.c₂.F C.σ₂ hRay
  set dd' : GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ := castDict hV.symm dd with hdd'
  have hdd2 : MuVal _ δc dd' ∨ MuVal _ δc⁻¹ dd' :=
    hdd.imp (muVal_cast hV δc dd) (muVal_cast hV δc⁻¹ dd)
  have hval := twist_mem_fieldRange D _ C.d.pd _ C.σ₂ δ δc hTw dd' hdd2
  choose w hw using fun g => RingHom.mem_fieldRange.1 (hval g)
  have hinj : ∀ g g', dd' g = dd' g' → w g = w g' := fun g g' h => C.σ₂.injective (by rw [hw, hw, h])
  have key := (GlobalTheory.CoverComp.forms_mul_comp D T hL ((i : ℕ) + 1) ⟨Nat.succ_pos _, i.2⟩ T.σ₀ rfl C hU
    (T.Q.l.M * C.d.pd) (Nat.mul_pos (by have := T.Q.l.three_le; omega) hpd) (by rw [hlev]) (Or.inr hcurve) w
    (fun h h' hh => hinj _ _ (twist_eq_of_finHom D _ C.d.pd _ C.σ₂ δ δc hTw dd' hdd2 h h' hh))
    (fun γ hγ h => hinj _ _ (twist_mul_left D _ C.d.pd _ C.σ₂ δ δc hTw dd' hdd2 γ hγ h))
    (fun u hu1 hu2 h => hinj _ _ (twist_mul_right D _ T.Q.l.M C.d.pd _ C.σ₂ δ δc hAux hTw dd' hdd2 u hu1 (hlev ▸ hu2) h))
    (wtA (κ i)) (κ i).n).1 φ' hφ'
  refine ⟨_, key, ?_⟩
  simp only [hw]
  exact castDict_mul hV dd φ'

end GlobalTheory.TwistRat
