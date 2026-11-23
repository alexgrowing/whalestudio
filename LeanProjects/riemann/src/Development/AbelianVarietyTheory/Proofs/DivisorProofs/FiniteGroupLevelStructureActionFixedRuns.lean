import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapAllComparison
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDetOfMemSt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLevelChangeActionOnCuspForms

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelActionOnto

def quotMap {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (f : M →ₗ[R] M) :
    (M ⧸ I • (⊤ : Submodule R M)) →ₗ[R] (M ⧸ I • (⊤ : Submodule R M)) :=
  (I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R M)) f
    (Submodule.map_le_iff_le_comap.1 (by rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top))

theorem quotMap_mk {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (f : M →ₗ[R] M) (a : M) :
    quotMap I f ((I • (⊤ : Submodule R M)).mkQ a) = (I • (⊤ : Submodule R M)).mkQ (f a) := rfl

open Classical in

def quotEquiv {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (f : M →ₗ[R] M) :
    (M ⧸ I • (⊤ : Submodule R M)) ≃ₗ[R] (M ⧸ I • (⊤ : Submodule R M)) :=
  if hb : Function.Bijective (quotMap I f) then LinearEquiv.ofBijective _ hb else LinearEquiv.refl R _

theorem quotEquiv_mk {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (f : M →ₗ[R] M)
    (hb : Function.Bijective (quotMap I f)) (a : M) :
    quotEquiv I f ((I • (⊤ : Submodule R M)).mkQ a) = (I • (⊤ : Submodule R M)).mkQ (f a) := by
  unfold quotEquiv
  rw [dif_pos hb]
  rfl

theorem quotMap_bijective {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (f f' : M →ₗ[R] M)
    (h1 : ∀ a, f (f' a) - a ∈ I • (⊤ : Submodule R M)) (h2 : ∀ a, f' (f a) - a ∈ I • (⊤ : Submodule R M)) :
    Function.Bijective (quotMap I f) := by
  have k1 : ∀ q, quotMap I f (quotMap I f' q) = q := fun q => by
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ q
    rw [quotMap_mk, quotMap_mk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact h1 a
  have k2 : ∀ q, quotMap I f' (quotMap I f q) = q := fun q => by
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ q
    rw [quotMap_mk, quotMap_mk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact h2 a
  exact ⟨Function.LeftInverse.injective k2, Function.RightInverse.surjective k1⟩

end GlobalTheory.LevelActionOnto

namespace GlobalTheory.LevelActionOnto

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem levelPin_actionPin : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (O : ∀ i, OMDat J.toCore R i Unit (fun _ => A.μ0)), GlobalTheory.Hk3.Core R F → (∀ i, OMPins J R κ v₀ O i) → RhoGeo fw O → (∀ i, OneMapRow0 J R κ v₀ O i) → J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → ∃ ℓ : ∀ i : Fin D.R.m, G → (LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l ≃ₗ[𝓞 D.host.E] LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l), ∀ (r : RunData J) (h : LawsFull r.full) (i : Fin D.R.m), letI : Algebra r.full.J.Q.c.F D.what₂.LL := ‹Algebra J.Q.c.F D.what₂.LL›; LevelPin (T := r.full) R i (ℓ i) ∧ ActionPin (T := r.full) (R := R) h.p fw i (ℓ i) := by
  intro D G _ _ Pl0 T0 A J _ R F κ v₀ fw O hc hpins hrho hrow hMb
  classical
  refine ⟨fun i g => quotEquiv J.Q.l.Mb ((O i).lev g), fun r h i => ?_⟩
  have hlev : LevIs R i (iotaW J i) J.Q.l.M (Mfr J.Q.l) (O i).lev := (hpins i).2.lift.lev
  have hι : LatEmb (Wc D i) (iotaW J i) := GlobalTheory.TraceLattice.latEmb_iotaW h i
  have hβ : IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1 := hc.lev.βW i
  obtain ⟨h1, hm⟩ := GlobalTheory.LevelActionPinned.congr_of_levIs R i hι hβ hMb hlev
  have hbij : ∀ g, Function.Bijective (quotMap J.Q.l.Mb ((O i).lev g)) := fun g => by
    refine quotMap_bijective _ _ ((O i).lev g⁻¹) (fun a => ?_) (fun a => ?_)
    · have e1 := hm g g⁻¹ a
      have e2 := h1 a
      rw [mul_inv_cancel] at e1
      have := Submodule.sub_mem _ e2 e1
      rwa [sub_sub_sub_cancel_left] at this
    · have e1 := hm g⁻¹ g a
      have e2 := h1 a
      rw [inv_mul_cancel] at e1
      have := Submodule.sub_mem _ e2 e1
      rwa [sub_sub_sub_cancel_left] at this
  have hspec : ∀ g a, liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)) a - (O i).lev g a ∈
      J.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (J.Q.Dw ((i : ℕ) + 1)).La) := fun g a => by
    rw [← Submodule.Quotient.eq]
    have := liftLa_spec (quotEquiv J.Q.l.Mb ((O i).lev g)) a
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at this
    rw [this]
    exact quotEquiv_mk _ _ (hbij g) a
  have hA : J.Q.l.A = 1 := h.j.pins.2.1.2
  refine ⟨?_, ?_⟩

  · change LevIs R i (iotaW J i) J.Q.l.M (Mfr J.Q.l) (fun g => liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)))
    intro g
    obtain ⟨k, hk, hw⟩ := hlev g
    refine ⟨k, hk, fun a ha => ?_⟩
    obtain ⟨w, hwm, e⟩ := hw a ha
    have hd : liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)) a - (O i).lev g a ∈
        (Ideal.span {(J.Q.l.M : 𝓞 D.host.E)}) • (⊤ : Submodule (𝓞 D.host.E) (J.Q.Dw ((i : ℕ) + 1)).La) := by
      rw [← J.Q.l.prod, mul_comm, Submodule.mul_smul]
      have key : ∀ f : (J.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (J.Q.Dw ((i : ℕ) + 1)).La,
          (∀ x, f x ∈ J.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (J.Q.Dw ((i : ℕ) + 1)).La)) →
          f a ∈ Mfr J.Q.l • J.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (J.Q.Dw ((i : ℕ) + 1)).La) := fun f hf => by
        refine Submodule.smul_induction_on ha (fun b hb x _ => ?_) (fun x y hx hy => ?_)
        · rw [map_smul]
          exact Submodule.smul_mem_smul hb (hf x)
        · rw [map_add]
          exact add_mem hx hy
      exact key (liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)) - (O i).lev g) (hspec g)
    rw [Submodule.ideal_span_singleton_smul] at hd
    obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hd
    have hy' : liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)) a = (O i).lev g a + J.Q.l.M • y := by
      rw [← Nat.cast_smul_eq_nsmul (𝓞 D.host.E), hy, add_sub_cancel]
    have hmem : finVec (Wc D i) (iotaW J i y) ∈ latGHat (Wc D i) 1 :=
      ((GlobalTheory.MarkCoset.latG_spec D (Wc D i) 1).1 _).1 (hι.2 ▸ LinearMap.mem_range_self (iotaW J i) y)
    refine ⟨w + finVec (Wc D i) (iotaW J i y), add_mem hwm hmem, ?_⟩
    have e2 : GlobalTheory.LevelActionPinned.fvec (Wc D i) (iotaW J i) (liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)) a) =
        GlobalTheory.LevelActionPinned.fvec (Wc D i) (iotaW J i) ((O i).lev g a) +
          J.Q.l.M • GlobalTheory.LevelActionPinned.fvec (Wc D i) (iotaW J i) y := by
      rw [hy', map_add, map_nsmul]
    have e3 : finVec (Wc D i) (iotaW J i (liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)) a)) =
        finVec (Wc D i) (iotaW J i ((O i).lev g a)) + J.Q.l.M • finVec (Wc D i) (iotaW J i y) := e2
    rw [e3, nsmul_add, ← e]
    abel

  · obtain ⟨cc, ph, hone⟩ := hrow i
    have hkeep : ActKeeps (κ := κ) O i := fun g f hf => by
      obtain ⟨k, hk, -⟩ := hlev g
      exact (hone.1 g k hk f hf).1
    have hrho' := (hrho i).1 hkeep
    have hact_eq : ∀ g, actLev (Xo := J.Q.Xo ((i : ℕ) + 1)) J.Q.c (levFull (J.Q.Dw ((i : ℕ) + 1)) J.Q.l)
        (quotEquiv J.Q.l.Mb ((O i).lev g)) = actLev J.Q.c (O i).lev2 g := fun g => by
      have e1 : actLev (Xo := J.Q.Xo ((i : ℕ) + 1)) J.Q.c (levFull (J.Q.Dw ((i : ℕ) + 1)) J.Q.l)
          (quotEquiv J.Q.l.Mb ((O i).lev g)) = actLev (Xo := J.Q.Xo ((i : ℕ) + 1)) J.Q.c
          (fun _ : Unit => levFull (J.Q.Dw ((i : ℕ) + 1)) J.Q.l (quotEquiv J.Q.l.Mb ((O i).lev g))) () := rfl
      have e2 : actLev (Xo := J.Q.Xo ((i : ℕ) + 1)) J.Q.c (O i).lev2 g =
          actLev (Xo := J.Q.Xo ((i : ℕ) + 1)) J.Q.c (fun _ : Unit => (O i).lev2 g) () := rfl
      rw [e1, e2, GlobalTheory.OneMapAllCompare.actLev_congr (lev' := fun _ : Unit => (O i).lev2 g) J.Q.c hA (fun _ a => hspec g a)]
    obtain ⟨act, hact⟩ := GlobalTheory.FormTies.exists_isLevAct D r.full.toTop h.p ((i : ℕ) + 1) (inR_succ i) (κ i) G
      (fun g => quotEquiv J.Q.l.Mb ((O i).lev g))
    refine ⟨act, hact, fun g F => ?_⟩
    obtain ⟨hf, he⟩ := hrho' g ⟨F.1, cutR_le J.toCore.C ((i : ℕ) + 1) (κ i) F.2⟩
    have e : (act g F).1 = actLev (Xo := J.Q.Xo ((i : ℕ) + 1)) J.Q.c (O i).lev2 g F.1 := (hact g F).trans (LinearMap.congr_fun (hact_eq g) F.1)
    change ((fw.e i ⟨(act g F).1, _⟩ : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) =
      (R.FW i).ρ g ((fw.e i ⟨F.1, _⟩ : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)
    rw [← he]
    congr 3

end GlobalTheory.LevelActionOnto
