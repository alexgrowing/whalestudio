import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConnK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAVInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechOneCoboundaryOfRefinementStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LogDerivativePrincipalPolarisationIndependent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueInvariantVectorFieldOfTangent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CohomologyLogDerivativeAdjointEndomorphisms
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmTensorSmoothOfRelativeDimension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisedModel
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatConn.Vert
open GlobalTheory.KS

theorem transport {k : Type} [Field k] {R : Type} [CommRing R] (A : Over (Sp R)) (L : LB A.left)
    (A₀ B₀ : Over (Sp k)) (m₀ : A₀.left ⟶ A.left) (e : B₀.left ⟶ A₀.left) (he : e ≫ A₀.hom = B₀.hom)
    (D' : R → k) {J : Type} (V : J → A.left.Opens) (jj : J → L.ι)
    (v : ∀ W : A.left.Opens, Γ(A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (q : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i))
    (hc : GlobalTheory.HeatConn.IsConnK A L A₀ m₀ D' V jj v q) :
    GlobalTheory.HeatConn.IsConnK A L B₀ (e ≫ m₀) D' V jj (fun W f => pbT e (v W f) ((e ≫ m₀) ⁻¹ᵁ W))
      (fun i => pbT e (q i) ((e ≫ m₀) ⁻¹ᵁ V i)) := by
  obtain ⟨hd, hcov, hle, htr⟩ := hc
  have le : ∀ W : A.left.Opens, (e ≫ m₀) ⁻¹ᵁ W ≤ e ⁻¹ᵁ (m₀ ⁻¹ᵁ W) := fun W => le_rfl
  have app : ∀ W (f : Γ(A.left, W)), pbT e ((m₀.app W).hom f) ((e ≫ m₀) ⁻¹ᵁ W) = ((e ≫ m₀).app W).hom f := by
    intro W f
    rw [AdjDlog.app_eq_pbT m₀, AdjDlog.app_eq_pbT (e ≫ m₀), AdjDlog.pbT_pbT e m₀ le_rfl (le W)]
  refine ⟨⟨fun W _ f f' => ?_, fun W _ f f' => ?_, fun W W' h _ f => ?_, fun W _ r => ?_⟩, hcov, hle, fun i i' => ?_⟩
  · simp only [hd.add W le_top, pbT_add]
  · rw [hd.mul W le_top, pbT_add, pbT_mul, pbT_mul, app, app]
  · show pbT e (v W' (resG A.left h f)) _ = rsT (pbT e (v W f) _) _
    rw [hd.res W W' h le_top, pbT_rsT e (m₀.preimage_mono h) (le W'), rsT_pbT e (le W) ((e ≫ m₀).preimage_mono h)]
  · show pbT e (v W (constFn A.hom W r)) _ = _
    rw [hd.base W le_top, pbT_constFn A₀.hom e (le W), he]
  · show pbT e (v (V i ⊓ V i') _) _ = _
    rw [htr i i', pbT_mul, pbT_sub, AdjDlog.pbT_pbT e m₀ (m₀.preimage_mono (le_inf (inf_le_left.trans (hle i)) (inf_le_right.trans (hle i')))) (le _),
      pbT_rsT e (m₀.preimage_mono inf_le_left) (le _), pbT_rsT e (m₀.preimage_mono inf_le_right) (le _),
      rsT_pbT e (le _) ((e ≫ m₀).preimage_mono inf_le_left), rsT_pbT e (le _) ((e ≫ m₀).preimage_mono inf_le_right)]

theorem coeff_const (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (x₀ : R →+* k)
    (P₀ : PolAV (Sp k)) (θ : P₀.A.left ⟶ P.A.left) (hθ : IsPullback θ P₀.A.hom P.A.hom (spMap x₀))
    {n : ℕ} (u : Fin n → (epsR k ⟶ P₀.A)) (hu : IsLieBasis u)
    (dd : Fin n → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)) (hdd : ∀ a, IsInvDer (u a) (dd a))
    (v : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(P₀.A.left, θ ⁻¹ᵁ W))
    (hv : LocDerK P₀.A.hom P.A.hom θ (fun _ => (0 : k)) ⊤ v) :
    ∃ c : Fin n → k, ∀ W f, v W f = ∑ a, constFn P₀.A.hom (θ ⁻¹ᵁ W) (c a) * dd a (θ ⁻¹ᵁ W) ((θ.app W).hom f) := by
  have hs : Smooth P₀.A.hom := P₀.isAb.smooth
  have hU : IsAffineOpen (⊤ : (Sp R).Opens) := isAffineOpen_top _
  obtain ⟨c0, hc0, -⟩ := GlobalTheory.KSUniq.coeff_id hs hu hdd (spMap x₀) P.A.hom θ hθ hU ⊤ (fun _ _ => trivial) v
    (fun W _ => hv.add W le_top) (fun W _ => hv.mul W le_top) (fun W W' h _ => hv.res W W' h le_top) (fun W _ r => by
      have e1 : pbT P.A.hom r W = constFn P.A.hom W ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) := by
        rw [pbT_of_le _ (by simp)]
        simp [constFn]
      rw [e1, hv.base W le_top]
      simp [constFn])
  have hGF := GlobalTheory.allSixLaws.1.globalFns
  choose s hs' using fun a => (hGF _ P₀.A P₀.isAb).2 (rsT (c0 a) ⊤)
  refine ⟨fun a => (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom (s a), fun W f => ?_⟩
  rw [hc0 W le_top f]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [← rsT_rsT (O₁ := ⊤) (by simp) le_top, ← hs' a, rsT_of_le le_top]
  simp [constFn]
  rfl

theorem cob_of_conn (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R))
    (P₀ : PolAV (Sp k)) (θ : P₀.A.left ⟶ P.A.left)
    {n : ℕ} (u : Fin n → (epsR k ⟶ P₀.A)) (hu : IsLieBasis u)
    (dd : Fin n → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)) (hdd : ∀ a, IsInvDer (u a) (dd a))
    (φ : Fin n → C1 (fun i => θ ⁻¹ᵁ P.L.U i)) (hφ : IsDlog θ P.L dd φ) (hcoc : ∀ a, IsCoc _ (φ a))
    {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι)
    (v : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(P₀.A.left, θ ⁻¹ᵁ W)) (q : ∀ i, Γ(P₀.A.left, θ ⁻¹ᵁ V i))
    (hc : GlobalTheory.HeatConn.IsConnK P.A P.L P₀.A θ (fun _ => 0) V jj v q) (c : Fin n → k)
    (hcv : ∀ W f, v W f = ∑ a, constFn P₀.A.hom (θ ⁻¹ᵁ W) (c a) * dd a (θ ⁻¹ᵁ W) ((θ.app W).hom f)) :
    IsCob _ (lc P₀.A.hom c φ) := by
  obtain ⟨-, hcov, hle, htr⟩ := hc
  have hres : ∀ a, ∀ W W' (f : Γ(P₀.A.left, W)), W' ≤ W → dd a W' (rsT f W') = rsT (dd a W f) W' :=
    fun a => ((GlobalTheory.KS.InvField.main k P₀.A (u a) (hu.1 a)).2 (dd a) (hdd a)).2.2.1
  have hcovθ : ⨆ p, θ ⁻¹ᵁ V p = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    have hz : θ z ∈ ⨆ i, V i := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  refine GlobalTheory.T.isCechOneCoboundary_of_refinement (fun i => θ ⁻¹ᵁ P.L.U i) (lc P₀.A.hom c φ) (GlobalTheory.KSUniq.isCoc_lc _ _ _ hcoc)
    (fun p => θ ⁻¹ᵁ V p) jj (fun p => θ.preimage_mono (hle p)) hcovθ q (fun p p' => ?_)
  have hWU : V p ⊓ V p' ≤ P.L.U (jj p) ⊓ P.L.U (jj p') := le_inf (inf_le_left.trans (hle p)) (inf_le_right.trans (hle p'))
  have hOU : θ ⁻¹ᵁ (V p ⊓ V p') ≤ θ ⁻¹ᵁ P.L.U (jj p) ⊓ θ ⁻¹ᵁ P.L.U (jj p') := θ.preimage_mono hWU
  change rsT (lc P₀.A.hom c φ (jj p) (jj p')) (θ ⁻¹ᵁ (V p ⊓ V p')) =
    rsT (q p') (θ ⁻¹ᵁ (V p ⊓ V p')) - rsT (q p) (θ ⁻¹ᵁ (V p ⊓ V p'))
  have E := htr p p'
  rw [hcv] at E
  set g := (P.L.g (jj p) (jj p')).val with hg
  have r1 : rsT (pbT θ g (θ ⁻¹ᵁ P.L.U (jj p) ⊓ θ ⁻¹ᵁ P.L.U (jj p'))) (θ ⁻¹ᵁ (V p ⊓ V p')) = pbT θ g (θ ⁻¹ᵁ (V p ⊓ V p')) :=
    rsT_pbT θ (O₀ := P.L.U (jj p) ⊓ P.L.U (jj p')) (O₁ := θ ⁻¹ᵁ P.L.U (jj p) ⊓ θ ⁻¹ᵁ P.L.U (jj p')) le_rfl hOU _
  have e1 : (θ.app (V p ⊓ V p')).hom (rsT g (V p ⊓ V p')) =
      rsT (pbT θ g (θ ⁻¹ᵁ P.L.U (jj p) ⊓ θ ⁻¹ᵁ P.L.U (jj p'))) (θ ⁻¹ᵁ (V p ⊓ V p')) := by
    rw [AdjDlog.app_eq_pbT, pbT_rsT θ hWU le_rfl, r1]
  have e2 : ∀ a, dd a (θ ⁻¹ᵁ (V p ⊓ V p')) ((θ.app (V p ⊓ V p')).hom (rsT g (V p ⊓ V p'))) =
      pbT θ g (θ ⁻¹ᵁ (V p ⊓ V p')) * rsT (φ a (jj p) (jj p')) (θ ⁻¹ᵁ (V p ⊓ V p')) := fun a => by
    rw [e1, hres a _ _ _ hOU, ← hφ a (jj p) (jj p'), rsT_mul, r1]
  simp only [e2] at E
  have hunit : IsUnit (pbT θ g (θ ⁻¹ᵁ (V p ⊓ V p'))) := AdjDlog.isUnit_pbT θ (θ.preimage_mono hWU) _
  refine (hunit.mul_left_cancel ?_).symm
  rw [← E, lc, rsT_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rsT_mul, rsT_constFn _ hOU]
  ring

theorem vert_polAV (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (x₀ : R →+* k)
    (P₀ : PolAV (Sp k)) (θ : P₀.A.left ⟶ P.A.left) (hθ : IsPullback θ P₀.A.hom P.A.hom (spMap x₀))
    (hiso : LBIso P₀.L (P.L.pull θ)) {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι)
    (v : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(P₀.A.left, θ ⁻¹ᵁ W)) (q : ∀ i, Γ(P₀.A.left, θ ⁻¹ᵁ V i))
    (hc : GlobalTheory.HeatConn.IsConnK P.A P.L P₀.A θ (fun _ => 0) V jj v q) (W : P.A.left.Opens) (f : Γ(P.A.left, W)) :
    v W f = 0 := by
  haveI : IsCommMonObj P₀.A := P₀.isAb.comm
  obtain ⟨u, hu⟩ := GlobalTheory.CM.TenDim.exists_isLieBasis P₀.A P₀.smoothDim
  choose dd hdd using fun a => (GlobalTheory.KS.InvField.main k P₀.A (u a) (hu.1 a)).1
  obtain ⟨⟨φ, hφ⟩, hind⟩ := GlobalTheory.KS.DlogPol.dlog_independent k P₀ P₀.g u dd hu hdd _ θ P.L P.isLB hiso
  obtain ⟨hcoc, hcob⟩ := hind φ hφ
  obtain ⟨c, hcv⟩ := coeff_const k R P x₀ P₀ θ hθ u hu dd hdd v hc.1
  have c0 := hcob c (cob_of_conn k R P P₀ θ u hu dd hdd φ hφ hcoc V jj v q hc c hcv)
  rw [hcv]
  simp [c0, constFn]

theorem vert_eq_zero : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (x₀ : R →+* k) (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap x₀) m₀ → ∀ {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι) (v : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (q : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), GlobalTheory.HeatConn.IsConnK P.A P.L A₀ m₀ (fun _ => 0) V jj v q → ∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), v W f = 0 := by
  intro k _ R _ P x₀ A₀ _ m₀ hm J V jj v q hc W f
  obtain ⟨P₀, θ, hθ, hiso⟩ := GlobalTheory.UniformisedModel.exists_polBaseChange GlobalTheory.allSixLaws.1.polBaseChange (spMap x₀) P
  obtain ⟨e, -, he⟩ := grpPullback_iso hθ hm
  subst he
  have hw : e.hom.left ≫ A₀.hom = P₀.A.hom := Over.w e.hom
  have hc' := transport P.A P.L A₀ P₀.A m₀ e.hom.left hw (fun _ => 0) V jj v q hc
  have h0 := vert_polAV k R P x₀ P₀ _ hθ.1 hiso V jj _ _ hc' W f
  haveI : IsIso e.hom.left := ⟨⟨e.inv.left, by rw [← Over.comp_left, e.hom_inv_id, Over.id_left],
    by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]⟩⟩
  have hle : m₀ ⁻¹ᵁ W ≤ (inv e.hom.left) ⁻¹ᵁ ((e.hom.left ≫ m₀) ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, IsIso.inv_hom_id_assoc]
  have key := congrArg (fun s => pbT (inv e.hom.left) s (m₀ ⁻¹ᵁ W)) h0
  rw [AdjDlog.pbT_pbT (inv e.hom.left) e.hom.left (U := m₀ ⁻¹ᵁ W) (V := (e.hom.left ≫ m₀) ⁻¹ᵁ W) le_rfl hle, IsIso.inv_hom_id, LinDir.pbT_id, pbT_zero] at key
  exact key

end GlobalTheory.HeatConn.Vert
