import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymmOfKsCoc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LogDerivativePrincipalPolarisationIndependent
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvFieldBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKsCocOfKsRel
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KSRelSymm

theorem fieldCompat : ∀ {R : Type} [CommRing R] {K : Type} [Field K] (x₀ : R →+* K) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] (m : A.left ⟶ G.left), IsGrpPullback A G (spMap x₀) m → ∀ (w : TanM (𝟙 (Sp R)) G) (e : Fld G.left), IsInv G w e → ∀ (v : epsR K ⟶ A), IsTangent v → v.left ≫ m = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR x₀) ≫ (tv w).left → ∀ (dd : ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)), GlobalTheory.KS.IsInvDer v dd → ∀ (O : G.left.Opens) (f : Γ(G.left, O)), dd (m ⁻¹ᵁ O) ((m.app O).hom f) = pbT m (e O f) (m ⁻¹ᵁ O) := @GlobalTheory.Heat.FieldCompat.invField_baseChange

theorem cechData : ∀ {R : Type} [CommRing R] {K : Type} [Field K] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) {A : Over (Sp K)} [GrpObj A] (m : A.left ⟶ P.A.left), m ≫ P.A.hom = A.hom ≫ spMap x₀ → ∀ {g : ℕ} (e : Fin g → Fld P.A.left) (dd : Fin g → ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)), (∀ a, IsField ⊤ (e a)) → (∀ a (O : P.A.left.Opens) (f : Γ(P.A.left, O)), dd a (m ⁻¹ᵁ O) ((m.app O).hom f) = pbT m (e a O f) (m ⁻¹ᵁ O)) → ∀ (D : Derivation ℤ R R) (M : Matrix (Fin g) (Fin g) R), KSRel P.A (𝟙 P.A.left) P.L e ⇑D M → ∃ L : LB P.A.left, Finite L.ι ∧ L.IsLB ∧ (∀ i, IsAffineOpen (L.U i)) ∧ LBIso P.L L ∧ ∃ d : L.ι → ∀ O : P.A.left.Opens, Γ(P.A.left, O) → Γ(A.left, m ⁻¹ᵁ O), ∀ φ, GlobalTheory.KS.IsDlog m L dd φ → GlobalTheory.KS.KSCoc A.hom P.A.hom m (fun r => x₀ (D r)) L.U dd d (fun a => GlobalTheory.KS.lc A.hom (fun b => -x₀ (M a b)) φ) := @GlobalTheory.KSCechData.exists_ksCoc_of_ksRel

theorem ksRel_symm : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (P : Out.PolAV (Sp R)) (g : ℕ) (w : Module.Basis (Fin g) R (TanM (𝟙 (Sp R)) P.A)) (e : Fin g → Fld P.A.left), (∀ c, IsInv P.A (w c) (e c)) → ∀ (D : Derivation ℤ R R) (M : Matrix (Fin g) (Fin g) R), KSRel P.A (𝟙 P.A.left) P.L e ⇑D M → Mᵀ = M := by
  intro R _ _ _ _ _ _ P g w e he D M hKS
  let K := FractionRing R
  let x₀ : R →+* K := algebraMap R K
  let P₀ : Out.PolAV (Sp K) := GlobalTheory.StrictPull.polPull P (spMap x₀)
  let m : P₀.A.left ⟶ P.A.left := pullback.fst P.A.hom (spMap x₀)
  have hm : IsGrpPullback P₀.A P.A (spMap x₀) m := isGrpPullback_pullback P.A (spMap x₀)
  have := P.isAb.comm
  have := P₀.isAb.comm
  have hs : Smooth P.A.hom := P.isAb.smooth
  obtain ⟨u, hu, hul⟩ := GlobalTheory.Heat.CoeffWt.exists_isLieBasis w
  obtain ⟨v, hv, hvl⟩ := GlobalTheory.exists_isLieBasis_baseChange R K x₀ P.A P₀.A m hm hs g u hu
  choose dd hdd using fun a => (GlobalTheory.KS.InvField.main K P₀.A (v a) (hv.1 a)).1
  have hcomp : ∀ a (O : P.A.left.Opens) (f : Γ(P.A.left, O)), dd a (m ⁻¹ᵁ O) ((m.app O).hom f) = pbT m (e a O f) (m ⁻¹ᵁ O) :=
    fun a => fieldCompat x₀ m hm (w a) (e a) (he a) (v a) (hv.1 a) (by rw [hvl, hul]) (dd a) (hdd a)
  obtain ⟨L, hfin, hL, haff, hPL, d, hd⟩ := cechData x₀ P m hm.1.w e dd (fun a => (he a).1) hcomp D M hKS
  have hI : LBIso P₀.L (L.pull m) :=
    LBIso.trans P₀.isLB (pull_isLB P.isLB m) (pull_isLB hL m) (GlobalTheory.PolBaseChange.lbIso_refl P₀.isLB)
      (hPL.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl))
  obtain ⟨⟨φ, hφ⟩, hφ'⟩ := GlobalTheory.KS.DlogPol.dlog_independent K P₀ g v dd hv hdd _ m L hL hI
  obtain ⟨Θ', hsy, hΘ'⟩ := GlobalTheory.KS.Sym.exists_symm_of_ksCoc GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1
    GlobalTheory.Moduli.cube_of_isLB K P₀ g v dd hv hdd R x₀ P m L _ d _ φ hm hL haff hI (hd φ hφ) hφ
  have e1 : Θ' = -M.map x₀ := by
    rw [eq_comm, ← sub_eq_zero]
    funext b
    refine (hφ' φ hφ).2 _ ?_
    rw [GlobalTheory.LogKSBal.lc_sub]
    exact hΘ' b
  have h1 : (M.map x₀)ᵀ = M.map x₀ := by
    have h : Θ'ᵀ = Θ' := hsy
    rwa [e1, Matrix.transpose_neg, neg_inj] at h
  ext a b
  have := congrFun (congrFun h1 a) b
  simp only [Matrix.transpose_apply, Matrix.map_apply] at this
  exact IsFractionRing.injective R K this

end GlobalTheory.KSRelSymm
