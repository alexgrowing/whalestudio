import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePreservingMapGivesEndomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolUnifReparam
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ConjTangentSemilin

open GlobalTheory.ArchMetricCompare

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {p : A'.left ⟶ A.left} {g : ℂ ≃+* ℂ}

theorem isIso_spMap (g : ℂ ≃+* ℂ) : IsIso (spMap (g : ℂ →+* ℂ)) := by
  have : IsIso (CommRingCat.ofHom (g : ℂ →+* ℂ)) :=
    ⟨⟨CommRingCat.ofHom (g.symm : ℂ →+* ℂ), by ext; simp, by ext; simp⟩⟩
  unfold spMap
  infer_instance

theorem snd_pull [IsIso p] {L : LB A.left} {N : ℕ} (u : HolUnif A L N) {v : epsR ℂ ⟶ A} {v' : epsR ℂ ⟶ A'}
    (e : v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left) {w : Fin N → ℂ} (hd : u.IsDiff w v)
    (U : A'.left.Opens) (hU : ⊤ ≤ v'.left ⁻¹ᵁ U) (f : Γ(A'.left, U)) :
    (TangentOrigin.evalPt (R := DualNumber ℂ) v'.left U hU f).snd =
      g (fderiv ℂ (fun z => valAt' (u.ex z).left (inv p ⁻¹ᵁ U) (((inv p).app U).hom f)) 0 w) := by
  have e2 : v'.left = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫
      (show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ inv p := by
    rw [← Category.assoc]
    exact (IsIso.eq_comp_inv p).2 e
  have h2 : ⊤ ≤ v.left ⁻¹ᵁ (inv p ⁻¹ᵁ U) := fun q _ => by
    have := subsingleton_dual ℂ
    have hq := hU (show q ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)
    rw [e2] at hq
    rw [Subsingleton.elim (α := PrimeSpectrum (DualNumber ℂ)) q
      (spMap (Chart.dualMapR (g : ℂ →+* ℂ)) q)]
    exact hq
  have k : ∀ (y : Sp (DualNumber ℂ) ⟶ A'.left) (hy : ⊤ ≤ y ⁻¹ᵁ U),
      y = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ inv p →
      TangentOrigin.evalPt y U hy f = Chart.dualMapR (g : ℂ →+* ℂ)
        (TangentOrigin.evalPt (R := DualNumber ℂ) v.left _ h2 (((inv p).app U).hom f)) := by
    rintro _ hy rfl
    rw [TangentOrigin.evalPt_spMap_comp _ _ U h2]
    congr 1
  rw [k _ hU e2]
  have e3 := hd _ h2 (((inv p).app U).hom f)
  simp only [Chart.dualMapR, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add,
    TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
  exact congrArg g e3

def Rel {L : LB A.left} {L' : LB A'.left} {N : ℕ} (p : A'.left ⟶ A.left) [IsIso p] (g : ℂ ≃+* ℂ)
    (u : HolUnif A L N) (u' : HolUnif A' L' N) (w' w : Fin N → ℂ) : Prop :=
  ∀ (U : A'.left.Opens), ⊤ ≤ (u'.ex 0).left ⁻¹ᵁ U → ∀ f : Γ(A'.left, U),
    fderiv ℂ (fun z => valAt' (u'.ex z).left U f) 0 w' =
      g (fderiv ℂ (fun z => valAt' (u.ex z).left (inv p ⁻¹ᵁ U) (((inv p).app U).hom f)) 0 w)

theorem isDiff_iff_rel [IsIso p] (h : IsGrpPullback A' A (spMap (g : ℂ →+* ℂ)) p) {L : LB A.left} {L' : LB A'.left}
    {N : ℕ} (u : HolUnif A L N) (u' : HolUnif A' L' N) {v : epsR ℂ ⟶ A} {v' : epsR ℂ ⟶ A'} (hv : IsTangent v)
    (e : v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left) {w : Fin N → ℂ} (hd : u.IsDiff w v)
    (w' : Fin N → ℂ) : u'.IsDiff w' v' ↔ Rel p g u u' w' w := by
  have hv' : IsTangent v' := isTangent_of_pull (σ := (g : ℂ →+* ℂ)) h hv e
  constructor
  · intro hd' U hU f
    have hU' := (TangentOrigin.tangent_mem_iff (u := u') hv' U).2 hU
    exact (hd' U hU' f).symm.trans (snd_pull u e hd U hU' f)
  · intro hr U hU f
    exact (snd_pull u e hd U hU f).trans
      (hr U ((TangentOrigin.tangent_mem_iff (u := u') hv' U).1 hU) f).symm

theorem rel_add [IsIso p] {L : LB A.left} {L' : LB A'.left} {N : ℕ} (u : HolUnif A L N) (u' : HolUnif A' L' N)
    {w₁' w₁ w₂' w₂ : Fin N → ℂ} (h₁ : Rel p g u u' w₁' w₁) (h₂ : Rel p g u u' w₂' w₂) :
    Rel p g u u' (w₁' + w₂') (w₁ + w₂) := fun U hU f => by
  rw [map_add, map_add, map_add, h₁ U hU f, h₂ U hU f]

theorem rel_smul [IsIso p] {L : LB A.left} {L' : LB A'.left} {N : ℕ} (u : HolUnif A L N) (u' : HolUnif A' L' N)
    {w' w : Fin N → ℂ} (c : ℂ) (h₁ : Rel p g u u' w' w) : Rel p g u u' (g c • w') (c • w) := fun U hU f => by
  rw [map_smul, map_smul, h₁ U hU f, smul_eq_mul, smul_eq_mul, map_mul]

theorem pull_sq (g : ℂ ≃+* ℂ) (v : epsR ℂ ⟶ A) :
    (spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left) ≫ A.hom = (epsR ℂ).hom ≫ spMap (g : ℂ →+* ℂ) := by
  rw [Category.assoc, Over.w]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

def liftT (h : IsGrpPullback A' A (spMap (g : ℂ →+* ℂ)) p) (v : epsR ℂ ⟶ A) : epsR ℂ ⟶ A' :=
  Over.homMk (h.1.lift _ _ (pull_sq g v)) (h.1.lift_snd _ _ _)

theorem liftT_left (h : IsGrpPullback A' A (spMap (g : ℂ →+* ℂ)) p) (v : epsR ℂ ⟶ A) :
    (liftT h v).left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left :=
  h.1.lift_fst _ _ _

theorem exists_semilinear_transport : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (p : A'.left ⟶ A.left) (g : ℂ ≃+* ℂ),
    IsGrpPullback A' A (spMap (g : ℂ →+* ℂ)) p → ∀ (L : LB A.left) (L' : LB A'.left) (N : ℕ) (u : HolUnif A L N)
    (u' : HolUnif A' L' N), (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → (∀ v, IsTangent v → ∃! w, u'.IsDiff w v) →
    ∃ T : (Fin N → ℂ) →ₛₗ[(g : ℂ →+* ℂ)] (Fin N → ℂ), Function.Injective T ∧
      ∀ (w : Fin N → ℂ) (v : epsR ℂ ⟶ A) (v' : epsR ℂ ⟶ A'), IsTangent v →
        v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → u.IsDiff w v → u'.IsDiff (T w) v' := by
  intro A A' _ _ p g h L L' N u u' hex huniq
  haveI := isIso_spMap g
  haveI : IsIso p := h.1.isIso_fst_of_isIso
  choose vv hvv using fun w => (hex w).exists
  have ht : ∀ w, IsTangent (liftT h (vv w)) := fun w =>
    isTangent_of_pull (σ := (g : ℂ →+* ℂ)) h (hvv w).1 (liftT_left h _)
  choose T hT using fun w => (huniq _ (ht w)).exists
  have hR : ∀ w, Rel p g u u' (T w) w := fun w =>
    (isDiff_iff_rel h u u' (hvv w).1 (liftT_left h _) (hvv w).2 _).1 (hT w)
  have hU : ∀ w w', Rel p g u u' w' w → T w = w' := fun w w' hr =>
    (huniq _ (ht w)).unique (hT w) ((isDiff_iff_rel h u u' (hvv w).1 (liftT_left h _) (hvv w).2 _).2 hr)
  let Tl : (Fin N → ℂ) →ₛₗ[(g : ℂ →+* ℂ)] (Fin N → ℂ) :=
    { toFun := T
      map_add' := fun a b => hU _ _ (rel_add u u' (hR a) (hR b))
      map_smul' := fun c a => hU _ _ (rel_smul u u' c (hR a)) }
  refine ⟨Tl, ?_, ?_⟩
  · refine (injective_iff_map_eq_zero Tl).2 fun w hw => ?_
    have hw' : T w = 0 := hw
    have h0 : u'.IsDiff 0 (liftT h (vv w)) := by rw [← hw']; exact hT w
    have e1 := eq_of_isDiff u' (ht w) (isTangent_zero A') h0 (isDiff_zero u')
    have e2 := (zero_pull_iff (σ := (g : ℂ →+* ℂ)) h (liftT_left h (vv w))).1 e1
    have hd := (hvv w).2
    rw [e2] at hd
    exact eq_zero_of_isDiff u hd
  · intro w v v' hv e hd
    exact (isDiff_iff_rel h u u' hv e hd _).2 (hR w)

end GlobalTheory.ConjTangentSemilin
