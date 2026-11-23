import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ThetaPointDeterminesPolarisedLevel
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsRelAcyclicPolAVBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAbelianFibreIsoOfMatchedTorsionTheta
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqOneOfIsGrpPullbackOfInjectiveDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingSpreadPointsEqSpreadRootStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStructureGeometricFibrePullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointPowEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPtFibreSpreadModelAtFieldPointStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCore

theorem linComb_hom {S S' : Scheme.{0}} {A T : Over S} {A' T' : Over S'} [GrpObj A] [GrpObj A']
    (f : (T ⟶ A) →* (T' ⟶ A')) {r : ℕ} (y : Fin r → (T ⟶ A)) (a : Fin r → ℕ) :
    f (linComb y a) = linComb (fun i => f (y i)) a := by
  have h := map_list_prod f (List.ofFn fun i => y i ^ a i)
  rw [List.map_ofFn] at h
  exact h.trans (congrArg List.prod (congrArg List.ofFn (funext fun i => map_pow f (y i) (a i))))

theorem comp_linComb' {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (U : T' ⟶ T) {r : ℕ} (y : Fin r → (T ⟶ A))
    (a : Fin r → ℕ) : U ≫ linComb y a = linComb (fun i => U ≫ y i) a :=
  linComb_hom (MonoidHom.mk' (U ≫ ·) fun x y => MonObj.comp_mul U x y) y a

theorem linComb_pow_eq_one {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {r : ℕ} (y : Fin r → (T ⟶ A))
    (a : Fin r → ℕ) (M : ℕ) (h : ∀ i, y i ^ M = 1) : linComb y a ^ M = 1 := by
  unfold linComb
  rw [List.prod_ofFn, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, Nat.mul_comm, pow_mul, h, one_pow]

theorem push_linComb {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} {T₀ : Over S} (U : T.left ⟶ T₀.left)
    (hU : U ≫ T₀.hom = T.hom ≫ f) {r : ℕ} (x : Fin r → (T ⟶ G')) (y : Fin r → (T₀ ⟶ G))
    (hxy : ∀ i, (x i).left ≫ φ = U ≫ (y i).left) (a : Fin r → ℕ) :
    (linComb x a).left ≫ φ = U ≫ (linComb y a).left := by
  let V : Over.mk (T.hom ≫ f) ⟶ T₀ := Over.homMk U hU
  have e : pushHom h T (linComb x a) = V ≫ linComb y a := by
    rw [linComb_hom, comp_linComb']
    exact congrArg (linComb · a) (funext fun i => Over.OverMorphism.ext (hxy i))
  exact congrArg (fun z => z.left) e

theorem unitOn_zpow {R : Type} [CommRing R] (c : Rˣ) (e : ℤ) : unitOn (c ^ e) = unitOn c ^ e := map_zpow _ c e

theorem final_pf : ∀ (F Ω : Type) [Field F] [Field Ω] (em : F →+* Ω) (A B : PolAV (Sp Ω)) (A₀ : PolAV (Sp F)) (σ : A.A ≅ B.A) (ψ : B.A.left ⟶ A₀.A.left), GlobalTheory.IsPolIso A B σ → IsGrpPullback B.A A₀.A (spMap em) ψ → LBIso B.L (A₀.L.pull ψ) → ∃ a : A.A.left ⟶ A₀.A.left, IsGrpPullback A.A A₀.A (spMap em) a ∧ LBIso A.L (A₀.L.pull a) := by
  intro F Ω _ _ em A B A₀ σ ψ hσ h hLB
  haveI := hσ.1
  obtain ⟨w, hw⟩ := hσ.2
  refine ⟨σ.hom.left ≫ ψ, ((isGrpPullback_of_iso σ).comp h).congr (Category.id_comp _) rfl, ?_⟩
  exact LBIso.trans A.isLB (pull_isLB B.isLB _) (pull_isLB A₀.isLB _) (LBIso.symm ⟨w, hw⟩)
    (GlobalTheory.ArcDataDescent.lbIso_pull hLB σ.hom.left rfl)

theorem fibre_descends : ∀ (F Ω T : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field Ω] [IsAlgClosed Ω] [CommRing T] [IsDomain T] [Algebra F T] (em : F →+* Ω) (jT : T →+* Ω) (t : T →ₐ[F] F), Algebra.FiniteType F T → Function.Injective jT → jT.comp (algebraMap F T) = em → ∀ (A : PolAV (Sp Ω)) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap jT) φ → LBIso A.L (P.L.pull φ) → ∀ (n J : ℕ), n.Prime → Odd n → 4 ≤ J → ((n ^ 2) ^ 2) ^ A.g * A.g.factorial < n ^ J → ∀ (ζ : Fˣ) (lev : Level A ((n ^ J) ^ 2) (unitOn (Units.map em.toMonoidHom ζ))) (y₀ : Fin (2 * A.g) → (baseOver (Sp T) ⟶ P.A)) (v' : (Fin (2 * A.g) → ZMod ((n ^ J) ^ 2)) → F), IsPrimitiveRoot ζ ((n ^ J) ^ 2) → (∀ i, (lev.pt i).left ≫ φ = spMap jT ≫ (y₀ i).left) → IsThetaPt A (n ^ J) (GlobalTheory.levelPoint lev rfl) (fun a => (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (em (v' a))) → ∃ (A₀ : PolAV (Sp F)) (a : A.A.left ⟶ A₀.A.left), IsGrpPullback A.A A₀.A (spMap em) a ∧ LBIso A.L (A₀.L.pull a) := by
  intro F Ω T _ _ _ _ _ _ _ _ em jT t hft hinj hcomp A P φ hP hL n J hn ho hJ hb ζ lev y₀ v' hζ hy hv
  obtain ⟨⟨hL1, hL2, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  have := P.isAb.comm
  haveI : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing F T
  have hgP : P.g = A.g := H1.dim_unique A.A.hom
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hP.1 P.smoothDim) A.smoothDim
    ((1 : baseOver (Sp Ω) ⟶ A.A).left (IsLocalRing.closedPoint Ω))
  have hn3 : 3 ≤ n := by
    have h2 := hn.two_le
    have : n ≠ 2 := by rintro rfl; exact absurd ho (by decide)
    omega
  have hm3 : 3 ≤ n ^ J := hn3.trans (Nat.le_self_pow (by omega) n)
  have hM0 : (n ^ J) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)
  have hF0 : (((n ^ J) ^ 2 : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 hM0
  have hΩ0 : (((n ^ J) ^ 2 : ℕ) : Ω) ≠ 0 := by rw [← map_natCast em]; exact (map_ne_zero em).2 hF0
  have hnΩ : (n : Ω) ≠ 0 := by
    rw [← map_natCast em]; exact (map_ne_zero em).2 (Nat.cast_ne_zero.2 hn.ne_zero)
  have hyt : ∀ i, y₀ i ^ ((n ^ J) ^ 2) = 1 := fun i =>
    GlobalTheory.T.pow_eq_one_of_isGrpPullback_of_injective_domain Ω T jT hinj A P φ hP (lev.pt i) (y₀ i) _ (hy i) (lev.torsion i)
  let ζT : Tˣ := Units.map (algebraMap F T).toMonoidHom ζ
  have hjζ : Units.map jT.toMonoidHom ζT = Units.map em.toMonoidHom ζ := by
    ext; simp [ζT, ← hcomp]
  have hpair : ∀ i j, WeilIs P.A P.L (((n ^ J) ^ 2 : ℕ) : ℤ) (y₀ i) (y₀ j) (unitOn ζT ^ stdSymp A.g i j) := fun i j => by
    have := GlobalTheory.T.commutatorPairing_spread_points_eq_spread_root Ω T jT hinj A P φ hP hL ((n ^ J) ^ 2) (lev.pt i) (lev.pt j) (y₀ i) (y₀ j) (ζT ^ stdSymp A.g i j)
      (Nat.one_le_iff_ne_zero.2 hM0) (hy i) (hy j) (hyt i) (hyt j)
      (by rw [map_zpow, hjζ, unitOn_zpow]; exact lev.pairing i j)
    rwa [unitOn_zpow] at this
  let tR : T →+* F := t.toRingHom
  have htζ : Units.map tR.toMonoidHom ζT = ζ := by ext; simp [ζT, tR]
  let A₀ := GlobalTheory.AmpleSymModel.polPull P (spMap tR)
  let ψ₀ : A₀.A.left ⟶ P.A.left := pullback.fst P.A.hom (spMap tR)
  have hA₀ : IsGrpPullback A₀.A P.A (spMap tR) ψ₀ := isGrpPullback_pullback P.A (spMap tR)
  have hLA₀ : LBIso A₀.L (P.L.pull ψ₀) := PolBaseChange.lbIso_refl (pull_isLB P.isLB _)
  obtain ⟨levF, hlevF⟩ := GlobalTheory.T.exists_level_structure_geometric_fibre_pullback T F tR P A₀ ψ₀ hA₀ hLA₀ A.g ((n ^ J) ^ 2) hgP ζT ζ hF0 htζ hζ y₀ hyt hpair
  have cover : ∀ z : Over.mk (spMap t.toRingHom) ⟶ P.A, z ^ (n ^ J) = 1 →
      ∃ a : Fin (2 * A.g) → ZMod ((n ^ J) ^ 2),
      ((Over.homMk (spMap t.toRingHom) : Over.mk (spMap t.toRingHom) ⟶ baseOver (Sp T)) ≫
        linComb y₀ (fun i => (a i).val)) ^ (n ^ J) = z := by
    intro z hz
    obtain ⟨e, he⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hA₀ (𝟙 (Sp F)) (spMap tR) (Category.id_comp _).symm
    obtain ⟨a, ha⟩ := GlobalTheory.T.exists_levelPoint_pow_eq' F A₀ (n ^ J) A.g hgP _ levF (e.symm z) (by omega) (by rw [← map_pow, hz, map_one])
    refine ⟨a, ?_⟩
    have key : e (GlobalTheory.levelPoint levF hgP a) =
        (Over.homMk (spMap t.toRingHom) : Over.mk (spMap t.toRingHom) ⟶ baseOver (Sp T)) ≫
          linComb y₀ (fun i => (a i).val) := by
      apply Over.OverMorphism.ext
      refine (he _).trans ((congrArg (fun z => z.left ≫ ψ₀) (GlobalTheory.ThetaPtDet.levelPoint_eq levF hgP a)).trans ?_)
      exact push_linComb hA₀ (T := baseOver (Sp F)) (T₀ := baseOver (Sp T)) (spMap tR) (by simp) _ _ hlevF _
    rw [← key, ← map_pow, ha, MulEquiv.apply_symm_apply]
  have hxF : ∀ a : Fin (2 * A.g) → ZMod ((n ^ J) ^ 2), (GlobalTheory.levelPoint lev rfl a).left ≫ φ =
      spMap jT ≫ (linComb y₀ (fun i => (a i).val)).left := fun a =>
    (congrArg (fun z => z.left ≫ φ) (GlobalTheory.ThetaPtDet.levelPoint_eq lev rfl a)).trans
      (push_linComb hP (T := baseOver (Sp Ω)) (T₀ := baseOver (Sp T)) (spMap jT) (by simp) _ _ hy _)
  have thF : IsThetaPt P (n ^ J)
      (fun a : Fin (2 * A.g) → ZMod ((n ^ J) ^ 2) =>
        (Over.homMk (spMap t.toRingHom) : Over.mk (spMap t.toRingHom) ⟶ baseOver (Sp T)) ≫
          linComb y₀ (fun i => (a i).val))
      (fun a => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (v' a)) :=
    GlobalTheory.T.isThetaPt_fibre_spread_model_at_fieldPoint F Ω T em jT t hft hinj hcomp A P φ hP hL (n ^ J) (Fin (2 * A.g) → ZMod ((n ^ J) ^ 2))
      (GlobalTheory.levelPoint lev rfl) (fun a => linComb y₀ (fun i => (a i).val)) v' ho.pow hm3 hxF
      (fun a => linComb_pow_eq_one _ _ _ hyt) cover hv
  let B := GlobalTheory.AmpleSymModel.polPull A₀ (spMap em)
  let ψ₁ : B.A.left ⟶ A₀.A.left := pullback.fst A₀.A.hom (spMap em)
  have hB₁ : IsGrpPullback B.A A₀.A (spMap em) ψ₁ := isGrpPullback_pullback A₀.A (spMap em)
  have hLB₁ : LBIso B.L (A₀.L.pull ψ₁) := PolBaseChange.lbIso_refl (pull_isLB A₀.isLB _)
  have hsp : spMap em ≫ spMap tR = spMap (em.comp tR) := by simp [spMap, ← Spec.map_comp]
  have hB : IsGrpPullback B.A P.A (spMap em ≫ spMap tR) (ψ₁ ≫ ψ₀) := hB₁.comp hA₀
  have hLB : LBIso B.L (P.L.pull (ψ₁ ≫ ψ₀)) := GlobalTheory.ArcDataDescent.lbIso_pull_pull P.isLB ψ₀ ψ₁ rfl
  have hBζ : Units.map (em.comp tR).toMonoidHom ζT = Units.map em.toMonoidHom ζ := by ext; simp [ζT, tR]
  obtain ⟨levB, hlevB⟩ := GlobalTheory.T.exists_level_structure_geometric_fibre_pullback T Ω (em.comp tR) P B (ψ₁ ≫ ψ₀) (hB.congr hsp rfl) hLB A.g ((n ^ J) ^ 2) hgP ζT _
    hΩ0 hBζ (hζ.map_of_injective (Units.map_injective (f := em.toMonoidHom) em.injective)) y₀ hyt hpair
  have thΩ := GlobalTheory.Ex.Specialise.isThetaPt_map hL2 P em (x := spMap em ≫ spMap tR) rfl thF
  have key : ∀ (s : Sp Ω ⟶ Sp T) (_ : s = (baseOver (Sp Ω)).hom ≫ (spMap em ≫ spMap tR))
      (x₀ : (Fin (2 * A.g) → ZMod ((n ^ J) ^ 2)) → (Over.mk s ⟶ P.A))
      (v : (Fin (2 * A.g) → ZMod ((n ^ J) ^ 2)) → Γ(Sp Ω, ⊤)),
      (∀ a, (x₀ a).left = (GlobalTheory.levelPoint levB hgP a).left ≫ (ψ₁ ≫ ψ₀)) → IsThetaPt P (n ^ J) x₀ v →
      IsThetaPt B (n ^ J) (GlobalTheory.levelPoint levB hgP) v := by
    rintro s rfl x₀ v hx h
    have := B.isAb.comm
    exact (GlobalTheory.ThetaPtUp.isThetaPt_iff (T := baseOver (Sp Ω)) hB hLB hx
      (fun a => (congrArg (· ^ ((n ^ J) ^ 2)) (GlobalTheory.ThetaPtDet.levelPoint_eq levB hgP a)).trans
        (linComb_pow_eq_one _ _ _ fun i => levB.torsion _)) v).2 h
  have thB := key _ (Category.id_comp _).symm _ _ (fun a => by
    refine Eq.symm ((congrArg (fun z => z.left ≫ (ψ₁ ≫ ψ₀)) (GlobalTheory.ThetaPtDet.levelPoint_eq levB hgP a)).trans ?_)
    refine (push_linComb hB (T := baseOver (Sp Ω)) (T₀ := baseOver (Sp T)) (spMap em ≫ spMap tR) (by simp) _ _
      (fun i => (hlevB i).trans (by rw [hsp])) _).trans ?_
    simp only [Over.comp_left, Over.homMk_left, Category.assoc]) thΩ
  have hN' : n ^ J = n ^ (J - 4) * (n ^ 2) ^ 2 := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.thetaPt_determines hL1 A.g n 2 (J - 4) ((n ^ 2) ^ 2) (n ^ J) hn ho le_rfl rfl hN' hb Ω hnΩ
    A B rfl hgP _ lev levB _ hv thB
  exact ⟨A₀, final_pf F Ω em A B A₀ σ ψ₁ hσ hB₁ hLB₁⟩

end GlobalTheory.MumCore
