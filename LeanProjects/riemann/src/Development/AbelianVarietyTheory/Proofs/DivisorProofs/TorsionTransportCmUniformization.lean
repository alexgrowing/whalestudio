import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnimodularSolCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmCurveTorsionTransportSecondPeriod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPeriodChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLFunctionEulerProductConvergentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateCurveTangentCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealValConjInvStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTwistFunctionDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralLinearCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticMapTangentDifferentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealValDifferentEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeDecompositionOfIdeleApproxStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

theorem GlobalTheory.cmTorsionConj : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left),
        X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p →
        ∀ u' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E)),
 (∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : epsR ℂ ⟶ T.X.A) (v' : epsR ℂ ⟶ X'.A),
            v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → T.U.u.IsDiff w v →
              u'.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v') → (∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            (u'.ex (fun j ↦ g (φ (T.U.e j) x'))).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) x)).left) := by
  intro hPC hAD hDC K _ _ d δ io hK hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hTT E _ _ _ _ I _ φ hCM hres c y hc 𝔠 T X' p hpb u' htan
    x x' hxx'
  have hTT' := hTT
  obtain ⟨hΩ₀, hΩ₁, hgio, hΛ₀, -, hg₂, hg₃, -⟩ := hTT'
  have hW : (curve Λ₀ Ω₀).map (g : ℂ →+* ℂ) = curve Λ₁ Ω₁ := curve_map (g : ℂ →+* ℂ) hg₂ hg₃
  obtain ⟨hU1, hE2, hE3⟩ := GlobalTheory.T.conjugate_group_points_injective_mul T.X.A X'.A g p hpb.grp
  obtain ⟨m, b, a, a', hbL, hx', hxL, hint⟩ := GlobalTheory.T.lattice_approximation_upward_idele K E t c y hc x x' hxx'
  have hlat : ∀ z ∈ lattice c y, (fun j ↦ φ (T.U.e j) z) ∈ T.U.u.Λ := fun z hz =>
    (T.U.lat _).2 ⟨z, hz, funext fun j => by simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]⟩
  have hφK : ∀ i (r : K), φ i (algebraMap K E r) = io r := fun i r => by rw [← RingHom.comp_apply, hres i]
  have hpt : ∀ z, pt Λ₁ Ω₁ z ≫ toSpec (curve Λ₁ Ω₁) = 𝟙 _ := fun z => by
    rw [pt, GlobalTheory.WeierstrassCurve.ptHom_toSpec]; simp
  have key : ∀ k, (u'.ex (fun j ↦ g (φ (T.U.e j) (algebraMap K E (a' k) * b k)))).left ≫ p =
      spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) (algebraMap K E (a k) * b k))).left := by
    intro k
    set β : Fin (Module.finrank ℚ (FR E)) → ℂ := fun j ↦ φ (T.U.e j) (b k) with hβdef
    have hβ : ∀ l ∈ Λ₀.lattice, l • β ∈ T.U.u.Λ := by
      intro l hl
      obtain ⟨r, hr, rfl⟩ := ((GlobalTheory.LatVal.CurveTransport.isLatOf_iff).1 hΛ₀ l).1 hl
      obtain ⟨r', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hr
      have h1 := hlat _ (hbL k r')
      convert h1 using 1
      funext j
      simp [β, hφK]
    obtain ⟨f, hfo, hf⟩ := GlobalTheory.T.elliptic_curve_map_to_abelian (FR E) 𝔠 T.X T.U.c _ T.U.u Λ₀ Ω₀ hΩ₀ β hβ
    have hsq : (mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) hW ≫ f) ≫ T.X.A.hom =
        toSpec (curve Λ₁ Ω₁) ≫ spMap (g : ℂ →+* ℂ) := by
      rw [Category.assoc, hfo, GlobalTheory.WeierstrassCurve.mapHom_toSpec]
    let f' := hpb.grp.1.lift _ _ hsq
    have hf'p : f' ≫ p = mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) hW ≫ f := hpb.grp.1.lift_fst _ _ _
    have hf'o : f' ≫ X'.A.hom = toSpec (curve Λ₁ Ω₁) := hpb.grp.1.lift_snd _ _ _
    let e' : ℂ → (𝟙_ (Over (Sp ℂ)) ⟶ X'.A) := fun z => Over.homMk (pt Λ₁ Ω₁ z ≫ f') (by
      rw [Category.assoc, hf'o, hpt]; rfl)
    have hD3 := GlobalTheory.T.conjugate_curve_point_addition_compat Λ₀ Λ₁ Ω₀ Ω₁ g hΩ₀ hΩ₁ hW
    have hover : ∀ z z', pt Λ₁ Ω₁ z' ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) hW = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ z →
        (e' z').left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (z • β)).left := by
      intro z z' hzz
      show (pt Λ₁ Ω₁ z' ≫ f') ≫ p = _
      rw [Category.assoc, hf'p, ← Category.assoc, hzz, Category.assoc, hf]
    have hadd : ∀ z' w', e' (z' + w') = e' z' * e' w' := by
      intro z' w'
      obtain ⟨z, hz⟩ := hD3.1 z'
      obtain ⟨w, hw⟩ := hD3.1 w'
      apply hU1
      rw [hover _ _ (hD3.2 z w z' w' hz hw), hE2 _ _ _ _ (hover _ _ hz) (hover _ _ hw), add_smul, T.U.u.ex_add]
    obtain ⟨β₁, hβ₁⟩ := GlobalTheory.T.elliptic_map_uniformization_line (FR E) 𝔠 X' T.U.c _ u' Λ₁ Ω₁ hΩ₁ f' hf'o e' hadd (fun z => rfl)
    let v : epsR ℂ ⟶ T.X.A := Over.homMk (tan (curve Λ₀ Ω₀) Ω₀ ≫ f) (by
      rw [Category.assoc, hfo, tan, GlobalTheory.WeierstrassCurve.ptHom_toSpec]; rfl)
    let v' : epsR ℂ ⟶ X'.A := Over.homMk (tan (curve Λ₁ Ω₁) ((g : ℂ →+* ℂ) Ω₀) ≫ f') (by
      rw [Category.assoc, hf'o, tan, GlobalTheory.WeierstrassCurve.ptHom_toSpec]; rfl)
    obtain ⟨-, hv⟩ := GlobalTheory.T.elliptic_map_tangent_differential T.X.A _ _ T.U.u Λ₀ Ω₀ hΩ₀ f β hf Ω₀ v rfl
    obtain ⟨hv't, hv'⟩ := GlobalTheory.T.elliptic_map_tangent_differential X'.A _ _ u' Λ₁ Ω₁ hΩ₁ f' β₁ hβ₁ ((g : ℂ →+* ℂ) Ω₀) v' rfl
    rw [div_self hΩ₀, one_smul] at hv
    have hvv : v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left := by
      show (tan (curve Λ₁ Ω₁) ((g : ℂ →+* ℂ) Ω₀) ≫ f') ≫ p = _ ≫ (tan (curve Λ₀ Ω₀) Ω₀ ≫ f)
      rw [Category.assoc, hf'p, ← Category.assoc, GlobalTheory.T.conjugate_curve_tangent_compat _ _ (g : ℂ →+* ℂ) hW Ω₀, Category.assoc]
    have h1 := htan β v v' hvv hv
    have heq := GlobalTheory.T.tangent_differential_unique X'.A _ _ u' v' _ _ hv't hv' h1
    have hgΩ : g Ω₀ ≠ 0 := (map_ne_zero g).2 hΩ₀
    have hβ₁eq : β₁ = fun j ↦ g (β j) := by
      funext j
      have h2 := congrFun heq j
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.coe_toRingHom] at h2
      field_simp at h2
      exact h2
    have hd1 := GlobalTheory.T.conjugate_torsion_point_compat K io g t Λ₀ Λ₁ Ω₀ Ω₁ hTT hW (a k) (a' k) (hint k)
    have e1 : (fun j ↦ g (φ (T.U.e j) (algebraMap K E (a' k) * b k))) = io (a' k) • β₁ := by
      rw [hβ₁eq]; funext j; simp [β, hφK, hgio]
    have e2 : (fun j ↦ φ (T.U.e j) (algebraMap K E (a k) * b k)) = io (a k) • β := by
      funext j; simp [β, hφK]
    rw [e1, e2, ← hβ₁, Category.assoc, hf'p, ← Category.assoc, hd1, Category.assoc, hf]
  have exsum : ∀ {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A] {L : LB A.left} {n : ℕ} (uu : HolUnif A L n)
      (w : Fin m → Fin n → ℂ), uu.ex (∑ k, w k) = ∏ k, uu.ex (w k) := by
    intro A _ _ L n uu w
    induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
    | empty => simpa using (uu.ker 0).2 (zero_mem _)
    | insert k s hk ih => rw [Finset.sum_insert hk, Finset.prod_insert hk, uu.ex_add, ih]
  have hsum' : (fun j ↦ g (φ (T.U.e j) x')) = ∑ k, (fun j ↦ g (φ (T.U.e j) (algebraMap K E (a' k) * b k))) := by
    rw [hx']; funext j; simp [map_sum]
  have hsum : (fun j ↦ φ (T.U.e j) (∑ k, algebraMap K E (a k) * b k)) =
      ∑ k, (fun j ↦ φ (T.U.e j) (algebraMap K E (a k) * b k)) := by
    funext j; simp [map_sum]
  have hxm : T.U.u.ex (fun j ↦ φ (T.U.e j) x) =
      T.U.u.ex (fun j ↦ φ (T.U.e j) (∑ k, algebraMap K E (a k) * b k)) := by
    have h1 := hlat _ hxL
    have e3 : (fun j ↦ φ (T.U.e j) x) = (fun j ↦ φ (T.U.e j) (∑ k, algebraMap K E (a k) * b k)) +
        (fun j ↦ φ (T.U.e j) (x - ∑ k, algebraMap K E (a k) * b k)) := by
      funext j; simp
    rw [e3, T.U.u.ex_add, (T.U.u.ker _).2 h1, _root_.mul_one]
  rw [hxm, hsum', hsum, exsum, exsum]
  exact hE3 (Fin m) Finset.univ _ _ (fun k _ => key k)
