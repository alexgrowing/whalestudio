import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizedSuperlatticeOfRiemannForm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalTorusAlgebraic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeMapGivesHomomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfHolUnif
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolUnifPullAlongGroupHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormsAddOfFactorProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFactorImFormIntegralOnLattice
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PosAHIsog

open GlobalTheory.PullUnifHom GlobalTheory.PullHermitian GlobalTheory.CechPic

variable {A B : Over (Sp ℂ)} [GrpObj A] [GrpObj B]

def trivUnif {L : LB A.left} {g : ℕ} (u : HolUnif A L g) : HolUnif A (LB.triv A.left) g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr := fun _ _ => 1
  fr_hol := fun _ => differentiableOn_const 1
  fr_ne := fun _ _ _ => one_ne_zero
  fr_compat := fun i j z h => by
    simp [valAt', valAt, h]

theorem trivUnif_factor {L : LB A.left} {g : ℕ} (u : HolUnif A L g) :
    IsFactorAH (trivUnif u) 0 (fun _ => 1) :=
  ⟨Matrix.isHermitian_zero, fun _ => by simp, fun l i z hz => by simp [trivUnif]⟩

theorem pull_chart_iff (φ : A ⟶ B) {L : LB B.left} {g : ℕ} (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A))
    (ex' : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ B)) (hφ : ∀ z, ex z ≫ φ = ex' z)
    (j : (L.pull φ.left).ι) (z : Fin g → ℂ) :
    ⊤ ≤ (ex z).left ⁻¹ᵁ (L.pull φ.left).U j ↔ ⊤ ≤ (ex' z).left ⁻¹ᵁ L.U (j PUnit.unit) := by
  have keyl : (ex z).left ≫ φ.left = (ex' z).left := by rw [← Over.comp_left, hφ]
  exact (chart_pull_iff' _ L _ j).trans (iff_of_eq (by rw [keyl]))

def pullUnif (φ : A ⟶ B) {L : LB B.left} {M : LB A.left} {g : ℕ} (u : HolUnif A M g) (u' : HolUnif B L g)
    (hφ : ∀ z, u.ex z ≫ φ = u'.ex z) : HolUnif A (L.pull φ.left) g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr := fun j z => u'.fr (j PUnit.unit) z
  fr_hol := fun j => (u'.fr_hol (j PUnit.unit)).mono
    (fun z hz => (pull_chart_iff φ u.ex u'.ex hφ j z).1 hz)
  fr_ne := fun j z hz => u'.fr_ne _ _ ((pull_chart_iff φ u.ex u'.ex hφ j z).1 hz)
  fr_compat := fun i j z h => by
    have keyl : (u.ex z).left ≫ φ.left = (u'.ex z).left := by rw [← Over.comp_left, hφ]
    have hi := (pull_chart_iff φ u.ex u'.ex hφ i z).1 (le_left' h)
    have hj := (pull_chart_iff φ u.ex u'.ex hφ j z).1 (le_right' h)
    show u'.fr (i PUnit.unit) z = _ * u'.fr (j PUnit.unit) z
    rw [valAt'_pull_g' _ L _ i j h, keyl]
    exact u'.fr_compat _ _ _ (inf_of _ hi hj)

theorem pullUnif_factor (φ : A ⟶ B) {L : LB B.left} {M : LB A.left} {g : ℕ} (u : HolUnif A M g)
    (u' : HolUnif B L g) (hφ : ∀ z, u.ex z ≫ φ = u'.ex z) (hΛ : u.Λ ≤ u'.Λ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ' : u'.Λ → ℂ) (h : IsFactorAH u' Hm χ') :
    IsFactorAH (pullUnif φ u u' hφ) Hm (fun l => χ' ⟨l.1, hΛ l.2⟩) := by
  obtain ⟨h1, h3, h4⟩ := h
  exact ⟨h1, fun l => h3 _, fun l i z hz =>
    h4 ⟨l.1, hΛ l.2⟩ (i PUnit.unit) z ((pull_chart_iff φ u.ex u'.ex hφ i z).1 hz)⟩

theorem ex_nsmul {G : Over (Sp ℂ)} [GrpObj G] {g : ℕ} (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ G))
    (he : ∀ z w, e (z + w) = e z * e w) (he0 : e 0 = 1) (w : Fin g → ℂ) (n : ℕ) :
    e ((n : ℂ) • w) = e w ^ n := by
  induction n with
  | zero => simp [he0]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, he, ih, pow_succ]

theorem unif_ex_zero {G : Over (Sp ℂ)} [GrpObj G] {L : LB G.left} {g : ℕ} (u : HolUnif G L g) : u.ex 0 = 1 :=
  (u.ker 0).2 (zero_mem _)

end GlobalTheory.PosAHIsog

namespace GlobalTheory.PosAHIsog

open GlobalTheory.CechPic

theorem exists_isog_principal_lam :
    ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → u.IsAH Hm χ →
    ∃ (P : Out.PolAV (Sp ℂ)) (ψ : A ⟶ P.A) (ρ : P.A ⟶ A) (N : ℕ), 1 ≤ N ∧ IsMonHom ψ ∧ IsMonHom ρ ∧
      ψ ≫ ρ = (𝟙 A) ^ N ∧ ρ ≫ ψ = (𝟙 P.A) ^ N ∧
      LBIso (abelian₂ A M) ((abelian₂ P.A P.L).pull (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left) := by
  intro g A _ hA M u Hm χ hM hAH
  haveI := hA.comm
  haveI := hA.smooth
  haveI := hA.proper
  haveI : IsReduced A.left := GlobalTheory.isReduced_of_smooth_complex _ A.hom hA.smooth
  have hint := GlobalTheory.TorusRM.ahFactor_im_int g A M u Hm χ hM (isFactorAH_of_isAH hAH)
  obtain ⟨Λ₁, N, Ef, hle, hN, hNΛ, hd1, hf1, hEf, hbij⟩ :=
    GlobalTheory.UnimodOver.exists_unimodular_overlattice g u.Λ Hm u.discrete u.full hAH.1 hAH.2.1 hint
  obtain ⟨P, uB, χB, -, hΛB, hAHB, -, -⟩ :=
    GlobalTheory.principalTorus_algebraic g Λ₁ Hm Ef hd1 hf1 hAH.1 hAH.2.1 hEf hbij
  haveI := P.isAb.comm
  haveI := P.isAb.smooth
  haveI := P.isAb.proper
  haveI : IsReduced P.A.left := GlobalTheory.isReduced_of_smooth_complex _ P.A.hom P.isAb.smooth
  have hsA := GlobalTheory.TorusAction.smoothOfRelativeDimension_of_holUnif A hA u
  have hsP := GlobalTheory.TorusAction.smoothOfRelativeDimension_of_holUnif P.A P.isAb uB
  have hle' : u.Λ ≤ uB.Λ := hΛB ▸ hle
  obtain ⟨ψ, hψ, hψe⟩ := GlobalTheory.HolUnifHom.exists_isMonHom_of_map_lattice A P.A g hA P.isAb hsA hsP M P.L u uB
    LinearMap.id (fun x hx => hle' hx)
  obtain ⟨ρ, hρ, hρe⟩ := GlobalTheory.HolUnifHom.exists_isMonHom_of_map_lattice P.A A g P.isAb hA hsP hsA P.L M uB u
    ((N : ℂ) • LinearMap.id) (fun x hx => by simpa using hNΛ x (hΛB ▸ hx))
  have hψe' : ∀ w, u.ex w ≫ ψ = uB.ex w := fun w => (hψe w).symm
  have hρe' : ∀ w, uB.ex w ≫ ρ = u.ex ((N : ℂ) • w) := fun w => by simpa using (hρe w).symm
  refine ⟨P, ψ, ρ, N, hN, hψ, hρ, ?_, ?_, ?_⟩
  · refine GlobalTheory.ComplexPoints.over_hom_ext_of_complexPoints fun x => ?_
    obtain ⟨w, rfl⟩ := u.ex_onto x
    rw [← Category.assoc, hψe', hρe', comp_pow, Category.comp_id,
      ex_nsmul u.ex u.ex_add (unif_ex_zero u)]
  · refine GlobalTheory.ComplexPoints.over_hom_ext_of_complexPoints fun x => ?_
    obtain ⟨w, rfl⟩ := uB.ex_onto x
    rw [← Category.assoc, hρe', hψe', comp_pow, Category.comp_id,
      ex_nsmul uB.ex uB.ex_add (unif_ex_zero uB)]
  · haveI := hψ
    have hM' : (P.L.pull ψ.left).IsLB := pull_isLB P.isLB _
    have hF₃ := pullUnif_factor ψ u uB hψe' hle' Hm χB (isFactorAH_of_isAH hAHB)
    obtain ⟨H, m, s, hH, hs, -⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmple ℂ A hA
    have hamp : Out.RelAmple A H :=
      (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A hH).2 (GlobalTheory.isAmpleLB_of_veryAmpleBy hs)
    have hadd := GlobalTheory.T.hermitian_forms_add_of_factor_product g A hA (GlobalTheory.ProjSpace.isProjOver_of_relAmple hamp) (LB.triv A.left) M (P.L.pull ψ.left) (trivUnif u) u (pullUnif ψ u uB hψe')
      0 Hm Hm (fun _ => 1) χ _ (LB.isLB_triv _) hM hM' rfl rfl (trivUnif_factor u) (isFactorAH_of_isAH hAH) hF₃
      (by rw [zero_add])
    have hLM : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
    have hLM' : (abelian₂ A (P.L.pull ψ.left)).IsLB := LB.isLB_linComb hM' _ _
    have hLT : (abelian₂ A (LB.triv A.left)).IsLB := LB.isLB_linComb (LB.isLB_triv _) _ _
    have hD : (LB.div (abelian₂ A (P.L.pull ψ.left)) (abelian₂ A (LB.triv A.left))).IsLB := LB.isLB_div hLM' hLT
    have hR : ((abelian₂ P.A P.L).pull (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left).IsLB :=
      pull_isLB (LB.isLB_linComb P.isLB _ _) _
    refine (cls_eq_iff hLM hR).1 ?_
    have e₁ : cls _ hLM' = lam (cls _ hM') (fst A A) (snd A A) := cls_cube_two hM' _ _ hLM'
    have e₂ : cls _ hLT = lam (cls _ (LB.isLB_triv A.left)) (fst A A) (snd A A) :=
      cls_cube_two (LB.isLB_triv _) _ _ hLT
    rw [(cls_eq_iff hLM hD).2 hadd, cls_div hLM' hLT hD, GlobalTheory.RealMult.Elliptic.cls_pull_lam P.isLB _ _ hR,
      e₁, e₂, cls_pull P.isLB, lam_pull]
    have h0 : cls (LB.triv A.left) (LB.isLB_triv _) = 0 := rfl
    rw [h0]
    simp [lam]

end GlobalTheory.PosAHIsog
