import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsDiffSumSmulOfIsLieComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieCombIffIsCombAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieImageCorrespondence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodNormIntegral
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CMVecBC

def diagL {g : ℕ} (d : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun w j := d j * w j
  map_add' w w' := by funext j; simp [mul_add]
  map_smul' r w := by funext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem diagL_apply {g : ℕ} (d w : Fin g → ℂ) (j : Fin g) : diagL d w j = d j * w j := rfl

section Rep

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

def lcH (P : u.Λ →+ HdR A) : (u.Λ →₀ ℂ) →ₗ[ℂ] HdR A := Finsupp.linearCombination ℂ (fun x ↦ P x)

def lcW : (u.Λ →₀ ℂ) →ₗ[ℂ] (Fin g → ℂ) := Finsupp.linearCombination ℂ (fun x : u.Λ ↦ (x : Fin g → ℂ))

def Good (h : HdR A) (W : Fin g → ℂ) : Prop := ∃ v, IsLieImage h v ∧ u.IsDiff W v

variable {u}

theorem good_comb (hA : IsAbelianScheme A) {n : ℕ} (cf : Fin n → ℂ) {h : Fin n → HdR A}
    {W : Fin n → Fin g → ℂ} (H : ∀ k, Good u (h k) (W k)) :
    Good u (∑ k, cf k • h k) (∑ k, cf k • W k) := by
  choose v hv using H
  exact ⟨FlagTan.lieComb cf v, FlagTan.isLieImage_lieComb cf fun k ↦ (hv k).1,
    isDiff_sum_smul_of_isLieComb A hA L g n u v W cf _ (fun k ↦ (hv k).1.1) (fun k ↦ (hv k).2)
      (FlagTan.isLieComb_lieComb cf v)⟩

theorem good_zero (hA : IsAbelianScheme A) : Good u 0 0 := by
  simpa using good_comb (u := u) hA (n := 0) Fin.elim0 (h := Fin.elim0) (W := Fin.elim0) fun k ↦ k.elim0

theorem good_add (hA : IsAbelianScheme A) {h h' : HdR A} {W W' : Fin g → ℂ} (H : Good u h W)
    (H' : Good u h' W') : Good u (h + h') (W + W') := by
  have := good_comb (u := u) hA ![1, 1] (h := ![h, h']) (W := ![W, W']) fun k ↦ by
    fin_cases k
    · exact H
    · exact H'
  simpa [Fin.sum_univ_two] using this

theorem good_smul (hA : IsAbelianScheme A) {h : HdR A} {W : Fin g → ℂ} (H : Good u h W) (r : ℂ) :
    Good u (r • h) (r • W) := by
  have := good_comb (u := u) hA ![r] (h := ![h]) (W := ![W]) fun k ↦ by
    fin_cases k
    exact H
  simpa using this

variable (u)

theorem rep_good (hA : IsAbelianScheme A) (P : u.Λ →+ HdR A)
    (hP : ∀ x : u.Λ, ∃ v, IsLieImage (P x) v ∧ u.IsDiff x v) (f : u.Λ →₀ ℂ) :
    Good u (lcH u P f) (lcW u f) := by
  refine Finsupp.induction_linear f ?_ (fun f f' hf hf' ↦ ?_) (fun x r ↦ ?_)
  · simpa using good_zero (u := u) hA
  · simpa [map_add] using good_add hA hf hf'
  · simpa [lcH, lcW] using good_smul hA (hP x) r

theorem rep_push (P : u.Λ →+ HdR A) (α : A ⟶ A) [IsMonHom α] (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hM : ∀ w, u.ex (M w) = u.ex w ≫ α)
    (hpush : ∀ x x' : u.Λ, (x' : Fin g → ℂ) = M x → push (dp0 ℂ) (𝟙 _) α (P x) = P x')
    (f : u.Λ →₀ ℂ) : ∃ f', lcH u P f' = push (dp0 ℂ) (𝟙 _) α (lcH u P f) ∧ lcW u f' = M (lcW u f) := by
  have hΛ : ∀ x : u.Λ, M x ∈ u.Λ := fun x ↦ (u.ker _).1 (by rw [hM, (u.ker _).2 x.2, one_comp])
  let mu : u.Λ → u.Λ := fun x ↦ ⟨M x, hΛ x⟩
  refine ⟨Finsupp.mapDomain mu f, ?_, ?_⟩
  · simp only [lcH, Finsupp.linearCombination_mapDomain, Finsupp.apply_linearCombination]
    congr 2
    funext x
    exact (hpush x (mu x) rfl).symm
  · simp only [lcW, Finsupp.linearCombination_mapDomain, Finsupp.apply_linearCombination]
    rfl

end Rep

theorem coe_functional {R : Subring ℂ} {n : ℕ} (ℓ : (Fin n → R) →ₗ[R] R) (z : ℂ) (v w : Fin n → R)
    (h : ∀ k, ((v k : R) : ℂ) = z * (w k : ℂ)) : ((ℓ v : R) : ℂ) = z * (ℓ w : ℂ) := by
  classical
  rw [LinearMap.pi_apply_eq_sum_univ ℓ v, LinearMap.pi_apply_eq_sum_univ ℓ w]
  simp only [smul_eq_mul, AddSubmonoidClass.coe_finset_sum, Subring.coe_mul, h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ mul_assoc _ _ _

end GlobalTheory.CMVecBC

namespace GlobalTheory.CMVecBC

open GlobalTheory.CMVecBC in

theorem isCMVec_of_mem_eigLat : GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.PeriodComparison → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (c : Ideal (OF E))
    (y : (Af E)ˣ) (𝔠 : FracId (FR E)) (R : Subring ℂ) [IsDiscreteValuationRing R]
    (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X)
    (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC c) X₀.A), c ≠ ⊥ → X.IsPullBy X₀ (spMap R.subtype) p →
    (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a) = X₀.rm.act a) →
    (∀ a : orderC c, ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
      ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i)) →
    ∀ (hL : LieExact X₀.A) (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap R ℂ) (spMap (algebraMap R ℂ)) p), m.IsBC →
    ∀ (i : I) (g : Fin n → R), g ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (φK i) →
    ∃ (yv : HdR X.A) (w : ℂ), U.IsCMVec i yv w ∧ m.Corr (eH.symm g) yv ∧
      ((e i (hL.toLie X₀.rm (eH.symm g)) : R) : ℂ) = a i * w := by
  intro hdR hPC E _ _ _ I _ φ c y 𝔠 R _ X₀ X U p cm hc hpull hcmF hcmC j hj φK hφK e a hPG hL n eH m hm i g hg
  classical
  set g0 := Module.finrank ℚ (FR E) with hg0
  obtain ⟨ε, hPC⟩ := hPC
  obtain ⟨P, hspan, -, hlie, hpush, -⟩ :=
    hPC X.A g0 X.ab X.dim (X.diag U.c) (LB.isLB_pull (X.isLB U.c) _) U.u
  obtain ⟨yv, hyv⟩ := hm.exists (eH.symm g)
  set ρ := eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm) with hρ
  have hcoord : ∀ (b : orderC c) k, (((ρ b g) k : R) : ℂ) = φ i b * (g k : ℂ) := by
    intro b k
    have hg' : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (FractionRing R) (Fin n → R) g ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ (φK i) :=
      Submodule.mem_comap.1 hg
    have h1 := Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hg' b)
    have h2 := congrArg (LinearMap.liftBaseChange (FractionRing R)
      ((Algebra.linearMap R (FractionRing R)) ∘ₗ LinearMap.proj k)) h1
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK, TensorProduct.mk_apply, LinearMap.baseChange_tmul, LinearMap.map_smul,
      LinearMap.liftBaseChange_tmul, one_smul, smul_eq_mul, LinearMap.comp_apply, Algebra.linearMap_apply,
      LinearMap.proj_apply] at h2
    have h3 := congrArg j h2
    have h4 : j (φK i b) = φ i b := by rw [← RingHom.comp_apply, hφK]
    simp only [map_mul, map_one, one_mul, hj, h4] at h3
    simpa using h3
  have hmodel : ∀ (b : orderC c) (α : X.A ⟶ X.A) [IsMonHom α], α.left ≫ p = p ≫ (cm.act b).left →
      push (dp0 ℂ) (𝟙 _) α yv = φ i b • yv := by
    intro b α _ hα
    haveI := cm.hom b
    have h1 : m.Corr (push (dp0 R) (𝟙 _) (cm.act b) (eH.symm g)) (push (dp0 ℂ) (𝟙 _) α yv) :=
      GrpMor.Corr.push m (cm.act b) α hα.symm hyv
    refine (hm.unique h1 fun c' ↦ ?_)
    have he : push (dp0 R) (𝟙 _) (cm.act b) (eH.symm g) = eH.symm (ρ b g) := by
      rw [← act_apply]
      simp [ρ, LinearEquiv.conjRingEquiv, LinearEquiv.conj_apply]
    rw [LinearMap.smul_apply, hyv c', smul_eq_mul, he]
    exact (coe_functional ((LinearMap.applyₗ c') ∘ₗ eH.symm.toLinearMap) _ _ _ (hcoord b)).symm
  have hΛ : ∀ (b : E) (α : X.A ⟶ X.A) [IsMonHom α],
      (∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
      ∀ x : U.u.Λ, (fun j ↦ φ (U.e j) b * (x : Fin g0 → ℂ) j) ∈ U.u.Λ := fun b α _ hα x ↦
    (U.u.ker _).1 (by rw [hα, (U.u.ker _).2 x.2, one_comp])
  have hCM1 : ∀ (b : E) (α : X.A ⟶ X.A) [IsMonHom α],
      (∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
      push (dp0 ℂ) (𝟙 _) α yv = φ i b • yv := by
    intro b α _ hα
    obtain ⟨N, hN, hNb⟩ := GlobalTheory.CMExtend.exists_natMul_mem_orderC hc b
    obtain ⟨α', _, hα'p, hα'⟩ := hcmC ⟨_, hNb⟩
    have e1 := hmodel ⟨_, hNb⟩ α' hα'p
    have e2 : push (dp0 ℂ) (𝟙 _) α' = (N : ℂ) • push (dp0 ℂ) (𝟙 _) α := by
      refine LinearMap.ext_on_range hspan fun x ↦ ?_
      rw [hpush α' (diagL fun j ↦ φ (U.e j) ((N : E) * b)) hα' x (N • ⟨_, hΛ b α hα x⟩) ?_,
        LinearMap.smul_apply, hpush α (diagL fun j ↦ φ (U.e j) b) hα x ⟨_, hΛ b α hα x⟩ rfl, map_nsmul,
        Nat.cast_smul_eq_nsmul]
      funext k
      have hvec : φ (U.e k) ((N : E) * b) * (x : Fin g0 → ℂ) k = (N : ℂ) * (φ (U.e k) b * (x : Fin g0 → ℂ) k) := by
        simp only [map_mul, map_natCast]; ring
      rw [diagL_apply, hvec]
      clear * - hvec
      simp
    rw [e2, LinearMap.smul_apply] at e1
    have e3 : φ i ((N : E) * b) = (N : ℂ) * φ i b := by simp
    refine smul_right_injective _ (Nat.cast_ne_zero.2 hN : (N : ℂ) ≠ 0) ?_
    simp only
    rw [e1]
    change φ i ((N : E) * b) • yv = _
    rw [e3, mul_smul]
  have hinj : Function.Injective φ := by
    intro i1 i2 h12
    by_contra hne
    have hk : U.e.symm i1 ≠ U.e.symm i2 := fun h ↦ hne (U.e.symm.injective h)
    let S : Submodule ℝ (Fin g0 → ℂ) := LinearMap.ker
      (((LinearMap.proj (R := ℂ) (φ := fun _ : Fin g0 ↦ ℂ) (U.e.symm i1)) - LinearMap.proj (R := ℂ) (φ := fun _ : Fin g0 ↦ ℂ) (U.e.symm i2)).restrictScalars ℝ)
    have hΛS : (U.u.Λ : Set (Fin g0 → ℂ)) ⊆ S := by
      intro w hw
      obtain ⟨x, -, rfl⟩ := (U.lat w).1 hw
      simp [S, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord, h12]
    have hle : Submodule.span ℝ (U.u.Λ : Set (Fin g0 → ℂ)) ≤ S := Submodule.span_le.2 hΛS
    rw [U.u.full] at hle
    have h1 := hle (Submodule.mem_top (x := Pi.single (U.e.symm i1) 1))
    simp [S, Pi.single_apply, hk.symm] at h1
  have hsep : ∀ k : Fin g0, k ≠ U.e.symm i → ∃ b : orderC c, φ (U.e k) b ≠ φ i b := by
    intro k hk
    have hne : φ (U.e k) ≠ φ i := fun h ↦ hk (U.e.eq_symm_apply.2 (hinj h))
    obtain ⟨x, hx⟩ := DFunLike.ne_iff.1 hne
    obtain ⟨N, hN, hNx⟩ := GlobalTheory.CMExtend.exists_natMul_mem_orderC hc x
    refine ⟨⟨_, hNx⟩, ?_⟩
    simp only [map_mul, map_natCast]
    exact fun h ↦ hx (mul_left_cancel₀ (Nat.cast_ne_zero.2 hN) h)
  have hrep0 : ∃ f, lcH U.u P f = yv := by
    have h0 : yv ∈ Submodule.span ℂ (Set.range fun x ↦ P x) := by
      rw [show (fun x ↦ P x) = ⇑P from rfl, hspan]; exact Submodule.mem_top
    rw [← Finsupp.range_linearCombination] at h0
    exact h0
  have hstep : ∀ s : Finset (Fin g0), ∃ f, lcH U.u P f = yv ∧ ∀ k ∈ s, k ≠ U.e.symm i → lcW U.u f k = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨f, hf⟩ := hrep0
      exact ⟨f, hf, by simp⟩
    | insert k s hks ih =>
      obtain ⟨f, hf, hz⟩ := ih
      by_cases hk : k = U.e.symm i
      · refine ⟨f, hf, fun k' hk' hne ↦ ?_⟩
        rcases Finset.mem_insert.1 hk' with rfl | h
        · exact absurd hk hne
        · exact hz k' h hne
      obtain ⟨b, hb⟩ := hsep k hk
      obtain ⟨α, _, hαp, hα⟩ := hcmC b
      obtain ⟨f', hf'1, hf'2⟩ :=
        rep_push U.u P α (diagL fun j ↦ φ (U.e j) b) hα (hpush α _ hα) f
      have hne : φ i b - φ (U.e k) b ≠ 0 := sub_ne_zero.2 (Ne.symm hb)
      refine ⟨(φ i b - φ (U.e k) b)⁻¹ • (f' - φ (U.e k) b • f), ?_, fun k' hk' hne' ↦ ?_⟩
      · rw [map_smul, map_sub, map_smul, hf'1, hf, hmodel b α hαp, ← sub_smul, smul_smul,
          inv_mul_cancel₀ hne, one_smul]
      · rw [map_smul, map_sub, map_smul, hf'2]
        simp only [Pi.smul_apply, Pi.sub_apply, diagL_apply, smul_eq_mul]
        rcases Finset.mem_insert.1 hk' with rfl | h
        · ring
        · rw [hz k' h hne']; ring
  obtain ⟨f, hf, hz⟩ := hstep Finset.univ
  obtain ⟨v, hv, hdv⟩ := rep_good U.u X.ab P hlie f
  have hW : lcW U.u f = Pi.single (U.e.symm i) (lcW U.u f (U.e.symm i)) := by
    funext k
    by_cases hk : k = U.e.symm i
    · subst hk; simp
    · rw [hz k (Finset.mem_univ _) hk]; simp [Pi.single_apply, hk]
  rw [hf] at hv
  rw [hW] at hdv
  refine ⟨yv, lcW U.u f (U.e.symm i), ⟨fun b α _ hα ↦ hCM1 b α hα, v, hv, hdv⟩, hyv, ?_⟩
  have hcorr := GlobalTheory.RealMult.Obj.lieCorr_of_isLieImage hdR R.subtype hpull m hyv
    ((hL.toLie_eq_iff X₀.rm).1 rfl) (v' := GlobalTheory.Serre.Lie.mk X.rm v hv.1) hv
  have := hPG i _ _ _ hcorr hdv
  rw [this, Pi.single_eq_same]

end GlobalTheory.CMVecBC
