import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsParamFunVIffIsSysParamDOfLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalHeckeOperatorEqSmulOfLocalParameterStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsHyperspecialDoubleCosetOfElementaryDivisor
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHeckeOpFullDualLab

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ParamEigen

variable {D : D7} {V : HSp D}

theorem heckeLin_eq_of_rep {K : Subgroup (GA D V)} {α α' : GA D V} {R R' : Finset (GA D V)}
    (hR : IsCosetRep V (K : Set (GA D V)) α R) (hR' : IsCosetRep V (K : Set (GA D V)) α' R')
    {a b : GA D V} (ha : a ∈ K) (hb : b ∈ K) (hα : α' = a * α * b) {f : GA D V → ℂ}
    (hf : ∀ k ∈ K, ∀ g, f (g * k) = f g) : heckeLin V R f = heckeLin V R' f := by
  classical
  have m1 : ∀ γ ∈ R, ∃ k₁ ∈ (K : Set (GA D V)), ∃ k₂ ∈ (K : Set (GA D V)), γ = k₁ * α' * k₂ := fun γ hγ => by
    obtain ⟨-, k₁, h₁, k₂, h₂, rfl⟩ := hR.1 γ hγ
    exact ⟨k₁ * a⁻¹, K.mul_mem h₁ (K.inv_mem ha), b⁻¹ * k₂, K.mul_mem (K.inv_mem hb) h₂, by rw [hα]; group⟩
  have m2 : ∀ γ ∈ R', ∃ k₁ ∈ (K : Set (GA D V)), ∃ k₂ ∈ (K : Set (GA D V)), γ = k₁ * α * k₂ := fun γ hγ => by
    obtain ⟨-, k₁, h₁, k₂, h₂, rfl⟩ := hR'.1 γ hγ
    exact ⟨k₁ * a, K.mul_mem h₁ ha, b * k₂, K.mul_mem hb h₂, by rw [hα]; group⟩
  have inv : ∀ x y : GA D V, x⁻¹ * y ∈ K → y⁻¹ * x ∈ K := fun x y h => by
    simpa using K.inv_mem h
  funext g
  simp only [heckeLin, LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_bij' (fun γ hγ => (hR'.2 γ (m1 γ hγ)).exists.choose)
    (fun γ hγ => (hR.2 γ (m2 γ hγ)).exists.choose)
    (fun γ hγ => (hR'.2 γ (m1 γ hγ)).exists.choose_spec.1)
    (fun γ hγ => (hR.2 γ (m2 γ hγ)).exists.choose_spec.1) ?_ ?_ ?_
  · intro γ hγ
    have s1 := (hR'.2 γ (m1 γ hγ)).exists.choose_spec
    set γ' := (hR'.2 γ (m1 γ hγ)).exists.choose
    have s2 := (hR.2 γ' (m2 γ' s1.1)).exists.choose_spec
    exact (hR.2 γ' (m2 γ' s1.1)).unique s2 ⟨hγ, inv _ _ s1.2⟩
  · intro γ hγ
    have s1 := (hR.2 γ (m2 γ hγ)).exists.choose_spec
    set γ' := (hR.2 γ (m2 γ hγ)).exists.choose
    have s2 := (hR'.2 γ' (m1 γ' s1.1)).exists.choose_spec
    exact (hR'.2 γ' (m1 γ' s1.1)).unique s2 ⟨hγ, inv _ _ s1.2⟩
  · intro γ hγ
    have s1 := (hR'.2 γ (m1 γ hγ)).exists.choose_spec
    set γ' := (hR'.2 γ (m1 γ hγ)).exists.choose
    have e : g * γ = g * γ' * (γ'⁻¹ * γ) := by group
    rw [e, hf _ s1.2]

end GlobalTheory.ParamEigen

namespace GlobalTheory.ParamEigen

variable {D : D7} {V : HSp D}

open GlobalTheory.AdelicU GlobalTheory.PRep in

theorem heckeLin_eq_heckeVec {v : HeightOneSpectrum (𝓞 D.host.F)} {K : Set (GA D V)}
    (hK : ∀ x, x ∈ K ↔ ∃ k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v, emb D.sp.cm.sig V.gram v k = x)
    (g : GLoc D.sp.cm.sig V.gram v) {R : Finset (GA D V)} (hR : IsCosetRep V K (emb D.sp.cm.sig V.gram v g) R)
    {φ : GA D V → ℂ}
    (hφ : φ ∈ fixed ((rightReg ℂ _ ℂ).comp (emb D.sp.cm.sig V.gram v)) (stabLoc D.sp.cm.sig V.gram (frameLat V) v)) :
    heckeLin V R φ = GlobalTheory.LFun.heckeVec ((rightReg ℂ _ ℂ).comp (emb D.sp.cm.sig V.gram v))
      (stabLoc D.sp.cm.sig V.gram (frameLat V) v)
      (Formalism.UG.dosetInd ℂ (stabLoc D.sp.cm.sig V.gram (frameLat V) v) g) φ := by
  classical
  let H : Subgroup (GA D V) := (stabLoc D.sp.cm.sig V.gram (frameLat V) v).map (emb D.sp.cm.sig V.gram v)
  have hKH : K = (H : Set (GA D V)) := Set.ext fun x => (hK x).trans (by simp [H])
  subst hKH
  have := GlobalTheory.HeckeDual.isLattice_frameLat V
  obtain ⟨R₀, r1, r2⟩ := GlobalTheory.HeckeDual.exists_rep _ (isOpen_stabLoc D.sp.cm.sig V.gram (frameLat V) v)
    (isCompact_stabLoc D.sp.cm.sig V.gram (frameLat V) v) g
  obtain ⟨s1, s2⟩ := GlobalTheory.LFun.rep_image (emb D.sp.cm.sig V.gram v) (emb_injective _ _ v) hK r1 r2
  have hR₀ : IsCosetRep V (H : Set (GA D V)) (emb D.sp.cm.sig V.gram v g) (R₀.image (emb D.sp.cm.sig V.gram v)) :=
    ⟨fun γ hγ => ⟨by
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hγ
      exact mem_finPts.2 (projInf_emb _ _ v y), s1 γ hγ⟩, s2⟩
  have hinv : ∀ k ∈ H, ∀ x, φ (x * k) = φ x := by
    rintro _ ⟨k, hk, rfl⟩ x
    exact congrFun (GlobalTheory.LGrp.mem_fixed.1 hφ k hk) x
  rw [heckeLin_eq_of_rep hR hR₀ (one_mem H) (one_mem H) (by group) hinv,
    GlobalTheory.LFun.heckeVec_dosetInd hφ (R := R₀) (fun γ hγ => DoubleCoset.mem_doubleCoset.2 (r1 γ hγ))
      fun x hx => r2 x (DoubleCoset.mem_doubleCoset.1 hx)]
  funext x
  rw [heckeLin_apply, Finset.sum_image (emb_injective _ _ v).injOn, Finset.sum_apply]
  rfl

theorem doubleCoset_of_divAt {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} (hP : IsPrimeIdem P e f)
    {ϖ ϖ' : 𝓞 D.host.E} (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) (h1' : ϖ' ∈ P.asIdeal)
    (h2' : ϖ' ∉ P.asIdeal ^ 2) {d : List ℤ} (hd : d.Pairwise (fun a b => b ≤ a)) {α α' : GA D V}
    (hα : SuppF V f α) (hα' : SuppF V f α') (hD : DivAt V e (ϖ : D.host.E) d α)
    (hD' : DivAt V e (ϖ' : D.host.E) d α') :
    ∃ a b, a ∈ KsphC V ∅ ∧ SuppF V f a ∧ b ∈ KsphC V ∅ ∧ SuppF V f b ∧ α' = a * α * b := by
  rcases id hP with ⟨hi, rfl⟩ | ⟨rfl, -, -⟩
  · obtain ⟨a, ⟨ha, ha'⟩, b, ⟨hb, hb'⟩, hab⟩ :=
      GlobalTheory.SplitLabel.split_label V P e ϖ ϖ' d α α' hi h1 h2 h1' h2' hα hα' hD hD'
    exact ⟨a, b, ha, ha', hb, hb', hab⟩
  · exact (GlobalTheory.InertDoubleCoset.inert_double_cosets V P _ hP (GlobalTheory.SphLabelOps.exists_real_unif D P) α hα).2.2
      ϖ ϖ' d α' h1 h2 h1' h2' hd hα' hD hD'

end GlobalTheory.ParamEigen

namespace GlobalTheory.ParamEigen

variable {D : D7} {V : HSp D}

open GlobalTheory.AdelicU GlobalTheory.PRep in

theorem exists_eig {J : Set (GA D V)} {χ : GA D V → ℂ} {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (hJ : SphOff J χ Sb) (B : GlobalTheory.LFun.Fam D.host.E) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) :
    ∃ z : ℂ, ∀ f : GA D V → ℂ, GlobalTheory.LFun.IsParamFunV V Sb f B → ∀ R, Hecke₂ V J χ Sb P d R →
      heckeLin V R f = z • f := by
  classical
  by_cases h : ∃ R, Hecke₂ V J χ Sb P d R
  swap
  · exact ⟨0, fun f _ R hR => absurd ⟨R, hR⟩ h⟩
  obtain ⟨R₀, e₀, f₀, ϖ₀, α₀, hS, hP₀, p1, p2, hd, hJ1, -, hα₀, hD₀, -, hR₀⟩ := h
  have hv : P.under (𝓞 D.host.F) ∉ Sb := GlobalTheory.LFun.offS_iff.1 hS
  have hs := Supp.suppF_iff_of_isPrimeIdem V hP₀ rfl
  have hK : ∀ x, x ∈ {k | k ∈ J ∧ SuppF V f₀ k} ↔
      ∃ k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) (P.under (𝓞 D.host.F)), emb D.sp.cm.sig V.gram _ k = x :=
    fun x => by
      constructor
      · rintro ⟨m1, m2⟩
        obtain ⟨k, rfl⟩ := (hs x).1 m2
        exact ⟨k, (Supp.emb_mem_KsphC V k).1 ((hJ1 _ m2).1 m1), rfl⟩
      · rintro ⟨k, hk, rfl⟩
        have := (hs _).2 ⟨k, rfl⟩
        exact ⟨(hJ1 _ this).2 ((Supp.emb_mem_KsphC V k).2 hk), this⟩
  let H : Subgroup (GA D V) :=
    (stabLoc D.sp.cm.sig V.gram (frameLat V) (P.under (𝓞 D.host.F))).map (emb D.sp.cm.sig V.gram _)
  have hKH : {k | k ∈ J ∧ SuppF V f₀ k} = (H : Set (GA D V)) := Set.ext fun x => (hK x).trans (by simp [H])
  obtain ⟨g₀, rfl⟩ := (hs α₀).1 hα₀
  obtain ⟨z, hz⟩ := GlobalTheory.T.sphericalHeckeOperator_eq_smul_of_localParameter _ _ D.sp.cm.sig V.rank V.gram (frameLat V) _ P rfl (B P) _
    (Formalism.UG.Final.DosetIndMem _ (stabLoc D.sp.cm.sig V.gram (frameLat V) (P.under (𝓞 D.host.F))) ℂ g₀)
  refine ⟨z, fun f hf R hR => ?_⟩
  obtain ⟨e, f', ϖ, α, -, hP', q1, q2, -, -, -, hα, hD, -, hRc⟩ := hR
  obtain ⟨rfl, rfl⟩ :=
    ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e₀ f₀ hP₀).2.2.2.1 e f' hP'
  have hpv := hf _ hv P rfl
  have hfix := hpv.mem_fixed
  obtain ⟨a, b, ha, ha', hb, hb', hab⟩ := doubleCoset_of_divAt hP₀ p1 p2 q1 q2 hd hα₀ hα hD₀ hD
  have hmem : ∀ k, k ∈ KsphC V ∅ → SuppF V f' k → k ∈ H := fun k hk hk' => by
    rw [← SetLike.mem_coe, ← hKH]
    exact ⟨(hJ1 k hk').2 hk, hk'⟩
  have hinv : ∀ k ∈ H, ∀ x, f (x * k) = f x := by
    rintro _ ⟨k, hk, rfl⟩ x
    exact congrFun (GlobalTheory.LGrp.mem_fixed.1 hfix k hk) x
  rw [hKH] at hRc hR₀
  rw [heckeLin_eq_of_rep hRc hR₀ (H.inv_mem (hmem a ha ha')) (H.inv_mem (hmem b hb hb')) (by rw [hab]; group) hinv,
    heckeLin_eq_heckeVec hK g₀ (hKH ▸ hR₀) hfix, hz _ _ f hpv]

end GlobalTheory.ParamEigen

namespace GlobalTheory.ParamEigen

theorem eig_of_param : ∀ (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), SphOff J χ Sb → ∀ B : GlobalTheory.LFun.Fam D.host.E,
    ∃ a : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, ∀ f : GA D V → ℂ, GlobalTheory.LFun.IsParamFunV V Sb f B →
      ∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = a P d • f := by
  intro D V J χ Sb hJ B
  choose a ha using exists_eig (V := V) hJ B
  exact ⟨a, fun f hf P d R hR => ha P d f hf R hR⟩

end GlobalTheory.ParamEigen

end
