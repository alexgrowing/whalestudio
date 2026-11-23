import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SigmaSplitSymmInl
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesPrincipalAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalSiegelObjectGlueArtinFibreProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectDeterminedOverArtinianPinchStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyTangentBoundNonconstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFirstOrderTangentPointSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialSquareZeroExtensionPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectTangentShiftConstancyDirectionIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.FirstOrderSiegel

open GlobalTheory.SiegelPullComp GlobalTheory.SiegelRingChange

variable {h k : ℕ}

theorem isLocalRing_tsze (K : Type) [Field K] (r : ℕ) : IsLocalRing (TrivSqZeroExt K (Fin r → K)) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact IsLocalRing.isUnit_or_isUnit_one_sub_self _

theorem isArtinianRing_tsze (K : Type) [Field K] (r : ℕ) : IsArtinianRing (TrivSqZeroExt K (Fin r → K)) :=
  haveI : Module.Finite K (TrivSqZeroExt K (Fin r → K)) := inferInstanceAs (Module.Finite K (K × (Fin r → K)))
  IsArtinianRing.of_finite K _

theorem pull_exists {B : Type} [CommRing B] {ζ : B} {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B}
    (f : S' ⟶ S) (hf : f ≫ s = s') (c : SiegPre h k ζ s) :
    ∃ c' : SiegPre h k ζ s', SiegPB c' c f ∧ (c.Principal → c'.Principal) := by
  have e : f ≫ s = s' ≫ spMap (RingHom.id B) := by
    rw [hf]
    simp [spMap]
  have H := siegPre_pull_ringChange h k B B ζ ζ (RingHom.id B) S S' s s' f rfl e
  obtain ⟨c', hc'⟩ := H.1 c
  exact ⟨c', hc', H.2.1 c c' hc'⟩

theorem pb_symm {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S : Scheme.{0}} {s : S ⟶ Sp B}
    {s' : S ⟶ Sp B'} {c : SiegPre h k ζ s} {c' : SiegPre h k ζ' s'} (m : SiegPB c' c (𝟙 S)) : SiegPB c c' (𝟙 S) :=
  pb_cancel m (by rw [Category.comp_id]; exact pb_id c)

theorem constPt_comp {K : Type} [Field K] {X Y : Scheme.{0}} (x : Sp (DualNumber K) ⟶ X) (z : X ⟶ Y) :
    constPt (x ≫ z) = constPt x ≫ z := by
  unfold constPt
  simp only [Category.assoc]

theorem base_map {K o V W : Type} [Field K] [CommRing o] [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V] [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W] (β : o →+* K)
    (L : V →ₗ[K] W) : spMap (TrivSqZeroExt.map L).toRingHom ≫ spMap ((algebraMap K (TrivSqZeroExt K V)).comp β) =
      spMap ((algebraMap K (TrivSqZeroExt K W)).comp β) := by
  rw [← spMap_comp']
  congr 1 <;> exact RingHom.ext fun z => (TrivSqZeroExt.map L).commutes (β z)

theorem fst_base {K o V : Type} [Field K] [CommRing o] [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V] (β : o →+* K) :
    spMap (TrivSqZeroExt.fstHom K K V).toRingHom ≫ spMap ((algebraMap K (TrivSqZeroExt K V)).comp β) = spMap β := by
  rw [← spMap_comp']
  congr 1 <;> exact RingHom.ext fun z => (TrivSqZeroExt.fstHom K K V).commutes (β z)

theorem constPt_base {K o : Type} [Field K] [CommRing o] {X : Scheme.{0}} (β : o →+* K) (x : Sp (DualNumber K) ⟶ X)
    (s : X ⟶ Sp o) (hx : x ≫ s = spMap ((algebraMap K (DualNumber K)).comp β)) :
    constPt x ≫ s = x ≫ s := by
  unfold constPt
  rw [Category.assoc, Category.assoc, hx, fst_base, ← spMap_comp']

theorem dirMap_comp {K : Type} [Field K] {r m : ℕ} (mu : (Fin m → K) →ₗ[K] K) (L : (Fin r → K) →ₗ[K] (Fin m → K)) :
    spMap (dirMap (mu ∘ₗ L)) = spMap (dirMap mu) ≫ spMap (TrivSqZeroExt.map L).toRingHom := by
  rw [← spMap_comp']
  congr 1 <;> exact RingHom.ext fun x => TrivSqZeroExt.ext (by simp [dirMap]) (by simp [dirMap])

def drop (K : Type) [Field K] (d : ℕ) : (Fin (d + 1) → K) →ₗ[K] (Fin d → K) := GlobalTheory.InnerAutomorphism.dropLast K d

def lastC (K : Type) [Field K] (d : ℕ) : (Fin (d + 1) → K) →ₗ[K] K := LinearMap.proj (Fin.last d)

def incl (K : Type) [Field K] (d : ℕ) : (Fin d → K) →ₗ[K] (Fin (d + 1) → K) where
  toFun w := Fin.snoc w 0
  map_add' w w' := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' a w := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem bij_drop_last (K : Type) [Field K] (d : ℕ) : Function.Bijective ((drop K d).prod (lastC K d)) := by
  refine ⟨fun v w hvw => ?_, fun p => ⟨Fin.snoc p.1 p.2, ?_⟩⟩
  · have h1 := congrArg Prod.fst hvw
    have h2 := congrArg Prod.snd hvw
    simp only [LinearMap.prod_apply, Pi.prod] at h1 h2
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact h2
    · exact congrFun h1 j
  · ext j <;> simp [drop, lastC]

theorem lam_decomp (K : Type) [Field K] (d : ℕ) (lam : (Fin (d + 1) → K) →ₗ[K] K) :
    lam = (lam ∘ₗ incl K d) ∘ₗ drop K d + lam (Pi.single (Fin.last d) 1) • lastC K d := by
  refine LinearMap.ext fun v => ?_
  have hv : v = incl K d (drop K d v) + v (Fin.last d) • Pi.single (Fin.last d) 1 := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [incl]
    · simp [incl, drop, Pi.single_apply, Fin.castSucc_ne_last]
  conv_lhs => rw [hv]
  simp [lastC, mul_comm]

theorem classified_dualNumber_of_algClosed : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (K : Type) [Field K] [IsAlgClosed K] (β₀ : cycAway n →+* K) (c : SiegPre g n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β₀))), c.Principal → ∃ f : Sp (DualNumber K) ⟶ F.X, f ≫ F.s = spMap ((algebraMap K (DualNumber K)).comp β₀) ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F K _ _ β₀ c hc

  obtain ⟨c₀, hc₀, hc₀p⟩ := pull_exists (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (fst_base β₀) c
  obtain ⟨x₀, hx₀s, hx₀⟩ := GlobalTheory.T.siegel_family_classifies_principal_algClosed g n hg hn hodd F K β₀ c₀ (hc₀p hc)

  obtain ⟨y, hy₀, hys, hyinj⟩ := GlobalTheory.T.exists_firstOrder_tangentPoint_smooth F.X F.s (g * (g + 1) / 2) F.smooth K β₀ x₀ hx₀s
  obtain ⟨cy, hcy, hcyp⟩ := pull_exists y hys F.univ
  have h0y : SiegPB c₀ cy (spMap (TrivSqZeroExt.fstHom K K (Fin (g * (g + 1) / 2) → K)).toRingHom) :=
    pb_cancel hcy (by rw [hy₀]; exact hx₀)

  have hsq := GlobalTheory.T.trivial_square_zero_extension_pullback K (Fin (g * (g + 1) / 2 + 1) → K) (Fin (g * (g + 1) / 2) → K) K (drop K _) (lastC K _)
    (bij_drop_last K _)
  let β : CommRingCat.of (cycAway n) ⟶ CommRingCat.of (TrivSqZeroExt K (Fin (g * (g + 1) / 2 + 1) → K)) :=
    CommRingCat.ofHom ((algebraMap K (TrivSqZeroExt K (Fin (g * (g + 1) / 2 + 1) → K))).comp β₀)
  obtain ⟨c₁, hc₁, hc₁p⟩ := pull_exists (𝟙 _)
    (s' := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (drop K (g * (g + 1) / 2))).toRingHom) ≫ Spec.map β)
    (by rw [Category.id_comp]; exact (base_map β₀ _).symm) cy
  obtain ⟨c₂, hc₂, hc₂p⟩ := pull_exists (𝟙 _)
    (s' := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (lastC K (g * (g + 1) / 2))).toRingHom) ≫ Spec.map β)
    (by rw [Category.id_comp]; exact (base_map β₀ _).symm) c
  obtain ⟨c₀', hc₀', -⟩ := pull_exists (𝟙 _)
    (s' := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K (Fin (g * (g + 1) / 2) → K)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (drop K (g * (g + 1) / 2))).toRingHom) ≫ Spec.map β)
    (by
      rw [Category.id_comp]
      exact ((congrArg (spMap (TrivSqZeroExt.fstHom K K (Fin (g * (g + 1) / 2) → K)).toRingHom ≫ ·)
        (base_map β₀ (drop K _))).trans (fst_base β₀)).symm) c₀
  have h01 : SiegPB c₀' c₁ (spMap (TrivSqZeroExt.fstHom K K (Fin (g * (g + 1) / 2) → K)).toRingHom) := by
    have := pb_comp (pb_comp (pb_symm hc₁) h0y) hc₀'
    rwa [Category.comp_id, Category.id_comp] at this
  have h02 : SiegPB c₀' c₂ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    have := pb_comp (pb_comp (pb_symm hc₂) hc₀) hc₀'
    rwa [Category.comp_id, Category.id_comp] at this
  obtain ⟨G, hGp, hG1, hG2⟩ := GlobalTheory.T.exists_principalSiegelObject_glue_artinFibreProduct g n hn hodd _ _ (CommRingCat.of (DualNumber K)) (CommRingCat.of K) _ _ _ _
    hsq (isLocalRing_tsze K _) (isArtinianRing_tsze K _) (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩)
    (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩) β c₁ c₂ (hc₁p (hcyp F.princ)) (hc₂p hc) ⟨c₀', h01, h02⟩
  have hGy : SiegPB cy G (spMap (TrivSqZeroExt.map (drop K (g * (g + 1) / 2))).toRingHom) := by
    have := pb_comp hG1 (pb_symm hc₁)
    rwa [Category.id_comp] at this
  have hGc : SiegPB c G (spMap (dirMap (lastC K (g * (g + 1) / 2)))) := by
    have := pb_comp hG2 (pb_symm hc₂)
    rwa [Category.id_comp] at this

  have htb := GlobalTheory.T.siegelFamily_tangentBound_nonconstant g n hg hn hodd K (g * (g + 1) / 2 + 1) β₀ G hGp
  obtain ⟨lam, c', h1, h2, hlam⟩ : ∃ (lam : (Fin (g * (g + 1) / 2 + 1) → K) →ₗ[K] K)
      (c' : SiegPre g n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β₀))),
      SiegPB c' G (spMap (dirMap lam)) ∧ SiegPB c' G (constPt (spMap (dirMap lam))) ∧ lam ≠ 0 := by
    by_contra hne
    push_neg at hne
    have := htb fun lam c' h1 h2 => hne lam c' h1 h2
    omega
  obtain ⟨mu, a, hdec⟩ : ∃ (mu : (Fin (g * (g + 1) / 2) → K) →ₗ[K] K) (a : K),
      lam = mu ∘ₗ drop K _ + a • lastC K _ := ⟨_, _, lam_decomp K _ lam⟩
  by_cases ha : a = 0
  ·
    exfalso
    rw [ha, zero_smul, add_zero] at hdec
    subst hdec
    rw [dirMap_comp] at h1 h2
    rw [constPt_comp] at h2
    have k1 : SiegPB c' F.univ (spMap (dirMap mu) ≫ y) := pb_comp hcy (pb_cancel hGy h1)
    have k2 : SiegPB c' F.univ (constPt (spMap (dirMap mu) ≫ y)) := by
      rw [constPt_comp]
      exact pb_comp hcy (pb_cancel hGy h2)
    have hxs : (spMap (dirMap mu) ≫ y) ≫ F.s = spMap ((algebraMap K (DualNumber K)).comp β₀) := by
      rw [Category.assoc, hys]
      exact base_map β₀ mu
    obtain ⟨c'', hc'', -⟩ := pull_exists (𝟙 _) (s' := (spMap (dirMap mu) ≫ y) ≫ F.s)
      (by rw [Category.id_comp, hxs]) c'
    have e := F.eq_constPt K (spMap (dirMap mu) ≫ y) c'' (constPt_base β₀ _ _ hxs).symm
      (by have := pb_comp k1 hc''; rwa [Category.id_comp] at this)
      (by have := pb_comp k2 hc''; rwa [Category.id_comp] at this)
    have := hyinj mu e
    subst this
    exact hlam (by simp)
  ·
    have hκ : lastC K (g * (g + 1) / 2) = ((-a⁻¹) • mu) ∘ₗ drop K _ + a⁻¹ • lam := by
      rw [hdec]
      refine LinearMap.ext fun v => ?_
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, neg_mul]
      field_simp
      ring
    have k := GlobalTheory.T.siegelObject_tangentShift_constancy_direction_iso g n hn hodd K _ β₀ G hGp lam _ _ a⁻¹ c' c hκ h1 h2 hGc
    rw [dirMap_comp] at k
    refine ⟨spMap (dirMap ((-a⁻¹) • mu)) ≫ y, ?_, pb_comp hcy (pb_cancel hGy k)⟩
    rw [Category.assoc, hys]
    exact base_map β₀ _

end GlobalTheory.FirstOrderSiegel

end
