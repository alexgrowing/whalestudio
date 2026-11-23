import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import GroundTheory.GlobalFields.LocalAtPlace

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SaGen

structure PlaceMap (F K : Type) [Field F] [NumberField F] [Field K] [Algebra F K] [TopologicalSpace K] where

  proj : AF F →ₐ[F] K

  inj : K →ₙₐ[F] AF F
  proj_inj : ∀ x, proj (inj x) = x
  inj_proj : ∀ a, inj (proj a) = inj 1 * a
  cont_proj : Continuous proj
  cont_inj : Continuous inj

section Inhabitants

variable {F : Type} [Field F] [NumberField F]

theorem adele_ext {a b : AF F} (h1 : fstA F a = fstA F b) (h2 : sndA F a = sndA F b) : a = b :=
  Prod.ext h1 h2

theorem finAdele_ext {x y : Af F} (h : ∀ w, evalV F w x = evalV F w y) : x = y :=
  RestrictedProduct.ext _ _ h

theorem fstA_pairA (x : Ainf F) (y : Af F) : fstA F (pairA F x y) = x := rfl

theorem sndA_pairA (x : Ainf F) (y : Af F) : sndA F (pairA F x y) = y := rfl

theorem continuous_singleV' (v : HeightOneSpectrum (𝓞 F)) : Continuous (singleV F v) := by
  classical
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion F → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
      (Filter.principal ({v}ᶜ : Set _)) :=
    fun x => ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v x, by
      intro w hw
      have hw' : w ≠ v := hw
      simp only [Set.mem_ofPred_eq, Pi.single_eq_of_ne hw', SetLike.mem_coe]
      exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

theorem evalV_singleV_eq (v w : HeightOneSpectrum (𝓞 F)) (y : Fv F v) (f : ∀ u, Fv F u → Fv F u)
    (h0 : ∀ u, f u 0 = 0) :
    f w (evalV F w (singleV F v y)) = evalV F w (singleV F v (f v y)) := by
  by_cases h : w = v
  · subst h
    rw [StrongApprox.evalV_single_same, StrongApprox.evalV_single_same]
  · rw [StrongApprox.evalV_single_ne h, StrongApprox.evalV_single_ne h, h0]

def placeMapFin (v : HeightOneSpectrum (𝓞 F)) : PlaceMap F (Fv F v) where
  proj := (evalV F v).comp (sndA F)
  inj :=
    { toFun := fun y => pairA F 0 (singleV F v y)
      map_smul' := by
        intro c y
        refine adele_ext ?_ (finAdele_ext fun w => ?_)
        · rw [map_smul, fstA_pairA, fstA_pairA, smul_zero]
        · rw [map_smul, sndA_pairA, sndA_pairA, map_smul]
          exact (evalV_singleV_eq v w y (fun u t => c • t) (fun u => smul_zero c)).symm ▸ rfl
      map_zero' := by
        refine adele_ext rfl (finAdele_ext fun w => ?_)
        rw [sndA_pairA, map_zero, map_zero]
        by_cases h : w = v
        · subst h
          rw [StrongApprox.evalV_single_same]
        · rw [StrongApprox.evalV_single_ne h]
      map_add' := by
        intro x y
        refine adele_ext ?_ (finAdele_ext fun w => ?_)
        · rw [map_add, fstA_pairA, fstA_pairA, fstA_pairA, add_zero]
        · rw [map_add, sndA_pairA, sndA_pairA, sndA_pairA, map_add]
          by_cases h : w = v
          · subst h
            simp only [StrongApprox.evalV_single_same]
          · simp only [StrongApprox.evalV_single_ne h, add_zero]
      map_mul' := by
        intro x y
        refine adele_ext ?_ (finAdele_ext fun w => ?_)
        · rw [map_mul, fstA_pairA, fstA_pairA, fstA_pairA, mul_zero]
        · rw [map_mul, sndA_pairA, sndA_pairA, sndA_pairA, map_mul]
          by_cases h : w = v
          · subst h
            simp only [StrongApprox.evalV_single_same]
          · simp only [StrongApprox.evalV_single_ne h, mul_zero] }
  proj_inj := fun x => StrongApprox.evalV_single_same v x
  inj_proj := by
    intro a
    refine adele_ext ?_ (finAdele_ext fun w => ?_)
    · change (0 : Ainf F) = fstA F (pairA F 0 (singleV F v 1) * a)
      rw [map_mul, fstA_pairA, zero_mul]
    · change evalV F w (singleV F v (evalV F v (sndA F a))) = evalV F w (sndA F (pairA F 0 (singleV F v 1) * a))
      rw [map_mul, map_mul, sndA_pairA]
      by_cases h : w = v
      · subst h
        simp only [StrongApprox.evalV_single_same, one_mul]
      · simp only [StrongApprox.evalV_single_ne h, zero_mul]
  cont_proj := StrongApprox.continuous_evalV v
  cont_inj := continuous_const.prodMk (continuous_singleV' v)

open Classical in

def singleI (w : InfinitePlace F) (y : w.Completion) : Ainf F :=
  (Pi.single (M := fun u : InfinitePlace F => u.Completion) w y : ∀ u : InfinitePlace F, u.Completion)

open Classical in
theorem singleI_self (w : InfinitePlace F) (y : w.Completion) : (singleI w y : ∀ u : InfinitePlace F, u.Completion) w = y :=
  Pi.single_eq_same (M := fun u : InfinitePlace F => u.Completion) w y

open Classical in
theorem singleI_ne {w u : InfinitePlace F} (h : u ≠ w) (y : w.Completion) :
    (singleI w y : ∀ u : InfinitePlace F, u.Completion) u = 0 :=
  Pi.single_eq_of_ne (M := fun u : InfinitePlace F => u.Completion) h y

theorem ainf_ext {x y : Ainf F} (h : ∀ u, (x : ∀ u : InfinitePlace F, u.Completion) u = (y : ∀ u : InfinitePlace F, u.Completion) u) : x = y :=
  funext h

open Classical in

def placeMapInf (w : InfinitePlace F) : PlaceMap F w.Completion where
  proj := (Pi.evalAlgHom F (fun u : InfinitePlace F => u.Completion) w).comp (fstA F)
  inj :=
    { toFun := fun y => pairA F (singleI w y) 0
      map_smul' := by
        intro c y
        refine adele_ext ?_ ?_
        · rw [map_smul, fstA_pairA, fstA_pairA]
          exact Pi.single_smul (f := fun u : InfinitePlace F => u.Completion) w c y
        · rw [map_smul, sndA_pairA, sndA_pairA, smul_zero]
      map_zero' := by
        refine adele_ext ?_ rfl
        rw [fstA_pairA, map_zero]
        exact Pi.single_zero (M := fun u : InfinitePlace F => u.Completion) w
      map_add' := by
        intro x y
        refine adele_ext ?_ ?_
        · rw [map_add, fstA_pairA, fstA_pairA, fstA_pairA]
          exact Pi.single_add (f := fun u : InfinitePlace F => u.Completion) w x y
        · rw [map_add, sndA_pairA, sndA_pairA, sndA_pairA, add_zero]
      map_mul' := by
        intro x y
        refine adele_ext ?_ ?_
        · rw [map_mul, fstA_pairA, fstA_pairA, fstA_pairA]
          exact Pi.single_mul (α := fun u : InfinitePlace F => u.Completion) w x y
        · rw [map_mul, sndA_pairA, sndA_pairA, sndA_pairA, mul_zero] }
  proj_inj := fun x => singleI_self w x
  inj_proj := by
    intro a
    refine adele_ext ?_ ?_
    · change singleI w (fstA F a w) = fstA F (pairA F (singleI w 1) 0 * a)
      rw [map_mul, fstA_pairA]
      refine ainf_ext fun u => ?_
      change (singleI w (fstA F a w) : ∀ u : InfinitePlace F, u.Completion) u =
        (singleI w 1 : ∀ u : InfinitePlace F, u.Completion) u * fstA F a u
      by_cases h : u = w
      · subst h
        rw [singleI_self, singleI_self, one_mul]
      · rw [singleI_ne h, singleI_ne h, zero_mul]
    · change (0 : Af F) = sndA F (pairA F (singleI w 1) 0 * a)
      rw [map_mul, sndA_pairA, zero_mul]
  cont_proj := (continuous_apply w).comp continuous_fst
  cont_inj := (continuous_single w).prodMk continuous_const

theorem exists_placeMap_fin (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (K : Type) (_ : NontriviallyNormedField K) (_ : ProperSpace K) (_ : Algebra F K) (P : PlaceMap F K),
      IsPlacesIdem ∅ {v} (P.inj 1) := by
  letI nn : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
  haveI pr : ProperSpace (v.adicCompletion F) :=
    ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (v.adicCompletion F)
  refine ⟨v.adicCompletion F, nn, pr, inferInstance, placeMapFin v, ?_, ?_, ?_, ?_⟩
  · intro w hw
    exact absurd hw (Finset.notMem_empty w)
  · intro w _
    rfl
  · intro u hu
    rw [Finset.mem_singleton.1 hu]
    exact StrongApprox.evalV_single_same v 1
  · intro u hu
    exact StrongApprox.evalV_single_ne (fun h => hu (Finset.mem_singleton.2 h)) 1

theorem exists_placeMap_inf (w : InfinitePlace F) :
    ∃ (K : Type) (_ : NontriviallyNormedField K) (_ : ProperSpace K) (_ : Algebra F K) (P : PlaceMap F K),
      IsPlacesIdem {w} ∅ (P.inj 1) := by
  classical
  letI nn : NontriviallyNormedField w.Completion :=
    { (inferInstance : NormedField w.Completion) with
      non_trivial := ⟨2, by
        rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _),
          map_ofNat]
        simp⟩ }
  haveI pr : ProperSpace w.Completion :=
    ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace w.Completion
  refine ⟨w.Completion, nn, pr, inferInstance, placeMapInf w, ?_, ?_, ?_, ?_⟩
  · intro u hu
    rw [Finset.mem_singleton.1 hu]
    exact singleI_self w 1
  · intro u hu
    exact singleI_ne (fun h => hu (Finset.mem_singleton.2 h)) 1
  · intro u hu
    exact absurd hu (Finset.notMem_empty u)
  · intro u _
    exact map_zero (evalV F u)

end Inhabitants

section Ring

variable {R : Type} [CommRing R] {M : ℕ}

def qr (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a : Fin M → R) (k : R) : Matrix (Fin M) (Fin M) R :=
  1 + k • Matrix.vecMulVec a (fun j => ∑ i, c (a i) * Jm i j)

def IsQR (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (X : Matrix (Fin M) (Fin M) R) : Prop :=
  ∃ (a : Fin M → R) (l k : R), IsUnit (Formalism.UG.hform c Jm a a) ∧ l * c l = 1 ∧ k * Formalism.UG.hform c Jm a a = l - 1 ∧
    X = qr c Jm a k

def IsQPairOf (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a b : Fin M → R) (X : Matrix (Fin M) (Fin M) R) : Prop :=
  ∃ l ka kb : R, IsUnit (Formalism.UG.hform c Jm a a) ∧ IsUnit (Formalism.UG.hform c Jm b b) ∧ l * c l = 1 ∧
    ka * Formalism.UG.hform c Jm a a = l - 1 ∧ kb * Formalism.UG.hform c Jm b b = c l - 1 ∧ X = qr c Jm a ka * qr c Jm b kb

def IsQPair (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (X : Matrix (Fin M) (Fin M) R) : Prop :=
  ∃ a b, IsQPairOf c Jm a b X

def NormOneGen (c : R →+* R) : Prop :=
  ∀ α p : R, IsUnit α → c α = α →
    ∃ μ : R, μ * c μ = 1 ∧ IsUnit (α - μ * p) ∧ IsUnit (2 * α - μ * p - c (μ * p))

end Ring

section Lift

variable {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [Field K] [Algebra F K]
  [TopologicalSpace K]

def iB (P : PlaceMap F K) : K ⊗[F] E →ₗ[F] AF F ⊗[F] E :=
  TensorProduct.map { toFun := P.inj, map_add' := map_add _, map_smul' := map_smul _ } LinearMap.id

def IsLift (P : PlaceMap F K) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (L : HA K σ J →* HA (AF F) σ J) : Prop :=
  ∀ (x : HA K σ J) (i j : Fin M),
    (((HA.mat (AF F) σ J (L x)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j =
      iB P ((((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) - 1) i j)

end Lift

section Iso

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def incV (K : Type) [CommRing K] [Algebra F K] {M : ℕ} (x : Fin M → E) : Fin M → K ⊗[F] E :=
  fun i => inclR K (x i)

def IsoAt (K : Type) [CommRing K] [Algebra F K] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Prop :=
  ∃ u v : Fin M → K ⊗[F] E, hR K σ J u u = 0 ∧ hR K σ J u v = 1

def IsoPlane (K : Type) [CommRing K] [Algebra F K] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (a b : Fin M → K ⊗[F] E) : Prop :=
  hR K σ J a a * hR K σ J b b - hR K σ J a b * hR K σ J b a ≠ 0 ∧
    ∃ (x y : K ⊗[F] E) (z : Fin M → K ⊗[F] E),
      hR K σ J (x • a + y • b) (x • a + y • b) = 0 ∧ hR K σ J (x • a + y • b) z = 1

end Iso

end GlobalTheory.CompanionTheory.SaGen
