import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalHHermScal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeBetweenNonemptySpheresStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureIndependentChoicesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureSimilitudeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramFibreMeasureLocalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeScalingHermitianMeasureStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MassSimil

theorem JR_sim {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (γ : GL (Fin M) E) (l : F)
    (hγ : cT (σ : E →+* E) (γ : Matrix (Fin M) (Fin M) E) * J * (γ : Matrix (Fin M) (Fin M) E) = (algebraMap F E l) • J) :
    cT (sigR R σ) ((bc (inclR R) γ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
        ((bc (inclR R) γ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      (algebraMap R (R ⊗[F] E) (algebraMap F R l)) • JR R J := by
  rw [← GlobalTheory.CompanionTheory.SW.HIsom.JR_conj, hγ]
  ext i j
  change inclR R (algebraMap F E l * J i j) = algebraMap R (R ⊗[F] E) (algebraMap F R l) * inclR R (J i j)
  rw [map_mul]
  congr 1
  rw [← IsScalarTower.algebraMap_apply]
  exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes l

theorem simil : PositivityTheory.Rg.Mass.Simil := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ _ hli hlam hμ h𝓕 hmi hm β β' hβ hβ' hs hs' c hc
  have hl0 : β' / β ≠ 0 := div_ne_zero hβ' hβ
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.similitude_between_nonempty_spheres F E σ hcm J hJ β β' hβ hβ' hs hs'
  obtain ⟨μ', 𝓕', hμ', h𝓕', hth⟩ := GlobalTheory.T.theta_measure_similitude F E σ hcm 2 J hJ μ 𝓕 hμ h𝓕 γ (β' / β) hl0 hγ
  have hT : (fun _ _ => algebraMap F E β' : Matrix (Fin 1) (Fin 1) E) =
      (algebraMap F E (β' / β)) • (fun _ _ => algebraMap F E β : Matrix (Fin 1) (Fin 1) E) := by
    funext a b'
    change algebraMap F E β' = algebraMap F E (β' / β) * algebraMap F E β
    rw [← map_mul, div_mul_cancel₀ _ hβ]
  have hth1 := hth 1 _ _ hT
  have hind := GlobalTheory.T.theta_measure_independent_choices F E σ hcm 2 J hJ μ μ' 𝓕 𝓕' hμ h𝓕 hμ' h𝓕' 1 (fun _ _ => algebraMap F E β)
  change (thetaMeas σ J μ' 𝓕' (PositivityTheory.Rg.Mass.sph σ J β)).map _ = thetaMeas σ J μ 𝓕 (PositivityTheory.Rg.Mass.sph σ J β') at hth1
  change thetaMeas σ J μ 𝓕 (PositivityTheory.Rg.Mass.sph σ J β) = thetaMeas σ J μ' 𝓕' (PositivityTheory.Rg.Mass.sph σ J β) at hind
  obtain ⟨ai, a, hau, hai, hav⟩ := GlobalTheory.T.haar_modulus_gl_action_product_formula F E σ hcm 1 2 γ
  obtain ⟨ci, cv, hcu, hci, hcv⟩ := GlobalTheory.T.similitude_scaling_hermitian_measure F E σ hcm (β' / β) hl0
  obtain ⟨-, -, -, -, hq, -⟩ := PositivityTheory.PlacePermOperatorBicommutantSpan.up_alg F ai ci a cv hau hcu
  obtain ⟨⟨i1, i2, i3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have hLi : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hcm.1
  have hLv : ∀ v, IsLocR (Fv F v) := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  have hWi := SWIsom.haar_of_loc σ hcm (Ainf F) hLi b li hli.1 1 2
  have hWv := fun v => SWIsom.haar_of_loc σ hcm (Fv F v) (hLv v) b (lam v) (hlam v).1 1 2
  have hJR : ∀ (R : Type) [CommRing R] [Algebra F R],
      cT (sigR R σ) ((bc (inclR R) γ : GL (Fin 2) (R ⊗[F] E)) : Matrix (Fin 2) (Fin 2) (R ⊗[F] E)) * JR R J *
        ((bc (inclR R) γ : GL (Fin 2) (R ⊗[F] E)) : Matrix (Fin 2) (Fin 2) (R ⊗[F] E)) =
        (algebraMap R (R ⊗[F] E) (algebraMap F R (β' / β))) • JR R J := fun R _ _ => JR_sim R σ J γ _ hγ
  have hunit : ∀ (R : Type) [CommRing R] [Algebra F R] [Nontrivial R], IsUnit (algebraMap F R (β' / β)) :=
    fun R _ _ _ => (IsUnit.mk0 _ hl0).map _
  have sInf := GlobalTheory.T.gram_fibre_measure_local F E σ hcm 2 J hJ (Ainf F) hLi 1 _ _ mi hWi.1 hWi.2 hmi _ _ (hunit _) (hJR _) ai ci
    (hai _ hWi.1) (hci _ hWi.2)
  have sV := fun v => GlobalTheory.T.gram_fibre_measure_local F E σ hcm 2 J hJ (Fv F v) (hLv v) 1 _ _ (m v) (hWv v).1 (hWv v).2 (hm v) _ _ (hunit _)
    (hJR _) (a v) (cv v) (hav v _ (hWv v).1) (hcv v _ (hWv v).2)
  have hS : ∀ (R : Type) [CommRing R] [Algebra F R], scalH R σ (algebraMap F R (β' / β))
      (hermScal R σ (algebraMap F R β)) = hermScal R σ (algebraMap F R β') := fun R _ _ => by
    rw [scalH_hermScal, ← map_mul, div_mul_cancel₀ _ hβ]
  have hproj : ∀ X : Fin 1 → Fin 2 → AF F ⊗[F] E,
      projInf (actTup (AF F) (bc (inclR (AF F)) γ) X) =
          actTup (Ainf F) (bc (inclR (Ainf F)) γ) (projInf X) ∧
        ∀ v, projV v (projFin (actTup (AF F) (bc (inclR (AF F)) γ) X)) =
          actTup (Fv F v) (bc (inclR (Fv F v)) γ) (projV v (projFin X)) := by
    intro X
    refine ⟨?_, fun v => ?_⟩
    · funext a i
      exact SWIsom.map_actTup (fstA F) γ X a i
    · have h1 : projFin (actTup (AF F) (bc (inclR (AF F)) γ) X) =
          actTup (Af F) (bc (inclR (Af F)) γ) (projFin X) := by
        funext a i
        exact SWIsom.map_actTup (sndA F) γ X a i
      rw [h1]
      funext a i
      exact SWIsom.map_actTup (evalV F v) γ (projFin X) a i
  have hfin : ∀ v, m v (hermScal (Fv F v) σ (algebraMap F _ β')) (latV b v) < ⊤ := by
    intro v
    haveI := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hcm 2 J hJ (Fv F v) (hLv v) 1 _ _ (m v) (hWv v).1 (hWv v).2 (hm v)
      (hermScal (Fv F v) σ (algebraMap F _ β'))).1
    exact ((GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 2).2.2.2.1 v).1.measure_lt_top
  have key := euler_move_c F E σ hcm d b 1 2 (thetaMeas σ J μ' 𝓕' (PositivityTheory.Rg.Mass.sph σ J β)) (mi (hermScal (Ainf F) σ (algebraMap F _ β)))
    (mi (hermScal (Ainf F) σ (algebraMap F _ β')))
    (fun v => m v (hermScal (Fv F v) σ (algebraMap F _ β)))
    (fun v => m v (hermScal (Fv F v) σ (algebraMap F _ β')))
    (actTup (AF F) (bc (inclR (AF F)) γ))
    (actTup (Ainf F) (bc (inclR (Ainf F)) γ)) (fun v => actTup (Fv F v) (bc (inclR (Fv F v)) γ))
    (SWIsom.measurable_actTup σ hcm (AF F) _) (SWIsom.measurable_of_loc σ hcm (Ainf F) hLi _)
    (fun v => SWIsom.measurable_of_loc σ hcm (Fv F v) (hLv v) _) hproj
    ((GlobalTheory.CompanionTheory.SW.LatRat.latV_rational F E σ hcm d b 1 2).2.1 γ) (ai / ci) (fun v => a v / cv v) hq
    (by rw [sInf, hS]) (fun v => by rw [sV v, hS]) hfin c
  unfold PositivityTheory.Rg.Mass.EP at hc ⊢
  rw [hind] at hc
  rw [← hth1]
  exact key hc

end GlobalTheory.CompanionTheory.SW.MassSimil

end
