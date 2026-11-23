import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen

section Component

variable {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [Field K] [Algebra F K]
  [TopologicalSpace K]

def projB (P : PlaceMap F K) : AF F ⊗[F] E →ₐ[F] K ⊗[F] E :=
  Algebra.TensorProduct.map P.proj (AlgHom.id F E)

theorem projB_sigR (P : PlaceMap F K) (σ : E →ₐ[F] E) (y : AF F ⊗[F] E) :
    projB P (sigR (AF F) σ y) = sigR K σ (projB P y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [projB, sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem projB_inclR (P : PlaceMap F K) (e : E) : projB P (inclR (AF F) e) = inclR K e := by
  simp [projB, inclR]

theorem iB_projB (P : PlaceMap F K) (y : AF F ⊗[F] E) :
    iB P (projB P y) = algebraMap (AF F) (AF F ⊗[F] E) (P.inj 1) * y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp [projB, iB, P.inj_proj, Algebra.TensorProduct.algebraMap_apply]
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]

theorem cT_map_projB (P : PlaceMap F K) (σ : E →ₐ[F] E) {M : ℕ}
    (A : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) :
    Formalism.UG.cT (sigR K σ) (A.map (projB P)) = (Formalism.UG.cT (sigR (AF F) σ) A).map (projB P) := by
  ext i j
  simp [Formalism.UG.cT, projB_sigR]

theorem JR_map_projB (P : PlaceMap F K) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    (JR (F := F) (AF F) J).map (projB P) = JR (F := F) K J := by
  ext i j
  simp [JR, projB_inclR]

end Component

theorem exists_lift_of_mem_supp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E),
    ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J),
    IsLift P σ J L → ∀ g ∈ SUSupp σ J (P.inj 1), ∃ x : HA K σ J,
      ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 ∧ L x = g := by
  intro F E _ _ _ _ _ σ _ M J K _ _ P L hL g hg
  obtain ⟨hdet, hsupp⟩ := hg
  have hdet' := StrongApprox.mem_SUAdelic.1 hdet
  set G : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) := ((HA.mat (AF F) σ J g).1 : _) with hG
  let X : GL (Fin M) (K ⊗[F] E) := Formalism.UG.bc (projB P).toRingHom (HA.mat (AF F) σ J g)
  have hXG : (X : Matrix (Fin M) (Fin M) (K ⊗[F] E)) = G.map (projB P) := rfl
  have hg0 : Formalism.UG.cT (sigR (AF F) σ) G * JR (F := F) (AF F) J * G = JR (F := F) (AF F) J := g.2
  have hX : X ∈ HR K σ J := by
    change Formalism.UG.cT (sigR K σ) (X : Matrix (Fin M) (Fin M) (K ⊗[F] E)) * JR (F := F) K J * (X : Matrix (Fin M) (Fin M) (K ⊗[F] E)) = JR (F := F) K J
    have h1 := congrArg (fun A => (projB P).toRingHom.mapMatrix A) hg0
    simp only [map_mul] at h1
    rw [hXG, cT_map_projB, ← JR_map_projB P J]
    exact h1
  let x : HA K σ J := (⟨X, hX⟩ : HR K σ J)
  have hxm : ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) = G.map (projB P) := rfl
  refine ⟨x, ?_, ?_⟩
  · rw [hxm]
    have h2 := RingHom.map_det (projB P).toRingHom G
    rw [hdet'] at h2
    simpa using h2.symm
  · have hm : ((HA.mat (AF F) σ J (L x)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) = G := by
      ext i j
      have h3 := hL x i j
      have h4 : (((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) - 1) i j = projB P ((G - 1) i j) := by
        rw [hxm]
        by_cases hij : i = j
        · subst hij
          simp
        · simp [Matrix.one_apply_ne hij]
      rw [h4, iB_projB, hsupp i j] at h3
      exact sub_left_injective h3
    exact Subtype.ext (Units.ext hm)

end GlobalTheory.CompanionTheory.SaGen
