import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem uj_neg_eq {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (s : A →+* A)
    (J : Matrix n n A) : Formalism.UG.UJ s (-J) = Formalism.UG.UJ s J := by
  ext g
  show Formalism.UG.cT s (g : Matrix n n A) * (-J) * (g : Matrix n n A) = -J ↔
    Formalism.UG.cT s (g : Matrix n n A) * J * (g : Matrix n n A) = J
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem hR_neg_eq {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : HR R σ (-J) = HR R σ J := by
  unfold HR JR
  rw [Matrix.map_neg _ (map_neg _), uj_neg_eq]

theorem hFin_neg_eq {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : HFin R σ (-J) = HFin R σ J := by
  unfold HFin
  rw [uj_neg_eq]

theorem unitary_neg_same : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J J' : Matrix (Fin M) (Fin M) E), J' = -J → ∃ φ : HA (AF F) σ J ≃ₜ* HA (AF F) σ J', (∀ h, HA.mat (AF F) σ J' (φ h) = HA.mat (AF F) σ J h) ∧ (∀ h, h ∈ HFinIn (AF F) σ J ↔ φ h ∈ HFinIn (AF F) σ J') ∧ ∀ (L : Set (Fin M → E)) h, h ∈ StabFin.SFin σ J L ↔ φ h ∈ StabFin.SFin σ J' L := by
  intro F E _ _ _ _ _ σ M J J' hJ
  subst hJ
  have e := (hR_neg_eq (AF F) σ J).symm
  let ψ : HA (AF F) σ J ≃* HA (AF F) σ (-J) := MulEquiv.subgroupCongr e
  have hψ : ∀ h : HA (AF F) σ J, HA.mat (AF F) σ (-J) (ψ h) = HA.mat (AF F) σ J h := fun h => rfl
  let φ : HA (AF F) σ J ≃ₜ* HA (AF F) σ (-J) :=
    { ψ with
      continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
      continuous_invFun := Continuous.subtype_mk continuous_subtype_val _ }
  have hφ : ∀ h : HA (AF F) σ J, HA.mat (AF F) σ (-J) (φ h) = HA.mat (AF F) σ J h := fun h => rfl
  refine ⟨φ, hφ, ?_, ?_⟩
  · intro h
    show (HA.mat (AF F) σ J h) ∈ HFin (AF F) σ J ↔ (HA.mat (AF F) σ (-J) (φ h)) ∈ HFin (AF F) σ (-J)
    rw [hFin_neg_eq]
    exact Iff.rfl
  · intro L h
    exact Iff.rfl

end GlobalTheory
