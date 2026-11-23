import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners

noncomputable section

open scoped Classical

namespace GlobalTheory.IndefiniteRowSideFullHecke.DiscriminantKernelAutomorphisms

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section AnyLat

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def autGrp (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule (𝓞 K) V) : Subgroup (V ≃ₗ[K] V) where
  carrier := Formalism.ThetaLiftIndependence.autL h M
  one_mem' := ⟨(Formalism.HermitianLatticesTheory.isom h).one_mem, by ext x; simp [Formalism.HermitianLatticesTheory.gmap]⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(Formalism.HermitianLatticesTheory.isom h).mul_mem ha hb, ?_⟩
    have e : Formalism.HermitianLatticesTheory.gmap (a * b) M = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b M) := by
      unfold Formalism.HermitianLatticesTheory.gmap
      rw [← Submodule.map_comp]
      rfl
    rw [e, hb', ha']
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(Formalism.HermitianLatticesTheory.isom h).inv_mem ha, ?_⟩
    have e : Formalism.HermitianLatticesTheory.gmap a⁻¹ (Formalism.HermitianLatticesTheory.gmap a M) = M := by
      unfold Formalism.HermitianLatticesTheory.gmap
      rw [← Submodule.map_comp]
      have : (((a⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V).restrictScalars (𝓞 K)) ∘ₗ
          ((a : V →ₗ[K] V).restrictScalars (𝓞 K)) = LinearMap.id := by
        ext x
        exact a.symm_apply_apply x
      rw [this, Submodule.map_id]
    rwa [ha'] at e

def discKerAt (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule (𝓞 K) V) (P : Ideal (𝓞 K)) : Set (V ≃ₗ[K] V) :=
  {γ | γ ∈ Formalism.HermitianLatticesTheory.isom h ∧
    Formalism.HermitianLatticesTheory.gmap γ (Formalism.HermitianLatticesTheory.loc (K := K) P M) = Formalism.HermitianLatticesTheory.loc (K := K) P M ∧
    ∀ x ∈ Formalism.HermitianLatticesTheory.loc (K := K) P (Formalism.HermitianLatticesTheory.dual h M), γ x - x ∈ Formalism.HermitianLatticesTheory.loc (K := K) P M}

end AnyLat

section Row

variable (D : D7)

def sumMap {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) :
    ((D.sp.X 0).V × D.host.E) →ₗ[D.host.E] (VS D).V :=
  (D.sp.iXY 0).coprod (LinearMap.toSpanSingleton D.host.E (VS D).V F0.z)

def latL {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LatV D) :
    Submodule (𝓞 D.host.E) ((D.sp.X 0).V × D.host.E) :=
  (Lsub Λ (lf D F0)).comap ((sumMap D F0).restrictScalars (𝓞 D.host.E))

abbrev flagPairDefinitePartLattice {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LatV D) :
    Submodule (𝓞 D.host.E) (D.sp.X 0).V :=
  L0X D Λ (lf D F0)

def massFlagLatticeZero {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LatV D) : ℝ :=
  Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT (flagPairDefinitePartLattice D F0 Λ)

def stabPairAt {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LatV D) (P : Ideal (𝓞 D.host.E)) :
    Set ((D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) :=
  {γ | γ ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT ∧
    Formalism.HermitianLatticesTheory.gmap (γ.prodCongr (LinearEquiv.refl D.host.E D.host.E))
              (Formalism.HermitianLatticesTheory.loc (K := D.host.E) P (latL D F0 Λ)) =
      Formalism.HermitianLatticesTheory.loc (K := D.host.E) P (latL D F0 Λ)}

def HidaSetting (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : LatV D) : Prop :=
  F0.e = D.sp.hypE ∧ F0.z = D.zmOf u ∧ (Tu D u).Prime ∧ SplitsCompletely (E := D.host.E) (Tu D u) ∧
    IsRowLat D F0 Λ

end Row

def RowMasses : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : LatV D),
    HidaSetting D u F0 Λ →
      (∀ s : Finset (LatV D), IsRowReps D F0 s →
        massRows D F0 s = massS D D.R.k * (((Tu D u : ℕ) : ℝ) ^ D.R.k - 1) ^ D.R.f ∧
        massFlagLatticeZero D F0 Λ = massRows D F0 s / (((Tu D u : ℕ) : ℝ) - 1) ^ D.R.f) ∧
      massFlagLatticeZero D F0 Λ = massS D D.R.k * (∑ i ∈ Finset.range D.R.k, ((Tu D u : ℕ) : ℝ) ^ i) ^ D.R.f ∧
      massS D D.R.k * NT D u ^ (D.R.k - 1) ≤ massFlagLatticeZero D F0 Λ

def RowRepsExist : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : LatV D),
    HidaSetting D u F0 Λ → ∃ s : Finset (LatV D), IsRowReps D F0 s

def KernelIsStabiliser : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : LatV D),
    HidaSetting D u F0 Λ → ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal →
      discKerAt (D.sp.X 0).hT (flagPairDefinitePartLattice D F0 Λ) P = stabPairAt D F0 Λ P

def DiamondQuotient : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : LatV D),
    HidaSetting D u F0 Λ →
      omegaF D.host.F (Tu D u) = D.R.f ∧
      (∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → ((Tu D u : ℕ) : 𝓞 D.host.E) ∈ P →
        Nonempty ((𝓞 D.host.F ⧸ P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))) ≃+* ZMod (Tu D u)) ∧
        ∃ χ : autGrp (D.sp.X 0).hT (Formalism.HermitianLatticesTheory.loc (K := D.host.E) P (flagPairDefinitePartLattice D F0 Λ)) →*
            (𝓞 D.host.F ⧸ P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)))ˣ,
          Function.Surjective χ ∧
          ∀ γ, χ γ = 1 ↔ γ.1 ∈ discKerAt (D.sp.X 0).hT (flagPairDefinitePartLattice D F0 Λ) P) ∧
      levelIdx (D.sp.X 0).hT (flagPairDefinitePartLattice D F0 Λ) (Tu D u ^ D.R.f) = (Tu D u - 1) ^ D.R.f

def RowMassesFull : Prop :=
  KernelIsStabiliser ∧ DiamondQuotient ∧ RowRepsExist ∧ RowMasses

theorem mem_orthModIsotropicLatticePerpNegative_iff (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (hz : F0.z = D.zmOf u) (Λ : LatV D) (w : (D.sp.X 0).V) :
    w ∈ flagPairDefinitePartLattice D F0 Λ ↔ (w, (0 : D.host.E)) ∈ latL D F0 Λ := by
  have h0 : (VS D).hT F0.z (D.sp.iXY 0 w) = 0 := by
    have h1 : (VS D).hT (D.sp.iXY 0 w) F0.z = 0 := by
      rw [hz, D7.zmOf, map_smul, D.sp.zm_orth w, smul_zero]
    have h2 := (VS D).herm.eq (D.sp.iXY 0 w) F0.z
    rw [h1, map_zero] at h2
    exact h2.symm
  simp [flagPairDefinitePartLattice, L0X, L0sub, latL, sumMap, h0]

example (T : ℝ) (hT : T ≠ 1) (k f : ℕ) :
    (T ^ k - 1) ^ f / (T - 1) ^ f = (∑ i ∈ Finset.range k, T ^ i) ^ f := by
  rw [← div_pow, geom_sum_eq hT]

end GlobalTheory.IndefiniteRowSideFullHecke.DiscriminantKernelAutomorphisms

end
