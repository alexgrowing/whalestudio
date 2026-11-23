import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.HermitianLattices.HermitianLatticesProofs.MassTelescope
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DiscriminantKernelAutomorphisms

noncomputable section

open scoped Classical

namespace GlobalTheory.RowMassCompare

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.IndefiniteRowSideFullHecke.DiscriminantKernelAutomorphisms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pieces

variable (D : D7) (u : D.what₂.Word)

def FixedFlagSetting (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) : Prop :=
  F0.e = D.sp.hypE ∧ F0.z = D.zmOf u ∧ (Tu D u).Prime ∧ SplitsCompletely (E := D.host.E) (Tu D u)

def RepsPart : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : LatV D), HidaSetting D u F0 Λ →
    ∀ s : Finset (LatV D), IsRowReps D F0 s →
      massRows D F0 s = massS D D.R.k * (((Tu D u : ℕ) : ℝ) ^ D.R.k - 1) ^ D.R.f ∧
      massFlagLatticeZero D F0 Λ = massRows D F0 s / (((Tu D u : ℕ) : ℝ) - 1) ^ D.R.f

def LatPart : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : LatV D), HidaSetting D u F0 Λ →
    massFlagLatticeZero D F0 Λ = massS D D.R.k * (∑ i ∈ Finset.range D.R.k, ((Tu D u : ℕ) : ℝ) ^ i) ^ D.R.f ∧
    massS D D.R.k * NT D u ^ (D.R.k - 1) ≤ massFlagLatticeZero D F0 Λ

def RowMassesAt : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : LatV D), HidaSetting D u F0 Λ →
    (∀ s : Finset (LatV D), IsRowReps D F0 s →
      massRows D F0 s = massS D D.R.k * (((Tu D u : ℕ) : ℝ) ^ D.R.k - 1) ^ D.R.f ∧
      massFlagLatticeZero D F0 Λ = massRows D F0 s / (((Tu D u : ℕ) : ℝ) - 1) ^ D.R.f) ∧
    massFlagLatticeZero D F0 Λ = massS D D.R.k * (∑ i ∈ Finset.range D.R.k, ((Tu D u : ℕ) : ℝ) ^ i) ^ D.R.f ∧
    massS D D.R.k * NT D u ^ (D.R.k - 1) ≤ massFlagLatticeZero D F0 Λ

def RowLatExistsAt : Prop :=
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), FixedFlagSetting D u F0 → ∃ Λ : LatV D, IsRowLat D F0 Λ

def RowRepsExistAt : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : LatV D), HidaSetting D u F0 Λ →
    ∃ s : Finset (LatV D), IsRowReps D F0 s

end Pieces

def RowLatExists : Prop := ∀ (D : D7) (u : D.what₂.Word), RowLatExistsAt D u

def RowDescent : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)), FixedFlagSetting D u F0 →
    ∀ Λ Λ' : LatV D, IsRowLat D F0 Λ → IsRowLat D F0 Λ' →
    ∀ γ ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT,
      Formalism.HermitianLatticesTheory.gmap (γ.prodCongr (LinearEquiv.refl D.host.E D.host.E)) (latL D F0 Λ') = latL D F0 Λ →
      ∃ δ ∈ stabF D F0, Formalism.HermitianLatticesTheory.gmap δ Λ' = Λ

def PairsFinite : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)), FixedFlagSetting D u F0 →
    ∃ S : Finset (Submodule (𝓞 D.host.E) ((D.sp.X 0).V × D.host.E)),
      ∀ Λ : LatV D, IsRowLat D F0 Λ → ∃ M ∈ S, ∃ γ ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT,
        Formalism.HermitianLatticesTheory.gmap (γ.prodCongr (LinearEquiv.refl D.host.E D.host.E)) M = latL D F0 Λ

section Gmap

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem gmap_mul' (a b : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) M = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b M) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [← Submodule.map_comp]
  rfl

theorem gmap_one' (M : Submodule (𝓞 K) V) : Formalism.HermitianLatticesTheory.gmap (1 : V ≃ₗ[K] V) M = M := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

end Gmap

section Stab

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem one_mem_stabF : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ stabF D F0 :=
  ⟨(Formalism.HermitianLatticesTheory.isom _).one_mem, fun j => Submodule.map_id _, rfl⟩

theorem mul_mem_stabF {a b : (VS D).V ≃ₗ[D.host.E] (VS D).V} (ha : a ∈ stabF D F0) (hb : b ∈ stabF D F0) :
    a * b ∈ stabF D F0 := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ha.1 hb.1, fun j => ?_, ?_⟩
  · have : ((a * b : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) =
        (a : (VS D).V →ₗ[D.host.E] (VS D).V) ∘ₗ (b : (VS D).V →ₗ[D.host.E] (VS D).V) := rfl
    rw [this, Submodule.map_comp, hb.2.1 j, ha.2.1 j]
  · show a (b F0.z) = F0.z
    rw [hb.2.2, ha.2.2]

theorem inv_mem_stabF {a : (VS D).V ≃ₗ[D.host.E] (VS D).V} (ha : a ∈ stabF D F0) : a⁻¹ ∈ stabF D F0 := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom _).inv_mem ha.1, fun j => ?_, ?_⟩
  · conv_lhs => rw [← ha.2.1 j]
    rw [← Submodule.map_comp]
    have : ((a⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) ∘ₗ
        (a : (VS D).V →ₗ[D.host.E] (VS D).V) = LinearMap.id := by
      ext x
      exact a.symm_apply_apply x
    rw [this, Submodule.map_id]
  · show a.symm F0.z = F0.z
    rw [LinearEquiv.symm_apply_eq, ha.2.2]

def rowSetoid : Setoid {Λ : LatV D // IsRowLat D F0 Λ} where
  r A B := ∃ γ ∈ stabF D F0, Formalism.HermitianLatticesTheory.gmap γ A.1 = B.1
  iseqv :=
    ⟨fun A => ⟨1, one_mem_stabF D F0, gmap_one' _⟩,
      fun ⟨γ, hγ, h⟩ => ⟨γ⁻¹, inv_mem_stabF D F0 hγ, by rw [← h, ← gmap_mul', inv_mul_cancel, gmap_one']⟩,
      fun ⟨γ, hγ, h⟩ ⟨δ, hδ, h'⟩ => ⟨δ * γ, mul_mem_stabF D F0 hδ hγ, by rw [gmap_mul', h, h']⟩⟩

end Stab

end GlobalTheory.RowMassCompare

end
