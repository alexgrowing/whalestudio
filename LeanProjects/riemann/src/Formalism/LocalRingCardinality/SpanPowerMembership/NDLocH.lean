import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocG

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc LB

def DeltaGap {R : Ranks} (H : Host R) {Ω : Type} [Field Ω] [Algebra H.E Ω] (cc : Ω ≃+* Ω) (p : ℕ) : Prop :=
  ∃ (N : ℕ) (_ : 0 < N) (δ : Formalism.ConjugateSelfDual.G H.E Ω →* Multiplicative (ZMod N)),
    IsOpen (δ.ker : Set (Formalism.ConjugateSelfDual.G H.E Ω)) ∧ AntiHom cc δ ∧ RamExactly δ (placesOver H.E p) ∧
    ∀ v ∈ placesOver H.E p, ∀ A : ValuationSubring Ω, IsPlaceOver A v →
      Nat.card ((Ine (F := H.E) A).map δ) = 15

structure RcgAt {R : Ranks} (H : Host R) {Ω : Type} [Field Ω] [Algebra H.E Ω] (cc : Ω ≃+* Ω) (l : ℕ) : Type 1 where
  RCG : Finset (HeightOneSpectrum (𝓞 H.E)) → Type
  [grpRCG : ∀ Q, CommGroup (RCG Q)]
  [finRCG : ∀ Q, Fintype (RCG Q)]
  RCG_l : ∀ Q (x : RCG Q), ∃ n : ℕ, x ^ (l ^ n) = 1
  art : ∀ Q, Formalism.ConjugateSelfDual.G H.E Ω →* RCG Q
  art_surj : ∀ Q, Function.Surjective (art Q)
  art_cont : ∀ Q, IsOpen ((art Q).ker : Set (Formalism.ConjugateSelfDual.G H.E Ω))
  art_anti : ∀ Q, AntiHom cc (art Q)
  art_unr : ∀ Q v, v ∉ Q → ∀ A : ValuationSubring Ω, IsPlaceOver A v →
    ∀ σ ∈ Ine (F := H.E) A, art Q σ = 1
  art_univ : ∀ Q, (∀ v ∈ Q, v ∉ placesOver H.E l) → ∀ (A' : Type) [CommGroup A'] [Finite A'],
    (∀ x : A', ∃ n : ℕ, x ^ (l ^ n) = 1) → ∀ φ : Formalism.ConjugateSelfDual.G H.E Ω →* A',
    IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G H.E Ω)) → AntiHom cc φ →
    (∀ v, v ∉ Q → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, φ σ = 1) →
    ∃ f : RCG Q →* A', f.comp (art Q) = φ
  res : ∀ (Q Q' : Finset (HeightOneSpectrum (𝓞 H.E))), Q' ⊆ Q → (RCG Q →* RCG Q')
  res_art : ∀ Q Q' (h : Q' ⊆ Q), (res Q Q' h).comp (art Q) = art Q'

attribute [instance] RcgAt.grpRCG RcgAt.finRCG

namespace TwB

variable {R : Ranks} (H : Host R) (F : Type) [Field F] [NumberField F]
  {Ω : Type} [Field Ω] [Algebra H.E Ω] {cc : Ω ≃+* Ω}

def pOf (l : ℕ) : ℕ := if l = H.pde then H.pde' else H.pde

variable (dg : ∀ l : ℕ, DeltaGap H cc (pOf H l))

def NOf (l : ℕ) : ℕ := (dg l).choose

instance (l : ℕ) : NeZero (NOf H dg l) := ⟨(dg l).choose_spec.choose.ne'⟩

def dOf (l : ℕ) : Formalism.ConjugateSelfDual.G H.E Ω →* Multiplicative (ZMod (NOf H dg l)) := (dg l).choose_spec.choose_spec.choose

theorem dOf_spec (l : ℕ) : IsOpen ((dOf H dg l).ker : Set (Formalism.ConjugateSelfDual.G H.E Ω)) ∧ AntiHom cc (dOf H dg l) ∧
    RamExactly (dOf H dg l) (placesOver H.E (pOf H l)) ∧
    ∀ v ∈ placesOver H.E (pOf H l), ∀ A : ValuationSubring Ω, IsPlaceOver A v →
      Nat.card ((Ine (F := H.E) A).map (dOf H dg l)) = 15 := (dg l).choose_spec.choose_spec.choose_spec

variable (l : ℕ) [hl : Fact l.Prime]

def zeta : PadicAlgCl l := (exists_prim l (NOf H dg l) (NeZero.pos _)).choose

theorem zeta_prim : IsPrimitiveRoot (zeta H dg l) (NOf H dg l) :=
  (exists_prim l (NOf H dg l) (NeZero.pos _)).choose_spec

def LLf : FinExt l :=
  ⟨KE l H.E ⊔ KE l F ⊔ IntermediateField.adjoin ℚ_[l] {zeta H dg l},
    haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] {zeta H dg l}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
    inferInstance⟩

theorem E_le : KE l H.E ≤ (LLf H F dg l).1 := le_sup_left.trans le_sup_left
theorem F_le : KE l F ≤ (LLf H F dg l).1 := le_sup_right.trans le_sup_left
theorem zeta_mem : zeta H dg l ∈ (LLf H F dg l).1 :=
  (le_sup_right : _ ≤ (LLf H F dg l).1) (IntermediateField.mem_adjoin_simple_self _ _)

def delta : Formalism.ConjugateSelfDual.G H.E Ω →* (↥(OL (LLf H F dg l)))ˣ :=
  (muHom (LLf H F dg l) (zeta_prim H dg l) (zeta_mem H F dg l)).comp (dOf H dg l)

theorem delta_eq_one (σ : Formalism.ConjugateSelfDual.G H.E Ω) : delta H F dg l σ = 1 ↔ dOf H dg l σ = 1 := by
  show muHom _ _ _ (dOf H dg l σ) = 1 ↔ _
  rw [← map_one (muHom (LLf H F dg l) (zeta_prim H dg l) (zeta_mem H F dg l))]
  exact (muHom_injective _ _ _).eq_iff

theorem delta_ker : (delta H F dg l).ker = (dOf H dg l).ker := by
  ext σ
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, delta_eq_one]

set_option synthInstance.maxHeartbeats 400000 in

def br [IsAlgClosure H.E Ω] (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) :
    LocBridge l H.E Ω (Dec (F := H.E) A) ↥(OL (LLf H F dg l)) :=
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap H.E Ω).injective
  haveI : IsAlgClosure ℚ Ω := isAlgClosureQ H.E Ω
  bridgeOf (exists_emb (l := l) A hA).choose_spec (LLf H F dg l) fun τ x =>
    E_le H F dg l (conj_mem_KE (jE (E := H.E) (exists_emb (l := l) A hA).choose) τ x)

end TwB

end Formalism.BasicNotions.Examples₂
