import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.JPMemAwayP
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.RepTie
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.FiniteClassSetOfLe
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsFib
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsLat
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G.Cmp

def bcE {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n] (e : A ≃+* B) : GL n A ≃* GL n B :=
  Units.mapEquiv (RingEquiv.mapMatrix e).toMulEquiv

theorem bcE_symm_apply {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n] (e : A ≃+* B) (g : GL n B)
    (a b : n) : ((bcE e).symm g : Matrix n n A) a b = e.symm ((g : Matrix n n B) a b) := rfl

theorem castGL_symm_apply {a b : ℕ} (h : a = b) (R : Type) [CommRing R] (g : GL (Fin b) R) (x y : Fin a) :
    ((castGL h R).symm g : Matrix (Fin a) (Fin a) R) x y = (g : Matrix (Fin b) (Fin b) R) (Fin.cast h x) (Fin.cast h y) := by
  first
  | rfl
  | (subst h; rfl)
  | simp [castGL]

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

abbrev fstV (I : LocId L p nV W Qq) (v : Fin nV) : E ⊗[F] (I.plc v).adicCompletion F →+* (I.plc v).adicCompletion F :=
  (RingHom.fst _ _).comp (I.spl (I.plc v) (I.pl v).2).toRingHom

abbrev frV (I : LocId L p nV W Qq) (v : Fin nV) : GL (Fin R.k) ((I.plc v).adicCompletion F) := I.fr (I.plc v) (I.pl v).2

def toF (I : LocId L p nV W Qq) {m : ℕ} (hk : m + 1 = R.k) (v : Fin nV) :
    GL (Fin (m + 1)) Qq ≃* GL (Fin R.k) ((I.plc v).adicCompletion F) :=
  ((castGL hk Qq).trans (bcE (I.eQ v))).trans (MulAut.conj (frV I v))

theorem toF_symm (I : LocId L p nV W Qq) {m : ℕ} (hk : m + 1 = R.k) (v : Fin nV)
    (X : GL (Fin R.k) ((I.plc v).adicCompletion F)) :
    (toF I hk v).symm X = (castGL hk Qq).symm ((bcE (I.eQ v)).symm ((frV I v)⁻¹ * X * frV I v)) := rfl

abbrev GA (sp : Spaces R F E) : Type := UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)

def prP (I : LocId L p nV W Qq) {m : ℕ} (hk : m + 1 = R.k) : GA sp →* (Fin nV → GL (Fin (m + 1)) Qq) :=
  MonoidHom.pi fun v => (toF I hk v).symm.toMonoidHom.comp
    ((bc (fstV I v)).comp ((bc (prV (E := E) (I.plc v))).comp (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)).subtype))

theorem prP_apply (I : LocId L p nV W Qq) {m : ℕ} (hk : m + 1 = R.k) (x : GA sp) (v : Fin nV) :
    prP I hk x v = (toF I hk v).symm (bc (fstV I v) (bc (prV (E := E) (I.plc v)) (x : GL (Fin R.k) _))) := rfl

def jQ (I : LocId L p nV W Qq) (hdet : IsUnit sp.gram0.det) {m : ℕ} (hk : m + 1 = R.k) :
    (Fin nV → GL (Fin (m + 1)) Qq) →* GA sp :=
  (jP I hdet).comp (MonoidHom.pi fun v => (toF I hk v).toMonoidHom.comp (Pi.evalMonoidHom _ v))

theorem prP_jQ (I : LocId L p nV W Qq) (hdet : IsUnit sp.gram0.det) {m : ℕ} (hk : m + 1 = R.k)
    (g : Fin nV → GL (Fin (m + 1)) Qq) : prP I hk (jQ I hdet hk g) = g := by
  funext v
  rw [prP_apply]
  have := jP_at I hdet (fun v => toF I hk v (g v)) v
  show (toF I hk v).symm (bc (fstV I v) (bc (prV (E := E) (I.plc v)) (jP I hdet (fun v => toF I hk v (g v)) : GL (Fin R.k) _))) = g v
  rw [this, MulEquiv.symm_apply_apply]

def HypAtP (I : LocId L p nV W Qq) : Prop :=
  ∀ (v : Fin nV) (x : GL (Fin R.k) (E ⊗[F] (I.plc v).adicCompletion F)),
    x ∈ UPts sp.cm.sig sp.gram0 ((I.plc v).adicCompletion F) →
    (x ∈ L.Uloc (I.plc v) ↔
      (∀ a b, (((frV I v)⁻¹ * bc (fstV I v) x * frV I v : GL (Fin R.k) _) : Matrix (Fin R.k) (Fin R.k) _) a b ∈
        (I.plc v).adicCompletionIntegers F) ∧
      ∀ a b, ((((frV I v)⁻¹ * bc (fstV I v) x * frV I v)⁻¹ : GL (Fin R.k) _) : Matrix (Fin R.k) (Fin R.k) _) a b ∈
        (I.plc v).adicCompletionIntegers F)

theorem toF_symm_stab (I : LocId L p nV W Qq) {m : ℕ} (hk : m + 1 = R.k) (v : Fin nV)
    (X : GL (Fin R.k) ((I.plc v).adicCompletion F)) :
    (toF I hk v).symm X ∈ stabStd (k := m + 1) (Qq := Qq) W ↔
      (∀ a b, (((frV I v)⁻¹ * X * frV I v : GL (Fin R.k) _) : Matrix (Fin R.k) (Fin R.k) _) a b ∈
        (I.plc v).adicCompletionIntegers F) ∧
      ∀ a b, ((((frV I v)⁻¹ * X * frV I v)⁻¹ : GL (Fin R.k) _) : Matrix (Fin R.k) (Fin R.k) _) a b ∈
        (I.plc v).adicCompletionIntegers F := by
  rw [stabStd_iff, ← map_inv, toF_symm, toF_symm]
  have key : ∀ M : GL (Fin R.k) ((I.plc v).adicCompletion F),
      (∀ a b, ((castGL hk Qq).symm ((bcE (I.eQ v)).symm M) : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) a b ∈
        (algebraMap W Qq).range) ↔ ∀ a b, (M : Matrix (Fin R.k) (Fin R.k) _) a b ∈ (I.plc v).adicCompletionIntegers F := by
    intro M
    have h1 : ∀ a b, ((castGL hk Qq).symm ((bcE (I.eQ v)).symm M) : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) a b ∈
        (algebraMap W Qq).range ↔ (M : Matrix (Fin R.k) (Fin R.k) _) (Fin.cast hk a) (Fin.cast hk b) ∈
          (I.plc v).adicCompletionIntegers F := by
      intro a b
      rw [castGL_symm_apply, bcE_symm_apply]
      have := I.completion_integers_iff v ((I.eQ v).symm ((M : Matrix (Fin R.k) (Fin R.k) _) (Fin.cast hk a) (Fin.cast hk b)))
      rw [RingEquiv.apply_symm_apply] at this
      exact this
    constructor
    · intro h a b
      have := (h1 (Fin.cast hk.symm a) (Fin.cast hk.symm b)).1 (h _ _)
      simpa using this
    · intro h a b
      exact (h1 a b).2 (h _ _)
  have e : (frV I v)⁻¹ * X⁻¹ * frV I v = ((frV I v)⁻¹ * X * frV I v)⁻¹ := by group
  rw [key, e, key]

def fibP (I : LocId L p nV W Qq) (hdet : IsUnit sp.gram0.det) {m : ℕ} (hk : m + 1 = R.k) (hH : HypAtP I) :
    Fib (L.U.subgroupOf (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)))
      ((Formalism.L2.Herm.awayFrom₂ L p).subgroupOf (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)))
      (stabTup (nV := nV) (k := m + 1) (Qq := Qq) W) where
  j := jQ I hdet hk
  pr := prP I hk
  pr_j := prP_jQ I hdet hk
  j_mem := fun g => Subgroup.mem_subgroupOf.2 (jP_mem_awayP I hdet _)
  K_iff := by
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, L.U_eq, mem_stabTup]
    have hloc : ∀ v : Fin nV, bc (prV (E := E) (I.plc v)) (x : GL (Fin R.k) _) ∈ L.Uloc (I.plc v) ↔
        prP I hk x v ∈ stabStd (k := m + 1) (Qq := Qq) W := by
      intro v
      rw [prP_apply, toF_symm_stab]
      exact hH v _ (Formalism.UG.P.afsplit_bc_mem sp.cm.sig sp.gram0 (I.plc v) _ x.2)
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨Subgroup.mem_inf.2 ⟨h1, ?_⟩, fun v => (hloc v).1 (h2 _)⟩
      simp only [Subgroup.mem_iInf]
      intro v _
      exact h2 v
    · rintro ⟨h1, h2⟩
      obtain ⟨h3, h4⟩ := Subgroup.mem_inf.1 h1
      refine ⟨h3, fun v => ?_⟩
      by_cases hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal
      · obtain ⟨v', rfl⟩ : ∃ v', I.plc v' = v := ⟨I.pl.symm ⟨v, hv⟩, by simp [LocId.plc]⟩
        exact (hloc v').2 (h2 v')
      · simp only [Subgroup.mem_iInf] at h4
        exact h4 v hv

end Formalism.L2.G.Cmp
