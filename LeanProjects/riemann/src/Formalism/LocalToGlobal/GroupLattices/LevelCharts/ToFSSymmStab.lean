import Formalism.LocalToGlobal.GroupLattices.LevelCharts.LevelsOfCh
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.CastGLSymmApply

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G Formalism.L2.G.Cmp
open scoped TensorProduct

namespace Formalism.L2.G

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

structure StepG (I : LocId L p nV W Qq) (N : ℕ) where
  J : Matrix (Fin N) (Fin N) E
  hJ : IsHerm (sp.cm.sig : E →+* E) J
  hdet : IsUnit J.det
  Lb : Submodule (𝓞 E) (Fin N → E)
  Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F))
  fr : FrS I Lb
  U : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  U_eq : ∀ x, x ∈ U ↔ x ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) x ∈ Uloc v

variable {I : LocId L p nV W Qq} {N : ℕ}

def StepG.uGL (S : StepG I N) (v : Fin nV) :
    UPts sp.cm.sig S.J ((I.plc v).adicCompletion F) ≃* GL (Fin N) ((I.plc v).adicCompletion F) :=
  locGL sp.cm.sig S.J S.hJ S.hdet _ (I.spl (I.plc v) (I.pl v).2) (I.spl_sig (I.plc v) (I.pl v).2)

def jPS (S : StepG I N) :
    (∀ v : Fin nV, GL (Fin N) ((I.plc v).adicCompletion F)) →* UPts sp.cm.sig S.J (FiniteAdeleRing (𝓞 F) F) :=
  (secAll F E sp.cm.sig S.J I.plc I.plc_inj).comp
    (MonoidHom.pi fun v => (S.uGL v).symm.toMonoidHom.comp (Pi.evalMonoidHom _ v))

theorem jPS_at (S : StepG I N) (g : ∀ v : Fin nV, GL (Fin N) ((I.plc v).adicCompletion F)) (v : Fin nV) :
    bc ((RingHom.fst _ _).comp (I.spl (I.plc v) (I.pl v).2).toRingHom)
      (bc (prV (E := E) (I.plc v)) (jPS S g : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) = g v := by
  show bc _ (bc (prV (E := E) (I.plc v)) (secAll F E sp.cm.sig S.J I.plc I.plc_inj _ : GL (Fin N) _)) = g v
  rw [bc_secAll_same]
  have := locGL_apply sp.cm.sig S.J S.hJ S.hdet _ (I.spl (I.plc v) (I.pl v).2)
    (I.spl_sig (I.plc v) (I.pl v).2) ((S.uGL v).symm (g v))
  exact this.symm.trans ((S.uGL v).apply_symm_apply (g v))

theorem jPS_off (S : StepG I N) (g : ∀ v : Fin nV, GL (Fin N) ((I.plc v).adicCompletion F))
    (w' : HeightOneSpectrum (𝓞 F)) (hw : ((p : ℕ) : 𝓞 F) ∉ w'.asIdeal) :
    bc (prV (E := E) w') (jPS S g : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = 1 :=
  bc_secAll_off F E sp.cm.sig S.J I.plc I.plc_inj w' (fun v h => hw (h ▸ (I.pl v).2)) _

theorem jPS_mem_awayG (S : StepG I N) (g : ∀ v : Fin nV, GL (Fin N) ((I.plc v).adicCompletion F)) :
    (jPS S g : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ awayG sp.cm.sig S.J S.Uloc p := by
  refine (mem_awayG sp.cm.sig S.J S.Uloc p _).2 ⟨(jPS S g).2, ?_⟩
  intro v hv
  rw [jPS_off S g v hv]
  exact Subgroup.one_mem _

abbrev frVS (S : StepG I N) (v : Fin nV) : GL (Fin N) ((I.plc v).adicCompletion F) := S.fr.fr (I.plc v) (I.pl v).2

def toFS (S : StepG I N) {m : ℕ} (hk : m + 1 = N) (v : Fin nV) :
    GL (Fin (m + 1)) Qq ≃* GL (Fin N) ((I.plc v).adicCompletion F) :=
  ((castGL hk Qq).trans (bcE (I.eQ v))).trans (MulAut.conj (frVS S v))

theorem toFS_symm (S : StepG I N) {m : ℕ} (hk : m + 1 = N) (v : Fin nV)
    (X : GL (Fin N) ((I.plc v).adicCompletion F)) :
    (toFS S hk v).symm X = (castGL hk Qq).symm ((bcE (I.eQ v)).symm ((frVS S v)⁻¹ * X * frVS S v)) := rfl

abbrev GAS (S : StepG I N) : Type := UPts sp.cm.sig S.J (FiniteAdeleRing (𝓞 F) F)

def prPS (S : StepG I N) {m : ℕ} (hk : m + 1 = N) : GAS S →* (Fin nV → GL (Fin (m + 1)) Qq) :=
  MonoidHom.pi fun v => (toFS S hk v).symm.toMonoidHom.comp
    ((bc (fstV I v)).comp ((bc (prV (E := E) (I.plc v))).comp (UPts sp.cm.sig S.J (FiniteAdeleRing (𝓞 F) F)).subtype))

theorem prPS_apply (S : StepG I N) {m : ℕ} (hk : m + 1 = N) (x : GAS S) (v : Fin nV) :
    prPS S hk x v = (toFS S hk v).symm (bc (fstV I v) (bc (prV (E := E) (I.plc v)) (x : GL (Fin N) _))) := rfl

def jQS (S : StepG I N) {m : ℕ} (hk : m + 1 = N) : (Fin nV → GL (Fin (m + 1)) Qq) →* GAS S :=
  (jPS S).comp (MonoidHom.pi fun v => (toFS S hk v).toMonoidHom.comp (Pi.evalMonoidHom _ v))

theorem prPS_jQS (S : StepG I N) {m : ℕ} (hk : m + 1 = N) (g : Fin nV → GL (Fin (m + 1)) Qq) :
    prPS S hk (jQS S hk g) = g := by
  funext v
  rw [prPS_apply]
  have := jPS_at S (fun v => toFS S hk v (g v)) v
  show (toFS S hk v).symm (bc (fstV I v) (bc (prV (E := E) (I.plc v)) (jPS S (fun v => toFS S hk v (g v)) : GL (Fin N) _))) = g v
  rw [this, MulEquiv.symm_apply_apply]

def HypAtPS (S : StepG I N) : Prop :=
  ∀ (v : Fin nV) (x : GL (Fin N) (E ⊗[F] (I.plc v).adicCompletion F)),
    x ∈ UPts sp.cm.sig S.J ((I.plc v).adicCompletion F) →
    (x ∈ S.Uloc (I.plc v) ↔
      (∀ a b, (((frVS S v)⁻¹ * bc (fstV I v) x * frVS S v : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) a b ∈
        (I.plc v).adicCompletionIntegers F) ∧
      ∀ a b, ((((frVS S v)⁻¹ * bc (fstV I v) x * frVS S v)⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) a b ∈
        (I.plc v).adicCompletionIntegers F)

theorem toFS_symm_stab (S : StepG I N) {m : ℕ} (hk : m + 1 = N) (v : Fin nV)
    (X : GL (Fin N) ((I.plc v).adicCompletion F)) :
    (toFS S hk v).symm X ∈ stabStd (k := m + 1) (Qq := Qq) W ↔
      (∀ a b, (((frVS S v)⁻¹ * X * frVS S v : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) a b ∈
        (I.plc v).adicCompletionIntegers F) ∧
      ∀ a b, ((((frVS S v)⁻¹ * X * frVS S v)⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) a b ∈
        (I.plc v).adicCompletionIntegers F := by
  rw [stabStd_iff, ← map_inv, toFS_symm, toFS_symm]
  have key : ∀ M : GL (Fin N) ((I.plc v).adicCompletion F),
      (∀ a b, ((castGL hk Qq).symm ((bcE (I.eQ v)).symm M) : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) a b ∈
        (algebraMap W Qq).range) ↔ ∀ a b, (M : Matrix (Fin N) (Fin N) _) a b ∈ (I.plc v).adicCompletionIntegers F := by
    intro M
    have h1 : ∀ a b, ((castGL hk Qq).symm ((bcE (I.eQ v)).symm M) : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) a b ∈
        (algebraMap W Qq).range ↔ (M : Matrix (Fin N) (Fin N) _) (Fin.cast hk a) (Fin.cast hk b) ∈
          (I.plc v).adicCompletionIntegers F := by
      intro a b
      rw [castGL_symm_apply, bcE_symm_apply]
      have := I.completion_integers_iff v ((I.eQ v).symm ((M : Matrix (Fin N) (Fin N) _) (Fin.cast hk a) (Fin.cast hk b)))
      rw [RingEquiv.apply_symm_apply] at this
      exact this
    constructor
    · intro h a b
      have := (h1 (Fin.cast hk.symm a) (Fin.cast hk.symm b)).1 (h _ _)
      simpa using this
    · intro h a b
      exact (h1 a b).2 (h _ _)
  have e : (frVS S v)⁻¹ * X⁻¹ * frVS S v = ((frVS S v)⁻¹ * X * frVS S v)⁻¹ := by group
  rw [key, e, key]

def fibPS (S : StepG I N) {m : ℕ} (hk : m + 1 = N) (hH : HypAtPS S) :
    Fib (S.U.subgroupOf (UPts sp.cm.sig S.J (FiniteAdeleRing (𝓞 F) F)))
      ((awayG sp.cm.sig S.J S.Uloc p).subgroupOf (UPts sp.cm.sig S.J (FiniteAdeleRing (𝓞 F) F)))
      (stabTup (nV := nV) (k := m + 1) (Qq := Qq) W) where
  j := jQS S hk
  pr := prPS S hk
  pr_j := prPS_jQS S hk
  j_mem := fun g => Subgroup.mem_subgroupOf.2 (jPS_mem_awayG S _)
  K_iff := by
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, S.U_eq, mem_stabTup, mem_awayG]
    have hloc : ∀ v : Fin nV, bc (prV (E := E) (I.plc v)) (x : GL (Fin N) _) ∈ S.Uloc (I.plc v) ↔
        prPS S hk x v ∈ stabStd (k := m + 1) (Qq := Qq) W := by
      intro v
      rw [prPS_apply, toFS_symm_stab]
      exact hH v _ (Formalism.UG.P.afsplit_bc_mem sp.cm.sig S.J (I.plc v) _ x.2)
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun v _ => h2 v⟩, fun v => (hloc v).1 (h2 _)⟩
    · rintro ⟨⟨h3, h4⟩, h2⟩
      refine ⟨h3, fun v => ?_⟩
      by_cases hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal
      · obtain ⟨v', rfl⟩ : ∃ v', I.plc v' = v := ⟨I.pl.symm ⟨v, hv⟩, by simp [LocId.plc]⟩
        exact (hloc v').2 (h2 v')
      · exact h4 v hv

end Formalism.L2.G
