import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.CastGLSymmApply
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsHypA

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G.Cmp

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

def NotBad (I : LocId L p nV W Qq) : Prop :=
  ∀ v : Fin nV, (gp 0 : 𝓞 F) ∉ (I.plc v).asIdeal ∧ (gp 1 : 𝓞 F) ∉ (I.plc v).asIdeal ∧ (A.T : 𝓞 F) ∉ (I.plc v).asIdeal

abbrev splV (I : LocId L p nV W Qq) (v : Fin nV) :
    E ⊗[F] (I.plc v).adicCompletion F ≃+* (I.plc v).adicCompletion F × (I.plc v).adicCompletion F :=
  I.spl (I.plc v) (I.pl v).2

def IntSplit (I : LocId L p nV W Qq) : Prop :=
  ∀ (v : Fin nV) (t : E ⊗[F] (I.plc v).adicCompletion F), t ∈ intV E (I.plc v) ↔
    (splV I v t).1 ∈ ((I.plc v).adicCompletionIntegers F).toSubring ∧
      (splV I v t).2 ∈ ((I.plc v).adicCompletionIntegers F).toSubring

def SelfDualAtP (I : LocId L p nV W Qq) : Prop :=
  ∀ (v : Fin nV) (y : Fin R.k → E ⊗[F] (I.plc v).adicCompletion F), y ∈ Formalism.L2.Herm.locL (I.plc v) L.Lb ↔
    ∀ z ∈ Formalism.L2.Herm.locL (I.plc v) L.Lb,
      hform (sigR sp.cm.sig ((I.plc v).adicCompletion F))
        (sp.gram0.map (inclE (F := F) ((I.plc v).adicCompletion F))) z y ∈ intV E (I.plc v)

theorem fst_mulVec (I : LocId L p nV W Qq) (v : Fin nV) (x : GL (Fin R.k) (E ⊗[F] (I.plc v).adicCompletion F))
    (y : Fin R.k → E ⊗[F] (I.plc v).adicCompletion F) (a : Fin R.k) :
    (splV I v (((x : Matrix (Fin R.k) (Fin R.k) _) *ᵥ y) a)).1 =
      (((bc (fstV I v) x : GL (Fin R.k) _) : Matrix (Fin R.k) (Fin R.k) _) *ᵥ fun b => (splV I v (y b)).1) a := by
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Prod.fst_sum, Prod.fst_mul]
  rfl

theorem first_iff (I : LocId L p nV W Qq) (v : Fin nV) (x : GL (Fin R.k) (E ⊗[F] (I.plc v).adicCompletion F)) :
    (∀ y ∈ Formalism.L2.Herm.locL (I.plc v) L.Lb, ∃ y' ∈ Formalism.L2.Herm.locL (I.plc v) L.Lb,
      ∀ a, (splV I v (y' a)).1 = (splV I v (((x : Matrix (Fin R.k) (Fin R.k) _) *ᵥ y) a)).1) ↔
      ∀ a b, (((frV I v)⁻¹ * bc (fstV I v) x * frV I v : GL (Fin R.k) _) : Matrix (Fin R.k) (Fin R.k) _) a b ∈
        (I.plc v).adicCompletionIntegers F := by
  have hfr := I.fr_lat (I.plc v) (I.pl v).2
  refine Iff.trans ?_ (int_conj_iff ((I.plc v).adicCompletionIntegers F).toSubring (frV I v) (bc (fstV I v) x))
  constructor
  · intro h t ht
    obtain ⟨y, hy, e⟩ := (hfr t).2 ht
    obtain ⟨y', hy', e'⟩ := h y hy
    refine (hfr _).1 ⟨y', hy', fun a => ?_⟩
    rw [e' a, fst_mulVec]
    congr 2
    funext b
    exact e b
  · intro h y hy
    have h1 := h (fun b => (splV I v (y b)).1) ((hfr _).1 ⟨y, hy, fun _ => rfl⟩)
    obtain ⟨y', hy', e'⟩ := (hfr _).2 h1
    exact ⟨y', hy', fun a => by rw [e' a, fst_mulVec]⟩

theorem isHyperbolicAt_of_integralSplit (I : LocId L p nV W Qq) (hb : NotBad I) (h1 : IntSplit I) (h2 : SelfDualAtP I) : HypAtP I := by
  intro v x hx
  rw [L.Uloc_hyp (I.plc v) (hb v).1 (hb v).2.1 (hb v).2.2]
  have hlev : x ∈ levelVL sp.cm.sig sp.gram0 (I.plc v) L.Lb ↔ x ∈ stabGL (Formalism.L2.Herm.locL (I.plc v) L.Lb) :=
    ⟨fun h => (Subgroup.mem_inf.1 h).2, fun h => Subgroup.mem_inf.2 ⟨hx, h⟩⟩
  have einv : ((frV I v)⁻¹ * bc (fstV I v) x * frV I v)⁻¹ = (frV I v)⁻¹ * bc (fstV I v) x⁻¹ * frV I v := by
    rw [map_inv]; group
  rw [hlev, einv, ← first_iff, ← first_iff]
  constructor
  · intro h
    exact ⟨fun y hy => ⟨_, (h y).1 hy, fun _ => rfl⟩,
      fun y hy => ⟨_, (((stabGL (Formalism.L2.Herm.locL (I.plc v) L.Lb)).inv_mem h) y).1 hy, fun _ => rfl⟩⟩
  · rintro ⟨ha, hb'⟩
    exact stab_of_first (splV I v) (sigR sp.cm.sig ((I.plc v).adicCompletion F)) (I.spl_sig (I.plc v) (I.pl v).2)
      ((I.plc v).adicCompletionIntegers F).toSubring (intV E (I.plc v)) (h1 v) _ _ (h2 v) x hx ha hb'

end Formalism.L2.G.Cmp
