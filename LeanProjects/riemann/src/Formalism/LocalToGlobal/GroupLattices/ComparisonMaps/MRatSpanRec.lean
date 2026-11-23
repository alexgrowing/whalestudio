import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.YvRatOfValRat

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.BasicNotions

section Pl

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) (α : Type) {LL : Type} [Field LL] (e : LL →+* Kf) (Mi : Submodule O (FnP P α))

abbrev modLL : Module LL (FnP P α) := Module.compHom _ e

theorem isRational_add {F F' : FnP P α} (h : RatFnP P α e F) (h' : RatFnP P α e F') : RatFnP P α e (F + F') := by
  intro i L
  obtain ⟨Q, hQ⟩ := h i L
  obtain ⟨Q', hQ'⟩ := h' i L
  exact ⟨Q + Q', by rw [map_add, hQ, hQ']; rfl⟩

theorem isRational_smul (a : LL) {F : FnP P α} (h : RatFnP P α e F) : RatFnP P α e (e a • F) := by
  intro i L
  obtain ⟨Q, hQ⟩ := h i L
  refine ⟨MvPolynomial.C a * Q, ?_⟩
  rw [map_mul, MvPolynomial.map_C, hQ, ← MvPolynomial.smul_eq_C_mul]
  rfl

def formsLL : @Submodule LL (FnP P α) _ _ (modLL P α e) :=
  letI := modLL P α e
  { carrier := {F | F ∈ Submodule.span Kf (Mi : Set (FnP P α)) ∧ RatFnP P α e F}
    add_mem' := fun h h' => ⟨Submodule.add_mem _ h.1 h'.1, isRational_add P α e h.2 h'.2⟩
    zero_mem' := ⟨Submodule.zero_mem _, fun _ _ => ⟨0, map_zero _⟩⟩
    smul_mem' := fun a _ h => ⟨Submodule.smul_mem _ (e a) h.1, isRational_smul P α e a h.2⟩ }

abbrev FormsLL : Type := ↥(formsLL P α e Mi)

instance : Module LL (FormsLL P α e Mi) :=
  letI := modLL P α e
  Submodule.module _

def cmpF : FormsLL P α e Mi →+ FnP P α :=
  letI := modLL P α e
  (formsLL P α e Mi).subtype.toAddMonoidHom

theorem cmpF_apply (x : FormsLL P α e Mi) : cmpF P α e Mi x = x.1 := rfl

theorem cmpF_rat (x : FormsLL P α e Mi) : RatFnP P α e (cmpF P α e Mi x) := by rw [cmpF_apply]; exact x.2.2

def intLL : Set (FormsLL P α e Mi) := {x | cmpF P α e Mi x ∈ Mi}

def MRatSpan : Prop := Submodule.span O (cmpF P α e Mi '' intLL P α e Mi) = Mi

end Pl

section Rec

variable {D : D7} (c : LatCmp D)

abbrev FormsRec u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : Type :=
  FormsLL (D.gat u w hg).P (D.gat u w hg).comp (c.embW u w hg) (D.gat u w hg).M

def equivRec (h : ValRat c) u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    ((D.fm u).lat 0).V ≃ₗ[D.what₂.LL] FormsRec c u w hg :=
  LinearEquiv.ofBijective
    { toFun := fun x => ⟨c.cmp u w hg x, cmp_mem_span c u w hg x, h.all c u w hg x⟩
      map_add' := fun x y => Subtype.ext (map_add (c.cmp u w hg) x y)
      map_smul' := fun a x => Subtype.ext (c.cmp_smul u w hg a x) }
    ⟨fun x y hxy => cmp_inj c u w hg (congrArg Subtype.val hxy), fun F => by
      obtain ⟨x, hx⟩ := (range_cmp c h u w hg F.1).2 F.2
      exact ⟨x, Subtype.ext hx⟩⟩

theorem mRatSpan_rec (h : ValRat c) u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    MRatSpan (D.gat u w hg).P (D.gat u w hg).comp (c.embW u w hg) (D.gat u w hg).M := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  · refine (c.cmp_M u w hg).symm.le.trans ?_
    apply Submodule.span_mono
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨equivRec c h u w hg x, ?_, rfl⟩
    show c.cmp u w hg x ∈ (D.gat u w hg).M
    rw [← c.cmp_M u w hg]
    exact Submodule.subset_span ⟨x, hx, rfl⟩

end Rec

end Formalism.L2.G.Cmp
