import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasLev

noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct

namespace Formalism.L2.S.S7.ZsCovFin

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

abbrev swp : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E ≃ₐ[F] E ⊗[F] Formalism.MainNotions.S.Af F :=
  Algebra.TensorProduct.comm F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) E

theorem intAf_one : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ∈ intAf F := fun v => by
  show evalV F v 1 ∈ _
  rw [map_one]; exact one_mem _

theorem intAf_mul {a b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F} (ha : a ∈ intAf F) (hb : b ∈ intAf F) : a * b ∈ intAf F := fun v => by
  show evalV F v (a * b) ∈ _
  rw [map_mul]; exact mul_mem (ha v) (hb v)

theorem mul_mem_latHat (L : Set (Fin n → E)) (c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)
    (hc : ∀ a ∈ intAf F, ∀ x ∈ L, (fun i => c * (a ⊗ₜ[F] x i)) ∈ latHat F E L)
    {w : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E} (hw : w ∈ latHat F E L) : (fun i => c * w i) ∈ latHat F E L := by
  induction hw using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    exact hc a ha x hx
  | zero =>
    convert (latHat F E L).zero_mem using 1
    funext i; simp
  | add y z _ _ hy hz =>
    convert (latHat F E L).add_mem hy hz using 1
    funext i; simp [mul_add]
  | neg y _ hy =>
    convert (latHat F E L).neg_mem hy using 1
    funext i; simp [mul_neg]

theorem mem_latHat_iff (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) :
    y ∈ latHat F E (L : Set (Fin n → E)) ↔ (fun i => swp (y i)) ∈ lamAf (F := F) L := by
  constructor
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      have hmem : ((1 : E) ⊗ₜ[F] a) ∈ IntAf F E :=
        Subring.subset_closure (Or.inr ⟨⟨a, fun v => ha v⟩, rfl⟩)
      have hx' : (fun i => Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) (x i)) ∈ lamAf (F := F) L :=
        Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
      have := (lamAf (F := F) L).smul_mem (⟨_, hmem⟩ : IntAf F E) hx'
      convert this using 1
      funext i
      simp [swp, Formalism.UG.inclE, Subring.smul_def, Algebra.TensorProduct.tmul_mul_tmul]
    | zero =>
      convert (lamAf (F := F) L).zero_mem using 1
      funext i; simp
    | add y z _ _ hy hz =>
      convert (lamAf (F := F) L).add_mem hy hz using 1
      funext i; simp
    | neg y _ hy =>
      convert (lamAf (F := F) L).neg_mem hy using 1
      funext i; simp
  · intro hz

    let R : Subring (E ⊗[F] Formalism.MainNotions.S.Af F) :=
      { carrier := {r | ∀ w ∈ latHat F E (L : Set (Fin n → E)), (fun i => swp.symm r * w i) ∈ latHat F E (L : Set (Fin n → E))}
        mul_mem' := fun {r s} hr hs w hw => by
          have := hr _ (hs w hw)
          simpa [map_mul, mul_assoc] using this
        one_mem' := fun w hw => by simpa using hw
        add_mem' := fun {r s} hr hs w hw => by
          convert (latHat F E (L : Set (Fin n → E))).add_mem (hr w hw) (hs w hw) using 1
          funext i; simp [map_add, add_mul]
        zero_mem' := fun w _ => by
          convert (latHat F E (L : Set (Fin n → E))).zero_mem using 1
          funext i; simp
        neg_mem' := fun {r} hr w hw => by
          convert (latHat F E (L : Set (Fin n → E))).neg_mem (hr w hw) using 1
          funext i; simp [map_neg, neg_mul] }
    have hIR : IntAf F E ≤ R := by
      refine (Subring.closure_le).2 ?_
      rintro r (⟨⟨o, ho⟩, rfl⟩ | ⟨⟨a', ha'⟩, rfl⟩)
      · intro w hw
        refine mul_mem_latHat _ _ ?_ hw
        intro a ha x hx
        obtain ⟨o', rfl⟩ := ho
        refine AddSubgroup.subset_closure ⟨a, ha, o' • x, L.smul_mem o' hx, ?_⟩
        funext i
        simp [swp, Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]
      · intro w hw
        refine mul_mem_latHat _ _ ?_ hw
        intro a ha x hx
        refine AddSubgroup.subset_closure ⟨a' * a, intAf_mul (fun v => ha' v) ha, x, hx, ?_⟩
        funext i
        simp [swp, Algebra.TensorProduct.tmul_mul_tmul]
    have key : ∀ z ∈ lamAf (F := F) L, (fun i => swp.symm (z i)) ∈ latHat F E (L : Set (Fin n → E)) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, rfl⟩ := hz
        refine AddSubgroup.subset_closure ⟨1, intAf_one, x, x.2, ?_⟩
        funext i
        simp [swp, Formalism.UG.inclE]
      | zero =>
        convert (latHat F E (L : Set (Fin n → E))).zero_mem using 1
        funext i; simp
      | add z z' _ _ hz hz' =>
        convert (latHat F E (L : Set (Fin n → E))).add_mem hz hz' using 1
        funext i; simp
      | smul r z _ hz =>
        have := hIR r.2 _ hz
        simpa [Subring.smul_def, map_mul] using this
    have := key _ hz
    simpa using this

theorem stab_iff (L : Submodule (𝓞 E) (Fin n → E)) (M : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E))
    (M' : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) (hM : M' = M.map swp) :
    (∀ y, y ∈ latHat F E (L : Set (Fin n → E)) ↔ Matrix.mulVec M y ∈ latHat F E (L : Set (Fin n → E))) ↔
      ∀ z, z ∈ lamAf (F := F) L ↔ Matrix.mulVec M' z ∈ lamAf (F := F) L := by
  subst hM
  have hmv : ∀ y : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E,
      Matrix.mulVec (M.map swp) (fun i => swp (y i)) = fun i => swp ((Matrix.mulVec M y) i) := fun y => by
    funext i
    exact (RingHom.map_mulVec (swp (F := F) (E := E)).toRingEquiv.toRingHom M y i).symm
  constructor
  · intro h z
    obtain ⟨y, rfl⟩ : ∃ y : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E, (fun i => swp (y i)) = z :=
      ⟨fun i => swp.symm (z i), by funext i; simp⟩
    rw [hmv, ← mem_latHat_iff, ← mem_latHat_iff]
    exact h y
  · intro h y
    rw [mem_latHat_iff, mem_latHat_iff, ← hmv]
    exact h _

end Gen

section Brg

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}

theorem hermitianSpaceBaseLattice_eq_frameLattice : L0c D V = ((Formalism.IndefR.Eqv.UI.Lv D V : Submodule _ _) : Set (Fin V.rank → D.host.E)) := by
  ext x
  exact (Formalism.IndefR.Eqv.UI.mem_Lv D V x).symm

theorem finCond_brg (fr : Formalism.IndefR.Eqv.UI.Frames D V) (hΛ : fr.Λ = Formalism.IndefR.Eqv.UI.Lv D V)
    (x : (Formalism.IndefR.Eqv.UI.instV fr).GA) :
    (∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      (finMat D.sp.cm.sig V.gram (Formalism.IndefR.Eqv.UI.brg fr x)).mulVec y ∈ latHat D.host.F D.host.E (L0c D V)) ↔
    x.2 ∈ (Formalism.IndefR.Eqv.UI.instV fr).Kset := by
  have hfin := Formalism.IndefR.Eqv.finE_brg fr x
  have hM : ((x.2.1 : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)).val : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) =
      (finMat D.sp.cm.sig V.gram (Formalism.IndefR.Eqv.UI.brg fr x)).map swp := by
    have := congrArg (fun g : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D) => g.val) hfin
    exact this.symm
  have hL : L0c D V = ((fr.Λ : Submodule _ _) : Set (Fin V.rank → D.host.E)) := by
    rw [hΛ]; exact hermitianSpaceBaseLattice_eq_frameLattice
  rw [hL]
  exact stab_iff fr.Λ _ _ hM

end Brg

end Formalism.L2.S.S7.ZsCovFin
