import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMemIwC
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.AlgebraTools

section Ring

variable {R n : Type} [CommRing R] [Fintype n] [DecidableEq n] [LinearOrder n]

private theorem q_diag_mul {a b : GL n R} (ha : a ∈ borel R n) (hb : b ∈ borel R n) (i : n) :
    ((a * b : GL n R) : Matrix n n R) i i = (a : Matrix n n R) i i * (b : Matrix n n R) i i := by
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i]
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with h | h
    · rw [(mem_borel R).1 ha i l h, zero_mul]
    · rw [(mem_borel R).1 hb l i h, mul_zero]
  · simp

private theorem q_exD : ∃ D : borel R n →* (n → Rˣ),
    ∀ (g : borel R n) (i : n), (D g i : R) = ((g : GL n R) : Matrix n n R) i i := by
  let D0 : n → (borel R n →* R) := fun i =>
    { toFun := fun g => ((g : GL n R) : Matrix n n R) i i
      map_one' := by simp
      map_mul' := fun a b => q_diag_mul a.2 b.2 i }
  exact ⟨MonoidHom.pi fun i => (D0 i).toHomUnits, fun g i => rfl⟩

private theorem q_map_diagT {S : Type} [CommRing S] (f : R →+* S) (d : n → Rˣ) :
    GeneralLinearGroup.map (n := n) f (diagT R n d) = diagT S n fun i => Units.map f.toMonoidHom (d i) := by
  ext i j
  show f ((diagT R n d : Matrix n n R) i j) = _
  rw [val_diagT, val_diagT, diagonal_apply, diagonal_apply]
  split_ifs
  · rfl
  · simp

end Ring

section Loc

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)

private theorem q_exF : ∃ F : iwC k n ⊤ →* (Fin n → 𝓀[k]ˣ), ∀ (h : GL (Fin n) 𝒪[k])
    (hh : GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k) h ∈ iwC k n ⊤) (i : Fin n),
    (F ⟨_, hh⟩ i : 𝓀[k]) = IsLocalRing.residue 𝒪[k] ((h : Matrix (Fin n) (Fin n) 𝒪[k]) i i) := by
  have hinj : Function.Injective (algebraMap 𝒪[k] k) := Subtype.val_injective
  have hinj2 : Function.Injective (GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k)) := by
    intro a b hab
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact hinj (congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j) hab)
  obtain ⟨D, hD⟩ := q_exD (R := 𝓀[k]) (n := Fin n)
  let r := GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue 𝒪[k])
  let H := (borel 𝓀[k] (Fin n)).comap r
  have hle : iwC k n ⊤ ≤ H.map (GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k)) :=
    le_of_eq (memIwC k n ⊤).2.1
  let e := H.equivMapOfInjective _ hinj2
  refine ⟨D.comp ((r.subgroupComap _).comp (e.symm.toMonoidHom.comp (Subgroup.inclusion hle))), fun h hh i => ?_⟩
  have hH : h ∈ H := by
    obtain ⟨h', h1, h2⟩ := hle hh
    rwa [← hinj2 h2]
  have : e.symm (Subgroup.inclusion hle ⟨_, hh⟩) = ⟨h, hH⟩ := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  show (D (r.subgroupComap _ (e.symm (Subgroup.inclusion hle ⟨_, hh⟩))) i : 𝓀[k]) = _
  rw [this, hD]
  rfl

end Loc

end UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.iwQuot :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ), ∃ f : iwC k n ⊤ →* (Fin n → 𝓀[k]ˣ ⧸ C), Function.Surjective f ∧ (∀ g : iwC k n ⊤, f g = 1 ↔ (g : GL (Fin n) k) ∈ iwC k n C) ∧ ∀ (u : Fin n → 𝒪[k]ˣ) (h : diagT k (Fin n) (fun i => Units.map (algebraMap 𝒪[k] k).toMonoidHom (u i)) ∈ iwC k n ⊤) (i : Fin n), f ⟨_, h⟩ i = ((Units.map (IsLocalRing.residue 𝒪[k]).toMonoidHom (u i) : 𝓀[k]ˣ) : 𝓀[k]ˣ ⧸ C) := by
  intro k _ _ _ _ n C
  have hinj : Function.Injective (algebraMap 𝒪[k] k) := Subtype.val_injective
  obtain ⟨F, hF⟩ := q_exF k n
  let f : iwC k n ⊤ →* (Fin n → 𝓀[k]ˣ ⧸ C) :=
    MonoidHom.pi fun i => (QuotientGroup.mk' C).comp ((Pi.evalMonoidHom _ i).comp F)
  have hf : ∀ g i, f g i = ((F g i : 𝓀[k]ˣ) : 𝓀[k]ˣ ⧸ C) := fun _ _ => rfl
  have h3 : ∀ (u : Fin n → 𝒪[k]ˣ) (h : diagT k (Fin n) (fun i => Units.map (algebraMap 𝒪[k] k).toMonoidHom (u i)) ∈ iwC k n ⊤) (i : Fin n), f ⟨_, h⟩ i = ((Units.map (IsLocalRing.residue 𝒪[k]).toMonoidHom (u i) : 𝓀[k]ˣ) : 𝓀[k]ˣ ⧸ C) := by
    intro u h i
    have e := q_map_diagT (algebraMap 𝒪[k] k) u
    have h' : GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k) (diagT _ _ u) ∈ iwC k n ⊤ := e ▸ h
    have e2 : (⟨_, h⟩ : iwC k n ⊤) = ⟨_, h'⟩ := Subtype.ext e.symm
    rw [hf, e2]
    congr 1
    apply Units.ext
    rw [hF, val_diagT, diagonal_apply_eq]
    rfl
  refine ⟨f, fun y => ?_, fun g => ?_, h3⟩
  · have h1 : ∀ i, ∃ u : 𝒪[k]ˣ,
        ((Units.map (IsLocalRing.residue 𝒪[k]).toMonoidHom u : 𝓀[k]ˣ) : 𝓀[k]ˣ ⧸ C) = y i := by
      intro i
      obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (y i)
      obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective (R := 𝒪[k]) (c : 𝓀[k])
      have hu : IsUnit x := by
        rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hx]
        exact c.ne_zero
      obtain ⟨u, rfl⟩ := hu
      refine ⟨u, ?_⟩
      rw [← hc]
      congr 1
      exact Units.ext hx
    choose u hu using h1
    have h : diagT k (Fin n) (fun i => Units.map (algebraMap 𝒪[k] k).toMonoidHom (u i)) ∈ iwC k n ⊤ :=
      Subgroup.mem_sup_right ⟨_, fun i _ => ⟨u i, trivial, rfl⟩, rfl⟩
    exact ⟨⟨_, h⟩, funext fun i => (h3 u h i).trans (hu i)⟩
  · obtain ⟨g, hg⟩ := g
    have hg' : g ∈ iwahori k (Fin n) := (memIwC k n C).2.1 ▸ hg
    obtain ⟨h, hh, rfl⟩ := id hg'
    rw [(memIwC k n C).1, and_iff_right hg', funext_iff]
    refine forall_congr' fun i => ?_
    rw [hf, Pi.one_apply, QuotientGroup.eq_one_iff]
    have e := hF h hg i
    constructor
    · intro hc
      have hu : IsUnit ((h : Matrix (Fin n) (Fin n) 𝒪[k]) i i) := by
        rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← e]
        exact Units.ne_zero _
      obtain ⟨d, hd⟩ := hu
      refine ⟨_, ⟨d, ?_, rfl⟩, congrArg (algebraMap 𝒪[k] k) hd⟩
      rw [← hd] at e
      have : Units.map (IsLocalRing.residue 𝒪[k]).toMonoidHom d = F ⟨_, hg⟩ i := Units.ext e.symm
      show Units.map (IsLocalRing.residue 𝒪[k]).toMonoidHom d ∈ C
      rw [this]
      exact hc
    · rintro ⟨_, ⟨d, hd, rfl⟩, e1⟩
      have e' : (d : 𝒪[k]) = (h : Matrix (Fin n) (Fin n) 𝒪[k]) i i := hinj e1
      rw [← e'] at e
      have : Units.map (IsLocalRing.residue 𝒪[k]).toMonoidHom d = F ⟨_, hg⟩ i := Units.ext e.symm
      rw [← this]
      exact hd
