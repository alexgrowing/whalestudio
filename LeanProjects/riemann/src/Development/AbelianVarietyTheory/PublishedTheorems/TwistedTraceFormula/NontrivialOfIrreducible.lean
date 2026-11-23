import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot

noncomputable section

open GlobalTheory.PRep GlobalTheory.JHMult

namespace GlobalTheory.SmGL

section General

variable {F G V W U : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]

theorem jhMult_congr_left {σ : Representation F G W} {τ : Representation F G U} (φ : σ.Equiv τ)
    (ρ : Representation F G V) : jhMult σ ρ = jhMult τ ρ := by
  have : ∀ r, OccursTimes σ ρ r ↔ OccursTimes τ ρ r := fun r =>
    ⟨fun ⟨S, T, h1, h2, h3⟩ => ⟨S, T, h1, h2, fun i => (h3 i).map (·.trans φ)⟩,
      fun ⟨S, T, h1, h2, h3⟩ => ⟨S, T, h1, h2, fun i => (h3 i).map (·.trans φ.symm)⟩⟩
  simp only [jhMult, this]

theorem jhMult_congr_right (σ : Representation F G W) {ρ : Representation F G V}
    {τ : Representation F G U} (φ : ρ.Equiv τ) : jhMult σ ρ = jhMult σ τ := by
  have key : ∀ {V U : Type} [AddCommGroup V] [Module F V] [AddCommGroup U] [Module F U]
      {ρ : Representation F G V} {τ : Representation F G U} (φ : ρ.Equiv τ) (r : ℕ),
      OccursTimes σ ρ r → OccursTimes σ τ r := fun φ r ⟨S, T, h1, h2, h3⟩ =>
    ⟨fun i => subMap φ.toIntertwiningMap (S i), fun i => subMap φ.toIntertwiningMap (T i),
      fun i => subMap_mono _ (h1 i), fun i j h => subMap_mono _ (h2 i j h),
      fun i => step_iff.2 (step_map _ φ.injective (step_iff.1 (h3 i)))⟩
  have : ∀ r, OccursTimes σ ρ r ↔ OccursTimes σ τ r := fun r => ⟨key φ r, key φ.symm r⟩
  simp only [jhMult, this]

theorem nontrivial_of_irreducible {σ : Representation F G W} (h : σ.IsIrreducible) : Nontrivial W := by
  by_contra hW
  rw [not_nontrivial_iff_subsingleton] at hW
  exact (bot_ne_top : (⊥ : Subrepresentation σ) ≠ ⊤)
    (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem IsSubquotient.nonempty_equiv {σ : Representation F G W} {ρ : Representation F G V}
    (h : IsSubquotient σ ρ) (hσ : σ.IsIrreducible) (hρ : ρ.IsIrreducible) : Nonempty (ρ.Equiv σ) := by
  obtain ⟨S, f, hf⟩ := h
  have := nontrivial_of_irreducible hσ
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hf w
  rcases eq_bot_or_eq_top S with rfl | rfl
  · exact absurd (by rw [show v = 0 from Subtype.ext v.2, map_zero]) hw
  let j : ρ.IntertwiningMap (⊤ : Subrepresentation ρ).toRepresentation :=
    ⟨LinearMap.codRestrict _ LinearMap.id (fun _ => trivial), fun _ => rfl⟩
  have hs : Function.Surjective (f.comp j) := fun w => by
    obtain ⟨u, rfl⟩ := hf w
    exact ⟨u.1, rfl⟩
  have hi : Function.Injective (f.comp j) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    rcases eq_bot_or_eq_top (f.comp j).ker with h | h
    · have : x ∈ (f.comp j).ker := hx
      rw [h] at this
      exact this
    · have : v.1 ∈ (f.comp j).ker := by rw [h]; trivial
      exact absurd this hw
  exact ⟨.mk (LinearEquiv.ofBijective (f.comp j).toLinearMap ⟨hi, hs⟩) (f.comp j).isIntertwining'⟩

theorem jhMult_self {σ : Representation F G W} (hσ : σ.IsIrreducible) : jhMult σ σ = 1 := by
  refine le_antisymm (iSup₂_le ?_) (Order.one_le_iff_ne_zero.2
    (jhMult_ne_zero_iff.2 (IsSubquotient.refl σ)))
  rintro r ⟨S, T, -, h2, h3⟩
  rcases r with _ | _ | r
  · simp
  · simp
  exfalso
  have h0 := (step_iff.1 (h3 0)).not_le hσ
  have h1 := (step_iff.1 (h3 1)).not_le hσ
  rcases eq_bot_or_eq_top (S 0) with h | h
  · exact h0 (h ▸ bot_le)
  · exact h1 (le_top.trans (h ▸ h2 0 1 Fin.zero_lt_one))

theorem isIrreducible_subQuot {ρ : Representation F G V} {S T : Subrepresentation ρ} (h : T ⋖ S) :
    (subQuot S T).IsIrreducible := by
  let ι : S.toRepresentation.IntertwiningMap ρ := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hp : ∀ v, p v = 0 ↔ v.1 ∈ T.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
  have : Nontrivial (Subrepresentation (subQuot S T)) := ⟨⊥, ⊤, fun h' => h.lt.not_ge fun v hv => by
    have : p ⟨v, hv⟩ ∈ (⊥ : Subrepresentation (subQuot S T)).toSubmodule := by rw [h']; trivial
    exact (hp _).1 this⟩
  refine ⟨fun R => ?_⟩
  have h1 : T ≤ subMap ι (subComap p R) := fun v hv =>
    ⟨⟨v, h.le hv⟩, by
      show p _ ∈ R.toSubmodule
      rw [(hp _).2 hv]; exact zero_mem _, rfl⟩
  have h2 : subMap ι (subComap p R) ≤ S := by
    rintro _ ⟨v, -, rfl⟩
    exact v.2
  rcases h.eq_or_eq h1 h2 with h3 | h3
  · left
    refine le_antisymm (fun x hx => ?_) bot_le
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have : v.1 ∈ (subMap ι (subComap p R)).toSubmodule := ⟨v, hx, rfl⟩
    rw [h3] at this
    exact (hp v).2 this
  · right
    refine le_antisymm le_top (fun x _ => ?_)
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have : v.1 ∈ (subMap ι (subComap p R)).toSubmodule := by rw [h3]; exact v.2
    obtain ⟨u, hu, huv⟩ := this
    obtain rfl : u = v := Subtype.ext huv
    exact hu

theorem jhMult_of_le {σ : Representation F G W} (hσ : σ.IsIrreducible) {ρ : Representation F G V}
    {S T : Subrepresentation ρ} (h : T ≤ S) :
    jhMult σ S.toRepresentation = jhMult σ T.toRepresentation + jhMult σ (subQuot S T) := by
  let ι : T.toRepresentation.IntertwiningMap S.toRepresentation :=
    ⟨Submodule.inclusion h, fun _ => rfl⟩
  let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hp : ∀ v, p v = 0 ↔ v.1 ∈ T.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
  exact jhMult_exact ι p hσ (Submodule.inclusion_injective h) (Submodule.Quotient.mk_surjective _)
    (fun u => (hp _).2 u.2) fun v hv => ⟨⟨v.1, (hp v).1 hv⟩, rfl⟩

def topEquiv (ρ : Representation F G V) : (⊤ : Subrepresentation ρ).toRepresentation.Equiv ρ :=
  .mk Submodule.topEquiv fun _ => rfl

theorem jhMult_of_subsingleton [Subsingleton V] {σ : Representation F G W} (hσ : σ.IsIrreducible)
    (ρ : Representation F G V) : jhMult σ ρ = 0 := by
  by_contra h
  obtain ⟨S, f, hf⟩ := jhMult_ne_zero_iff.1 h
  have := nontrivial_of_irreducible hσ
  exact not_subsingleton W hf.subsingleton

theorem jhMult_filtration {σ : Representation F G W} (hσ : σ.IsIrreducible) {ρ : Representation F G V}
    {N : ℕ} (S : Fin (N + 1) → Subrepresentation ρ) (hS : Monotone S) (h0 : S 0 = ⊥)
    (h1 : S (Fin.last N) = ⊤) :
    jhMult σ ρ = ∑ t : Fin N, jhMult σ (subQuot (S t.succ) (S t.castSucc)) := by
  have key : ∀ (N : ℕ) (S : Fin (N + 1) → Subrepresentation ρ), Monotone S → S 0 = ⊥ →
      jhMult σ (S (Fin.last N)).toRepresentation =
        ∑ t : Fin N, jhMult σ (subQuot (S t.succ) (S t.castSucc)) := by
    intro N
    induction N with
    | zero =>
      intro S _ h0
      rw [show Fin.last 0 = 0 from rfl, h0, Finset.univ_eq_empty, Finset.sum_empty]
      have : Subsingleton (⊥ : Subrepresentation ρ).toSubmodule :=
        inferInstanceAs (Subsingleton (⊥ : Submodule F V))
      exact jhMult_of_subsingleton hσ _
    | succ N ih =>
      intro S hS h0
      rw [Fin.sum_univ_castSucc, jhMult_of_le hσ (hS (Fin.le_last (Fin.last N).castSucc)),
        ih (fun t => S t.castSucc) (fun a b h => hS h) h0]
      rfl
  rw [← key N S hS h0, h1]
  exact (jhMult_congr_right σ (topEquiv ρ)).symm

theorem HasFiniteLength.of_equiv {ρ : Representation F G V} {τ : Representation F G U}
    (h : HasFiniteLength ρ) (φ : ρ.Equiv τ) : HasFiniteLength τ :=
  IsFiniteLength.of_surjective h
    (f := Representation.IntertwiningMap.equivLinearMapAsModule ρ τ φ.toIntertwiningMap) φ.surjective

end General

section Groth

variable (G : Type) [Group G] [TopologicalSpace G]

structure IrrRep : Type 1 where

  V : Type
  [acg : AddCommGroup V]
  [mod : Module ℂ V]

  ρ : Representation ℂ G V
  smooth : IsSmooth ρ
  irr : ρ.IsIrreducible

attribute [instance] IrrRep.acg IrrRep.mod

def IrrRep.ofChar {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (χ : G →* ℂˣ)
    (h : IsSmoothChar χ) : IrrRep G :=
  ⟨ℂ, SmGL.ofChar χ, (isSmooth_ofChar_iff χ).2 h, isIrreducible_ofChar χ⟩

instance IrrRep.setoid : Setoid (IrrRep G) where
  r σ τ := Nonempty (σ.ρ.Equiv τ.ρ)
  iseqv := ⟨fun _ => ⟨.refl _⟩, fun ⟨φ⟩ => ⟨φ.symm⟩, fun ⟨φ⟩ ⟨ψ⟩ => ⟨φ.trans ψ⟩⟩

def IrrCl : Type 1 := Quotient (IrrRep.setoid G)

abbrev Groth : Type 1 := IrrCl G →₀ ℤ

variable {G} {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

def IrrRep.cl (σ : IrrRep G) : IrrCl G := Quotient.mk _ σ

theorem IrrRep.cl_eq_iff {σ τ : IrrRep G} : σ.cl = τ.cl ↔ Nonempty (σ.ρ.Equiv τ.ρ) := Quotient.eq

def IrrCl.rep (c : IrrCl G) : IrrRep G := Quotient.out c

@[simp] theorem IrrCl.cl_rep (c : IrrCl G) : c.rep.cl = c := Quotient.out_eq c

theorem IrrRep.nonempty_equiv_rep (σ : IrrRep G) : Nonempty (σ.cl.rep.ρ.Equiv σ.ρ) :=
  IrrRep.cl_eq_iff.1 (IrrCl.cl_rep _)

theorem IrrRep.cl_ofChar_inj [IsTopologicalGroup G] {χ ψ : G →* ℂˣ} (hχ : IsSmoothChar χ)
    (hψ : IsSmoothChar ψ) : (IrrRep.ofChar χ hχ).cl = (IrrRep.ofChar ψ hψ).cl ↔ χ = ψ := by
  refine ⟨fun h => ?_, by rintro rfl; rfl⟩
  by_contra hne
  obtain ⟨φ⟩ := IrrRep.cl_eq_iff.1 h
  have h1 := Model.jhMult_ofChar_ne hne
  have h2 : jhMult (SmGL.ofChar χ) (SmGL.ofChar ψ) = jhMult (SmGL.ofChar ψ) (SmGL.ofChar ψ) :=
    jhMult_congr_left φ _
  rw [h2, jhMult_self (isIrreducible_ofChar ψ)] at h1
  exact one_ne_zero h1

theorem finite_constituents {π : Representation ℂ G V} (h : HasFiniteLength π) :
    {c : IrrCl G | jhMult c.rep.ρ π ≠ 0}.Finite := by
  have φ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := π)
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 h
  have : WellFoundedGT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedGT
  have : WellFoundedLT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedLT
  have key : ∀ S : Subrepresentation π,
      {c : IrrCl G | jhMult c.rep.ρ S.toRepresentation ≠ 0}.Finite := by
    intro S
    induction S using WellFoundedLT.induction with
    | ind S ih =>
    rcases eq_or_ne S ⊥ with rfl | hS
    · have : Subsingleton (⊥ : Subrepresentation π).toSubmodule :=
        inferInstanceAs (Subsingleton (⊥ : Submodule ℂ V))
      simp [jhMult_of_subsingleton (IrrRep.irr _)]
    obtain ⟨T, -, hT⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.2 hS)
    have h2 : {c : IrrCl G | jhMult c.rep.ρ (subQuot S T) ≠ 0}.Subsingleton := fun c hc d hd => by
      obtain ⟨a⟩ := (jhMult_ne_zero_iff.1 hc).nonempty_equiv c.rep.irr (isIrreducible_subQuot hT)
      obtain ⟨b⟩ := (jhMult_ne_zero_iff.1 hd).nonempty_equiv d.rep.irr (isIrreducible_subQuot hT)
      rw [← c.cl_rep, ← d.cl_rep]
      exact IrrRep.cl_eq_iff.2 ⟨a.symm.trans b⟩
    refine ((ih T hT.lt).union h2.finite).subset fun c hc => ?_
    by_contra hn
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hn
    exact hc (by rw [jhMult_of_le c.rep.irr hT.le, hn.1, hn.2, add_zero])
  simpa only [jhMult_congr_right _ (topEquiv π)] using key ⊤

def cls (π : Representation ℂ G V) (h : HasFiniteLength π) : Groth G :=
  Finsupp.ofSupportFinite (fun c => ((jhMult c.rep.ρ π).toNat : ℤ))
    ((finite_constituents h).subset fun c hc h0 => hc (by simp [h0]))

theorem cls_apply (π : Representation ℂ G V) (h : HasFiniteLength π) (c : IrrCl G) :
    cls π h c = ((jhMult c.rep.ρ π).toNat : ℤ) := rfl

theorem cls_apply_cl (π : Representation ℂ G V) (h : HasFiniteLength π) (σ : IrrRep G) :
    ∃ r : ℕ, jhMult σ.ρ π = r ∧ cls π h σ.cl = r := by
  obtain ⟨φ⟩ := σ.nonempty_equiv_rep
  exact ⟨_, (ENat.coe_toNat (jhMult_ne_top σ.irr h)).symm, by rw [cls_apply, jhMult_congr_left φ]⟩

theorem cls_congr {π : Representation ℂ G V} {τ : Representation ℂ G W} (φ : π.Equiv τ)
    (h : HasFiniteLength π) (h' : HasFiniteLength τ) : cls π h = cls τ h' := by
  ext c
  rw [cls_apply, cls_apply, jhMult_congr_right _ φ]

theorem cls_exact {π : Representation ℂ G V} {π₁ : Representation ℂ G W} {π₂ : Representation ℂ G U}
    (ι : π₁.IntertwiningMap π) (p : π.IntertwiningMap π₂) (hι : Function.Injective ι)
    (hp : Function.Surjective p) (he : Function.Exact ι p) (h : HasFiniteLength π)
    (h₁ : HasFiniteLength π₁) (h₂ : HasFiniteLength π₂) : cls π h = cls π₁ h₁ + cls π₂ h₂ := by
  ext c
  rw [Finsupp.add_apply, cls_apply, cls_apply, cls_apply,
    jhMult_exact ι p c.rep.irr hι hp he.apply_apply_eq_zero (fun v hv => (he v).1 hv),
    ENat.toNat_add (jhMult_ne_top c.rep.irr h₁) (jhMult_ne_top c.rep.irr h₂), Nat.cast_add]

theorem cls_irr (σ : IrrRep G) (h : HasFiniteLength σ.ρ) : cls σ.ρ h = Finsupp.single σ.cl 1 := by
  ext c
  rw [cls_apply]
  rcases eq_or_ne c σ.cl with rfl | hc
  · obtain ⟨φ⟩ := σ.nonempty_equiv_rep
    rw [jhMult_congr_left φ, jhMult_self σ.irr, Finsupp.single_eq_same]
    rfl
  · rw [Finsupp.single_eq_of_ne hc]
    have : jhMult c.rep.ρ σ.ρ = 0 := by
      by_contra h0
      obtain ⟨φ⟩ := (jhMult_ne_zero_iff.1 h0).nonempty_equiv c.rep.irr σ.irr
      exact hc (c.cl_rep.symm.trans (IrrRep.cl_eq_iff.2 ⟨φ.symm⟩))
    simp [this]

theorem IrrRep.hasFiniteLength (σ : IrrRep G) : HasFiniteLength σ.ρ := by
  have φ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := σ.ρ)
  haveI : IsSimpleOrder (Subrepresentation σ.ρ) := σ.irr
  haveI : Finite (Subrepresentation σ.ρ) := IsSimpleOrder.instFinite
  haveI : Finite (Submodule (MonoidAlgebra ℂ G) σ.ρ.asModule) := Finite.of_equiv _ φ.toEquiv
  exact isFiniteLength_iff_isNoetherian_isArtinian.2
    ⟨isNoetherian_iff'.2 Finite.to_wellFoundedGT, Finite.to_wellFoundedLT⟩

end Groth

end GlobalTheory.SmGL
