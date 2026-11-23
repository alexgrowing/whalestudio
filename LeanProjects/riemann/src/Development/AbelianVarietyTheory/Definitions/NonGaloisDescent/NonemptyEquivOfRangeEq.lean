import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory.Parabolic (Embeds isIrreducible_of_equiv mem_fixed)

namespace GlobalTheory.LocGL

section General

variable {G H M V W X : Type} [Group G] [Group H] [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X]

def descend (ρ : Representation ℂ G V) (q : G →* M) (hq : Function.Surjective q) (h : ∀ g, q g = 1 → ρ g = 1) :
    Representation ℂ M V :=
  (Units.coeHom _).comp (q.liftOfSurjective hq ⟨ρ.toHomUnits, fun g hg => Units.ext (h g hg)⟩)

@[simp] theorem descend_apply (ρ : Representation ℂ G V) (q : G →* M) (hq : Function.Surjective q)
    (h : ∀ g, q g = 1 → ρ g = 1) (g : G) : descend ρ q hq h (q g) = ρ g := by
  simp [descend]

def equivOfBijective {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.IntertwiningMap σ)
    (hf : Function.Bijective f) : ρ.Equiv σ :=
  .mk (LinearEquiv.ofBijective f.toLinearMap hf) f.isIntertwining'

def twistEquiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) (χ : G →* ℂˣ) :
    (twist ρ χ).Equiv (twist σ χ) :=
  equivOfBijective (twistMap e.toIntertwiningMap χ) e.toLinearEquiv.bijective

def compEquiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) (s : H →* G) :
    Representation.Equiv (ρ.comp s) (σ.comp s) :=
  equivOfBijective (compMap e.toIntertwiningMap s) e.toLinearEquiv.bijective

def piTensorEquiv {α : Type} {Γ Y Z : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    [∀ a, AddCommGroup (Z a)] [∀ a, Module ℂ (Z a)] {ρ : ∀ a, Representation ℂ (Γ a) (Y a)}
    {σ : ∀ a, Representation ℂ (Γ a) (Z a)} (e : ∀ a, (ρ a).Equiv (σ a)) : (piTensor ρ).Equiv (piTensor σ) :=
  .mk (PiTensorProduct.congr fun a => (e a).toLinearEquiv) fun g => by
    ext x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, piTensor_tprod, LinearEquiv.coe_coe,
      PiTensorProduct.congr_tprod]
    congr 1
    funext a
    exact (e a).toIntertwiningMap.isIntertwining _ _ _ _

def subrepIso {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) :
    Subrepresentation ρ ≃o Subrepresentation σ where
  toFun S := ⟨S.toSubmodule.comap e.symm.toLinearMap, fun g v hv => by
    show e.symm.toIntertwiningMap (σ g v) ∈ S.toSubmodule
    rw [e.symm.toIntertwiningMap.isIntertwining]
    exact S.apply_mem_toSubmodule g hv⟩
  invFun S := ⟨S.toSubmodule.comap e.toLinearMap, fun g v hv => by
    show e.toIntertwiningMap (ρ g v) ∈ S.toSubmodule
    rw [e.toIntertwiningMap.isIntertwining]
    exact S.apply_mem_toSubmodule g hv⟩
  left_inv S := by
    ext v
    show e.symm (e v) ∈ S.toSubmodule ↔ _
    simp
  right_inv S := by
    ext v
    show e (e.symm v) ∈ S.toSubmodule ↔ _
    simp
  map_rel_iff' := by
    intro S T
    refine ⟨fun h v hv => ?_, fun h v hv => h hv⟩
    have h1 : e.symm (e v) ∈ S.toSubmodule := by rw [e.symm_apply_apply]; exact hv
    have h2 : e.symm (e v) ∈ T.toSubmodule := h h1
    rwa [e.symm_apply_apply] at h2

theorem mem_subrepIso {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) (S : Subrepresentation ρ)
    (w : W) : w ∈ subrepIso e S ↔ e.symm w ∈ S := Iff.rfl

def subrepTwist (ρ : Representation ℂ G V) (χ : G →* ℂˣ) : Subrepresentation (twist ρ χ) ≃o Subrepresentation ρ where
  toFun S := ⟨S.toSubmodule, fun g v hv => by
    have := S.toSubmodule.smul_mem (((χ g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
    simpa [smul_smul] using this⟩
  invFun S := ⟨S.toSubmodule, fun g v hv => S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_twist {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) (χ : G →* ℂˣ) :
    (twist ρ χ).IsIrreducible := (subrepTwist ρ χ).isSimpleOrder_iff.2 h

def IsSocle (σ : Representation ℂ G W) (π : Representation ℂ G V) : Prop :=
  σ.IsIrreducible ∧ ∃ f : σ.IntertwiningMap π, Function.Injective f ∧
    ∀ S : Subrepresentation π, IsAtom S → S = f.range

def IsCosocle (σ : Representation ℂ G W) (π : Representation ℂ G V) : Prop :=
  σ.IsIrreducible ∧ ∃ f : π.IntertwiningMap σ, Function.Surjective f ∧
    ∀ S : Subrepresentation π, IsCoatom S → S = f.ker

theorem IsSocle.embeds {σ : Representation ℂ G W} {π : Representation ℂ G V} (h : IsSocle σ π) : Embeds σ π :=
  let ⟨_, f, hf, _⟩ := h; ⟨f, hf⟩

theorem IsSocle.isSubquotient {σ : Representation ℂ G W} {π : Representation ℂ G V} (h : IsSocle σ π) :
    IsSubquotient σ π :=
  let ⟨_, f, hf, _⟩ := h; .of_injective f hf

theorem IsCosocle.isSubquotient {σ : Representation ℂ G W} {π : Representation ℂ G V} (h : IsCosocle σ π) :
    IsSubquotient σ π :=
  let ⟨_, f, hf, _⟩ := h; .of_surjective f hf

theorem IsSocle.of_equiv {σ : Representation ℂ G W} {π : Representation ℂ G V} {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    {σ' : Representation ℂ G X} {π' : Representation ℂ G Y} (h : IsSocle σ π) (a : σ.Equiv σ') (b : π.Equiv π') :
    IsSocle σ' π' := by
  obtain ⟨hi, f, hf, hS⟩ := h
  refine ⟨isIrreducible_of_equiv a hi, b.toIntertwiningMap.comp (f.comp a.symm.toIntertwiningMap),
    b.toLinearEquiv.injective.comp (hf.comp a.symm.toLinearEquiv.injective), fun S h => ?_⟩
  obtain ⟨S, rfl⟩ := (subrepIso b).surjective S
  rw [hS S ((OrderIso.isAtom_iff _ _).1 h)]
  refine SetLike.ext fun y => ⟨?_, ?_⟩
  · rintro ⟨w, hw⟩
    refine ⟨a w, ?_⟩
    show b (f (a.symm (a w))) = y
    have hw' : f w = b.symm y := hw
    simp [hw']
  · rintro ⟨x, rfl⟩
    refine ⟨a.symm x, ?_⟩
    show f (a.symm x) = b.symm (b (f (a.symm x)))
    simp

theorem IsCosocle.of_equiv {σ : Representation ℂ G W} {π : Representation ℂ G V} {Y : Type} [AddCommGroup Y]
    [Module ℂ Y] {σ' : Representation ℂ G X} {π' : Representation ℂ G Y} (h : IsCosocle σ π) (a : σ.Equiv σ')
    (b : π.Equiv π') : IsCosocle σ' π' := by
  obtain ⟨hi, f, hf, hS⟩ := h
  refine ⟨isIrreducible_of_equiv a hi, a.toIntertwiningMap.comp (f.comp b.symm.toIntertwiningMap),
    a.toLinearEquiv.surjective.comp (hf.comp b.symm.toLinearEquiv.surjective), fun S h => ?_⟩
  obtain ⟨S, rfl⟩ := (subrepIso b).surjective S
  rw [hS S ((OrderIso.isCoatom_iff _ _).1 h)]
  refine SetLike.ext fun y => ?_
  show f (b.symm y) = 0 ↔ a (f (b.symm y)) = 0
  simp

theorem isSocle_self {π : Representation ℂ G V} (h : π.IsIrreducible) : IsSocle π π :=
  ⟨h, .id π, fun _ _ e => e, fun S hS => by
    rw [(eq_bot_or_eq_top S).resolve_left hS.1]
    exact SetLike.ext fun v => ⟨fun _ => (Representation.IntertwiningMap.mem_range _ _ _ _).2 ⟨v, rfl⟩, fun _ => trivial⟩⟩

theorem isCosocle_self {π : Representation ℂ G V} (h : π.IsIrreducible) : IsCosocle π π :=
  ⟨h, .id π, fun v => ⟨v, rfl⟩, fun S hS => by
    rw [(eq_bot_or_eq_top S).resolve_right hS.1]
    exact SetLike.ext fun v => Iff.rfl⟩

theorem isAtom_range {σ : Representation ℂ G W} {π : Representation ℂ G V} (h : σ.IsIrreducible)
    (f : σ.IntertwiningMap π) (hf : Function.Injective f) : IsAtom f.range := by
  have := Model.nontrivial_of_isIrreducible h
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  refine ⟨fun e => hw (hf ?_), fun S hS => ?_⟩
  · have : f w ∈ (⊥ : Subrepresentation π) := e ▸ ⟨w, rfl⟩
    rw [map_zero]; exact this
  · let T : Subrepresentation σ := ⟨S.toSubmodule.comap f.toLinearMap, fun g v hv => by
      show f (σ g v) ∈ S.toSubmodule
      rw [f.isIntertwining]
      exact S.apply_mem_toSubmodule g hv⟩
    rcases eq_bot_or_eq_top T with e | e
    · refine eq_bot_iff.2 fun v hv => ?_
      obtain ⟨x, rfl⟩ := hS.le hv
      have hx : x ∈ T := hv
      rw [e] at hx
      have hx' : x = 0 := hx
      show f x = 0
      rw [hx', map_zero]
    · refine absurd (fun v hv => ?_) hS.not_ge
      obtain ⟨x, rfl⟩ := hv
      have hx : x ∈ T := e ▸ trivial
      exact hx

theorem isCoatom_ker {σ : Representation ℂ G W} {π : Representation ℂ G V} (h : σ.IsIrreducible)
    (f : π.IntertwiningMap σ) (hf : Function.Surjective f) : IsCoatom f.ker := by
  have := Model.nontrivial_of_isIrreducible h
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  refine ⟨fun e => hw ?_, fun S hS => ?_⟩
  · obtain ⟨v, rfl⟩ := hf w
    have : v ∈ f.ker := e ▸ trivial
    exact this
  · let T : Subrepresentation σ := ⟨S.toSubmodule.map f.toLinearMap, by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨π g v, S.apply_mem_toSubmodule g hv, f.isIntertwining _ _ g v⟩⟩
    rcases eq_bot_or_eq_top T with e | e
    · refine absurd (fun v hv => ?_) hS.not_ge
      have hx : f v ∈ T := ⟨v, hv, rfl⟩
      rw [e] at hx
      exact hx
    · refine eq_top_iff.2 fun v _ => ?_
      have hx : f v ∈ T := e ▸ trivial
      obtain ⟨x, hx, hxv⟩ := hx
      have hk : v - x ∈ f.ker := by
        show f (v - x) = 0
        rw [map_sub, sub_eq_zero]; exact hxv.symm
      have := S.toSubmodule.add_mem (hS.le hk) hx
      rwa [sub_add_cancel] at this

theorem nonempty_equiv_of_range_eq {σ : Representation ℂ G W} {τ : Representation ℂ G X} {π : Representation ℂ G V}
    (f : σ.IntertwiningMap π) (hf : Function.Injective f) (g : τ.IntertwiningMap π) (hg : Function.Injective g)
    (h : f.range = g.range) : Nonempty (σ.Equiv τ) := by
  let e : W ≃ₗ[ℂ] X := (LinearEquiv.ofInjective f.toLinearMap hf).trans
    ((LinearEquiv.ofEq _ _ (congrArg Subrepresentation.toSubmodule h)).trans
      (LinearEquiv.ofInjective g.toLinearMap hg).symm)
  have he : ∀ w, g (e w) = f w := fun w =>
    congrArg Subtype.val ((LinearEquiv.ofInjective g.toLinearMap hg).apply_symm_apply _)
  refine ⟨.mk e fun x => LinearMap.ext fun w => hg ?_⟩
  show g (e (σ x w)) = g (τ x (e w))
  rw [he, f.isIntertwining, g.isIntertwining, he]

theorem nonempty_equiv_of_ker_eq {σ : Representation ℂ G W} {τ : Representation ℂ G X} {π : Representation ℂ G V}
    (f : π.IntertwiningMap σ) (hf : Function.Surjective f) (g : π.IntertwiningMap τ) (hg : Function.Surjective g)
    (h : f.ker = g.ker) : Nonempty (σ.Equiv τ) := by
  let e : W ≃ₗ[ℂ] X := (f.toLinearMap.quotKerEquivOfSurjective hf).symm.trans
    ((Submodule.quotEquivOfEq _ _ (congrArg Subrepresentation.toSubmodule h)).trans
      (g.toLinearMap.quotKerEquivOfSurjective hg))
  have he : ∀ v, e (f v) = g v := fun v => by
    have : (f.toLinearMap.quotKerEquivOfSurjective hf).symm (f v) = Submodule.Quotient.mk v := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    exact (congrArg ((Submodule.quotEquivOfEq _ _ (congrArg Subrepresentation.toSubmodule h)).trans
      (g.toLinearMap.quotKerEquivOfSurjective hg)) this).trans rfl
  refine ⟨.mk e fun x => LinearMap.ext fun w => ?_⟩
  obtain ⟨v, rfl⟩ := hf w
  show e (σ x (f v)) = τ x (e (f v))
  rw [← f.isIntertwining, he, he, g.isIntertwining]

theorem IsSocle.equiv_of_embeds {σ : Representation ℂ G W} {τ : Representation ℂ G X} {π : Representation ℂ G V}
    (h : IsSocle σ π) (hτ : τ.IsIrreducible) (he : Embeds τ π) : Nonempty (τ.Equiv σ) := by
  obtain ⟨-, f, hf, hS⟩ := h
  obtain ⟨g, hg⟩ := he
  exact nonempty_equiv_of_range_eq g hg f hf (hS _ (isAtom_range hτ g hg))

theorem IsCosocle.equiv_of_surjective {σ : Representation ℂ G W} {τ : Representation ℂ G X} {π : Representation ℂ G V}
    (h : IsCosocle σ π) (hτ : τ.IsIrreducible) (g : π.IntertwiningMap τ) (hg : Function.Surjective g) :
    Nonempty (τ.Equiv σ) := by
  obtain ⟨-, f, hf, hS⟩ := h
  exact nonempty_equiv_of_ker_eq g hg f hf (hS _ (isCoatom_ker hτ g hg))

theorem IsSocle.unique {σ : Representation ℂ G W} {τ : Representation ℂ G X} {π : Representation ℂ G V}
    (h : IsSocle σ π) (h' : IsSocle τ π) : Nonempty (τ.Equiv σ) := h.equiv_of_embeds h'.1 h'.embeds

theorem IsCosocle.unique {σ : Representation ℂ G W} {τ : Representation ℂ G X} {π : Representation ℂ G V}
    (h : IsCosocle σ π) (h' : IsCosocle τ π) : Nonempty (τ.Equiv σ) :=
  let ⟨hi, g, hg, _⟩ := h'; h.equiv_of_surjective hi g hg

def isotypic (σ : Representation ℂ G V) (τ : Representation ℂ G W) : Subrepresentation σ where
  toSubmodule := ⨆ f : τ.IntertwiningMap σ, LinearMap.range f.toLinearMap
  apply_mem_toSubmodule g v hv := by
    refine Submodule.iSup_induction _ (motive := fun v => σ g v ∈ ⨆ f : τ.IntertwiningMap σ, LinearMap.range f.toLinearMap)
      hv ?_ (by simp) fun x y hx hy => by rw [map_add]; exact add_mem hx hy
    rintro f _ ⟨w, rfl⟩
    exact Submodule.mem_iSup_of_mem f ⟨τ g w, f.isIntertwining _ _ g w⟩

theorem apply_mem_isotypic {σ : Representation ℂ G V} {τ : Representation ℂ G W} (f : τ.IntertwiningMap σ) (w : W) :
    f w ∈ isotypic σ τ := Submodule.mem_iSup_of_mem f ⟨w, rfl⟩

theorem isotypic_ne_bot_iff {σ : Representation ℂ G V} {τ : Representation ℂ G W} :
    isotypic σ τ ≠ ⊥ ↔ ∃ f : τ.IntertwiningMap σ, f ≠ 0 := by
  rw [← not_iff_not, not_not, not_exists]
  simp only [not_not]
  constructor
  · intro h f
    ext w
    have := apply_mem_isotypic f w
    rw [h] at this
    exact this
  · intro h
    refine Subrepresentation.toSubmodule_injective (iSup_eq_bot.2 fun f => ?_)
    rw [h f]
    exact LinearMap.range_zero

theorem isotypic_ne_bot_iff_embeds {σ : Representation ℂ G V} {τ : Representation ℂ G W} (h : τ.IsIrreducible) :
    isotypic σ τ ≠ ⊥ ↔ Embeds τ σ := by
  rw [isotypic_ne_bot_iff]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, (injective_iff_map_eq_zero _).2 fun w hw => ?_⟩
    rcases eq_bot_or_eq_top f.ker with e | e
    · have : w ∈ f.ker := hw
      rw [e] at this
      exact this
    · refine absurd ?_ hf
      ext x
      have : x ∈ f.ker := e ▸ trivial
      exact this
  · rintro ⟨f, hf⟩
    have := Model.nontrivial_of_isIrreducible h
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    exact ⟨f, fun e => hw (hf (by rw [e, map_zero]; rfl))⟩

theorem map_mem_isotypic {σ : Representation ℂ G V} {σ' : Representation ℂ G X} (φ : σ.IntertwiningMap σ')
    (τ : Representation ℂ G W) {v : V} (hv : v ∈ isotypic σ τ) : φ v ∈ isotypic σ' τ := by
  refine Submodule.iSup_induction _ (motive := fun v => φ v ∈ isotypic σ' τ) hv ?_ ?_ fun x y hx hy => ?_
  · rintro f _ ⟨w, rfl⟩
    exact apply_mem_isotypic (φ.comp f) w
  · rw [map_zero]; exact (isotypic σ' τ).toSubmodule.zero_mem
  · rw [map_add]; exact (isotypic σ' τ).toSubmodule.add_mem hx hy

def isotypicMap {σ : Representation ℂ G V} {σ' : Representation ℂ G X} (φ : σ.IntertwiningMap σ')
    (τ : Representation ℂ G W) :
    (isotypic σ τ).toRepresentation.IntertwiningMap (isotypic σ' τ).toRepresentation where
  toLinearMap := φ.toLinearMap.restrict fun _ hv => map_mem_isotypic φ τ hv
  isIntertwining' g := LinearMap.ext fun v => Subtype.ext (φ.isIntertwining _ _ g v)

@[simp] theorem isotypicMap_apply {σ : Representation ℂ G V} {σ' : Representation ℂ G X} (φ : σ.IntertwiningMap σ')
    (τ : Representation ℂ G W) (v : (isotypic σ τ).toSubmodule) : (isotypicMap φ τ v : X) = φ v := rfl

def charIdem [Fintype G] (σ : Representation ℂ G V) (τ : Representation ℂ G W) [FiniteDimensional ℂ W] : V →ₗ[ℂ] V :=
  ((Module.finrank ℂ W : ℂ) / Fintype.card G) • ∑ g : G, LinearMap.trace ℂ W (τ g⁻¹) • σ g

end General

section Idem

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

def cosetSum (π : Representation ℂ G V) {H : Subgroup G} (U : Subgroup H) [Fintype (H ⧸ U)] : V →ₗ[ℂ] V :=
  ∑ q : H ⧸ U, π (q.out : H)

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem out_apply (π : Representation ℂ G V) {H : Subgroup G} {U : Subgroup H} {v : V} (hv : ∀ u ∈ U, π (u : H) v = v)
    (h : H) : π ((h : H ⧸ U).out : H) v = π h v := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U h
  rw [hu, Subgroup.coe_mul, map_mul, Module.End.mul_apply, hv u u.2]

theorem exists_normal_fix {π : Representation ℂ G V} (hπ : IsSmooth π) {H : Subgroup G} (hH : IsCompact (H : Set G))
    (v : V) : ∃ U : Subgroup H, U.Normal ∧ U.FiniteIndex ∧ ∀ u ∈ U, π (u : H) v = v := by
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hH
  let S : Subgroup H :=
    { carrier := {h | π h v = v}
      mul_mem' := fun {a b} ha hb => by
        show π (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        show π (a : G)⁻¹ v = v
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul]; simp }
  have ho : IsOpen (S : Set H) := (hπ v).preimage continuous_subtype_val
  haveI := S.quotient_finite_of_isOpen ho
  haveI := S.finiteIndex_of_finite_quotient
  exact ⟨S.normalCore, inferInstance, inferInstance, fun u hu => S.normalCore_le hu⟩

theorem isCompl_fixed_twKer {π : Representation ℂ G V} (hπ : IsSmooth π) {H : Subgroup G} (hH : IsCompact (H : Set G)) :
    IsCompl (fixed π H) (twKer π H 1) := by
  constructor
  · have key : ∀ v ∈ twKer π H 1, ∃ U₀ : Subgroup H, U₀.FiniteIndex ∧
        ∀ (U : Subgroup H) [U.Normal] [Fintype (H ⧸ U)], U ≤ U₀ → cosetSum π U v = 0 := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨n, u, rfl⟩ := hx
        obtain ⟨U₀, -, h0, hu⟩ := exists_normal_fix hπ hH u
        refine ⟨U₀, h0, fun U _ _ hU => ?_⟩
        simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, sub_eq_zero, cosetSum, LinearMap.sum_apply]
        refine Fintype.sum_equiv (Equiv.mulRight (n : H ⧸ U)) _ _ fun q => ?_
        have e : Equiv.mulRight (n : H ⧸ U) q = ((q.out * n : H) : H ⧸ U) := by
          rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']; rfl
        rw [e, out_apply π fun x hx => hu x (hU hx), Subgroup.coe_mul, map_mul, Module.End.mul_apply]
      | zero => exact ⟨⊤, inferInstance, fun U _ _ _ => map_zero _⟩
      | add x y _ _ hx hy =>
        obtain ⟨A, _, hA⟩ := hx
        obtain ⟨B, _, hB⟩ := hy
        exact ⟨A ⊓ B, inferInstance, fun U _ _ hU => by
          rw [map_add, hA U (hU.trans inf_le_left), hB U (hU.trans inf_le_right), add_zero]⟩
      | smul c x _ hx =>
        obtain ⟨A, h0, hA⟩ := hx
        exact ⟨A, h0, fun U _ _ hU => by rw [map_smul, hA U hU, smul_zero]⟩
    refine Submodule.disjoint_def.2 fun v hv hv' => ?_
    obtain ⟨U, _, hU⟩ := key v hv'
    letI := Fintype.ofFinite (H ⧸ U.normalCore)
    have h := hU U.normalCore U.normalCore_le
    rw [cosetSum, LinearMap.sum_apply, Finset.sum_congr rfl fun q _ => mem_fixed.1 hv _ (q.out : H).2,
      Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ] at h
    exact (smul_eq_zero.1 h).resolve_left (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  · refine codisjoint_iff.2 (eq_top_iff.2 fun v _ => ?_)
    obtain ⟨U, -, _, hU⟩ := exists_normal_fix hπ hH v
    letI := Fintype.ofFinite (H ⧸ U)
    have hc : (Fintype.card (H ⧸ U) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have h1 : cosetSum π U v ∈ fixed π H := mem_fixed.2 fun h hh => by
      simp only [cosetSum, LinearMap.sum_apply, map_sum]
      refine Fintype.sum_equiv (MulAction.toPerm (⟨h, hh⟩ : H)) _ _ fun q => ?_
      conv_rhs => rw [MulAction.toPerm_apply, ← q.out_eq, MulAction.Quotient.smul_mk]
      rw [out_apply π hU, smul_eq_mul, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
    have h2 : cosetSum π U v - (Fintype.card (H ⧸ U) : ℂ) • v ∈ twKer π H 1 := by
      rw [cosetSum, LinearMap.sum_apply, Nat.cast_smul_eq_nsmul, ← Finset.card_univ, ← Finset.sum_const,
        ← Finset.sum_sub_distrib]
      exact Submodule.sum_mem _ fun q _ => Submodule.subset_span ⟨q.out, v, by simp⟩
    have h3 := Submodule.smul_mem _ (Fintype.card (H ⧸ U) : ℂ)⁻¹
      (sub_mem (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2))
    rwa [sub_sub_cancel, smul_smul, inv_mul_cancel₀ hc, one_smul] at h3

def idem {π : Representation ℂ G V} (hπ : IsSmooth π) {H : Subgroup G} (hH : IsCompact (H : Set G)) : V →ₗ[ℂ] V :=
  (fixed π H).subtype ∘ₗ Submodule.linearProjOfIsCompl _ _ (isCompl_fixed_twKer hπ hH)

variable {π : Representation ℂ G V} (hπ : IsSmooth π) {H : Subgroup G} (hH : IsCompact (H : Set G))

theorem idem_mem (v : V) : idem hπ hH v ∈ fixed π H := Subtype.property _

theorem idem_of_mem {v : V} (hv : v ∈ fixed π H) : idem hπ hH v = v :=
  congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left (isCompl_fixed_twKer hπ hH) ⟨v, hv⟩)

theorem idem_eq_zero_iff {v : V} : idem hπ hH v = 0 ↔ v ∈ twKer π H 1 := by
  rw [← Submodule.linearProjOfIsCompl_apply_eq_zero_iff (isCompl_fixed_twKer hπ hH)]
  exact Submodule.coe_eq_zero

theorem idem_apply_mem {h : G} (hh : h ∈ H) (v : V) : idem hπ hH (π h v) = idem hπ hH v := by
  rw [← sub_eq_zero, ← map_sub, idem_eq_zero_iff]
  exact Submodule.subset_span ⟨⟨h, hh⟩, v, by simp⟩

theorem idem_eq_cosetSum (U : Subgroup H) [Fintype (H ⧸ U)] {v : V} (hv : ∀ u ∈ U, π (u : H) v = v) :
    idem hπ hH v = (Fintype.card (H ⧸ U) : ℂ)⁻¹ • ∑ q : H ⧸ U, π (q.out : H) v := by
  have hc : (Fintype.card (H ⧸ U) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h1 : ∑ q : H ⧸ U, π (q.out : H) v ∈ fixed π H := mem_fixed.2 fun h hh => by
    simp only [map_sum]
    refine Fintype.sum_equiv (MulAction.toPerm (⟨h, hh⟩ : H)) _ _ fun q => ?_
    conv_rhs => rw [MulAction.toPerm_apply, ← q.out_eq, MulAction.Quotient.smul_mk]
    rw [out_apply π hv, smul_eq_mul, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  rw [← idem_of_mem hπ hH h1, map_sum, Finset.sum_congr rfl fun q _ => idem_apply_mem hπ hH (q.out : H).2 v,
    Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

end Idem

section Classes

variable {G : Type} [Group G] [TopologicalSpace G]

omit [TopologicalSpace G] in

def orbitMap {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V) :
    (Representation.leftRegular ℂ G).IntertwiningMap ρ where
  toLinearMap := (LinearMap.applyₗ v ∘ₗ ρ.asAlgebraHom.toLinearMap : MonoidAlgebra ℂ G →ₗ[ℂ] V)
  isIntertwining' g := by
    ext h
    simp

omit [TopologicalSpace G] in

theorem orbitMap_surjective {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (h : ρ.IsIrreducible)
    {v : V} (hv : v ≠ 0) : Function.Surjective (orbitMap ρ v) := by
  have h1 : v ∈ (orbitMap ρ v).range := ⟨MonoidAlgebra.single 1 1, by
    show ρ.asAlgebraHom (MonoidAlgebra.single 1 1) v = v
    simp⟩
  rcases eq_bot_or_eq_top (orbitMap ρ v).range with e | e
  · rw [e] at h1; exact absurd h1 hv
  · intro w
    have : w ∈ (orbitMap ρ v).range := e ▸ trivial
    exact this

variable (G) in

instance small_irrCl : Small.{0} (IrrCl G) := by
  have hv : ∀ c : IrrCl G, ∃ v : c.rep.V, v ≠ 0 := fun c =>
    haveI := Model.nontrivial_of_isIrreducible c.rep.irr
    exists_ne 0
  choose v hv using hv
  refine small_of_injective (f := fun c => (orbitMap c.rep.ρ (v c)).ker) fun c d h => ?_
  rw [← c.cl_rep, ← d.cl_rep]
  exact IrrRep.cl_eq_iff.2 (nonempty_equiv_of_ker_eq _ (orbitMap_surjective c.rep.irr (hv c)) _
    (orbitMap_surjective d.rep.irr (hv d)) h)

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem cl_eq_iff_rep {σ : IrrRep G} {c : IrrCl G} : σ.cl = c ↔ Nonempty (σ.ρ.Equiv c.rep.ρ) := by
  conv_lhs => rw [← c.cl_rep]
  exact IrrRep.cl_eq_iff

theorem irrCl_eq_iff {c d : IrrCl G} : c = d ↔ Nonempty (c.rep.ρ.Equiv d.rep.ρ) := by
  rw [← cl_eq_iff_rep, IrrCl.cl_rep]

def equivRep (σ : IrrRep G) : σ.ρ.Equiv σ.cl.rep.ρ := (cl_eq_iff_rep.1 rfl).some

variable [IsTopologicalGroup G]

def irrTwist (σ : IrrRep G) (χ : G →* ℂˣ) (hχ : IsSmoothChar χ) : IrrRep G :=
  ⟨σ.V, twist σ.ρ χ, isSmooth_twist σ.smooth hχ, isIrreducible_twist σ.irr χ⟩

def clTwist (c : IrrCl G) (χ : G →* ℂˣ) (hχ : IsSmoothChar χ) : IrrCl G := (irrTwist c.rep χ hχ).cl

theorem clTwist_cl (σ : IrrRep G) (χ : G →* ℂˣ) (hχ : IsSmoothChar χ) :
    clTwist σ.cl χ hχ = (irrTwist σ χ hχ).cl :=
  IrrRep.cl_eq_iff.2 ⟨twistEquiv (equivRep σ).symm χ⟩

theorem clTwist_clTwist (c : IrrCl G) (χ ψ : G →* ℂˣ) (hχ : IsSmoothChar χ) (hψ : IsSmoothChar ψ) :
    clTwist (clTwist c χ hχ) ψ hψ = clTwist c (χ * ψ) (hχ.mul hψ) := by
  rw [clTwist.eq_1 c, clTwist_cl]
  refine IrrRep.cl_eq_iff.2 ⟨?_⟩
  show (twist (twist c.rep.ρ χ) ψ).Equiv (twist c.rep.ρ (χ * ψ))
  rw [twist_twist, mul_comm]
  exact .refl _

theorem clTwist_one (c : IrrCl G) (h : IsSmoothChar (1 : G →* ℂˣ)) : clTwist c 1 h = c :=
  cl_eq_iff_rep.2 ⟨by
    show (twist c.rep.ρ 1).Equiv c.rep.ρ
    rw [twist_one]; exact .refl _⟩

theorem clTwist_ofChar (χ ψ : G →* ℂˣ) (hχ : IsSmoothChar χ) (hψ : IsSmoothChar ψ) :
    clTwist (IrrRep.ofChar χ hχ).cl ψ hψ = (IrrRep.ofChar (χ * ψ) (hχ.mul hψ)).cl := by
  rw [clTwist_cl]
  refine IrrRep.cl_eq_iff.2 ⟨?_⟩
  show (twist (ofChar χ) ψ).Equiv (ofChar (χ * ψ))
  rw [ofChar, twist_twist, mul_comm]
  exact .refl _

end Classes

example {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] {χ ψ : G →* ℂˣ} (h : χ ≠ ψ) (σ : Representation ℂ G W) :
    ¬ IsSocle σ ((ofChar χ).prod (ofChar ψ)) := fun hs => by
  obtain ⟨a⟩ := hs.equiv_of_embeds (isIrreducible_ofChar χ)
    ⟨.inl ℂ (ofChar χ) (ofChar ψ), fun _ _ e => congrArg Prod.fst e⟩
  obtain ⟨b⟩ := hs.equiv_of_embeds (isIrreducible_ofChar ψ)
    ⟨.inr ℂ (ofChar χ) (ofChar ψ), fun _ _ e => congrArg Prod.snd e⟩
  have h1 := Model.jhMult_ofChar_ne h
  rw [jhMult_congr_left (a.trans b.symm), jhMult_self (isIrreducible_ofChar ψ)] at h1
  exact one_ne_zero h1

end GlobalTheory.LocGL
