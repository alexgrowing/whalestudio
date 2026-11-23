import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuationStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FieldTransport

section Pull

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

abbrev pull (ρ : Representation ℂ H V) (φ : G →* H) : Representation ℂ G V := ρ.comp φ

def subrepComp (ρ : Representation ℂ H V) (φ : G →* H) (hφ : Function.Surjective φ) :
    Subrepresentation (pull ρ φ) ≃o Subrepresentation ρ where
  toFun S := ⟨S.toSubmodule, fun h v hv => by
    obtain ⟨g, rfl⟩ := hφ h
    exact S.apply_mem_toSubmodule g hv⟩
  invFun S := ⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (φ g) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_comp_iff {ρ : Representation ℂ H V} {φ : G →* H} (hφ : Function.Surjective φ) :
    (pull ρ φ).IsIrreducible ↔ ρ.IsIrreducible :=
  (subrepComp ρ φ hφ).isSimpleOrder_iff

def intertwiningOfComp {ρ : Representation ℂ H V} {σ : Representation ℂ H W} {φ : G →* H}
    (hφ : Function.Surjective φ) (f : (pull ρ φ).IntertwiningMap (pull σ φ)) : ρ.IntertwiningMap σ :=
  ⟨f.toLinearMap, fun h => by
    obtain ⟨g, rfl⟩ := hφ h
    exact f.isIntertwining' g⟩

def equivComp {ρ : Representation ℂ H V} {σ : Representation ℂ H W} (φ : G →* H) (e : ρ.Equiv σ) :
    (pull ρ φ).Equiv (pull σ φ) :=
  equivOfBijective ⟨e.toLinearMap, fun g => e.toIntertwiningMap.isIntertwining' (φ g)⟩
    e.toLinearEquiv.bijective

theorem isCosocle_of_comp {σ : Representation ℂ H W} {π : Representation ℂ H V} {φ : G →* H}
    (hφ : Function.Surjective φ) (h : IsCosocle (pull σ φ) (pull π φ)) : IsCosocle σ π := by
  obtain ⟨hi, f, hf, hS⟩ := h
  refine ⟨(isIrreducible_comp_iff hφ).1 hi, intertwiningOfComp hφ f, hf, fun S hS' => ?_⟩
  have h1 := hS ((subrepComp π φ hφ).symm S) (((subrepComp π φ hφ).symm.isCoatom_iff S).2 hS')
  have h2 := congrArg Subrepresentation.toSubmodule h1
  have inj : Function.Injective (Subrepresentation.toSubmodule (ρ := π)) := by
    rintro ⟨a, _⟩ ⟨b, _⟩ rfl; rfl
  exact inj h2

variable [TopologicalSpace G] [TopologicalSpace H]

theorem isSmooth_comp {ρ : Representation ℂ H V} (hρ : IsSmooth ρ) {φ : G →* H} (hφ : Continuous φ) :
    IsSmooth (pull ρ φ) := fun v => (hρ v).preimage hφ

end Pull

section GLMap

variable {n R S : Type} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]

@[simp] theorem glMap_symm_glMap (j : R ≃+* S) (g : GL n R) :
    GeneralLinearGroup.map (j.symm : S →+* R) (GeneralLinearGroup.map (j : R →+* S) g) = g := by
  ext; simp

@[simp] theorem glMap_glMap_symm (j : R ≃+* S) (g : GL n S) :
    GeneralLinearGroup.map (j : R →+* S) (GeneralLinearGroup.map (j.symm : S →+* R) g) = g := by
  ext; simp

theorem glMap_surjective (j : R ≃+* S) : Function.Surjective (GeneralLinearGroup.map (n := n) (j : R →+* S)) :=
  fun g => ⟨_, glMap_glMap_symm j g⟩

theorem continuous_glMap [TopologicalSpace R] [TopologicalSpace S] (j : R →+* S) (hj : Continuous j) :
    Continuous (GeneralLinearGroup.map (n := n) j) := by
  refine Units.continuous_iff.2 ⟨Units.continuous_val.matrix_map hj, ?_⟩
  simp only [← map_inv]
  exact Units.continuous_coe_inv.matrix_map hj

end GLMap

end GlobalTheory.FieldTransport

namespace GlobalTheory.FieldTransport

section Ind

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n] {W : Type} [AddCommGroup W] [Module ℂ W]

def leviMap (j : k' →+* k) : Levi k' m →* Levi k m :=
  MonoidHom.pi fun a => (GeneralLinearGroup.map j).comp (Pi.evalMonoidHom (fun a => GL (m a) k') a)

theorem det_glMap {p : Type} [Fintype p] [DecidableEq p] (j : k' →+* k) (g : GL p k') :
    GeneralLinearGroup.det (GeneralLinearGroup.map j g) = Units.map j.toMonoidHom (GeneralLinearGroup.det g) := by
  ext; simp [RingHom.map_det]

theorem glMap_mem_parab (e : (Σ a, m a) ≃ n) (j : k' →+* k) (p : parab k' e) :
    GeneralLinearGroup.map j (p : GL n k') ∈ parab k e :=
  mem_parab_iff.2 fun a b i l hab => by
    show j (((p : GL n k') : Matrix n n k') (e ⟨a, i⟩) (e ⟨b, l⟩)) = 0
    rw [mem_parab_iff.1 p.2 a b i l hab, map_zero]

theorem leviProj_glMap (e : (Σ a, m a) ≃ n) (j : k' →+* k) (p : parab k' e) :
    leviProj k e ⟨_, glMap_mem_parab e j p⟩ = leviMap j (leviProj k' e p) := by
  funext a
  ext i l
  rfl

theorem deltaHalf_leviMap (j : k' →+* k)
    (habs : ∀ (s : ℂ) (x : k'ˣ), absPow k s (Units.map j.toMonoidHom x) = absPow k' s x) (h : Levi k' m) :
    deltaHalf k m (leviMap j h) = deltaHalf k' m h := by
  rw [deltaHalf_apply, deltaHalf_apply]
  refine Finset.prod_congr rfl fun a _ => ?_
  show absPow k _ (GeneralLinearGroup.det (GeneralLinearGroup.map j (h a))) = _
  rw [det_glMap, habs]

end Ind

end GlobalTheory.FieldTransport

namespace GlobalTheory.FieldTransport

section IndMap

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n] {W : Type} [AddCommGroup W] [Module ℂ W]

def indFun (e : (Σ a, m a) ≃ n) (j : k ≃+* k') (hj : Continuous j.symm)
    (habs : ∀ (s : ℂ) (x : k'ˣ), absPow k s (Units.map (j.symm : k' →+* k).toMonoidHom x) = absPow k' s x)
    {ρ : Representation ℂ (Levi k m) W} {ρ' : Representation ℂ (Levi k' m) W}
    (hρ : ∀ h, ρ' h = ρ (leviMap (j.symm : k' →+* k) h)) (f : IndSp e ρ) : IndSp e ρ' :=
  ⟨⟨fun g => f.1.1 (GeneralLinearGroup.map (j.symm : k' →+* k) g), fun p g => by
    have h1 := parInd_law e ρ f ⟨_, glMap_mem_parab e (j.symm : k' →+* k) p⟩
      (GeneralLinearGroup.map (j.symm : k' →+* k) g)
    rw [leviProj_glMap, deltaHalf_leviMap _ habs, ← hρ] at h1
    show f.1.1 (GeneralLinearGroup.map (j.symm : k' →+* k) (p * g)) =
      (deltaHalf k' m (leviProj k' e p) : ℂ) • ρ' (leviProj k' e p) (f.1.1 (GeneralLinearGroup.map (j.symm : k' →+* k) g))
    rw [map_mul]
    exact h1⟩, by
    have hf : IsOpen {g : GL n k | ind (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e)) g f.1 = f.1} := f.2
    show IsOpen {g' : GL n k' | _}
    convert hf.preimage (continuous_glMap (n := n) (j.symm : k' →+* k) hj) using 1
    ext g'
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · intro h
      refine Subtype.ext (funext fun x => ?_)
      have h2 : f.1.1 (GeneralLinearGroup.map (j.symm : k' →+* k) (GeneralLinearGroup.map (j : k →+* k') x * g')) =
          f.1.1 (GeneralLinearGroup.map (j.symm : k' →+* k) (GeneralLinearGroup.map (j : k →+* k') x)) :=
        congrFun (congrArg Subtype.val h) _
      rw [map_mul, glMap_symm_glMap] at h2
      exact h2
    · intro h
      refine Subtype.ext (funext fun x => ?_)
      have h2 : f.1.1 (GeneralLinearGroup.map (j.symm : k' →+* k) x * GeneralLinearGroup.map (j.symm : k' →+* k) g') =
          f.1.1 (GeneralLinearGroup.map (j.symm : k' →+* k) x) :=
        congrFun (congrArg Subtype.val h) _
      show f.1.1 (GeneralLinearGroup.map (j.symm : k' →+* k) (x * g')) = _
      rw [map_mul]
      exact h2⟩

end IndMap

end GlobalTheory.FieldTransport

namespace GlobalTheory.FieldTransport

section IndEquiv

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n] {W : Type} [AddCommGroup W] [Module ℂ W]

theorem leviMap_symm_leviMap (j : k ≃+* k') (h : Levi k m) :
    leviMap (j.symm : k' →+* k) (leviMap (j : k →+* k') h) = h :=
  funext fun a => glMap_symm_glMap j (h a)

theorem nonempty_equiv_parInd (e : (Σ a, m a) ≃ n) (j : k ≃+* k') (hj : Continuous j) (hj' : Continuous j.symm)
    (habs : ∀ (s : ℂ) (x : k'ˣ), absPow k s (Units.map (j.symm : k' →+* k).toMonoidHom x) = absPow k' s x)
    (habs' : ∀ (s : ℂ) (x : kˣ), absPow k' s (Units.map (j : k →+* k').toMonoidHom x) = absPow k s x)
    {ρ : Representation ℂ (Levi k m) W} {ρ' : Representation ℂ (Levi k' m) W}
    (hρ : ∀ h, ρ' h = ρ (leviMap (j.symm : k' →+* k) h)) :
    Nonempty ((parInd e ρ).Equiv (pull (parInd e ρ') (GeneralLinearGroup.map (j : k →+* k')))) := by
  have hρ' : ∀ h, ρ h = ρ' (leviMap (j.symm.symm : k →+* k') h) := fun h => by
    rw [hρ]
    exact congrArg ρ (leviMap_symm_leviMap j h).symm
  let Φ : (parInd e ρ).IntertwiningMap (pull (parInd e ρ') (GeneralLinearGroup.map (j : k →+* k'))) :=
    ⟨{ toFun := indFun e j hj' habs hρ
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl }, fun g => LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => by
      show f.1.1 (GeneralLinearGroup.map (j.symm : k' →+* k) x * g) =
        f.1.1 (GeneralLinearGroup.map (j.symm : k' →+* k) (x * GeneralLinearGroup.map (j : k →+* k') g))
      rw [map_mul, glMap_symm_glMap]))⟩
  refine ⟨equivOfBijective Φ ⟨fun f f' h => Subtype.ext (Subtype.ext (funext fun g => ?_)), fun F => ?_⟩⟩
  · have h2 : f.1.1 (GeneralLinearGroup.map (j.symm : k' →+* k) (GeneralLinearGroup.map (j : k →+* k') g)) =
        f'.1.1 (GeneralLinearGroup.map (j.symm : k' →+* k) (GeneralLinearGroup.map (j : k →+* k') g)) :=
      congrFun (congrArg (fun F : IndSp e ρ' => F.1.1) h) _
    rwa [glMap_symm_glMap] at h2
  · refine ⟨indFun (k := k') (k' := k) e j.symm hj habs' hρ' F, Subtype.ext (Subtype.ext (funext fun x => ?_))⟩
    show F.1.1 (GeneralLinearGroup.map (j.symm.symm : k →+* k') (GeneralLinearGroup.map (j.symm : k' →+* k) x)) = F.1.1 x
    rw [glMap_symm_glMap]

end IndEquiv

end GlobalTheory.FieldTransport

namespace GlobalTheory.FieldTransport

section Classes

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem nonempty_equiv_of_repRel (i : k ≃+* k') {N : ℕ} (y : IrrRep (GL (Fin N) k)) (y' : IrrRep (GL (Fin N) k'))
    (h : RepRel i (cls y) (cls y')) : Nonempty (y.ρ.Equiv (pull y'.ρ (GeneralLinearGroup.map (i : k →+* k')))) := by
  obtain ⟨n, π, π', e, h1, h2, he⟩ := h
  obtain ⟨rfl, h1⟩ := Sigma.mk.inj_iff.1 h1
  obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.1 h2
  obtain ⟨a⟩ := IrrRep.cl_eq_iff.1 (eq_of_heq h1)
  obtain ⟨b⟩ := IrrRep.cl_eq_iff.1 (eq_of_heq h2)
  let f : π.ρ.Equiv (pull π'.ρ (GeneralLinearGroup.map (i : k →+* k'))) :=
    equivOfBijective ⟨e.toLinearMap, fun g => LinearMap.ext fun v => he g v⟩ e.bijective
  exact ⟨a.trans (f.trans (equivComp _ b.symm))⟩

theorem eq_of_repRel (i : k ≃+* k') (hi : Continuous i.symm) {z : IrrGL k} {z' : IrrGL k'} (h : RepRel i z z') :
    z' = IrrGL.of (pull z.rep (GeneralLinearGroup.map (i.symm : k' →+* k)))
      (isSmooth_comp z.2.rep.smooth (continuous_glMap (i.symm : k' →+* k) hi))
      ((isIrreducible_comp_iff (glMap_surjective i.symm)).2 z.2.rep.irr) := by
  obtain ⟨n, π, π', e, rfl, rfl, he⟩ := h
  refine congrArg (Sigma.mk n) (IrrRep.cl_eq_iff.2 ?_)
  obtain ⟨b⟩ := IrrRep.nonempty_equiv_rep π
  let f : π'.ρ.Equiv (pull π.ρ (GeneralLinearGroup.map (i.symm : k' →+* k))) :=
    equivOfBijective ⟨e.symm.toLinearMap, fun g => LinearMap.ext fun v => by
      apply e.injective
      show e (e.symm (π'.ρ g v)) = e (π.ρ (GeneralLinearGroup.map (i.symm : k' →+* k) g) (e.symm v))
      rw [e.apply_symm_apply, he, e.apply_symm_apply]
      exact congrArg (fun g => π'.ρ g v) (glMap_glMap_symm i g).symm⟩ e.symm.bijective
  exact ⟨f.trans (equivComp _ b.symm)⟩

end Classes

theorem isCosocle_prodIrr_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k']
    [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (r N : ℕ) (x : Fin r → IrrGL k)
    (x' : Fin r → IrrGL k') (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x' a).1 = N) (y : IrrRep (GL (Fin N) k))
    (y' : IrrRep (GL (Fin N) k')), (∀ a, RepRel i (x a) (x' a)) → RepRel i (cls y) (cls y') →
    IsCosocle y.ρ (prodIrr x hd) → IsCosocle y'.ρ (prodIrr x' hd') := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi r N x x' hd hd' y y' hx hy hc
  have T1 := GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation k k' i hi
  have hi' : Continuous i.symm := T1.1
  have T2 := GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation k' k i.symm hi'
  have hs : ∀ a, IsSmooth (pull (x a).rep (GeneralLinearGroup.map (i.symm : k' →+* k))) := fun a =>
    isSmooth_comp (x a).2.rep.smooth (continuous_glMap (i.symm : k' →+* k) hi')
  have hirr : ∀ a, (pull (x a).rep (GeneralLinearGroup.map (i.symm : k' →+* k))).IsIrreducible := fun a =>
    (isIrreducible_comp_iff (glMap_surjective i.symm)).2 (x a).2.rep.irr
  have hx' : x' = fun a => IrrGL.of _ (hs a) (hirr a) := funext fun a => eq_of_repRel i hi' (hx a)
  subst hx'
  have A := (nonempty_equiv_of_repRel i y y' hy).some
  have B := (nonempty_equiv_parInd (stdBlocks (fun a => (x a).1) hd) i hi hi' T2.2.2.2.2 T1.2.2.2.2
    (ρ := piTensor fun a => (x a).rep)
    (ρ' := piTensor fun a => pull (x a).rep (GeneralLinearGroup.map (i.symm : k' →+* k))) (fun _ => rfl)).some
  have C : (multiProd (stdBlocks (fun a => (x a).1) hd) (fun a => pull (x a).rep (GeneralLinearGroup.map (i.symm : k' →+* k)))).Equiv
      (prodIrr (fun a => IrrGL.of _ (hs a) (hirr a)) hd') :=
    prodIrrEquiv hd (fun a => pull (x a).rep (GeneralLinearGroup.map (i.symm : k' →+* k))) hs hirr
  have D : (prodIrr x hd).Equiv (pull (prodIrr (fun a => IrrGL.of _ (hs a) (hirr a)) hd') (GeneralLinearGroup.map (i : k →+* k'))) :=
    B.trans (equivComp _ C)
  have E : IsCosocle (pull y'.ρ (GeneralLinearGroup.map (i : k →+* k')))
      (pull (prodIrr (fun a => IrrGL.of _ (hs a) (hirr a)) hd') (GeneralLinearGroup.map (i : k →+* k'))) :=
    hc.of_equiv A D
  exact isCosocle_of_comp (glMap_surjective i) E

end GlobalTheory.FieldTransport
