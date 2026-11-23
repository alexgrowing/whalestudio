import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Formalism.GaloisCohomology.LocalTateDualityK

noncomputable section

open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Filter Topology
open scoped TensorProduct

namespace GlobalTheory.TensIsoExt

open ReciprocityTheory.Def (Z1 B1 H1 d0 d1 C1)

section Abstract

variable {O G : Type} [CommRing O] [Group G]
variable {A B C : Type} [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B]
  [AddCommGroup C] [Module O C]

def ambMap {π : Representation O G A} {π' : Representation O G B} (f : A →ₗ[O] B)
    (hf : ∀ g m, f (π g m) = π' g (f m)) : Amb π →ₗ[O] Amb π' :=
  Submodule.mapQ _ _ (f.compLeft G) (by
    rintro z ⟨b, -, hb⟩
    refine ⟨f b, Submodule.mem_top, ?_⟩
    funext g
    have h1 : π g b - b = z g := congrFun hb g
    change π' g (f b) - f b = f (z g)
    rw [← h1, map_sub, hf])

theorem ambMap_mk {π : Representation O G A} {π' : Representation O G B} (f : A →ₗ[O] B)
    (hf : ∀ g m, f (π g m) = π' g (f m)) (u : G → A) :
    ambMap f hf (Submodule.Quotient.mk u) = Submodule.Quotient.mk (fun g => f (u g)) := rfl

theorem amb_eq_iff {π : Representation O G A} (u v : G → A) :
    (Submodule.Quotient.mk u : Amb π) = Submodule.Quotient.mk v ↔ ∃ m, ∀ g, π g m - m = u g - v g := by
  rw [Submodule.Quotient.eq, ReciprocityTheory.Def.B1, Submodule.mem_map]
  constructor
  · rintro ⟨m, -, hm⟩
    exact ⟨m, fun g => congrFun hm g⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, Submodule.mem_top, funext hm⟩

variable [TopologicalSpace G]

theorem mem_range_toAmb {π : Representation O G A} (x : Amb π) :
    x ∈ LinearMap.range (toAmb π) ↔ ∃ z ∈ Z1 π ⊤, Submodule.Quotient.mk z = x := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨z, z.2, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨Submodule.Quotient.mk ⟨z, hz⟩, rfl⟩

theorem mem_cocycles_units_iff {π : Representation O G A} (z : G → A) :
    z ∈ Z1 π ⊤ ↔ IsLocallyConstant z ∧ ∀ g h, π g (z h) - z (g * h) + z g = 0 := by
  rw [Z1, Submodule.mem_inf, LinearMap.mem_ker]
  constructor
  · rintro ⟨hc, hd⟩
    exact ⟨hc.1, fun g h => congrFun hd (g, h)⟩
  · rintro ⟨hlc, hd⟩
    refine ⟨⟨hlc, fun _ => Submodule.mem_top⟩, ?_⟩
    funext x
    exact hd x.1 x.2

variable {HA HB HC : Type} [AddCommGroup HA] [Module O HA] [AddCommGroup HB] [Module O HB]
  [AddCommGroup HC] [Module O HC]

private theorem ambMap_injective_lemma {πA : Representation O G A} {πB : Representation O G B}
    {πC : Representation O G C} (α : A →ₗ[O] B) (β : B →ₗ[O] C) (hα : ∀ g m, α (πA g m) = πB g (α m))
    (hβ : ∀ g m, β (πB g m) = πC g (β m)) (αinj : Function.Injective α) (ex : Function.Exact α β)
    (hinv : πC.invariants = ⊥) : Function.Injective (ambMap α hα) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h0 : (Submodule.Quotient.mk (fun g => α (u g)) : Amb πB) = Submodule.Quotient.mk 0 := by
    rw [Submodule.Quotient.mk_zero, ← hx, ambMap_mk]
  obtain ⟨m, hm⟩ := (amb_eq_iff _ _).1 h0
  have hm' : ∀ g, πB g m - m = α (u g) := fun g => by simpa using hm g
  have hfix : β m ∈ πC.invariants := by
    rw [Representation.mem_invariants]
    intro g
    have e := congrArg β (hm' g)
    rw [map_sub, hβ, ex.apply_apply_eq_zero] at e
    exact sub_eq_zero.1 e
  rw [hinv, Submodule.mem_bot] at hfix
  obtain ⟨a₀, ha₀⟩ := (ex m).1 hfix
  rw [← Submodule.Quotient.mk_zero, amb_eq_iff]
  refine ⟨a₀, fun g => αinj ?_⟩
  rw [map_sub, hα, ha₀, hm' g, Pi.zero_apply, sub_zero]

theorem five {πA : Representation O G A} {πB : Representation O G B} {πC : Representation O G C}
    (α : A →ₗ[O] B) (β : B →ₗ[O] C) (hα : ∀ g m, α (πA g m) = πB g (α m))
    (hβ : ∀ g m, β (πB g m) = πC g (β m)) (αinj : Function.Injective α) (ex : Function.Exact α β)
    (βsurj : Function.Surjective β)
    (a : HA →ₗ[O] HB) (b : HB →ₗ[O] HC) (ex' : Function.Exact a b) (bsurj : Function.Surjective b)
    (φA : HA →ₗ[O] Amb πA) (φB : HB →ₗ[O] Amb πB) (φC : HC →ₗ[O] Amb πC)
    (sqa : ∀ y, ambMap α hα (φA y) = φB (a y)) (sqb : ∀ y, ambMap β hβ (φB y) = φC (b y))
    (hle : LinearMap.range φB ≤ LinearMap.range (toAmb πB))
    (hlc : ∀ m, IsLocallyConstant fun g => πB g m) (hinv : πC.invariants = ⊥)
    (hA : Function.Injective φA ∧ LinearMap.range φA = LinearMap.range (toAmb πA))
    (hC : Function.Injective φC ∧ LinearMap.range φC = LinearMap.range (toAmb πC)) :
    Function.Injective φB ∧ LinearMap.range φB = LinearMap.range (toAmb πB) := by
  have hαi := ambMap_injective_lemma α β hα hβ αinj ex hinv
  refine ⟨?_, le_antisymm hle ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h1 : φC (b y) = 0 := by rw [← sqb, hy, map_zero]
    have h2 : b y = 0 := hC.1 (by rw [h1, map_zero])
    obtain ⟨x, rfl⟩ := (ex' y).1 h2
    have h3 : φA x = 0 := hαi (by rw [sqa, hy, map_zero])
    have h4 : x = 0 := hA.1 (by rw [h3, map_zero])
    rw [h4, map_zero]
  · rintro _ ⟨ζ, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ ζ
    obtain ⟨hzlc, hzc⟩ := (mem_cocycles_units_iff (z : G → B)).1 z.2
    have hβz : (fun g => β ((z : G → B) g)) ∈ Z1 πC ⊤ := by
      refine (mem_cocycles_units_iff _).2 ⟨hzlc.comp β, fun g h => ?_⟩
      rw [← hβ, ← map_sub, ← map_add, hzc g h, map_zero]
    have hC' := (mem_range_toAmb (Submodule.Quotient.mk (fun g => β ((z : G → B) g)) : Amb πC)).2
      ⟨_, hβz, rfl⟩
    rw [← hC.2] at hC'
    obtain ⟨w, hw⟩ := hC'
    obtain ⟨y, rfl⟩ := bsurj w
    obtain ⟨z', hz'mem, hz'eq⟩ := (mem_range_toAmb (φB y)).1 (hle (LinearMap.mem_range_self φB y))
    obtain ⟨hz'lc, hz'c⟩ := (mem_cocycles_units_iff z').1 hz'mem
    have hcl : (Submodule.Quotient.mk (fun g => β (z' g)) : Amb πC) =
        Submodule.Quotient.mk (fun g => β ((z : G → B) g)) := by
      rw [← ambMap_mk β hβ, hz'eq, sqb, hw]
    obtain ⟨c, hc⟩ := (amb_eq_iff _ _).1 hcl
    obtain ⟨m₀, hm₀⟩ := βsurj c
    have hk : ∀ g, β ((z : G → B) g - z' g + (πB g m₀ - m₀)) = 0 := by
      intro g
      have e := hc g
      rw [map_add, map_sub, map_sub, hβ, hm₀, e]
      abel
    choose u hu using fun g => (ex ((z : G → B) g - z' g + (πB g m₀ - m₀))).1 (hk g)
    have hulc : IsLocallyConstant u := by
      refine IsLocallyConstant.desc u α ?_ αinj
      have e : α ∘ u = fun g => (z : G → B) g - z' g + (πB g m₀ - m₀) := funext hu
      rw [e]
      exact (hzlc.sub hz'lc).add ((hlc m₀).sub (IsLocallyConstant.const m₀))
    have hum : u ∈ Z1 πA ⊤ := by
      refine (mem_cocycles_units_iff u).2 ⟨hulc, fun g h => αinj ?_⟩
      have e1 : (z : G → B) (g * h) = πB g ((z : G → B) h) + (z : G → B) g := by
        have e := hzc g h
        rw [sub_add_eq_add_sub, sub_eq_zero] at e
        exact e.symm
      have e2 : z' (g * h) = πB g (z' h) + z' g := by
        have e := hz'c g h
        rw [sub_add_eq_add_sub, sub_eq_zero] at e
        exact e.symm
      rw [map_zero, map_add, map_sub, hα, hu, hu, hu, e1, e2, map_mul, Module.End.mul_apply]
      simp only [map_add, map_sub]
      abel
    obtain ⟨x, hx⟩ : Submodule.Quotient.mk u ∈ LinearMap.range φA := by
      rw [hA.2]
      exact (mem_range_toAmb _).2 ⟨u, hum, rfl⟩
    refine ⟨y + a x, ?_⟩
    rw [map_add, ← sqa, hx, ambMap_mk, ← hz'eq, ← Submodule.Quotient.mk_add]
    change _ = (Submodule.Quotient.mk (z : G → B) : Amb πB)
    rw [amb_eq_iff]
    refine ⟨m₀, fun g => ?_⟩
    rw [Pi.add_apply, hu]
    abel

end Abstract
section Tens

variable {G LL O V : Type} [Group G] [TopologicalSpace G] [Field LL] [CommRing O] [Algebra O LL]
  [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [TopologicalSpace V] [ContinuousAdd V]
  [ContinuousConstSMul LL V] {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (χ : G →* Oˣ)
  {X X' : Type} [AddCommGroup X] [Module O X] [AddCommGroup X'] [Module O X']

omit [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] in

theorem lTensor_equivariant (f : X →ₗ[O] X') (g : G) (m : ↥L.T ⊗[O] X) :
    f.lTensor ↥L.T (twCoef (latRep L) χ X g m) = twCoef (latRep L) χ X' g (f.lTensor ↥L.T m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul t x => simp only [twCoef, coefRep_tmul, LinearMap.lTensor_tmul]
  | add p q hp hq => simp only [map_add, hp, hq]

theorem tensAmb_natural (f : X →ₗ[O] X') (y : H1tw L χ ⊗[O] X) :
    ambMap (f.lTensor ↥L.T) (lTensor_equivariant L χ f) (tensAmb L χ X y) =
      tensAmb L χ X' (f.lTensor (H1tw L χ) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c x =>
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    rw [LinearMap.lTensor_tmul, tensAmb_tmul, tensAmb_tmul, ambMap_mk]
    congr 1
  | add p q hp hq => simp only [map_add, hp, hq]

end Tens

theorem tensIso_of_exact : ∀ (G LL O V : Type) [Group G] [TopologicalSpace G] [Field LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] (ρ : Representation LL G V) (L : Lattice (O := O) ρ) (χ : G →* Oˣ) (S X Y : Type) [AddCommGroup S] [Module O S] [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module O Y] (i : S →ₗ[O] X) (p : X →ₗ[O] Y), Function.Injective i → Function.Exact i p → Function.Surjective p → (∀ c x, tensCoc L χ X c x ∈ ReciprocityTheory.Def.Z1 (twCoef (latRep L) χ X) ⊤) → (∀ m, IsLocallyConstant fun g => twCoef (latRep L) χ X g m) → (twCoef (latRep L) χ Y).invariants = ⊥ → TensIso L χ S → TensIso L χ Y → TensIso L χ X := by
  intro G LL O V _ _ _ _ _ _ _ _ _ _ _ _ ρ L χ S X Y _ _ _ _ _ _ i p hi hex hp hcoc hlc hinv hS hY
  have := L.free
  refine five (i.lTensor ↥L.T) (p.lTensor ↥L.T) (lTensor_equivariant L χ i) (lTensor_equivariant L χ p)
    (Module.Flat.lTensor_preserves_injective_linearMap i hi) (lTensor_exact _ hex hp)
    (LinearMap.lTensor_surjective _ hp) (i.lTensor (H1tw L χ)) (p.lTensor (H1tw L χ))
    (lTensor_exact _ hex hp) (LinearMap.lTensor_surjective _ hp)
    (tensAmb L χ S) (tensAmb L χ X) (tensAmb L χ Y) (fun y => tensAmb_natural L χ i y)
    (fun y => tensAmb_natural L χ p y) ?_ hlc hinv hS hY
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul c x =>
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    rw [tensAmb_tmul]
    exact (mem_range_toAmb _).2 ⟨_, hcoc c x, rfl⟩
  | add p q hp hq => rw [map_add]; exact Submodule.add_mem _ hp hq

end GlobalTheory.TensIsoExt
