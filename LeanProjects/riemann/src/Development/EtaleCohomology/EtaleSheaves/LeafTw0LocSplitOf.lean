import Development.EtaleCohomology.EtaleSheaves.LeafTensMonoPf
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.ZModInj

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0LocSplitPf

def LeafTw0LocGen : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (n : ℕ) (a : Fin n → Sec (tw q 0) U),
  Loc U fun V g => ∃ (e : Sec (tw q 0) V) (c : Fin n → ULift.{1} (ZMod q)),
    (∀ k, Sec.res g (a k) = c k • e) ∧ (e = 0 ∨ ∃ ζ : Prim q Γ(V, ⊤), e = twGen 0 ζ)

theorem baerU (q : ℕ) [NeZero q] : Module.Baer (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q)) := by
  intro I g
  let J : Ideal (ZMod q) :=
    { carrier := {y | (ULift.up y : ULift.{1} (ZMod q)) ∈ I}
      add_mem' := fun {a b} ha hb => I.add_mem ha hb
      zero_mem' := I.zero_mem
      smul_mem' := fun c {y} hy => by
        have := I.smul_mem (ULift.up c) hy
        exact this }
  let g' : J →ₗ[ZMod q] ZMod q :=
    { toFun := fun y => (g ⟨ULift.up y.1, y.2⟩).down
      map_add' := fun a b => by
        have := g.map_add ⟨ULift.up a.1, a.2⟩ ⟨ULift.up b.1, b.2⟩
        exact congrArg ULift.down this
      map_smul' := fun c a => by
        have := g.map_smul (ULift.up c) ⟨ULift.up a.1, a.2⟩
        exact congrArg ULift.down this }
  obtain ⟨h, hh⟩ := KStar.Selmer.zmod_baer J g'
  refine ⟨{ toFun := fun x => ULift.up (h x.down)
            map_add' := fun a b => congrArg ULift.up (h.map_add a.down b.down)
            map_smul' := fun c a => congrArg ULift.up (h.map_smul c.down a.down) }, ?_⟩
  intro x hx
  exact congrArg ULift.up (hh x.down hx)

theorem retract (q : ℕ) [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (x : M)
    (hx : ∀ c : ULift.{1} (ZMod q), c • x = 0 → c = 0) :
    ∃ r : M →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q), r x = 1 := by
  let f : ULift.{1} (ZMod q) →ₗ[ULift.{1} (ZMod q)] M := LinearMap.toSpanSingleton _ _ x
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc; exact hx c hc
  obtain ⟨r, hr⟩ := (baerU q).extension_property f hf LinearMap.id
  refine ⟨r, ?_⟩
  have := LinearMap.congr_fun hr 1
  simpa [f] using this

def LeafTw0GenFree : Prop := ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)),
  twGen 0 ζ = 0 ∨ ∀ c : ULift.{1} (ZMod q), c • resGen 0 ζ = 0 → c = 0

theorem genSplit_of (hF : LeafTw0GenFree) (q : ℕ) [NeZero q] (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)) :
    twGen 0 ζ = 0 ∨ ∃ r : Sec ((res _ (tw q 0)).X 0) V →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q), r (resGen 0 ζ) = 1 := by
  rcases hF q V ζ with h | h
  · exact Or.inl h
  · exact Or.inr (retract q _ h)

section
variable {R : Type} [CommRing R]

theorem map_comp' {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := by
  simp [Sec.map]

theorem map_res' {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  exact congrArg (fun f => ModuleCat.Hom.hom f x) (φ.hom.naturality g.op)
end

theorem LeafTw0LocSplit_of (h1 : LeafTw0LocGen) (h2 : LeafTw0GenFree) : LateralTheory.E.LeafTensMonoPf.LeafTw0LocSplit := by
  intro q _ U n a
  let I : (sgl (tw q 0)).X 0 ≅ tw q 0 := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q 0)
  obtain ⟨S, hS, hP⟩ := h1 q U n (fun k => Sec.map I.hom (a k))
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨e', c, hc, he'⟩ := hP V g hg
  have back : ∀ y : Sec ((sgl (tw q 0)).X 0) V, Sec.map I.inv (Sec.map I.hom y) = y := by
    intro y; refine (map_comp' I.hom I.inv y).symm.trans ?_; simp [Sec.map]
  refine ⟨Sec.map I.inv e', c, fun k => ?_, ?_⟩
  · rw [← back (Sec.res g (a k)), map_res' I.hom g (a k), hc k]
    exact map_smul (I.inv.hom.app (op V)).hom (c k) e'
  · rcases he' with rfl | ⟨ζ, rfl⟩
    · left; simp [Sec.map]
    · rcases genSplit_of h2 q V ζ with h0 | ⟨r, hr⟩
      · left; simp [h0, Sec.map]
      · right; refine ⟨r, ?_⟩
        convert hr using 2
        exact (map_comp' I.inv ((resAug (tw q 0)).f 0) (twGen 0 ζ)).symm

end LateralTheory.E.LeafTw0LocSplitPf
