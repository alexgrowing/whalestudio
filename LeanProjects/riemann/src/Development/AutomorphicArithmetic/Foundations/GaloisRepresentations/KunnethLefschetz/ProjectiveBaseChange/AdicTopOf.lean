import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtProps
import Development.EtaleCohomology.EtaleTrace.FrobTraceOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

structure Gens (l : ℕ) [Fact l.Prime] {X : Scheme.{0}} {r : ℕ} {Y : Fin r → Scheme.{0}} (j : ∀ s, Y s ⟶ X) {w : ℤ}
    (g : Fin r → V l X w) : Prop where
  ne : ∀ s, pb l (j s) w (g s) ≠ 0
  line : ∀ s (v : V l (Y s) w), ∃ z : ℚ_[l], v = z • pb l (j s) w (g s)
  off : ∀ s t, s ≠ t → pb l (j t) w (g s) = 0

def ProjBC : Prop := (∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)),
  IsProjOver p → IsProjOver (pullback.snd p (Spec.map (CommRingCat.ofHom φ)))) ∧
  ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)), IsProjOver p → IsProper p

def SumCl : Prop := ∀ {X : Scheme.{0}} {r : ℕ} {Y : Fin r → Scheme.{0}} (j : ∀ s, Y s ⟶ X), IsSum j → ∀ s, IsClosedImmersion (j s)

def SumBC : Prop := ∀ {X' X : Scheme.{0}} {r : ℕ} {Y' Y : Fin r → Scheme.{0}} (j' : ∀ s, Y' s ⟶ X') (j : ∀ s, Y s ⟶ X) (f : X' ⟶ X)
  (u : ∀ s, Y' s ⟶ Y s), (∀ s, IsPullback (j' s) (u s) f (j s)) → IsSum j → IsSum j'

def GeomPb : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (M N : Model l K) (u : M.X ⟶ N.X)
  (hu : u ≫ N.p = M.p), IsPullback (GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu))
    (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.fst _ _ ≫ pullback.fst _ _) u

def SumHl : Prop := InSum → ∀ (l : ℕ) [Fact l.Prime] {X : Scheme.{0}} {r : ℕ} {Y : Fin r → Scheme.{0}} (j : ∀ s, Y s ⟶ X), IsSum j →
  ∀ n : ℤ, Function.Bijective fun (x : Hl l (sch.obj X) n 0) (s : Fin r) => pullHl l (sch.map (j s)) n 0 x

def PiBC : Prop := ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (A : Type 1) (B : Fin r → Type 1) [AddCommGroup A] [Module ℤ_[l] A]
  [∀ s, AddCommGroup (B s)] [∀ s, Module ℤ_[l] (B s)] (f : ∀ s, A →ₗ[ℤ_[l]] B s), (Function.Bijective fun (x : A) s => f s x) →
  Function.Bijective fun (x : ℚ_[l] ⊗[ℤ_[l]] A) s => (f s).baseChange ℚ_[l] x

def DualSum : Prop := ∀ (l : ℕ) [Fact l.Prime], Ring l → ∀ {X : Scheme.{0}} {r : ℕ} {Y : Fin r → Scheme.{0}} (j : ∀ s, Y s ⟶ X) (d : ℕ),
  (∀ n : ℤ, Function.Bijective fun (x : V l X n) (s : Fin r) => pb l (j s) n x) → (∀ s, Dual l d (Y s)) →
  ∀ (a b w : ℤ) (h : a + b = w), w = 2 * d → ∃ g : Fin r → V l X w, Gens l j g ∧ Submodule.span ℚ_[l] (Set.range g) = ⊤ ∧
    Submodule.span ℚ_[l] {f : Module.Dual ℚ_[l] (V l X a) | ∃ (s : Fin r) (y : V l X b), ∀ x, cupV l X h x y = f x • g s} = ⊤

def Perm : Prop := ∀ (l : ℕ) [Fact l.Prime] {X : Scheme.{0}} {r : ℕ} {Y : Fin r → Scheme.{0}} (j : ∀ s, Y s ⟶ X) (w : ℤ),
  (Function.Injective fun (x : V l X w) (s : Fin r) => pb l (j s) w x) → ∀ g : Fin r → V l X w, Gens l j g →
  ∀ (φ : X ⟶ X) (π : Equiv.Perm (Fin r)) (θ : ∀ s, Y s ≅ Y (π s)), (∀ s, j s ≫ φ = (θ s).hom ≫ j (π s)) →
  ∀ s, ∃ z : ℚ_[l], z ≠ 0 ∧ pb l φ w (g (π s)) = z • g s

def IntFun : Prop := A11 → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (M : Model l K), Ring l →
  ∀ (i j r : ℕ) (g : Fin r → M.V (i + j)) (h : (i : ℤ) + (j : ℤ) = ((i + j : ℕ) : ℤ)),
  Submodule.span ℚ_[l] {f : Module.Dual ℚ_[l] (V l (GlobalTheory.Et.geom (PadicAlgCl l) M.q) i) | ∃ (s : Fin r)
    (y : V l (GlobalTheory.Et.geom (PadicAlgCl l) M.q) j), ∀ x, cupV l _ h x y =
      f x • (show V l (GlobalTheory.Et.geom (PadicAlgCl l) M.q) ((i + j : ℕ) : ℤ) from g s)} = ⊤ →
  Submodule.span ℚ_[l] {f : Module.Dual ℚ_[l] (M.V i) | ∃ (s : Fin r) (y : M.T j),
    ∀ x : M.T i, ∃ z, M.CupT x y z ∧ M.toV (i + j) z = f (M.toV i x) • g s} = ⊤

def CupEx : Prop := A11 → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (M : Model l K) {i j : ℕ}
  (x : M.T i) (y : M.T j), ∃ z, M.CupT x y z

def AdicTop : Prop := In → QDual → InSum → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
  (G : Model l K → Prop), (∀ M, G M → M.Good) → CompM G → (∀ M, G M → ∀ d, M.Conn d → M.Geo) → EtSide G

section
variable (h1 : ProjBC) (h2 : SumCl) (h5 : SumHl) (h6 : PiBC) (hQ : QDual) (hS : InSum)
  {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

include h5 h6 hS in
theorem sumQ {X : Scheme.{0}} {r : ℕ} {Y : Fin r → Scheme.{0}} (j : ∀ s, Y s ⟶ X) (hj : IsSum j) (n : ℤ) :
    Function.Bijective fun (x : V l X n) (s : Fin r) => pb l (j s) n x :=
  h6 l r _ _ (fun s => pullHl l (sch.map (j s)) n 0) (h5 hS l j hj n)

include h1 h2 hQ in
theorem dual_comp (M : Model l K) (hM : M.Good) (d : ℕ) (hc : M.Conn d) {r : ℕ} {Y : Fin r → Scheme.{0}}
    (j : ∀ s, Y s ⟶ GlobalTheory.Et.geom (PadicAlgCl l) M.q) (hj : IsSum j) (hY : ∀ s, IsIntegral (Y s)) (s : Fin r) : Dual l d (Y s) := by
  have hp : IsProjOver (pullback.snd M.q (Spec.map (CommRingCat.ofHom (algebraMap K (PadicAlgCl l))))) :=
    h1.1 _ _ _ _ (h1.1 _ _ _ _ hM.1)
  have := h1.2 _ _ hp
  have := h2 j hj s
  have := hj.1 s
  have := hc.2
  have hs : SmoothOfRelativeDimension d (pullback.snd M.q (Spec.map (CommRingCat.ofHom (algebraMap K (PadicAlgCl l))))) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback (IsPullback.of_hasPullback _ _) hc.2
  refine hQ l (PadicAlgCl l) (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) d
    (j s ≫ pullback.snd M.q (Spec.map (CommRingCat.ofHom (algebraMap K (PadicAlgCl l))))) ⟨inferInstance, ?_⟩ ?_ (hY s)
  · have h : SmoothOfRelativeDimension (0 + d)
        (j s ≫ pullback.snd M.q (Spec.map (CommRingCat.ofHom (algebraMap K (PadicAlgCl l))))) := inferInstance
    rwa [Nat.zero_add] at h
  · obtain ⟨N, i, hi, e⟩ := hp
    exact ⟨N, j s ≫ i, inferInstance, by rw [Category.assoc]; exact congrArg (j s ≫ ·) e⟩

end

theorem adicTop_of (hR : RingL) (h1 : ProjBC) (h2 : SumCl) (h3 : SumBC) (h4 : GeomPb) (h5 : SumHl) (h6 : PiBC) (h7 : DualSum)
    (h8 : Perm) (h9 : IntFun) (h10 : CupEx) : AdicTop := by
  intro hI hQ hS l _ K G hG hC hGeo
  have hcomp : ∀ M, G M → ∃ (r : ℕ) (P : Fin r → Model l K) (d : Fin r → ℕ) (u : ∀ a, (P a).X ⟶ M.X)
      (hu : ∀ a, u a ≫ M.p = (P a).p), (∀ a, G (P a) ∧ (P a).Conn (d a)) ∧
      ∀ (j : ℕ) (v : M.V j), (∀ a, Model.pullV (u a) (hu a) j v = 0) → v = 0 := fun M hM => by
    obtain ⟨r, P, d, u, hu, hs, hP⟩ := hC M hM
    refine ⟨r, P, d, u, hu, hP, fun j v hv => ?_⟩
    have hb := sumQ (l := l) h5 h6 hS _ (h3 _ u _ _ (fun a => h4 l K (P a) M (u a) (hu a)) hs) (j : ℤ)
    exact hb.1 (funext fun a => (hv a).trans (map_zero _).symm)
  have hfin : ∀ M, G M → ∀ d, M.Conn d → ∀ n : ℕ, FiniteDimensional ℚ_[l] (M.V n) := fun M hM d hd n => by
    obtain ⟨r, Y, j, hj, hY, -⟩ := hGeo M hM d hd
    have := fun s => (dual_comp h1 h2 hQ M (hG M hM) d hd j hj hY s).1 (n : ℤ)
    exact FiniteDimensional.of_injective (LinearMap.pi fun s => pb l (j s) (n : ℤ)) (sumQ h5 h6 hS j hj n).1
  refine ⟨fun M _ _ x y => h10 hI.a11 l K M x y, fun M hM n => ?_, fun M hM d hd => ?_, hcomp⟩
  · obtain ⟨r, P, d, u, hu, hP, h⟩ := hcomp M hM
    have := fun a => hfin (P a) (hP a).1 (d a) (hP a).2 n
    exact FiniteDimensional.of_injective (LinearMap.pi fun a => Model.pullV (u a) (hu a) n)
      ((injective_iff_map_eq_zero _).2 fun v hv => h n v fun a => congrFun hv a)
  · obtain ⟨r, Y, j, hj, hY, hπ, ht⟩ := hGeo M hM d hd
    have hD := dual_comp h1 h2 hQ M (hG M hM) d hd j hj hY
    have hb := sumQ (l := l) h5 h6 hS j hj
    refine ⟨fun i hi => ⟨fun x y => (hb i).1 (funext fun s => ((hD s).2.1 i (by omega)).elim _ _)⟩, fun a b hab => ?_⟩
    have hw : (a : ℤ) + (b : ℤ) = ((a + b : ℕ) : ℤ) := by push_cast; rfl
    obtain ⟨g, hg, hsp, hf⟩ := h7 l (hR hI l) j d hb hD a b _ hw (by omega)
    refine ⟨r, g, hsp, fun s s' => ?_, h9 hI.a11 l K M (hR hI l) a b r g hw hf⟩
    obtain ⟨σ, θ, e⟩ := ht s' s
    obtain ⟨π, θ', e'⟩ := hπ σ
    have hs : π s' = s := by
      by_contra hne
      have := hY s'
      obtain ⟨y⟩ : Nonempty (Y s') := inferInstance
      refine Set.disjoint_left.1 (hj.2.2 _ _ hne) ⟨(θ' s').hom y, rfl⟩ ⟨θ y, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← e, e' s']
    obtain ⟨z, hz, h⟩ := h8 l j _ (hb _).1 g hg _ π θ' e' s'
    rw [hs] at h
    exact ⟨σ, z, hz, h⟩

end UpperTheory.Gal.KunnethLefschetz
