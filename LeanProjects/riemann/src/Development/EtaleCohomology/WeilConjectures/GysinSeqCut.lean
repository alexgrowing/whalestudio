import Development.EtaleCohomology.WeilConjectures.FermatCount

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

namespace LateralTheory.EWeil.Gys

section Supp
variable (q : ℕ) (i : ℤ)

abbrev SecI (X : Scheme.{0}) (n : ℤ) : Type 1 := Sec ((res _ (tw q i)).X n) X

def resA {V U : Scheme.{0}} (g : V ⟶ U) (n : ℤ) : SecI q i U n →+ SecI q i V n :=
  ((((res _ (tw q i)).X n).obj.map g.op).hom).toAddMonoidHom

def dA (U : Scheme.{0}) (n m : ℤ) : SecI q i U n →+ SecI q i U m :=
  ((((res _ (tw q i)).d n m).hom.app (Opposite.op U)).hom).toAddMonoidHom

theorem resA_dA {V U : Scheme.{0}} (g : V ⟶ U) (n m : ℤ) (x : SecI q i U n) :
    resA q i g m (dA q i U n m x) = dA q i V n m (resA q i g n x) :=
  (ConcreteCategory.congr_hom (((res _ (tw q i)).d n m).hom.naturality g.op) x).symm

theorem resA_comp {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (n : ℤ) (x : SecI q i U n) :
    resA q i (f ≫ g) n x = resA q i f n (resA q i g n x) :=
  ConcreteCategory.congr_hom (((res _ (tw q i)).X n).obj.map_comp g.op f.op) x

def cyc {U X : Scheme.{0}} (j : U ⟶ X) (n : ℤ) : AddSubgroup (SecI q i X n) := (resA q i j n).ker ⊓ (dA q i X n (n + 1)).ker

def bnd {U X : Scheme.{0}} (j : U ⟶ X) (n : ℤ) : AddSubgroup (SecI q i X n) := (resA q i j (n - 1)).ker.map (dA q i X (n - 1) n)

abbrev HZ {U X : Scheme.{0}} (j : U ⟶ X) (n : ℤ) : Type 1 := cyc q i j n ⧸ (bnd q i j n).addSubgroupOf (cyc q i j n)

def pullZ {U X U' X' : Scheme.{0}} {j : U ⟶ X} {j' : U' ⟶ X'} (f : X' ⟶ X) (g : U' ⟶ U) (w : g ≫ j = j' ≫ f) (n : ℤ) :
    HZ q i j n →+ HZ q i j' n :=
  have h : ∀ (m : ℤ) (x : SecI q i X m), resA q i j m x = 0 → resA q i j' m (resA q i f m x) = 0 := fun m x hx => by
    rw [← resA_comp, ← w, resA_comp, hx, map_zero]
  QuotientAddGroup.map _ _
    (((resA q i f n).comp (cyc q i j n).subtype).codRestrict (cyc q i j' n) fun x =>
      ⟨h n x.1 x.2.1, ((resA_dA q i f n (n + 1) x.1).symm.trans (congrArg _ x.2.2)).trans (map_zero _)⟩)
    (by
      rintro x ⟨y, hy, e⟩
      exact ⟨resA q i f _ y, h _ y hy, (resA_dA q i f _ _ y).symm.trans (congrArg _ e)⟩)

def redZ (Q q : ℕ) (i : ℤ) {U X : Scheme.{0}} (j : U ⟶ X) (n : ℤ) : HZ Q i j n →+ HZ q i j n :=
  have h : ∀ (m : ℤ) (x : SecI Q i X m), resA Q i j m x = 0 → resA q i j m ((redMap Q q i).app X m x) = 0 := fun m x hx =>
    (((redMap Q q i).nat j m x).trans (congrArg _ hx)).trans (map_zero _)
  QuotientAddGroup.map _ _
    ((((redMap Q q i).app X n).comp (cyc Q i j n).subtype).codRestrict (cyc q i j n) fun x =>
      ⟨h n x.1 x.2.1, (((redMap Q q i).comm X n (n + 1) x.1).trans (congrArg _ x.2.2)).trans (map_zero _)⟩)
    (by
      rintro x ⟨y, hy, e⟩
      exact ⟨(redMap Q q i).app X _ y, h _ y hy, ((redMap Q q i).comm X _ _ y).trans (congrArg _ e)⟩)

end Supp

def Good (l r : ℕ) {X Z U : Scheme.{0}} (ι : Z ⟶ X) (j : U ⟶ X) : Prop :=
  IsClosedImmersion ι ∧ IsOpenImmersion j ∧ Set.range j = (Set.range ι)ᶜ ∧
  ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (e : ℕ) (p : X ⟶ Sp Ω), (l : Ω) ≠ 0 ∧
    SmoothOfRelativeDimension (e + r) p ∧ SmoothOfRelativeDimension e (ι ≫ p)

structure SPair (l r : ℕ) where
  (X Z U : Scheme.{0})
  (ι : Z ⟶ X)
  (j : U ⟶ X)
  good : Good l r ι j

structure SPair.Hom {l r : ℕ} (P' P : SPair l r) where
  (fX : P'.X ⟶ P.X)
  (fZ : P'.Z ⟶ P.Z)
  (fU : P'.U ⟶ P.U)
  etale : Etale fX
  sqZ : IsPullback fZ P'.ι P.ι fX
  sqU : fU ≫ P.j = P'.j ≫ fX

section Lim
variable (l : ℕ) [Fact l.Prime]

structure Tower (E : Spc) (n i : ℤ) (E' : Spc) (n' i' : ℤ) where
  app : ∀ c : ℕ, Ht (l ^ c) E n i →+ Ht (l ^ c) E' n' i'
  comm : ∀ c x, red (l ^ (c + 1)) (l ^ c) E' n' i' (app (c + 1) x) = app c (red (l ^ (c + 1)) (l ^ c) E n i x)

variable {l} {E E' : Spc} {n i n' i' : ℤ}

def Tower.hl (u : Tower l E n i E' n' i') : Hl l E n i →ₗ[ℤ_[l]] Hl l E' n' i' where
  toFun x := ⟨fun c => u.app c (x.1 c), fun c => (u.comm c _).trans (congrArg _ (x.2 c))⟩
  map_add' x y := Subtype.ext (funext fun c => map_add (u.app c) (x.1 c) (y.1 c))
  map_smul' r x := Subtype.ext (funext fun c =>
    ((congrArg (u.app c) (HtL.smul_eq l c c le_rfl E n i r (x.1 c))).trans (map_nsmul (u.app c) _ _)).trans
      (HtL.smul_eq l c c le_rfl E' n' i' r (u.app c (x.1 c))).symm)

def Tower.hq (u : Tower l E n i E' n' i') : HQ l E n i →ₗ[ℚ_[l]] HQ l E' n' i' := u.hl.baseChange ℚ_[l]

variable (l) in

def Tower.pull (f : E ⟶ E') (n i : ℤ) : Tower l E' n i E n i := ⟨fun _ => GlobalTheory.EtC.pull _ f _ n, fun _ x => (pull_red _ _ f n i x).symm⟩

end Lim

abbrev HG (q : ℕ) {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Sp k) (n i : ℤ) : Type 1 :=
  Ht q (sch.obj (geom Ω p)) n i

abbrev frG (q : ℕ) {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Sp k) (σ : Ω ≃ₐ[k] Ω)
    (n i : ℤ) : HG q Ω p n i →+ HG q Ω p n i := pull _ (sch.map (galMap Ω p σ⁻¹)) (tw q i) n

open CochainComplex.HomComplex in

def OpSpec : Prop := ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J) (E : Spc) (n : ℤ)
  (α : Cocycle ((chains S).obj E) I n), ∃ β : Cocycle ((chains R).obj E) J n,
    (∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev β.1 p s h U x = ρ.app U s (ev α.1 p s h U x)) ∧
    ρ.op.app E n (CohomologyClass.mk α) = CohomologyClass.mk β

def SuppSeq : Prop :=
  ∃ (o : ∀ (q : ℕ) (i : ℤ) {U X : Scheme.{0}} (j : U ⟶ X) (n : ℤ), HZ q i j n →+ Ht q (sch.obj X) n i)
    (b : ∀ (q : ℕ) (i : ℤ) {U X : Scheme.{0}} (j : U ⟶ X) [Mono j] (n : ℤ), Ht q (sch.obj U) n i →+ HZ q i j (n + 1)),
    (∀ (q : ℕ) (i : ℤ) {U X : Scheme.{0}} (j : U ⟶ X) [Mono j] (n : ℤ),
      Function.Exact (o q i j n) (pull _ (sch.map j) (tw q i) n) ∧ Function.Exact (pull _ (sch.map j) (tw q i) n) (b q i j n) ∧
      Function.Exact (b q i j n) (o q i j (n + 1))) ∧
    (∀ (q : ℕ) (i : ℤ) {U X U' X' : Scheme.{0}} (j : U ⟶ X) (j' : U' ⟶ X') [Mono j] [Mono j'] (f : X' ⟶ X) (g : U' ⟶ U)
      (w : g ≫ j = j' ≫ f) (n : ℤ), (∀ x, o q i j' n (pullZ q i f g w n x) = pull _ (sch.map f) _ n (o q i j n x)) ∧
      ∀ y, b q i j' n (pull _ (sch.map g) _ n y) = pullZ q i f g w (n + 1) (b q i j n y)) ∧
    ∀ (Q q : ℕ) (i : ℤ) {U X : Scheme.{0}} (j : U ⟶ X) [Mono j] (n : ℤ),
      (∀ x, o q i j n (redZ Q q i j n x) = red Q q _ n i (o Q i j n x)) ∧
      ∀ y, b q i j n (red Q q _ n i y) = redZ Q q i j (n + 1) (b Q i j n y)

def LocalVan : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (P : SPair l r) (c : ℕ) (i n : ℤ), n ≠ 2 * r →
  ∀ x : HZ (l ^ c) i P.j n, ∃ (P' : SPair l r) (f : P'.Hom P), Surjective f.fX ∧ pullZ _ i f.fX f.fU f.sqU n x = 0

def Thom0 : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ),
  ∃ θ : ∀ (P : SPair l r) (c : ℕ) (i : ℤ), Ht (l ^ c) (sch.obj P.Z) 0 i ≃+ HZ (l ^ c) (i + r) P.j (2 * r),
    (∀ (P' P : SPair l r) (f : P'.Hom P) (c : ℕ) (i : ℤ) x,
      θ P' c i (pull _ (sch.map f.fZ) _ 0 x) = pullZ _ _ f.fX f.fU f.sqU _ (θ P c i x)) ∧
    ∀ (P : SPair l r) (c : ℕ) (i : ℤ) x, θ P c i (red (l ^ (c + 1)) (l ^ c) _ 0 i x) = redZ _ _ _ P.j _ (θ P (c + 1) i x)

def Purity : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ),
  ∃ θ : ∀ (P : SPair l r) (c : ℕ) (i a b : ℤ), a + 2 * r = b → (Ht (l ^ c) (sch.obj P.Z) a i ≃+ HZ (l ^ c) (i + r) P.j b),
    (∀ (P' P : SPair l r) (f : P'.Hom P) (c : ℕ) (i a b : ℤ) h x,
      θ P' c i a b h (pull _ (sch.map f.fZ) _ a x) = pullZ _ _ f.fX f.fU f.sqU _ (θ P c i a b h x)) ∧
    ∀ (P : SPair l r) (c : ℕ) (i a b : ℤ) h x,
      θ P c i a b h (red (l ^ (c + 1)) (l ^ c) _ a i x) = redZ _ _ _ P.j _ (θ P (c + 1) i a b h x)

def GysinFin : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ),
  ∃ (g : ∀ (P : SPair l r) (i i' a b : ℤ), i + r = i' → a + 2 * r = b → Tower l (sch.obj P.Z) a i (sch.obj P.X) b i')
    (δ : ∀ (P : SPair l r) (i i' b a : ℤ), i + r = i' → a + 2 * r = b + 1 → Tower l (sch.obj P.U) b i' (sch.obj P.Z) a i),
    (∀ P i i' a b h h' c, Function.Exact ((g P i i' a b h h').app c) (pull _ (sch.map P.j) _ b)) ∧
    (∀ P i i' b a h h' c, Function.Exact (pull _ (sch.map P.j) _ b) ((δ P i i' b a h h').app c)) ∧
    (∀ P i i' b a h h' c, Function.Exact ((δ P i i' b a h h').app c) ((g P i i' a (b + 1) h h').app c)) ∧
    (∀ (P' P : SPair l r) (f : P'.Hom P) i i' a b h h' c x,
      (g P' i i' a b h h').app c (pull _ (sch.map f.fZ) _ a x) = pull _ (sch.map f.fX) _ b ((g P i i' a b h h').app c x)) ∧
    ∀ (P' P : SPair l r) (f : P'.Hom P) i i' b a h h' c x,
      (δ P' i i' b a h h').app c (pull _ (sch.map f.fU) _ b x) = pull _ (sch.map f.fZ) _ a ((δ P i i' b a h h').app c x)

def Geo : Prop := ∀ (l : ℕ) (k : Type) [Field k], (l : k) ≠ 0 →
  ∀ (e r : ℕ) {X Z : Scheme.{0}} (p : X ⟶ Sp k) (ι : Z ⟶ X) (U : X.Opens), IsClosedImmersion ι →
  SmoothOfRelativeDimension (e + r) p → SmoothOfRelativeDimension e (ι ≫ p) → (U : Set X) = (Set.range ι)ᶜ →
  ∀ (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω],
    Good l r (geomMap Ω (p := ι ≫ p) (q := p) ι rfl) (geomMap Ω (p := U.ι ≫ p) (q := p) U.ι rfl) ∧
    ∀ τ : Ω ≃ₐ[k] Ω, Etale (galMap Ω p τ) ∧
      IsPullback (galMap Ω (ι ≫ p) τ) (geomMap Ω (p := ι ≫ p) (q := p) ι rfl) (geomMap Ω (p := ι ≫ p) (q := p) ι rfl)
        (galMap Ω p τ) ∧
      galMap Ω (U.ι ≫ p) τ ≫ geomMap Ω (p := U.ι ≫ p) (q := p) U.ι rfl =
        geomMap Ω (p := U.ι ≫ p) (q := p) U.ι rfl ≫ galMap Ω p τ

def Twist : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (σ : Ω ≃ₐ[k] Ω), IsFrob σ → ∀ r : ℕ,
  ∃ t : ∀ {X : Scheme.{0}} (p : X ⟶ Sp k) (n : ℤ), Tower l (sch.obj (geom Ω p)) n 0 (sch.obj (geom Ω p)) n r,
    (∀ {X : Scheme.{0}} (p : X ⟶ Sp k) n c, Function.Bijective ((t p n).app c)) ∧
    (∀ {X Y : Scheme.{0}} (p : X ⟶ Sp k) (p' : Y ⟶ Sp k) (u : X ⟶ Y) (hu : u ≫ p' = p) n c x,
      (t p n).app c (pull _ (sch.map (geomMap Ω p u hu)) _ n x) = pull _ (sch.map (geomMap Ω p u hu)) _ n ((t p' n).app c x)) ∧
    ∀ {X : Scheme.{0}} (p : X ⟶ Sp k) n c x,
      (t p n).app c (frG _ p σ n 0 x) = (Nat.card k) ^ r • frG _ p σ n r ((t p n).app c x)

def FinPart : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (e r : ℕ) {X Z : Scheme.{0}} (p : X ⟶ Sp k) (ι : Z ⟶ X) (U : X.Opens), IsClosedImmersion ι →
  SmoothOfRelativeDimension (e + r) p → SmoothOfRelativeDimension e (ι ≫ p) → (U : Set X) = (Set.range ι)ᶜ →
  (FinT l (ι ≫ p) → (FinT l p ↔ FinT l (U.ι ≫ p))) ∧ (FinT l p → FinT l (U.ι ≫ p) → FinT l (ι ≫ p))

def GysinTw : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (e r : ℕ) {X Z : Scheme.{0}} (p : X ⟶ Sp k) (ι : Z ⟶ X) (U : X.Opens), IsClosedImmersion ι →
  SmoothOfRelativeDimension (e + r) p → SmoothOfRelativeDimension e (ι ≫ p) → (U : Set X) = (Set.range ι)ᶜ →
  ∀ (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (σ : Ω ≃ₐ[k] Ω), IsFrob σ →
  ∃ (g : ∀ a b : ℤ, a + 2 * r = b → Tower l (sch.obj (geom Ω (ι ≫ p))) a 0 (sch.obj (geom Ω p)) b 0)
    (δ : ∀ b a : ℤ, a + 2 * r = b + 1 → Tower l (sch.obj (geom Ω (U.ι ≫ p))) b 0 (sch.obj (geom Ω (ι ≫ p))) a 0),
    (∀ a b h c, Function.Exact ((g a b h).app c) (pull _ (sch.map (geomMap Ω (p := U.ι ≫ p) (q := p) U.ι rfl)) _ b)) ∧
    (∀ b a h c, Function.Exact (pull _ (sch.map (geomMap Ω (p := U.ι ≫ p) (q := p) U.ι rfl)) _ b) ((δ b a h).app c)) ∧
    (∀ b a h c, Function.Exact ((δ b a h).app c) ((g a (b + 1) h).app c)) ∧
    (∀ a b h c x, frG _ p σ b 0 ((g a b h).app c x) = (Nat.card k) ^ r • (g a b h).app c (frG _ (ι ≫ p) σ a 0 x)) ∧
    ∀ b a h c x, (δ b a h).app c (frG _ (U.ι ≫ p) σ b 0 x) = (Nat.card k) ^ r • frG _ (ι ≫ p) σ a 0 ((δ b a h).app c x)

def LimExact : Prop := ∀ (l : ℕ) [Fact l.Prime] {E E' E'' : Spc} {n i n' i' n'' i'' : ℤ} (u : Tower l E n i E' n' i')
  (v : Tower l E' n' i' E'' n'' i''), (∀ c, Finite (Ht (l ^ c) E n i)) → (∀ c, Function.Exact (u.app c) (v.app c)) →
  Function.Exact u.hq v.hq

theorem bc_comm {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {M N P P' : Type 1} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [AddCommGroup P'] [Module R M] [Module R N] [Module R P] [Module R P'] (f : M →ₗ[R] P) (g : P →ₗ[R] N)
    (f' : M →ₗ[R] P') (g' : P' →ₗ[R] N) (m r : ℕ) (h : ∀ x, g (f x) = m ^ r • g' (f' x)) (x : TensorProduct R A M) :
    g.baseChange A (f.baseChange A x) = (m : A) ^ r • g'.baseChange A (f'.baseChange A x) := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  induction x with
  | zero => simp
  | tmul a y => simp only [LinearMap.baseChange_tmul, h, TensorProduct.tmul_smul]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

theorem goal_of (h1 : FinPart) (h2 : GysinTw) (h3 : LimExact) : GysinSeq := by
  intro hB l _ k _ _ hl e r X Z _ p ι U hι hp hZ hU
  obtain ⟨a1, a2⟩ := h1 hB l k hl e r p ι U hι hp hZ hU
  refine ⟨a1, a2, fun fX fZ Ω _ _ _ σ hσ => ?_⟩
  have fU := (a1 fZ).1 fX
  obtain ⟨g, δ, e1, e2, e3, c1, c2⟩ := h2 hB l k hl e r p ι U hι hp hZ hU Ω σ hσ
  refine ⟨fun a b h => (g a b h).hq, fun b a h => (δ b a h).hq,
    fun a b h => h3 l (g a b h) (Tower.pull l _ b 0) (fun c => fZ Ω c a 0) (e1 a b h),
    fun b a h => h3 l (Tower.pull l _ b 0) (δ b a h) (fun c => fX Ω c b 0) (e2 b a h),
    fun b a h => h3 l (δ b a h) (g a (b + 1) h) (fun c => fU Ω c b 0) (e3 b a h), fun a b h x => ?_, fun b a h x => ?_⟩
  · exact bc_comm (g a b h).hl (galHl l Ω p b 0 σ⁻¹) (galHl l Ω (ι ≫ p) a 0 σ⁻¹) (g a b h).hl _ _
      (fun y => Subtype.ext (funext fun c => c1 a b h c (y.1 c))) x
  · exact bc_comm (galHl l Ω (U.ι ≫ p) b 0 σ⁻¹) (δ b a h).hl (δ b a h).hl (galHl l Ω (ι ≫ p) a 0 σ⁻¹) _ _
      (fun y => Subtype.ext (funext fun c => c2 b a h c (y.1 c))) x

end LateralTheory.EWeil.Gys

end
