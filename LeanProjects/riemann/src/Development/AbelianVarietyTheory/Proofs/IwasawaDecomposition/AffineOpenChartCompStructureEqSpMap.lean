import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsTrans
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueSubMemInitSpan
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp
  tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag

attribute [local instance] Over.cartesianMonoidalCategory in
open MonObj in

instance tanAddCommGroup {X : Scheme.{0}} {S : Type} [CommRing S] (x : Sp S ⟶ X) (G : Over X) [GrpObj G]
    [IsCommMonObj G] : AddCommGroup (TanM x G) := inferInstance

section Bundles

structure Charts (X : Scheme.{0}) : Type 1 where
  ι : Type
  [fin : Finite ι]
  R : ι → Type
  [ring : ∀ a, CommRing (R a)]
  χ : ∀ a, Sp (R a) ⟶ X
  opn : ∀ a, IsOpenImmersion (χ a)

attribute [instance] Charts.fin Charts.ring Charts.opn

def Charts.carrier {X : Scheme.{0}} (ch : Charts X) : Set X := ⋃ a, Set.range (ch.χ a)

structure Coc (Z : Scheme.{0}) : Type 1 where
  A : Type
  B : A → Z.Opens
  aff : ∀ α, IsAffineOpen (B α)
  cover : ∀ x : Z, ∃ α, x ∈ B α
  n : A → ℕ
  T : ∀ α β, Matrix (Fin (n α)) (Fin (n β)) Γ(Z, B α ⊓ B β)
  refl : ∀ (α : A) (S : Type) [CommRing S] (z : Sp S ⟶ Z) (h : ⊤ ≤ z ⁻¹ᵁ B α),
    (T α α).map (ev z _ (le_preimage_inf h h)) = 1
  coc : ∀ (α β γ : A) (S : Type) [CommRing S] (z : Sp S ⟶ Z) (hα : ⊤ ≤ z ⁻¹ᵁ B α) (hβ : ⊤ ≤ z ⁻¹ᵁ B β)
    (hγ : ⊤ ≤ z ⁻¹ᵁ B γ), (T α β).map (ev z _ (le_preimage_inf hα hβ)) * (T β γ).map (ev z _ (le_preimage_inf hβ hγ)) =
      (T α γ).map (ev z _ (le_preimage_inf hα hγ))

namespace Coc

variable {Z Z' : Scheme.{0}} (C : Coc Z) {S S' : Type} [CommRing S] [CommRing S']

def tr (α β : C.A) (z : Sp S ⟶ Z) (hα : ⊤ ≤ z ⁻¹ᵁ C.B α) (hβ : ⊤ ≤ z ⁻¹ᵁ C.B β) :
    Matrix (Fin (C.n α)) (Fin (C.n β)) S := (C.T α β).map (ev z _ (le_preimage_inf hα hβ))

theorem tr_self (α : C.A) (z : Sp S ⟶ Z) (h : ⊤ ≤ z ⁻¹ᵁ C.B α) : C.tr α α z h h = 1 := C.refl α S z h

theorem tr_mul (α β γ : C.A) (z : Sp S ⟶ Z) (hα : ⊤ ≤ z ⁻¹ᵁ C.B α) (hβ : ⊤ ≤ z ⁻¹ᵁ C.B β) (hγ : ⊤ ≤ z ⁻¹ᵁ C.B γ) :
    C.tr α β z hα hβ * C.tr β γ z hβ hγ = C.tr α γ z hα hγ := C.coc α β γ S z hα hβ hγ

theorem tr_spMap (α β : C.A) (φ : S →+* S') (z : Sp S ⟶ Z) (hα : ⊤ ≤ z ⁻¹ᵁ C.B α) (hβ : ⊤ ≤ z ⁻¹ᵁ C.B β)
    {z' : Sp S' ⟶ Z} (e : spMap φ ≫ z = z') (hα' : ⊤ ≤ z' ⁻¹ᵁ C.B α) (hβ' : ⊤ ≤ z' ⁻¹ᵁ C.B β) :
    C.tr α β z' hα' hβ' = (C.tr α β z hα hβ).map φ := by
  subst e
  rw [tr, tr, ev_spMap φ z _ (le_preimage_inf hα hβ), Matrix.map_map]; rfl

def refine {Γ : Type} (a : Γ → C.A) (D : Γ → Z.Opens) (aff : ∀ γ, IsAffineOpen (D γ)) (cover : ∀ x : Z, ∃ γ, x ∈ D γ)
    (le : ∀ γ, D γ ≤ C.B (a γ)) : Coc Z where
  A := Γ
  B := D
  aff := aff
  cover := cover
  n γ := C.n (a γ)
  T γ δ := (C.T (a γ) (a δ)).map (resG Z (inf_le_inf (le γ) (le δ)))
  refl γ S _ z h := by
    rw [← C.refl (a γ) S z (le_preimage_mono (le γ) h), Matrix.map_map]
    ext i j
    exact ev_res z _ _ _ _
  coc γ δ ε S _ z h₁ h₂ h₃ := by
    have key : ∀ (γ δ : Γ) (h₁ : ⊤ ≤ z ⁻¹ᵁ D γ) (h₂ : ⊤ ≤ z ⁻¹ᵁ D δ),
        ((C.T (a γ) (a δ)).map (resG Z (inf_le_inf (le γ) (le δ)))).map (ev z _ (le_preimage_inf h₁ h₂)) =
        C.tr (a γ) (a δ) z (le_preimage_mono (le γ) h₁) (le_preimage_mono (le δ) h₂) := fun γ δ h₁ h₂ => by
      ext i j
      exact ev_res z _ _ _ _
    rw [key γ δ h₁ h₂, key δ ε h₂ h₃, key γ ε h₁ h₃, tr_mul]

theorem refine_tr {Γ : Type} (a : Γ → C.A) (D : Γ → Z.Opens) (aff : ∀ γ, IsAffineOpen (D γ))
    (cover : ∀ x : Z, ∃ γ, x ∈ D γ) (le : ∀ γ, D γ ≤ C.B (a γ)) (γ δ : Γ) (z : Sp S ⟶ Z) (h₁ : ⊤ ≤ z ⁻¹ᵁ D γ)
    (h₂ : ⊤ ≤ z ⁻¹ᵁ D δ) : (C.refine a D aff cover le).tr γ δ z h₁ h₂ =
      C.tr (a γ) (a δ) z (le_preimage_mono (le γ) h₁) (le_preimage_mono (le δ) h₂) := by
  ext i j
  exact ev_res z _ _ _ _

structure Emb (N : ℕ) : Type where
  A : ∀ α, Matrix (Fin (N + 1)) (Fin (C.n α)) Γ(Z, C.B α)
  linv : ∀ α, ∃ A' : Matrix (Fin (C.n α)) (Fin (N + 1)) Γ(Z, C.B α), A' * A α = 1
  compat : ∀ (α β : C.A) (S : Type) [CommRing S] (z : Sp S ⟶ Z) (hα : ⊤ ≤ z ⁻¹ᵁ C.B α) (hβ : ⊤ ≤ z ⁻¹ᵁ C.B β),
    ∃ u : Sˣ, (A α).map (ev z _ hα) * C.tr α β z hα hβ = (u : S) • (A β).map (ev z _ hβ)

structure Line (f : Z' ⟶ Z) : Type 1 where
  J : Type
  B : J → Z'.Opens
  aff : ∀ β, IsAffineOpen (B β)
  cover : ∀ x : Z', ∃ β, x ∈ B β
  a : J → C.A
  le : ∀ β, B β ≤ f ⁻¹ᵁ C.B (a β)
  η : ∀ β, Fin (C.n (a β)) → Γ(Z', B β)
  unit : ∀ β, ∃ c, IsUnit (η β c)

variable {C} in

def Line.Carries {f : Z' ⟶ Z} (L : C.Line f) (w : Sp S ⟶ Z') (α : C.A) (h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α)
    (ξ : Fin (C.n α) → S) : Prop :=
  ∀ (β : L.J) (hw : ⊤ ≤ w ⁻¹ᵁ L.B β), ∃ u : Sˣ,
    (C.tr (L.a β) α (w ≫ f) (le_preimage_map f (L.le β) hw) h).mulVec ξ = fun i => (u : S) * ev w _ hw (L.η β i)

structure Sub (ch : Charts Z) (r : ℕ) : Type where
  α : ch.ι → C.A
  le : ∀ a, ⊤ ≤ ch.χ a ⁻¹ᵁ C.B (α a)
  M : ∀ a, Matrix (Fin (C.n (α a))) (Fin (r + 1)) (ch.R a)
  inj : ∀ (a : ch.ι) (K : Type) [Field K] (φ : ch.R a →+* K), Function.Injective ((M a).map φ).mulVec
  glue : ∀ (a a' : ch.ι) (K : Type) [Field K] (φ : ch.R a →+* K) (φ' : ch.R a' →+* K) (z : Sp K ⟶ Z),
    spMap φ ≫ ch.χ a = z → spMap φ' ≫ ch.χ a' = z → ∀ (h : ⊤ ≤ z ⁻¹ᵁ C.B (α a)) (h' : ⊤ ≤ z ⁻¹ᵁ C.B (α a')),
      ∃ P : Matrix (Fin (r + 1)) (Fin (r + 1)) K, C.tr (α a) (α a') z h h' * (M a').map φ' = (M a).map φ * P

variable {C} in

structure Sub.Closure {ch : Charts Z} {r : ℕ} (D : C.Sub ch r) {O : Type} [CommRing O] (s : Z ⟶ Sp O) : Type 1 where
  Z' : Scheme.{0}
  f : Z' ⟶ Z
  proj : IsProjOver (f ≫ s)
  normal : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z'
  flat : Flat (f ≫ s)
  L : C.Line f
  ch' : Charts Z'
  b : ch'.ι → ch.ι
  ρ : ∀ k, ch.R (b k) →+* ch'.R k
  smooth : ∀ k, Smooth (spMap (ρ k))
  sq : ∀ k, ch'.χ k ≫ f = spMap (ρ k) ≫ ch.χ (b k)
  P : ∀ k, Matrix (Fin (r + 1)) (Fin (r + 1)) (ch'.R k)
  P_unit : ∀ k, IsUnit (P k)
  carrier_eq : ch'.carrier = f ⁻¹' ch.carrier
  dense : Dense ch'.carrier
  car : ∀ (k : ch'.ι) (K : Type) [Field K] (ψ : ch'.R k →+* K) (w : Sp K ⟶ Z'), spMap ψ ≫ ch'.χ k = w →
    ∀ h, L.Carries w (D.α (b k)) h (((D.M (b k)).map (ψ.comp (ρ k))).mulVec fun i => ψ (P k i 0))
  bij : ∀ (a : ch.ι) (K : Type) [Field K] (φ : ch.R a →+* K) (v : Fin (r + 1) → K), v ≠ 0 →
    ∃! w : Sp K ⟶ Z', w ≫ f = spMap φ ≫ ch.χ a ∧ ∀ h, L.Carries w (D.α a) h (((D.M a).map φ).mulVec v)
  lift : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] (z : Sp R ⟶ Z) (α : C.A) (_ : ⊤ ≤ z ⁻¹ᵁ C.B α) (ξ : Fin (C.n α) → R), (∃ c, IsUnit (ξ c)) →
    ∀ y : Sp K ⟶ Z', y ≫ f = spMap (algebraMap R K) ≫ z → (∀ h, L.Carries y α h fun i => algebraMap R K (ξ i)) →
      ∃ z' : Sp R ⟶ Z', spMap (algebraMap R K) ≫ z' = y

end Coc

end Bundles

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Tan

variable {X : Scheme.{0}} {t : SAB H X} {S S' : Type} [CommRing S] [CommRing S']

variable (Dw t) in

abbrev TVecs (x : Sp S ⟶ X) : Type := ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → TanM x t.G

def up {x : Sp S ⟶ X} (u : TVecs Dw t x) : Vecs Dw t S := fun σ i => (tv (u σ i)).left

theorem exists_up {x : Sp S ⟶ X} {u : Vecs Dw t S} (h : ∀ σ i, IsTanAtG t x (u σ i)) :
    ∃ U : TVecs Dw t x, up U = u := ⟨fun σ i => tanOf (h σ i), rfl⟩

theorem up_injective {x : Sp S ⟶ X} {u u' : TVecs Dw t x} (h : up u = up u') : u = u' :=
  funext fun σ => funext fun i => tan_ext (congrFun (congrFun h σ) i)

theorem up_tanPull (φ : S →+* S') {x : Sp S ⟶ X} {x' : Sp S' ⟶ X} (e : spMap φ ≫ x = x') (u : TVecs Dw t x) :
    up (Dw := Dw) (fun σ i => tanPull φ e (u σ i)) = (up u).bc φ := rfl

theorem sameFlag_up_iff {ty : (E →+* ℂ) → Finset ℕ} {x : Sp S ⟶ X} (u u' : TVecs Dw t x) :
    SameFlag ty t x (up u) (up u') ↔ ∀ σ, ∀ k ∈ ty σ, initSpan S (u' σ) k ≤ initSpan S (u σ) k := by
  refine forall_congr' fun σ => forall_congr' fun k => forall_congr' fun _ => ⟨fun h => Submodule.span_le.2 ?_, fun h i hi => ?_⟩
  · rintro _ ⟨i, hi, rfl⟩
    obtain ⟨cf, h1, h2⟩ := h i hi
    exact mem_initSpan.2 ⟨cf, h1, ((isComb_iff (u σ) cf (u' σ i)).1 h2).symm⟩
  · obtain ⟨cf, h1, h2⟩ := mem_initSpan.1 (h (Submodule.subset_span ⟨i, hi, rfl⟩))
    exact ⟨cf, h1, (isComb_iff (u σ) cf (u' σ i)).2 h2.symm⟩

variable (t) in

def eig {l : Level H} {c : Coeff l} (f : c.F →+* S) (x : Sp S ⟶ X) (σ : E →+* ℂ) : Submodule S (TanM x t.G) where
  carrier := {v | ∀ a : 𝓞 E, ReciprocityTheory.ChartRestriction.G.PullbackSections.actR t.act a v = f (embK c σ a) • v}
  zero_mem' := fun a => by rw [map_zero, smul_zero]
  add_mem' := fun hu hv a => by rw [map_add, hu a, hv a, smul_add]
  smul_mem' := fun r v hv a => by rw [map_smul, hv a, smul_comm]

theorem mem_eig_iff {l : Level H} {c : Coeff l} (f : c.F →+* S) (x : Sp S ⟶ X) (σ : E →+* ℂ) (v : TanM x t.G) :
    v ∈ eig t f x σ ↔ ∀ a : 𝓞 E, (tv v).left ≫ (t.act.act a).left = spMap (epsMul (f (embK c σ a))) ≫ (tv v).left :=
  forall_congr' fun _ => ⟨fun h => congrArg (fun V => (tv V).left) h, fun h => tan_ext h⟩

theorem isFrame_up_iff {l : Level H} {c : Coeff l} (f : c.F →+* S) {x : Sp S ⟶ X} (u : TVecs Dw t x) :
    LocM.IsFrame t f x (up u) ↔ ∀ σ, LinearIndependent S (u σ) ∧ Submodule.span S (Set.range (u σ)) = eig t f x σ := by
  constructor
  · rintro ⟨h1, h2⟩ σ
    have hm : ∀ i, u σ i ∈ eig t f x σ := fun i => (mem_eig_iff f x σ _).2 (h1 σ i).2
    have h3 : ∀ w ∈ eig t f x σ, ∃! a : Fin (Dw.mult σ) → S, w = ∑ i, a i • u σ i := fun w hw =>
      (existsUnique_congr fun a => isComb_iff (u σ) a w).1 (h2 σ _ (isTan_tv w) ((mem_eig_iff f x σ w).1 hw))
    refine ⟨Fintype.linearIndependent_iff.2 fun a ha => congrFun ((h3 0 (Submodule.zero_mem _)).unique ha.symm
      (by simp : (0 : TanM x t.G) = ∑ i, (0 : Fin (Dw.mult σ) → S) i • u σ i)), le_antisymm ?_ fun w hw => ?_⟩
    · exact Submodule.span_le.2 (Set.range_subset_iff.2 hm)
    · obtain ⟨a, rfl, -⟩ := h3 w hw
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro h
    refine ⟨fun σ i => ⟨isTan_tv _, (mem_eig_iff f x σ _).1 ((h σ).2 ▸ Submodule.subset_span ⟨i, rfl⟩)⟩,
      fun σ w hw he => ?_⟩
    have hm : tanOf hw ∈ Submodule.span S (Set.range (u σ)) := (h σ).2 ▸ (mem_eig_iff f x σ _).2 he
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 hm
    refine (existsUnique_congr fun a => isComb_iff (u σ) a (tanOf hw)).2 ⟨a, ha.symm, fun b hb => funext ?_⟩
    exact Fintype.linearIndependent_iffₛ.1 (h σ).1 _ _ (hb.symm.trans ha.symm)

theorem exists_basis_tanPull (φ : S →+* S') {x : Sp S ⟶ X} {x' : Sp S' ⟶ X} (e : spMap φ ≫ x = x') {κ : Type}
    [Finite κ] (b : Module.Basis κ S (TanM x t.G)) :
    ∃ b' : Module.Basis κ S' (TanM x' t.G), ∀ i, b' i = tanPull φ e (b i) := by
  subst e
  have := Fintype.ofFinite κ
  let q := Fintype.equivFin κ
  have h0 : FrameBC.Full (t := t) b := fun n =>
    ⟨b.repr n, (b.sum_repr n).symm, fun a ha => by rw [ha]; exact (b.repr_sum_self a).symm⟩
  have h1 := FrameBC.full_equiv q (FrameBC.full_bc φ (FrameBC.full_equiv q.symm h0))
  simp only [Equiv.symm_apply_apply] at h1
  refine ⟨Module.Basis.mk (v := fun i => tanPull φ rfl (b i)) (Fintype.linearIndependent_iff.2 fun a ha => congrFun
    ((h1 0).unique ha.symm (by simp : (0 : TanM _ t.G) = ∑ i, (0 : κ → S') i • FrameBC.resM φ (b i))))
    fun w _ => ?_, fun i => Module.Basis.mk_apply _ _ i⟩
  obtain ⟨a, rfl, -⟩ := h1 w
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def basPull (φ : S →+* S') {x : Sp S ⟶ X} {x' : Sp S' ⟶ X} (e : spMap φ ≫ x = x') {κ : Type}
    [Finite κ] (b : Module.Basis κ S (TanM x t.G)) : Module.Basis κ S' (TanM x' t.G) :=
  (exists_basis_tanPull φ e b).choose

theorem basPull_apply (φ : S →+* S') {x : Sp S ⟶ X} {x' : Sp S' ⟶ X} (e : spMap φ ≫ x = x') {κ : Type}
    [Finite κ] (b : Module.Basis κ S (TanM x t.G)) (i : κ) : basPull φ e b i = tanPull φ e (b i) :=
  (exists_basis_tanPull φ e b).choose_spec i

theorem basPull_repr (φ : S →+* S') {x : Sp S ⟶ X} {x' : Sp S' ⟶ X} (e : spMap φ ≫ x = x') {κ : Type}
    [Finite κ] (b : Module.Basis κ S (TanM x t.G)) (v : TanM x t.G) (i : κ) :
    (basPull φ e b).repr (tanPull φ e v) i = φ (b.repr v i) := by
  have := Fintype.ofFinite κ
  conv_lhs => rw [← b.sum_repr v, map_sum]
  simp only [map_smulₛₗ, ← basPull_apply]
  exact congrFun ((basPull φ e b).repr_sum_self _) i

theorem tanPull_tanPull {S'' : Type} [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'') {x : Sp S ⟶ X} {x' : Sp S' ⟶ X}
    {x'' : Sp S'' ⟶ X} (e : spMap φ ≫ x = x') (e' : spMap ψ ≫ x' = x'') (e'' : spMap (ψ.comp φ) ≫ x = x'')
    (v : TanM x t.G) : tanPull ψ e' (tanPull φ e v) = tanPull (ψ.comp φ) e'' v := by
  apply tan_ext
  rw [FlagMod.tanPull_left, FlagMod.tanPull_left, FlagMod.tanPull_left, FlagMod.dualMap_comp, ← spMap_comp',
    Category.assoc]

variable {Z : Scheme.{0}} {π : Z ⟶ X} {U : Z.Opens} {hU : IsAffineOpen U} {κ : Type} [Finite κ]

def basAt (b : Module.Basis κ Γ(Z, U) (TanM (tau hU ≫ π) t.G)) (w : Sp S ⟶ Z) (hw : ⊤ ≤ w ⁻¹ᵁ U) :
    Module.Basis κ S (TanM (w ≫ π) t.G) :=
  basPull (ev w U hw) (by rw [← Category.assoc, tau, spMap_ev]) b

theorem basAt_left (b : Module.Basis κ Γ(Z, U) (TanM (tau hU ≫ π) t.G)) (w : Sp S ⟶ Z) (hw : ⊤ ≤ w ⁻¹ᵁ U) (i : κ) :
    (tv (basAt b w hw i)).left = spMap (dualMap (ev w U hw)) ≫ (tv (b i)).left := by
  rw [basAt, basPull_apply]; rfl

theorem tanPull_basAt (b : Module.Basis κ Γ(Z, U) (TanM (tau hU ≫ π) t.G)) (φ : S →+* S') (w : Sp S ⟶ Z)
    (hw : ⊤ ≤ w ⁻¹ᵁ U) {w' : Sp S' ⟶ Z} (e : spMap φ ≫ w = w') (hw' : ⊤ ≤ w' ⁻¹ᵁ U) (e' : spMap φ ≫ w ≫ π = w' ≫ π)
    (i : κ) : tanPull φ e' (basAt b w hw i) = basAt b w' hw' i := by
  subst e
  apply tan_ext
  rw [FlagMod.tanPull_left, basAt_left, basAt_left, ev_spMap φ w U hw, FlagMod.dualMap_comp, ← spMap_comp']
  exact (Category.assoc _ _ _).symm

theorem basAt_repr (b : Module.Basis κ Γ(Z, U) (TanM (tau hU ≫ π) t.G)) (φ : S →+* S') (w : Sp S ⟶ Z)
    (hw : ⊤ ≤ w ⁻¹ᵁ U) {w' : Sp S' ⟶ Z} (e : spMap φ ≫ w = w') (hw' : ⊤ ≤ w' ⁻¹ᵁ U) (e' : spMap φ ≫ w ≫ π = w' ≫ π)
    (v : TanM (w ≫ π) t.G) (i : κ) : (basAt b w' hw').repr (tanPull φ e' v) i = φ ((basAt b w hw).repr v i) := by
  have : basAt b w' hw' = basPull φ e' (basAt b w hw) :=
    Module.Basis.eq_of_apply_eq fun i => by rw [basPull_apply, tanPull_basAt b φ w hw e hw']
  rw [this, basPull_repr]

end Tan

section Atlas

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F}

structure Geo (M : Model Xo c V.subtype) {X : Scheme.{0}} (π : X ⟶ M.X) : Prop where
  proj : IsProjOver (π ≫ M.s)
  normal : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X
  flat : Flat (π ≫ M.s)
  dense : Dense (π ⁻¹' Set.range M.j)

structure PreAtlas (M : Model Xo c V.subtype) (X : Scheme.{0}) : Type 1 where
  ch : Charts X
  alg : ∀ a, c.F →+* ch.R a
  fr : ∀ a, Vecs Dw M.t (ch.R a)

def PreAtlas.FlagAt {M : Model Xo c V.subtype} {X : Scheme.{0}} (A : PreAtlas M X) (π : X ⟶ M.X)
    (ty : (E →+* ℂ) → Finset ℕ) {k : Type} [Field k] (w : Sp k ⟶ X) (u : Vecs Dw M.t k) : Prop :=
  ∃ (a : A.ch.ι) (φ : A.ch.R a →+* k), spMap φ ≫ A.ch.χ a = w ∧
    LocM.IsFrame M.t (φ.comp (A.alg a)) (w ≫ π) u ∧ SameFlag ty M.t (w ≫ π) ((A.fr a).bc φ) u

structure Atlas (M : Model Xo c V.subtype) {X : Scheme.{0}} (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) : Type 1
    extends PreAtlas M X where
  cover : ch.carrier = π ⁻¹' Set.range M.j
  alg_s : ∀ a, ch.χ a ≫ π ≫ M.s = spMap ((alg a).comp V.subtype)
  smooth : ∀ a, Smooth (ch.χ a ≫ π)
  frame : ∀ a, LocM.IsFrame M.t (alg a) (ch.χ a ≫ π) (fr a)
  glue : ∀ (k : Type) [Field k] (a a' : ch.ι) (φ : ch.R a →+* k) (φ' : ch.R a' →+* k),
    spMap φ ≫ ch.χ a = spMap φ' ≫ ch.χ a' → SameFlag ty M.t (spMap φ ≫ ch.χ a ≫ π) ((fr a).bc φ) ((fr a').bc φ')
  bij : ∀ (k : Type) [Field k] (f : c.F →+* k) (y : Sp k ⟶ Xo.XF c), y ≫ pullback.snd _ _ = spMap f →
    ∀ u, LocM.IsFrame M.t f (y ≫ M.j) u → ∃! w : Sp k ⟶ X, w ≫ π = y ≫ M.j ∧ toPreAtlas.FlagAt π ty w u

variable {M : Model Xo c V.subtype} {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ}

abbrev Atlas.FlagAt (A : Atlas M π ty) {k : Type} [Field k] (w : Sp k ⟶ X) (u : Vecs Dw M.t k) : Prop :=
  A.toPreAtlas.FlagAt π ty w u

theorem initSpan_eq_of_le {K N : Type} [Field K] [AddCommGroup N] [Module K N] {m : ℕ} {u u' : Fin m → N}
    (hu : LinearIndependent K u) (hu' : LinearIndependent K u') {k : ℕ} (h : initSpan K u' k ≤ initSpan K u k) :
    initSpan K u' k = initSpan K u k := by
  have key : ∀ {v : Fin m → N}, LinearIndependent K v →
      Module.finrank K (initSpan K v k) = Fintype.card {j : Fin m // (j : ℕ) < k} := fun {v} hv => by
    have := finrank_span_eq_card (hv.comp (fun j : {j : Fin m // (j : ℕ) < k} => j.1) Subtype.val_injective)
    rw [← this, initSpan, Set.range_comp, Subtype.range_coe_subtype]
  have : FiniteDimensional K (initSpan K u k) := FiniteDimensional.span_of_finite K (Set.toFinite _)
  exact Submodule.eq_of_le_of_finrank_eq h (by rw [key hu, key hu'])

theorem Charts.exists_fac (ch : Charts X) {S : Type} [CommRing S] [IsLocalRing S] (w : Sp S ⟶ X)
    (h : w (IsLocalRing.closedPoint S) ∈ ch.carrier) : ∃ (a : ch.ι) (φ : ch.R a →+* S), spMap φ ≫ ch.χ a = w := by
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 h
  have h1 : ⊤ ≤ w ⁻¹ᵁ (ch.χ a).opensRange :=
    ((IsLocalRing.closed_point_mem_iff (U := w ⁻¹ᵁ (ch.χ a).opensRange)).1 ha).ge
  have h' : Set.range w ⊆ Set.range (ch.χ a) := by
    rintro _ ⟨x, rfl⟩
    exact h1 (Set.mem_univ x)
  refine ⟨a, (Spec.preimage (IsOpenImmersion.lift (ch.χ a) w h')).hom, ?_⟩
  show Spec.map (Spec.preimage _) ≫ _ = _
  rw [Spec.map_preimage]
  exact IsOpenImmersion.lift_fac _ _ _

theorem Charts.range_subset (ch : Charts X) {S : Type} [CommRing S] {a : ch.ι} {φ : ch.R a →+* S} {w : Sp S ⟶ X}
    (e : spMap φ ≫ ch.χ a = w) : Set.range w ⊆ ch.carrier := by
  rintro _ ⟨x, rfl⟩
  exact Set.mem_iUnion.2 ⟨a, spMap φ x, by rw [← e]; rfl⟩

namespace Atlas

variable (A : Atlas M π ty) {S : Type} [CommRing S] {K : Type} [Field K]

theorem affineOpenChart_comp_structure_eq_spMap {a : A.ch.ι} {φ : A.ch.R a →+* S} {w : Sp S ⟶ X} (e : spMap φ ≫ A.ch.χ a = w) :
    w ≫ π ≫ M.s = spMap ((φ.comp (A.alg a)).comp V.subtype) := by
  rw [← e, Category.assoc, A.alg_s, spMap_comp', RingHom.comp_assoc]

theorem alg_eq {a a' : A.ch.ι} {φ : A.ch.R a →+* S} {φ' : A.ch.R a' →+* S} {w : Sp S ⟶ X}
    (e : spMap φ ≫ A.ch.χ a = w) (e' : spMap φ' ≫ A.ch.χ a' = w) : φ.comp (A.alg a) = φ'.comp (A.alg a') :=
  IsLocalization.ringHom_ext (nonZeroDivisors V)
    (congrArg CommRingCat.Hom.hom (Spec.map_injective ((A.affineOpenChart_comp_structure_eq_spMap e).symm.trans (A.affineOpenChart_comp_structure_eq_spMap e'))))

theorem isFrame_bc {a : A.ch.ι} {φ : A.ch.R a →+* S} {w : Sp S ⟶ X} (e : spMap φ ≫ A.ch.χ a = w) :
    LocM.IsFrame M.t (φ.comp (A.alg a)) (w ≫ π) ((A.fr a).bc φ) := by
  rw [← e, Category.assoc]
  exact GlobalTheory.LocM.isFrame_bc E H Dw l c _ M.t _ _ _ φ _ _ (A.frame a)

theorem exists_up_fr {a : A.ch.ι} {φ : A.ch.R a →+* S} {w : Sp S ⟶ X} (e : spMap φ ≫ A.ch.χ a = w) :
    ∃ u : TVecs Dw M.t (w ≫ π), up u = (A.fr a).bc φ := exists_up fun σ i => ((A.isFrame_bc e).1 σ i).1

theorem flagAt_fr {a : A.ch.ι} {φ : A.ch.R a →+* K} {w : Sp K ⟶ X} (e : spMap φ ≫ A.ch.χ a = w) :
    A.FlagAt w ((A.fr a).bc φ) :=
  ⟨a, φ, e, A.isFrame_bc e, SameFlag.refl fun σ i => ((A.isFrame_bc e).1 σ i).1⟩

theorem FlagAt.exists_up {A : Atlas M π ty} {w : Sp K ⟶ X} {u : Vecs Dw M.t K} (h : A.FlagAt w u) :
    ∃ U : TVecs Dw M.t (w ≫ π), up U = u := by
  obtain ⟨a, φ, -, hf, -⟩ := h
  exact DRFlag.exists_up fun σ i => (hf.1 σ i).1

theorem flagAt_iff {a : A.ch.ι} {φ : A.ch.R a →+* K} {w : Sp K ⟶ X} (e : spMap φ ≫ A.ch.χ a = w)
    {u₀ : TVecs Dw M.t (w ≫ π)} (h₀ : up u₀ = (A.fr a).bc φ) (u : TVecs Dw M.t (w ≫ π)) :
    A.FlagAt w (up u) ↔ LocM.IsFrame M.t (φ.comp (A.alg a)) (w ≫ π) (up u) ∧
      ∀ σ, ∀ j ∈ ty σ, initSpan K (u σ) j = initSpan K (u₀ σ) j := by
  refine ⟨fun ⟨a', φ', e', hf, hs⟩ => ?_, fun ⟨hf, hs⟩ => ⟨a, φ, e, hf, ?_⟩⟩
  · obtain ⟨u₁, h₁⟩ := A.exists_up_fr e'
    have g := A.glue K a a' φ φ' (e.trans e'.symm)
    rw [← Category.assoc, e, ← h₀, ← h₁, sameFlag_up_iff] at g
    rw [← h₁, sameFlag_up_iff] at hs
    rw [← A.alg_eq e e'] at hf
    have f₀ := A.isFrame_bc e
    rw [← h₀] at f₀
    exact ⟨hf, fun σ j hj => initSpan_eq_of_le ((isFrame_up_iff _ _).1 f₀ σ).1 ((isFrame_up_iff _ _).1 hf σ).1
      ((hs σ j hj).trans (g σ j hj))⟩
  · rw [← h₀, sameFlag_up_iff]
    exact fun σ j hj => (hs σ j hj).le

theorem FlagAt.initSpan_eq {A : Atlas M π ty} {w : Sp K ⟶ X} {u u' : TVecs Dw M.t (w ≫ π)} (h : A.FlagAt w (up u))
    (h' : A.FlagAt w (up u')) (σ : E →+* ℂ) {j : ℕ} (hj : j ∈ ty σ) : initSpan K (u σ) j = initSpan K (u' σ) j := by
  obtain ⟨a, φ, e, -⟩ := id h
  obtain ⟨u₀, h₀⟩ := A.exists_up_fr e
  rw [((A.flagAt_iff e h₀ u).1 h).2 σ j hj, ((A.flagAt_iff e h₀ u').1 h').2 σ j hj]

end Atlas

namespace Atlas

variable (A : Atlas M π ty) {S : Type} [CommRing S] {K : Type} [Field K]

theorem exists_xF {a : A.ch.ι} {φ : A.ch.R a →+* S} {w : Sp S ⟶ X} (e : spMap φ ≫ A.ch.χ a = w) :
    ∃ y : Sp S ⟶ Xo.XF c, y ≫ M.j = w ≫ π ∧ y ≫ pullback.snd _ _ = spMap (φ.comp (A.alg a)) := by
  have := M.jQ_open
  have hp : IsPreimmersion (spMap V.subtype) := IsPreimmersion.of_isLocalization (R := V) (S := c.F) (nonZeroDivisors V)
  have : IsPreimmersion (pullback.fst M.s (spMap V.subtype)) := inferInstance
  let y' : Sp S ⟶ pullback M.s (spMap V.subtype) := pullback.lift (w ≫ π) (spMap (φ.comp (A.alg a)))
    (by rw [Category.assoc, A.affineOpenChart_comp_structure_eq_spMap e, spMap_comp'])
  have h1 : y' ≫ pullback.fst _ _ = w ≫ π := pullback.lift_fst _ _ _
  have hr : Set.range y' ⊆ Set.range M.jQ := by
    rintro _ ⟨x, rfl⟩
    have hx := A.ch.range_subset e ⟨x, rfl⟩
    rw [A.cover] at hx
    obtain ⟨q, hq⟩ := hx
    refine ⟨q, (pullback.fst M.s (spMap V.subtype)).isEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h1, Scheme.Hom.comp_apply w]
    exact hq
  refine ⟨IsOpenImmersion.lift M.jQ y' hr, ?_, ?_⟩
  · rw [Model.j, IsOpenImmersion.lift_fac_assoc, h1]
  · rw [← M.jQ_over, IsOpenImmersion.lift_fac_assoc]
    exact pullback.lift_snd _ _ _

theorem FlagAt.point_eq {A : Atlas M π ty} {w w' : Sp K ⟶ X} {u : Vecs Dw M.t K} (h : A.FlagAt w u) (h' : A.FlagAt w' u)
    (e : w ≫ π = w' ≫ π) : w = w' := by
  obtain ⟨a, φ, ea, hf, -⟩ := id h
  obtain ⟨y, hy, hy'⟩ := A.exists_xF ea
  exact (A.bij K _ y hy' u (hy ▸ hf)).unique ⟨hy.symm, h⟩ ⟨e.symm.trans hy.symm, h'⟩

theorem FlagAt.exists_point {A : Atlas M π ty} {w : Sp K ⟶ X} {u : Vecs Dw M.t K} (h : A.FlagAt w u) {X' : Scheme.{0}}
    {π' : X' ⟶ M.X} {ty' : (E →+* ℂ) → Finset ℕ} (A' : Atlas M π' ty') :
    ∃ w' : Sp K ⟶ X', w' ≫ π' = w ≫ π ∧ A'.FlagAt w' u := by
  obtain ⟨a, φ, ea, hf, -⟩ := h
  obtain ⟨y, hy, hy'⟩ := A.exists_xF ea
  obtain ⟨w', hw', -⟩ := A'.bij K _ y hy' u (hy ▸ hf)
  exact ⟨w', hw'.1.trans hy, hw'.2⟩

end Atlas

def IntOn (A : Atlas M π ty) (σ : E →+* ℂ) (k : ℕ) {U : X.Opens} (hU : IsAffineOpen U) {m : ℕ}
    (b : Module.Basis (Fin k ⊕ Fin m) Γ(X, U) (TanM (tau hU ≫ π) M.t.G)) : Prop :=
  ∀ (K : Type) [Field K] (w : Sp K ⟶ X) (hw : ⊤ ≤ w ⁻¹ᵁ U) (u : TVecs Dw M.t (w ≫ π)), A.FlagAt w (up u) →
    ∀ j ≤ k, initSpan K (u σ) j = initSpan K (fun i : Fin k => basAt b w hw (.inl i)) j

def IntStep (A : Atlas M π ty) (σ : E →+* ℂ) (k : ℕ) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (hU : IsAffineOpen U) (m : ℕ)
    (b : Module.Basis (Fin k ⊕ Fin m) Γ(X, U) (TanM (tau hU ≫ π) M.t.G)), x ∈ U ∧ IntOn A σ k hU b

def crd {k m : ℕ} {U : X.Opens} {hU : IsAffineOpen U}
    (b : Module.Basis (Fin k ⊕ Fin m) Γ(X, U) (TanM (tau hU ≫ π) M.t.G)) {S : Type} [CommRing S] (z : Sp S ⟶ X)
    (h : ⊤ ≤ z ⁻¹ᵁ U) (v : TanM (z ≫ π) M.t.G) : Fin m → S := fun j => (basAt b z h).repr v (.inr j)

structure Adapted (A : Atlas M π ty) (σ : E →+* ℂ) (k : ℕ) : Type 1 where
  C : Coc X
  b : ∀ α, Module.Basis (Fin k ⊕ Fin (C.n α)) Γ(X, C.B α) (TanM (tau (C.aff α) ≫ π) M.t.G)
  int : ∀ α, IntOn A σ k (C.aff α) (b α)
  coord : ∀ (α β : C.A) (S : Type) [CommRing S] (z : Sp S ⟶ X) (hα : ⊤ ≤ z ⁻¹ᵁ C.B α) (hβ : ⊤ ≤ z ⁻¹ᵁ C.B β)
    (v : TanM (z ≫ π) M.t.G), (C.tr α β z hα hβ).mulVec (crd (b β) z hβ v) = crd (b α) z hα v

variable {A : Atlas M π ty} {σ : E →+* ℂ} {k r : ℕ}

def IsFrSub (D : Adapted A σ k) (Sb : D.C.Sub A.ch r) (hj : k + r + 1 ≤ Dw.mult σ) : Prop :=
  ∀ (a : A.ch.ι) (S : Type) [CommRing S] (φ : A.ch.R a →+* S) (z : Sp S ⟶ X), spMap φ ≫ A.ch.χ a = z →
    ∀ (h : ⊤ ≤ z ⁻¹ᵁ D.C.B (Sb.α a)) (u : TVecs Dw M.t (z ≫ π)), up u = (A.fr a).bc φ →
      ∀ i : Fin (r + 1), (fun j => φ (Sb.M a j i)) = crd (D.b (Sb.α a)) z h (u σ ⟨k + i, by omega⟩)

def StepRel (D : Adapted A σ k) (hk : k < Dw.mult σ) {X' : Scheme.{0}} {f : X' ⟶ X} (L : D.C.Line f)
    {ty' : (E →+* ℂ) → Finset ℕ} (A' : Atlas M (f ≫ π) ty') : Prop :=
  ∀ (K : Type) [Field K] (w : Sp K ⟶ X') (u : TVecs Dw M.t ((w ≫ f) ≫ π)),
    A'.FlagAt w (up u) ↔ A.FlagAt (w ≫ f) (up u) ∧ ∀ α h, L.Carries w α h (crd (D.b α) (w ≫ f) h (u σ ⟨k, hk⟩))

end Atlas

section Maps

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

def atlasOf (Z : Mdl Y i₀) : Atlas (Y Z.i) Z.π Z.ty where
  ch := { ι := Fin Z.m, R := fun a => Γ(Z.X, (Z.U a).1), χ := Z.chart, opn := fun a => (Z.U a).2.isOpenImmersion_fromSpec }
  alg := Z.alg
  fr := Z.fr
  cover := by
    refine Eq.trans (Set.iUnion_congr fun a => ?_) Z.cover
    exact (Z.U a).2.range_fromSpec
  alg_s a := by rw [Z.π_s]; exact Z.alg_s a
  smooth := Z.smooth
  frame := Z.frame
  glue := Z.glue
  bij := Z.bij

theorem atlasOf_flagAt (Z : Mdl Y i₀) {k : Type} [Field k] (w : Sp k ⟶ Z.X) (u : Vecs Dw (Y Z.i).t k) :
    (atlasOf Z).FlagAt w u ↔ Z.FlagAt w u := Iff.rfl

theorem geoOf (Z : Mdl Y i₀) : Geo (Y Z.i) Z.π where
  proj := ⟨Z.n, Z.I.subschemeι, inferInstance, Z.π_s.symm⟩
  normal := have := Z.normal; GlobalTheory.IsNormalScheme.pred _
  flat := by rw [Z.π_s]; exact Z.flat
  dense := Z.dense

variable {i : Idx H p} {X : Scheme.{0}} {π : X ⟶ (Y i).X} {ty : (E →+* ℂ) → Finset ℕ}

def NatTo (Z : Mdl Y i₀) (A : Atlas (Y i) π ty) {k : Type} [Field k] (w₁ : Sp k ⟶ Z.X) (w₂ : Sp k ⟶ X) : Prop :=
  ∃ (τ : (Y Z.i).X ⟶ (Y i).X) (mu : SABMap (Y Z.i).t (Y i).t τ) (u : Vecs Dw (Y Z.i).t k),
    IsTrans i Z.i τ mu ∧ w₂ ≫ π = w₁ ≫ Z.π ≫ τ ∧ Z.FlagAt w₁ u ∧ A.FlagAt w₂ (fun σ j => u σ j ≫ mu.φ)

def MapsTo (Z : Mdl Y i₀) (A : Atlas (Y i) π ty) (g : Z.X ⟶ X) : Prop :=
  ∀ (k : Type) [Field k] (w : Sp k ⟶ Z.X), Set.range w ⊆ Z.opn → NatTo Z A w (w ≫ g)

def LocMaps (Z : Mdl Y i₀) (A : Atlas (Y i) π ty) : Prop :=
  ∀ (K : Type) [Field K] (w : Sp K ⟶ Z.X), Set.range w ⊆ Z.opn → ∃ y : Sp K ⟶ X, NatTo Z A w y ∧
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R] [Algebra R K] [IsFractionRing R K]
      (z : Sp R ⟶ Z.X), spMap (algebraMap R K) ≫ z = w → ∃ z' : Sp R ⟶ X, spMap (algebraMap R K) ≫ z' = y

theorem isMap_iff (Z₁ Z₂ : Mdl Y i₀) (g : Z₁.X ⟶ Z₂.X) : IsMap Z₁ Z₂ g ↔ LocM.Corr Z₁ Z₂ ∧ MapsTo Z₁ (atlasOf Z₂) g :=
  Iff.rfl

end Maps

end GlobalTheory.DRFlag
