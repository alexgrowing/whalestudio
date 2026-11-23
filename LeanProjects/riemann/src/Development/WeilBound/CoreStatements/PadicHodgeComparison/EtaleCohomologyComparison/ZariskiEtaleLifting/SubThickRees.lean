import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistable
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.B

structure Fn (O : Type) [CommRing O] : Type 1 where
  Pt : CommRingCat.{0} ⥤ Type
  Ov : ∀ {B : CommRingCat.{0}}, Pt.obj B → (O →+* B) → Prop
  ov_map : ∀ {B B' : CommRingCat.{0}} (φ : B ⟶ B') {y : Pt.obj B} {f : O →+* B}, Ov y f → Ov (Pt.map φ y) (φ.hom.comp f)
  ov_uniq : ∀ {B : CommRingCat.{0}} {y : Pt.obj B} {f f' : O →+* B}, Ov y f → Ov y f' → f = f'

variable {O : Type} [CommRing O]

def schFn {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) : Fn O where
  Pt := { obj := fun B => Spec B ⟶ X
          map := fun φ => TypeCat.ofHom fun y => Spec.map φ ≫ y
          map_id := fun B => by ext y; simp
          map_comp := fun f g => by ext y; simp }
  Ov y f := y ≫ q = Spec.map (CommRingCat.ofHom f)
  ov_map φ y f h := by
    change (Spec.map φ ≫ y) ≫ q = _
    rw [Category.assoc, h, ← Spec.map_comp]; rfl
  ov_uniq h h' := congrArg CommRingCat.Hom.hom (Spec.map_injective (h.symm.trans h'))

namespace Fn

variable (F : Fn O)

def ptK {k : Type} [CommRing k] (κ : O →+* k) : CommRingCat.{0} ⥤ Type where
  obj B := {z : (k →+* B) × F.Pt.obj B // F.Ov z.2 (z.1.comp κ)}
  map {B B'} φ := TypeCat.ofHom fun z => ⟨(φ.hom.comp z.1.1, F.Pt.map φ z.1.2), F.ov_map φ z.2⟩
  map_id B := by
    ext z
    · rfl
    · exact congrFun (congrArg (fun t => (ConcreteCategory.hom t : _ → _)) (F.Pt.map_id B)) z.1.2
  map_comp f g := by
    ext z
    · rfl
    · exact congrFun (congrArg (fun t => (ConcreteCategory.hom t : _ → _)) (F.Pt.map_comp f g)) z.1.2

def cr (b : Base) (ht : b.t = 1) (κ : O →+* b.R ⧸ b.I) : b.Fun where
  ι := Empty
  A := Unit
  Pt := F.ptK κ
  str y := y.1.1
  str_map _ _ := rfl
  In _ _ _ := True
  in_map _ _ _ := trivial
  f _ i := i.elim
  f_map i := i.elim
  g _ _ i := i.elim
  g_map i := i.elim
  f_eq i := i.elim
  g_self i := i.elim
  g_comp i := i.elim
  prod_f {_ _ y} _ := by simp [ht]
  prod_g _ _ := by simp

structure Sub (F : Fn O) where
  In : ∀ {B : CommRingCat.{0}}, F.Pt.obj B → Prop
  in_map : ∀ {B B' : CommRingCat.{0}} (φ : B ⟶ B') {y : F.Pt.obj B}, In y → In (F.Pt.map φ y)

variable {F} in

def Sub.fn (V : F.Sub) : Fn O where
  Pt := { obj := fun B => {y : F.Pt.obj B // V.In y}
          map := fun φ => TypeCat.ofHom fun y => ⟨F.Pt.map φ y.1, V.in_map φ y.2⟩
          map_id := fun B => by
            ext y
            exact congrFun (congrArg (fun t => (ConcreteCategory.hom t : _ → _)) (F.Pt.map_id B)) y.1
          map_comp := fun f g => by
            ext y
            exact congrFun (congrArg (fun t => (ConcreteCategory.hom t : _ → _)) (F.Pt.map_comp f g)) y.1 }
  Ov y f := F.Ov y.1 f
  ov_map φ _ _ h := F.ov_map φ h
  ov_uniq h h' := F.ov_uniq h h'

variable {F} in

def Sub.inter {A : Type} (V : A → F.Sub) (S : Set A) : F.Sub :=
  ⟨fun y => ∀ α ∈ S, (V α).In y, fun φ _ h α hα => (V α).in_map φ (h α hα)⟩

structure Small (d : ℕ) : Type 1 where
  R : Type
  [ring : CommRing R]
  a : O →+* R
  T : Fin d → Rˣ
  et : (MvPolynomial.eval₂Hom a fun k => (T k : R)).Etale
  y₀ : F.Pt.obj (CommRingCat.of R)
  ov : F.Ov y₀ a
  univ : ∀ (B : CommRingCat.{0}) (y : F.Pt.obj B) (f : O →+* B), F.Ov y f →
    ∃! g : R →+* B, F.Pt.map (CommRingCat.ofHom g) y₀ = y

attribute [instance] Small.ring

structure Atlas (d : ℕ) : Type 1 where
  A : Type
  fin : Finite A
  V : A → F.Sub
  cov : ∀ (B : CommRingCat.{0}) (y : F.Pt.obj B), ∃ (m : ℕ) (s : Fin m → B), Ideal.span (Set.range s) = ⊤ ∧
    ∀ k (B' : CommRingCat.{0}) (φ : B ⟶ B'), IsUnit (φ.hom (s k)) → ∃ α, (V α).In (F.Pt.map φ y)
  jac : ∀ α (B B' : CommRingCat.{0}) (φ : B ⟶ B') (y : F.Pt.obj B), Function.Surjective φ.hom →
    RingHom.ker φ.hom ≤ (⊥ : Ideal B).jacobson → (V α).In (F.Pt.map φ y) → (V α).In y
  small : ∀ S : Set A, S.Nonempty → ∃ d' ≤ d, Nonempty ((Sub.inter V S).fn.Small d')

end Fn

structure Lift {R : Type} [CommRing R] (a : O →+* R) {d : ℕ} (T : Fin d → R) (Λ : Type) [CommRing Λ] (I : Ideal Λ)
    (κ : O →+* Λ ⧸ I) : Type 1 where
  D : Type
  [ring : CommRing D]
  i : Λ →+* D
  t : Fin d → D
  et : (MvPolynomial.eval₂Hom i t).Etale
  j : R →+* D ⧸ I.map i
  hj : ∀ o x, Ideal.Quotient.mk I x = κ o → j (a o) = Ideal.Quotient.mk _ (i x)
  hT : ∀ k, j (T k) = Ideal.Quotient.mk _ (t k)
  univ : ∀ (B : Type) [CommRing B] (h : Λ →+* B) (g : R →+* B), (∀ x ∈ I, h x = 0) →
    (∀ o x, Ideal.Quotient.mk I x = κ o → g (a o) = h x) →
    ∃! f : D →+* B, f.comp i = h ∧ ∀ r z, Ideal.Quotient.mk _ z = j r → f z = g r

attribute [instance] Lift.ring

def EtLift {B : Type} [CommRing B] (J : Ideal B) : Prop :=
  ∀ (P E : Type) [CommRing P] [CommRing E] (ψ : P →+* E), ψ.Etale → ∀ (f : P →+* B) (g : E →+* B ⧸ J),
    g.comp ψ = (Ideal.Quotient.mk J).comp f → ∃! h : E →+* B, h.comp ψ = f ∧ (Ideal.Quotient.mk J).comp h = g

structure RootExt (p : ℕ) (D : Type) [CommRing D] {d : ℕ} (t : Fin d → D) : Type 1 where
  E : Type
  [ring : CommRing E]
  [alg : Algebra D E]
  r : Fin d → ℕ → E
  r_zero : ∀ k, r k 0 = algebraMap D E (t k)
  r_succ : ∀ k m, r k (m + 1) ^ p = r k m
  univ : ∀ (B : Type) [CommRing B] (f : D →+* B) (c : Fin d → ℕ → B), (∀ k, c k 0 = f (t k)) →
    (∀ k m, c k (m + 1) ^ p = c k m) → ∃! g : E →+* B, g.comp (algebraMap D E) = f ∧ ∀ k m, g (r k m) = c k m
  ι : Type
  b : Module.Basis ι D E
  a₀ : ι
  b_a₀ : b a₀ = 1
  mono : ∀ a, a ≠ a₀ → ∃ (m : ℕ) (c : Fin d → ℕ), b a = ∏ k, r k m ^ c k ∧ ∃ k, ¬ p ^ m ∣ c k

attribute [instance] RootExt.ring RootExt.alg

def Raises {Λ : Type} [CommRing Λ] (I : ℕ → Ideal Λ) (ξ : Λ) : Prop := ∀ r, ∀ x ∈ I r, ξ * x ∈ I (r + 1)

def Slow (ρ : ℕ → ℕ) : Prop := ρ 0 = 0 ∧ ∀ r, ρ (r + 1) ≤ ρ r + 1

section Thick

variable {b : Base} (L : b.Fun)

theorem pdPow_map {T T' : Thick L} (φ : T ⟶ T') (r : ℕ) {x : T.B} (hx : x ∈ T.pdPow r) : φ.φ x ∈ T'.pdPow r := by
  refine (show T.pdPow r ≤ (T'.pdPow r).comap φ.φ from Ideal.span_le.2 ?_) hx
  rintro _ ⟨l, hl, hr, rfl⟩
  refine Ideal.subset_span ⟨l.map fun q => (q.1, φ.φ q.2), ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    exact φ.hle (hl q' hq')
  · simpa [List.map_map, Function.comp_def] using hr
  · rw [map_list_prod, List.map_map, List.map_map]
    congr 1
    exact List.map_congr_left fun q hq => (φ.dp.2 q.2 (hl q hq)).symm

theorem mul_pdPow (T : Thick L) (r : ℕ) {z x : T.B} (hz : z ∈ T.J) (hx : x ∈ T.pdPow r) : z * x ∈ T.pdPow (r + 1) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, hr, rfl⟩ := hx
    refine Ideal.subset_span ⟨(1, z) :: l, ?_, ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      exacts [hz, hl q hq]
    · simp only [List.map_cons, List.sum_cons]; omega
    · simp [T.δ.dpow_one hz]
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ hx

variable {Λ : Type} [CommRing Λ] (c : Λ →+* b.R)

def OA : Thick L ⥤ CommAlgCat.{0} Λ where
  obj T := letI := (T.i.comp c).toAlgebra; CommAlgCat.of Λ T.B
  map {T T'} f :=
    letI := (T.i.comp c).toAlgebra; letI := (T'.i.comp c).toAlgebra
    CommAlgCat.ofHom ⟨f.φ, fun r => f.comm (c r)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev OM : Thick L ⥤ ModuleCat.{0} Λ := CH.modF (OA L c)

def pdS (r : ℕ) : CH.SubF (OM L c) where
  S T := { carrier := {x | (show T.B from x) ∈ T.pdPow r}
           add_mem' := fun hx hy => (T.pdPow r).add_mem hx hy
           zero_mem' := (T.pdPow r).zero_mem
           smul_mem' := fun a _ hx => (T.pdPow r).mul_mem_left (T.i (c a)) hx }
  map_mem φ _ hx := pdPow_map L φ r hx

def pdFlt (ρ : ℕ → ℕ) (hρ : Slow ρ) (μ : Λ) (hμ : c μ ∈ b.I) : Flt (OM L c) where
  S r := pdS L c (ρ r)
  μ := μ
  mul r T x hx := T.pdPow_anti (hρ.2 r) (mul_pdPow L T _ (T.i_mem hμ) hx)

theorem pdPow_eq_fil (T : Thick L) (r : ℕ) : T.pdPow r = GlobalTheory.PDA.fil T.δ r := rfl

variable {L c} in

def omMor {b' : Base} {L' : b'.Fun} {σ : b.R →+* b'.R} (m : GlobalTheory.LogCris.Mor L L' σ) {Λ' : Type} [CommRing Λ'] {c' : Λ' →+* b'.R}
    (σ₀ : Λ →+* Λ') (h : ∀ a, σ (c a) = c' (σ₀ a)) : CH.Mor (OM L c) (OM L' c') σ₀ where
  G := m.functor
  τ T := { toFun := fun z => z
           map_add' := fun _ _ => rfl
           map_smul' := fun a (z : T.B) => congrArg (fun u => T.i u * z) (h a) }
  nat _ _ := rfl

def thU (q : b.Rˣ) (hq : (q : b.R) - 1 ∈ b.I) : UF (Thick L) where
  U T := (Units.map (Ideal.Quotient.mk T.J).toMonoidHom).ker
  map {T T'} φ :=
    { toFun := fun x => ⟨Units.map φ.φ.toMonoidHom x.1, by
        have h : Ideal.Quotient.mk T.J (x.1 : T.B) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 x.2)
        refine MonoidHom.mem_ker.2 (Units.ext ?_)
        change Ideal.quotientMap T'.J φ.φ φ.hle (Ideal.Quotient.mk T.J (x.1 : T.B)) = 1
        rw [h, map_one]⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _) }
  map_id _ _ := rfl
  map_comp _ _ _ := rfl
  q T := ⟨Units.map T.i.toMonoidHom q, MonoidHom.mem_ker.2 (Units.ext (by
    have := T.i_mem hq
    rw [map_sub, map_one] at this
    exact Ideal.Quotient.eq.2 this))⟩
  map_q φ := Subtype.ext (Units.ext (φ.comm _))

end Thick

section Sub

variable {F : Fn O} (V : F.Sub) (b : Base) (ht : b.t = 1) (κ : O →+* b.R ⧸ b.I)

def subThick : Thick (V.fn.cr b ht κ) ⥤ Thick (F.cr b ht κ) where
  obj T := { B := T.B, i := T.i, J := T.J, δ := T.δ, adm := T.adm, compat := T.compat, α := (),
             y := ⟨(T.y.1.1, T.y.1.2.1), T.y.2⟩, inα := trivial, w := T.w, x := T.x, v := T.v, s := T.s,
             hx := fun j => j.elim, hs := T.hs, hv := T.hv }
  map {T T'} f := { φ := f.φ, u := f.u, comm := f.comm, dp := f.dp, hle := f.hle,
                    pt := Subtype.ext (Prod.ext (congrArg (fun z => z.1.1) f.pt) (congrArg (fun z => z.1.2.1) f.pt)),
                    hx := fun j => j.elim, hs := f.hs, hv := fun j => j.elim }
  map_id _ := rfl
  map_comp _ _ := rfl

variable {Λ : Type} [CommRing Λ] (c : Λ →+* b.R)

theorem subThick_OM : subThick V b ht κ ⋙ OM _ c = OM _ c := rfl

theorem subThick_rees (ρ : ℕ → ℕ) (hρ : Slow ρ) (μ : Λ) (hμ : c μ ∈ b.I) :
    subThick V b ht κ ⋙ (pdFlt _ c ρ hρ μ hμ).rees = (pdFlt _ c ρ hρ μ hμ).rees := rfl

end Sub

section CrMor

variable {O' : Type} [CommRing O'] {F : Fn O} {F' : Fn O'} {b b' : Base} {ht : b.t = 1} {ht' : b'.t = 1}
  {κ : O →+* b.R ⧸ b.I} {κ' : O' →+* b'.R ⧸ b'.I}

def crMor (σ : b.R →+* b'.R) (hp : b.p = b'.p) (hI : IsDPMorphism b.γ b'.γ σ) (pt : F'.ptK κ' ⟶ F.ptK κ)
    (str : ∀ (B : CommRingCat.{0}) (y : (F'.ptK κ').obj B) (r : b.R),
      (pt.app B y).1.1 (Ideal.Quotient.mk _ r) = y.1.1 (Ideal.Quotient.mk _ (σ r))) :
    GlobalTheory.LogCris.Mor (F.cr b ht κ) (F'.cr b' ht' κ') σ where
  hp := hp
  hI := hI
  a := 1
  ha := by simp
  m := 1
  ht := by simp [ht, ht']
  e i := i.elim
  he j := j.elim
  c α := α
  pt := pt
  str y r := str _ y r
  inc _ := trivial
  w _ i := i.elim
  w_map i := i.elim
  hf i := i.elim
  hg i := i.elim
  hw _ := Finset.prod_of_isEmpty (ι := Empty) _

end CrMor

section LiftObj

variable {F : Fn O} {d : ℕ} (s : F.Small d) {b : Base} (ht : b.t = 1) {κ : O →+* b.R ⧸ b.I}
  (𝓛 : Lift s.a (fun k => (s.T k : s.R)) b.R b.I κ) (δ : DividedPowers (b.I.map 𝓛.i)) (hδ : IsDPMorphism b.γ δ 𝓛.i)
  (hp : b.p ≠ 0) (hn : IsNilpotent (b.p : b.R))

def liftObj : Thick (F.cr b ht κ) where
  B := 𝓛.D
  i := 𝓛.i
  J := b.I.map 𝓛.i
  δ := δ
  adm := ⟨fun _ => by simpa using hn.map 𝓛.i, fun h => absurd h hp⟩
  compat := hδ
  α := ()
  y := ⟨(Ideal.quotientMap _ 𝓛.i Ideal.le_comap_map, F.Pt.map (CommRingCat.ofHom 𝓛.j) s.y₀), by
    have h := F.ov_map (CommRingCat.ofHom 𝓛.j) s.ov
    have e : 𝓛.j.comp s.a = (Ideal.quotientMap _ 𝓛.i Ideal.le_comap_map).comp κ := RingHom.ext fun o => by
      obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (κ o)
      rw [RingHom.comp_apply, RingHom.comp_apply, 𝓛.hj o x hx, ← hx]; rfl
    exact e ▸ h⟩
  inα := trivial
  w _ := rfl
  x j := j.elim
  v j := j.elim
  s := 1
  hx j := j.elim
  hs := (Finset.prod_of_isEmpty (ι := Empty) _).trans (by rw [ht]; simp)
  hv := (map_one _).trans (Finset.prod_of_isEmpty (ι := Empty) _).symm

end LiftObj

end CrystallineSemistableComparison.B
