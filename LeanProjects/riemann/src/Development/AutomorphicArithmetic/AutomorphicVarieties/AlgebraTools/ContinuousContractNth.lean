import Mathlib

noncomputable section

namespace UpperTheory.V.AlgebraTools

structure Cx (A : Type) [CommRing A] where
  X : ℕ → Type
  [grp : ∀ n, AddCommGroup (X n)]
  [mod : ∀ n, Module A (X n)]
  d : ∀ n, X n →ₗ[A] X (n + 1)
  dd : ∀ n x, d (n + 1) (d n x) = 0

attribute [instance] Cx.grp Cx.mod

namespace Cx

variable {A : Type} [CommRing A]

def Z (K : Cx A) (n : ℕ) : Submodule A (K.X n) := LinearMap.ker (K.d n)

def B (K : Cx A) : ∀ n : ℕ, Submodule A (K.X n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (K.d n)

theorem B_le_Z (K : Cx A) (n : ℕ) : K.B n ≤ K.Z n := by
  rcases n with _ | n
  · exact bot_le
  · exact fun _ ⟨y, hy⟩ => hy ▸ K.dd n y

abbrev H (K : Cx A) (n : ℕ) : Type := K.Z n ⧸ (K.B n).comap (K.Z n).subtype

abbrev cls (K : Cx A) {n : ℕ} (z : K.Z n) : K.H n := Submodule.Quotient.mk z

theorem cls_eq_zero (K : Cx A) {n : ℕ} (z : K.Z n) : K.cls z = 0 ↔ z.1 ∈ K.B n :=
  (Submodule.Quotient.mk_eq_zero _).trans Submodule.mem_comap

structure Hom (K L : Cx A) where
  f : ∀ n, K.X n →ₗ[A] L.X n
  comm : ∀ n x, f (n + 1) (K.d n x) = L.d n (f n x)

namespace Hom

variable {K L N : Cx A}

def id (K : Cx A) : Hom K K where
  f _ := LinearMap.id
  comm _ _ := rfl

def comp (ψ : Hom L N) (φ : Hom K L) : Hom K N where
  f n := ψ.f n ∘ₗ φ.f n
  comm n x := (congrArg (ψ.f (n + 1)) (φ.comm n x)).trans (ψ.comm n _)

def smul (a : A) (φ : Hom K L) : Hom K L where
  f n := a • φ.f n
  comm n x := by rw [LinearMap.smul_apply, LinearMap.smul_apply, φ.comm, map_smul]

def sub (φ ψ : Hom K L) : Hom K L where
  f n := φ.f n - ψ.f n
  comm n x := by rw [LinearMap.sub_apply, LinearMap.sub_apply, φ.comm, ψ.comm, map_sub]

def Z (φ : Hom K L) (n : ℕ) : K.Z n →ₗ[A] L.Z n :=
  (φ.f n).restrict fun x hx => by
    have h0 : K.d n x = 0 := hx
    exact (φ.comm n x).symm.trans (by rw [h0, map_zero])

theorem map_B (φ : Hom K L) (n : ℕ) : ∀ x ∈ K.B n, φ.f n x ∈ L.B n := by
  rcases n with _ | n
  · intro x hx
    rw [(Submodule.mem_bot A).1 hx, map_zero]
    exact zero_mem _
  · rintro _ ⟨y, rfl⟩
    exact ⟨φ.f n y, (φ.comm n y).symm⟩

def H (φ : Hom K L) (n : ℕ) : K.H n →ₗ[A] L.H n :=
  Submodule.mapQ _ _ (φ.Z n) fun z hz => φ.map_B n z.1 hz

theorem H_cls (φ : Hom K L) {n : ℕ} (z : K.Z n) : φ.H n (K.cls z) = L.cls (φ.Z n z) := rfl

theorem coe_Z (φ : Hom K L) {n : ℕ} (z : K.Z n) : (φ.Z n z).1 = φ.f n z.1 := rfl

theorem H_comp (ψ : Hom L N) (φ : Hom K L) (n : ℕ) (x : K.H n) :
    (ψ.comp φ).H n x = ψ.H n (φ.H n x) :=
  Submodule.Quotient.induction_on _ x fun _ => rfl

theorem H_id (n : ℕ) (x : K.H n) : (Hom.id K).H n x = x :=
  Submodule.Quotient.induction_on _ x fun _ => rfl

theorem H_smul (a : A) (φ : Hom K L) (n : ℕ) (x : K.H n) : (φ.smul a).H n x = a • φ.H n x :=
  Submodule.Quotient.induction_on _ x fun _ => rfl

end Hom

def prod (K L : Cx A) : Cx A where
  X n := K.X n × L.X n
  d n := (K.d n).prodMap (L.d n)
  dd n x := Prod.ext (K.dd n x.1) (L.dd n x.2)

def pi {ι : Type} (K : ι → Cx A) : Cx A where
  X n := ∀ i, (K i).X n
  d n := LinearMap.pi fun i => (K i).d n ∘ₗ LinearMap.proj i
  dd n x := funext fun i => (K i).dd n (x i)

def up (L : Cx A) : ℕ → Type
  | 0 => PUnit
  | n + 1 => L.X n

instance upGrp (L : Cx A) : ∀ n, AddCommGroup (L.up n)
  | 0 => inferInstanceAs (AddCommGroup PUnit)
  | n + 1 => L.grp n

instance upMod (L : Cx A) : ∀ n, Module A (L.up n)
  | 0 => inferInstanceAs (Module A PUnit)
  | n + 1 => L.mod n

def upD (L : Cx A) : ∀ n, L.up n →ₗ[A] L.X n
  | 0 => 0
  | n + 1 => L.d n

theorem d_upD (L : Cx A) (n : ℕ) (y : L.up n) : L.d n (L.upD n y) = 0 := by
  rcases n with _ | n
  · exact map_zero _
  · exact L.dd n y

variable {K L N : Cx A}

def fib (φ : Hom K L) : Cx A where
  X n := K.X n × L.up n
  d n := (K.d n ∘ₗ LinearMap.fst A _ _).prod
    (show K.X n × L.up n →ₗ[A] L.X n from φ.f n ∘ₗ LinearMap.fst A _ _ - L.upD n ∘ₗ LinearMap.snd A _ _)
  dd n x := Prod.ext (K.dd n x.1) <| by
    change φ.f (n + 1) (K.d n x.1) - L.d n (φ.f n x.1 - L.upD n x.2) = 0
    rw [map_sub, L.d_upD, φ.comm, sub_zero, sub_self]

theorem fib_d (φ : Hom K L) (n : ℕ) (x : K.X n) (y : L.up n) :
    (fib φ).d n (x, y) = (K.d n x, show L.X n from φ.f n x - L.upD n y) := rfl

def fibFst (φ : Hom K L) : Hom (fib φ) K where
  f _ := LinearMap.fst A _ _
  comm _ _ := rfl

def upMap {L L' : Cx A} (β : Hom L L') : ∀ n, L.up n →ₗ[A] L'.up n
  | 0 => 0
  | n + 1 => β.f n

theorem upD_upMap {L L' : Cx A} (β : Hom L L') (n : ℕ) (y : L.up n) :
    L'.upD n (upMap β n y) = β.f n (L.upD n y) := by
  rcases n with _ | n
  · exact (map_zero _).symm
  · exact (β.comm n y).symm

def fibMap {K L K' L' : Cx A} {φ : Hom K L} {φ' : Hom K' L'} (α : Hom K K') (β : Hom L L')
    (h : ∀ n x, φ'.f n (α.f n x) = β.f n (φ.f n x)) : Hom (fib φ) (fib φ') where
  f n := (α.f n).prodMap (upMap β n)
  comm n x := Prod.ext (α.comm n x.1) <| by
    change β.f n (φ.f n x.1 - L.upD n x.2) = φ'.f n (α.f n x.1) - L'.upD n (upMap β n x.2)
    rw [h, upD_upMap, map_sub]

def fibIn (φ : Hom K L) (n : ℕ) : L.Z n →ₗ[A] (fib φ).H (n + 1) :=
  Submodule.mkQ _ ∘ₗ LinearMap.codRestrict ((fib φ).Z (n + 1))
    (LinearMap.inr A (K.X (n + 1)) (L.X n) ∘ₗ (L.Z n).subtype) fun y =>
      Prod.ext (map_zero (K.d (n + 1))) <| by
        have hy : L.d n y.1 = 0 := y.2
        change φ.f (n + 1) 0 - L.d n y.1 = 0
        rw [hy, map_zero, sub_zero]

structure SES (i : Hom K L) (p : Hom L N) : Prop where
  inj : ∀ n, Function.Injective (i.f n)
  ex : ∀ n, Function.Exact (i.f n) (p.f n)
  surj : ∀ n, Function.Surjective (p.f n)

def IsDelta (i : Hom K L) (p : Hom L N) (δ : ∀ n, N.H n →ₗ[A] K.H (n + 1)) : Prop :=
  ∀ (n : ℕ) (z : N.Z n) (x : L.X n) (w : K.Z (n + 1)),
    p.f n x = z.1 → i.f (n + 1) w.1 = L.d n x → δ n (N.cls z) = K.cls w

def toMathlib (K : Cx A) : CochainComplex (ModuleCat.{0} A) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of A (K.X n)) (fun n => ModuleCat.ofHom (K.d n)) fun n =>
    ModuleCat.hom_ext (LinearMap.ext (K.dd n))

def single (M : Type) [AddCommGroup M] [Module A M] : Cx A where
  X n := match n with | 0 => M | _ + 1 => PUnit
  grp n := match n with | 0 => ‹AddCommGroup M› | _ + 1 => inferInstanceAs (AddCommGroup PUnit)
  mod n := match n with | 0 => ‹Module A M› | _ + 1 => (inferInstance : Module A PUnit)
  d _ := 0
  dd _ _ := rfl

instance instInhabited : Inhabited (Cx A) := ⟨single PUnit⟩

end Cx

section Cochains

variable {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]

def dInh (ρ : Representation A G M) (n : ℕ) : ((Fin n → G) → M) →ₗ[A] ((Fin (n + 1) → G) → M) :=
  (inhomogeneousCochains.d (k := A) (G := G) (Rep.of ρ) n).hom

theorem dInh_apply (ρ : Representation A G M) (n : ℕ) (f : (Fin n → G) → M) (g : Fin (n + 1) → G) :
    dInh ρ n f g = ρ (g 0) (f fun i => g i.succ) +
      ∑ j : Fin (n + 1), (-1 : A) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g) := rfl

theorem dInh_dInh (ρ : Representation A G M) (n : ℕ) (f : (Fin n → G) → M) :
    dInh ρ (n + 1) (dInh ρ n f) = 0 :=
  LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (groupCohomology.inhomogeneousCochains.d_comp_d (A := Rep.of ρ) (n := n))) f

variable [TopologicalSpace G] [TopologicalSpace M]

def ContAct (ρ : Representation A G M) : Prop := Continuous fun q : G × M => ρ q.1 q.2

theorem continuous_contractNth {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}
    (j : Fin (n + 1)) : Continuous fun g : Fin (n + 1) → G => Fin.contractNth j (· * ·) g :=
  continuous_pi fun k => by
    unfold Fin.contractNth
    split_ifs <;> fun_prop

variable [IsTopologicalAddGroup M] [ContinuousConstSMul A M]

variable (A G M) in
omit [Group G] in

def contC (n : ℕ) : Submodule A ((Fin n → G) → M) where
  carrier := {f | Continuous f}
  add_mem' hf hg := Continuous.add hf hg
  zero_mem' := continuous_const
  smul_mem' a _ hf := Continuous.const_smul hf a

theorem continuous_dInh [IsTopologicalGroup G] {ρ : Representation A G M} (hρ : ContAct ρ) (n : ℕ)
    {f : (Fin n → G) → M} (hf : Continuous f) : Continuous (dInh ρ n f) := by
  have h1 : Continuous fun g : Fin (n + 1) → G => ρ (g 0) (f fun i => g i.succ) :=
    Continuous.comp (f := fun g : Fin (n + 1) → G => (g 0, f fun i => g i.succ)) hρ (by fun_prop)
  exact h1.add (continuous_finset_sum _ fun j _ => (hf.comp (continuous_contractNth j)).const_smul _)

def contCx [IsTopologicalGroup G] (ρ : Representation A G M) (hρ : ContAct ρ) : Cx A where
  X n := contC A G M n
  d n := (dInh ρ n).restrict fun _ hf => continuous_dInh hρ n hf
  dd n f := Subtype.ext (dInh_dInh ρ n f.1)

def contMap {G' M' : Type} [Group G'] [AddCommGroup M'] [Module A M'] [TopologicalSpace G']
    [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul A M']
    [IsTopologicalGroup G] [IsTopologicalGroup G'] {ρ : Representation A G M} (hρ : ContAct ρ)
    {ρ' : Representation A G' M'} (hρ' : ContAct ρ') (φ : G' →* G) (hφ : Continuous φ)
    (u : M →ₗ[A] M') (hu : Continuous u) (h : ∀ g m, u (ρ (φ g) m) = ρ' g (u m)) :
    Cx.Hom (contCx ρ hρ) (contCx ρ' hρ') where
  f n :=
    { toFun := fun f => ⟨fun g => u (f.1 fun i => φ (g i)),
        hu.comp (Continuous.comp f.2 (continuous_pi fun i => hφ.comp (continuous_apply i)))⟩
      map_add' := fun _ _ => Subtype.ext (funext fun _ => map_add u _ _)
      map_smul' := fun _ _ => Subtype.ext (funext fun _ => map_smul u _ _) }
  comm n f := Subtype.ext <| funext fun g => by
    have hc : ∀ j : Fin (n + 1), Fin.contractNth j (· * ·) (fun i => φ (g i)) =
        fun i => φ (Fin.contractNth j (· * ·) g i) := fun j =>
      (Fin.comp_contractNth (· * ·) (· * ·) (map_mul φ) j g).symm
    change u (dInh ρ n f.1 fun i => φ (g i)) = dInh ρ' n (fun g => u (f.1 fun i => φ (g i))) g
    simp only [dInh_apply, map_add, map_sum, map_smul, h, hc]

def crossed (ρ : Representation A G M) : Submodule A (G → M) where
  carrier := {z | Continuous z ∧ ∀ g h, z (g * h) = z g + ρ g (z h)}
  add_mem' := fun ⟨c, e⟩ ⟨c', e'⟩ => ⟨c.add c', fun g h => by
    simp only [Pi.add_apply, e, e', map_add]; abel⟩
  zero_mem' := ⟨continuous_const, fun g h => by simp⟩
  smul_mem' := fun a _ ⟨c, e⟩ => ⟨c.const_smul a, fun g h => by
    simp only [Pi.smul_apply, e, map_smul, smul_add]⟩

end Cochains

def IsPrincipal {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (z : G → M) : Prop := ∃ m : M, ∀ g, z g = ρ g m - m

def IsTAdic {A : Type} [CommRing A] (t : A) (M : Type) [AddCommGroup M] [Module A M]
    [TopologicalSpace M] : Prop :=
  (nhds (0 : M)).HasBasis (fun _ : ℕ => True) fun k => Set.range fun m : M => t ^ k • m

theorem contAct_trivial {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul A M] :
    ContAct (Representation.trivial A G M) := continuous_snd

end UpperTheory.V.AlgebraTools

end
