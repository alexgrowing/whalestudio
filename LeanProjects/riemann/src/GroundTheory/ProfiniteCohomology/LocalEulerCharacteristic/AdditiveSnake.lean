import Mathlib
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.AdditiveDefs
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

universe u v

open Representation

section Intertwining

variable {k Γ X Y : Type*} [CommRing k] [Monoid Γ] [AddCommGroup X] [Module k X]
  [AddCommGroup Y] [Module k Y] {ρ : Representation k Γ X} {σ : Representation k Γ Y}
  {φ : X →ₗ[k] Y}

theorem ker_le_comap_of_isIntertwiningMap (hφ : ρ.IsIntertwiningMap σ φ) (γ : Γ) :
    LinearMap.ker φ ≤ (LinearMap.ker φ).comap (ρ γ) := fun x hx => by
  simp only [Submodule.mem_comap, LinearMap.mem_ker] at hx ⊢
  rw [hφ.isIntertwining, hx, map_zero]

theorem range_le_comap_of_isIntertwiningMap (hφ : ρ.IsIntertwiningMap σ φ) (γ : Γ) :
    LinearMap.range φ ≤ (LinearMap.range φ).comap (σ γ) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨ρ γ x, hφ.isIntertwining γ x⟩

end Intertwining

theorem finite_of_exact {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    (f : X →+ Y) (g : Y →+ Z) (hfg : Function.Exact f g) [Finite X] [Finite Z] : Finite Y := by
  refine (AddMonoidHom.finite_iff_finite_ker_range g).2 ⟨?_, inferInstance⟩
  have hs : (g.ker : Set Y) ⊆ Set.range f := fun y hy => (hfg y).1 hy
  exact ((Set.finite_range f).subset hs).to_subtype

namespace AdditiveFunction

variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)

section Basic

variable {X Y : Type u} [AddCommGroup X] [Module (ZMod l) X] [Finite X]
  [AddCommGroup Y] [Module (ZMod l) Y] [Finite Y]

theorem toFun_eq_zero_of_subsingleton [Subsingleton X] (ρ : Representation (ZMod l) Γ X) :
    d.toFun X ρ = 0 := by
  have h := d.additive ρ ρ ρ 0 0 ⟨fun _ _ => Subsingleton.elim _ _⟩
    ⟨fun _ _ => Subsingleton.elim _ _⟩ (fun _ _ _ => Subsingleton.elim _ _)
    (fun _ => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩)
    (fun _ => ⟨0, Subsingleton.elim _ _⟩)
  omega

theorem toFun_congr (ρ : Representation (ZMod l) Γ X) (σ : Representation (ZMod l) Γ Y)
    (e : X ≃ₗ[ZMod l] Y) (he : ∀ γ x, e (ρ γ x) = σ γ (e x)) :
    d.toFun X ρ = d.toFun Y σ := by
  have h := d.additive ρ σ (Representation.trivial (ZMod l) Γ PUnit.{u + 1}) e.toLinearMap 0
    ⟨he⟩ ⟨fun _ _ => Subsingleton.elim _ _⟩ e.injective
    (fun y => ⟨fun _ => ⟨e.symm y, by simp⟩, fun _ => Subsingleton.elim _ _⟩)
    (fun _ => ⟨0, Subsingleton.elim _ _⟩)
  rw [h, d.toFun_eq_zero_of_subsingleton (X := PUnit.{u + 1}), add_zero]

theorem toFun_eq_ker_add_range (ρ : Representation (ZMod l) Γ X)
    (σ : Representation (ZMod l) Γ Y) (φ : X →ₗ[ZMod l] Y) (hφ : ρ.IsIntertwiningMap σ φ) :
    d.toFun X ρ = d.toFun (LinearMap.ker φ)
        (ρ.subrepresentation _ (ker_le_comap_of_isIntertwiningMap hφ)) +
      d.toFun (LinearMap.range φ)
        (σ.subrepresentation _ (range_le_comap_of_isIntertwiningMap hφ)) :=
  d.additive _ ρ _ (LinearMap.ker φ).subtype φ.rangeRestrict ⟨fun _ _ => rfl⟩
    ⟨fun γ x => Subtype.ext (hφ.isIntertwining γ x)⟩ (Submodule.injective_subtype _)
    (fun y => by
      rw [← LinearMap.exact_subtype_ker_map φ y, Subtype.ext_iff]
      rfl)
    (LinearMap.surjective_rangeRestrict φ)

theorem toFun_subrep_congr (ρ : Representation (ZMod l) Γ X) {p q : Submodule (ZMod l) X}
    (h : p = q) (hp : ∀ γ, p ≤ p.comap (ρ γ)) (hq : ∀ γ, q ≤ q.comap (ρ γ)) :
    d.toFun p (ρ.subrepresentation p hp) = d.toFun q (ρ.subrepresentation q hq) := by
  subst h
  rfl

theorem toFun_range_of_injective (ρ : Representation (ZMod l) Γ X)
    (σ : Representation (ZMod l) Γ Y) (φ : X →ₗ[ZMod l] Y) (hφ : ρ.IsIntertwiningMap σ φ)
    (hinj : Function.Injective φ) :
    d.toFun (LinearMap.range φ)
        (σ.subrepresentation _ (range_le_comap_of_isIntertwiningMap hφ)) = d.toFun X ρ := by
  have : Subsingleton (LinearMap.ker φ) :=
    ⟨fun a b => Subtype.ext (hinj (by rw [LinearMap.mem_ker.1 a.2, LinearMap.mem_ker.1 b.2]))⟩
  rw [d.toFun_eq_ker_add_range ρ σ φ hφ,
    d.toFun_eq_zero_of_subsingleton (X := LinearMap.ker φ), zero_add]

omit [Finite X] in

theorem toFun_range_of_surjective (ρ : Representation (ZMod l) Γ X)
    (σ : Representation (ZMod l) Γ Y) (φ : X →ₗ[ZMod l] Y) (hφ : ρ.IsIntertwiningMap σ φ)
    (hs : Function.Surjective φ) :
    d.toFun (LinearMap.range φ)
        (σ.subrepresentation _ (range_le_comap_of_isIntertwiningMap hφ)) = d.toFun Y σ :=
  d.toFun_congr _ _ (LinearEquiv.ofTop _ (LinearMap.range_eq_top.2 hs)) (fun _ _ => rfl)

end Basic

theorem alternating_sum_six {T₁ T₂ T₃ Q₁ Q₂ Q₃ : Type u}
    [AddCommGroup T₁] [Module (ZMod l) T₁] [Finite T₁]
    [AddCommGroup T₂] [Module (ZMod l) T₂] [Finite T₂]
    [AddCommGroup T₃] [Module (ZMod l) T₃] [Finite T₃]
    [AddCommGroup Q₁] [Module (ZMod l) Q₁] [Finite Q₁]
    [AddCommGroup Q₂] [Module (ZMod l) Q₂] [Finite Q₂]
    [AddCommGroup Q₃] [Module (ZMod l) Q₃] [Finite Q₃]
    (τ₁ : Representation (ZMod l) Γ T₁) (τ₂ : Representation (ZMod l) Γ T₂)
    (τ₃ : Representation (ZMod l) Γ T₃) (κ₁ : Representation (ZMod l) Γ Q₁)
    (κ₂ : Representation (ZMod l) Γ Q₂) (κ₃ : Representation (ZMod l) Γ Q₃)
    (φ₁ : T₁ →ₗ[ZMod l] T₂) (φ₂ : T₂ →ₗ[ZMod l] T₃) (φ₃ : T₃ →ₗ[ZMod l] Q₁)
    (φ₄ : Q₁ →ₗ[ZMod l] Q₂) (φ₅ : Q₂ →ₗ[ZMod l] Q₃)
    (i₁ : τ₁.IsIntertwiningMap τ₂ φ₁) (i₂ : τ₂.IsIntertwiningMap τ₃ φ₂)
    (i₃ : τ₃.IsIntertwiningMap κ₁ φ₃) (i₄ : κ₁.IsIntertwiningMap κ₂ φ₄)
    (i₅ : κ₂.IsIntertwiningMap κ₃ φ₅)
    (h₁ : Function.Injective φ₁) (e₁₂ : Function.Exact φ₁ φ₂) (e₂₃ : Function.Exact φ₂ φ₃)
    (e₃₄ : Function.Exact φ₃ φ₄) (e₄₅ : Function.Exact φ₄ φ₅) (h₅ : Function.Surjective φ₅) :
    d.toFun T₁ τ₁ - d.toFun T₂ τ₂ + d.toFun T₃ τ₃ - d.toFun Q₁ κ₁ + d.toFun Q₂ κ₂ -
      d.toFun Q₃ κ₃ = 0 := by
  have a₂ := d.toFun_eq_ker_add_range τ₂ τ₃ φ₂ i₂
  have a₃ := d.toFun_eq_ker_add_range τ₃ κ₁ φ₃ i₃
  have a₄ := d.toFun_eq_ker_add_range κ₁ κ₂ φ₄ i₄
  have a₅ := d.toFun_eq_ker_add_range κ₂ κ₃ φ₅ i₅
  have k₂ := (d.toFun_subrep_congr τ₂ (LinearMap.exact_iff.1 e₁₂)
    (ker_le_comap_of_isIntertwiningMap i₂) (range_le_comap_of_isIntertwiningMap i₁)).trans
    (d.toFun_range_of_injective τ₁ τ₂ φ₁ i₁ h₁)
  have k₃ := d.toFun_subrep_congr τ₃ (LinearMap.exact_iff.1 e₂₃)
    (ker_le_comap_of_isIntertwiningMap i₃) (range_le_comap_of_isIntertwiningMap i₂)
  have k₄ := d.toFun_subrep_congr κ₁ (LinearMap.exact_iff.1 e₃₄)
    (ker_le_comap_of_isIntertwiningMap i₄) (range_le_comap_of_isIntertwiningMap i₃)
  have k₅ := d.toFun_subrep_congr κ₂ (LinearMap.exact_iff.1 e₄₅)
    (ker_le_comap_of_isIntertwiningMap i₅) (range_le_comap_of_isIntertwiningMap i₄)
  have r₅ := d.toFun_range_of_surjective κ₂ κ₃ φ₅ i₅ h₅
  omega

end AdditiveFunction

instance modN_finite (A : Type*) [AddCommGroup A] [Finite A] (n : ℕ) : Finite (ModN A n) :=
  Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)

section Maps

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (n : ℕ)

def torsNMap (f : A →+ B) : TorsN A n →ₗ[ZMod n] TorsN B n :=
  (f.toIntLinearMap.restrict (p := LinearMap.ker (LinearMap.lsmul ℤ A (n : ℤ)))
    (q := LinearMap.ker (LinearMap.lsmul ℤ B (n : ℤ))) (fun x hx => by
      rw [mem_ker_lsmul_iff] at hx ⊢
      simp [← map_nsmul, hx])).toAddMonoidHom.toZModLinearMap n

@[simp]
theorem coe_torsNMap_apply (f : A →+ B) (x : TorsN A n) :
    ((torsNMap n f x : TorsN B n) : B) = f x :=
  rfl

def modNMap (f : A →+ B) : ModN A n →ₗ[ZMod n] ModN B n :=
  (Submodule.mapQ _ _ f.toIntLinearMap (by
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, by simp⟩)).toAddMonoidHom.toZModLinearMap n

@[simp]
theorem modNMap_mk (f : A →+ B) (x : A) :
    modNMap n f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) :=
  rfl

theorem modN_mk_eq_zero_iff (x : A) :
    (Submodule.Quotient.mk x : ModN A n) = 0 ↔ ∃ y : A, n • y = x := by
  rw [Submodule.Quotient.mk_eq_zero]
  simp

section Connecting

variable {n} (f : A →+ B) (h : B →+ C) (hh : Function.Surjective h)

noncomputable def connectingFun (c : TorsN C n) : ModN A n :=
  Submodule.Quotient.mk (Function.invFun f (n • Function.surjInv hh (c : C)))

variable {f h}
variable (hfh : Function.Exact f h)
include hh hfh

theorem exists_lift (c : TorsN C n) : ∃ b a, h b = c ∧ f a = n • b := by
  refine ⟨Function.surjInv hh (c : C), Function.invFun f (n • Function.surjInv hh (c : C)),
    Function.surjInv_eq hh _, Function.invFun_eq ?_⟩
  refine (hfh _).1 ?_
  rw [map_nsmul, Function.surjInv_eq hh]
  exact (mem_ker_lsmul_iff n (c : C)).1 c.2

variable (hf : Function.Injective f)
include hf

theorem connectingFun_spec (c : TorsN C n) (b : B) (a : A) (hb : h b = c) (ha : f a = n • b) :
    connectingFun f h hh c = Submodule.Quotient.mk a := by
  have h₀ : f (Function.invFun f (n • Function.surjInv hh (c : C))) =
      n • Function.surjInv hh (c : C) :=
    Function.invFun_eq (by
      refine (hfh _).1 ?_
      rw [map_nsmul, Function.surjInv_eq hh]
      exact (mem_ker_lsmul_iff n (c : C)).1 c.2)
  obtain ⟨a₁, ha₁⟩ := (hfh (b - Function.surjInv hh (c : C))).1 (by
    rw [map_sub, hb, Function.surjInv_eq hh, sub_self])
  have key : a - Function.invFun f (n • Function.surjInv hh (c : C)) = n • a₁ := hf (by
    rw [map_sub, ha, h₀, map_nsmul, ha₁, smul_sub])
  rw [connectingFun, Submodule.Quotient.eq]
  exact ⟨-a₁, by simp [← key]⟩

theorem connectingFun_zero : connectingFun f h hh (0 : TorsN C n) = 0 := by
  rw [connectingFun_spec hh hfh hf 0 0 0 (by simp) (by simp)]
  rfl

theorem connectingFun_add (c c' : TorsN C n) :
    connectingFun f h hh (c + c') = connectingFun f h hh c + connectingFun f h hh c' := by
  obtain ⟨b, a, hb, ha⟩ := exists_lift hh hfh c
  obtain ⟨b', a', hb', ha'⟩ := exists_lift hh hfh c'
  rw [connectingFun_spec hh hfh hf c b a hb ha, connectingFun_spec hh hfh hf c' b' a' hb' ha',
    connectingFun_spec hh hfh hf (c + c') (b + b') (a + a') (by simp [hb, hb'])
      (by simp [ha, ha', smul_add])]
  rfl

noncomputable def connecting : TorsN C n →ₗ[ZMod n] ModN A n :=
  AddMonoidHom.toZModLinearMap n
    { toFun := connectingFun f h hh
      map_zero' := connectingFun_zero hh hfh hf
      map_add' := connectingFun_add hh hfh hf }

theorem connecting_apply (c : TorsN C n) : connecting hh hfh hf c = connectingFun f h hh c :=
  rfl

theorem connecting_spec (c : TorsN C n) (b : B) (a : A) (hb : h b = c) (ha : f a = n • b) :
    connecting hh hfh hf c = Submodule.Quotient.mk a :=
  connectingFun_spec hh hfh hf c b a hb ha

omit hh hfh in

theorem torsNMap_injective : Function.Injective (torsNMap n f) := fun _ _ hxy =>
  Subtype.ext (hf (congrArg Subtype.val hxy))

omit hh in

theorem exact_torsNMap_torsNMap : Function.Exact (torsNMap n f) (torsNMap n h) := by
  intro y
  constructor
  · intro hy
    obtain ⟨a, ha⟩ := (hfh (y : B)).1 (congrArg Subtype.val hy)
    refine ⟨⟨a, (mem_ker_lsmul_iff n a).2 (hf ?_)⟩, Subtype.ext ha⟩
    rw [map_nsmul, ha, map_zero]
    exact (mem_ker_lsmul_iff n (y : B)).1 y.2
  · rintro ⟨x, rfl⟩
    exact Subtype.ext ((hfh _).2 ⟨x, rfl⟩)

theorem exact_torsNMap_connecting : Function.Exact (torsNMap n h) (connecting hh hfh hf) := by
  intro c
  obtain ⟨b, a, hb, ha⟩ := exists_lift hh hfh c
  rw [connecting_spec hh hfh hf c b a hb ha, modN_mk_eq_zero_iff]
  constructor
  · rintro ⟨a₁, ha₁⟩
    have hb₁ : n • (b - f a₁) = 0 := by rw [smul_sub, ← ha, ← map_nsmul, ha₁, sub_self]
    refine ⟨⟨b - f a₁, (mem_ker_lsmul_iff n _).2 hb₁⟩, Subtype.ext ?_⟩
    simp [hb, (hfh _).2 ⟨a₁, rfl⟩]
  · rintro ⟨t, rfl⟩
    have h₀ := connecting_spec hh hfh hf (torsNMap n h t) t 0 rfl
      (by rw [map_zero, (mem_ker_lsmul_iff n (t : B)).1 t.2])
    rw [connecting_spec hh hfh hf _ b a hb ha, Submodule.Quotient.eq, sub_zero] at h₀
    simpa [eq_comm] using h₀

theorem exact_connecting_modNMap : Function.Exact (connecting hh hfh hf) (modNMap n f) := by
  intro q
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [modNMap_mk, modN_mk_eq_zero_iff]
  constructor
  · rintro ⟨b, hb⟩
    have hc : h b ∈ LinearMap.ker (LinearMap.lsmul ℤ C (n : ℤ)) := by
      rw [mem_ker_lsmul_iff, ← map_nsmul, hb]
      exact (hfh _).2 ⟨a, rfl⟩
    exact ⟨⟨h b, hc⟩, connecting_spec hh hfh hf _ b a rfl hb.symm⟩
  · rintro ⟨c, hc⟩
    obtain ⟨b, a', hb, ha'⟩ := exists_lift hh hfh c
    rw [connecting_spec hh hfh hf c b a' hb ha', Submodule.Quotient.eq] at hc
    obtain ⟨y, hy⟩ := hc
    refine ⟨b - f y, ?_⟩
    simp only [LinearMap.lsmul_apply, natCast_zsmul] at hy
    rw [smul_sub, ← ha', ← map_nsmul, ← map_sub, hy, sub_sub_cancel]

omit hf in

theorem exact_modNMap_modNMap : Function.Exact (modNMap n f) (modNMap n h) := by
  intro q
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [modNMap_mk, modN_mk_eq_zero_iff]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨b', rfl⟩ := hh c
    obtain ⟨a, ha⟩ := (hfh (b - n • b')).1 (by rw [map_sub, map_nsmul, hc, sub_self])
    refine ⟨Submodule.Quotient.mk a, ?_⟩
    rw [modNMap_mk, ha, Submodule.Quotient.eq]
    exact ⟨-b', by simp⟩
  · rintro ⟨q', hq'⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q'
    rw [modNMap_mk, Submodule.Quotient.eq] at hq'
    obtain ⟨y, hy⟩ := hq'
    simp only [LinearMap.lsmul_apply, natCast_zsmul] at hy
    refine ⟨-h y, ?_⟩
    rw [smul_neg, ← map_nsmul, hy, map_sub, (hfh _).2 ⟨a, rfl⟩, zero_sub, neg_neg]

omit hfh hf in

theorem modNMap_surjective : Function.Surjective (modNMap n h) := by
  intro q
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨b, rfl⟩ := hh c
  exact ⟨Submodule.Quotient.mk b, rfl⟩

end Connecting

end Maps

section Equivariant

variable {Γ : Type*} [Group Γ] {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [DistribMulAction Γ A] [DistribMulAction Γ B] [DistribMulAction Γ C] (n : ℕ)

theorem isIntertwiningMap_torsNMap {f : A →+ B} (hfγ : ∀ (γ : Γ) (a : A), f (γ • a) = γ • f a) :
    (torsNRep Γ A n).IsIntertwiningMap (torsNRep Γ B n) (torsNMap n f) :=
  ⟨fun γ x => Subtype.ext (hfγ γ x)⟩

theorem isIntertwiningMap_modNMap {f : A →+ B} (hfγ : ∀ (γ : Γ) (a : A), f (γ • a) = γ • f a) :
    (modNRep Γ A n).IsIntertwiningMap (modNRep Γ B n) (modNMap n f) :=
  ⟨fun γ x => by
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact congrArg Submodule.Quotient.mk (hfγ γ a)⟩

theorem isIntertwiningMap_connecting {n : ℕ} {f : A →+ B} {h : B →+ C}
    (hh : Function.Surjective h) (hfh : Function.Exact f h) (hf : Function.Injective f)
    (hfγ : ∀ (γ : Γ) (a : A), f (γ • a) = γ • f a) (hhγ : ∀ (γ : Γ) (b : B), h (γ • b) = γ • h b) :
    (torsNRep Γ C n).IsIntertwiningMap (modNRep Γ A n) (connecting hh hfh hf) :=
  ⟨fun γ c => by
    obtain ⟨b, a, hb, ha⟩ := exists_lift hh hfh c
    rw [connecting_spec hh hfh hf c b a hb ha,
      connecting_spec hh hfh hf _ (γ • b) (γ • a) (by rw [hhγ, hb]; rfl)
        (by rw [hfγ, ha, smul_comm])]
    rfl⟩

end Equivariant

section Finiteness

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] {n : ℕ}
  {f : A →+ B} {h : B →+ C}

theorem finite_torsN_of_exact (hfh : Function.Exact f h) (hf : Function.Injective f)
    [Finite (TorsN A n)] [Finite (TorsN C n)] : Finite (TorsN B n) :=
  finite_of_exact (torsNMap n f).toAddMonoidHom (torsNMap n h).toAddMonoidHom
    (exact_torsNMap_torsNMap hfh hf)

theorem finite_modN_of_exact (hh : Function.Surjective h) (hfh : Function.Exact f h)
    [Finite (ModN A n)] [Finite (ModN C n)] : Finite (ModN B n) :=
  finite_of_exact (modNMap n f).toAddMonoidHom (modNMap n h).toAddMonoidHom
    (exact_modNMap_modNMap hh hfh)

theorem finite_torsN_of_injective (hf : Function.Injective f) [Finite (TorsN B n)] :
    Finite (TorsN A n) :=
  Finite.of_injective _ (torsNMap_injective hf)

theorem finite_modN_of_surjective (hh : Function.Surjective h) [Finite (ModN B n)] :
    Finite (ModN C n) :=
  Finite.of_surjective _ (modNMap_surjective hh)

end Finiteness

section Actions

variable {Γ : Type*} [Monoid Γ] {A : Type*} [AddCommGroup A] [DistribMulAction Γ A]

abbrev subgroupDistribMulAction (H : AddSubgroup A) (hH : ∀ (γ : Γ) (a : A), a ∈ H → γ • a ∈ H) :
    DistribMulAction Γ H where
  smul γ a := ⟨γ • (a : A), hH γ a a.2⟩
  one_smul a := Subtype.ext (one_smul Γ (a : A))
  mul_smul γ δ a := Subtype.ext (mul_smul γ δ (a : A))
  smul_zero γ := Subtype.ext (smul_zero γ)
  smul_add γ a b := Subtype.ext (smul_add γ (a : A) b)

abbrev quotientDistribMulAction (H : AddSubgroup A) (hH : ∀ (γ : Γ) (a : A), a ∈ H → γ • a ∈ H) :
    DistribMulAction Γ (A ⧸ H) where
  smul γ := QuotientAddGroup.map H H (DistribSMul.toAddMonoidHom A γ) (fun a ha => hH γ a ha)
  one_smul x := by
    induction x using QuotientAddGroup.induction_on with
    | H a => exact congrArg QuotientAddGroup.mk (one_smul Γ a)
  mul_smul γ δ x := by
    induction x using QuotientAddGroup.induction_on with
    | H a => exact congrArg QuotientAddGroup.mk (mul_smul γ δ a)
  smul_zero γ := map_zero _
  smul_add γ x y := map_add _ x y

end Actions

namespace AdditiveFunction

variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)

theorem g_add {A B C : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction Γ A] [DistribMulAction Γ B] [DistribMulAction Γ C] (f : A →+ B)
    (h : B →+ C) (hfγ : ∀ (γ : Γ) (a : A), f (γ • a) = γ • f a)
    (hhγ : ∀ (γ : Γ) (b : B), h (γ • b) = γ • h b) (hf : Function.Injective f)
    (hfh : Function.Exact f h) (hh : Function.Surjective h)
    [Finite (ModN A l)] [Finite (TorsN A l)] [Finite (ModN C l)] [Finite (TorsN C l)] :
    d.g B = d.g A + d.g C := by
  have := finite_torsN_of_exact (n := l) hfh hf
  have := finite_modN_of_exact (n := l) hh hfh
  rw [d.g_eq A, d.g_eq B, d.g_eq C]
  have := d.alternating_sum_six (torsNRep Γ A l) (torsNRep Γ B l) (torsNRep Γ C l)
    (modNRep Γ A l) (modNRep Γ B l) (modNRep Γ C l) (torsNMap l f) (torsNMap l h)
    (connecting hh hfh hf) (modNMap l f) (modNMap l h) (isIntertwiningMap_torsNMap l hfγ)
    (isIntertwiningMap_torsNMap l hhγ) (isIntertwiningMap_connecting hh hfh hf hfγ hhγ)
    (isIntertwiningMap_modNMap l hfγ) (isIntertwiningMap_modNMap l hhγ) (torsNMap_injective hf)
    (exact_torsNMap_torsNMap hfh hf) (exact_torsNMap_connecting hh hfh hf)
    (exact_connecting_modNMap hh hfh hf) (exact_modNMap_modNMap hh hfh) (modNMap_surjective hh)
  linarith

end AdditiveFunction

end GroundTheory.ProfCoh
