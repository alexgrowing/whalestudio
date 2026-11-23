import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg

namespace UpperTheory.V.Fr

section Cone

variable {k G W V : Type} [CommRing k] [Group G] [TopologicalSpace G] [AddCommGroup W] [Module k W]
  {Gv : V → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  (loc : ∀ v, Gv v →* G) (ρ : Representation k G W) (b : V → Submodule k W)

def coneH0 : Submodule k W where
  carrier := {X | (∀ g, ρ g X = X) ∧ ∀ v, X ∈ b v}
  add_mem' := by
    rintro x y ⟨a1, a2⟩ ⟨b1, b2⟩
    exact ⟨fun g => by rw [map_add, a1, b1], fun v => add_mem (a2 v) (b2 v)⟩
  zero_mem' := ⟨fun g => map_zero _, fun v => zero_mem _⟩
  smul_mem' := by
    rintro c x ⟨a1, a2⟩
    exact ⟨fun g => by rw [map_smul, a1], fun v => Submodule.smul_mem _ c (a2 v)⟩

def Z1C : Submodule k ((G → W) × (V → W)) where
  carrier := {x | IsLocallyConstant x.1 ∧ (∀ s t, x.1 (s * t) = x.1 s + ρ s (x.1 t)) ∧
    ∀ v s, x.1 (loc v s) - (ρ (loc v s) (x.2 v) - x.2 v) ∈ b v}
  add_mem' := by
    rintro x y ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    refine ⟨a1.add b1, fun s t => ?_, fun v s => ?_⟩
    · simp only [Prod.fst_add, Pi.add_apply, a2, b2, map_add]; abel
    · convert add_mem (a3 v s) (b3 v s) using 1
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add]; abel
  zero_mem' := ⟨IsLocallyConstant.const 0, by simp, by simp⟩
  smul_mem' := by
    rintro c x ⟨a1, a2, a3⟩
    refine ⟨a1.comp (c • ·), fun s t => by simp [a2], fun v s => ?_⟩
    convert Submodule.smul_mem _ c (a3 v s) using 1
    simp [smul_sub]

def continuousCoboundaries1 : Submodule k ((G → W) × (V → W)) where
  carrier := {x | ∃ X : W, (∀ s, x.1 s = ρ s X - X) ∧ ∀ v, x.2 v - X ∈ b v}
  add_mem' := by
    rintro x y ⟨X, a1, a2⟩ ⟨Y, b1, b2⟩
    refine ⟨X + Y, fun s => ?_, fun v => ?_⟩
    · simp only [Prod.fst_add, Pi.add_apply, a1, b1, map_add]; abel
    · convert add_mem (a2 v) (b2 v) using 1
      simp only [Prod.snd_add, Pi.add_apply]; abel
  zero_mem' := ⟨0, by simp, by simp⟩
  smul_mem' := by
    rintro c x ⟨X, a1, a2⟩
    refine ⟨c • X, fun s => by simp [a1, smul_sub], fun v => ?_⟩
    convert Submodule.smul_mem _ c (a2 v) using 1
    simp [smul_sub]

abbrev H1C : Type := Z1C loc ρ b ⧸ (continuousCoboundaries1 ρ b).comap (Z1C loc ρ b).subtype

def continuousCocycles2 : Submodule k ((G × G → W) × (∀ v, Gv v → W)) where
  carrier := {x | IsLocallyConstant x.1 ∧ (∀ v, IsLocallyConstant (x.2 v)) ∧
    (∀ s t u, ρ s (x.1 (t, u)) + x.1 (s, t * u) = x.1 (s * t, u) + x.1 (s, t)) ∧
    ∀ v s t, x.1 (loc v s, loc v t) - dOne (ρ.comp (loc v)) (x.2 v) (s, t) ∈ b v}
  add_mem' := by
    rintro x y ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩
    refine ⟨a1.add b1, fun v => (a2 v).add (b2 v), fun s t u => ?_, fun v s t => ?_⟩
    · simp only [Prod.fst_add, Pi.add_apply, map_add]
      rw [add_add_add_comm, a3, b3, add_add_add_comm]
    · convert add_mem (a4 v s t) (b4 v s t) using 1
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, dOne, map_add]; abel
  zero_mem' := ⟨IsLocallyConstant.const 0, fun _ => IsLocallyConstant.const 0, by simp, by simp [dOne]⟩
  smul_mem' := by
    rintro c x ⟨a1, a2, a3, a4⟩
    refine ⟨a1.comp (c • ·), fun v => (a2 v).comp (c • ·), fun s t u => ?_, fun v s t => ?_⟩
    · simp only [Prod.smul_fst, Pi.smul_apply, map_smul, ← smul_add, a3]
    · convert Submodule.smul_mem _ c (a4 v s t) using 1
      simp [dOne, smul_sub]

def continuousCoboundaries2 : Submodule k ((G × G → W) × (∀ v, Gv v → W)) where
  carrier := {x | ∃ (β : G → W) (Y : V → W), IsLocallyConstant β ∧ x.1 = dOne ρ β ∧
    ∀ v s, x.2 v s - (β (loc v s) - (ρ (loc v s) (Y v) - Y v)) ∈ b v}
  add_mem' := by
    rintro x y ⟨β, Y, a1, a2, a3⟩ ⟨β', Y', b1, b2, b3⟩
    refine ⟨β + β', Y + Y', a1.add b1, ?_, fun v s => ?_⟩
    · funext p
      simp only [Prod.fst_add, Pi.add_apply, a2, b2, dOne, map_add]; abel
    · convert add_mem (a3 v s) (b3 v s) using 1
      simp only [Prod.snd_add, Pi.add_apply, map_add]; abel
  zero_mem' := ⟨0, 0, IsLocallyConstant.const 0, by funext p; simp [dOne], by simp⟩
  smul_mem' := by
    rintro c x ⟨β, Y, a1, a2, a3⟩
    refine ⟨c • β, c • Y, a1.comp (c • ·), ?_, fun v s => ?_⟩
    · funext p
      simp [a2, dOne, smul_sub]
    · convert Submodule.smul_mem _ c (a3 v s) using 1
      simp [smul_sub]

abbrev coneH2 : Type := continuousCocycles2 loc ρ b ⧸ (continuousCoboundaries2 loc ρ b).comap (continuousCocycles2 loc ρ b).subtype

end Cone

def chRep {k G : Type} [CommRing k] [Group G] (χ : G →* kˣ) : Representation k G k where
  toFun g := (χ g : k) • LinearMap.id
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_comm]

@[simp] theorem chRep_apply {k G : Type} [CommRing k] [Group G] (χ : G →* kˣ) (g : G) (x : k) :
    chRep χ g x = χ g * x := rfl

structure Frame (l : ℕ) [Fact l.Prime] (k : Type) [Field k] : Type 1 where
  Γ : Type
  [grp : Group Γ]
  [top : TopologicalSpace Γ]
  [tg : IsTopologicalGroup Γ]
  [cpt : CompactSpace Γ]
  [t2 : T2Space Γ]
  [td : TotallyDisconnectedSpace Γ]
  del : Γ →* ℤˣ
  c : Γ
  V : Type
  [fV : Fintype V]
  Gv : V → Type
  [gv : ∀ v, Group (Gv v)]
  [tv : ∀ v, TopologicalSpace (Gv v)]
  [tgv : ∀ v, IsTopologicalGroup (Gv v)]
  [cv : ∀ v, CompactSpace (Gv v)]
  [t2v : ∀ v, T2Space (Gv v)]
  [tdv : ∀ v, TotallyDisconnectedSpace (Gv v)]
  loc0 : ∀ v, Gv v →* del.ker
  Iv : ∀ v, Subgroup (Gv v)
  dv : V → ℕ
  Inf : Type
  [fI : Fintype Inf]
  cw : Inf → Γ
  eps : Γ →* ℤ_[l]ˣ
  Ψ : Γ →* kˣ
  g0 : del.ker

attribute [instance] Frame.grp Frame.top Frame.tg Frame.cpt Frame.t2 Frame.td Frame.fV Frame.gv Frame.tv Frame.tgv
  Frame.cv Frame.t2v Frame.tdv Frame.fI

namespace Frame

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] (F : Frame l k)

abbrev G0 : Type := F.del.ker

def loc (v : F.V) : F.Gv v →* F.Γ := F.del.ker.subtype.comp (F.loc0 v)

def conj : F.G0 →* F.G0 := (MulAut.conjNormal F.c : MulAut F.G0).toMonoidHom

def star (g : F.G0) : F.G0 := F.conj g⁻¹

def loc2 (p : F.V × Bool) : F.Gv p.1 →* F.G0 := if p.2 then F.conj.comp (F.loc0 p.1) else F.loc0 p.1

def d : ℕ := ∑ v, F.dv v

def om (K : Type) [CommRing K] [CharP K l] : F.Γ →* Kˣ :=
  (Units.map ((ZMod.castHom (dvd_refl l) K).comp PadicInt.toZMod).toMonoidHom).comp F.eps

def delK (K : Type) [CommRing K] : F.Γ →* Kˣ := (Units.map (Int.castRingHom K).toMonoidHom).comp F.del

def Nv (v : F.V) : Subgroup (F.Gv v) := F.Iv v ⊓ (F.eps.comp (F.loc v)).ker

def ext {k' : Type} [Field k'] (f : k →+* k') : Frame l k' :=
  { F with Ψ := (Units.map f.toMonoidHom).comp F.Ψ }

def EC : Prop :=
  ∀ (K W : Type) [Field K] [Finite K] [CharP K l] [AddCommGroup W] [Module K W] [Module.Finite K W]
    (ρ : Representation K F.Γ W) (b : F.V → Submodule K W), IsOpen (ρ.ker : Set F.Γ) →
    (∀ v s, ∀ X ∈ b v, ρ (F.loc v s) X ∈ b v) →
    (∀ f : W →ₗ[K] K, (∀ g X, f (ρ g X) = F.om K g * f X) → f = 0) →
    Module.Finite K (coneH2 F.loc ρ b) ∧
    Module.finrank K (coneH2 F.loc ρ b) + Module.finrank K (coneH0 ρ b) + ∑ v, F.dv v * Module.finrank K (b v) ≤
      Module.finrank K (H1C F.loc ρ b) + ∑ w, Module.finrank K (LinearMap.ker (ρ (F.cw w) - 1))

structure Ok [CharP k l] (C₀ : ℕ) : Prop where
  l_odd : l ≠ 2
  fin : Finite k
  del_open : IsOpen (F.del.ker : Set F.Γ)
  c_sq : F.c * F.c = 1
  del_c : F.del F.c = -1
  loc_cont : ∀ v, Continuous (F.loc0 v)
  eps_cont : Continuous F.eps
  Ψ_open : IsOpen (F.Ψ.ker : Set F.Γ)
  Ψ_c : F.Ψ F.c = 1
  baseSubgroup_spec : F.Ψ F.g0 ^ 2 ≠ 1
  phi : PhiCond F.Γ l
  card_inf : Fintype.card F.Inf = F.d
  cw_sq : ∀ w, F.cw w * F.cw w = 1
  del_cw : ∀ w, F.del (F.cw w) = -1
  f2a : ∃ g : F.G0, F.om k g ≠ 1
  f2b : ∀ j : ℤ, j = 1 ∨ j = -1 → ∃ g : F.G0, F.om k g * F.Ψ g ^ j ≠ 1
  f2c : ∀ j : ℤ, j = 2 ∨ j = -2 → ∃ g, F.om k g * F.Ψ g ^ j * F.delK k g ≠ 1
  f3 : ∀ v, ∃ g, F.Ψ (F.loc v g) ^ 2 ≠ 1
  f4 : Nontrivial (H1C F.loc (chRep (F.Ψ⁻¹ * F.delK k)) fun _ => ⊥)
  f4' : Nontrivial (H1C F.loc (chRep (F.Ψ⁻¹ ^ 2 * F.delK k)) fun _ => ⊥)
  f5 : ¬ ∃ j : ℤ, ∀ g : F.G0, F.om k g = F.Ψ g ^ j
  Ψ_N : ∀ v, ∀ g ∈ F.Nv v, F.Ψ (F.loc v g) = 1

  gen : ∀ v, ∃ (u : Fin (F.dv v) → F.Gv v) (a₀ : Fin (F.dv v)), (∀ a, u a ∈ F.Iv v ∧ F.Ψ (F.loc v (u a)) = 1) ∧
    (∀ a, a ≠ a₀ → u a ∈ F.Nv v) ∧
    ∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ χ : F.Gv v →* A, IsOpen (χ.ker : Set (F.Gv v)) →
      (∀ a, χ (u a) = 1) → ∀ g ∈ F.Iv v, χ g = 1

  cl : ∃ h : ℕ, h ≠ 0 ∧ ∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ χ : F.G0 →* A,
    IsOpen (χ.ker : Set F.G0) → (∀ p : F.V × Bool, ∀ g ∈ F.Iv p.1, χ (F.loc2 p g) = 1) → ∀ g, χ g ^ h = 1
  ec : F.EC
  b1p : Module.rank k (H1C F.loc (chRep (F.Ψ⁻¹ ^ 2 * F.delK k)) fun _ => ⊥) ≤ C₀
  b1 : Module.rank k (H1C F.loc2 (chRep (F.Ψ⁻¹.comp F.del.ker.subtype)) fun _ => ⊥) ≤ C₀
  h1 : Module.rank k (H1C F.loc (chRep (1 : F.Γ →* kˣ)) fun _ => ⊤) ≤ 1 + C₀

def Big (C₀ : ℕ) : Prop := 3 * C₀ + 5 + 2 < F.d ∧ ∀ v, 5 < F.dv v

end Frame

end UpperTheory.V.Fr
