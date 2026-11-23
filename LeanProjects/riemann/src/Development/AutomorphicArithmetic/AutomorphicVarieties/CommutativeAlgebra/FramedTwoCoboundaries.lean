import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

noncomputable section

open IsLocalRing Matrix

namespace UpperTheory.V.Alg

structure FormData (O : Type) [CommRing O] {ι X : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X) where
  J : Matrix ι ι O
  unit : IsUnit J
  sym : Jᵀ = J ∨ Jᵀ = -J
  κ : Type
  blk : ι → κ
  σ : κ → κ
  invol : Function.Involutive σ
  hblk : ∀ a b, J a b ≠ 0 → blk b = σ (blk a)
  c : X
  hw : ∀ a b, J a b ≠ 0 → w a + w b = c

namespace FormData

variable {O : Type} [CommRing O] {ι X : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup X] {w : ι → X}
  (Φ : FormData O w) (R : Type) [CommRing R] [Algebra O R]

def JR : Matrix ι ι R := Φ.J.map (algebraMap O R)

def g : Submodule R (Matrix ι ι R) where
  carrier := {Y | Yᵀ * Φ.JR R + Φ.JR R * Y = 0 ∧ ∀ a b, Φ.blk a ≠ Φ.blk b → Y a b = 0}
  add_mem' := by
    rintro Y Y' ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨?_, fun a b h => by simp [h2 a b h, h4 a b h]⟩
    rw [transpose_add, add_mul, mul_add, add_add_add_comm, h1, h3, add_zero]
  zero_mem' := ⟨by simp, fun _ _ _ => rfl⟩
  smul_mem' := by
    rintro c Y ⟨h1, h2⟩
    refine ⟨?_, fun a b h => by simp [h2 a b h]⟩
    rw [transpose_smul, smul_mul_assoc, mul_smul_comm, ← smul_add, h1, smul_zero]

def gw (j : X) : Submodule R (Matrix ι ι R) :=
  Φ.g R ⊓
    { carrier := {Y | ∀ a b, w a - w b ≠ j → Y a b = 0}
      add_mem' := fun h h' a b e => by simp [h a b e, h' a b e]
      zero_mem' := fun _ _ _ => rfl
      smul_mem' := fun c Y h a b e => by simp [h a b e] }

variable {R} in

def Normalises {Γ : Type} [Group Γ] (ρ : Γ →* Matrix ι ι R) : Prop :=
  (∀ g, ∃ ν : R, (ρ g)ᵀ * Φ.JR R * ρ g = ν • Φ.JR R) ∧
  (∃ π : Γ →* Equiv.Perm Φ.κ, ∀ g a b, ρ g a b ≠ 0 → Φ.blk a = π g (Φ.blk b)) ∧
  ∀ g a b, w a ≠ w b → ρ g a b = 0

variable {Φ R} in
theorem ad_mem {Γ : Type} [Group Γ] {ρ : Γ →* Matrix ι ι R} (h : Φ.Normalises ρ) (j : X) (s : Γ) {Y : Matrix ι ι R}
    (hY : Y ∈ Φ.gw R j) : ρ s * Y * ρ s⁻¹ ∈ Φ.gw R j := by
  obtain ⟨h1, ⟨π, h2⟩, h3⟩ := h
  obtain ⟨⟨y1, y2⟩, y3⟩ := hY
  have key : ∀ a b, (ρ s * Y * ρ s⁻¹) a b ≠ 0 → ∃ c d, ρ s a c ≠ 0 ∧ Y c d ≠ 0 ∧ ρ s⁻¹ d b ≠ 0 := by
    intro a b hab
    rw [Matrix.mul_apply] at hab
    obtain ⟨d, -, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
    have hd1 := left_ne_zero_of_mul hd
    rw [Matrix.mul_apply] at hd1
    obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd1
    exact ⟨c, d, left_ne_zero_of_mul hc, right_ne_zero_of_mul hc, right_ne_zero_of_mul hd⟩
  refine ⟨⟨?_, fun a b e => ?_⟩, fun a b e => ?_⟩
  · obtain ⟨ν, hν⟩ := h1 s
    have e1 : ρ s * ρ s⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have e2 : (ρ s⁻¹)ᵀ * (ρ s)ᵀ = 1 := by rw [← transpose_mul, e1, transpose_one]
    have : (ρ s * Y * ρ s⁻¹)ᵀ * Φ.JR R + Φ.JR R * (ρ s * Y * ρ s⁻¹) =
        (ρ s⁻¹)ᵀ * (Yᵀ * ((ρ s)ᵀ * Φ.JR R * ρ s) + ((ρ s)ᵀ * Φ.JR R * ρ s) * Y) * ρ s⁻¹ := by
      simp only [transpose_mul, mul_add, add_mul, mul_assoc, e1, mul_one]
      rw [← mul_assoc (ρ s⁻¹)ᵀ (ρ s)ᵀ, e2, one_mul]
    rw [this, hν, mul_smul_comm, smul_mul_assoc, ← smul_add, y1, smul_zero, mul_zero, zero_mul]
  · by_contra hab
    obtain ⟨c, d, k1, k2, k3⟩ := key a b hab
    have k4 : Φ.blk c = Φ.blk d := by_contra fun n => k2 (y2 c d n)
    apply e
    rw [h2 s a c k1, k4, h2 s⁻¹ d b k3, map_inv]
    simp
  · by_contra hab
    obtain ⟨c, d, k1, k2, k3⟩ := key a b hab
    have k4 : w c - w d = j := by_contra fun n => k2 (y3 c d n)
    have k5 : w a = w c := by_contra fun n => k1 (h3 s a c n)
    have k6 : w d = w b := by_contra fun n => k3 (h3 s⁻¹ d b n)
    exact e (by rw [k5, ← k6, k4])

variable {Φ R} in

def adRep {Γ : Type} [Group Γ] {ρ : Γ →* Matrix ι ι R} (h : Φ.Normalises ρ) (j : X) :
    Representation R Γ (Φ.gw R j) where
  toFun s :=
    { toFun := fun Y => ⟨ρ s * Y.1 * ρ s⁻¹, ad_mem h j s Y.2⟩
      map_add' := fun Y Y' => Subtype.ext (by simp [mul_add, add_mul])
      map_smul' := fun c Y => Subtype.ext (by simp) }
  map_one' := LinearMap.ext fun Y => Subtype.ext (by simp)
  map_mul' s t := LinearMap.ext fun Y => Subtype.ext (by simp [mul_assoc])

variable [IsLocalRing O]

variable {R} in

def HH [IsCO O R] (h : Matrix ι ι R) : Prop :=
  hᵀ * Φ.JR R * h = Φ.JR R ∧ (∀ a b, Φ.blk a ≠ Φ.blk b → h a b = 0) ∧ h.map (res O R) = 1

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {rbar : Γ →* Matrix ι ι (ResidueField O)}

def InH (r0 : Γ →* Matrix ι ι O) : Cond O rbar :=
  fun R _ _ _ r => ∀ s, Φ.HH (r.hom s * (r0 s⁻¹).map (algebraMap O R))

structure IsLocCond (r0 : Γ →* Matrix ι ι O) (N : Subgroup Γ) (L : Cond O rbar) : Prop where
  closed : ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r : Lift O rbar R), Φ.InH r0 R r → ∃ I : Ideal R,
    ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R'), L R' (r.map f) ↔ ∀ x ∈ I, f x = 0
  conj : ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r r' : Lift O rbar R) (h : Matrix ι ι R),
    Φ.InH r0 R r → Φ.HH h → (∀ s, r'.hom s * h = h * r.hom s) → L R r → L R r'
  torus : ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r r' : Lift O rbar R) (t : Multiplicative X →* Rˣ),
    Φ.InH r0 R r → (∀ j, res O R (t j) = 1) → IsTorusConj w t r r' → L R r → L R r'
  lift : ∀ (R R' : Type) [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R']
    (p : R →ₐ[O] R'), Function.Surjective p → maximalIdeal R * RingHom.ker p = ⊥ →
    ∀ r' : Lift O rbar R', Φ.InH r0 R' r' → L R' r' → ∃ r : Lift O rbar R, Φ.InH r0 R r ∧ L R r ∧ r.map p = r'
  tangent : ∀ (R R' : Type) [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R']
    (p : R →ₐ[O] R'), Function.Surjective p → maximalIdeal R * RingHom.ker p = ⊥ →
    ∀ r₁ r₂ : Lift O rbar R, Φ.InH r0 R r₁ → Φ.InH r0 R r₂ → r₁.map p = r₂.map p → L R r₁ →
      (L R r₂ ↔ ∀ n ∈ N, r₂.hom n = r₁.hom n)

end FormData

def killCond {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [Fintype ι]
    [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) (N : Set Γ) : Cond O rbar :=
  fun _ _ _ _ r => ∀ n ∈ N, r.hom n = 1

def Cond.IsClosed {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [Fintype ι]
    [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)} (P : Cond O rbar) : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r : Lift O rbar R), ∃ I : Ideal R,
    ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R'), P R' (r.map f) ↔ ∀ x ∈ I, f x = 0

structure Frame (Γ : Type) [Group Γ] [TopologicalSpace Γ] where
  T : Type
  [fT : Fintype T]
  v0 : T
  Gv : T → Type
  [gv : ∀ v, Group (Gv v)]
  [tv : ∀ v, TopologicalSpace (Gv v)]
  φ : ∀ v, Gv v →* Γ
  hφ : ∀ v, Continuous (φ v)
  Q : Type
  [fQ : Fintype Q]
  Gq : Q → Type
  [gq : ∀ q, Group (Gq q)]
  [tq : ∀ q, TopologicalSpace (Gq q)]
  ψ : ∀ q, Gq q →* Γ
  hψ : ∀ q, Continuous (ψ q)
  N : ∀ q, Subgroup (Gq q)

attribute [instance] Frame.fT Frame.gv Frame.tv Frame.fQ Frame.gq Frame.tq

def dOne {k G M : Type} [CommRing k] [Group G] [AddCommGroup M] [Module k M] (ρ : Representation k G M) (a : G → M) :
    G × G → M := fun p => a p.1 + ρ p.1 (a p.2) - a (p.1 * p.2)

namespace Frame

variable {k Γ M : Type} [CommRing k] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module k M] (F : Frame Γ)
  (ρ : Representation k Γ M)

def H1c : Submodule k ((Γ → M) × (F.T → M)) where
  carrier := {x | IsLocallyConstant x.1 ∧ (∀ s t, x.1 (s * t) = x.1 s + ρ s (x.1 t)) ∧
    (∀ q, ∀ n ∈ F.N q, x.1 (F.ψ q n) = 0) ∧ (∀ v s, x.1 (F.φ v s) = ρ (F.φ v s) (x.2 v) - x.2 v) ∧ x.2 F.v0 = 0}
  add_mem' := by
    rintro x y ⟨a1, a2, a3, a4, a5⟩ ⟨b1, b2, b3, b4, b5⟩
    refine ⟨a1.add b1, fun s t => ?_, fun q n h => ?_, fun v s => ?_, ?_⟩
    · simp only [Prod.fst_add, Pi.add_apply, a2, b2, map_add]; abel
    · simp [a3 q n h, b3 q n h]
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, a4, b4, map_add]; abel
    · simp [a5, b5]
  zero_mem' := ⟨IsLocallyConstant.const 0, by simp, by simp, by simp, rfl⟩
  smul_mem' := by
    rintro c x ⟨a1, a2, a3, a4, a5⟩
    refine ⟨a1.comp (c • ·), fun s t => ?_, fun q n h => ?_, fun v s => ?_, ?_⟩
    · simp [a2]
    · simp [a3 q n h]
    · simp [a4, smul_sub]
    · simp [a5]

abbrev C2 (M : Type) : Type := (Γ × Γ → M) × (∀ v, F.Gv v → M) × (∀ q, F.Gq q → M)

def framedTwoCocycles : Submodule k (F.C2 M) where
  carrier := {x | IsLocallyConstant x.1 ∧ (∀ v, IsLocallyConstant (x.2.1 v)) ∧ (∀ q, IsLocallyConstant (x.2.2 q)) ∧
    (∀ s t u, ρ s (x.1 (t, u)) + x.1 (s, t * u) = x.1 (s * t, u) + x.1 (s, t)) ∧
    (∀ v s t, x.1 (F.φ v s, F.φ v t) = dOne (ρ.comp (F.φ v)) (x.2.1 v) (s, t)) ∧
    ∀ q s t, x.1 (F.ψ q s, F.ψ q t) = dOne (ρ.comp (F.ψ q)) (x.2.2 q) (s, t)}
  add_mem' := by
    rintro x y ⟨a1, a2, a3, a4, a5, a6⟩ ⟨b1, b2, b3, b4, b5, b6⟩
    refine ⟨a1.add b1, fun v => (a2 v).add (b2 v), fun q => (a3 q).add (b3 q), fun s t u => ?_, fun v s t => ?_,
      fun q s t => ?_⟩
    · simp only [Prod.fst_add, Pi.add_apply, map_add]
      rw [add_add_add_comm, a4, b4, add_add_add_comm]
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, a5, b5, dOne, map_add]; abel
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, a6, b6, dOne, map_add]; abel
  zero_mem' := ⟨IsLocallyConstant.const 0, fun _ => IsLocallyConstant.const 0, fun _ => IsLocallyConstant.const 0,
    by simp, by simp [dOne], by simp [dOne]⟩
  smul_mem' := by
    rintro c x ⟨a1, a2, a3, a4, a5, a6⟩
    refine ⟨a1.comp (c • ·), fun v => (a2 v).comp (c • ·), fun q => (a3 q).comp (c • ·), fun s t u => ?_,
      fun v s t => ?_, fun q s t => ?_⟩
    · simp only [Prod.smul_fst, Pi.smul_apply, map_smul, ← smul_add, a4]
    · simp [a5, dOne, smul_sub]
    · simp [a6, dOne, smul_sub]

def framedTwoCoboundaries : Submodule k (F.C2 M) :=
  Submodule.span k {x | ∃ (h : Γ → M) (y : F.T → M) (e : ∀ q, F.Gq q → M), IsLocallyConstant h ∧
    (∀ q, IsLocallyConstant (e q) ∧ (∀ s t, e q (s * t) = e q s + ρ (F.ψ q s) (e q t)) ∧ ∀ n ∈ F.N q, e q n = 0) ∧
    x.1 = dOne ρ h ∧ (∀ v s, x.2.1 v s = h (F.φ v s) - (ρ (F.φ v s) (y v) - y v)) ∧
    ∀ q s, x.2.2 q s = h (F.ψ q s) - e q s}

abbrev Ob : Type := F.framedTwoCocycles ρ ⧸ (F.framedTwoCoboundaries ρ).comap (F.framedTwoCocycles ρ).subtype

end Frame

section P

variable {O : Type} [CommRing O] [IsLocalRing O] {ι X : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup X] {w : ι → X}
  (Φ : FormData O w) {Γ : Type} [Group Γ] [TopologicalSpace Γ] {rbar : Γ →* Matrix ι ι (ResidueField O)}
  (r0 : Γ →* Matrix ι ι O) (F : Frame Γ) (L : ∀ q, Cond O (rbar.comp (F.ψ q)))
  {B : Type} [CommRing B] [Algebra O B] [IsCO O B] (ρ : ∀ v, Lift O (rbar.comp (F.φ v)) B)

def IsFramed {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (i : B →ₐ[O] R) (r : Lift O rbar R)
    (α : F.T → Matrix ι ι R) : Prop :=
  Φ.InH r0 R r ∧ (∀ q, L q R (r.comap (F.ψ q) (F.hψ q))) ∧ (∀ v, Φ.HH (α v)) ∧ α F.v0 = 1 ∧
    ∀ v s, r.hom (F.φ v s) * α v = α v * ((ρ v).hom s).map i

def IsUnivFramed {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (i : B →ₐ[O] R) (r : Lift O rbar R)
    (α : F.T → Matrix ι ι R) : Prop :=
  IsFramed Φ r0 F L ρ i r α ∧
  ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (i' : B →ₐ[O] R') (r' : Lift O rbar R')
    (α' : F.T → Matrix ι ι R'), IsFramed Φ r0 F L ρ i' r' α' →
    ∃! f : R →ₐ[O] R', f.comp i = i' ∧ r.map f = r' ∧ ∀ v, (α v).map f = α' v

end P

def IsRelPres {O X B R : Type} [CommRing O] [AddCommGroup X] [CommRing B] [Algebra O B] [CommRing R] [Algebra O R]
    (WB : WPres O X B) (i : B →ₐ[O] R) (W : WPres O X R) {τ κ : Type} (e : WB.σ ⊕ τ ≃ W.σ)
    (f : κ → MvPowerSeries W.σ O) (wf : κ → X) : Prop :=
  (∀ s, W.wt (e (.inl s)) = WB.wt s) ∧
  (∀ x, W.π (MvPowerSeries.rename (fun s => e (.inl s)) x) = i (WB.π x)) ∧
  (∀ u, f u ∈ wtPart O W.wt (wf u)) ∧
  RingHom.ker W.π = (RingHom.ker WB.π).map (MvPowerSeries.rename (fun s => e (.inl s))) ⊔ Ideal.span (Set.range f)

def LemmaP : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l], l ≠ 2 →
  ∀ (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (w : ι → X)
    (Φ : FormData O w) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [TotallyDisconnectedSpace Γ] [T2Space Γ], PhiCond Γ l →
  ∀ (rbar : Γ →* Matrix ι ι (ResidueField O)) (r0 : Lift O rbar O) (hbar : Φ.Normalises rbar), Φ.Normalises r0.hom →
  ∀ (F : Frame Γ) (L : ∀ q, Cond O (rbar.comp (F.ψ q))), (∀ q, ∀ n ∈ F.N q, rbar (F.ψ q n) = 1) →
    (∀ q, Φ.IsLocCond (r0.hom.comp (F.ψ q)) (F.N q) (L q)) → (∀ q, L q O (r0.comap (F.ψ q) (F.hψ q))) →
    (∀ j, Module.Finite (ResidueField O) (F.Ob (FormData.adRep hbar j))) →
  ∀ (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (WB : WPres O X B) (ρ : ∀ v, Lift O (rbar.comp (F.φ v)) B),
    (∀ s, WB.z s ∈ maximalIdeal B) → (∀ v, Φ.InH (r0.hom.comp (F.φ v)) B (ρ v)) →
    (∀ v s a b, (ρ v).hom s a b ∈ WB.part (w a - w b)) →
  ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (i : B →ₐ[O] R) (r : Lift O rbar R)
    (α : F.T → Matrix ι ι R) (W : WPres O X R) (τ κ : Type) (_ : Fintype τ) (_ : Fintype κ) (e : WB.σ ⊕ τ ≃ W.σ)
    (f : κ → MvPowerSeries W.σ O) (wf : κ → X),
    IsUnivFramed Φ r0.hom F L ρ i r α ∧ IsRelPres WB i W e f wf ∧
    (∀ s a b, r.hom s a b ∈ W.part (w a - w b)) ∧ (∀ v a b, α v a b ∈ W.part (w a - w b)) ∧
    (∀ t, ∃ a b, W.wt (e (.inr t)) = w a - w b ∧
      ((∃ s, W.z (e (.inr t)) = r.hom s a b - algebraMap O R (r0.hom s a b)) ∨
        ∃ v, W.z (e (.inr t)) = (α v - 1) a b)) ∧
    (∀ j, Nat.card {t // W.wt (e (.inr t)) = j} =
      Module.finrank (ResidueField O) (F.H1c (FormData.adRep hbar j))) ∧
    ∀ j, Nat.card {u // wf u = j} = Module.finrank (ResidueField O) (F.Ob (FormData.adRep hbar j))

end UpperTheory.V.Alg
