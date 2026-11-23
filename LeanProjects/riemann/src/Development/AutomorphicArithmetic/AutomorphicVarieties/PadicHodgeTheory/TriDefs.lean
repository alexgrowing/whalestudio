import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic

noncomputable section

namespace UpperTheory.V.Loc

open Formalism.BasicNotions Formalism.BasicNotions.Loc UpperTheory.V.U3 ReciprocityTheory.Gal

section Alg

variable {G B : Type} [Group G] [CommRing B]

def triM (t : Fin 3 → Bˣ) (x y z : B) : Matrix (Fin 3) (Fin 3) B :=
  !![(t 0 : B), x * t 1, z * t 2; 0, t 1, y * t 2; 0, 0, t 2]

structure Tor (η : G →* ℤˣ) (B : Type) [CommRing B] where
  t : G → Fin 3 → Bˣ
  mul : ∀ g h i, t (g * h) i = t g i * if η g = 1 then t h i else (t h i.rev)⁻¹

def omg (v w : B × B) : B := v.1 * w.2 - v.2 * w.1

def ext2 (a b : G →* Bˣ) (x : G → B) (hx : ∀ g h, x (g * h) = x g + ((a / b) g : Bˣ) * x h) :
    Representation B G (B × B) where
  toFun g :=
    { toFun := fun v => ((a g : B) * v.1 + x g * b g * v.2, (b g : B) * v.2)
      map_add' := fun v w => by ext <;> simp <;> ring
      map_smul' := fun c v => by ext <;> simp <;> ring }
  map_one' := by
    have h := hx 1 1
    simp only [mul_one, map_one, Units.val_one, one_mul, left_eq_add] at h
    refine LinearMap.ext fun v => ?_
    simp [h]
  map_mul' g h := by
    refine LinearMap.ext fun v => ?_
    have e : (((a / b) g : Bˣ) : B) * b g = a g := by
      rw [← Units.val_mul, MonoidHom.div_apply, div_mul_cancel]
    ext
    · simp only [map_mul, Units.val_mul, hx, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply, ← e]
      ring
    · simp only [map_mul, Units.val_mul, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply]
      ring

theorem characterExtensionRep_apply (a b : G →* Bˣ) (x : G → B) (hx : ∀ g h, x (g * h) = x g + ((a / b) g : Bˣ) * x h) (g : G)
    (v : B × B) : ext2 a b x hx g v = ((a g : B) * v.1 + x g * b g * v.2, (b g : B) * v.2) := rfl

theorem chRep_apply (a : G →* Bˣ) (g : G) (v : B) : chRep a g v = (a g : B) * v := rfl

theorem twist_apply {V : Type} [AddCommGroup V] [Module B V] (a : G →* Bˣ) (ρ : Representation B G V) (g : G)
    (v : V) : twist a ρ g v = (a g : B) • ρ g v := rfl

theorem colRep_apply {n : Type} [Fintype n] [DecidableEq n] (r : G →* GL n B) (g : G) (v : n → B) :
    colRep r g v = (r g : Matrix n n B).mulVec v := rfl

namespace Tor

variable {η : G →* ℤˣ} (T : Tor η B)

theorem t_one (i : Fin 3) : T.t 1 i = 1 := by
  have h := T.mul 1 1 i
  simpa using h

def M1 : Representation B G (B × B) where
  toFun g :=
    { toFun := fun v => if η g = 1 then (((T.t g 0 / T.t g 1 : Bˣ) : B) * v.1, ((T.t g 1 / T.t g 2 : Bˣ) : B) * v.2)
        else (-(((T.t g 0 / T.t g 1 : Bˣ) : B) * v.2), -(((T.t g 1 / T.t g 2 : Bˣ) : B) * v.1))
      map_add' := fun v w => by split_ifs <;> ext <;> simp <;> ring
      map_smul' := fun c v => by split_ifs <;> ext <;> simp <;> ring }
  map_one' := by
    refine LinearMap.ext fun v => ?_
    simp [T.t_one]
  map_mul' g h := by
    refine LinearMap.ext fun v => ?_
    have hn : ((-1 : ℤˣ) = 1) = False := by decide
    have r0 : (0 : Fin 3).rev = 2 := rfl
    have r1 : (1 : Fin 3).rev = 1 := rfl
    have r2 : (2 : Fin 3).rev = 0 := rfl
    rcases Int.units_eq_one_or (η g) with hg | hg <;> rcases Int.units_eq_one_or (η h) with hh | hh <;>
      simp only [map_mul, T.mul, hg, hh, hn, r0, r1, r2, if_true, if_false, mul_one, one_mul, neg_mul_neg,
        LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply, div_eq_mul_inv, mul_inv, inv_inv, Units.val_mul] <;>
      ext <;> simp only [] <;> ring

theorem adjointSuperdiagRep_apply (g : G) (v : B × B) : T.M1 g v =
    if η g = 1 then (((T.t g 0 / T.t g 1 : Bˣ) : B) * v.1, ((T.t g 1 / T.t g 2 : Bˣ) : B) * v.2)
      else (-(((T.t g 0 / T.t g 1 : Bˣ) : B) * v.2), -(((T.t g 1 / T.t g 2 : Bˣ) : B) * v.1)) := rfl

def χ2 : G →* Bˣ where
  toFun g := Units.map (Int.castRingHom B : ℤ →* B) (η g) * (T.t g 0 / T.t g 2)
  map_one' := by simp [T.t_one]
  map_mul' g h := by
    have r0 : (0 : Fin 3).rev = 2 := rfl
    have r2 : (2 : Fin 3).rev = 0 := rfl
    simp only [map_mul, T.mul, r0, r2]
    split_ifs <;> simp only [div_eq_mul_inv, mul_inv, inv_inv] <;> ac_rfl

theorem χ2_apply (g : G) : (T.χ2 g : B) = ((η g : ℤ) : B) * ((T.t g 0 / T.t g 2 : Bˣ) : B) := rfl

theorem alternatingForm_adjointSuperdiagRep (g : G) (v w : B × B) : omg (T.M1 g v) (T.M1 g w) = T.χ2 g * omg v w := by
  have e : ((T.t g 0 / T.t g 2 : Bˣ) : B) = ((T.t g 0 / T.t g 1 : Bˣ) : B) * ((T.t g 1 / T.t g 2 : Bˣ) : B) := by
    rw [← Units.val_mul, div_mul_div_cancel]
  have hn : ((-1 : ℤˣ) = 1) = False := by decide
  rcases Int.units_eq_one_or (η g) with hg | hg <;>
    simp only [adjointSuperdiagRep_apply, χ2_apply, hg, hn, if_true, if_false, omg, e, Units.val_one, Units.val_neg, Int.cast_one,
      Int.cast_neg] <;> ring

def ch (H : Subgroup G) (hH : ∀ g ∈ H, η g = 1) (i : Fin 3) : H →* Bˣ where
  toFun g := T.t g i
  map_one' := T.t_one i
  map_mul' g h := by rw [Subgroup.coe_mul, T.mul, if_pos (hH g g.2)]

theorem ch_apply (H : Subgroup G) (hH : ∀ g ∈ H, η g = 1) (i : Fin 3) (g : H) : T.ch H hH i g = T.t g i := rfl

def IsGam (h : B) (β : G → B × B) (γ : G → B) : Prop :=
  ∀ g g', γ (g * g') = γ g + T.χ2 g * γ g' + h * omg (β g) (T.M1 g (β g'))

structure Coord (h : B) (β : G → B × B) (γ : G → B) (u : G →* GG 3 B) : Prop where
  right : ∀ g, (u g).right = η g
  mat : ∀ g, (u g).mat = triM (T.t g) (β g).1 (β g).2 (γ g + h * (β g).1 * (β g).2)

end Tor

end Alg

section Top

variable {G B : Type} [Group G] [TopologicalSpace G] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

theorem cont_char_inv [IsTopologicalGroup G] {a : G →* Bˣ} (ha : Continuous fun g => (a g : B)) :
    Continuous fun g => ((a⁻¹ g : Bˣ) : B) := by
  simp only [MonoidHom.inv_apply, ← map_inv]
  exact ha.comp continuous_inv

theorem cont_char_div [IsTopologicalGroup G] {a b : G →* Bˣ} (ha : Continuous fun g => (a g : B))
    (hb : Continuous fun g => (b g : B)) : Continuous fun g => (((a / b) g : Bˣ) : B) := by
  simp only [div_eq_mul_inv, MonoidHom.mul_apply, Units.val_mul]
  exact ha.mul (cont_char_inv hb)

theorem contAction_chRep {a : G →* Bˣ} (ha : Continuous fun g => (a g : B)) : ContAction (chRep a) :=
  (ha.comp continuous_fst).mul continuous_snd

theorem contAction_twist {V : Type} [AddCommGroup V] [Module B V] [TopologicalSpace V] [ContinuousSMul B V]
    {a : G →* Bˣ} (ha : Continuous fun g => (a g : B)) {ρ : Representation B G V} (hρ : ContAction ρ) :
    ContAction (twist a ρ) :=
  (ha.comp continuous_fst).smul hρ

theorem contAction_charExtension_of_continuous_cocycle {a b : G →* Bˣ} (ha : Continuous fun g => (a g : B)) (hb : Continuous fun g => (b g : B))
    {x : G → B} (hx : ∀ g h, x (g * h) = x g + ((a / b) g : Bˣ) * x h) (hc : Continuous x) :
    ContAction (ext2 a b x hx) := by
  unfold ReciprocityTheory.Gal.ContAction
  simp only [characterExtensionRep_apply]
  have p1 : Continuous fun p : G × B × B => p.2.1 := by fun_prop
  have p2 : Continuous fun p : G × B × B => p.2.2 := by fun_prop
  exact (((ha.comp continuous_fst).mul p1).add
    (((hc.comp continuous_fst).mul (hb.comp continuous_fst)).mul p2)).prodMk ((hb.comp continuous_fst).mul p2)

theorem contAction_colRep {n : Type} [Fintype n] [DecidableEq n] {r : G →* GL n B}
    (hr : Continuous fun g => (r g : Matrix n n B)) : ContAction (colRep r) :=
  Continuous.matrix_mulVec (hr.comp continuous_fst) continuous_snd

theorem continuous_triM {X : Type} [TopologicalSpace X] {t : X → Fin 3 → Bˣ} {x y z : X → B}
    (ht : ∀ i, Continuous fun g => (t g i : B)) (hx : Continuous x) (hy : Continuous y) (hz : Continuous z) :
    Continuous fun g => triM (t g) (x g) (y g) (z g) := by
  refine continuous_matrix fun i j => ?_
  have h0 := ht 0
  have h1 := ht 1
  have h2 := ht 2
  fin_cases i <;> fin_cases j <;> simp [triM] <;> fun_prop

theorem Tor.contAction_torus_module {η : G →* ℤˣ} (hη : IsLocallyConstant η) (T : Tor η B)
    (ht : ∀ i, Continuous fun g => (T.t g i : B)) (hi : ∀ i, Continuous fun g => (((T.t g i)⁻¹ : Bˣ) : B)) :
    ContAction T.M1 := by
  unfold ReciprocityTheory.Gal.ContAction
  simp only [Tor.adjointSuperdiagRep_apply, div_eq_mul_inv, Units.val_mul]
  have p1 : Continuous fun p : G × B × B => p.2.1 := by fun_prop
  have p2 : Continuous fun p : G × B × B => p.2.2 := by fun_prop
  have a := ((ht 0).mul (hi 1)).comp (continuous_fst : Continuous fun p : G × B × B => p.1)
  have b := ((ht 1).mul (hi 2)).comp (continuous_fst : Continuous fun p : G × B × B => p.1)
  refine Continuous.if ?_ ((a.mul p1).prodMk (b.mul p2)) ((a.mul p2).neg.prodMk (b.mul p1).neg)
  intro p hp
  have : IsClopen {p : G × B × B | η p.1 = 1} := (hη.comp_continuous continuous_fst).isClopen_fiber 1
  rw [this.frontier_eq] at hp
  exact hp.elim

theorem Tor.continuous_χ2 {η : G →* ℤˣ} (hη : IsLocallyConstant η) (T : Tor η B)
    (ht : ∀ i, Continuous fun g => (T.t g i : B)) (hi : ∀ i, Continuous fun g => (((T.t g i)⁻¹ : Bˣ) : B)) :
    Continuous fun g => (T.χ2 g : B) := by
  simp only [Tor.χ2_apply, div_eq_mul_inv, Units.val_mul]
  exact (hη.comp fun s : ℤˣ => ((s : ℤ) : B)).continuous.mul ((ht 0).mul (hi 2))

theorem contConstSMul_alg (E : Type) [CommRing E] [Algebra E B] : ContinuousConstSMul E B :=
  ⟨fun c => by simp only [Algebra.smul_def]; fun_prop⟩

end Top

section admitted

variable {l : ℕ} [Fact l.Prime]

theorem crOn_top {G A V : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (φ : G →* GQ l) (ρ : Representation A G V) :
    CrOn φ ρ ⊤ ↔ IsCr φ ρ := by
  have h1 : (φ.comp (⊤ : Subgroup G).subtype).range = φ.range := by
    ext x
    simp
  have h2 : Dcr (φ.comp (⊤ : Subgroup G).subtype)
      (resCoef ℚ_[l] (ρ.comp (⊤ : Subgroup G).subtype : Representation A (⊤ : Subgroup G) V)) =
      Dcr φ (resCoef ℚ_[l] ρ) := by
    ext x
    simp only [Dcr, Submodule.mem_iInf]
    exact ⟨fun h g => h ⟨g, trivial⟩, fun h g => h g⟩
  unfold CrOn IsCr
  rw [h1, h2]

def LCr {B : Type} [CommRing B] [Algebra ℚ_[l] B] (H : Subgroup (GQ l)) (u : GQ l →* GG 3 B) : Prop :=
  ∃ ρ : ↥H →* GL (Fin 3) B, (∀ g, ρ g = (u g).left) ∧ IsCr H.subtype (colRep ρ)

variable {E : Type} [Field E] [Algebra ℚ_[l] E] [Algebra ℤ_[l] E]

structure TriDat (η : GQ l →* ℤˣ) (Ψ : GQ l →* Eˣ) (H : Subgroup (GQ l)) (e : ℕ) : Prop where
  normal : H.Normal
  isOpen : IsOpen (H : Set (GQ l))
  fin : H.FiniteIndex
  ηH : ∀ g ∈ H, η g = 1
  ηI : ∀ g ∈ Iq l, η g = 1
  ηlc : IsLocallyConstant η
  e_pos : 1 ≤ e
  ΨH : ∀ g ∈ H, g ∈ Iq l → Ψ g = cycA l l E g ^ e
  Ψc : QCont l fun g => (Ψ g : E)

variable {B : Type} [CommRing B] [Algebra E B] [TopologicalSpace B]

structure Tor.Good {η : GQ l →* ℤˣ} (T : Tor η B) (π : B →ₐ[E] E) (Ψ : GQ l →* Eˣ) : Prop where
  cont : ∀ i, Continuous fun g => (T.t g i : B)
  cont_inv : ∀ i, Continuous fun g => (((T.t g i)⁻¹ : Bˣ) : B)
  ine : ∀ g ∈ Iq l, ∀ i, (T.t g i : B) = algebraMap E B ((Ψ g ^ wt1 i : Eˣ) : E)
  red : ∀ g i, π (T.t g i : B) = ((Ψ g ^ wt1 i : Eˣ) : E)

structure Chars [Algebra ℤ_[l] B] {G : Type} [Group G] [TopologicalSpace G] (φ : G →* GQ l) (π : B →ₐ[E] E) (e : ℕ)
    (ψ : G →* Eˣ) (κ : Fin 3 → G →* Bˣ) : Prop where
  e_pos : 1 ≤ e
  cont : ∀ i, Continuous fun g => (κ i g : B)
  ine : ∀ g, φ g ∈ Iq l → ∀ i, κ i g = cycA l l B (φ g) ^ ((e : ℤ) * wt1 i)
  red : ∀ g i, π (κ i g : B) = ((ψ g ^ wt1 i : Eˣ) : E)
  wt : ∀ g, φ g ∈ Iq l → ψ g = cycA l l E (φ g) ^ e

omit [TopologicalSpace B] in
theorem algebraMap_cycA [Algebra ℚ_[l] B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] E]
    [IsScalarTower ℚ_[l] E B] (g : GQ l) : Units.map (algebraMap E B : E →* B) (cycA l l E g) = cycA l l B g := by
  apply Units.ext
  change algebraMap E B (algebraMap ℤ_[l] E _) = algebraMap ℤ_[l] B _
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B,
    ← IsScalarTower.algebraMap_apply ℚ_[l] E B]

theorem Tor.Good.chars [Algebra ℚ_[l] B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] E]
    [IsScalarTower ℚ_[l] E B] {η : GQ l →* ℤˣ} {T : Tor η B} {π : B →ₐ[E] E} {Ψ : GQ l →* Eˣ} (hT : T.Good π Ψ)
    {H : Subgroup (GQ l)} {e : ℕ} (hD : TriDat η Ψ H e) :
    Chars H.subtype π e (Ψ.comp H.subtype) (T.ch H hD.ηH) where
  e_pos := hD.e_pos
  cont i := (hT.cont i).comp continuous_subtype_val
  ine g hg i := by
    apply Units.ext
    rw [Tor.ch_apply, hT.ine g hg, hD.ΨH g g.2 hg, ← algebraMap_cycA (E := E) (B := B), zpow_mul, zpow_natCast, ← map_pow (Units.map _),
      ← map_zpow (Units.map (algebraMap E B : E →* B))]
    rfl
  red g i := hT.red g i
  wt g hg := hD.ΨH g g.2 hg

end admitted

end UpperTheory.V.Loc
