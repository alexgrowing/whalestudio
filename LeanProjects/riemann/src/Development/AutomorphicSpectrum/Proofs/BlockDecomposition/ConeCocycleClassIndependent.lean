import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedLogMultiplicative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeLiftRatioMemIdeal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeZcls

section Gen
variable {X : Scheme.{0}} {D : E.LineData X}

def ub {A : Type} [CommRing A] (a b : Spec (CommRingCat.of A) ⟶ D.Y) (h : a ≫ D.f = b ≫ D.f) : A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (D.u a b h : Γ(Spec (CommRingCat.of A), ⊤))

theorem ub_mul {A : Type} [CommRing A] (a b c : Spec (CommRingCat.of A) ⟶ D.Y) (h : a ≫ D.f = b ≫ D.f)
    (h' : b ≫ D.f = c ≫ D.f) : ub a b h * ub b c h' = ub a c (h.trans h') := by
  unfold ub
  rw [← map_mul, ← Units.val_mul, D.coc]

theorem ub_isUnit {A : Type} [CommRing A] (a b : Spec (CommRingCat.of A) ⟶ D.Y) (h : a ≫ D.f = b ≫ D.f) :
    IsUnit (ub a b h) :=
  (D.u a b h).isUnit.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom

theorem ub_nat {A A' : Type} [CommRing A] [CommRing A'] (ρ : A →+* A') (a b : Spec (CommRingCat.of A) ⟶ D.Y)
    (h : a ≫ D.f = b ≫ D.f) (h' : (Spec.map (CommRingCat.ofHom ρ) ≫ a) ≫ D.f = (Spec.map (CommRingCat.ofHom ρ) ≫ b) ≫ D.f) :
    ub (Spec.map (CommRingCat.ofHom ρ) ≫ a) (Spec.map (CommRingCat.ofHom ρ) ≫ b) h' = ρ (ub a b h) := by
  unfold ub
  rw [D.nat (Spec.map (CommRingCat.ofHom ρ)) a b h]
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ρ)
  exact congrArg (fun t => t.hom (D.u a b h : Γ(Spec (CommRingCat.of A), ⊤))) e

end Gen

section T
variable {K : Type} [Field K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem pt_map {T T' : Thick (smFun X q)} (f : T ⟶ T') :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J f.φ f.hle)) ≫ pt T = pt T' :=
  congrArg (fun z => z.1.2) f.pt

theorem J_nil (T : Thick (smFun X q)) : IsNilpotent T.J := T.adm.2 rfl

theorem exists_unit_lift (T : Thick (smFun X q)) (x : T.B ⧸ T.J) (hx : IsUnit x) :
    ∃ v : T.Bˣ, Ideal.Quotient.mk T.J (v : T.B) = x := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : T.B ⧸ T.J)
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective ((u⁻¹ : (T.B ⧸ T.J)ˣ) : T.B ⧸ T.J)
  have hab : a * b - 1 ∈ T.J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ha, hb, Units.mul_inv, map_one, sub_self]
  have hn : IsNilpotent (a * b - 1) := by
    obtain ⟨n, hn⟩ := J_nil T
    refine ⟨n, ?_⟩
    have : (a * b - 1) ^ n ∈ T.J ^ n := Ideal.pow_mem_pow hab n
    rw [hn] at this
    simpa using this
  have hu : IsUnit (a * b) := by
    have := hn.isUnit_one_add
    simpa using this
  exact ⟨(isUnit_of_mul_isUnit_left hu).unit, by simpa using ha⟩

theorem nat_unit (T : Thick (smFun X q)) [CharZero K] (n : ℕ) (hn : n ≠ 0) : IsUnit ((n : T.B)) := by
  have : ((n : T.B)) = T.i (n : K) := by simp
  rw [this]
  exact (IsUnit.mk0 (n : K) (by exact_mod_cast hn)).map T.i

end T

section L
variable {K : Type} [Field K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {C : Type 1} [Category.{0} C]
  {g : C ⥤ Thick (smFun X q)} {D : E.LineData X}

def eps (Λ Λ' : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) {c c' : C} (φ : c ⟶ c') : (g.obj c').Bˣ :=
  Λ'.w φ * Units.map (g.map φ).φ.toMonoidHom (v c) * (Λ.w φ)⁻¹ * (v c')⁻¹

theorem eps_sub (Λ Λ' : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ)
    (hv : ∀ c, Ideal.Quotient.mk (g.obj c).J ((v c : (g.obj c).Bˣ) : (g.obj c).B) =
      ub (Λ.p c) (Λ'.p c) ((Λ.hp c).trans (Λ'.hp c).symm)) {c c' : C} (φ : c ⟶ c') :
    ((eps Λ Λ' v φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J := by
  set qm := Ideal.quotientMap (g.obj c').J (g.map φ).φ (g.map φ).hle with hqm
  have hpt := pt_map (g.map φ)
  have h1 : (Spec.map (CommRingCat.ofHom qm) ≫ Λ.p c) ≫ D.f = Λ.p c' ≫ D.f := by
    rw [Category.assoc, Λ.hp, Λ.hp, hpt]
  have h1' : (Spec.map (CommRingCat.ofHom qm) ≫ Λ'.p c) ≫ D.f = Λ'.p c' ≫ D.f := by
    rw [Category.assoc, Λ'.hp, Λ'.hp, hpt]
  have hw : Ideal.Quotient.mk (g.obj c').J ((Λ.w φ : (g.obj c').Bˣ) : (g.obj c').B) = ub _ _ h1 := Λ.hw φ h1
  have hw' : Ideal.Quotient.mk (g.obj c').J ((Λ'.w φ : (g.obj c').Bˣ) : (g.obj c').B) = ub _ _ h1' := Λ'.hw φ h1'
  have e : eps Λ Λ' v φ * Λ.w φ * v c' = Λ'.w φ * Units.map (g.map φ).φ.toMonoidHom (v c) := by
    unfold eps
    rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc]
    simp
  have e' := congrArg (fun u : (g.obj c').Bˣ => Ideal.Quotient.mk (g.obj c').J (u : (g.obj c').B)) e
  simp only [Units.val_mul, map_mul] at e'
  have hm : Ideal.Quotient.mk (g.obj c').J ((Units.map (g.map φ).φ.toMonoidHom (v c) : (g.obj c').Bˣ) : (g.obj c').B) =
      qm (Ideal.Quotient.mk (g.obj c).J ((v c : (g.obj c).Bˣ) : (g.obj c).B)) := rfl
  rw [hm, hw, hw', hv, hv, ← ub_nat qm _ _ _ (by rw [Category.assoc, Category.assoc, Λ.hp, Λ'.hp])] at e'
  rw [mul_assoc, ub_mul, mul_comm (ub _ _ h1'), ub_mul] at e'
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero]
  exact (IsUnit.mul_left_inj (ub_isUnit _ _ _)).1 (e'.trans (one_mul _).symm)

theorem grpA {G : Type} [AddCommGroup G] (a b c d p q r t v : G) :
    a + p + -r = (c + q + -t) + (a + b + -c + -d) + (p + d + -q + -v) + -(r + b + -t + -v) := by abel

theorem grp {G : Type} [CommGroup G] (a b c d p q r t v : G) :
    a * p * r⁻¹ = (c * q * t⁻¹) * (a * b * c⁻¹ * d⁻¹) * (p * d * q⁻¹ * v⁻¹) * (r * b * t⁻¹ * v⁻¹)⁻¹ :=
  @grpA (Additive G) _ a b c d p q r t v

def rr (Λ : CLiftK g D) {c₀ c₁ c₂ : C} (φ : c₀ ⟶ c₁) (ψ : c₁ ⟶ c₂) (χ : c₀ ⟶ c₂) : (g.obj c₂).Bˣ :=
  Units.map (g.map ψ).φ.toMonoidHom (Λ.w φ) * Λ.w ψ * (Λ.w χ)⁻¹

theorem rr_eq (Λ Λ' : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) {c₀ c₁ c₂ : C} (φ : c₀ ⟶ c₁) (ψ : c₁ ⟶ c₂) (χ : c₀ ⟶ c₂)
    (hχ : χ = φ ≫ ψ) :
    rr Λ' φ ψ χ = rr Λ φ ψ χ * Units.map (g.map ψ).φ.toMonoidHom (eps Λ Λ' v φ) * eps Λ Λ' v ψ * (eps Λ Λ' v χ)⁻¹ := by
  subst hχ
  have h : Units.map (g.map (φ ≫ ψ)).φ.toMonoidHom (v c₀) =
      Units.map (g.map ψ).φ.toMonoidHom (Units.map (g.map φ).φ.toMonoidHom (v c₀)) := by
    rw [g.map_comp]; rfl
  unfold rr eps
  rw [h]
  simp only [map_mul, map_inv]
  exact grp _ _ _ _ _ _ _ _ _

end L

section Log
variable {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem plogK_zero {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ) : plogK δ s 0 = 0 := by
  unfold plogK
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [δ.dpow_eval_zero (Nat.succ_ne_zero k), mul_zero]

theorem plogK_map {T T' : Thick (smFun X q)} (f : T ⟶ T') (s : ℕ) {x : T.B} (hx : x ∈ T.J) :
    f.φ (plogK T.δ s x) = plogK T'.δ s (f.φ x) := by
  unfold plogK
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, map_pow, map_neg, map_one, map_natCast, f.dp.2 x hx]

theorem plog_mul (T : Thick (smFun X q)) (s : ℕ) (hs : T.pdPow s = ⊥) (a b : T.Bˣ) (ha : (a : T.B) - 1 ∈ T.J)
    (hb : (b : T.B) - 1 ∈ T.J) :
    plogK T.δ s (((a * b : T.Bˣ) : T.B) - 1) = plogK T.δ s ((a : T.B) - 1) + plogK T.δ s ((b : T.B) - 1) := by
  have := GlobalTheory.CompanionTheory.PlogMul.plogK_mul T.δ s hs (nat_unit T) ha hb
  simpa using this

theorem inv_sub (T : Thick (smFun X q)) (a : T.Bˣ) (ha : (a : T.B) - 1 ∈ T.J) :
    ((a⁻¹ : T.Bˣ) : T.B) - 1 ∈ T.J := by
  have : ((a⁻¹ : T.Bˣ) : T.B) - 1 = -(((a⁻¹ : T.Bˣ) : T.B) * ((a : T.B) - 1)) := by
    rw [mul_sub, Units.inv_mul]; ring
  rw [this]
  exact T.J.neg_mem (T.J.mul_mem_left _ ha)

theorem mul_sub_mem (T : Thick (smFun X q)) (a b : T.Bˣ) (ha : (a : T.B) - 1 ∈ T.J) (hb : (b : T.B) - 1 ∈ T.J) :
    ((a * b : T.Bˣ) : T.B) - 1 ∈ T.J := by
  have : ((a * b : T.Bˣ) : T.B) - 1 = (a : T.B) * ((b : T.B) - 1) + ((a : T.B) - 1) := by
    rw [Units.val_mul]; ring
  rw [this]
  exact T.J.add_mem (T.J.mul_mem_left _ hb) ha

theorem plog_inv (T : Thick (smFun X q)) (s : ℕ) (hs : T.pdPow s = ⊥) (a : T.Bˣ) (ha : (a : T.B) - 1 ∈ T.J) :
    plogK T.δ s (((a⁻¹ : T.Bˣ) : T.B) - 1) = -plogK T.δ s ((a : T.B) - 1) := by
  have h := plog_mul T s hs a a⁻¹ ha (inv_sub T a ha)
  rw [mul_inv_cancel, Units.val_one, sub_self, plogK_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

end Log

section Main
variable {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {C : Type 1} [Category.{0} C]
  {g : C ⥤ Thick (smFun X q)} {D : E.LineData X}

def ee (Λ Λ' : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (s : ℕ) {c c' : C} (φ : c ⟶ c') : (g.obj c').B :=
  plogK (g.obj c').δ s (((eps Λ Λ' v φ : (g.obj c').Bˣ) : (g.obj c').B) - 1)

theorem log_eq (Λ Λ' : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ)
    (hv : ∀ c, Ideal.Quotient.mk (g.obj c).J ((v c : (g.obj c).Bˣ) : (g.obj c).B) =
      ub (Λ.p c) (Λ'.p c) ((Λ.hp c).trans (Λ'.hp c).symm)) (s : ℕ) (hs : ∀ c, (g.obj c).pdPow s = ⊥)
    {c₀ c₁ c₂ : C} (φ : c₀ ⟶ c₁) (ψ : c₁ ⟶ c₂) (χ : c₀ ⟶ c₂) (hχ : χ = φ ≫ ψ)
    (hr : ((rr Λ φ ψ χ : (g.obj c₂).Bˣ) : (g.obj c₂).B) - 1 ∈ (g.obj c₂).J) :
    plogK (g.obj c₂).δ s (((rr Λ' φ ψ χ : (g.obj c₂).Bˣ) : (g.obj c₂).B) - 1) =
      plogK (g.obj c₂).δ s (((rr Λ φ ψ χ : (g.obj c₂).Bˣ) : (g.obj c₂).B) - 1) +
        ((g.map ψ).φ (ee Λ Λ' v s φ) + ee Λ Λ' v s ψ - ee Λ Λ' v s χ) := by
  have e0 := eps_sub Λ Λ' v hv φ
  have e1 := eps_sub Λ Λ' v hv ψ
  have e2 := eps_sub Λ Λ' v hv χ
  have e0' : ((Units.map (g.map ψ).φ.toMonoidHom (eps Λ Λ' v φ) : (g.obj c₂).Bˣ) : (g.obj c₂).B) - 1 ∈ (g.obj c₂).J := by
    have := (g.map ψ).hle e0
    simpa using this
  have hm : plogK (g.obj c₂).δ s (((Units.map (g.map ψ).φ.toMonoidHom (eps Λ Λ' v φ) : (g.obj c₂).Bˣ) : (g.obj c₂).B) - 1) =
      (g.map ψ).φ (ee Λ Λ' v s φ) := by
    unfold ee
    rw [plogK_map (g.map ψ) s e0]
    simp
  rw [rr_eq Λ Λ' v φ ψ χ hχ,
    plog_mul _ s (hs _) _ _ (mul_sub_mem _ _ _ (mul_sub_mem _ _ _ hr e0') e1) (inv_sub _ _ e2),
    plog_mul _ s (hs _) _ _ (mul_sub_mem _ _ _ hr e0') e1, plog_mul _ s (hs _) _ _ hr e0',
    plog_inv _ s (hs _) _ e2, hm]
  unfold ee
  ring

theorem map_self (F : C ⥤ ModuleCat.{0} K) (σ : ComposableArrows C 2) (i : Fin 3) (h : i ⟶ i) (x : F.obj (σ.obj i)) :
    (F.map (σ.map h)).hom x = x := by
  rw [Subsingleton.elim h (𝟙 _), σ.map_id, F.map_id]
  rfl

theorem composable_arrows_map_zero_two (σ : ComposableArrows C 2) : σ.map' 0 2 = σ.map' 0 1 ≫ σ.map' 1 2 := by
  simp only [ComposableArrows.map']
  rw [← σ.map_comp]
  rfl

def eC (Λ Λ' : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (s : ℕ) : CH.Cn (g ⋙ O (smFun X q)) 1 :=
  fun τ => (show (g.obj (τ.obj (Fin.last 1))).B from ee Λ Λ' v s (τ.map' 0 1))

theorem zK_eq (Λ Λ' : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ)
    (hv : ∀ c, Ideal.Quotient.mk (g.obj c).J ((v c : (g.obj c).Bˣ) : (g.obj c).B) =
      ub (Λ.p c) (Λ'.p c) ((Λ.hp c).trans (Λ'.hp c).symm)) (s : ℕ) (hs : ∀ c, (g.obj c).pdPow s = ⊥) :
    zK Λ' s = zK Λ s + CH.d _ 1 (eC Λ Λ' v s) := by
  funext σ
  have hr : ((rr Λ (σ.map' 0 1) (σ.map' 1 2) (σ.map' 0 2) : (g.obj (σ.obj (Fin.last 2))).Bˣ) :
      (g.obj (σ.obj (Fin.last 2))).B) - 1 ∈ (g.obj (σ.obj (Fin.last 2))).J := GlobalTheory.CompanionTheory.ConeUnit.r_sub_one Λ σ
  have key := log_eq Λ Λ' v hv s hs (σ.map' 0 1) (σ.map' 1 2) (σ.map' 0 2) (composable_arrows_map_zero_two σ) hr
  have h0 : ((g ⋙ O (smFun X q)).map (GlobalTheory.CatH.toLast 0 σ)).hom (eC Λ Λ' v s (GlobalTheory.CatH.face 0 σ)) =
      (show (g.obj (σ.obj (Fin.last 2))).B from ee Λ Λ' v s (σ.map' 1 2)) :=
    map_self (g ⋙ O (smFun X q)) σ (Fin.last 2) _ _
  have h1 : ((g ⋙ O (smFun X q)).map (GlobalTheory.CatH.toLast 1 σ)).hom (eC Λ Λ' v s (GlobalTheory.CatH.face 1 σ)) =
      (show (g.obj (σ.obj (Fin.last 2))).B from ee Λ Λ' v s (σ.map' 0 2)) :=
    map_self (g ⋙ O (smFun X q)) σ (Fin.last 2) _ _
  have h2 : ((g ⋙ O (smFun X q)).map (GlobalTheory.CatH.toLast 2 σ)).hom (eC Λ Λ' v s (GlobalTheory.CatH.face 2 σ)) =
      (show (g.obj (σ.obj (Fin.last 2))).B from (g.map (σ.map' 1 2)).φ (ee Λ Λ' v s (σ.map' 0 1))) := rfl
  have hd : CH.d (g ⋙ O (smFun X q)) 1 (eC Λ Λ' v s) σ =
      ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • ((g ⋙ O (smFun X q)).map (GlobalTheory.CatH.toLast i σ)).hom
        (eC Λ Λ' v s (GlobalTheory.CatH.face i σ)) := rfl
  rw [Pi.add_apply, hd, Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_smul, even_two, Even.neg_pow, one_pow]
  rw [h0, h1, h2]
  refine key.trans ?_
  change _ + _ = _ + _
  congr 1
  have fin : ∀ a b c : (g.obj (σ.obj (Fin.last 2))).B, a + b - c = b + -c + a := fun a b c => by ring
  exact fin _ _ _

theorem main : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {C : Type 1}
    [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ Λ' : CLiftK g D) (s : ℕ),
    (∀ c, (g.obj c).pdPow s = ⊥) → ∀ (hz : CH.d _ 2 (zK Λ s) = 0) (hz' : CH.d _ 2 (zK Λ' s) = 0),
    (CH.cx _).cls (zK Λ s) hz = (CH.cx _).cls (zK Λ' s) hz' := by
  intro K _ _ X q C _ g D Λ Λ' s hs hz hz'
  have hl : ∀ c, ∃ v : (g.obj c).Bˣ, Ideal.Quotient.mk (g.obj c).J ((v : (g.obj c).Bˣ) : (g.obj c).B) =
      ub (Λ.p c) (Λ'.p c) ((Λ.hp c).trans (Λ'.hp c).symm) :=
    fun c => exists_unit_lift (g.obj c) _ (ub_isUnit _ _ _)
  choose v hv using hl
  have key := zK_eq Λ Λ' v hv s hs
  refine (Submodule.Quotient.eq _).2 ?_
  change zK Λ s - zK Λ' s ∈ (CH.cx (g ⋙ O (smFun X q))).B 2
  refine ⟨-eC Λ Λ' v s, ?_⟩
  change CH.d _ 1 (-eC Λ Λ' v s) = _
  rw [map_neg, key]
  abel

end Main

end GlobalTheory.CompanionTheory.ConeZcls
