import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.ClsZeroOfRep
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.RSubOneMem
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.PowKPull
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IsFirstChernDeRhamUnique
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.KIsoPf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFiltrationViaTruncation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeCocycleClosed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeCocycleClassIndependent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConeLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.HT

open Pb
open GlobalTheory.CatH (face toLast)

namespace DlogClassConstruction

theorem mem1 {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {x : B} (hx : x ∈ J) : x ∈ pdP δ 1 := by
  have := dpow_mem_pdP δ 1 hx
  rwa [δ.dpow_one hx] at this

theorem mul2 {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {x y : B} (hx : x ∈ J) (hy : y ∈ J) : x * y ∈ pdP δ 2 :=
  dividedPowerFiltration_mul δ 1 1 (mem1 δ hx) (mem1 δ hy)

theorem four {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {a b c d : B} (ha : a - 1 ∈ J) (hb : b - 1 ∈ J)
    (hc : c - 1 ∈ J) (hd : d - 1 ∈ J) (h : a * b = c * d) : (c - 1) - (b - 1) + (d - 1) - (a - 1) ∈ pdP δ 2 := by
  have := sub_mem (mul2 δ ha hb) (mul2 δ hc hd)
  convert this using 1
  linear_combination (-1 : B) * h

theorem five {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {r' r a b c : B} (hr' : r' - 1 ∈ J) (hr : r - 1 ∈ J)
    (ha : a - 1 ∈ J) (hb : b - 1 ∈ J) (hc : c - 1 ∈ J) (h : r' * c = r * a * b) :
    ((b - 1) - (c - 1) + (a - 1)) - ((r' - 1) - (r - 1)) ∈ pdP δ 2 := by
  have hra : r * a - 1 ∈ J := by
    have := add_mem (J.mul_mem_left r ha) hr
    convert this using 1; ring
  have := sub_mem (sub_mem (mul2 δ hr' hc) (mul2 δ hr ha)) (mul2 δ hra hb)
  convert this using 1
  linear_combination (-1 : B) * h

theorem plog_sub {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ) {x : B} (hx : x ∈ J) :
    x - plogK δ (s + 1) x ∈ pdP δ 2 := by
  unfold plogK
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, zero_add, δ.dpow_one hx]
  rw [sub_add_cancel_right]
  exact neg_mem (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (dividedPowerFiltration_anti δ (by omega) (dpow_mem_pdP δ _ hx)))

theorem incl_res {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r r' : ℤ) (j : ℕ)
    (x : CH.H (sq (thFil L r) (thFil L r')) j) :
    ((incl h).sq (incl_fil h r) (incl_fil h r')).pull j ((CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q.ι).pull j x) =
      (CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q'.ι).pull j x := by
  obtain ⟨z, hz, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ j).1 x
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun σ => Subtype.ext ?_))
  have key : ∀ (T : Thick L) (h') (w : T.B ⧸ T.pdPow r'.toNat), Ideal.quotientMap (T.pdPow r'.toNat) (RingHom.id T.B) h' w = w := by
    intro T h' w
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
    rfl
  exact key _ _ _

variable {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}
  {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X}

abbrev Fg (g : C ⥤ Thick (smFun X q)) (r : ℤ) : IdF (g ⋙ thA (smFun X q)) := (thFil (smFun X q) r).res g

abbrev zz (Λ : CLiftK g D) : ∀ σ : ComposableArrows C 2, (g ⋙ thA (smFun X q)).obj (σ.obj (Fin.last 2)) :=
  fun σ => ((Λ.r σ : (g.obj (σ.obj (Fin.last 2))).B) - 1 : (g.obj (σ.obj (Fin.last 2))).B)

def fz (Λ : CLiftK g D) : CH.Cn (sq (Fg g ((1 : ℕ) : ℤ)) (Fg g (((1 : ℕ) : ℤ) + 1))) 2 :=
  fun σ => sqMk _ _ (zz Λ σ) (mem1 (g.obj (σ.obj (Fin.last 2))).δ (r_sub_one_mem Λ σ))

theorem fz_coc (Λ : CLiftK g D) : CH.d _ 2 (fz Λ) = 0 := by
  funext τ
  have m0 := GlobalTheory.CompanionTheory.ConeZcoc.mem_J Λ (face 0 τ) (toLast 0 τ)
  have m1 := GlobalTheory.CompanionTheory.ConeZcoc.mem_J Λ (face 1 τ) (toLast 1 τ)
  have m2 := GlobalTheory.CompanionTheory.ConeZcoc.mem_J Λ (face 2 τ) (toLast 2 τ)
  have m3 := GlobalTheory.CompanionTheory.ConeZcoc.mem_J Λ (face 3 τ) (toLast 3 τ)
  have e0 : Units.map (g.map (toLast 0 τ)).φ.toMonoidHom (Λ.r (face 0 τ)) = Λ.r (face 0 τ) :=
    GlobalTheory.CompanionTheory.ConeZcoc.map_id_unit (g := g) (c := τ.obj (Fin.last 3)) (toLast 0 τ) (τ.map_id _) _
  have e1 : Units.map (g.map (toLast 1 τ)).φ.toMonoidHom (Λ.r (face 1 τ)) = Λ.r (face 1 τ) :=
    GlobalTheory.CompanionTheory.ConeZcoc.map_id_unit (g := g) (c := τ.obj (Fin.last 3)) (toLast 1 τ) (τ.map_id _) _
  have e2 : Units.map (g.map (toLast 2 τ)).φ.toMonoidHom (Λ.r (face 2 τ)) = Λ.r (face 2 τ) :=
    GlobalTheory.CompanionTheory.ConeZcoc.map_id_unit (g := g) (c := τ.obj (Fin.last 3)) (toLast 2 τ) (τ.map_id _) _
  have key : Units.map (g.map (toLast 3 τ)).φ.toMonoidHom (Λ.r (face 3 τ)) *
      Units.map (g.map (toLast 1 τ)).φ.toMonoidHom (Λ.r (face 1 τ)) =
      Units.map (g.map (toLast 0 τ)).φ.toMonoidHom (Λ.r (face 0 τ)) *
      Units.map (g.map (toLast 2 τ)).φ.toMonoidHom (Λ.r (face 2 τ)) := by
    rw [e0, e1, e2]
    exact GlobalTheory.CompanionTheory.ConeZcoc.rr_coboundary Λ (τ.map' 0 1) (τ.map' 1 2) (τ.map' 2 3) (τ.map' 0 2) (τ.map' 1 3) (τ.map' 0 3)
      (τ.map'_comp 0 1 2) (τ.map'_comp 1 2 3)
  have hval := congrArg (Units.val) key
  rw [Units.val_mul, Units.val_mul] at hval
  have p := four (g.obj (τ.obj (Fin.last 3))).δ m3 m1 m0 m2 hval
  have hi : ∀ i : Fin 4, ((sq (Fg g ((1 : ℕ) : ℤ)) (Fg g (((1 : ℕ) : ℤ) + 1))).map (toLast i τ)).hom (fz Λ (face i τ)) =
      sqMk (Fg g ((1 : ℕ) : ℤ)) (Fg g (((1 : ℕ) : ℤ) + 1)) (T := τ.obj (Fin.last 3))
        (((Units.map (g.map (toLast i τ)).φ.toMonoidHom (Λ.r (face i τ)) : (g.obj (τ.obj (Fin.last 3))).Bˣ) :
          (g.obj (τ.obj (Fin.last 3))).B) - 1 : (g.obj (τ.obj (Fin.last 3))).B)
        (mem1 (g.obj (τ.obj (Fin.last 3))).δ (GlobalTheory.CompanionTheory.ConeZcoc.mem_J Λ (face i τ) (toLast i τ))) := fun i =>
    Subtype.ext (congrArg (Ideal.Quotient.mk _) (by
      change (g.map (toLast i τ)).φ (_ - 1) = _
      rw [map_sub, map_one]; rfl))
  change ∑ i : Fin 4, (-1 : ℤ) ^ (i : ℕ) • ((sq (Fg g ((1 : ℕ) : ℤ)) (Fg g (((1 : ℕ) : ℤ) + 1))).map (toLast i τ)).hom
    (fz Λ (face i τ)) = 0
  rw [Fin.sum_univ_four, hi, hi, hi, hi]
  have fin : ∀ {M : Type} [AddCommGroup M] (a b c d : M), a - b + c - d = 0 →
      (-1 : ℤ) ^ ((0 : Fin 4) : ℕ) • a + (-1 : ℤ) ^ ((1 : Fin 4) : ℕ) • b + (-1 : ℤ) ^ ((2 : Fin 4) : ℕ) • c +
        (-1 : ℤ) ^ ((3 : Fin 4) : ℕ) • d = 0 := by
    intro M _ a b c d h
    change (-1 : ℤ) ^ 0 • a + (-1 : ℤ) ^ 1 • b + (-1 : ℤ) ^ 2 • c + (-1 : ℤ) ^ 3 • d = 0
    rw [← h]
    norm_num
    abel
  exact fin _ _ _ _ (Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.2 p))

def cz (Λ : CLiftK g D) : CH.H (sq (Fg g ((1 : ℕ) : ℤ)) (Fg g (((1 : ℕ) : ℤ) + 1))) 2 := (CH.cx _).cls (fz Λ) (fz_coc Λ)

theorem rep_cz (Λ : CLiftK g D) : Rep (Fg g ((1 : ℕ) : ℤ)) (Fg g (((1 : ℕ) : ℤ) + 1)) (zz Λ) (cz Λ) :=
  ⟨fz Λ, fz_coc Λ, rfl, fun _ => rfl⟩

open GlobalTheory.CompanionTheory.ConeZcls in
theorem eps_rel (Λ Λ' : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ)
    (hv : ∀ c, Ideal.Quotient.mk (g.obj c).J ((v c : (g.obj c).Bˣ) : (g.obj c).B) =
      ub (Λ.p c) (Λ'.p c) ((Λ.hp c).trans (Λ'.hp c).symm)) {c₀ c₁ c₂ : C} (φ : c₀ ⟶ c₁) (ψ : c₁ ⟶ c₂) (χ : c₀ ⟶ c₂)
    (hχ : χ = φ ≫ ψ) : ((Units.val (eps Λ Λ' v ψ) - 1) - (Units.val (eps Λ Λ' v χ) - 1) + (g.map ψ).φ (Units.val (eps Λ Λ' v φ) - 1)) -
      ((Units.val (rr Λ' φ ψ χ) - 1) - (Units.val (rr Λ φ ψ χ) - 1)) ∈ pdP (g.obj c₂).δ 2 := by
  have e0 := (g.map ψ).hle (eps_sub Λ Λ' v hv φ)
  rw [Ideal.mem_comap, map_sub, map_one] at e0
  have key := rr_eq Λ Λ' v φ ψ χ hχ
  have key' := congrArg Units.val (mul_inv_eq_iff_eq_mul.1 key.symm).symm
  rw [Units.val_mul, Units.val_mul, Units.val_mul] at key'
  rw [map_sub, map_one]
  exact five (g.obj c₂).δ (GlobalTheory.CompanionTheory.ConeUnit.r_sub_mem Λ' φ ψ χ hχ) (GlobalTheory.CompanionTheory.ConeUnit.r_sub_mem Λ φ ψ χ hχ) e0
    (eps_sub Λ Λ' v hv ψ) (eps_sub Λ Λ' v hv χ) key'

open GlobalTheory.CompanionTheory.ConeZcls in
theorem cz_eq (Λ Λ' : CLiftK g D) : cz Λ' = cz Λ := by
  have hl : ∀ c, ∃ v : (g.obj c).Bˣ, Ideal.Quotient.mk (g.obj c).J ((v : (g.obj c).Bˣ) : (g.obj c).B) =
      ub (Λ.p c) (Λ'.p c) ((Λ.hp c).trans (Λ'.hp c).symm) :=
    fun c => exists_unit_lift (g.obj c) _ (ub_isUnit _ _ _)
  choose v hv using hl
  let F := sq (Fg g ((1 : ℕ) : ℤ)) (Fg g (((1 : ℕ) : ℤ) + 1))
  let ε : ∀ {c c' : C}, (c ⟶ c') → F.obj c' := fun {c c'} φ =>
    sqMk (Fg g ((1 : ℕ) : ℤ)) (Fg g (((1 : ℕ) : ℤ) + 1)) (T := c') (((eps Λ Λ' v φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 : (g.obj c').B)
      (mem1 (g.obj c').δ (eps_sub Λ Λ' v hv φ))
  let e : CH.Cn F 1 := fun τ => ε (τ.map' 0 1)
  refine ((CrystallineSemistableComparison.P.cls_surj (CH.cx F) 2).2.2.1 _ _ _ _).2 ⟨e, ?_⟩
  funext σ
  have h0 : (F.map (toLast 0 σ)).hom (e (face 0 σ)) = ε (σ.map' 1 2) := map_self F σ (Fin.last 2) _ _
  have h1 : (F.map (toLast 1 σ)).hom (e (face 1 σ)) = ε (σ.map' 0 2) := map_self F σ (Fin.last 2) _ _
  have h2 : (F.map (toLast 2 σ)).hom (e (face 2 σ)) = (F.map (σ.map' 1 2)).hom (ε (σ.map' 0 1)) := rfl
  have p := eps_rel Λ Λ' v hv (σ.map' 0 1) (σ.map' 1 2) (σ.map' 0 2) (composable_arrows_map_zero_two σ)
  change ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i σ)).hom (e (face i σ)) = fz Λ' σ - fz Λ σ
  rw [Fin.sum_univ_three, h0, h1, h2]
  have fin : ∀ {M : Type} [AddCommGroup M] (a b c d : M), a - b + c - d = 0 →
      (-1 : ℤ) ^ ((0 : Fin 3) : ℕ) • a + (-1 : ℤ) ^ ((1 : Fin 3) : ℕ) • b + (-1 : ℤ) ^ ((2 : Fin 3) : ℕ) • c = d := by
    intro M _ a b c d h
    change (-1 : ℤ) ^ 0 • a + (-1 : ℤ) ^ 1 • b + (-1 : ℤ) ^ 2 • c = d
    rw [← sub_eq_zero, ← h]
    norm_num
    abel
  exact fin _ _ _ _ (Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.2 p))

omit [CharZero K] in
theorem lift_ex (g : C ⥤ Thick (smFun X q)) (D : E.LineData X) (h : ∀ c, ∃ V ∈ 𝒱D D, InU V (g.obj c)) : Nonempty (CLiftK g D) := by
  have hp : ∀ c : C, ∃ p : Spec (CommRingCat.of ((g.obj c).B ⧸ (g.obj c).J)) ⟶ D.Y, p ≫ D.f = pt (g.obj c) := by
    intro c
    obtain ⟨V, ⟨σ, hσ⟩, hV⟩ := h c
    have hr : Set.range (pt (g.obj c)) ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact hV (show x ∈ (⊤ : Scheme.Opens _) from trivial)
    refine ⟨IsOpenImmersion.lift V.ι (pt (g.obj c)) hr ≫ σ, ?_⟩
    rw [Category.assoc, hσ, IsOpenImmersion.lift_fac]
  choose p hp using hp
  have hw : ∀ {c c' : C} (φ : c ⟶ c'), ∃ w : (g.obj c').Bˣ,
      ∀ (h : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c').J (g.map φ).φ (g.map φ).hle)) ≫ p c) ≫ D.f = p c' ≫ D.f),
        Ideal.Quotient.mk (g.obj c').J w = (Scheme.ΓSpecIso (CommRingCat.of ((g.obj c').B ⧸ (g.obj c').J))).hom.hom
          (D.u (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c').J (g.map φ).φ (g.map φ).hle)) ≫ p c) (p c') h) := by
    intro c c' φ
    by_cases h : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c').J (g.map φ).φ (g.map φ).hle)) ≫ p c) ≫ D.f = p c' ≫ D.f
    · obtain ⟨w, hw⟩ := GlobalTheory.CompanionTheory.ConeZcls.exists_unit_lift (g.obj c') _ (GlobalTheory.CompanionTheory.ConeZcls.ub_isUnit _ _ h)
      exact ⟨w, fun _ => hw⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose w hw using @hw
  exact ⟨{ p := p, hp := hp, w := fun φ => w φ, hw := fun φ h => hw φ h }⟩

variable (q)

abbrev Q0 (𝒱 : Set X.Opens) : ObjectProperty (Thick (smFun X q)) :=
  St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) ⊤ 𝒱

omit [CharZero K] in
theorem res_ks (s a j : ℕ) (hs : a < s) (𝒱 : Set X.Opens) (h : sSup 𝒱 = ⊤) :
    Function.Bijective ((CH.Mor.restrict (grT (smFun X q) a) (KS q s 𝒱).ι).pull j) := by
  have b := GlobalTheory.CompanionTheory.KIso.chain_bij q s 𝒱 h (a : ℤ) ((a : ℤ) + 1) (by omega) j
  have e : GlobalTheory.CompanionTheory.KIso.chain q s 𝒱 (a : ℤ) ((a : ℤ) + 1) j =
      fun x => (CH.Mor.restrict (grT (smFun X q) a) (KS q s 𝒱).ι).pull j x :=
    funext fun x => (congrArg _ (incl_res (GlobalTheory.CompanionTheory.KIso.top_ge q s) _ _ j x)).trans (incl_res (GlobalTheory.CompanionTheory.KIso.st_le q s 𝒱) _ _ j x)
  rw [e] at b
  exact b

omit [CharZero K] in
theorem restriction_open_cover_bijective (a j : ℕ) (𝒱 : Set X.Opens) (h : sSup 𝒱 = ⊤) :
    Function.Bijective ((CH.Mor.restrict (grT (smFun X q) a) (Q0 q 𝒱).ι).pull j) := by
  have hle : KS q (a + 1) 𝒱 ≤ Q0 q 𝒱 := fun _ h => ⟨trivial, h.2⟩
  have b1 := Pb.refl (γ := dividedPowersBot K) (q := q) (κ := Ideal.Quotient.mk ⊥) ⊤ 1 (a + 1) (Or.inl ⟨rfl, rfl⟩) 𝒱 hle
    (a : ℤ) ((a : ℤ) + 1) (by push_cast; omega) j
  have b := res_ks q (a + 1) a j (by omega) 𝒱 h
  refine ⟨fun x y hxy => b.1 ?_, fun y => ?_⟩
  · exact (incl_res hle _ _ j x).symm.trans ((congrArg _ hxy).trans (incl_res hle _ _ j y))
  · obtain ⟨x, hx⟩ := b.2 (((incl hle).sq (incl_fil hle (a : ℤ)) (incl_fil hle ((a : ℤ) + 1))).pull j y)
    exact ⟨x, b1.1 ((incl_res hle _ _ j x).trans hx)⟩

theorem pow_rep (g : C ⥤ Thick (smFun X q)) (c : Hdg q 1 2) (z : CH.Cn (CH.modF (g ⋙ thA (smFun X q))) 2)
    (hz : ∀ s, z s ∈ (Fg g ((1 : ℕ) : ℤ)).S _)
    (hc : Rep (Fg g ((1 : ℕ) : ℤ)) (Fg g (((1 : ℕ) : ℤ) + 1)) z ((CH.Mor.restrict (grT (smFun X q) 1) g).pull 2 c)) (k : ℕ) :
    (∀ s, cupPowC (g ⋙ thA (smFun X q)) z k s ∈ (Fg g (k : ℤ)).S _) ∧
    Rep (Fg g (k : ℤ)) (Fg g ((k : ℤ) + 1)) (cupPowC (g ⋙ thA (smFun X q)) z k)
      ((CH.Mor.restrict (grT (smFun X q) k) g).pull (2 * k) (powH q c k)) := by
  induction k with
  | zero =>
    refine ⟨fun s => ?_, _, _, rfl, fun s => rfl⟩
    change _ ∈ (g.obj _).pdPow 0
    rw [Thick.pdPow_zero]; trivial
  | succ k ih =>
    have ok : MulOk (Fg g (k : ℤ)) (Fg g ((k : ℤ) + 1)) (Fg g ((1 : ℕ) : ℤ)) (Fg g (((1 : ℕ) : ℤ) + 1))
        (Fg g ((k + 1 : ℕ) : ℤ)) (Fg g (((k + 1 : ℕ) : ℤ) + 1)) :=
      ⟨fun T _ _ => (grOk (smFun X q) rfl).aa (g.obj T), fun T _ _ => (grOk (smFun X q) rfl).ab (g.obj T),
        fun T _ _ => (grOk (smFun X q) rfl).ba (g.obj T)⟩
    have h := rep_cup ok (show 2 * k + 2 = 2 * (k + 1) by omega) _ z ih.1 hz ih.2 hc
    have key := CrystallineSemistableComparison.P.cup_pull (grOk (smFun X q) (rfl : k + 1 = k + 1)).pair ok.pair g
      (fun _ => LinearMap.id) (fun _ => LinearMap.id) (fun _ => LinearMap.id)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
      (show 2 * k + 2 = 2 * (k + 1) by omega) (powH q c k) c
    exact ⟨h.1, key ▸ h.2⟩

end DlogClassConstruction

open DlogClassConstruction

theorem dlog_class_exists_unique : DlogClassExistsUnique := by
  intro K _ _ X q D hD
  have hb := restriction_open_cover_bijective q 1 2 (𝒱D D) hD
  have hU : ∀ c : (Q0 q (𝒱D D)).FullSubcategory, ∃ V ∈ 𝒱D D, InU V ((Q0 q (𝒱D D)).ι.obj c) := fun c => c.property.2
  obtain ⟨Λ₀⟩ := lift_ex (Q0 q (𝒱D D)).ι D hU
  obtain ⟨x, hx⟩ := hb.2 (cz Λ₀)
  refine ⟨x, fun C _ g hg Λ => ?_, fun y hy => hb.1 ((rep_uniq (hy _ _ hU Λ₀) (rep_cz Λ₀)).trans hx.symm)⟩
  let h : C ⥤ (Q0 q (𝒱D D)).FullSubcategory := (Q0 q (𝒱D D)).lift g fun c => ⟨trivial, hg c⟩
  have e1 : (CH.Mor.restrict (grT (smFun X q) 1) g).pull 2 x =
      (CH.Mor.restrict ((Q0 q (𝒱D D)).ι ⋙ grT (smFun X q) 1) h).pull 2 ((CH.Mor.restrict (grT (smFun X q) 1) (Q0 q (𝒱D D)).ι).pull 2 x) :=
    (CrystallineSemistableComparison.P.pull_comp (CH.Mor.restrict (grT (smFun X q) 1) (Q0 q (𝒱D D)).ι)
      (CH.Mor.restrict ((Q0 q (𝒱D D)).ι ⋙ grT (smFun X q) 1) h) 2 x).1
  have e2 : (CH.Mor.restrict (grT (smFun X q) 1) g).pull 2 x = cz Λ :=
    e1.trans ((congrArg _ hx).trans (cz_eq Λ (Λ₀.precomp h)))
  rw [e2]
  exact rep_cz Λ

theorem kTop : KTop := by
  intro K _ _ X q _ d _ D hD c hc h0
  obtain ⟨c', hc'⟩ := isFirstChernDeRham_exists q d D hD
  refine powK_ne_zero q d D hD c' hc' ?_
  obtain ⟨N, i, hi, hip, hO⟩ := hD
  have hP : IsProper q := GlobalTheory.CommonModel.isProper_of_isProjOver ⟨N, i, hi, hip⟩
  obtain ⟨U, hUd⟩ := (cov_ex q).2 d inferInstance
  have hcov : sSup (𝒱D D) = ⊤ := sSup_𝒱D D N i hO
  have hk := (k_iso_pf q U (d + 1) (fun α => by rw [hUd]; omega) (𝒱D D) hcov (2 * d)).1
  let g := (KS q (d + 1) (𝒱D D)).ι
  obtain ⟨Λ⟩ := lift_exists q D (d + 1)
  obtain ⟨z, hz, hzf, hzc⟩ := hc' (d + 1) _ g (fun c => c.property.1.1) (fun c => by
    obtain ⟨-, V, ⟨σ, hσ⟩, hV⟩ := c.property
    exact ⟨V, σ, hσ, hV⟩) Λ
  have r1 := hc _ g (fun c => c.property.2) Λ
  have r2 : Rep (Fg g ((1 : ℕ) : ℤ)) (Fg g (((1 : ℕ) : ℤ) + 1)) z ((CH.Mor.restrict (grT (smFun X q) 1) g).pull 2 c) :=
    rep_congr (fun s => by
      have := plog_sub (g.obj (s.obj (Fin.last 2))).δ d (r_sub_one_mem Λ s)
      rw [← hzf s] at this
      exact this) r1
  have r3 := (pow_rep q g c z (fun s => by
      have := mem1 (g.obj (s.obj (Fin.last 2))).δ (plogK_mem (g.obj (s.obj (Fin.last 2))).δ (d + 1) (r_sub_one_mem Λ s))
      rw [← hzf s] at this
      exact this) r2 d).2
  rw [h0, map_zero] at r3
  obtain ⟨hp, ep⟩ := powK_pull q g c' z hz hzc d
  have := cls_zero_of_rep (fun T => T.property.1.1) _ hp r3
  exact hk.1 ((ep.symm.trans this).trans (map_zero _).symm)

end CrystallineSemistableComparison.HT
