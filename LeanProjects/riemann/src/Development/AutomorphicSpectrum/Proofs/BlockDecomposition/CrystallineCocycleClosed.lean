import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.IsFirstChernClassOfLineBundle
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerLogMultiplicativeStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge

noncomputable section

namespace GlobalTheory.CompanionTheory.CocCls

open CrystallineSemistableComparison.B

section Ring

variable {A A' : Type} [CommRing A] [CommRing A'] {J : Ideal A} {J' : Ideal A'}

theorem dlog_map {δ : DividedPowers J} {δ' : DividedPowers J'} {f : A →+* A'} (hf : IsDPMorphism δ δ' f)
    (N : ℕ) {v : A} (hv : v - 1 ∈ J) : f (dlog δ N v) = dlog δ' N (f v) := by
  unfold dlog
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : f v - 1 = f (v - 1) := by rw [map_sub, map_one]
  rw [e, hf.dpow_comp _ hv]
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast]

theorem dlog_rel (δ : DividedPowers J) (N : ℕ)
    (hN : ∀ k, N ≤ k → ∀ x ∈ J, (k.factorial : A) * δ.dpow (k + 1) x = 0) {a b c e : A}
    (ha : a - 1 ∈ J) (hb : b - 1 ∈ J) (hc : c - 1 ∈ J) (he : e - 1 ∈ J) (h : a * b = c * e) :
    dlog δ N a + dlog δ N b = dlog δ N c + dlog δ N e := by
  rw [← GlobalTheory.T.divided_power_log_multiplicative δ N hN a b ha hb, ← GlobalTheory.T.divided_power_log_multiplicative δ N hN c e hc he, h]

theorem divided_power_log_three_term_relation (δ : DividedPowers J) (N : ℕ)
    (hN : ∀ k, N ≤ k → ∀ x ∈ J, (k.factorial : A) * δ.dpow (k + 1) x = 0) {a b c e f : A}
    (ha : a - 1 ∈ J) (hb : b - 1 ∈ J) (hc : c - 1 ∈ J) (he : e - 1 ∈ J) (hf : f - 1 ∈ J)
    (h : a * b * c = e * f) :
    dlog δ N a + dlog δ N b + dlog δ N c = dlog δ N e + dlog δ N f := by
  have hab : a * b - 1 ∈ J := by
    have : a * b - 1 = (a - 1) * b + (b - 1) := by ring
    rw [this]
    exact J.add_mem (J.mul_mem_right _ ha) hb
  rw [← GlobalTheory.T.divided_power_log_multiplicative δ N hN a b ha hb, ← GlobalTheory.T.divided_power_log_multiplicative δ N hN _ c hab hc, ← GlobalTheory.T.divided_power_log_multiplicative δ N hN e f he hf, h]

theorem unit_lift (J : Ideal A) (hJ : ∀ x ∈ J, IsNilpotent x) (u : (A ⧸ J)ˣ) :
    ∃ w : Aˣ, Units.map (Ideal.Quotient.mk J).toMonoidHom w = u := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : A ⧸ J)
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective ((u⁻¹ : (A ⧸ J)ˣ) : A ⧸ J)
  have hmem : a * b - 1 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ha, hb, Units.mul_inv, map_one, sub_self]
  have hu : IsUnit (a * b) := by
    have := (hJ _ hmem).isUnit_one_add
    simpa using this
  exact ⟨(isUnit_of_mul_isUnit_left hu).unit, Units.ext (by simpa using ha)⟩

theorem sub_one_mem {J : Ideal A} {v : Aˣ} (h : Units.map (Ideal.Quotient.mk J).toMonoidHom v = 1) :
    (v : A) - 1 ∈ J := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero]
  exact congrArg Units.val h

end Ring

section Nil

theorem thick_nil {b : Base} {L : b.Fun} (T : Thick L) : ∀ x ∈ T.J, IsNilpotent x := by
  intro x hx
  by_cases hp : b.p = 0
  · obtain ⟨n, hn⟩ := T.adm.2 hp
    refine ⟨n, ?_⟩
    have h : x ^ n ∈ T.J ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at h
    exact h
  · obtain ⟨n, hn⟩ : IsNilpotent ((b.p : ℕ) : T.B) := T.adm.1 hp
    refine ⟨b.p * n, ?_⟩
    have h1 : x ^ b.p = (b.p.factorial : T.B) * T.δ.dpow b.p x := (T.δ.factorial_mul_dpow_eq_pow hx).symm
    have h2 : (b.p.factorial : T.B) = (b.p : T.B) * ((b.p - 1).factorial : T.B) := by
      rw [← Nat.cast_mul, Nat.mul_factorial_pred hp]
    rw [pow_mul, h1, h2, mul_assoc, mul_pow, hn, zero_mul]

end Nil

section Line

variable {X : Scheme.{0}} (D : E.LineData X)

def uq {A : Type} [CommRing A] (a b : Spec (CommRingCat.of A) ⟶ D.Y) (h : a ≫ D.f = b ≫ D.f) : Aˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom (D.u a b h)

variable {A A' : Type} [CommRing A] [CommRing A']

theorem uq_mul (a b c : Spec (CommRingCat.of A) ⟶ D.Y) (h : a ≫ D.f = b ≫ D.f) (h' : b ≫ D.f = c ≫ D.f) :
    uq D a b h * uq D b c h' = uq D a c (h.trans h') := by
  rw [uq, uq, ← map_mul, D.coc]
  rfl

theorem uq_self (a : Spec (CommRingCat.of A) ⟶ D.Y) : uq D a a rfl = 1 := by
  have := uq_mul D a a a rfl rfl
  simpa using this

theorem uq_congr {a a' b b' : Spec (CommRingCat.of A) ⟶ D.Y} (ea : a = a') (eb : b = b')
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) : uq D a b h = uq D a' b' h' := by
  subst ea eb
  rfl

theorem uq_map (f : A →+* A') (a b : Spec (CommRingCat.of A) ⟶ D.Y) (h : a ≫ D.f = b ≫ D.f)
    (h' : (Spec.map (CommRingCat.ofHom f) ≫ a) ≫ D.f = (Spec.map (CommRingCat.ofHom f) ≫ b) ≫ D.f) :
    uq D (Spec.map (CommRingCat.ofHom f) ≫ a) (Spec.map (CommRingCat.ofHom f) ≫ b) h' =
      Units.map f.toMonoidHom (uq D a b h) := by
  have e := D.nat (Spec.map (CommRingCat.ofHom f)) a b h
  ext
  change (Scheme.ΓSpecIso (CommRingCat.of A')).hom.hom (D.u _ _ h').val =
    f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (D.u a b h).val)
  rw [e]
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)) _

end Line

section Cocycle

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b : Base} {ht : b.t = 1}
  {κ : O →+* b.R ⧸ b.I} {C : Type 1} [Category.{0} C] {G : C ⥤ Thick ((schFn q).cr b ht κ)} {D : E.LineData X}

theorem thPt_map {T T' : Thick ((schFn q).cr b ht κ)} (φ : T ⟶ T') : thSp φ ≫ thPt T = thPt T' :=
  congrArg (fun z => z.1.2) φ.pt

theorem thSp_comp {T T' T'' : Thick ((schFn q).cr b ht κ)} (f : T ⟶ T') (g : T' ⟶ T'') :
    thSp (f ≫ g) = thSp g ≫ thSp f := by
  unfold thSp
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun r => Spec.map (CommRingCat.ofHom r)) (Thick.qmap_comp f g _)

abbrev red (T : C) (G : C ⥤ Thick ((schFn q).cr b ht κ)) : ((G.obj T).B)ˣ →* ((G.obj T).B ⧸ (G.obj T).J)ˣ :=
  Units.map (Ideal.Quotient.mk (G.obj T).J).toMonoidHom

abbrev um {T T' : C} (φ : T ⟶ T') (G : C ⥤ Thick ((schFn q).cr b ht κ)) : ((G.obj T).B)ˣ →* ((G.obj T').B)ˣ :=
  Units.map (G.map φ).φ.toMonoidHom

theorem um_comp {T T' T'' : C} (f : T ⟶ T') (g : T' ⟶ T'') (x : ((G.obj T).B)ˣ) :
    um (f ≫ g) G x = um g G (um f G x) := by
  rw [um, G.map_comp]
  rfl

theorem red_um {T T' : C} (φ : T ⟶ T') (x : ((G.obj T).B)ˣ) :
    red T' G (um φ G x) = Units.map (Ideal.quotientMap (G.obj T').J (G.map φ).φ (G.map φ).hle).toMonoidHom (red T G x) :=
  Units.ext (Ideal.quotientMap_mk).symm

theorem hh (Λ : CLift G D) {T T' : C} (φ : T ⟶ T') : (thSp (G.map φ) ≫ Λ.p T) ≫ D.f = Λ.p T' ≫ D.f := by
  rw [Category.assoc, Λ.hp, Λ.hp, thPt_map]

theorem red_w (Λ : CLift G D) {T T' : C} (φ : T ⟶ T') :
    red T' G (Λ.w φ) = uq D (thSp (G.map φ) ≫ Λ.p T) (Λ.p T') (hh Λ φ) :=
  Units.ext (Λ.hw φ (hh Λ φ))

def Rf (Λ : CLift G D) {T₀ T₁ T₂ : C} (f : T₀ ⟶ T₁) (g : T₁ ⟶ T₂) (k : T₀ ⟶ T₂) : ((G.obj T₂).B)ˣ :=
  um g G (Λ.w f) * Λ.w g * (Λ.w k)⁻¹

theorem r_eq (Λ : CLift G D) (s : ComposableArrows C 2) :
    Λ.r s = Rf Λ (s.map' 0 1) (s.map' 1 2) (s.map' 0 2) := rfl

theorem red_Rf (Λ : CLift G D) {T₀ T₁ T₂ : C} (f : T₀ ⟶ T₁) (g : T₁ ⟶ T₂) :
    red T₂ G (Rf Λ f g (f ≫ g)) = 1 := by
  have e1 : red T₂ G (um g G (Λ.w f)) = uq D (thSp (G.map g) ≫ thSp (G.map f) ≫ Λ.p T₀) (thSp (G.map g) ≫ Λ.p T₁)
      (by rw [Category.assoc, Category.assoc, Category.assoc, Λ.hp, Λ.hp, thPt_map, thPt_map]) := by
    rw [red_um, red_w]
    exact (uq_map D _ _ _ _ _).symm
  have e2 : red T₂ G (Λ.w (f ≫ g)) = uq D (thSp (G.map g) ≫ thSp (G.map f) ≫ Λ.p T₀) (Λ.p T₂)
      (by rw [Category.assoc, Category.assoc, Λ.hp, Λ.hp, thPt_map, thPt_map]) := by
    rw [red_w]
    refine uq_congr D ?_ rfl _ _
    rw [G.map_comp, thSp_comp, Category.assoc]
  rw [Rf, map_mul, map_mul, map_inv, e1, red_w, uq_mul, e2, mul_inv_cancel]

theorem rel_closed (Λ : CLift G D) {T₀ T₁ T₂ T₃ : C} (f : T₀ ⟶ T₁) (g : T₁ ⟶ T₂) (h : T₂ ⟶ T₃) :
    Rf Λ g h (g ≫ h) * Rf Λ f (g ≫ h) (f ≫ g ≫ h) =
      Rf Λ (f ≫ g) h (f ≫ g ≫ h) * um h G (Rf Λ f g (f ≫ g)) := by
  simp only [Rf, map_mul, map_inv, um_comp]
  generalize um h G (um g G (Λ.w f)) = P
  generalize um h G (Λ.w g) = A
  generalize um h G (Λ.w (f ≫ g)) = Q
  generalize Λ.w h = w
  generalize Λ.w (g ≫ h) = W
  generalize Λ.w (f ≫ g ≫ h) = V
  calc A * w * W⁻¹ * (P * W * V⁻¹) = A * w * P * V⁻¹ * (W⁻¹ * W) := by ac_rfl
    _ = A * w * P * V⁻¹ * (Q * Q⁻¹) := by simp
    _ = _ := by ac_rfl

theorem map_id_of {R : Type} [CommRing R] (F : C ⥤ ModuleCat.{0} R) {T : C} (f : T ⟶ T) (hf : f = 𝟙 T) (x : F.obj T) :
    (F.map f).hom x = x := by
  subst hf
  simp

theorem dlog_arrow {T T' : C} (φ : T ⟶ T') (N : ℕ) {v : ((G.obj T).B)ˣ} (hv : red T G v = 1) :
    (G.map φ).φ (dlog (G.obj T).δ N v.val) = dlog (G.obj T').δ N (um φ G v).val :=
  dlog_map (G.map φ).dp N (sub_one_mem hv)

theorem alt4 {M : Type} [AddCommGroup M] {a b c e : M} (h : a + c = b + e) :
    (-1 : ℤ) ^ ((0 : Fin 4) : ℕ) • a + (-1 : ℤ) ^ ((1 : Fin 4) : ℕ) • b + (-1 : ℤ) ^ ((2 : Fin 4) : ℕ) • c +
      (-1 : ℤ) ^ ((3 : Fin 4) : ℕ) • e = 0 := by
  have e0 : ((0 : Fin 4) : ℕ) = 0 := rfl
  have e1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have e2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have e3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [e0, e1, e2, e3]
  simp only [pow_zero, pow_one, one_smul, neg_smul, even_two, Even.neg_pow, one_pow, Odd.neg_one_pow (by decide : Odd 3)]
  have e4 : a + -b + c + -e = (a + c) - (b + e) := by abel
  rw [e4, h, sub_self]

theorem alt3 {M : Type} [AddCommGroup M] {a b c r r' : M} (h : a + c + r' = b + r) :
    (-1 : ℤ) ^ ((0 : Fin 3) : ℕ) • a + (-1 : ℤ) ^ ((1 : Fin 3) : ℕ) • b + (-1 : ℤ) ^ ((2 : Fin 3) : ℕ) • c = r - r' := by
  have e0 : ((0 : Fin 3) : ℕ) = 0 := rfl
  have e1 : ((1 : Fin 3) : ℕ) = 1 := rfl
  have e2 : ((2 : Fin 3) : ℕ) = 2 := rfl
  rw [e0, e1, e2]
  simp only [pow_zero, pow_one, one_smul, neg_smul, even_two, Even.neg_pow, one_pow]
  have e3 : r = a + c + r' - b := by rw [h]; abel
  rw [e3]
  abel

theorem closed (Λ : CLift G D) {R : Type} [CommRing R] (c : R →+* b.R) (N : ℕ)
    (hN : ∀ T k, N ≤ k → ∀ x ∈ (G.obj T).J, (k.factorial : (G.obj T).B) * (G.obj T).δ.dpow (k + 1) x = 0) :
    CH.d _ 2 (Λ.coc c N) = 0 := by
  funext s
  change ∑ i : Fin 4, (-1 : ℤ) ^ (i : ℕ) • ((G ⋙ B.OM _ c).map (GlobalTheory.CatH.toLast i s)).hom (Λ.coc c N (GlobalTheory.CatH.face i s)) = 0
  rw [Fin.sum_univ_four]
  have h0 : GlobalTheory.CatH.toLast (0 : Fin 4) s = 𝟙 _ := s.map_id _
  have h1 : GlobalTheory.CatH.toLast (1 : Fin 4) s = 𝟙 _ := s.map_id _
  have h2 : GlobalTheory.CatH.toLast (2 : Fin 4) s = 𝟙 _ := s.map_id _
  let f := s.map' 0 1
  let g := s.map' 1 2
  let h := s.map' 2 3
  have hgh : s.map' 1 3 = g ≫ h := s.map'_comp 1 2 3
  have hfg : s.map' 0 2 = f ≫ g := s.map'_comp 0 1 2
  have hfgh : s.map' 0 3 = f ≫ g ≫ h := (s.map'_comp 0 1 3).trans (congrArg _ hgh)
  have r0 : Λ.r (GlobalTheory.CatH.face 0 s) = Rf Λ g h (g ≫ h) := by rw [← hgh]; rfl
  have r1 : Λ.r (GlobalTheory.CatH.face 1 s) = Rf Λ (f ≫ g) h (f ≫ g ≫ h) := by rw [← hfgh, ← hfg]; rfl
  have r2 : Λ.r (GlobalTheory.CatH.face 2 s) = Rf Λ f (g ≫ h) (f ≫ g ≫ h) := by rw [← hfgh, ← hgh]; rfl
  have r3 : Λ.r (GlobalTheory.CatH.face 3 s) = Rf Λ f g (f ≫ g) := by rw [← hfg]; rfl
  have m0 := red_Rf Λ g h
  have m1 : red _ G (Rf Λ (f ≫ g) h (f ≫ g ≫ h)) = 1 := by
    have := red_Rf Λ (f ≫ g) h
    rwa [Category.assoc] at this
  have m2 := red_Rf Λ f (g ≫ h)
  have m3 : red _ G (um h G (Rf Λ f g (f ≫ g))) = 1 := by rw [red_um, red_Rf, map_one]
  have key := dlog_rel (G.obj (s.obj (Fin.last 3))).δ N (hN _) (sub_one_mem m0) (sub_one_mem m2) (sub_one_mem m1)
    (sub_one_mem m3) (congrArg Units.val (rel_closed Λ f g h))
  have v0 : ((G ⋙ B.OM _ c).map (GlobalTheory.CatH.toLast 0 s)).hom (Λ.coc c N (GlobalTheory.CatH.face 0 s)) =
      dlog (G.obj (s.obj (Fin.last 3))).δ N (Rf Λ g h (g ≫ h)).val :=
    (map_id_of _ _ h0 _).trans (congrArg (fun u : ((G.obj (s.obj (Fin.last 3))).B)ˣ => dlog (G.obj (s.obj (Fin.last 3))).δ N u.val) r0)
  have v1 : ((G ⋙ B.OM _ c).map (GlobalTheory.CatH.toLast 1 s)).hom (Λ.coc c N (GlobalTheory.CatH.face 1 s)) =
      dlog (G.obj (s.obj (Fin.last 3))).δ N (Rf Λ (f ≫ g) h (f ≫ g ≫ h)).val :=
    (map_id_of _ _ h1 _).trans (congrArg (fun u : ((G.obj (s.obj (Fin.last 3))).B)ˣ => dlog (G.obj (s.obj (Fin.last 3))).δ N u.val) r1)
  have v2 : ((G ⋙ B.OM _ c).map (GlobalTheory.CatH.toLast 2 s)).hom (Λ.coc c N (GlobalTheory.CatH.face 2 s)) =
      dlog (G.obj (s.obj (Fin.last 3))).δ N (Rf Λ f (g ≫ h) (f ≫ g ≫ h)).val :=
    (map_id_of _ _ h2 _).trans (congrArg (fun u : ((G.obj (s.obj (Fin.last 3))).B)ˣ => dlog (G.obj (s.obj (Fin.last 3))).δ N u.val) r2)
  have v3 : ((G ⋙ B.OM _ c).map (GlobalTheory.CatH.toLast 3 s)).hom (Λ.coc c N (GlobalTheory.CatH.face 3 s)) =
      dlog (G.obj (s.obj (Fin.last 3))).δ N (um h G (Rf Λ f g (f ≫ g))).val :=
    Eq.trans (congrArg (fun u : ((G.obj (s.obj ⟨2, by omega⟩)).B)ˣ => (G.map h).φ (dlog (G.obj (s.obj ⟨2, by omega⟩)).δ N u.val)) r3)
      (dlog_arrow h N (red_Rf Λ f g))
  refine alt4 ?_
  exact (congrArg₂ (· + ·) v0 v2).trans (key.trans (congrArg₂ (· + ·) v1 v3).symm)

section Ind

variable (Λ Λ' : CLift G D) (v : ∀ T : C, ((G.obj T).B)ˣ)

def Ef {T T' : C} (φ : T ⟶ T') : ((G.obj T').B)ˣ :=
  Λ.w φ * v T' * (um φ G (v T))⁻¹ * (Λ'.w φ)⁻¹

variable {Λ Λ' v}

theorem red_Ef (hv : ∀ T, red T G (v T) = uq D (Λ.p T) (Λ'.p T) ((Λ.hp T).trans (Λ'.hp T).symm))
    {T T' : C} (φ : T ⟶ T') : red T' G (Ef Λ Λ' v φ) = 1 := by
  have e : red T' G (um φ G (v T)) = uq D (thSp (G.map φ) ≫ Λ.p T) (thSp (G.map φ) ≫ Λ'.p T)
      (by rw [Category.assoc, Category.assoc, Λ.hp, Λ'.hp]) := by
    rw [red_um, hv]
    exact (uq_map D _ _ _ _ _).symm
  rw [Ef, map_mul, map_mul, map_mul, map_inv, map_inv, e, red_w, red_w, hv, uq_mul,
    ← uq_mul D (thSp (G.map φ) ≫ Λ.p T) (thSp (G.map φ) ≫ Λ'.p T) (Λ'.p T')
      (by rw [Category.assoc, Category.assoc, Λ.hp, Λ'.hp]) (hh Λ' φ), mul_inv_cancel_comm, mul_inv_cancel]

theorem rel_ind {T₀ T₁ T₂ : C} (f : T₀ ⟶ T₁) (g : T₁ ⟶ T₂) :
    Ef Λ Λ' v g * um g G (Ef Λ Λ' v f) * Rf Λ' f g (f ≫ g) = Ef Λ Λ' v (f ≫ g) * Rf Λ f g (f ≫ g) := by
  simp only [Ef, Rf, map_mul, map_inv, um_comp]
  generalize um g G (um f G (v T₀)) = a
  generalize um g G (v T₁) = b
  generalize um g G (Λ.w f) = e
  generalize um g G (Λ'.w f) = e'
  generalize Λ.w g = x
  generalize Λ'.w g = x'
  generalize Λ.w (f ≫ g) = k
  generalize Λ'.w (f ≫ g) = k'
  generalize v T₂ = t
  calc x * t * b⁻¹ * x'⁻¹ * (e * b * a⁻¹ * e'⁻¹) * (e' * x' * k'⁻¹)
      = x * t * e * a⁻¹ * k'⁻¹ * (b⁻¹ * b) * (x'⁻¹ * x') * (e'⁻¹ * e') := by ac_rfl
    _ = x * t * e * a⁻¹ * k'⁻¹ * (k * k⁻¹) := by simp
    _ = _ := by ac_rfl

variable (Λ Λ' v)

def yc {R : Type} [CommRing R] (c : R →+* b.R) (N : ℕ) : CH.Cn (G ⋙ B.OM _ c) 1 :=
  fun s => (dlog (G.obj (s.obj (Fin.last 1))).δ N (Ef Λ Λ' v (s.map' 0 1)).val : (G.obj (s.obj (Fin.last 1))).B)

variable {Λ Λ' v}

theorem d_yc (hv : ∀ T, red T G (v T) = uq D (Λ.p T) (Λ'.p T) ((Λ.hp T).trans (Λ'.hp T).symm))
    {R : Type} [CommRing R] (c : R →+* b.R) (N : ℕ)
    (hN : ∀ T k, N ≤ k → ∀ x ∈ (G.obj T).J, (k.factorial : (G.obj T).B) * (G.obj T).δ.dpow (k + 1) x = 0) :
    CH.d _ 1 (yc Λ Λ' v c N) = Λ.coc c N - Λ'.coc c N := by
  funext s
  change ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • ((G ⋙ B.OM _ c).map (GlobalTheory.CatH.toLast i s)).hom (yc Λ Λ' v c N (GlobalTheory.CatH.face i s)) =
    Λ.coc c N s - Λ'.coc c N s
  rw [Fin.sum_univ_three]
  have h0 : GlobalTheory.CatH.toLast (0 : Fin 3) s = 𝟙 _ := s.map_id _
  have h1 : GlobalTheory.CatH.toLast (1 : Fin 3) s = 𝟙 _ := s.map_id _
  let f := s.map' 0 1
  let g := s.map' 1 2
  have hfg : s.map' 0 2 = f ≫ g := s.map'_comp 0 1 2
  have r1 : Ef Λ Λ' v ((GlobalTheory.CatH.face 1 s).map' 0 1) = Ef Λ Λ' v (f ≫ g) := by rw [← hfg]; rfl
  have mr := red_Rf Λ f g
  have mr' := red_Rf Λ' f g
  have me0 := red_Ef hv g
  have me1 := red_Ef hv (f ≫ g)
  have me2 : red _ G (um g G (Ef Λ Λ' v f)) = 1 := by rw [red_um, red_Ef hv, map_one]
  have key := divided_power_log_three_term_relation (G.obj (s.obj (Fin.last 2))).δ N (hN _) (sub_one_mem me0) (sub_one_mem me2) (sub_one_mem mr')
    (sub_one_mem me1) (sub_one_mem mr) (congrArg Units.val (rel_ind f g))
  have v0 : ((G ⋙ B.OM _ c).map (GlobalTheory.CatH.toLast 0 s)).hom (yc Λ Λ' v c N (GlobalTheory.CatH.face 0 s)) =
      dlog (G.obj (s.obj (Fin.last 2))).δ N (Ef Λ Λ' v g).val := map_id_of _ _ h0 _
  have v1 : ((G ⋙ B.OM _ c).map (GlobalTheory.CatH.toLast 1 s)).hom (yc Λ Λ' v c N (GlobalTheory.CatH.face 1 s)) =
      dlog (G.obj (s.obj (Fin.last 2))).δ N (Ef Λ Λ' v (f ≫ g)).val :=
    (map_id_of _ _ h1 _).trans (congrArg (fun u : ((G.obj (s.obj (Fin.last 2))).B)ˣ => dlog (G.obj (s.obj (Fin.last 2))).δ N u.val) r1)
  have v2 : ((G ⋙ B.OM _ c).map (GlobalTheory.CatH.toLast 2 s)).hom (yc Λ Λ' v c N (GlobalTheory.CatH.face 2 s)) =
      dlog (G.obj (s.obj (Fin.last 2))).δ N (um g G (Ef Λ Λ' v f)).val :=
    dlog_arrow g N (red_Ef hv f)
  have c1 : Λ.coc c N s = dlog (G.obj (s.obj (Fin.last 2))).δ N (Rf Λ f g (f ≫ g)).val := by
    change dlog _ N (Rf Λ f g (s.map' 0 2)).val = _
    rw [hfg]
  have c2 : Λ'.coc c N s = dlog (G.obj (s.obj (Fin.last 2))).δ N (Rf Λ' f g (f ≫ g)).val := by
    change dlog _ N (Rf Λ' f g (s.map' 0 2)).val = _
    rw [hfg]
  refine alt3 ?_
  rw [c2, v0, v2, v1, c1]
  exact key

end Ind

theorem exists_v (Λ Λ' : CLift G D) : ∃ v : ∀ T : C, ((G.obj T).B)ˣ,
    ∀ T, red T G (v T) = uq D (Λ.p T) (Λ'.p T) ((Λ.hp T).trans (Λ'.hp T).symm) := by
  have h : ∀ T : C, ∃ w : ((G.obj T).B)ˣ, red T G w = uq D (Λ.p T) (Λ'.p T) ((Λ.hp T).trans (Λ'.hp T).symm) :=
    fun T => unit_lift _ (thick_nil (G.obj T)) _
  choose v hv using h
  exact ⟨v, hv⟩

end Cocycle

theorem coc_cls : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b : Base} {ht : b.t = 1}
    {κ : O →+* b.R ⧸ b.I} {C : Type 1} [Category.{0} C] (G : C ⥤ Thick ((B.schFn q).cr b ht κ)) (D : E.LineData X)
    {R : Type} [CommRing R] (c : R →+* b.R) (N : ℕ),
    (∀ T k, N ≤ k → ∀ x ∈ (G.obj T).J, (k.factorial : (G.obj T).B) * (G.obj T).δ.dpow (k + 1) x = 0) →
    (∀ Λ : B.CLift G D, CH.d _ 2 (Λ.coc c N) = 0) ∧
    ∀ (Λ Λ' : B.CLift G D) hz hz', (CH.cx _).cls (Λ.coc c N) hz = (CH.cx _).cls (Λ'.coc c N) hz' := by
  intro O _ X q b ht κ C _ G D R _ c N hN
  refine ⟨fun Λ => closed Λ c N hN, fun Λ Λ' hz hz' => ?_⟩
  obtain ⟨v, hv⟩ := exists_v Λ Λ'
  exact ((CrystallineSemistableComparison.P.cls_surj _ 2).2.2.1 _ _ hz hz').2 ⟨yc Λ Λ' v c N, d_yc hv c N hN⟩

end GlobalTheory.CompanionTheory.CocCls
