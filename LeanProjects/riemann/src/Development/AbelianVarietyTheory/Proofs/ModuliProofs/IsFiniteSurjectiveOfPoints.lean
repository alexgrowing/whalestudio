import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.HeckeIsogenyKernels
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NatCastMemConj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPullCubicalOfIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfProper
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LambdaBundleIsoOfPrimeToPWeilPairings
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsogenyOfSurjectivePolAV

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckeCompare

open GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels GlobalTheory.HeckePoint GlobalTheory.CechPic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem splitPrime_iff (l : Level H) (p : ℕ) (P : Ideal (𝓞 E)) : IsSplitPrimeOff l p P ↔
    P.IsMaximal ∧ P ⊔ P.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧ p.Prime ∧ (p : 𝓞 E) ∈ P ∧ ¬ p ∣ l.M' := by
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨h₂, h₂.coprime_of_ne (conj_isMaximal H P) (Ne.symm h₄), h₁, h₃, h₅⟩
  · rintro ⟨h₂, h₄, h₁, h₃, h₅⟩
    refine ⟨h₁, h₂, h₃, fun h => h₂.ne_top ?_, h₅⟩
    rw [← h₄, show P.map (H.bar : 𝓞 E →+* 𝓞 E) = P from h, sup_idem]

section Fibre

variable {B : Type} [CommRing B] {b : Base l B} {k : Type} [Field k] {s : Sp k ⟶ Sp B}

def ptAct {S : Scheme.{0}} (t : SAB H S) (T : Over S) (a : 𝓞 E) : (T ⟶ t.G) →* (T ⟶ t.G) :=
  haveI := t.act.hom a
  MonoidHom.mk' (fun x => x ≫ t.act.act a) fun x y => MonObj.mul_comp x y _

theorem isAct_ptAct {S : Scheme.{0}} (t : SAB H S) (T : Over S) : IsAct (ptAct t T) :=
  ⟨fun x => by show x ≫ _ = x; rw [t.act.one, Category.comp_id],
    fun a c x => by show x ≫ _ = (x ≫ _) ≫ _; rw [t.act.mul, Category.assoc],
    fun a c x => by show x ≫ _ = (x ≫ _) * (x ≫ _); rw [t.act.add, MonObj.comp_mul]⟩

abbrev ptWeil (t : SAB H (Sp k)) : ℕ → Pts t → Pts t → kˣ → Prop :=
  fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)

theorem ptWeil_one (t : SAB H (Sp k)) (n : ℕ) (x y : Pts t) : ptWeil t n x y 1 ↔ Out.WeilIs t.G t.PP.L n x y 1 :=
  iff_of_eq (congrArg (Out.WeilIs t.G t.PP.L n x y) unitOn_one)

theorem kerSet_eq (t : SAB H (Sp k)) (p : ℕ) (P : Ideal (𝓞 E)) (C₀ : Subgroup (Pts t)) :
    kerSet (ptAct t _) (ptWeil t) p P (P.map (H.bar : 𝓞 E →+* 𝓞 E)) C₀ = heckeKernel t p P C₀ := by
  ext x
  constructor
  · rintro ⟨x₁, x₂, x₃, h, h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨x₁, x₂, x₃, h, h₁, h₂, h₃, h₄, fun c hc => (ptWeil_one t p _ _).1 (h₅ c hc)⟩
  · rintro ⟨x₁, x₂, x₃, h, h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨x₁, x₂, x₃, h, h₁, h₂, h₃, h₄, fun c hc => (ptWeil_one t p _ _).2 (h₅ c hc)⟩

abbrev objPol (o : Obj D l b s) : Out.PolAV (Sp k) :=
  polOf o.t o.proper o.ample o.ktriv (obj_isAbelianScheme_dim_rigidified_sym E H D l B b _ s o).2.1

theorem tate_facts [IsAlgClosed k] [CharZero k] (hL : Out.Laws) (o : Obj D l b s) :
    Nonempty (TateIso D k (Pts o.t) (fun a x => ptAct o.t _ a x) (ptWeil o.t)) ∧ Uniq (ptWeil o.t) ∧
      ∀ p : ℕ, 0 < p → Nat.card {x : Pts o.t // x ^ p = 1} = p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) := by
  obtain ⟨-, I, -⟩ := o.geom k (𝟙 _) (Spec.preimage s).hom (by simp [spMap])
  exact ⟨⟨I⟩, fun n z w c c' _ hz hw h h' =>
    (unitOn_bijective k).1 (((hL.weil _ (objPol o) n _).1 z w hz hw).unique h h'),
    fun p hp => (hL.mulN _ (objPol o) p hp).2.2.2.2 k (𝟙 _) (Nat.cast_ne_zero.2 hp.ne')⟩

theorem weil_sq (t : SAB H (Sp k)) (p : ℕ) (x y : Pts t) :
    ptWeil t (p * p) x y 1 ↔ Out.WeilIs t.G t.PP.L ((p : ℤ) ^ 2) x y 1 := by
  rw [ptWeil_one, Nat.cast_mul, pow_two]

theorem card_tors (t : SAB H (Sp k)) (p : ℕ) :
    Nat.card (t.tors (𝟙_ _) (Ideal.span {(p : 𝓞 E)})) = Nat.card {x : Pts t // x ^ p = 1} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun x => (isAct_ptAct t _).kill_span_iff p x)

theorem card_inter_tors (t : SAB H (Sp k)) (p : ℕ) (C : Subgroup (Pts t)) :
    Nat.card ((C : Set (Pts t)) ∩ t.tors (𝟙_ _) (Ideal.span {(p : 𝓞 E)}) : Set (Pts t)) =
      Nat.card {x : Pts t // x ∈ C ∧ x ^ p = 1} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun x => and_congr_right' ((isAct_ptAct t _).kill_span_iff p x))

variable [IsAlgClosed k] [CharZero k] (hL : Out.Laws) (o : Obj D l b s) {p : ℕ} {P : Ideal (𝓞 E)}
include hL

theorem exists_heckeKer_of_datum (h : IsSplitPrimeOff l p P) {i : ℕ} {C₀ : Subgroup (Pts o.t)}
    (h₀ : IsHeckeDatum o.t P i C₀) :
    ∃ C : Subgroup (Pts o.t), (C : Set (Pts o.t)) = heckeKernel o.t p P C₀ ∧ o.t.HeckeKer (𝟙_ _) D P p i C := by
  obtain ⟨hP, hco, hp, hpP, -⟩ := (splitPrime_iff l p P).1 h
  obtain ⟨⟨I⟩, hu, hc⟩ := tate_facts hL o
  have hf : Finite {x : Pts o.t // x ^ p = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc p hp.pos]; exact (pow_pos hp.pos _).ne')
  obtain ⟨C, e, c₁, c₂, c₃, c₄, c₅, c₆⟩ := exists_subgroup I hu (isAct_ptAct _ _) hco hp.pos hpP h₀.1 h₀.2.1 hf
  exact ⟨C, e.trans (kerSet_eq _ _ _ _), c₁, c₂, c₃, fun x hx y hy => (weil_sq _ _ _ _).1 (c₄ x hx y hy),
    c₅.trans (hc p hp.pos), by rw [card_tors, card_inter_tors, c₆, h₀.2.2.2]⟩

theorem heckeKer_iff (h : IsSplitPrimeOff l p P) (i : ℕ) (C : Subgroup (Pts o.t)) :
    o.t.HeckeKer (𝟙_ _) D P p i C ↔
      ∃ C₀, IsHeckeDatum o.t P i C₀ ∧ (C : Set (Pts o.t)) = heckeKernel o.t p P C₀ := by
  constructor
  · rintro ⟨c₁, -, c₃, c₄, c₅, c₆⟩
    obtain ⟨hP, hco, hp, hpP, -⟩ := (splitPrime_iff l p P).1 h
    obtain ⟨⟨I⟩, hu, hc⟩ := tate_facts hL o
    have hpos := pow_pos hp.pos (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))
    have hf : Finite {x : Pts o.t // x ^ p = 1} := Nat.finite_of_card_ne_zero (by rw [hc p hp.pos]; exact hpos.ne')
    obtain ⟨d₁, d₂, e⟩ := eq_kerSet I hu (isAct_ptAct _ _) hco hp.pos hpP hf C c₁ c₃
      (fun x hx y hy => (weil_sq _ _ _ _).2 (c₄ x hx y hy)) (c₅.trans (hc p hp.pos).symm)
    have hm := card_eq_tors_mul C p
    rw [card_tors, card_inter_tors, hc p hp.pos] at c₆
    rw [c₅] at hm
    have h₀ := mul_ne_zero_iff.1 (hm ▸ hpos.ne')
    exact ⟨_, ⟨d₁, d₂, Nat.finite_of_card_ne_zero h₀.2, mul_left_cancel₀ h₀.1 (hm.symm.trans c₆)⟩,
      e.trans (kerSet_eq _ _ _ _)⟩
  · rintro ⟨C₀, h₀, e⟩
    obtain ⟨C', e', h'⟩ := exists_heckeKer_of_datum hL o h h₀
    rwa [SetLike.coe_injective (e.trans e'.symm)]

end Fibre

section Isogeny

variable {B : Type} [CommRing B] {b : Base l B} {k : Type} [Field k] {s : Sp k ⟶ Sp B}

def IsIsogenyOnPoints (o o' : Obj D l b s) (p : ℕ) (C : Set (Pts o.t)) (ψ : o.t.G ⟶ o'.t.G) : Prop :=
  IsMonHom ψ ∧ (∀ a, o.t.act.act a ≫ ψ = ψ ≫ o'.t.act.act a) ∧
  (∀ y : Pts o'.t, ∃ x, x ≫ ψ = y) ∧ (∀ x, x ≫ ψ = 1 ↔ x ∈ C) ∧
  (∀ (n : ℕ) (x x' : Pts o.t) (c : kˣ), n.Coprime p → Out.WeilIs o.t.G o.t.PP.L n x x' (unitOn c) →
    Out.WeilIs o'.t.G o'.t.PP.L n (x ≫ ψ) (x' ≫ ψ) (unitOn (c ^ (p ^ 2)))) ∧
  ∀ p' : ℕ, p * p' ≡ 1 [MOD l.M'] → ∀ a, o.eta (p' • a) ≫ ψ = o'.eta a ∧ o.etaA (p' • a) ≫ ψ = o'.etaA a

end Isogeny

section Transfer

variable {B : Type} [CommRing B] {b : Base l B} {X : Scheme.{0}} {sX : X ⟶ Sp B} {k : Type} [Field k]
  {s : Sp k ⟶ Sp B}

theorem exists_fibre_equiv (u : Obj D l b sX) {o : Obj D l b s} {y : Sp k ⟶ X} (m : ObjMap o u y) :
    ∃ (ρ : Pts o.t ≃* (Over.mk y ⟶ u.t.G)) (e : o.t.G.left ≅ pullback u.t.G.hom y),
      (∀ x, (ρ x).left = x.left ≫ m.cm.F) ∧
      e.hom ≫ pullback.snd _ _ = o.t.G.hom ∧ (∀ x, fibPt _ (ρ x) = x.left ≫ e.hom) ∧
      (∀ a x, ρ (x ≫ o.t.act.act a) = ρ x ≫ u.t.act.act a) ∧
      (∀ (n : ℤ) x x' (c : kˣ), Out.WeilIs o.t.G o.t.PP.L n x x' (unitOn c) ↔
        Out.WeilIs u.t.G u.t.PP.L n (ρ x) (ρ x') (unitOn c)) ∧
      (∀ a, ρ (o.eta a) = toUnit _ ≫ u.eta a) ∧ ∀ a, ρ (o.etaA a) = toUnit _ ≫ u.etaA a := by
  obtain ⟨ρ, hρ⟩ := exists_ptsEquiv m.cart (𝟙_ (Over (Sp k))) y (Category.id_comp _)
  have key : ∀ (T : Over (Sp k)) (y' : T.left ⟶ X) (_ : T.hom ≫ y = y') (n : ℤ) (x x' : T ⟶ o.t.G)
      (x₀ x₀' : Over.mk y' ⟶ u.t.G) (c : Γ(T.left, ⊤)ˣ), x₀.left = x.left ≫ m.cm.F → x₀'.left = x'.left ≫ m.cm.F →
      (Out.WeilIs o.t.G o.t.PP.L n x x' c ↔ Out.WeilIs u.t.G u.t.PP.L n x₀ x₀' c) := by
    intro T y' e
    subst e
    obtain ⟨w, hw, -⟩ := m.lin
    exact fun n x x' x₀ x₀' c =>
      weilIs_grpPullback_of_comm _ _ _ _ y m.cm.F _ _ u.t.PP.isLB o.t.PP.isLB m.cart ⟨w, hw⟩ T n x x' x₀ x₀' c
  have tu : (toUnit (Over.mk y)).left = y := by simp
  refine ⟨ρ, m.cart.1.isoPullback, hρ, m.cart.1.isoPullback_hom_snd, fun x => ?_,
    fun a x => Over.OverMorphism.ext ?_, fun n x x' c => key _ y (Category.id_comp _) n x x' _ _ _ (hρ x) (hρ x'),
    fun a => Over.OverMorphism.ext ?_, fun a => Over.OverMorphism.ext ?_⟩
  · apply pullback.hom_ext
    · rw [fibPt, pullback.lift_fst, hρ, Category.assoc, m.cart.1.isoPullback_hom_fst]
    · rw [fibPt, pullback.lift_snd, Category.assoc, m.cart.1.isoPullback_hom_snd]
      exact (Over.w x).symm
  · rw [hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, m.act, Category.assoc]
  · rw [hρ, Over.comp_left, tu]; exact m.eta a
  · rw [hρ, Over.comp_left, tu]; exact m.etaA a

def SamePoints {u : Obj D l b sX} {o : Obj D l b s} {y : Sp k ⟶ X} (m : ObjMap o u y) (C' : Set (Pts o.t))
    (C : Set (Over.mk y ⟶ u.t.G)) : Prop :=
  ∀ (x : Pts o.t) (x₀ : Over.mk y ⟶ u.t.G), x₀.left = x.left ≫ m.cm.F → (x ∈ C' ↔ x₀ ∈ C)

theorem heckeKer_transfer {u : Obj D l b sX} {o : Obj D l b s} {y : Sp k ⟶ X} (m : ObjMap o u y)
    {C' : Subgroup (Pts o.t)} {C : Subgroup (Over.mk y ⟶ u.t.G)} (h : SamePoints m C' C) (P : Ideal (𝓞 E))
    (p i : ℕ) : u.t.HeckeKer (Over.mk y) D P p i C ↔ o.t.HeckeKer (𝟙_ _) D P p i C' := by
  obtain ⟨ρ, -, e₀, -, -, e₃, e₄, -⟩ := exists_fibre_equiv u m
  have mem : ∀ x, x ∈ C' ↔ ρ x ∈ C := fun x => h x _ (e₀ x)
  have tor : ∀ J x, x ∈ o.t.tors (𝟙_ _) J ↔ ρ x ∈ u.t.tors (Over.mk y) J := fun J x =>
    forall₂_congr fun a _ => by rw [← e₃, map_eq_one_iff _ ρ.injective]
  have wl : ∀ (n : ℤ) x x', Out.WeilIs o.t.G o.t.PP.L n x x' 1 ↔ Out.WeilIs u.t.G u.t.PP.L n (ρ x) (ρ x') 1 :=
    fun n x x' => (iff_of_eq (congrArg (Out.WeilIs o.t.G o.t.PP.L n x x') unitOn_one)).symm.trans ((e₄ n x x' 1).trans
      (iff_of_eq (congrArg (Out.WeilIs u.t.G u.t.PP.L n (ρ x) (ρ x')) unitOn_one)))
  have c₁ : Nat.card C' = Nat.card C := Nat.card_congr (ρ.toEquiv.subtypeEquiv mem)
  have c₂ : ∀ J, Nat.card (o.t.tors (𝟙_ _) J) = Nat.card (u.t.tors (Over.mk y) J) := fun J =>
    Nat.card_congr (ρ.toEquiv.subtypeEquiv (tor J))
  have c₃ : ∀ J, Nat.card ((C' : Set (Pts o.t)) ∩ o.t.tors (𝟙_ _) J : Set (Pts o.t)) =
      Nat.card ((C : Set (Over.mk y ⟶ u.t.G)) ∩ u.t.tors (Over.mk y) J : Set (Over.mk y ⟶ u.t.G)) := fun J =>
    Nat.card_congr (ρ.toEquiv.subtypeEquiv fun x => and_congr (mem x) (tor J x))
  unfold SAB.HeckeKer
  rw [c₁, c₂, c₃]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ Iff.rfl)))
  · rw [ρ.surjective.forall]
    exact forall_congr' fun x => imp_congr (mem x).symm (forall_congr' fun a => by rw [← e₃, mem])
  · refine forall₂_congr fun J _ => ?_
    rw [Set.subset_def, Set.subset_def, ρ.surjective.forall]
    exact forall_congr' fun x => imp_congr (tor J x).symm (mem x).symm
  · rw [Set.subset_def, Set.subset_def, ρ.surjective.forall]
    exact forall_congr' fun x => imp_congr (mem x).symm (tor _ x).symm
  · rw [ρ.surjective.forall]
    refine forall_congr' fun x => imp_congr (mem x).symm ?_
    rw [ρ.surjective.forall]
    exact forall_congr' fun x' => imp_congr (mem x').symm (wl _ x x').symm

def IsIsogenyOnFibres (u : Obj D l b sX) (y y'' : Sp k ⟶ X) (p : ℕ) (C : Subgroup (Over.mk y ⟶ u.t.G)) : Prop :=
  ∃ (ψ : pullback u.t.G.hom y ⟶ pullback u.t.G.hom y'') (ψp : (Over.mk y ⟶ u.t.G) →* (Over.mk y'' ⟶ u.t.G)),
    ψ ≫ pullback.snd _ _ = pullback.snd _ _ ∧ (∀ x, fibPt _ x ≫ ψ = fibPt _ (ψp x)) ∧
    (∀ a x, ψp (x ≫ u.t.act.act a) = ψp x ≫ u.t.act.act a) ∧
    Function.Surjective ψp ∧ ψp.ker = C ∧
    (∀ (n : ℕ) (x x' : Over.mk y ⟶ u.t.G) (c : kˣ), n.Coprime p →
      Out.WeilIs u.t.G u.t.PP.L n x x' (unitOn c) →
      Out.WeilIs u.t.G u.t.PP.L n (ψp x) (ψp x') (unitOn (c ^ (p ^ 2)))) ∧
    ∀ p' : ℕ, p * p' ≡ 1 [MOD l.M'] → ∀ a,
      ψp (toUnit _ ≫ u.eta (p' • a)) = toUnit _ ≫ u.eta a ∧ ψp (toUnit _ ≫ u.etaA (p' • a)) = toUnit _ ≫ u.etaA a

end Transfer

section Statements

variable {k : Type} [Field k]

theorem exists_fibre_obj (Xo : Moduli D l) (y y' : Sp k ⟶ Xo.X) (h : y' ≫ Xo.s = y ≫ Xo.s) :
    ∃ o : Obj D l (baseKA l) (y ≫ Xo.s), Nonempty (ObjMap o Xo.univ y') :=
  obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (y ≫ Xo.s) y' rfl rfl
    (by rw [h, spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]) Xo.univ

def HeckePointsAt (Xo : Moduli D l) : Prop :=
  ∀ (P : Ideal (𝓞 E)) (p i : ℕ), P.IsMaximal → P ⊔ P.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ → p.Prime → (p : 𝓞 E) ∈ P →
    ¬ p ∣ l.M' → ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo.X)
      (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G)), Xo.univ.t.HeckeKer (Over.mk y) D P p i C →
      ∃! y'' : Sp k ⟶ Xo.X, y'' ≫ Xo.s = y ≫ Xo.s ∧ IsIsogenyOnFibres Xo.univ y y'' p C

end Statements

end GlobalTheory.HeckeCompare
