import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenWeilIsIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLevelCoverOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

noncomputable section

namespace GlobalTheory.HkClopen

variable {S : Scheme.{0}}

abbrev GeoCond (S : Scheme.{0}) := ∀ (k : Type) [Field k] [IsAlgClosed k], (Sp k ⟶ S) → Prop

def Loc (P : GeoCond S) : Prop :=
  ∃ V : Set S, IsClopen V ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S),
    x (default : PrimeSpectrum k) ∈ V ↔ P k x

theorem range_subset_iff {k : Type} [Field k] (x : Sp k ⟶ S) (V : Set S) :
    Set.range x ⊆ V ↔ x (default : PrimeSpectrum k) ∈ V := by
  refine ⟨fun h => h ⟨_, rfl⟩, fun h => ?_⟩
  rintro _ ⟨u, rfl⟩
  have : u = (default : PrimeSpectrum k) := Subsingleton.elim (α := PrimeSpectrum k) _ _
  rw [this]
  exact h

theorem Loc.congr {P Q : GeoCond S} (h : Loc P)
    (e : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), P k x ↔ Q k x) : Loc Q := by
  obtain ⟨V, hV, H⟩ := h
  exact ⟨V, hV, fun k _ _ x => (H k x).trans (e k x)⟩

theorem Loc.comb {I₀ : Type} [Finite I₀] {P : I₀ → GeoCond S} (h : ∀ i, Loc (P i)) (Φ : (I₀ → Prop) → Prop) :
    Loc fun k _ _ x => Φ fun i => P i k x := by
  choose V hV H using h
  have hf : IsLocallyConstant fun (s : S) (i : I₀) => s ∈ V i := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro s
    have : ∀ i, ∀ᶠ y in nhds s, (y ∈ V i) = (s ∈ V i) := fun i => by
      by_cases hs : s ∈ V i
      · filter_upwards [(hV i).isOpen.mem_nhds hs] with y hy
        simp [hy, hs]
      · filter_upwards [(hV i).compl.isOpen.mem_nhds hs] with y hy
        simp [show y ∉ V i from hy, hs]
    filter_upwards [Filter.eventually_all.2 this] with y hy
    exact funext hy
  refine ⟨(fun (s : S) (i : I₀) => s ∈ V i) ⁻¹' {f | Φ f}, ⟨⟨hf {f | Φ f}ᶜ⟩, hf _⟩, fun k _ _ x => ?_⟩
  have : (fun i => x (default : PrimeSpectrum k) ∈ V i) = fun i => P i k x := funext fun i => propext (H i k x)
  change Φ (fun i => x (default : PrimeSpectrum k) ∈ V i) ↔ _
  rw [this]

theorem Loc.const (A : Prop) : Loc (S := S) fun _ _ _ _ => A :=
  Loc.comb (I₀ := Empty) (P := fun i => i.elim) (fun i => i.elim) fun _ => A

theorem Loc.and {P Q : GeoCond S} (h : Loc P) (h' : Loc Q) : Loc fun k _ _ x => P k x ∧ Q k x := by
  obtain ⟨V, hV, H⟩ := h
  obtain ⟨V', hV', H'⟩ := h'
  exact ⟨V ∩ V', hV.inter hV', fun k _ _ x => and_congr (H k x) (H' k x)⟩

theorem Loc.imp_const {P : GeoCond S} (h : Loc P) (A : Prop) : Loc fun k _ _ x => P k x → A :=
  Loc.comb (I₀ := Unit) (P := fun _ => P) (fun _ => h) fun f => f () → A

theorem Loc.all {I₀ : Type} [Finite I₀] {P : I₀ → GeoCond S} (h : ∀ i, Loc (P i)) :
    Loc fun k _ _ x => ∀ i, P i k x :=
  Loc.comb h fun f => ∀ i, f i

theorem Loc.ex {I₀ : Type} [Finite I₀] {P : I₀ → GeoCond S} (h : ∀ i, Loc (P i)) :
    Loc fun k _ _ x => ∃ i, P i k x :=
  Loc.comb h fun f => ∃ i, f i

theorem Loc.all_mem {α : Type} {A : Set α} (hA : A.Finite) {P : α → GeoCond S} (h : ∀ a ∈ A, Loc (P a)) :
    Loc fun k _ _ x => ∀ a ∈ A, P a k x := by
  have := hA.to_subtype
  exact (Loc.all (I₀ := A) (P := fun a => P a.1) fun a => h a.1 a.2).congr fun k _ _ x => Subtype.forall

theorem Loc.all_range {O α : Type} (f : O → α) (hf : (Set.range f).Finite) (I : Set O) {P : α → GeoCond S}
    (h : ∀ a, Loc (P (f a))) : Loc fun k _ _ x => ∀ a ∈ I, P (f a) k x :=
  (Loc.all_mem (A := f '' I) (hf.subset (Set.image_subset_range _ _)) (P := P)
    (by rintro _ ⟨a, -, rfl⟩; exact h a)).congr fun k _ _ x => Set.forall_mem_image

theorem loc_eq (G : Over S) [GrpObj G] (hG : IsAbelianScheme G) (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤)))
    (a b : 𝟙_ (Over S) ⟶ G) (ha : a ^ n = 1) (hb : b ^ n = 1) :
    Loc fun _ _ _ x => toUnit (Over.mk x) ≫ a = toUnit (Over.mk x) ≫ b := by
  obtain ⟨U, hU, H⟩ := LevelCover.exists_clopen_eq G hG n hn a b ha hb
  exact ⟨(U : Set (𝟙_ (Over S)).left), ⟨hU, U.isOpen⟩, fun k _ _ x => (range_subset_iff x _).symm.trans (H _ (toUnit (Over.mk x))).symm⟩

theorem loc_weil (P : Out.PolAV S) (n : ℕ) (h0 : 0 < n) (hn : IsUnit (n : Γ(S, ⊤)))
    (a b : 𝟙_ (Over S) ⟶ P.A) (ha : a ^ n = 1) (hb : b ^ n = 1) :
    Loc fun _ _ _ x => Out.WeilIs P.A P.L n (toUnit (Over.mk x) ≫ a) (toUnit (Over.mk x) ≫ b) 1 := by
  obtain ⟨U, hU, H⟩ := exists_clopen_weilIs_iff firstFiveLaws.1 S P n _ a b 1 h0 hn ha hb (one_pow _)
  refine ⟨(U : Set (𝟙_ (Over S)).left), ⟨hU, U.isOpen⟩, fun k _ _ x => (range_subset_iff x _).symm.trans ?_⟩
  have := (H _ (toUnit (Over.mk x))).symm
  rw [map_one] at this
  exact this

theorem finite_range {O M : Type} [AddCommGroup O] [Module.Finite ℤ O] [CommGroup M] (f : O → M)
    (hf : ∀ a b, f (a + b) = f a * f b) {n : ℕ} (hn : 0 < n) (h : ∀ a, f a ^ n = 1) : (Set.range f).Finite := by
  let φ : Multiplicative O →* M := MonoidHom.mk' (fun x => f x.toAdd) fun x y => hf _ _
  have : AddGroup.FG O := Module.Finite.iff_addGroup_fg.1 inferInstance
  have : Group.FG φ.range := inferInstance
  have : Finite φ.range := CommGroup.finite_of_fg_torsion _ (by
    rintro ⟨_, a, rfl⟩
    exact isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, Subtype.ext (h _)⟩)
  exact Set.Finite.subset (Set.toFinite (φ.range : Set M)) (by rintro _ ⟨a, rfl⟩; exact ⟨Multiplicative.ofAdd a, rfl⟩)

theorem comp_act_natCast {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) {T : Over S} (x : T ⟶ G)
    (n : ℕ) : x ≫ act.act n = x ^ n := by
  induction n with
  | zero =>
    have := act.add 0 0
    rw [add_zero, left_eq_mul] at this
    rw [Nat.cast_zero, this, pow_zero, MonObj.comp_one]
  | succ n ih => rw [Nat.cast_succ, act.add, MonObj.comp_mul, ih, act.one, Category.comp_id, pow_succ]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def torsCount (D : Datum H) (n : ℕ) (J : Ideal (𝓞 E)) : ℕ :=
  Nat.card (Quot fun a b : {a : D.La // ∀ c ∈ J, ∃ b, c • a = n • b} => ∃ d, a.1 - b.1 = n • d)

theorem card_eq_torsCount {D : Datum H} {k Q : Type} [Field k] [Group Q] {act : 𝓞 E → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) (hact : ∀ x, act n x = x ^ n)
    (J : Ideal (𝓞 E)) (hJ : (n : 𝓞 E) ∈ J) : Nat.card {x | ∀ a ∈ J, act a x = 1} = torsCount D n J := by
  let f : {a : D.La // ∀ c ∈ J, ∃ b, c • a = n • b} → Q := fun a => I.ev n a.1
  have h1 : {x | ∀ a ∈ J, act a x = 1} = Set.range f := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, rfl⟩ := (I.onto n hn x).1 (hact x ▸ hx _ hJ)
      exact ⟨⟨a, fun c hc => (I.ker n hn _).1 ((I.lin n c a).trans (hx c hc))⟩, rfl⟩
    · rintro ⟨a, rfl⟩ c hc
      exact (I.lin n c a.1).symm.trans ((I.ker n hn _).2 (a.2 c hc))
  have h2 : (Setoid.ker f).r = fun a b => ∃ d, a.1 - b.1 = n • d := by
    funext a b
    rw [← I.ker n hn]
    have := I.add n (a.1 - b.1) b.1
    rw [sub_add_cancel] at this
    change (I.ev n a.1 = I.ev n b.1) = _
    rw [this, mul_eq_right]
  rw [h1, ← Nat.card_congr (Setoid.quotientKerEquivRange f), torsCount, ← h2]
  rfl

theorem card_range_inter {I₀ Q : Type} (g : I₀ → Q) (hg : Function.Injective g) (A : Set Q) :
    Nat.card (Set.range g ∩ A : Set Q) = Nat.card {j // g j ∈ A} := by
  rw [Set.inter_comm, ← Set.image_preimage_eq_inter_range]
  exact Nat.card_image_of_injective hg _

theorem subset_iff_card {Q : Type} {C A : Set Q} (hC : C.Finite) {u : Q} (hu : u ∈ C) (hu' : u ∈ A) :
    A ⊆ C ↔ Nat.card (C ∩ A : Set Q) = Nat.card A := by
  refine ⟨fun h => by rw [Set.inter_eq_right.2 h], fun h => ?_⟩
  have hf : (C ∩ A).Finite := hC.inter_of_left A
  have hpos : 0 < (C ∩ A).ncard := (Set.ncard_pos hf).2 ⟨u, hu, hu'⟩
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h
  have hA : A.Finite := Set.finite_of_ncard_pos (h ▸ hpos)
  exact Set.inter_eq_right.1 (Set.eq_of_subset_of_ncard_le Set.inter_subset_right h.ge hA)

theorem heckeKer_iff (D : Datum H) (t : SAB H S) (T : Over S) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (g : Fin n → (T ⟶ t.G))
    (c : Ideal (𝓞 E) → ℕ) (hc : ∀ J, (p : 𝓞 E) ∈ J → Nat.card (t.tors T J) = c J) :
    (Function.Injective g ∧ ∃ C : Subgroup (T ⟶ t.G), (C : Set _) = Set.range g ∧ t.HeckeKer T D 𝔓 p i C) ↔
    (∀ j j', g j = g j' → j = j') ∧ (∃ j, g j = 1) ∧ (∀ j j', ∃ m, g m = g j * g j') ∧ (∀ j, ∃ m, g m = (g j)⁻¹) ∧
    (∀ j, ∀ a ∈ (Set.univ : Set (𝓞 E)), ∃ m, g m = g j ≫ t.act.act a) ∧
    (∀ J ∈ {J | J * 𝔓 = Ideal.span {(p : 𝓞 E)}}, Nat.card {j // ∀ a ∈ J, g j ≫ t.act.act a = 1} = c J) ∧
    (∀ j, ∀ a ∈ Ideal.span {(p : 𝓞 E)} * 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E), g j ≫ t.act.act a = 1) ∧
    (∀ j j', Out.WeilIs t.G t.PP.L (p ^ 2 : ℕ) (g j) (g j') 1) ∧
    n = p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) ∧
    c (Ideal.span {(p : 𝓞 E)}) =
      Nat.card {j // ∀ a ∈ Ideal.span {(p : 𝓞 E)}, g j ≫ t.act.act a = 1} * Ideal.absNorm 𝔓 ^ i := by
  refine and_congr_right fun hg => ?_
  have hp : ∀ J : Ideal (𝓞 E), J * 𝔓 = Ideal.span {(p : 𝓞 E)} → (p : 𝓞 E) ∈ J := fun J hJ =>
    Ideal.dvd_span_singleton.1 ⟨𝔓, hJ.symm⟩
  have hone : ∀ J, (1 : T ⟶ t.G) ∈ t.tors T J := fun J a _ => by
    have := t.act.hom a
    exact MonObj.one_comp _
  have hsub : (1 : T ⟶ t.G) ∈ Set.range g → ∀ J, J * 𝔓 = Ideal.span {(p : 𝓞 E)} →
      (t.tors T J ⊆ Set.range g ↔ Nat.card {j // ∀ a ∈ J, g j ≫ t.act.act a = 1} = c J) := fun h1 J hJ => by
    rw [subset_iff_card (Set.finite_range g) h1 (hone J), card_range_inter g hg, hc J (hp J hJ)]
    rfl
  have hn : Nat.card (Set.range g) = n := by
    rw [Nat.card_range_of_injective hg, Nat.card_fin]
  have hcp := hc _ (Ideal.mem_span_singleton_self (p : 𝓞 E))
  constructor
  · rintro ⟨C, hC, h1, h2, h3, h4, h5, h6⟩
    have hm : ∀ x, x ∈ C ↔ x ∈ Set.range g := fun x => by rw [← hC]; rfl
    have hj : ∀ j, g j ∈ C := fun j => (hm _).2 ⟨j, rfl⟩
    refine ⟨(hm _).1 C.one_mem, fun j j' => (hm _).1 (C.mul_mem (hj j) (hj j')), fun j => (hm _).1 (C.inv_mem (hj j)),
      fun j a _ => (hm _).1 (h1 _ (hj j) a), fun J hJ => (hsub ((hm _).1 C.one_mem) J hJ).1 (fun x hx => (hm x).1 (h2 J hJ hx)),
      fun j => h3 (hj j), fun j j' => ?_, ?_, ?_⟩
    · rw [Nat.cast_pow]
      exact h4 _ (hj j) _ (hj j')
    · have e : Nat.card C = Nat.card (Set.range g) := Nat.card_congr (Equiv.subtypeEquivRight hm)
      exact hn.symm.trans (e.symm.trans h5)
    · rw [← hcp, h6, hC, card_range_inter g hg]
      rfl
  · rintro ⟨h1, hm, hi, ha, h2, h3, h4, h5, h6⟩
    let C : Subgroup (T ⟶ t.G) :=
      { carrier := Set.range g
        one_mem' := h1
        mul_mem' := by rintro _ _ ⟨j, rfl⟩ ⟨j', rfl⟩; exact hm j j'
        inv_mem' := by rintro _ ⟨j, rfl⟩; exact hi j }
    refine ⟨C, rfl, ?_, fun J hJ => (hsub h1 J hJ).2 (h2 J hJ), ?_, ?_, hn.trans h5, ?_⟩
    · rintro _ ⟨j, rfl⟩ a
      exact ha j a trivial
    · rintro _ ⟨j, rfl⟩
      exact h3 j
    · rintro _ ⟨j, rfl⟩ _ ⟨j', rfl⟩
      have := h4 j j'
      rwa [Nat.cast_pow] at this
    · exact hcp.trans (h6.trans (congrArg (· * Ideal.absNorm 𝔓 ^ i)
        (card_range_inter g hg (t.tors T (Ideal.span {(p : 𝓞 E)}))).symm))

end GlobalTheory.HkClopen

namespace GlobalTheory

open HkClopen in

theorem exists_clopen_heckeKer_iff :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (o : Ob D l s) (σ : Fin n → (𝟙_ (Over S) ⟶ o.t.G)), admitted l 𝔓 p → (∀ j, σ j ^ p ^ 2 = 1) → ∃ V : S.Opens, IsClosed (V : Set S) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), Set.range x ⊆ V ↔ (Function.Injective fun j => x ≫ (σ j).left) ∧ ∃ C : Subgroup (Over.mk x ⟶ o.t.G), (C : Set _) = Set.range (fun j => toUnit (Over.mk x) ≫ σ j) ∧ o.t.HeckeKer (Over.mk x) D 𝔓 p i C := by
  intro E _ _ _ H D l 𝔓 p i n S s o σ hA hσ
  obtain ⟨-, -, hp, -, -⟩ := hA
  have hN : 0 < p ^ 2 := pow_pos hp.pos 2
  have hu : IsUnit ((p ^ 2 : ℕ) : Γ(S, ⊤)) := by
    have := ((baseKA l).unit _ hN).map ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv ≫ s.appTop).hom
    rwa [map_natCast] at this
  have eqv := loc_eq o.t.G (ObjDim.isAbelianScheme o) _ hu
  have hact : ∀ j a, (σ j ≫ o.t.act.act a) ^ p ^ 2 = 1 := fun j a => by
    have := o.t.act.hom a
    rw [← MonObj.pow_comp, hσ, MonObj.one_comp]
  have hfin : ∀ j, (Set.range fun a => σ j ≫ o.t.act.act a).Finite := fun j =>
    finite_range _ (fun a b => by rw [o.t.act.add, MonObj.comp_mul]) hN (hact j)
  have kill : ∀ j (J : Ideal (𝓞 E)), Loc fun k _ _ (x : Sp k ⟶ S) =>
      ∀ a ∈ J, (toUnit (Over.mk x) ≫ σ j) ≫ o.t.act.act a = 1 := fun j J =>
    (Loc.all_range _ (hfin j) J (P := fun τ k _ _ x => toUnit (Over.mk x) ≫ τ = toUnit (Over.mk x) ≫ 1)
      fun a => eqv _ _ (hact j a) (one_pow _)).congr fun k _ _ x => by
        simp only [Category.assoc, MonObj.comp_one, SetLike.mem_coe]
  have hJ : {J | J * 𝔓 = Ideal.span {(p : 𝓞 E)}}.Finite := by
    refine Set.Subsingleton.finite fun J hJ J' hJ' => ?_
    have h0 : 𝔓 ≠ 0 := by
      rintro rfl
      have : Ideal.span {(p : 𝓞 E)} = ⊥ := by rw [← show J * 0 = _ from hJ, mul_zero]; rfl
      exact hp.ne_zero (Nat.cast_eq_zero.1 (Ideal.span_singleton_eq_bot.1 this))
    exact mul_right_cancel₀ h0 (hJ.trans hJ'.symm)
  have L1 := Loc.all fun j => Loc.all fun j' => (eqv _ _ (hσ j) (hσ j')).imp_const (j = j')
  have L2 := Loc.ex fun j => eqv _ _ (hσ j) (one_pow _)
  have L3 := Loc.all fun j => Loc.all fun j' => Loc.ex fun m =>
    eqv _ (σ j * σ j') (hσ m) (by rw [mul_pow, hσ, hσ, _root_.one_mul])
  have L4 := Loc.all fun j => Loc.ex fun m => eqv _ (σ j)⁻¹ (hσ m) (by rw [inv_pow, hσ, inv_one])
  have L5 := Loc.all fun j => Loc.all_range _ (hfin j) Set.univ
    (P := fun τ k _ _ x => ∃ m, toUnit (Over.mk x) ≫ σ m = toUnit (Over.mk x) ≫ τ)
    fun a => Loc.ex fun m => eqv _ _ (hσ m) (hact j a)
  have L6 := Loc.all_mem hJ fun J _ => Loc.comb (fun j => kill j J) fun f => Nat.card {j // f j} = torsCount D p J
  have L7 := Loc.all fun j => kill j (Ideal.span {(p : 𝓞 E)} * 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E))
  have L8 := Loc.all fun j => Loc.all fun j' => loc_weil (Obj.toPolAV o) _ hN hu _ _ (hσ j) (hσ j')
  have liftZP_newton := Loc.const (S := S) (n = p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))))
  have ParameterUpperBound := Loc.comb (fun j => kill j (Ideal.span {(p : 𝓞 E)})) fun f =>
    torsCount D p (Ideal.span {(p : 𝓞 E)}) = Nat.card {j // f j} * Ideal.absNorm 𝔓 ^ i
  obtain ⟨V, hV, HV⟩ := L1.and (L2.and (L3.and (L4.and (L5.and (L6.and (L7.and (L8.and (liftZP_newton.and ParameterUpperBound))))))))
  refine ⟨⟨V, hV.isOpen⟩, hV.isClosed, fun k _ _ x => ?_⟩
  obtain ⟨-, I, -⟩ := o.geom k x (Spec.preimage (x ≫ s)).hom (Spec.map_preimage (x ≫ s)).symm
  have key := heckeKer_iff D o.t (Over.mk x) 𝔓 p i n (fun j => toUnit (Over.mk x) ≫ σ j) (torsCount D p)
    fun J hJ => card_eq_torsCount I hp.pos (fun y => comp_act_natCast o.t.act y p) J hJ
  have hinj : (Function.Injective fun j => x ≫ (σ j).left) ↔
      Function.Injective fun j => toUnit (Over.mk x) ≫ σ j :=
    ⟨fun h a b e => h (congrArg (·.left) e), fun h a b e => h (Over.OverMorphism.ext e)⟩
  rw [hinj, key]
  refine ((range_subset_iff x V).trans (HV k x)).trans ?_
  simp only [MonObj.comp_one, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc]
  rfl

end GlobalTheory
