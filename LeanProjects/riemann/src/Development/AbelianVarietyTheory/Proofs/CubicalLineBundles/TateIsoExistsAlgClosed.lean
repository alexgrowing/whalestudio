import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUnitOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTorsionFieldExtStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem exists_algClosure_lift {K k : Type} [Field K] [Field k] [IsAlgClosed k] (β : K →+* k) :
    ∃ j : AlgebraicClosure K →+* k, j.comp (algebraMap K (AlgebraicClosure K)) = β := by
  letI : Algebra K k := β.toAlgebra
  let f : AlgebraicClosure K →ₐ[K] k := IsAlgClosed.lift
  exact ⟨f.toRingHom, RingHom.ext fun z => f.commutes z⟩

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

section Abstract

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q}

def OnTors (e : ℕ → Q → Q → kˣ → Prop) (n : ℕ) (x y : Q) (c : kˣ) : Prop :=
  0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c

def tateIsoCongr {e e' : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e)
    (h : ∀ n x y c, 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e' n x y c) : TateIso D k Q act e' :=
  { I with
    isom := fun n hn a b =>
      h n _ _ _ hn ((I.onto n hn _).2 ⟨a, rfl⟩) ((I.onto n hn _).2 ⟨b, rfl⟩) (I.isom n hn a b) }

theorem onTors_iff {Ω Q' : Type} [Field Ω] [Group Q'] (i : k →+* Ω) (r : Q →* Q') (hr : Function.Injective r)
    {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → Ωˣ → Prop}
    (h : ∀ (n : ℕ) x y (c : kˣ), 0 < n → x ^ n = 1 → y ^ n = 1 →
      (e n x y c ↔ e' n (r x) (r y) (Units.map i.toMonoidHom c))) (n : ℕ) (x y : Q) (c : kˣ) :
    OnTors e' n (r x) (r y) (Units.map i.toMonoidHom c) ↔ OnTors e n x y c := by
  unfold OnTors
  rw [← map_pow, ← map_pow, map_eq_one_iff r hr, map_eq_one_iff r hr]
  exact forall₃_congr fun hn hx hy => (h n x y c hn hx hy).symm

theorem onto_tors {Q' : Type} [Group Q'] (r : Q →* Q') (hr : Function.Injective r)
    (h : ∀ (n : ℕ) y, 0 < n → y ^ n = 1 → ∃ x, r x = y) (n : ℕ) (hn : 0 < n) (z : Q') (hz : z ^ n = 1) :
    ∃ y : Q, y ^ n = 1 ∧ r y = z := by
  obtain ⟨x, rfl⟩ := h n z hn hz
  exact ⟨x, by rwa [← map_pow, map_eq_one_iff r hr] at hz, rfl⟩

end Abstract

theorem cmTorsionIsometry_transport_geometricPoint (hL : Out.Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (D : Datum H) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) (act : 𝓞 E → (P.A ⟶ P.A))
    (hm : ∀ c, IsMonHom (act c))
    {F Ω k : Type} [Field F] [Field Ω] [Field k] [IsAlgClosed F] [IsAlgClosed Ω] [IsAlgClosed k] [CharZero F]
    (i : F →+* Ω) (j : F →+* k) (x : Sp F ⟶ S) (y : Sp Ω ⟶ S) (z : Sp k ⟶ S)
    (hy : spMap i ≫ x = y) (hz : spMap j ≫ x = z)
    (I : TateIso D Ω (Over.mk y ⟶ P.A) (fun c y => y ≫ act c)
      (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c))) :
    ∃ I' : TateIso D k (Over.mk z ⟶ P.A) (fun c y => y ≫ act c)
      (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)),
      (∀ (n : ℕ) (u : F), 0 < n → (I.ζ n : Ω) = i u → (I'.ζ n : k) = j u) ∧
      ∀ (n : ℕ) a (s : 𝟙_ (Over S) ⟶ P.A), 0 < n → toUnit _ ≫ s = I.ev n a → toUnit _ ≫ s = I'.ev n a := by
  subst hy hz
  have key : ∀ (k' : Type) [Field k'] (l : F →+* k') (r : (Over.mk x ⟶ P.A) →* (Over.mk (spMap l ≫ x) ⟶ P.A)),
      (∀ y, (r y).left = spMap l ≫ y.left) →
      (∀ c y, r (y ≫ act c) = r y ≫ act c) ∧ ∀ s : 𝟙_ (Over S) ⟶ P.A, r (toUnit _ ≫ s) = toUnit _ ≫ s := by
    intro k' _ l r hr
    have h : ∀ y, r y = (Over.homMk (spMap l) rfl : Over.mk (spMap l ≫ x) ⟶ Over.mk x) ≫ y :=
      fun y => Over.OverMorphism.ext (hr y)
    exact ⟨fun c y => by rw [h, h, Category.assoc], fun s => by rw [h, ← Category.assoc, comp_toUnit]⟩
  obtain ⟨r, hr, rinj, ronto, rw'⟩ := GlobalTheory.T.exists_torsion_injective_weil_compatible hL S P F Ω i x
  obtain ⟨q, hq, qinj, qonto, qw⟩ := GlobalTheory.T.exists_torsion_injective_weil_compatible hL S P F k j x
  obtain ⟨I₀, h₀⟩ := TateIsoFieldExt.down D i r (act := fun c y => y ≫ act c)
    (e := OnTors fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)) rinj (onto_tors r rinj ronto)
    (key Ω i r hr).1 (fun c => by haveI := hm c; exact MonObj.one_comp (act c))
    (onTors_iff i r rinj rw') (tateIsoCongr I fun _ _ _ _ _ _ _ h _ _ _ => h)
  obtain ⟨I', h'⟩ := TateIsoFieldExt.up D j q (act' := fun c y => y ≫ act c)
    (e' := OnTors fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)) qinj (onto_tors q qinj qonto)
    (key k j q hq).1 (onTors_iff j q qinj qw) I₀
  refine ⟨tateIsoCongr I' fun _ _ _ _ hn hx hy h => h hn hx hy, fun n u hn hu => ?_, fun n a s hn hs => ?_⟩
  · have h1 : i (I₀.ζ n) = i u := (h₀ n hn).1.symm.trans hu
    exact (h' n hn).1.trans (congrArg j (i.injective h1))
  · have h1 : toUnit _ ≫ s = I₀.ev n a :=
      rinj (((key Ω i r hr).2 s).trans (hs.trans ((h₀ n hn).2 a)))
    exact ((key k j q hq).2 s).symm.trans ((congrArg q h1).trans ((h' n hn).2 a).symm)

theorem tateIso_move : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (T : PAT H (Sp K)) (I : TateIso D ℂ (Over.mk (spMap σ) ⟶ T.t.G) (fun a x => x ≫ T.t.act.act a) (fun n x x' c => Out.WeilIs T.t.G T.t.PP.L n x x' (unitOn c))) (k : Type) [Field k] [IsAlgClosed k] (β : K →+* k), ∃ I' : TateIso D k (Over.mk (spMap β) ⟶ T.t.G) (fun a x => x ≫ T.t.act.act a) (fun n x x' c => Out.WeilIs T.t.G T.t.PP.L n x x' (unitOn c)), (∀ (n : ℕ) (z : K), 0 < n → (I.ζ n : ℂ) = σ z → (I'.ζ n : k) = β z) ∧ ∀ (n : ℕ) a (s : 𝟙_ (Over (Sp K)) ⟶ T.t.G), 0 < n → toUnit _ ≫ s = I.ev n a → toUnit _ ≫ s = I'.ev n a := by
  intro hL E _ _ _ H D K _ _ σ T I k _ _ β
  obtain ⟨i, hi⟩ := exists_algClosure_lift σ
  obtain ⟨j, hj⟩ := exists_algClosure_lift β
  obtain ⟨I', h1, h2⟩ := cmTorsionIsometry_transport_geometricPoint hL D T.pol (fun a => T.t.act.act a) T.t.act.hom i j
    (spMap (algebraMap K (AlgebraicClosure K))) (spMap σ) (spMap β)
    (by rw [← spMap_comp_eq, hi]) (by rw [← spMap_comp_eq, hj]) I
  refine ⟨I', fun n z hn hz => ?_, h2⟩
  rw [h1 n (algebraMap K _ z) hn (by rw [hz, ← hi]; rfl), ← hj]; rfl

end GlobalTheory.CM
