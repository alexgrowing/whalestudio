import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIntegralModelNonemptyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateModuleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionOfGeneratingSection

noncomputable section

namespace GlobalTheory.UPel.HT.Gen

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] [Algebra ℚ R] {S : Scheme.{0}}

def GBase.toBaseAt (gb : GBase D.toG R) : Base D R where
  unit k hk := by
    have hk0 : (k : ℚ) ≠ 0 := by
      rintro h
      have : k = 0 := by exact_mod_cast h
      subst this
      exact (Fact.out : p.Prime).one_lt.ne' (by simpa using hk)
    simpa using (IsUnit.mk0 _ hk0).map (algebraMap ℚ R)
  ρ := gb.ρ
  ρ_root := gb.ρ_root
  t := gb.t
  t_ω := gb.t_ω
  comax := gb.comax
  apart i j _ k _ _ β := by
    exfalso
    have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have h := ((IsUnit.mk0 _ hp).map (algebraMap ℚ R)).map β
    simp at h

theorem fullTate (gb : GBase D.toG R) {N : ℕ} (h3 : 3 ≤ N) (hN : N.Coprime p) {s : S ⟶ Sp R} (o : Obj gb.toBaseAt N s)
    (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : R →+* k) (h : x ≫ s = spMap β) :
    ∃ I : GTateIso D.toG k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
        (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)),
      ∀ y, toUnit _ ≫ o.eta y = I.ev N y := by
  haveI : CharZero k := by
    letI : Algebra ℚ k := (β.comp (algebraMap ℚ R)).toAlgebra
    exact algebraRat.charZero k
  exact GlobalTheory.T.exists_tate_module_iso p D R gb.toBaseAt N h3 hN S s o k x β h

theorem kerPrimeTo {gb : GBase D.toG R} {N : ℕ} (h3 : 3 ≤ N) {s : S ⟶ Sp R} (o : GObj gb N s) :
    ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ o.A),
      (∃ t : (o.P.pull (lift (snd o.A T ≫ x) (fst o.A T)).left).Gen, t.IsGen) → x ^ e = 1 :=
  GlobalTheory.T.torsion_of_generating_section p D R gb N h3 S s o

def GTateIso.toPrimeTo {k : Type} [Field k] {Q : Type} [Group Q] {act : D.O → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : GTateIso D.toG k Q act e) : TateIsoO D k Q act e where
  ζ := I.ζ
  ζ_prim n h _ := I.ζ_prim n h
  ζ_pow n m h h' _ := I.ζ_pow n m h h'
  ev := I.ev
  add := I.add
  lin := I.lin
  ker n h _ := I.ker n h
  onto n h _ := I.onto n h
  tower n m h h' _ := I.tower n m h h'
  isom n h _ := I.isom n h

def GBase.ofObjAt (gb : GBase D.toG R) {N : ℕ} (h3 : 3 ≤ N) (hN : N.Coprime p) {s : S ⟶ Sp R}
    (o : Obj gb.toBaseAt N s) : GObj gb N s where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  rosati := o.rosati
  lie := o.lie
  lieRank := o.lieRank
  eta := o.eta
  eta_add := o.eta_add
  eta_lin := o.eta_lin
  eta_ker := o.eta_ker
  geom := fullTate gb h3 hN o

def GObj.toObjAt {gb : GBase D.toG R} {N : ℕ} {s : S ⟶ Sp R} (o : GObj gb N s) (h3 : 3 ≤ N) :
    Obj gb.toBaseAt N s where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  kerP := kerPrimeTo h3 o
  rosati := o.rosati
  lie := o.lie
  lieRank := o.lieRank
  eta := o.eta
  eta_add := o.eta_add
  eta_lin := o.eta_lin
  eta_ker := o.eta_ker
  geom k _ _ x β h := by
    obtain ⟨I, hI⟩ := o.geom k x β h
    exact ⟨I.toPrimeTo, hI⟩

def GBase.genModelOf (gb : GBase D.toG R) {N : ℕ} (h3 : 3 ≤ N) (hN : N.Coprime p) (M : Model gb.toBaseAt N) :
    GenModel gb N where
  X := M.X
  s := M.s
  univ := gb.ofObjAt h3 hN M.univ
  rep S s' o := by
    obtain ⟨f, ⟨hf, ⟨m⟩⟩, hu⟩ := M.rep S s' (o.toObjAt h3)
    refine ⟨f, ⟨hf, ⟨⟨m.φ, m.φ₂, m.cart, m.sq, m.act, m.pol, m.eta⟩⟩⟩, ?_⟩
    rintro g ⟨hg, ⟨n⟩⟩
    exact hu g ⟨hg, ⟨⟨n.φ, n.φ₂, n.cart, n.sq, n.act, n.pol, n.eta⟩⟩⟩

theorem genModel_nonempty (p : ℕ) [Fact p.Prime] (D : Datum p) (R' : Type) [CommRing R'] [Algebra ℚ R']
    [IsNoetherianRing R'] (gb : GBase D.toG R') (N : ℕ) (h3 : 3 ≤ N) (hN : N.Coprime p) :
    Nonempty (GenModel gb N) := by
  obtain ⟨M⟩ := GlobalTheory.T.harrisTaylorIntegralModel_nonempty p D R' gb.toBaseAt N h3 hN
  exact ⟨gb.genModelOf h3 hN M⟩

end GlobalTheory.UPel.HT.Gen
