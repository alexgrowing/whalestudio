import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HTTorsRep

theorem absNorm_coprime {K : Type} [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime] (𝔟 : Ideal (𝓞 K))
    (h : 𝔟 ⊔ Ideal.span {(p : 𝓞 K)} = ⊤) : (Ideal.absNorm 𝔟).Coprime p := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
  intro hdvd
  have h1 : (1 : 𝓞 K) ∈ 𝔟 ⊔ Ideal.span {(p : 𝓞 K)} := h ▸ Submodule.mem_top
  obtain ⟨β, hβ, z, hz, hβz⟩ := Submodule.mem_sup.1 h1
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  by_cases h0 : 𝔟 = ⊥
  · subst h0
    have hβ0 : β = 0 := (Submodule.mem_bot _).1 hβ
    subst hβ0
    rw [zero_add] at hβz
    have hu : IsUnit (p : 𝓞 K) := ⟨⟨(p : 𝓞 K), y, by rw [mul_comm]; exact hβz, hβz⟩, rfl⟩
    have hu' := hu.map (Algebra.norm ℤ : 𝓞 K →* ℤ)
    rw [show (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) by simp, Algebra.norm_algebraMap] at hu'
    have hd : Module.finrank ℤ (𝓞 K) ≠ 0 := (Module.finrank_pos).ne'
    rw [isUnit_pow_iff hd, Int.isUnit_iff] at hu'
    rcases hu' with h' | h'
    · exact hp.out.one_lt.ne' (by exact_mod_cast h')
    · have : (0 : ℤ) ≤ p := by positivity
      omega
  · have hne : Ideal.absNorm 𝔟 ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hne hdvd
    have : Finite (𝓞 K ⧸ 𝔟) := Nat.finite_of_card_ne_zero hne
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hdvd
    have hpx : (p : 𝓞 K ⧸ 𝔟) * x = 0 := by
      rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
    have h1' : (Ideal.Quotient.mk 𝔟 y) * (p : 𝓞 K ⧸ 𝔟) = 1 := by
      have := congrArg (Ideal.Quotient.mk 𝔟) hβz
      rwa [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hβ, zero_add, map_mul, map_natCast, map_one] at this
    have hx0 : x = 0 := by
      rw [← _root_.one_mul x, ← h1', _root_.mul_assoc, hpx, MulZeroClass.mul_zero]
    rw [hx0, addOrderOf_zero] at hx
    exact hp.out.one_lt.ne hx

section Tors

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (n : ℕ)

theorem mono_of_unit {X : Over S} (e : 𝟙_ (Over S) ⟶ X) : Mono e := ⟨fun g h _ => toUnit_unique g h⟩

theorem ι_mulN : torsion.ι A n ≫ mulN A n = toUnit _ ≫ η[A] := by
  exact (pullback.condition (f := mulN A n) (g := (η : 𝟙_ (Over S) ⟶ A))).trans
    (congrArg (· ≫ η[A]) (toUnit_unique _ _))

def torsEta : 𝟙_ (Over S) ⟶ torsion A n :=
  pullback.lift η[A] (𝟙 _) (by rw [IsMonHom.one_hom, Category.id_comp])

@[reassoc (attr := simp)] theorem torsEta_ι : torsEta n ≫ torsion.ι A n = η[A] := pullback.lift_fst _ _ _

theorem mono_ι : Mono (torsion.ι A n) := by
  have := mono_of_unit η[A]
  exact pullback.fst_of_mono

def torsAct (f : A ⟶ A) [IsMonHom f] (hf : f ≫ mulN A n = mulN A n ≫ f) : torsion A n ⟶ torsion A n :=
  pullback.lift (torsion.ι A n ≫ f) (toUnit _) (by
    rw [Category.assoc, hf, ← Category.assoc, ι_mulN, Category.assoc, IsMonHom.one_hom])

@[reassoc (attr := simp)] theorem torsAct_ι (f : A ⟶ A) [IsMonHom f] (hf : f ≫ mulN A n = mulN A n ≫ f) :
    torsAct n f hf ≫ torsion.ι A n = torsion.ι A n ≫ f := pullback.lift_fst _ _ _

theorem exists_openClosed {Ix : Type} [DecidableEq Ix] (act : Ix → (A ⟶ A)) [∀ a, IsMonHom (act a)]
    (hc : ∀ a, act a ≫ mulN A n = mulN A n ≫ act a) [Etale (torsion A n).hom] [IsSeparated (torsion A n).hom]
    (t : Finset Ix) :
    ∃ (Z : Over S) (j : Z ⟶ torsion A n), Mono j ∧ IsOpenImmersion j.left ∧ IsClosedImmersion j.left ∧
      ∀ (W : Over S) (y : W ⟶ torsion A n), (∃ z, z ≫ j = y) ↔ ∀ a ∈ t, y ≫ torsion.ι A n ≫ act a = 1 := by
  have hsec : IsOpenImmersion (torsEta (A := A) n).left ∧ IsClosedImmersion (torsEta (A := A) n).left :=
    GlobalTheory.isOpenImmersion_and_isClosedImmersion_of_section_of_etale (torsion A n).hom _ (Over.w (torsEta n))
  have := hsec.1; have := hsec.2
  have := mono_of_unit (torsEta (A := A) n)
  have := mono_ι (A := A) n
  induction t using Finset.induction_on with
  | empty =>
    exact ⟨_, 𝟙 _, inferInstance, by rw [Over.id_left]; infer_instance, by rw [Over.id_left]; infer_instance, fun W y =>
      ⟨fun _ a ha => absurd ha (Finset.notMem_empty a), fun _ => ⟨y, Category.comp_id y⟩⟩⟩
  | insert a t hat ih =>
    obtain ⟨Z, j, hj, hjo, hjc, hpts⟩ := ih
    let g := j ≫ torsAct n (act a) (hc a)
    have hP := (IsPullback.of_hasPullback g (torsEta n)).map (Over.forget S)
    have ho : IsOpenImmersion (pullback.fst g (torsEta n)).left :=
      MorphismProperty.of_isPullback (P := @IsOpenImmersion) hP.flip hsec.1
    have hcl : IsClosedImmersion (pullback.fst g (torsEta n)).left :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) hP.flip hsec.2
    refine ⟨pullback g (torsEta n), pullback.fst g (torsEta n) ≫ j, inferInstance, ?_, ?_, fun W y => ?_⟩
    · rw [Over.comp_left]; infer_instance
    · rw [Over.comp_left]; infer_instance
    constructor
    · rintro ⟨z, rfl⟩ b hb
      rcases Finset.mem_insert.1 hb with rfl | hb
      · have e : j ≫ torsion.ι A n ≫ act b = g ≫ torsion.ι A n := by simp [g]
        simp only [Category.assoc]
        rw [e, ← Category.assoc (pullback.fst g _), pullback.condition]
        simp only [Category.assoc, torsEta_ι]
        rw [← Category.assoc, toUnit_unique (z ≫ pullback.snd g (torsEta n)) (toUnit W)]; rfl
      · exact (hpts W _).1 ⟨z ≫ pullback.fst _ _, Category.assoc _ _ _⟩ b hb
    · intro h
      obtain ⟨w, hw⟩ := (hpts W y).2 (fun b hb => h b (Finset.mem_insert_of_mem hb))
      have hwg : w ≫ g = toUnit W ≫ torsEta n := by
        rw [← cancel_mono (torsion.ι A n)]
        simp only [g, Category.assoc, torsAct_ι, torsEta_ι]
        rw [← Category.assoc w j, hw, h a (Finset.mem_insert_self a t)]; rfl
      exact ⟨pullback.lift w (toUnit W) hwg, by rw [← Category.assoc, pullback.lift_fst, hw]⟩

end Tors

open GlobalTheory.IwLevel in

theorem exists_finiteEtale_killedBy : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (𝔟 : Ideal (𝓞 D.F)), 𝔟 ⊔ Ideal.span {(p : 𝓞 D.F)} = ⊤ → ∃ (K : Over S) (i : K ⟶ o.A), Mono i ∧ IsFinite K.hom ∧ Etale K.hom ∧ ∀ (T : Over S) (x : T ⟶ o.A), GlobalTheory.IwLevel.InSub i x ↔ GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) x := by
  intro p _ D R _ b N S s o 𝔟 h𝔟
  classical
  set n := Ideal.absNorm 𝔟 with hn_def
  have hcop := absNorm_coprime p 𝔟 h𝔟
  have hnR : IsUnit ((n : ℕ) : R) := b.unit n hcop
  have hnS : IsUnit ((n : ℕ) : Γ(S, ⊤)) := by
    have := hnR.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop).hom
    simpa using this
  haveI := o.ab
  obtain ⟨-, hTf, hTe⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion o.A hnS
  have hactN : ∀ k : ℕ, o.act.act (k : D.O) = mulN o.A k := by
    intro k
    induction k with
    | zero =>
      have h := o.act.add 0 0
      rw [add_zero] at h
      rw [Nat.cast_zero]
      exact left_eq_mul.1 h
    | succ k ih => rw [Nat.cast_succ, o.act.add, ih, o.act.one]; rfl
  have hc : ∀ a : D.O, o.act.act a ≫ mulN o.A n = mulN o.A n ≫ o.act.act a := by
    intro a
    rw [← hactN, ← o.act.mul, ← o.act.mul, Nat.cast_comm]
  haveI : ∀ a, IsMonHom (o.act.act a) := o.act.hom
  haveI : IsSeparated (torsion o.A n).hom := inferInstance
  have : Module.Finite ℤ D.O := D.finO
  have : IsNoetherian D.O D.O := isNoetherian_of_tower ℤ inferInstance
  obtain ⟨t, ht⟩ := IsNoetherian.noetherian (𝔟.map (algebraMap (𝓞 D.F) D.O))
  obtain ⟨Z, j, hj, hjo, hjc, hpts⟩ := exists_openClosed n o.act.act hc t
  have := mono_ι (A := o.A) n
  refine ⟨Z, j ≫ torsion.ι o.A n, inferInstance, ?_, ?_, fun T x => ?_⟩
  · rw [← Over.w j]; infer_instance
  · rw [← Over.w j]; infer_instance
  rw [← ht]
  refine Iff.trans ?_ (killedBy_span (htAct o) (t : Set D.O) x).symm
  simp only [htAct_act]
  constructor
  · rintro ⟨z, rfl⟩ a ha
    simpa only [Category.assoc] using (hpts T (z ≫ j)).1 ⟨z, rfl⟩ a ha
  · intro hx
    have hn𝔟 : ((n : ℕ) : 𝓞 D.F) ∈ 𝔟 := Ideal.absNorm_mem 𝔟
    have hnO : ((n : ℕ) : D.O) ∈ Submodule.span D.O (t : Set D.O) := by
      rw [ht]; simpa using Ideal.mem_map_of_mem (algebraMap (𝓞 D.F) D.O) hn𝔟
    have hxn : x ≫ mulN o.A n = toUnit T ≫ η[o.A] := by
      rw [← hactN]
      have := (killedBy_span (htAct o) (t : Set D.O) x).2 (by simpa only [htAct_act] using hx) _ hnO
      exact this
    let y : T ⟶ torsion o.A n := pullback.lift x (toUnit T) hxn
    have hy : y ≫ torsion.ι o.A n = x := pullback.lift_fst _ _ _
    obtain ⟨z, hz⟩ := (hpts T y).2 (fun a ha => by rw [← Category.assoc, hy]; exact hx a ha)
    exact ⟨z, by rw [← Category.assoc, hz, hy]⟩

end GlobalTheory.HTTorsRep
