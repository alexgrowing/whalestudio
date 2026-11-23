import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.TwGenRes
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.SheafSectionLemmas
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.LocBind
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.RootLoc

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace CrystallineSemistableComparison.TwSeq

open GlobalTheory.EtC

theorem sec_nsmul {R : Type} [CommRing R] {X Y : Shv R} (f : X ⟶ Y) (k : ℕ) {U : Scheme.{0}} (x : Sec X U) :
    Sec.map (k • f) x = k • Sec.map f x := map_nsmul (CupSpec.mapHom X Y x) k f

theorem sec_map_nsmul {R : Type} [CommRing R] {X Y : Shv R} (f : X ⟶ Y) (k : ℕ) {U : Scheme.{0}} (x : Sec X U) :
    Sec.map f (k • x) = k • Sec.map f x := map_nsmul (f.hom.app (op U)).hom k x

theorem res_nsmul {R : Type} [CommRing R] {X : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (k : ℕ) (x : Sec X U) :
    Sec.res g (k • x) = k • Sec.res g x := map_nsmul (X.obj.map g.op).hom k x

theorem res_zero {R : Type} [CommRing R] {X : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec X U) = 0 :=
  map_zero (X.obj.map g.op).hom

theorem sec_map_zero' {R : Type} [CommRing R] {X Y : Shv R} (f : X ⟶ Y) {U : Scheme.{0}} : Sec.map f (0 : Sec X U) = 0 :=
  map_zero (f.hom.app (op U)).hom

theorem sec_char {q : ℕ} {F : Shv (ZMod q)} {U : Scheme.{0}} (x : Sec F U) : q • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    rw [ULift.down_natCast, ZMod.natCast_self]
    rfl
  rw [this, zero_smul]

theorem morph_zero_of_sec {R : Type} [CommRing R] {X Y : Shv R} (f : X ⟶ Y)
    (h : ∀ (U : Scheme.{0}) (x : Sec X U), Sec.map f x = 0) : f = 0 := by
  apply Sheaf.hom_ext
  ext U x
  exact h U.unop x

theorem loc_of_img {R : Type} [CommRing R] {X Y : Shv R} (f : X ⟶ Y) {U V : Scheme.{0}} (g : V ⟶ U) (y : Sec Y U)
    (x : Sec X V) (hx : Sec.map f x = Sec.res g y) :
    Loc V fun W k => ∃ x' : Sec X W, Sec.map f x' = Sec.res (k ≫ g) y :=
  SheafSectionLemmas.loc_mono (SheafSectionLemmas.loc_true V) fun W k _ => ⟨Sec.res k x, by rw [← CupSpec.map_res, hx, TwSec.res_comp]⟩

theorem twSeq (hG : E.InGen) : InTwSeq := by
  intro p a b _ i
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have : NeZero (p ^ (a + b)) := ⟨pow_ne_zero _ hp⟩
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp⟩
  have : NeZero (p ^ b) := ⟨pow_ne_zero _ hp⟩
  obtain ⟨π, hπ, hπg⟩ := redSheaf hG (dvdB p a b) i
  obtain ⟨π', hπ', hπ'g⟩ := redSheaf hG (dvdA p a b) i
  obtain ⟨m, hmdef⟩ : ∃ m : tw (p ^ (a + b)) i ⟶ tw (p ^ (a + b)) i, m = p ^ b • 𝟙 _ := ⟨_, rfl⟩
  have hm : ∀ (U : Scheme.{0}) (x : Sec (tw (p ^ (a + b)) i) U), Sec.map m x = p ^ b • x := fun U x => by
    rw [hmdef]; exact sec_nsmul _ _ x
  have hw : m ≫ π = 0 := morph_zero_of_sec _ fun U x => by
    change Sec.map π (Sec.map m x) = 0
    rw [hm, sec_map_nsmul]
    exact sec_char (q := p ^ b) (F := tw (p ^ b) i) (Sec.map π x)
  have hQ : p ^ a • m = 0 := by
    rw [hmdef, smul_smul, ← pow_add]
    exact morph_zero_of_sec _ fun U x => by rw [sec_nsmul]; exact sec_char x

  have hπepi : Epi π := by
    refine SheafSectionLemmas.epi_of_loc π fun U y => ?_
    rcases Nat.eq_zero_or_pos b with hb | hb
    · have hy : y = 0 := by
        have h0 := sec_char (q := p ^ b) (F := tw (p ^ b) i) y
        have h1 : p ^ b = 1 := by rw [hb, pow_zero]
        exact (one_nsmul y).symm.trans ((congrArg (fun n : ℕ => n • y) h1.symm).trans h0)
      exact SheafSectionLemmas.loc_mono (SheafSectionLemmas.loc_true U) fun V g _ => ⟨0, by rw [sec_map_zero', hy]; exact (res_zero g).symm⟩
    · refine SheafSectionLemmas.loc_bind (TwSec.tw_loc hG (p ^ b) i U y) fun V g hy => ?_
      rcases hy with hy | ⟨ξ, c, hy⟩
      · exact loc_of_img π g y 0 (by rw [sec_map_zero']; exact hy.symm)
      · refine SheafSectionLemmas.loc_mono (KummerTwistLemmas.rootLoc p a b hb V ξ) fun W k ⟨ζ, hζ⟩ => ⟨c • twGen i ζ, ?_⟩
        rw [sec_map_nsmul, hπg]
        change c • twGen i (pw (dvdB p a b) ζ) = Sec.res (k ≫ g) (show Sec (tw (p ^ b) i) U from y)
        rw [TwSec.res_comp, hy, res_nsmul, twGen_res]
        congr 2
        apply Subtype.ext
        change ζ.1 ^ (p ^ (a + b) / p ^ b) = (k.appTop.hom) ξ.1
        rw [← hζ, Nat.pow_div (Nat.le_add_left b a) (Nat.pos_of_ne_zero hp), Nat.add_sub_cancel]

  have hepi : Epi (kernel.lift π m hw) := by
    refine SheafSectionLemmas.epi_lift_of_loc m π hw fun U y hy => ?_
    refine SheafSectionLemmas.loc_bind (TwSec.tw_loc hG (p ^ (a + b)) i U y) fun V g hy' => ?_
    rcases hy' with hy' | ⟨ζ, c, hy'⟩
    · exact loc_of_img m g y 0 (by rw [sec_map_zero']; exact hy'.symm)
    · rcases isEmpty_or_nonempty V with hV | hV
      · exact loc_of_img m g y 0 ((SheafSectionLemmas.sec_subsingleton_of_isEmpty _ V).elim _ _)
      · have h0 : c • twGen i (pw (dvdB p a b) ζ) = 0 := by
          have := congrArg (Sec.res g) hy
          rw [res_zero, CupSpec.map_res, hy', sec_map_nsmul, hπg] at this
          exact this
        obtain ⟨d, rfl⟩ := (hG (p ^ b) i).2.1 V (pw (dvdB p a b) ζ) c h0
        exact loc_of_img m g y (d • twGen i ζ) (by rw [hm, smul_smul, hy'])

  have hker : kernel.ι m ≫ π' = 0 := by
    refine SheafSectionLemmas.ker_comp_zero m π' fun U y hy => ?_
    refine SheafSectionLemmas.sec_eq_of_loc _ _ (SheafSectionLemmas.loc_mono (TwSec.tw_loc hG (p ^ (a + b)) i U y) fun V g hy' => ?_)
    rw [res_zero, CupSpec.map_res]
    rcases hy' with hy' | ⟨ζ, c, hy'⟩
    · rw [hy', sec_map_zero']
    · rcases isEmpty_or_nonempty V with hV | hV
      · exact (SheafSectionLemmas.sec_subsingleton_of_isEmpty _ V).elim _ _
      · have h0 : (p ^ b * c) • twGen i ζ = 0 := by
          have := congrArg (Sec.res g) hy
          rw [res_zero, CupSpec.map_res, hy', hm, smul_smul] at this
          exact this
        have hd := (hG (p ^ (a + b)) i).2.1 V ζ _ h0
        rw [pow_add, mul_comm (p ^ a)] at hd
        obtain ⟨d, rfl⟩ := Nat.dvd_of_mul_dvd_mul_left (pow_pos (Nat.pos_of_ne_zero hp) b) hd
        rw [hy', sec_map_nsmul, hπ'g, ← smul_smul]
        exact sec_char (q := p ^ a) (F := tw (p ^ a) i) _

  obtain ⟨e, hedef⟩ : ∃ e, e = kernel.lift π m hw := ⟨_, rfl⟩
  have he : e ≫ kernel.ι π = m := by rw [hedef]; exact kernel.lift_ι _ _ _
  have : Epi e := by rw [hedef]; exact hepi
  have hz : kernel.ι e ≫ π' = 0 := by
    have h1 : kernel.ι e ≫ m = 0 := by rw [← he, kernel.condition_assoc, zero_comp]
    rw [← kernel.lift_ι m (kernel.ι e) h1, Category.assoc, hker, comp_zero]
  obtain ⟨l, hl⟩ : ∃ l, e ≫ l = π' := ⟨Abelian.epiDesc e π' hz, Abelian.comp_epiDesc e π' hz⟩
  have hcomp : kernel.ι π ≫ π' = p ^ b • l := by
    apply (cancel_epi e).1
    have h2 : e ≫ kernel.ι π ≫ π' = m ≫ π' := by rw [← Category.assoc, he]
    rw [h2, Preadditive.comp_nsmul, hl, hmdef, Preadditive.nsmul_comp, Category.id_comp]
  have htor : p ^ a • kernel.ι π = 0 := by
    apply (cancel_epi e).1
    rw [Preadditive.comp_nsmul, he, hQ, comp_zero]
  exact ⟨π, π', l, hπ, hπ', hπepi, htor, hcomp⟩

end CrystallineSemistableComparison.TwSeq
