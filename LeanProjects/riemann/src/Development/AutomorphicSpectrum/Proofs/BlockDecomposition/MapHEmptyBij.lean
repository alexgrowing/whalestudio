import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveRes
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CrystallineSemistableComparison CrystallineSemistableComparison.Onto

universe w w'

namespace GlobalTheory.CompanionTheory.Onto

variable {R : Type} [CommRing R]

abbrev prodCx {I : Type} (K : I → Cx.{w} R) : Cx.{w} R where
  X n := ∀ i, (K i).X n
  d n := LinearMap.pi fun i => ((K i).d n).comp (LinearMap.proj i)
  dd n x := funext fun i => (K i).dd n (x i)

def prodHom {I : Type} {K : I → Cx.{w} R} {L : I → Cx.{w'} R}
    (φ : ∀ i, Cx.Hom (K i) (L i) (RingHom.id R)) : Cx.Hom (prodCx K) (prodCx L) (RingHom.id R) where
  f n := LinearMap.pi fun i => ((φ i).f n).comp (LinearMap.proj i)
  comm n x := funext fun i => (φ i).comm n (x i)

theorem mem_B_prod {I : Type} (K : I → Cx.{w} R) (n : ℕ) (a : (prodCx K).X n) :
    a ∈ (prodCx K).B n ↔ ∀ i, a i ∈ (K i).B n := by
  cases n with
  | zero =>
    constructor
    · intro h i
      have h0 : a = 0 := h
      rw [h0]
      exact Submodule.zero_mem _
    · intro h
      exact funext fun i => h i
  | succ n =>
    constructor
    · rintro ⟨b, rfl⟩ i
      exact ⟨b i, rfl⟩
    · intro h
      choose b hb using h
      exact ⟨b, funext hb⟩

theorem prod_bij {I : Type} {K : I → Cx.{w} R} {L : I → Cx.{w'} R}
    (φ : ∀ i, Cx.Hom (K i) (L i) (RingHom.id R))
    (h : ∀ i n, Function.Bijective ((φ i).mapH n)) (n : ℕ) :
    Function.Bijective ((prodHom φ).mapH n) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (prodCx K) n).1 x
    have hb : (prodCx L).d n ((prodHom φ).f n a) = 0 := by rw [(prodHom φ).comm, ha, map_zero]
    rw [CrystallineSemistableComparison.P.mapH_cls _ n a ha hb, (CrystallineSemistableComparison.P.cls_surj _ n).2.1 _ hb, mem_B_prod] at hx
    rw [(CrystallineSemistableComparison.P.cls_surj _ n).2.1, mem_B_prod]
    intro i
    have hai : (K i).d n (a i) = 0 := congrFun ha i
    have hbi : (L i).d n ((φ i).f n (a i)) = 0 := by rw [(φ i).comm, hai, map_zero]
    rw [← (CrystallineSemistableComparison.P.cls_surj _ n).2.1 _ hai]
    apply (injective_iff_map_eq_zero _).1 (h i n).1
    rw [CrystallineSemistableComparison.P.mapH_cls _ n _ hai hbi, (CrystallineSemistableComparison.P.cls_surj _ n).2.1]
    exact hx i
  · intro y
    obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (prodCx L) n).1 y
    have hbi : ∀ i, (L i).d n (b i) = 0 := fun i => congrFun hb i
    have key : ∀ i, ∃ a, ∃ ha : (K i).d n a = 0, (φ i).f n a - b i ∈ (L i).B n := by
      intro i
      obtain ⟨x, hx⟩ := (h i n).2 ((L i).cls (b i) (hbi i))
      obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (K i) n).1 x
      have hc : (L i).d n ((φ i).f n a) = 0 := by rw [(φ i).comm, ha, map_zero]
      rw [CrystallineSemistableComparison.P.mapH_cls _ n a ha hc] at hx
      exact ⟨a, ha, ((CrystallineSemistableComparison.P.cls_surj _ n).2.2.1 _ _ hc (hbi i)).1 hx⟩
    choose a ha hab using key
    have ha' : (prodCx K).d n a = 0 := funext ha
    have hc : (prodCx L).d n ((prodHom φ).f n a) = 0 := by rw [(prodHom φ).comm, ha', map_zero]
    refine ⟨(prodCx K).cls a ha', ?_⟩
    rw [CrystallineSemistableComparison.P.mapH_cls (prodHom φ) n a ha' hc, (CrystallineSemistableComparison.P.cls_surj _ n).2.2.1 _ _ hc hb, mem_B_prod]
    exact hab

variable {ι : Type} [DecidableEq ι]

abbrev cechCos (A : Sy.{w} R ι) : CosCx.{w} R where
  K p := prodCx fun i : Fin (p + 1) → ι => A.K (ent i)
  δ p k :=
    { f := fun q => (A.term q).cech.δ p k
      comm := fun q x => funext fun t => (A.res (ent_comp t k.succAbove)).comm q (x (t ∘ k.succAbove)) }
  rel p j i q x := (A.term q).cech.rel p j i x

def cechAug (A : Sy.{w} R ι) (hA : A.Desc) : DCx.AugRow (A.K ∅) (cechCos A).dcx where
  ε q := (A.term q).aug
  hε q x := (hA q).1 x
  comm q x := funext fun t => (A.res (Finset.empty_subset (ent t))).comm q x

theorem cechAug_row (A : Sy.{w} R ι) (hA : A.Desc) (q : ℕ) :
    ((cechCos A).dcx.row q).ResUpTo 1 ((cechAug A hA).ε q) := hA q

def cechHom {A B : Sy.{w} R ι} (m : A.Hom B) :
    DCx.Hom (cechCos A).dcx (cechCos B).dcx (RingHom.id R) where
  f p q := (prodHom fun i : Fin (p + 1) → ι => m.φ (ent i)).f q
  ch p q x := by
    rw [Cos.d_apply, Cos.d_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul]
    refine congrArg _ (funext fun t => ?_)
    exact (m.nat (ent_comp t k.succAbove) q (x (t ∘ k.succAbove))).symm
  cv p q x := (prodHom fun i : Fin (p + 1) → ι => m.φ (ent i)).comm q x

theorem cechHom_col {A B : Sy.{w} R ι} (m : A.Hom B)
    (h : ∀ S : Finset ι, S.Nonempty → ∀ n, Function.Bijective ((m.φ S).mapH n)) (p q : ℕ) :
    Function.Bijective (((cechHom m).col p).mapH q) :=
  prod_bij (fun i : Fin (p + 1) → ι => m.φ (ent i))
    (fun i n => h _ ⟨i 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩ n) q

theorem upTo_one {M : Type w} {N : Type w'} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) : UpTo (1 : R) f ↔ Function.Bijective f := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(injective_iff_map_eq_zero f).2 fun x hx => ?_, fun y => ?_⟩
    · simpa using h1 x hx
    · simpa using h2 y
  · intro h
    refine ⟨fun x hx => ?_, fun y => ?_⟩
    · rw [one_smul]
      exact (injective_iff_map_eq_zero f).1 h.1 x hx
    · simpa using h.2 y

theorem cls_congr {K : Cx.{w} R} {n : ℕ} {a b : K.X n} (h : a = b) (ha : K.d n a = 0) (hb : K.d n b = 0) :
    K.cls a ha = K.cls b hb := by
  subst h; rfl

theorem edge_square {A B : Sy.{w} R ι} (m : A.Hom B) (hA : A.Desc) (hB : B.Desc) (n : ℕ) (a : (A.K ∅).X n) :
    (cechHom m).tot.f n ((cechAug A hA).edge.f n a) = (cechAug B hB).edge.f n ((m.φ ∅).f n a) := by
  apply Subtype.ext
  funext p q
  by_cases h : p = 0 ∧ q = n
  · obtain ⟨rfl, rfl⟩ := h
    change (cechHom m).f 0 q ((cechCos A).dcx.sgl 0 q ((cechAug A hA).ε q a) 0 q) =
      (cechCos B).dcx.sgl 0 q ((cechAug B hB).ε q ((m.φ ∅).f q a)) 0 q
    rw [DCx.sgl_self, DCx.sgl_self]
    funext t
    exact m.nat (Finset.empty_subset (ent t)) q a
  · have h' : p ≠ 0 ∨ q ≠ n := by omega
    change (cechHom m).f p q ((cechCos A).dcx.sgl 0 n ((cechAug A hA).ε n a) p q) =
      (cechCos B).dcx.sgl 0 n ((cechAug B hB).ε n ((m.φ ∅).f n a)) p q
    rw [DCx.sgl_ne _ _ h', DCx.sgl_ne _ _ h', map_zero]

theorem mapH_empty_bij {A B : Sy.{w} R ι} (m : A.Hom B) (hA : A.Desc) (hB : B.Desc)
    (h : ∀ S : Finset ι, S.Nonempty → ∀ n, Function.Bijective ((m.φ S).mapH n)) (n : ℕ) :
    Function.Bijective ((m.φ ∅).mapH n) := by
  have eA : Function.Bijective ((cechAug A hA).edge.mapH n) := by
    have := CrystallineSemistableComparison.P.dc_row (cechAug A hA) 1 (cechAug_row A hA) n
    rw [one_pow] at this
    exact (upTo_one _).1 this
  have eB : Function.Bijective ((cechAug B hB).edge.mapH n) := by
    have := CrystallineSemistableComparison.P.dc_row (cechAug B hB) 1 (cechAug_row B hB) n
    rw [one_pow] at this
    exact (upTo_one _).1 this
  have eT : Function.Bijective ((cechHom m).tot.mapH n) := by
    have := CrystallineSemistableComparison.P.dc_map_col (cechHom m) 1 n fun p q _ => (upTo_one _).2 (cechHom_col m h p q)
    rw [one_pow] at this
    exact (upTo_one _).1 this
  have sq : ∀ x, (cechAug B hB).edge.mapH n ((m.φ ∅).mapH n x) =
      (cechHom m).tot.mapH n ((cechAug A hA).edge.mapH n x) := by
    intro x
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (A.K ∅) n).1 x
    have c1 : (B.K ∅).d n ((m.φ ∅).f n a) = 0 := by rw [(m.φ ∅).comm, ha, map_zero]
    have c2 : (cechCos B).dcx.tot.d n ((cechAug B hB).edge.f n ((m.φ ∅).f n a)) = 0 := by
      rw [(cechAug B hB).edge.comm, c1, map_zero]
    have c3 : (cechCos A).dcx.tot.d n ((cechAug A hA).edge.f n a) = 0 := by
      rw [(cechAug A hA).edge.comm, ha, map_zero]
    have c4 : (cechCos B).dcx.tot.d n ((cechHom m).tot.f n ((cechAug A hA).edge.f n a)) = 0 := by
      rw [(cechHom m).tot.comm, c3, map_zero]
    rw [CrystallineSemistableComparison.P.mapH_cls (m.φ ∅) n a ha c1, CrystallineSemistableComparison.P.mapH_cls (cechAug B hB).edge n _ c1 c2,
      CrystallineSemistableComparison.P.mapH_cls (cechAug A hA).edge n a ha c3, CrystallineSemistableComparison.P.mapH_cls (cechHom m).tot n _ c3 c4]
    exact cls_congr (edge_square m hA hB n a).symm c2 c4
  constructor
  · intro x y hxy
    apply eA.1
    apply eT.1
    rw [← sq, ← sq, hxy]
  · intro y
    obtain ⟨u, hu⟩ := eT.2 ((cechAug B hB).edge.mapH n y)
    obtain ⟨x, rfl⟩ := eA.2 u
    refine ⟨x, eB.1 ?_⟩
    rw [sq, hu]

theorem mvBij : CrystallineSemistableComparison.Onto.MVBij := fun _ _ _ _ _ _ m hA hB h n => mapH_empty_bij m hA hB h n

end GlobalTheory.CompanionTheory.Onto
