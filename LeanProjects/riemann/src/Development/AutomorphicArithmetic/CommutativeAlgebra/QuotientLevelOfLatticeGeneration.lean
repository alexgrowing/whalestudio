import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.LevelActionGenerator

variable {X : Scheme.{0}}

private theorem pb_mul {A B : Over X} [GrpObj A] [GrpObj B] {φ : A.left ⟶ B.left}
    (h : IsGrpPullback A B (𝟙 X) φ) (f : A ⟶ B) (hf : f.left = φ) {T : Over X} (x y : T ⟶ A) :
    (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
  let e : Over.mk (T.hom ≫ 𝟙 X) ≅ T := Over.isoMk (Iso.refl _) (by simp)
  have he : e.hom.left = 𝟙 _ := rfl
  have key := h.2 T x y (e.hom ≫ x ≫ f) (e.hom ≫ y ≫ f)
    (by rw [Over.comp_left, Over.comp_left, he, Category.id_comp, hf])
    (by rw [Over.comp_left, Over.comp_left, he, Category.id_comp, hf])
  rw [← MonObj.comp_mul, Over.comp_left, he, Category.id_comp] at key
  apply Over.OverMorphism.ext
  rw [key, Over.comp_left, hf]

private theorem pb_one {A B : Over X} [GrpObj A] [GrpObj B] {φ : A.left ⟶ B.left}
    (h : IsGrpPullback A B (𝟙 X) φ) (f : A ⟶ B) (hf : f.left = φ) {T : Over X} :
    (1 : T ⟶ A) ≫ f = 1 := by
  have h1 := pb_mul h f hf (1 : T ⟶ A) 1
  rw [_root_.mul_one] at h1
  simpa using h1

private theorem act_nat {O : Type} [Ring O] {A : Over X} [GrpObj A] [IsCommMonObj A] (act : OActN O A) {T : Over X}
    (u : T ⟶ A) (m : ℕ) : u ≫ act.act (m : O) = u ^ m := by
  induction m with
  | zero =>
    have h0 : act.act (0 : O) = 1 := by
      have := act.add 0 0
      rw [add_zero] at this
      simpa using this
    rw [Nat.cast_zero, h0, pow_zero, MonObj.comp_one]
  | succ m ih =>
    rw [Nat.cast_succ, act.add, act.one, MonObj.comp_mul, ih, Category.comp_id, pow_succ]

private theorem gen_mem {A : Type} [CommRing A] {a : A} {N : ℕ} {𝔞 : Ideal A} (h : IsGen a N 𝔞) : (N : A) ∈ 𝔞 := by
  have h' : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 = Ideal.span {(N : A)} := h
  have hm : (N : A) ∈ (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 := by
    rw [h']
    exact Ideal.subset_span (Set.mem_singleton _)
  exact (Ideal.mul_le_right (I := Ideal.span {a} ⊔ Ideal.span {(N : A)}) (J := 𝔞)) hm

end UpperTheory.LevelActionGenerator

open UpperTheory.LevelActionGenerator in
theorem UpperTheory.quotient_level_of_lattice_generation :
    LatGen → QLev := by
  intro hLat q _ D R R' _ _ _ b gb N N₀ c a 𝔞 hN hgen X s s₀ o o₀ n
  have hw : n.φ ≫ o₀.A.hom = o.A.hom := by simpa using n.cart.1.w
  haveI : IsIso n.φ := n.cart.1.isIso_fst_of_isIso
  let f : o.A ⟶ o₀.A := Over.homMk n.φ hw
  let g : o₀.A ⟶ o.A := Over.homMk (inv n.φ) (by rw [IsIso.inv_comp_eq, hw])
  have hfl : f.left = n.φ := rfl
  have hfg : f ≫ g = 𝟙 _ := by
    apply Over.OverMorphism.ext
    simp [f, g]
  have hgf : g ≫ f = 𝟙 _ := by
    apply Over.OverMorphism.ext
    simp [f, g]
  have hinj : ∀ {T : Over X} (u v : T ⟶ o.A), u ≫ f = v ≫ f → u = v := by
    intro T u v huv
    have := congrArg (· ≫ g) huv
    simpa [Category.assoc, hfg] using this
  have hmul : ∀ {T : Over X} (u v : T ⟶ o.A), (u * v) ≫ f = (u ≫ f) * (v ≫ f) :=
    fun u v => pb_mul n.cart f hfl u v
  have hone : ∀ {T : Over X}, (1 : T ⟶ o.A) ≫ f = 1 := pb_one n.cart f hfl
  have hone' : ∀ {T : Over X}, (1 : T ⟶ o₀.A) ≫ g = 1 := by
    intro T
    apply hinj
    rw [Category.assoc, hgf, Category.comp_id, hone]
  have hact : ∀ c' : D.O, o.act.act c' ≫ f = f ≫ o₀.act.act c' := by
    intro c'
    apply Over.OverMorphism.ext
    simp only [Over.comp_left]
    exact n.act c'
  have e_add : ∀ u v : D.La, o.eta (u + v) = o.eta u * o.eta v := fun u v => o.eta_add u v
  have e_lin : ∀ (c' : D.O) (u : D.La), o.eta (c' • u) = o.eta u ≫ o.act.act c' :=
    fun c' u => o.eta_lin c' u
  have e_ker : ∀ u : D.La, o.eta (N • u) = 1 := fun u => o.eta_ker u
  obtain ⟨hL1, hL2⟩ := hLat q D a N 𝔞 hN hgen
  refine ⟨fun y => o.eta (algebraMap (𝓞 D.F) D.O a • y) ≫ f, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro y z
    simp only
    rw [smul_add, e_add, hmul]
  · intro c' y
    simp only
    have hcomm : algebraMap (𝓞 D.F) D.O a • (c' • y) = c' • (algebraMap (𝓞 D.F) D.O a • y) := by
      rw [smul_smul, smul_smul, Algebra.commutes]
    rw [hcomm, e_lin, Category.assoc, hact, Category.assoc]
  · intro y hy
    obtain ⟨z, hz⟩ := (hL1 y).2 hy
    simp only
    rw [hz, e_ker, hone]
  · intro k _ _ x
    have hβ : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := by
      simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]
    obtain ⟨I, hI⟩ := o.geom k x _ hβ
    have hI' : ∀ y : D.La, toUnit (Over.mk x) ≫ o.eta y = I.ev N y := fun y => hI y
    have I_add : ∀ u v : D.La, I.ev N (u + v) = I.ev N u * I.ev N v := fun u v => I.add N u v
    have I_lin : ∀ (c' : D.O) (u : D.La), I.ev N (c' • u) = I.ev N u ≫ o.act.act c' :=
      fun c' u => I.lin N c' u
    have I_ker : ∀ u : D.La, I.ev N u = 1 ↔ ∃ v : D.La, u = N • v := fun u => I.ker N hN u
    have I_onto : ∀ r : Over.mk x ⟶ o.A, r ^ N = 1 ↔ ∃ u : D.La, I.ev N u = r :=
      fun r => I.onto N hN r
    constructor
    · intro y hy
      simp only at hy
      rw [← Category.assoc, ← hone] at hy
      have h1 := hinj _ _ hy
      rw [hI'] at h1
      obtain ⟨z, hz⟩ := (I_ker _).1 h1
      exact (hL1 y).1 ⟨z, hz⟩
    · intro g₀ hg₀
      have hg'act : ∀ c' : D.O, (g₀ ≫ g) ≫ o.act.act c' = (g₀ ≫ o₀.act.act c') ≫ g := by
        intro c'
        apply hinj
        simp only [Category.assoc, hact, reassoc_of% hgf, hgf, Category.comp_id]
      have hkill : ∀ c' ∈ 𝔞, (g₀ ≫ g) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c') = 1 := by
        intro c' hc'
        rw [hg'act, hg₀ c' (by rwa [pow_one]), hone']
      have hpow : (g₀ ≫ g) ^ N = 1 := by
        have hn := act_nat o.act (g₀ ≫ g) N
        have hc : ((N : ℕ) : D.toG.O) = algebraMap (𝓞 D.F) D.O (N : 𝓞 D.F) := (map_natCast _ N).symm
        rw [hc] at hn
        rw [← hn]
        exact hkill _ (gen_mem hgen)
      obtain ⟨x', hx'⟩ := (I_onto (g₀ ≫ g)).1 hpow
      have hcond : ∀ c' ∈ 𝔞, ∃ z : D.La, algebraMap (𝓞 D.F) D.O c' • x' = N • z := by
        intro c' hc'
        apply (I_ker _).1
        rw [I_lin, hx']
        exact hkill c' hc'
      obtain ⟨y, z, hyz⟩ := hL2 x' hcond
      refine ⟨y, ?_⟩
      have hyI : toUnit (Over.mk x) ≫ o.eta (algebraMap (𝓞 D.F) D.O a • y) = g₀ ≫ g := by
        rw [hI', ← hx', hyz, I_add, (I_ker (N • z)).2 ⟨z, rfl⟩, _root_.mul_one]
      simp only
      rw [← Category.assoc, hyI, Category.assoc, hgf, Category.comp_id]
  · intro y
    rfl
