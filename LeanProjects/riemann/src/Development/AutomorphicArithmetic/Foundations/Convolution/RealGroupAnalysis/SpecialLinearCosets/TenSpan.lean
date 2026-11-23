import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.FockGen

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical nonZeroDivisors

noncomputable section

namespace UpperTheory.ConvolutionTheory.R2.I

section Fin

variable {F : Type} [Field F] [NumberField F] (v : P F)

private def sf (x : Kv v) : Af F := (sg v x).2

private theorem sf_self (x : Kv v) : sf v x v = x := by
  change GroundTheory.Automorphic.AdelicGLn.finiteAdeleSingleAdd v x v = x
  rw [GroundTheory.Automorphic.AdelicGLn.finiteAdeleSingleAdd_apply, Pi.single_eq_same]

private theorem sf_ne (x : Kv v) {w : P F} (h : w ≠ v) : sf v x w = 0 := by
  change GroundTheory.Automorphic.AdelicGLn.finiteAdeleSingleAdd v x w = 0
  rw [GroundTheory.Automorphic.AdelicGLn.finiteAdeleSingleAdd_apply, Pi.single_eq_of_ne h]

private theorem extF {a b : Af F} (h : ∀ w : P F, a w = b w) : a = b := FiniteAdeleRing.ext F h

private theorem sf_sub (x y : Kv v) : sf v (x - y) = sf v x - sf v y := by
  refine extF fun w => ?_
  change _ = sf v x w - sf v y w
  by_cases h : w = v
  · subst h
    simp only [sf_self]
  · simp only [sf_ne _ _ h, sub_zero]

private theorem cont_sf : Continuous (sf v) :=
  continuous_snd.comp (continuous_const.prodMk (GroundTheory.Global.continuous_finiteAdeleSingleAdd (K := F) v))

private theorem cont_ev : Continuous fun x : Af F => x v :=
  RestrictedProduct.continuous_eval v

private def rm (x : Af F) : Af F := x - sf v (x v)

private theorem cont_rm : Continuous (rm v) :=
  continuous_id.sub ((cont_sf v).comp (cont_ev v))

private theorem rm_self (x : Af F) : rm v x v = 0 := by
  change x v - sf v (x v) v = 0
  rw [sf_self, sub_self]

private theorem mem_split (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (z : Af F) :
    z ∈ idealFiniteAdeles J ↔ rm v z ∈ idealFiniteAdeles J ∧ sf v (z v) ∈ idealFiniteAdeles J := by
  constructor
  · intro h
    have h2 : sf v (z v) ∈ idealFiniteAdeles J := by
      rw [mem_idealFiniteAdeles] at h ⊢
      intro w
      by_cases hw : w = v
      · subst hw
        rw [sf_self]
        exact h w
      · rw [sf_ne _ _ hw, map_zero]
        exact zero_le
    exact ⟨sub_mem h h2, h2⟩
  · rintro ⟨h1, h2⟩
    have := add_mem h1 h2
    rwa [rm, sub_add_cancel] at this

variable (θ : Kv v)

private def mF (y : Fin 4 → Af F) : M2 v :=
  !![y 1 v, y 2 v + y 3 v * θ; y 2 v - y 3 v * θ, y 0 v]

private def co (m : M2 v) : Fin 4 → Kv v :=
  ![m 1 1, m 0 0, (m 0 1 + m 1 0) / 2, (m 0 1 - m 1 0) / (2 * θ)]

private theorem two_ne : (2 : Kv v) ≠ 0 := by
  intro h
  have h2 : algebraMap F (Kv v) 2 = 0 := by rw [map_ofNat]; exact h
  exact two_ne_zero ((map_eq_zero _).1 h2)

private theorem cont_mF : Continuous (mF v θ) := by
  refine continuous_matrix fun i j => ?_
  have e : ∀ k : Fin 4, Continuous fun y : Fin 4 → Af F => y k v := fun k =>
    (cont_ev v).comp (continuous_apply k)
  fin_cases i <;> fin_cases j
  · exact e 1
  · exact (e 2).add ((e 3).mul continuous_const)
  · exact (e 2).sub ((e 3).mul continuous_const)
  · exact e 0

private theorem cont_co : Continuous (co v θ) := by
  refine continuous_pi fun i => ?_
  have e : ∀ a b : Fin 2, Continuous fun m : M2 v => m a b := fun a b => continuous_id.matrix_elem a b
  fin_cases i
  · exact e 1 1
  · exact e 0 0
  · exact ((e 0 1).add (e 1 0)).div_const _
  · exact ((e 0 1).sub (e 1 0)).div_const _

private theorem co_mF (hθ : θ ≠ 0) (y : Fin 4 → Af F) (i : Fin 4) : co v θ (mF v θ y) i = y i v := by
  have h2 := two_ne v
  fin_cases i
  · rfl
  · rfl
  · change (y 2 v + y 3 v * θ + (y 2 v - y 3 v * θ)) / 2 = y 2 v
    field_simp
    ring
  · change (y 2 v + y 3 v * θ - (y 2 v - y 3 v * θ)) / (2 * θ) = y 3 v
    field_simp
    ring

private theorem mF_co (hθ : θ ≠ 0) (m : M2 v) (a : Fin 4 → Af F) :
    mF v θ (fun i => rm v (a i) + sf v (co v θ m i)) = m := by
  have h2 := two_ne v
  have e : ∀ i, (rm v (a i) + sf v (co v θ m i)) v = co v θ m i := fun i => by
    change rm v (a i) v + sf v (co v θ m i) v = _
    rw [rm_self, sf_self, zero_add]
  refine Matrix.ext fun i j => ?_
  simp only [mF, e]
  fin_cases i <;> fin_cases j
  · rfl
  · change (m 0 1 + m 1 0) / 2 + (m 0 1 - m 1 0) / (2 * θ) * θ = m 0 1
    field_simp
    ring
  · change (m 0 1 + m 1 0) / 2 - (m 0 1 - m 1 0) / (2 * θ) * θ = m 1 0
    field_simp
    ring
  · rfl

private theorem ten_mem (hθ : θ ≠ 0) {g : (Fin 4 → Af F) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi F)
    {b : M2 v → ℂ} (hb : b ∈ SB (M2 v)) :
    (fun y : Fin 4 → Af F => g (fun i => rm v (y i)) * b (mF v θ y)) ∈ finiteSchwartzBruhatPi F := by
  have hb' := GroundTheory.LocalField.mem_schwartzBruhat.1 hb
  have hrm : Continuous fun y : Fin 4 → Af F => fun i => rm v (y i) :=
    continuous_pi fun i => (cont_rm v).comp (continuous_apply i)
  refine ⟨(hg.1.comp_continuous hrm).mul (hb'.1.comp_continuous (cont_mF v θ)), ?_⟩
  have hc : Continuous fun p : (Fin 4 → Af F) × M2 v => fun i => p.1 i + sf v (co v θ p.2 i) :=
    continuous_pi fun i => ((continuous_apply i).comp continuous_fst).add
      ((cont_sf v).comp ((continuous_apply i).comp ((cont_co v θ).comp continuous_snd)))
  refine HasCompactSupport.intro (((show IsCompact (tsupport g) from hg.2).prod
    (show IsCompact (tsupport b) from hb'.2)).image hc) fun y hy => ?_
  by_contra hne
  refine hy ⟨((fun i => rm v (y i)), mF v θ y), ⟨?_, ?_⟩, ?_⟩
  · exact subset_tsupport _ (left_ne_zero_of_mul hne)
  · exact subset_tsupport _ (right_ne_zero_of_mul hne)
  · funext i
    change rm v (y i) + sf v (co v θ (mF v θ y) i) = y i
    rw [co_mF v θ hθ, rm, sub_add_cancel]

private theorem coset_ten (hθ : θ ≠ 0) (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (a : Fin 4 → Af F) :
    ∃ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4), ∃ b ∈ SB (M2 v), ∀ y : Fin 4 → Af F,
      finiteTensor (fun i => cosetIndicator J (a i)) y = g (fun i => rm v (y i)) * b (mF v θ y) := by
  have hG : finiteTensor (fun i => cosetIndicator J (a i)) ∈ finiteSchwartzBruhatPi F :=
    finiteTensor_mem fun i => cosetIndicator_mem_finiteSchwartzBruhat J (a i)
  refine ⟨finiteTensor fun i => cosetIndicator J (rm v (a i)),
    finiteTensor_mem fun i => cosetIndicator_mem_finiteSchwartzBruhat J _,
    fun m => finiteTensor (fun i => cosetIndicator J (a i)) fun i => rm v (a i) + sf v (co v θ m i), ?_, ?_⟩
  · have hc : Continuous fun m : M2 v => fun i => rm v (a i) + sf v (co v θ m i) :=
      continuous_pi fun i => continuous_const.add
        ((cont_sf v).comp ((continuous_apply i).comp (cont_co v θ)))
    have hcl : IsClosedEmbedding fun m : M2 v => fun i => rm v (a i) + sf v (co v θ m i) :=
      Function.LeftInverse.isClosedEmbedding (f := mF v θ) (fun m => mF_co v θ hθ m a) (cont_mF v θ) hc
    exact GroundTheory.LocalField.mem_schwartzBruhat.2 ⟨hG.1.comp_continuous hc, hG.2.comp_isClosedEmbedding hcl⟩
  · intro y
    simp only [finiteTensor, co_mF v θ hθ]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have e1 : rm v (y i) - rm v (a i) = rm v (y i - a i) := by
      simp only [rm]
      change _ = y i - a i - sf v (y i v - a i v)
      rw [sf_sub]
      abel
    have e2 : rm v (a i) + sf v (y i v) - a i = sf v ((y i - a i) v) := by
      simp only [rm]
      change _ = sf v (y i v - a i v)
      rw [sf_sub]
      abel
    rw [cosetIndicator_apply, cosetIndicator_apply, cosetIndicator_apply, e1, e2]
    have hm := mem_split v J (y i - a i)
    by_cases h : y i - a i ∈ idealFiniteAdeles J
    · obtain ⟨h1, h2⟩ := hm.1 h
      rw [if_pos h, if_pos h1, if_pos h2, one_mul]
    · rw [if_neg h]
      by_cases h1 : rm v (y i - a i) ∈ idealFiniteAdeles J
      · rw [if_pos h1, one_mul, if_neg fun h2 => h (hm.2 ⟨h1, h2⟩)]
      · rw [if_neg h1, zero_mul]

end Fin

section Main

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : P F)

private theorem pInf_away (X : V4 F) (i : Fin 4) : TR.pInf F (away v X i) = TR.pInf F (X i) := by
  have h0 : TR.pInf F (sg v (cp v (X i))) = 0 := by
    change (TR.infEq F).symm 0 = 0
    exact map_zero _
  simp only [away, map_sub, h0, sub_zero]

private theorem poly_away {p : V4 F → ℂ} (hp : p ∈ polyFn (F := F)) (X : V4 F) : p (away v X) = p X := by
  refine Algebra.adjoin_induction (p := fun p _ => p (away v X) = p X) ?_ ?_ ?_ ?_ hp
  · rintro _ ⟨i, w, rfl⟩
    simp only [pInf_away]
  · intro c
    rfl
  · intro f g _ _ hf hg
    simp only [Pi.add_apply, hf, hg]
  · intro f g _ _ hf hg
    simp only [Pi.mul_apply, hf, hg]

private theorem gauss_away (δ : F) (X : V4 F) : gauss δ (away v X) = gauss δ X := by
  simp only [gauss, map_add, map_sub, map_mul, map_pow, pInf_away]

private theorem ten_eq (θ : Kv v) (δ : F) (p : V4 F → ℂ) (hp : p ∈ polyFn (F := F))
    (g : (Fin 4 → Af F) → ℂ) (b : M2 v → ℂ) (X : V4 F) :
    ten v θ (fun Y => p Y * gauss δ Y * g (finPartPi Y)) b X =
      p X * gauss δ X * (fun y : Fin 4 → Af F => g (fun i => rm v (y i)) * b (mF v θ y)) (finPartPi X) := by
  simp only [ten, poly_away v hp, gauss_away]
  rw [mul_assoc]
  rfl

private theorem good (θ : Kv v) (hθ : θ ≠ 0) (δ : F) (hδ : ∀ φ : F →+* ℝ, φ δ < 0) (p : V4 F → ℂ)
    (hp : p ∈ polyFn (F := F)) {g : (Fin 4 → Af F) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi F) :
    GoodU v δ θ fun Y => p Y * gauss δ Y * g (finPartPi Y) := by
  intro b hb
  have hG := ten_mem v θ hθ hg hb
  refine ⟨⟨_, fockGen F δ hδ p hp _ hG⟩, Submodule.subset_span ⟨p, hp, _, hG, rfl⟩, ?_⟩
  funext X
  exact (ten_eq v θ δ p hp g b X).symm

end Main

end UpperTheory.ConvolutionTheory.R2.I

end

theorem UpperTheory.ConvolutionTheory.R2.I.tenSpan :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (v : P F) (δ : F) (θ : Kv v), (∀ φ : F →+* ℝ, φ δ < 0) → θ ≠ 0 →
      Fock δ ≤ Submodule.span ℂ {φ : S4 F | ∃ u b, GoodU v δ θ u ∧ b ∈ SB (M2 v) ∧ φ.1 = ten v θ u b} := by
  intro F _ _ _ v δ θ hδ hθ φ hφ
  set T := Submodule.span ℂ {φ : S4 F | ∃ u b, GoodU v δ θ u ∧ b ∈ SB (M2 v) ∧ φ.1 = ten v θ u b} with hT
  have key : ∀ p ∈ polyFn (F := F), ∀ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4),
      (fun X => p X * gauss δ X * g (finPartPi X)) ∈ T.map (schwartzBruhatPi F (Fin 4)).subtype := by
    intro p hp g hg
    rw [finiteSchwartzBruhatPi_eq_span] at hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨J, a⟩, rfl⟩ := hx
      obtain ⟨g1, hg1, b, hb, he⟩ := coset_ten v θ hθ J a
      obtain ⟨φ1, -, hφ1⟩ := good v θ hθ δ hδ p hp hg1 b hb
      refine ⟨φ1, Submodule.subset_span ⟨_, b, good v θ hθ δ hδ p hp hg1, hb, hφ1⟩, ?_⟩
      funext X
      change φ1.1 X = _
      rw [hφ1, ten_eq v θ δ p hp g1 b X]
      simp only [he]
    | zero =>
      have : (fun X : V4 F => p X * gauss δ X * (0 : (Fin 4 → Af F) → ℂ) (finPartPi X)) = 0 := by
        funext X
        simp
      rw [this]
      exact zero_mem _
    | add x y _ _ hx hy =>
      have : (fun X : V4 F => p X * gauss δ X * (x + y) (finPartPi X)) =
          (fun X => p X * gauss δ X * x (finPartPi X)) + fun X => p X * gauss δ X * y (finPartPi X) := by
        funext X
        simp only [Pi.add_apply, mul_add]
      rw [this]
      exact add_mem hx hy
    | smul c x _ hx =>
      have : (fun X : V4 F => p X * gauss δ X * (c • x) (finPartPi X)) =
          c • fun X => p X * gauss δ X * x (finPartPi X) := by
        funext X
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [this]
      exact Submodule.smul_mem _ _ hx
  have hle : Submodule.span ℂ {φ : V4 F → ℂ | ∃ p ∈ polyFn (F := F), ∃ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4),
      φ = fun v => p v * gauss δ v * g (finPartPi v)} ≤ T.map (schwartzBruhatPi F (Fin 4)).subtype :=
    Submodule.span_le.2 (by
      rintro _ ⟨p, hp, g, hg, rfl⟩
      exact key p hp g hg)
  obtain ⟨ψ', hψ, he⟩ := hle hφ
  have : ψ' = φ := Subtype.ext he
  exact this ▸ hψ
