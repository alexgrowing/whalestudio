import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective

noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory

namespace GlobalTheory.PDivGroup.Test

open PDiv

variable {p : ℕ} {O : Type} [CommRing O]

@[reducible] def triv (p : ℕ) (O : Type) [CommRing O] : PDivGroup p O where
  height := 0
  A _ := O
  rank_eq n q := by
    have := q.nontrivial
    simp [rankAtStalk_eq_finrank_of_free]
  res _ := BialgHom.id O O
  res_surjective _ := Function.surjective_id
  ker_res n := by
    refine le_antisymm (fun a ha => ?_) ?_
    · rw [show a = 0 from ha]; exact zero_mem _
    · refine (kerIdeal_le_ker_iff _ (AlgHom.id O O)).2 fun c => ?_
      simpa using (mulBy O O (p ^ n) : O →ₐ[O] O).commutes c

theorem height_eq_of_iso [Fact p.Prime] [Nontrivial O] {G H : PDivGroup p O} (e : G ≅ H) :
    G.height = H.height := by
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum O) := inferInstance
  have h1 : ∀ a, e.hom.app 1 (e.inv.app 1 a) = a := fun a =>
    DFunLike.congr_fun (congrArg (fun f => Hom.app f 1) e.hom_inv_id) a
  have h2 : ∀ a, e.inv.app 1 (e.hom.app 1 a) = a := fun a =>
    DFunLike.congr_fun (congrArg (fun f => Hom.app f 1) e.inv_hom_id) a
  let l : H.A 1 ≃ₗ[O] G.A 1 :=
    { toFun := e.hom.app 1, map_add' := map_add _, map_smul' := map_smul _,
      invFun := e.inv.app 1, left_inv := h2, right_inv := h1 }
  have h := fibreDim_congr l q
  rw [fibreDim_eq, fibreDim_eq, one_mul, one_mul] at h
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h).symm

theorem not_iso_mu_const [Fact p.Prime] (hp : ¬ IsUnit (p : O)) :
    IsEmpty (mu p O ≅ const p O) := ⟨fun e => dlogT_ne_zero p O hp <| by
  have h := LinearMap.congr_fun (omegaMap_comp e.hom e.inv) (dlogT p O)
  rw [e.hom_inv_id, omegaMap_id, LinearMap.id_apply, LinearMap.comp_apply,
    Subsingleton.elim (omegaMap (const p O) (mu p O) e.inv (dlogT p O)) 0, map_zero] at h
  exact h⟩

theorem padicAction_const_injective [Fact p.Prime] [Nontrivial O] :
    Function.Injective (padicAction (const p O)) := fun a b h => by
  apply toSpanSingleton_constGen_injective p O
  have key : ∀ c : ℤ_[p], tateMap _ _ O (padicAction (const p O) c) (constGen p O) =
      c • constGen p O := fun c => by
    change tateMap _ _ O (algebraMap ℤ_[p] (End (const p O)) c) _ = _
    rw [Algebra.algebraMap_eq_smul_one]
    change tateMap _ _ O (c • 𝟙 (const p O)) _ = _
    rw [map_smul, LinearMap.smul_apply, tateMap_id]
  simp only [LinearMap.toSpanSingleton_apply]
  rw [← key, ← key, h]

theorem level_zero (G : PDivGroup p O) (a : G.A 0) : a = algebraMap O _ (counit a) := by
  have h := G.mulBy_pow_self 0 a
  rwa [pow_zero, mulBy, pow_one] at h

open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory in
variable {p : ℕ} {O : Type} [CommRing O] in

theorem _root_.GlobalTheory.PDivGroup.Test.mulP_injective (G : _root_.GlobalTheory.PDivGroup p O) (n : ℕ) :
    Function.Injective (G.mulP n) := by
  intro x y hxy
  have hinj := _root_.GlobalTheory.CartierDual.map_injective_of_surjective (G.dual_mulP_surjective n)
  have hx := _root_.GlobalTheory.CartierDual.map_map_bidual (G.mulP n) x
  have hy := _root_.GlobalTheory.CartierDual.map_map_bidual (G.mulP n) y
  rw [hxy, ← hy] at hx
  exact (_root_.GlobalTheory.CartierDual.bidual O (G.A n)).injective (hinj hx)

theorem mu_tate_char_p [Fact p.Prime] (k : Type) [Field k] [CharP k p] (x : (mu p k).Tate) :
    x = 0 := muRoot_ext fun n => by
  rw [muRoot_zero]
  have h := muRoot_pow_self x n
  have h2 : (muRoot x n - 1) ^ p ^ n = 0 := by rw [sub_pow_char_pow, h, one_pow, sub_self]
  exact sub_eq_zero.1 (pow_eq_zero_iff (pow_pos (Fact.out : p.Prime).pos n).ne' |>.1 h2)

theorem omega_eq_zero_of_isUnit (G : PDivGroup p O) (hp : IsUnit (p : O)) (w : G.omega) :
    w = 0 := Subtype.ext (funext fun n =>
  (hp.pow n).smul_left_cancel.1 ((G.pow_smul_cot n _).trans (smul_zero _).symm))

theorem hodgeTate_values [Fact p.Prime] (hp : ¬ IsUnit (p : O)) :
    (∀ t, hodgeTate (mu p O) t = 0) ∧ hodgeTate (const p O) (constGen p O) ≠ 0 := by
  refine ⟨fun t => Subsingleton.elim _ _, fun h => dlogT_ne_zero p O hp ?_⟩
  rw [hodgeTate_eq_omegaMap, ← dualHom_constHom, show constHom _ (constGen p O) = 𝟙 _ by
    rw [← LinearEquiv.eq_symm_apply, constHom_symm_apply, tateMap_id], dualHom_id,
    Category.id_comp] at h
  have h2 := LinearMap.congr_fun (omegaMap_comp (mu p O).bidual.hom (mu p O).bidual.inv) (dlogT p O)
  rw [Iso.hom_inv_id, omegaMap_id, LinearMap.id_apply, LinearMap.comp_apply] at h2
  rw [h2]
  exact (congrArg _ h).trans (map_zero _)

theorem tate_torsionFree [Fact p.Prime] (G : PDivGroup p O) {B : Type} [CommRing B] [Algebra O B]
    (x : G.TateOver B) (h : (p : ℤ_[p]) • x = 0) : x = 0 := TateOver.ext_conv fun n => by
  have h1 := congrArg (fun y => TateOver.conv y (n + 1)) h
  simp only [TateOver.smul_conv, TateOver.zero_conv] at h1
  rw [pow_digit_natCast (G.pts_pow_self _ _), TateOver.conv_succ_pow] at h1
  refine ofConv_injective (AlgHom.ext fun a => ?_)
  obtain ⟨b, rfl⟩ := G.res_surjective n a
  have h3 := DFunLike.congr_fun (congrArg ofConv h1) b
  refine h3.trans ?_
  change algebraMap O B (counit b) = algebraMap O B (counit (G.res n b))
  rw [CoalgHomClass.counit_comp_apply]

example [Fact p.Prime] {G : PDivGroup p O} {Λ : Type} [Ring Λ] (ρ : Action Λ G) (a b : Λ)
    (t : G.Tate) : ρ.onTate O (a * b) t = ρ.onTate O a (ρ.onTate O b t) := by
  rw [map_mul]; rfl

section Prod

variable (A B : Type) [CommRing A] [CommRing B] [Bialgebra O A] [Bialgebra O B]

def inl : A →ₐc[O] A ⊗[O] B :=
  (Bialgebra.TensorProduct.map (BialgHom.id O A) (Bialgebra.unitBialgHom O B)).comp
    (Bialgebra.TensorProduct.rid O O A).symm.toBialgHom

def inr : B →ₐc[O] A ⊗[O] B :=
  (Bialgebra.TensorProduct.map (Bialgebra.unitBialgHom O A) (BialgHom.id O B)).comp
    (Bialgebra.TensorProduct.lid O B).symm.toBialgHom

variable {A B}

theorem inl_apply (a : A) : inl (O := O) A B a = a ⊗ₜ 1 :=
  congrArg (fun y : B => a ⊗ₜ[O] y) (map_one (Bialgebra.unitBialgHom O B))

theorem inr_apply (b : B) : inr (O := O) A B b = 1 ⊗ₜ b :=
  congrArg (fun y : A => y ⊗ₜ[O] b) (map_one (Bialgebra.unitBialgHom O A))

theorem pts_ext {E : Type} [CommRing E] [Algebra O E] {x y : WithConv (A ⊗[O] B →ₐ[O] E)}
    (h1 : pointsMap E (inl A B) x = pointsMap E (inl A B) y)
    (h2 : pointsMap E (inr A B) x = pointsMap E (inr A B) y) : x = y := by
  refine ofConv_injective (Algebra.TensorProduct.ext' fun a b => ?_)
  have e1 : x.ofConv (inl A B a) = y.ofConv (inl A B a) := DFunLike.congr_fun (congrArg ofConv h1) a
  have e2 : x.ofConv (inr A B b) = y.ofConv (inr A B b) := DFunLike.congr_fun (congrArg ofConv h2) b
  have e : a ⊗ₜ[O] b = inl A B a * inr A B b := by simp [inl_apply, inr_apply]
  rw [e, map_mul, map_mul, e1, e2]

end Prod

@[reducible] def prod (G H : PDivGroup p O) : PDivGroup p O where
  height := G.height + H.height
  A n := G.A n ⊗[O] H.A n
  rank_eq n q := by
    rw [rankAtStalk_tensorProduct, Pi.mul_apply, G.rank_eq, H.rank_eq, mul_add, pow_add]
  res n := Bialgebra.TensorProduct.map (G.res n) (H.res n)
  res_surjective n := TensorProduct.map_surjective (g := (G.res n).toLinearMap) (g' := (H.res n).toLinearMap) (G.res_surjective n) (H.res_surjective n)
  ker_res n := by
    refine le_antisymm (fun a ha => ?_) ?_
    · let π := Ideal.Quotient.mkₐ O (torsionIdeal O (G.A (n + 1) ⊗[O] H.A (n + 1)) (p ^ n))
      have h1 := (torsionIdeal_le_ker_iff (p ^ n) π).1
        fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
      obtain ⟨y, hy⟩ := (G.exists_comp_res_iff n (pointsMap _ (inl _ _) (toConv π)).ofConv).2
        (by rw [toConv_ofConv, ← map_pow, h1, map_one])
      obtain ⟨z, hz⟩ := (H.exists_comp_res_iff n (pointsMap _ (inr _ _) (toConv π)).ofConv).2
        (by rw [toConv_ofConv, ← map_pow, h1, map_one])
      have h2 : (Algebra.TensorProduct.lift y z fun _ _ => .all _ _).comp
          (Bialgebra.TensorProduct.map (G.res n) (H.res n) :
            G.A (n + 1) ⊗[O] H.A (n + 1) →ₐ[O] G.A n ⊗[O] H.A n) = π :=
        Algebra.TensorProduct.ext' fun a b => by
          have e1 : y (G.res n a) = π (inl _ _ a) := DFunLike.congr_fun hy a
          have e2 : z (H.res n b) = π (inr _ _ b) := DFunLike.congr_fun hz b
          change y (G.res n a) * z (H.res n b) = _
          rw [e1, e2, ← map_mul, inl_apply, inr_apply]
          simp
      have h3 := (DFunLike.congr_fun h2 a).symm
      rw [AlgHom.comp_apply] at h3
      erw [show Bialgebra.TensorProduct.map (G.res n) (H.res n) a = 0 from ha, map_zero] at h3
      exact Ideal.Quotient.eq_zero_iff_mem.1 h3
    · refine (torsionIdeal_le_ker_iff (p ^ n) (Bialgebra.TensorProduct.map (G.res n) (H.res n) :
          G.A (n + 1) ⊗[O] H.A (n + 1) →ₐ[O] G.A n ⊗[O] H.A n)).2 (pts_ext ?_ ?_)
      · rw [map_pow, map_one]
        refine (G.exists_comp_res_iff n _).1 ⟨(inl (O := O) (G.A n) (H.A n)).toAlgHom, AlgHom.ext fun a => ?_⟩
        change inl _ _ (G.res n a) = Bialgebra.TensorProduct.map (G.res n) (H.res n) (inl _ _ a)
        simp [inl_apply]
      · rw [map_pow, map_one]
        refine (H.exists_comp_res_iff n _).1 ⟨(inr (O := O) (G.A n) (H.A n)).toAlgHom, AlgHom.ext fun a => ?_⟩
        change inr _ _ (H.res n a) = Bialgebra.TensorProduct.map (G.res n) (H.res n) (inr _ _ a)
        simp [inr_apply]

def swap (G : PDivGroup p O) : End (prod G G) :=
  ⟨fun n => (Bialgebra.TensorProduct.comm O (G.A n) (G.A n)).toBialgHom, fun n =>
    BialgHom.coe_toAlgHom_injective (Algebra.TensorProduct.ext' fun _ _ => rfl)⟩

theorem swap_mul_swap (G : PDivGroup p O) : swap G * swap G = 1 :=
  hom_ext fun _ => BialgHom.coe_toAlgHom_injective (Algebra.TensorProduct.ext' fun _ _ => rfl)

def fst (G H : PDivGroup p O) : prod G H ⟶ G :=
  ⟨fun _ => inl _ _, fun n => BialgHom.ext fun a => by
    change Bialgebra.TensorProduct.map (G.res n) (H.res n) (inl _ _ a) = inl _ _ (G.res n a)
    simp [inl_apply]⟩

def incl (G H : PDivGroup p O) : G ⟶ prod G H :=
  ⟨fun n => (Bialgebra.TensorProduct.rid O O (G.A n)).toBialgHom.comp
      (Bialgebra.TensorProduct.map (BialgHom.id O _) (Bialgebra.counitBialgHom O _)),
    fun n => BialgHom.coe_toAlgHom_injective (Algebra.TensorProduct.ext' fun a b => by
      change G.res n (counit (R := O) b • a) = counit (R := O) (H.res n b) • G.res n a
      rw [map_smul, CoalgHomClass.counit_comp_apply])⟩

theorem incl_fst (G H : PDivGroup p O) : incl G H ≫ fst G H = 𝟙 G :=
  hom_ext fun n => BialgHom.ext fun a => by
    change (incl G H).app n (inl _ _ a) = a
    rw [inl_apply]
    change counit (R := O) (1 : H.A n) • a = a
    simp

theorem incl_swap_fst (G : PDivGroup p O) : incl G G ≫ swap G ≫ fst G G = 0 :=
  hom_ext fun n => BialgHom.ext fun a => by
    change (incl G G).app n ((swap G).app n (inl _ _ a)) = algebraMap O _ (counit a)
    rw [inl_apply]
    change counit (R := O) a • (1 : G.A n) = _
    rw [Algebra.algebraMap_eq_smul_one]

def swapAction [Fact p.Prime] (G : PDivGroup p O) : Action (Polynomial ℤ_[p]) (prod G G) :=
  (Polynomial.aeval (swap G)).toRingHom

theorem swap_ne_scalar [Fact p.Prime] [Nontrivial O] (a : ℤ_[p]) :
    swapAction (const p O) Polynomial.X ≠ padicAction _ a := fun h => by
  have h0 : swap (const p O) = a • 𝟙 _ := by
    have : swapAction (const p O) Polynomial.X = swap (const p O) := Polynomial.aeval_X _
    rw [this] at h
    exact h.trans (Algebra.algebraMap_eq_smul_one a)
  have h1 := incl_swap_fst (const p O)
  rw [h0, Linear.smul_comp, Category.id_comp, Linear.comp_smul, incl_fst] at h1
  have ha : a = 0 := padicAction_const_injective (O := O)
    ((Algebra.algebraMap_eq_smul_one a).trans (h1.trans (map_zero _).symm))
  have h2 := swap_mul_swap (const p O)
  rw [h0, ha, zero_smul] at h2
  have h3 : 𝟙 (prod (const p O) (const p O)) = 0 := h2.symm.trans (mul_zero (M₀ := End _) _)
  have h4 : 𝟙 (const p O) = 0 := by
    rw [← incl_fst (const p O) (const p O), ← Category.id_comp (fst _ _), h3, Limits.zero_comp,
      Limits.comp_zero]
  exact one_ne_zero (padicAction_const_injective (p := p) (O := O)
    ((map_one _).trans (h4.trans (map_zero _).symm)))

example [Fact p.Prime] : (prod (mu p O) (const p O)).height = 2 := rfl

end GlobalTheory.PDivGroup.Test
