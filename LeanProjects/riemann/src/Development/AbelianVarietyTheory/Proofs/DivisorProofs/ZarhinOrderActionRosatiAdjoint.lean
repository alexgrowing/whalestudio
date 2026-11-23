import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOK
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeIdPowFiniteEtaleSurjective

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open GlobalTheory.CechPic GlobalTheory.AbDual

namespace GlobalTheory.ZarhinFam.AdjPf

section Alg

variable {U V C : Type*} [CommGroup U] [CommGroup V] [AddCommGroup C]

theorem add_prod {f : U → C} (hf : ∀ a a', f (a * a') = f a + f a') (g k : Fin 4 → U) (n m : Fin 4 → ℤ) :
    f (∏ j, (g j ^ n j * k j ^ m j)) = ∑ j, (n j • f (g j) + m j • f (k j)) := by
  let F : U →* Multiplicative C := MonoidHom.mk' (fun a => Multiplicative.ofAdd (f a)) fun a a' => by
    rw [hf, ofAdd_add]
  have e : ∀ a, f a = Multiplicative.toAdd (F a) := fun _ => rfl
  simp only [e, map_prod, map_mul, map_zpow, toAdd_prod, toAdd_mul, toAdd_zpow]

def zf (q : U → V → C) (l : U → V) (m : V → U) (x : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → U) (v : Fin 4 → V)
    (u' : Fin 4 → U) (v' : Fin 4 → V) : C :=
  (∑ i, q (u i) (l (u' i))) + (∑ i, ∑ j, x j i • q (u i) (v' j)) + (∑ i, ∑ j, x j i • q (u' i) (v j)) +
    ∑ j, q (m (v' j)) (v j)

theorem zf_symm {q : U → V → C} {l : U → V} {m : V → U} (hp : ∀ a a', q a (l a') = q a' (l a))
    (hm : ∀ b b', q (m b) b' = q (m b') b) (x : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → U) (v : Fin 4 → V)
    (u' : Fin 4 → U) (v' : Fin 4 → V) : zf q l m x u v u' v' = zf q l m x u' v' u v := by
  unfold zf
  rw [Finset.sum_congr rfl fun i _ => hp (u i) (u' i), Finset.sum_congr rfl fun i _ => hm (v' i) (v i)]
  abel

theorem zf_expand {q : U → V → C} {l : U → V} {m : V → U} {d : ℕ}
    (h₁ : ∀ a a' b, q (a * a') b = q a b + q a' b) (h₂ : ∀ a b b', q a (b * b') = q a b + q a b')
    (hp : ∀ a a', q a (l a') = q a' (l a)) (hm : ∀ b b', q (m b) b' = q (m b') b)
    (hd : ∀ a b, q (m b) (l a) = (d : ℤ) • q a b) (x a b c e : Matrix (Fin 4) (Fin 4) ℤ)
    (u : Fin 4 → U) (v : Fin 4 → V) (u' : Fin 4 → U) (v' : Fin 4 → V) :
    zf q l m x (fun i => ∏ j, (u j ^ a j i * m (v j) ^ b j i)) (fun i => ∏ j, (l (u j) ^ c j i * v j ^ e j i)) u' v' =
      ∑ j, ∑ k, ((a + c * x) j k • q (u j) (l (u' k)) + (a * x.transpose + (d : ℤ) • c) j k • q (u j) (v' k) +
        ((d : ℤ) • b + e * x) j k • q (u' k) (v j) + (b * x.transpose + e) j k • q (m (v j)) (v' k)) := by
  unfold zf
  simp only [fun b => add_prod (f := fun a => q a b) (fun a a' => h₁ a a' b), fun a => add_prod (f := q a) (h₂ a),
    hd, fun i j => hp (u' i) (u j), fun i j => hm (v' i) (v j)]
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul,
    Fin.sum_univ_four]
  module

theorem zf_adj {q : U → V → C} {l : U → V} {m : V → U} {d : ℕ}
    (h₁ : ∀ a a' b, q (a * a') b = q a b + q a' b) (h₂ : ∀ a b b', q a (b * b') = q a b + q a b')
    (hp : ∀ a a', q a (l a') = q a' (l a)) (hm : ∀ b b', q (m b) b' = q (m b') b)
    (hd : ∀ a b, q (m b) (l a) = (d : ℤ) • q a b) (x a b c e a' b' c' e' : Matrix (Fin 4) (Fin 4) ℤ)
    (e₁ : a' + c' * x = (a + c * x).transpose) (e₂ : a' * x.transpose + (d : ℤ) • c' = ((d : ℤ) • b + e * x).transpose)
    (e₃ : (d : ℤ) • b' + e' * x = (a * x.transpose + (d : ℤ) • c).transpose)
    (e₄ : b' * x.transpose + e' = (b * x.transpose + e).transpose)
    (u : Fin 4 → U) (v : Fin 4 → V) (u' : Fin 4 → U) (v' : Fin 4 → V) :
    zf q l m x (fun i => ∏ j, (u j ^ a j i * m (v j) ^ b j i)) (fun i => ∏ j, (l (u j) ^ c j i * v j ^ e j i)) u' v' =
      zf q l m x u v (fun i => ∏ j, (u' j ^ a' j i * m (v' j) ^ b' j i))
        (fun i => ∏ j, (l (u' j) ^ c' j i * v' j ^ e' j i)) := by
  rw [zf_symm hp hm x u v, zf_expand h₁ h₂ hp hm hd, zf_expand h₁ h₂ hp hm hd, e₁, e₂, e₃, e₄, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.transpose_apply]
  rw [hp (u' j) (u k), hm (v' j) (v k)]
  abel

end Alg

section Mat

open Matrix

def bA (N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) : Matrix (Fin 4) (Fin 4) ℤ := fun j i => N (.inl j) (.inl i)
def bB (d : ℕ) (N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  fun j i => N (.inr j) (.inl i) / (d : ℤ)
def bC (N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) : Matrix (Fin 4) (Fin 4) ℤ := fun j i => N (.inl j) (.inr i)
def bE (N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) : Matrix (Fin 4) (Fin 4) ℤ := fun j i => N (.inr j) (.inr i)

theorem mul_form_eq {d : ℕ} {N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ} (hN : N ∈ ord d) :
    N * form d = fromBlocks (bA N + bC N * quat d) (bA N * (quat d)ᵀ + (d : ℤ) • bC N)
      ((d : ℤ) • bB d N + bE N * quat d) ((d : ℤ) • (bB d N * (quat d)ᵀ + bE N)) := by
  have hb : (d : ℤ) • bB d N = N.toBlocks₂₁ := by
    ext j i
    simp [bB, toBlocks₂₁, Int.mul_ediv_cancel' (hN j i)]
  have e : N = fromBlocks (bA N) (bC N) ((d : ℤ) • bB d N) (bE N) := by
    rw [hb]; exact (fromBlocks_toBlocks N).symm
  conv_lhs => rw [e]
  rw [form, fromBlocks_multiply]
  congr 1
  · simp
  · simp only [Matrix.mul_smul, Matrix.mul_one]
  · simp [Matrix.smul_mul]
  · simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_add]

theorem blocks_bar {d : ℕ} (hd : 0 < d) (N : ord d) :
    bA (bar d N : Matrix _ _ ℤ) + bC (bar d N : Matrix _ _ ℤ) * quat d = (bA N + bC N * quat d)ᵀ ∧
    bA (bar d N : Matrix _ _ ℤ) * (quat d)ᵀ + (d : ℤ) • bC (bar d N : Matrix _ _ ℤ) =
      ((d : ℤ) • bB d N + bE N * quat d)ᵀ ∧
    (d : ℤ) • bB d (bar d N : Matrix _ _ ℤ) + bE (bar d N : Matrix _ _ ℤ) * quat d =
      (bA N * (quat d)ᵀ + (d : ℤ) • bC N)ᵀ ∧
    bB d (bar d N : Matrix _ _ ℤ) * (quat d)ᵀ + bE (bar d N : Matrix _ _ ℤ) = (bB d N * (quat d)ᵀ + bE N)ᵀ := by
  have key : (bar d N : Matrix _ _ ℤ) * form d = ((N : Matrix _ _ ℤ) * form d)ᵀ := by
    rw [bar_coe, Matrix.mul_assoc, formInv_mul_form hd, Matrix.mul_one, Matrix.transpose_mul, form_transpose]
  rw [mul_form_eq (bar d N).2, mul_form_eq N.2, fromBlocks_transpose, fromBlocks_inj] at key
  obtain ⟨k₁, k₂, k₃, k₄⟩ := key
  refine ⟨k₁, k₂, k₃, ?_⟩
  rw [Matrix.transpose_smul] at k₄
  exact smul_right_injective _ (by exact_mod_cast hd.ne') k₄

end Mat

section Geo

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

def pre {Y X : Over S} {G : Over S} [GrpObj G] (y : Y ⟶ X) : (X ⟶ G) →* (Y ⟶ G) :=
  MonoidHom.mk' (fun f => y ≫ f) fun f g => MonObj.comp_mul y f g

theorem comp_prod {Y X G : Over S} [GrpObj G] [IsCommMonObj G] (y : Y ⟶ X) (g : Fin 4 → (X ⟶ G))
    (k : Fin 4 → (X ⟶ G)) (n m : Fin 4 → ℤ) :
    y ≫ ∏ j, (g j ^ n j * k j ^ m j) = ∏ j, ((y ≫ g j) ^ n j * (y ≫ k j) ^ m j) := by
  have := map_prod (pre (G := G) y) (fun j => g j ^ n j * k j ^ m j) Finset.univ
  simp only [map_mul, map_zpow] at this
  exact this

theorem mkZ_pa {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (i : Fin 4) :
    mkZ A B u v ≫ pa A B i = u i := by
  rw [mkZ, pa, lift_fst_assoc]
  exact (Out.powIsLimit A 4).fac (Fan.mk T u) ⟨i⟩

theorem mkZ_pb {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (j : Fin 4) :
    mkZ A B u v ≫ pb A B j = v j := by
  rw [mkZ, pb, lift_snd_assoc]
  exact (Out.powIsLimit B 4).fac (Fan.mk T v) ⟨j⟩

theorem actZ_pa {Y : Over S} (w : Y ⟶ Zob A B) (d : ℕ) (la : A ⟶ B) (mu : B ⟶ A) (N : ord d) (i : Fin 4) :
    w ≫ actZ A B d la mu N ≫ pa A B i = ∏ j, ((w ≫ pa A B j) ^ bA (N : Matrix _ _ ℤ) j i *
      ((w ≫ pb A B j) ≫ mu) ^ bB d (N : Matrix _ _ ℤ) j i) := by
  rw [actZ, mkZ_pa, comp_prod]
  simp only [Category.assoc]
  rfl

theorem actZ_pb {Y : Over S} (w : Y ⟶ Zob A B) (d : ℕ) (la : A ⟶ B) (mu : B ⟶ A) (N : ord d) (i : Fin 4) :
    w ≫ actZ A B d la mu N ≫ pb A B i = ∏ j, (((w ≫ pa A B j) ≫ la) ^ bC (N : Matrix _ _ ℤ) j i *
      (w ≫ pb A B j) ^ bE (N : Matrix _ _ ℤ) j i) := by
  rw [actZ, mkZ_pb, comp_prod]
  simp only [Category.assoc]
  rfl

theorem zCls_eq {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A) :
    zCls A B hP hQ d mu =
      (∑ i, evc hP (fst (Zob A B) (Zob A B) ≫ pa A B i) (snd (Zob A B) (Zob A B) ≫ pa A B i)) +
      (∑ i, ∑ j, quat d j i • evc hQ (fst (Zob A B) (Zob A B) ≫ pa A B i) (snd (Zob A B) (Zob A B) ≫ pb A B j)) +
      (∑ i, ∑ j, quat d j i • evc hQ (snd (Zob A B) (Zob A B) ≫ pa A B i) (fst (Zob A B) (Zob A B) ≫ pb A B j)) +
      ∑ j, evc hQ (snd (Zob A B) (Zob A B) ≫ pb A B j ≫ mu) (fst (Zob A B) (Zob A B) ≫ pb A B j) := rfl

theorem pull_zCls {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (la : A ⟶ B)
    (mu : B ⟶ A) (hPQ : ∀ (Y : Over S) (a a' : Y ⟶ A), evc hP a a' = evc hQ a (a' ≫ la))
    {Y : Over S} (w w' : Y ⟶ Zob A B) :
    CechPic.pull (lift w w').left (zCls A B hP hQ d mu) =
      zf (fun a b => evc hQ a b) (fun a => a ≫ la) (fun b => b ≫ mu) (quat d) (fun i => w ≫ pa A B i)
        (fun j => w ≫ pb A B j) (fun i => w' ≫ pa A B i) (fun j => w' ≫ pb A B j) := by
  rw [zCls_eq]
  simp only [map_add, map_sum, map_zsmul, pull_evc, lift_fst_assoc, lift_snd_assoc, hPQ, zf, Category.assoc]

theorem comp_one_pow {Y : Over S} {G : Over S} [GrpObj G] (y : Y ⟶ G) (n : ℕ) : y ≫ (𝟙 G ^ n) = y ^ n := by
  have := map_pow (pre (G := G) y) (𝟙 G) n
  simp only [pre, MonoidHom.mk'_apply, Category.comp_id] at this
  exact this

end Geo

section Main

theorem adj_actZ : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S)
    [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A)
    (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d →
    IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d →
    Adj (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu) (GlobalTheory.ZarhinFam.bar d)
      (GlobalTheory.ZarhinFam.actZ c.A B d la mu) := by
  intro h M d S t c B _ _ Q la mu hZ _ _ _ hd _ hdu _
  obtain ⟨hB, hD1, hD2, hla, hmu, hlm, hml, hPiso⟩ := id hZ
  have hQ : Q.IsLB := hD1.isLB
  have hs : (swap Q).IsLB := hD2.isLB
  have h1 : ∀ (Y : Over S) (a a' : Y ⟶ c.A) (b : Y ⟶ B), evc hQ (a * a') b = evc hQ a b + evc hQ a' b :=
    fun Y a a' b => (isAdditive_iff hQ).1 hD1.additive Y a a' b
  have h2 : ∀ (Y : Over S) (a : Y ⟶ c.A) (b b' : Y ⟶ B), evc hQ a (b * b') = evc hQ a b + evc hQ a b' := by
    intro Y a b b'
    have e := (isAdditive_iff hs).1 hD2.additive Y b b' a
    rwa [evc_swap hQ hs, evc_swap hQ hs, evc_swap hQ hs] at e
  have hPQ : ∀ (Y : Over S) (a a' : Y ⟶ c.A), evc c.isLB a a' = evc hQ a (a' ≫ la) := by
    have e : cls c.P c.isLB = evc hQ (fst c.A c.A) (snd c.A c.A ≫ la) :=
      (cls_eq_iff c.isLB (pull_isLB hQ _)).2 hPiso
    intro Y a a'
    show CechPic.pull (lift a a').left (cls c.P c.isLB) = _
    rw [e, pull_evc, lift_fst, lift_snd_assoc]
  have hPs : ∀ (Y : Over S) (a a' : Y ⟶ c.A), evc c.isLB a a' = evc c.isLB a' a := by
    have e : cls c.P c.isLB = evc c.isLB (snd c.A c.A) (fst c.A c.A) :=
      (cls_eq_iff c.isLB (pull_isLB c.isLB _)).2 c.symm
    intro Y a a'
    show CechPic.pull (lift a a').left (cls c.P c.isLB) = _
    rw [e, pull_evc, lift_fst, lift_snd]
  have hp : ∀ (Y : Over S) (a a' : Y ⟶ c.A), evc hQ a (a' ≫ la) = evc hQ a' (a ≫ la) := by
    intro Y a a'
    rw [← hPQ, ← hPQ, hPs]
  have hpow : ∀ (Y : Over S) (a : Y ⟶ c.A) (b : Y ⟶ B) (n : ℕ), evc hQ a (b ^ n) = (n : ℤ) • evc hQ a b := by
    intro Y a b n
    induction n with
    | zero => rw [pow_zero, evc_one_right hQ hD1.zero a]; simp
    | succ n ih => rw [pow_succ, h2, ih]; push_cast; rw [add_smul, one_smul]
  have hpowL : ∀ (Y : Over S) (a : Y ⟶ c.A) (b : Y ⟶ B) (n : ℕ), evc hQ (a ^ n) b = (n : ℤ) • evc hQ a b := by
    intro Y a b n
    induction n with
    | zero => rw [pow_zero, hD1.additive.evc_one hQ b]; simp
    | succ n ih => rw [pow_succ, h1, ih]; push_cast; rw [add_smul, one_smul]
  have hdd : ∀ (Y : Over S) (a : Y ⟶ c.A) (b : Y ⟶ B), evc hQ (b ≫ mu) (a ≫ la) = (d : ℤ) • evc hQ a b := by
    intro Y a b
    rw [← hp _ a (b ≫ mu), Category.assoc, hml, comp_one_pow, hpow]

  have hmulmu : ∀ (Y : Over S) (b b' : Y ⟶ B), (b * b') ≫ mu = (b ≫ mu) * (b' ≫ mu) :=
    fun Y b b' => MonObj.mul_comp b b' mu
  have hmulla : ∀ (Y : Over S) (a a' : Y ⟶ c.A), (a * a') ≫ la = (a ≫ la) * (a' ≫ la) :=
    fun Y a a' => MonObj.mul_comp a a' la
  have hM1 : (ev Q (fst B B ≫ mu) (snd B B)).IsLB := pull_isLB hQ _
  have add1 : IsAdditive (ev Q (fst B B ≫ mu) (snd B B)) := by
    refine (isAdditive_iff hM1).2 fun Y b b' u => ?_
    simp only [evc_ev hQ, lift_fst_assoc, lift_snd, hmulmu, h1]
  obtain ⟨x1, hx1, -⟩ := hD2.univ B _ hM1 add1
  have hx1pt : ∀ (Y : Over S) (b u : Y ⟶ B), evc hQ (b ≫ mu) u = evc hQ (u ≫ x1) b := by
    have e := (cls_eq_iff hM1 (pull_isLB hs _)).2 hx1
    rw [cls_ev hQ, cls_ev hs] at e
    intro Y b u
    have e' := congrArg (CechPic.pull (lift b u).left) e
    rwa [pull_evc, pull_evc, lift_fst_assoc, lift_snd, lift_fst, lift_snd_assoc, evc_swap hQ hs] at e'
  have hM2 : (ev Q (fst B c.A ≫ mu) (snd B c.A ≫ la)).IsLB := pull_isLB hQ _
  have add2 : IsAdditive (ev Q (fst B c.A ≫ mu) (snd B c.A ≫ la)) := by
    refine (isAdditive_iff hM2).2 fun Y b b' u => ?_
    simp only [evc_ev hQ, lift_fst_assoc, lift_snd_assoc, hmulmu, h1]
  obtain ⟨y, -, huniq⟩ := hD2.univ c.A _ hM2 add2
  have hiso : ∀ z : c.A ⟶ c.A, (∀ (Y : Over S) (b : Y ⟶ B) (a : Y ⟶ c.A),
      evc hQ (b ≫ mu) (a ≫ la) = evc hQ (a ≫ z) b) →
      LBIso (ev Q (fst B c.A ≫ mu) (snd B c.A ≫ la)) (ev (swap Q) (fst B c.A) (snd B c.A ≫ z)) := by
    intro z hz
    refine (cls_eq_iff hM2 (pull_isLB hs _)).1 ?_
    rw [cls_ev hQ, cls_ev hs, evc_swap hQ hs, hz]
  have e1 : la ≫ x1 = y := huniq _ (hiso _ fun Y b a => by rw [hx1pt, Category.assoc])
  have e2 : la ≫ mu = y := huniq _ (hiso _ fun Y b a => by
    rw [hdd, hlm, comp_one_pow, hpowL])
  obtain ⟨-, -, het, hsurj⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective S B d hB hdu
  haveI : Flat (𝟙 B ^ d).left := inferInstance
  haveI : Epi (𝟙 B ^ d).left := Flat.epi_of_flat_of_surjective _
  haveI : Epi (𝟙 B ^ d) := (Over.forget S).epi_of_epi_map this
  haveI : Epi (mu ≫ la) := by rw [hml]; infer_instance
  haveI : Epi la := epi_of_epi mu la
  have hx : x1 = mu := (cancel_epi la).1 (e1.trans e2.symm)
  have hm : ∀ (Y : Over S) (b b' : Y ⟶ B), evc hQ (b ≫ mu) b' = evc hQ (b' ≫ mu) b := by
    intro Y b b'
    rw [hx1pt, hx]

  intro N
  have hz := zarhinBundle_isLineBundle c.A B c.isLB hQ d mu
  refine (cls_eq_iff (pull_isLB hz _) (pull_isLB hz _)).1 ?_
  rw [cls_pull hz, cls_pull hz, cls_zP, pull_zCls c.isLB hQ d la mu hPQ, pull_zCls c.isLB hQ d la mu hPQ]
  have ea : ∀ (N : ord d) (i : Fin 4), (fst (Zob c.A B) (Zob c.A B) ≫ actZ c.A B d la mu N) ≫ pa c.A B i = _ :=
    fun N i => (Category.assoc _ _ _).trans (actZ_pa _ d la mu N i)
  have eb : ∀ (N : ord d) (i : Fin 4), (fst (Zob c.A B) (Zob c.A B) ≫ actZ c.A B d la mu N) ≫ pb c.A B i = _ :=
    fun N i => (Category.assoc _ _ _).trans (actZ_pb _ d la mu N i)
  have ea' : ∀ (N : ord d) (i : Fin 4), (snd (Zob c.A B) (Zob c.A B) ≫ actZ c.A B d la mu N) ≫ pa c.A B i = _ :=
    fun N i => (Category.assoc _ _ _).trans (actZ_pa _ d la mu N i)
  have eb' : ∀ (N : ord d) (i : Fin 4), (snd (Zob c.A B) (Zob c.A B) ≫ actZ c.A B d la mu N) ≫ pb c.A B i = _ :=
    fun N i => (Category.assoc _ _ _).trans (actZ_pb _ d la mu N i)
  simp only [ea, eb, ea', eb']
  obtain ⟨k₁, k₂, k₃, k₄⟩ := blocks_bar hd N
  exact zf_adj (q := fun a b => evc hQ a b) (l := fun a => a ≫ la) (m := fun b => b ≫ mu) (d := d)
    (h1 _) (h2 _) (hp _) (hm _) (fun a b => hdd _ a b) _ _ _ _ _ _ _ _ _ k₁ k₂ k₃ k₄ _ _ _ _

end Main

end GlobalTheory.ZarhinFam.AdjPf
