import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsPullSnd

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

section GV

variable {X Y Y' : Scheme.{0}} (M : LB X)

def GV (F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U)
    (v : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z) (_ : (Z ⟶ X) → M.ι), (Z.presheaf.stalk z)ˣ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (u : LB.Gen (LB.LinComb M φ ε)), u.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = F U h) ∧
    ∀ Z r z J, Good M z J → val u r z J = v Z r z J

variable {M} {F F' : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} {v v'}

private lemma res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)ˣ) :
    res h₂ (res h₁ x) = res (h₂.trans h₁) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  first
    | (rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl)
    | (rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl)
    | simp [← Functor.map_comp_apply]
    | simp

private lemma isGen_mulGen_of_isGen {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (ht : t.IsGen) (ht' : t'.IsGen) :
    (LB.mulGen L φ ε φ' ε' t t').IsGen := by
  intro j j'
  have hl : ∀ i : K ⊕ K' → L.ι, LB.wchart L (Sum.elim φ φ') i ≤ LB.wchart L φ (i ∘ Sum.inl) :=
    fun i _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k)
  have hr : ∀ i : K ⊕ K' → L.ι, LB.wchart L (Sum.elim φ φ') i ≤ LB.wchart L φ' (i ∘ Sum.inr) :=
    fun i _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)
  have e1 := congrArg (res (inf_le_inf (hl j) (hl j'))) (ht (j ∘ Sum.inl) (j' ∘ Sum.inl))
  have e2 := congrArg (res (inf_le_inf (hr j) (hr j'))) (ht' (j ∘ Sum.inr) (j' ∘ Sum.inr))
  erw [map_mul, res_res_lemma, res_res_lemma] at e1
  erw [map_mul, res_res_lemma, res_res_lemma] at e2
  have hg : (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).g j j' =
      res (inf_le_inf (hl j) (hl j')) ((LB.LinComb L φ ε).g (j ∘ Sum.inl) (j' ∘ Sum.inl)) *
        res (inf_le_inf (hr j) (hr j')) ((LB.LinComb L φ' ε').g (j ∘ Sum.inr) (j' ∘ Sum.inr)) := by
    dsimp only [LB.LinComb]
    rw [Fintype.prod_sum_type]
    erw [map_prod, map_prod]
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) (Finset.prod_congr rfl fun k _ => ?_) <;>
      erw [map_zpow, res_res_lemma] <;> rfl
  dsimp only [LB.mulGen]
  erw [map_mul, map_mul, res_res_lemma, res_res_lemma, res_res_lemma, res_res_lemma, e1, e2, hg]
  exact mul_mul_mul_comm _ _ _ _

private lemma isGen_invGen_of_isGen {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    (LB.invGen L φ ε t).IsGen := by
  intro i i'
  have hg : (LB.LinComb L φ fun k => -ε k).g i i' = ((LB.LinComb L φ ε).g i i')⁻¹ := by
    dsimp only [LB.LinComb]
    simp only [zpow_neg, Finset.prod_inv_distrib] <;> rfl
  dsimp only [LB.invGen]
  erw [map_inv, map_inv, ht i i', mul_inv, hg]
  rfl

private lemma pullU_comp_toroidal_compactification {X Y Z : Scheme.{0}} (h : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) (x : Γ(X, U)ˣ) :
    pullU (h ≫ f) U x = pullU h (f ⁻¹ᵁ U) (pullU f U x) := by
  first
    | rfl
    | (ext; rfl)
    | (ext; simp [pullU])

private lemma pullU_res_toroidal_compactification {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (p : V ≤ U) (x : Γ(X, U)ˣ) :
    pullU f V (res p x) = res (fun _ hy => p hy : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) (pullU f U x) := by
  ext
  simp only [pullU, res, Units.coe_map, MonoidHom.coe_coe]
  first
    | exact congrArg (fun g => g.hom x.1) (f.naturality (homOfLE p).op)
    | exact (congrArg (fun g => g.hom x.1) (f.naturality (homOfLE p).op)).symm
    | (rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]; rfl)
    | simp [← CommRingCat.comp_apply, Scheme.Hom.naturality]

private lemma res_pullU_comp_eq_res_pullU_res_pullU {X Y Z : Scheme.{0}} (h : Z ⟶ Y) (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens}
    {W : Z.Opens} (p : V ≤ f ⁻¹ᵁ U) (hB : W ≤ h ⁻¹ᵁ V) (q : W ≤ (h ≫ f) ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res q (pullU (h ≫ f) U x) = res hB (pullU h V (res p (pullU f U x))) := by
  rw [pullU_res_toroidal_compactification]
  erw [res_res_lemma]
  first
    | done
    | rfl
    | (erw [pullU_comp_toroidal_compactification]; done)
    | (erw [pullU_comp_toroidal_compactification]; rfl)

set_option maxHeartbeats 800000 in

private lemma isGen_pullGen_of_isGen {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φ ε)) (hc : c.IsGen) (h : Z ⟶ Y) :
    (LB.pullGen L φ ε c h).IsGen := by
  intro j j'
  have hP : ∀ i : K → L.ι, LB.wchart L (fun k => h ≫ φ k) i ≤ h ⁻¹ᵁ LB.wchart L φ i :=
    fun i _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have hB : LB.wchart L (fun k => h ≫ φ k) j ⊓ LB.wchart L (fun k => h ≫ φ k) j' ≤
      h ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j') := by
    first
      | exact fun x hy => ⟨hP j hy.1, hP j' hy.2⟩
      | exact fun x hy => ⟨hP j (Opens.mem_inf.1 hy).1, hP j' (Opens.mem_inf.1 hy).2⟩
      | exact fun x hy => by simp only [Opens.mem_inf] at hy ⊢; exact ⟨hP j hy.1, hP j' hy.2⟩
  have e := congrArg (fun x => res hB (pullU h (LB.wchart L φ j ⊓ LB.wchart L φ j') x)) (hc j j')
  try dsimp only at e
  erw [map_mul, map_mul, pullU_res_toroidal_compactification, pullU_res_toroidal_compactification, res_res_lemma, res_res_lemma] at e
  have hg : (LB.LinComb L (fun k => h ≫ φ k) ε).g j j' =
      res hB (pullU h (LB.wchart L φ j ⊓ LB.wchart L φ j') ((LB.LinComb L φ ε).g j j')) := by
    dsimp only [LB.LinComb]
    erw [map_prod, map_prod]
    congr 1
    funext k
    erw [map_zpow, map_zpow]
    congr 1
    exact res_pullU_comp_eq_res_pullU_res_pullU (U := L.U (j k) ⊓ L.U (j' k)) h (φ k) _ hB _ (L.g (j k) (j' k))
  dsimp only [LB.pullGen]
  erw [res_res_lemma, res_res_lemma, e, hg]
  rfl

theorem GV.mul (a : GV M F v) (b : GV M F' v') :
    GV M (fun U _ h => F U h * F' U h) fun Z r z J => v Z r z J * v' Z r z J := by
  obtain ⟨K, hK, φ, ε, u, hu, hF, hv⟩ := a
  obtain ⟨K', hK', φ', ε', u', hu', hF', hv'⟩ := b
  refine ⟨K ⊕ K', inferInstance, Sum.elim φ φ', Sum.elim ε ε', LB.mulGen (L := M) φ ε φ' ε' u u',
    isGen_mulGen_of_isGen M φ ε φ' ε' u u' hu hu', ?_, ?_⟩
  · intro U _ h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, hF, hF']
  · intro Z r z J hJ
    rw [val_mul, hv Z r z J hJ, hv' Z r z J hJ]
    all_goals first | assumption | exact hJ

theorem GV.inv (a : GV M F v) : GV M (fun U _ h => (F U h)⁻¹) fun Z r z J => (v Z r z J)⁻¹ := by
  obtain ⟨K, hK, φ, ε, u, hu, hF, hv⟩ := a
  refine ⟨K, hK, φ, fun k => -ε k, LB.invGen (L := M) φ ε u, isGen_invGen_of_isGen M φ ε u hu, ?_, ?_⟩
  · intro U _ h
    simp only [zpow_neg, Finset.prod_inv_distrib, hF]
  · intro Z r z J hJ
    rw [val_inv, hv Z r z J hJ]
    all_goals first | assumption | exact hJ

theorem GV.pull (a : GV M F v) (g : Y' ⟶ Y) : GV M (fun U _ h => F U fun q => h (g ≫ q)) fun Z r z J => v Z (r ≫ g) z J := by
  obtain ⟨K, hK, φ, ε, u, hu, hF, hv⟩ := a
  refine ⟨K, hK, fun k => g ≫ φ k, ε, LB.pullGen (L := M) φ ε u g, isGen_pullGen_of_isGen M φ ε u hu g, ?_, ?_⟩
  · intro U _ h
    exact hF U fun q => h (g ≫ q)
  · intro Z r z J hJ
    rw [val_pull]
    · exact hv Z (r ≫ g) z J hJ
    all_goals first | assumption | exact hJ

theorem GV.pow (a : GV M F v) (n : ℕ) : GV M (fun U _ h => F U h ^ n) fun Z r z J => v Z r z J ^ n := by
  have key : ∀ {G G' : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U}
      {w w' : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z) (_ : (Z ⟶ X) → M.ι), (Z.presheaf.stalk z)ˣ},
      GV M G w → G = G' → w = w' → GV M G' w' := by
    intro G G' w w' h hG hw
    subst hG
    subst hw
    exact h
  induction n with
  | zero =>
    refine key (a.mul a.inv) ?_ ?_
    · funext U inst h
      exact (mul_inv_cancel _).trans (pow_zero _).symm
    · funext Z r z J
      exact (mul_inv_cancel _).trans (pow_zero _).symm
  | succ n ih =>
    refine key (ih.mul a) ?_ ?_
    · funext U inst h
      exact (pow_succ _ _).symm
    · funext Z r z J
      exact (pow_succ _ _).symm

end GV

theorem Th.sym_half {A U : Type} [CommGroup A] [CommGroup U] {ν f : A → U} {Y : A} {N : ℕ} (nn : ∀ u, ν u * ν u⁻¹ = ν 1 * ν 1)
    (cm : Commute (⟨Y, f⟩ : Th A U) ⟨Y, fun u => ν u * (ν (u * Y))⁻¹ * (f (u * Y)⁻¹)⁻¹⟩) (Yn : Y ^ N = 1)
    (cs : ∀ u, ((⟨Y, f⟩ : Th A U) ^ N).f u = ((⟨Y, f⟩ : Th A U) ^ N).f 1) :
    ((⟨Y, f⟩ : Th A U) * ⟨Y, fun u => ν u * (ν (u * Y))⁻¹ * (f (u * Y)⁻¹)⁻¹⟩).Sym ν N := by
  refine ⟨?_, fun u => ?_⟩
  · rw [cm.mul_pow]
    refine Th.ext ((congrArg₂ (· * ·) ((Th.theta_pow_x _ _).trans Yn) ((Th.theta_pow_x _ _).trans Yn)).trans (_root_.mul_one _))
      (funext fun u => ?_)
    rw [Th.mul_f, Th.theta_pow_x, Yn, _root_.mul_one, cs u, ← cs u⁻¹, Th.pow_f, Th.pow_f, ← Finset.prod_range_reflect]
    have tel : ∏ j ∈ Finset.range N, (ν (u * Y ^ j) * (ν (u * Y ^ j * Y))⁻¹) = 1 := by
      simp only [_root_.mul_assoc u, ← pow_succ, ← div_eq_mul_inv]
      rw [Finset.prod_range_div' (fun j => ν (u * Y ^ j)), Yn, pow_zero, div_self']
    show _ * ∏ j ∈ Finset.range N, (ν (u * Y ^ j) * (ν (u * Y ^ j * Y))⁻¹ * (f (u * Y ^ j * Y)⁻¹)⁻¹) = 1
    rw [Finset.prod_mul_distrib, tel, _root_.one_mul, Finset.prod_inv_distrib, mul_inv_eq_one]
    refine Finset.prod_congr rfl fun j hj => congrArg f ?_
    show u⁻¹ * Y ^ (N - 1 - j) = _
    rw [_root_.mul_assoc, ← pow_succ, mul_inv, _root_.mul_right_inj, eq_inv_iff_mul_eq_one, ← pow_add,
      show N - 1 - j + (j + 1) = N by have := Finset.mem_range.1 hj; omega, Yn]
  · have a₁ := congrArg Additive.ofMul (nn (u * Y⁻¹))
    have a₂ := congrArg Additive.ofMul (nn (u * (Y * Y)⁻¹))
    have e₁ : u * (Y * Y)⁻¹ * Y = u * Y⁻¹ := by rw [mul_inv, ← _root_.mul_assoc, inv_mul_cancel_right]
    have e₂ : u⁻¹ * Y = (u * Y⁻¹)⁻¹ := by rw [mul_inv, inv_inv]
    have e₃ : (u * Y⁻¹)⁻¹ * Y = (u * (Y * Y)⁻¹)⁻¹ := by rw [mul_inv, inv_inv, mul_inv, inv_inv, _root_.mul_assoc]
    simp only [Th.mul_f, Th.adapted_frame_mul_vecMulVec, e₁, e₂, e₃, inv_mul_cancel_right, inv_inv]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv] at a₁ a₂ ⊢
    linear_combination (norm := abel) a₁ - a₂

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L) (hG : GlobalFnsSt)
  (hA : IsAbelianScheme A)
include c hG hA

theorem exists_symLift_core (hs : L.IsSymmetric) {T : Over S} (x : T ⟶ A) {k n : ℕ} {k' : ℤ} (hk : k' = k) (hn : Odd n)
    (hxk : x ^ k = 1) (hxn : x ^ n = 1) (hloc : ∀ y : T ⟶ A, y ^ k = 1 → GenOf L.L fun _ _ h => h y.left ^ k) :
    ∃ W : ThetaGrp A L.L k' T, SymLift A L.L k' n x W := by
  subst hk
  obtain ⟨m, rfl⟩ := hn
  let y := x ^ (m + 1)
  have yy : y * y = x := by rw [← pow_add, show m + 1 + (m + 1) = 2 * m + 1 + 1 by ring, pow_succ, hxn, _root_.one_mul]
  have yk : y ^ k = 1 := by rw [← pow_mul, mul_comm, pow_mul, hxk, one_pow]
  have yn : y ^ (2 * m + 1) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hxn, one_pow]
  obtain ⟨ψ, hψ⟩ := (((genOf_cubN c (fst T A ≫ y) (snd T A) k).mul ((hloc y yk).pull (fst T A).left).inv).mul
    ((genOf_rig (T ⊗ A)).pow k)).gen L.isLB (φ := ![(snd T A).left, (translPt A y).left]) (ε := ![(k : ℤ), -k]) fun U _ h => by
      rw [← MonObj.comp_pow, yk, MonObj.comp_one, _root_.one_mul, Fin.prod_univ_two]
      show h _ ^ (k : ℤ) * h ((fst T A ≫ y) * snd T A).left ^ (-(k : ℤ)) = _ * (h (fst T A ≫ y).left ^ k)⁻¹ * _
      apply Additive.ofMul.injective
      simp only [Matrix.cons_val_zero, ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
      module
  obtain ⟨P, hP⟩ := (genOf_sym hs (𝟙 A)).inv.gen L.isLB (φ := ![𝟙 A.left, (𝟙 A : A ⟶ A)⁻¹.left]) (ε := ![1, -1]) fun U _ h => by
    rw [Fin.prod_univ_two, mul_inv_rev, inv_inv]; exact congrArg₂ (· * ·) (zpow_one _) (zpow_neg_one _)
  have pν : ∀ {T : Over S} (w : T ⟶ A) (V : Type) [CommGroup V] (h : (T.left ⟶ A.left) → V),
      ∏ i, h (w.left ≫ ![𝟙 A.left, (𝟙 A : A ⟶ A)⁻¹.left] i) ^ (![1, -1] : Fin 2 → ℤ) i = h w.left * (h w⁻¹.left)⁻¹ := fun w V _ h => by
    rw [Fin.prod_univ_two]
    exact congrArg₂ (· * ·) ((zpow_one _).trans (congrArg h (Category.comp_id _))) ((zpow_neg_one _).trans (congrArg (fun q => (h q)⁻¹)
      (by show (w ≫ (𝟙 A)⁻¹).left = _; rw [GrpObj.comp_inv, Category.comp_id])))
  have pθ : ∀ (a : T ⟶ A) (w : T ⊗ A ⟶ A) (V : Type) [CommGroup V] (h : ((T ⊗ A).left ⟶ A.left) → V),
      ∏ i, h ((lift (fst T A) w).left ≫ ![(snd T A).left, (translPt A a).left] i) ^ (![(k : ℤ), -k] : Fin 2 → ℤ) i =
        h w.left ^ k * (h (w * (fst T A ≫ a)).left ^ k)⁻¹ := fun a w V _ h => by
    rw [Fin.prod_univ_two]
    show h (lift (fst T A) w ≫ snd T A).left ^ (k : ℤ) * h (lift (fst T A) w ≫ ((fst T A ≫ a) * snd T A)).left ^ (-(k : ℤ)) = _
    rw [MonObj.comp_mul, lift_snd, lift_fst_assoc, mul_comm (fst T A ≫ a), zpow_neg, zpow_natCast, zpow_natCast]
  have gψ : ∀ w : T ⊗ A ⟶ A, GV L.L (fun _ _ h => h w.left ^ k * (h (w * (fst T A ≫ y)).left ^ k)⁻¹)
      fun Z r z J => val ψ (r ≫ (lift (fst T A) w).left) z J := fun w =>
    ⟨Fin 2, inferInstance, _, _, _, pullGen_isGen _ _ _ _ hψ (lift (fst T A) w).left, pθ y w, fun _ _ _ _ hJ => val_pull hJ _ _ _⟩
  have gν : ∀ w : T ⊗ A ⟶ A, GV L.L (fun _ _ h => h w.left * (h w⁻¹.left)⁻¹) fun Z r z J => val P (r ≫ w.left) z J := fun w =>
    ⟨Fin 2, inferInstance, _, _, _, pullGen_isGen _ _ _ _ hP w.left, pν w, fun _ _ _ _ hJ => val_pull hJ _ _ _⟩
  let s := snd T A
  let Y := fst T A ≫ y
  have iY : ∀ u : T ⊗ A ⟶ A, (u * (fst T A ≫ y))⁻¹ * (fst T A ≫ y) = u⁻¹ := fun u => by rw [mul_inv, inv_mul_cancel_right]
  obtain ⟨K₂, _, φ₂, ε₂, t₂, ht₂, p₂, v₂⟩ := (((gν s).pow k).mul ((gν (s * Y)).pow k).inv).mul (gψ (s * Y)⁻¹).inv
  obtain ⟨K₃, _, φ₃, ε₃, t₃, ht₃, p₃, v₃⟩ := (gψ s).mul ((((gν (s * Y)).pow k).mul ((gν (s * Y * Y)).pow k).inv).mul
    (gψ (s * Y * Y)⁻¹).inv)
  have YY : Y * Y = fst T A ≫ x := by rw [← MonObj.comp_mul, yy]
  obtain ⟨φ, hφ, vφ⟩ := exists_gen L.isLB (φ' := ![(snd T A).left, (translPt A x).left]) (ε' := ![(k : ℤ), -k]) (fun U _ h => by
    have e := pθ x s U h
    rw [lift_fst_snd] at e
    simp only [Over.id_left, Category.id_comp] at e
    rw [p₃, e]
    simp only [Y] at YY
    simp only [s, Y, iY]
    rw [← YY, ← _root_.mul_assoc (snd T A)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    module) t₃ ht₃
  obtain ⟨K₄, _, φ₄, ε₄, t₄, ht₄, p₄, v₄⟩ := (gν s).pow k
  obtain ⟨nu, hnu', vnu⟩ := exists_gen L.isLB (φ' := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left])
    (ε' := ![(k : ℤ), -k]) (fun U _ h => by
      rw [p₄, Fin.prod_univ_two]
      show (h s.left * (h s⁻¹.left)⁻¹) ^ k = h s.left ^ (k : ℤ) * h s⁻¹.left ^ (-(k : ℤ))
      rw [mul_pow, inv_pow, zpow_neg, zpow_natCast, zpow_natCast]) t₄ ht₄
  have l : ∀ u a : T ⊗ A ⟶ A, (lift (fst T A) u).left ≫ (lift (fst T A) a).left = (lift (fst T A) (lift (fst T A) u ≫ a)).left :=
    fun u a => by rw [← Over.comp_left, comp_lift, lift_fst]
  have core : ∀ (w : (T ⊗ A).left) I, Good L.L w I → (⟨fst T A ≫ x, fun u => val φ (lift (fst T A) u).left w I⟩ : Th _ _).Sym
      (fun u => val P u.left w I ^ k) (2 * m + 1) := fun w I hI => by
    let ν := fun u : T ⊗ A ⟶ A => val P u.left w I ^ k
    let f := fun u : T ⊗ A ⟶ A => val ψ (lift (fst T A) u).left w I
    have G₁ : IsGeo (fst T A) w I k y ⟨Y, f⟩ := ⟨rfl, Fin 2, inferInstance, _, _, ψ, hψ, fun V _ h => by
      rw [Fin.prod_univ_two]; exact congrArg₂ (· * ·) (zpow_natCast _ _) ((zpow_neg _ _).trans (congrArg _ (zpow_natCast _ _))),
      fun _ => rfl⟩
    have G₂ : IsGeo (fst T A) w I k y ⟨Y, fun u => ν u * (ν (u * Y))⁻¹ * (f (u * Y)⁻¹)⁻¹⟩ :=
      ⟨rfl, K₂, inferInstance, φ₂, ε₂, t₂, ht₂, fun V _ h => by
        rw [p₂]
        simp only [s, Y, iY]
        rw [mul_comm (fst T A ≫ y)]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_pow]
        module, fun u => by
        rw [v₂ _ _ w I hI]
        simp only [l]
        simp only [s, Y, ← Over.comp_left, MonObj.comp_mul, GrpObj.comp_inv, lift_snd, lift_fst_assoc]; rfl⟩
    have Yk : Y ^ k = 1 := by rw [← MonObj.comp_pow, yk, MonObj.comp_one]
    have Yn : Y ^ (2 * m + 1) = 1 := by rw [← MonObj.comp_pow, yn, MonObj.comp_one]
    have Gp : ∀ j, IsGeo (fst T A) w I k (y ^ (j + 1)) ((⟨Y, f⟩ : Th _ _) ^ (j + 1)) := fun j => by
      induction j with
      | zero => simpa only [zero_add, pow_one] using G₁
      | succ j ih => rw [pow_succ, pow_succ (⟨Y, f⟩ : Th _ _)]; exact ih.mul hI G₁
    have := Th.sym_half (ν := ν) (fun u => by
        have r := ratio_const hG hA L.isLB (T := T) (fun V _ h => (Fintype.prod_empty _).trans (Eq.symm ((prod_sum₂ (K := Fin 2)
          (K' := Fin 2) (U := V) _ (pν s V h) (pν s⁻¹ V h)).trans (by rw [inv_inv]; simp))))
          (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hP s.left) (pullGen_isGen _ _ _ _ hP s⁻¹.left)) (u' := LB.oneGen L.L)
          (fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
          (fst T A) u hI
        simp only [val_mul hI, val_pull hI, val_one, s, ← Over.comp_left, GrpObj.comp_inv, lift_snd, inv_one, _root_.mul_one,
          _root_.one_mul] at r
        simp only [ν, ← mul_pow, r])
      (Th.commute_of (isCub_cubV c hI) Yk Yk (G₁.cub hI c hG hA yk) (G₂.cub hI c hG hA yk) rfl) Yn fun u => by
        rw [(Gp (2 * m)).cub hI c hG hA (by rw [yn, one_pow]) u, Th.theta_pow_x, Yn]
        exact mul_eq_left.2 (Finset.prod_eq_one fun i _ => by rw [(isCub_cubV c hI).s01, (isCub_cubV c hI).face])
    refine (congrArg (Th.Sym ν _) (Th.ext (by exact YY) (funext fun u => Eq.symm ?_))).mp this
    show val φ (lift (fst T A) u).left w I = _
    rw [vφ _ _ w I hI, v₃ _ _ w I hI]
    simp only [l]
    simp only [s, Y, ← Over.comp_left, MonObj.comp_mul, GrpObj.comp_inv, lift_snd, lift_fst_assoc]; rfl
  refine ⟨⟨x, φ, hφ⟩, rfl, corr_of_val L.isLB fun w I hI => ?_, nu, hnu', corr_of_val L.isLB fun w I hI => ?_⟩
  · have hz := hI.mem (powφ A x (2 * m + 1)) (𝟙 _)
    have := congrArg (fun g => g.f (snd T A)) (core w I hI).pow
    simp only [Th.pow_f] at this
    rw [← Fin.prod_univ_eq_prod_range (fun j => val φ (lift (fst T A) (snd T A * (fst T A ≫ x) ^ j)).left w I)] at this
    have t : ∀ j : ℕ, 𝟙 _ ≫ (translT A (x ^ j)).left = (lift (fst T A) (snd T A * (fst T A ≫ x) ^ j)).left := fun j => by
      rw [Category.id_comp, translT, translPt, MonObj.comp_pow, mul_comm]; rfl
    refine Eq.trans ?_ (this.trans (val_one (L := L.L) (z := w) (J := I) (𝟙 (T ⊗ A).left)).symm)
    refine Eq.symm (Eq.trans (Finset.prod_congr rfl fun j _ => ?_) (map_prod _ _ _).symm)
    exact Eq.symm (((gm_res _ w _ hz _).trans (val_pull hI φ (translT A (x ^ (j : ℕ))).left (𝟙 _))).trans
      (congrArg (val φ · w I) (t j)))
  · have := (core w I hI).sym (snd T A)
    have vν : ∀ u : T ⊗ A ⟶ A, val nu (lift (fst T A) u).left w I = val P u.left w I ^ k := fun u => by
      rw [vnu _ _ w I hI, v₄ _ _ w I hI]
      simp only [s, ← Over.comp_left, lift_snd]
    have id : (𝟙 (T ⊗ A).left) = (lift (fst T A) (snd T A)).left := by rw [lift_fst_snd]; rfl
    have tr : 𝟙 _ ≫ (translT A x⁻¹).left = (lift (fst T A) (snd T A * (fst T A ≫ x)⁻¹)).left := by
      rw [Category.id_comp, translT, translPt, GrpObj.comp_inv, mul_comm]; rfl
    refine (val_mul hI _ _ _).trans (((congrArg₂ (· * ·) ((val_mul hI _ _ _).trans (congrArg₂ (· * ·) ((val_pull hI _ _ _).trans
      (congrArg (val φ · w I) tr)) ((congrArg (val nu · w I) id).trans (vν _)))) ((val_mul hI _ _ _).trans
      (congrArg₂ (· * ·) ((val_pull hI _ _ _).trans (congrArg (val φ · w I) (Category.id_comp _))) ((val_inv _ _).trans
      (congrArg (·⁻¹) ((val_pull hI _ _ _).trans ((congrArg (val nu · w I) tr).trans (vν _)))))))).trans
      (_root_.mul_assoc _ _ _).symm).trans ((mul_inv_eq_one.2 this).trans (val_one _).symm))

theorem exists_symLift_odd (hs : L.IsSymmetric) {T : Over S} (x : T ⟶ A) {k n : ℕ} {k' : ℤ} (hk : k' = k) (hko : Odd k) (hn : Odd n)
    (hxk : x ^ k = 1) (hxn : x ^ n = 1) : ∃ W : ThetaGrp A L.L k' T, SymLift A L.L k' n x W :=
  exists_symLift_core c hG hA hs x hk hn hxk hxn fun y yk => by
    obtain ⟨j, rfl⟩ := hko
    refine (((genOf_pow c hs y (2 * j + 1)).mul (((genOf_cubN c y y (2 * j + 1)).mul ((genOf_pow c hs y 2).pow (2 * j + 1)).inv).pow j)).mul
      ((genOf_rig T).pow (1 + j * (2 * j + 1)))).congr fun U _ h => ?_
    rw [yk, _root_.one_mul y, pow_two y]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    module

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
