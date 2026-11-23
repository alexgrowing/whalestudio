import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KerPow

section General

variable {X Y Y' B B' : Scheme.{0}} {L : LB X} {K K' K'' : Type} [Fintype K] [Fintype K'] [Fintype K'']

theorem gen_transfer {M M' : LB Y} (e : M'.ι → M.ι) (hU : ∀ j, M'.U j ≤ M.U (e j))
    (hg : ∀ i j (y : Y), y ∈ M'.U i → y ∈ M'.U j →
      gm (𝟙 Y) y (M'.U i ⊓ M'.U j) (M'.g i j) = gm (𝟙 Y) y (M.U (e i) ⊓ M.U (e j)) (M.g (e i) (e j)))
    (h : ∃ t : LB.Gen M, t.IsGen) : ∃ t' : LB.Gen M', t'.IsGen := by
  obtain ⟨t, ht⟩ := h
  refine ⟨⟨fun j => res (hU j) (t.s (e j))⟩, fun i j => unit_ext fun y hy => ?_⟩
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ M.U (e i) ⊓ M.U (e j) := ⟨hU i hy.1, hU j hy.2⟩
  have h1 := congrArg (gm (𝟙 Y) y (M.U (e i) ⊓ M.U (e j))) (ht (e i) (e j))
  rw [map_mul, gm_res _ y _ hm, gm_res _ y _ hm] at h1
  rw [map_mul, gm_res _ y inf_le_left hy, gm_res _ y inf_le_right hy, hg i j y hy.1 hy.2]
  exact (gm_res (𝟙 Y) y (hU i) (show y ∈ M'.U i from hy.1) _).trans
    (h1.trans (congrArg _ (gm_res (𝟙 Y) y (hU j) (show y ∈ M'.U j from hy.2) _).symm))

def HasGen (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Prop :=
  ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen

theorem pull_iff (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) :
    (∃ c : LB.Gen ((LB.LinComb L φ ε).pull h), c.IsGen) ↔ HasGen L (fun k => h ≫ φ k) ε := by
  have key : ∀ (y : Y') (i j : K → L.ι), h y ∈ LB.wchart L φ i → h y ∈ LB.wchart L φ j →
      gm (𝟙 Y') y (LB.wchart L (fun k => h ≫ φ k) i ⊓ LB.wchart L (fun k => h ≫ φ k) j)
        ((LB.LinComb L (fun k => h ≫ φ k) ε).g i j) =
      gm (𝟙 Y') y (((LB.LinComb L φ ε).pull h).U (fun _ => i) ⊓ ((LB.LinComb L φ ε).pull h).U (fun _ => j))
        (((LB.LinComb L φ ε).pull h).g (fun _ => i) (fun _ => j)) := by
    intro y i j hi hj
    refine (gm_linComb L (fun k => h ≫ φ k) ε (𝟙 Y') y i j
      (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hi k) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hj k)).trans ?_
    refine Eq.trans ?_ (gm_pull_g (LB.LinComb L φ ε) h (𝟙 Y') y (fun _ => i) (fun _ => j)
      (mem_pull.2 hi) (mem_pull.2 hj)).symm
    refine Eq.trans ?_ (gm_linComb L φ ε (𝟙 Y' ≫ h) y i j hi hj).symm
    simp only [Category.assoc]
  constructor
  · refine gen_transfer (M := (LB.LinComb L φ ε).pull h) (M' := LB.LinComb L (fun k => h ≫ φ k) ε)
      (fun j _ => j) (fun j y hy => mem_pull.2 (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)) ?_
    intro i j y hi hj
    exact key y i j (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hi k) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hj k)
  · refine gen_transfer (M' := (LB.LinComb L φ ε).pull h) (M := LB.LinComb L (fun k => h ≫ φ k) ε)
      (fun J => J PUnit.unit) (fun J y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (mem_pull.1 hy) k) ?_
    intro i j y hi hj
    exact (key y (i PUnit.unit) (j PUnit.unit) (mem_pull.1 hi) (mem_pull.1 hj)).symm

theorem HasGen.pull {φ : K → (Y ⟶ X)} {ε : K → ℤ} (H : HasGen L φ ε) (h : Y' ⟶ Y) {φ' : K → (Y' ⟶ X)}
    (e : ∀ k, h ≫ φ k = φ' k) : HasGen L φ' ε := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  obtain ⟨t, ht⟩ := H
  exact ⟨_, DVR.pullGen_isGen L φ ε t ht h⟩

theorem HasGen.comb (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {φ'' : K'' → (Y ⟶ X)} {ε'' : K'' → ℤ} (H : HasGen L φ ε) (H' : HasGen L φ' ε')
    (e : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U),
      (∏ k, h (φ k) ^ ε k) * (∏ k, h (φ' k) ^ ε' k)⁻¹ = ∏ k, h (φ'' k) ^ ε'' k) : HasGen L φ'' ε'' := by
  obtain ⟨t, ht⟩ := H
  obtain ⟨t', ht'⟩ := H'
  obtain ⟨u, hu, -⟩ := exists_gen hL (φ' := φ'') (ε' := ε'') (fun U _ h => by
      rw [← e U h, Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib])
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ t'))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ ht'))
  exact ⟨u, hu⟩

theorem hasGen_of_trivial (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (e : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = 1) : HasGen L φ ε := by
  obtain ⟨u, hu, -⟩ := exists_gen hL (φ' := φ) (ε' := ε) (fun U _ h => by rw [e U h]; simp)
    (LB.oneGen L (Y := Y)) (fun i j => by
      have e1 : (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim).g i j = 1 :=
        rfl
      rw [e1, _root_.one_mul]
      exact (map_one _).trans (map_one _).symm)
  exact ⟨u, hu⟩

def LocGen (L : LB X) (π : Y ⟶ B) (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Prop :=
  ∀ p : B, ∃ V : B.Opens, p ∈ V ∧ HasGen L (fun k => (π ⁻¹ᵁ V).ι ≫ φ k) ε

theorem locGen_iff (π : Y ⟶ B) (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    (∀ p : B, ∃ V : B.Opens, p ∈ V ∧ ∃ c : LB.Gen ((LB.LinComb L φ ε).pull (π ⁻¹ᵁ V).ι), c.IsGen) ↔
      LocGen L π φ ε := by
  simp only [LocGen, pull_iff]

theorem LocGen.comb (hL : L.IsLB) {π : Y ⟶ B} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {φ'' : K'' → (Y ⟶ X)} {ε'' : K'' → ℤ} (H : LocGen L π φ ε) (H' : LocGen L π φ' ε')
    (e : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U),
      (∏ k, h (φ k) ^ ε k) * (∏ k, h (φ' k) ^ ε' k)⁻¹ = ∏ k, h (φ'' k) ^ ε'' k) : LocGen L π φ'' ε'' := by
  intro p
  obtain ⟨V, hV, t⟩ := H p
  obtain ⟨V', hV', t'⟩ := H' p
  refine ⟨V ⊓ V', ⟨hV, hV'⟩, ?_⟩
  have a := t.pull (Y.homOfLE (show π ⁻¹ᵁ (V ⊓ V') ≤ π ⁻¹ᵁ V from fun _ h => h.1))
    (φ' := fun k => (π ⁻¹ᵁ (V ⊓ V')).ι ≫ φ k) (fun k => by rw [← Category.assoc, Scheme.homOfLE_ι])
  have a' := t'.pull (Y.homOfLE (show π ⁻¹ᵁ (V ⊓ V') ≤ π ⁻¹ᵁ V' from fun _ h => h.2))
    (φ' := fun k => (π ⁻¹ᵁ (V ⊓ V')).ι ≫ φ' k) (fun k => by rw [← Category.assoc, Scheme.homOfLE_ι])
  exact a.comb hL a' fun U _ h => e U fun q => h ((π ⁻¹ᵁ (V ⊓ V')).ι ≫ q)

theorem locGen_of_trivial (hL : L.IsLB) {π : Y ⟶ B} {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (e : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = 1) : LocGen L π φ ε :=
  fun _ => ⟨⊤, trivial, hasGen_of_trivial hL fun U _ h => e U fun q => h ((π ⁻¹ᵁ ⊤).ι ≫ q)⟩

theorem HasGen.of_range {φ : K → (Y ⟶ X)} {ε : K → ℤ} {W : Y.Opens} (H : HasGen L (fun k => W.ι ≫ φ k) ε)
    (h : Y' ⟶ Y) (hW : ∀ y, h y ∈ W) {φ' : K → (Y' ⟶ X)} (e : ∀ k, h ≫ φ k = φ' k) : HasGen L φ' ε :=
  H.pull (IsOpenImmersion.lift W.ι h (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hW y))
    (fun k => (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ k) (IsOpenImmersion.lift_fac _ _ _)).trans (e k)))

theorem LocGen.baseChange {π : Y ⟶ B} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (H : LocGen L π φ ε) {π' : Y' ⟶ B'}
    (h : Y' ⟶ Y) (g : B' ⟶ B) (sq : h ≫ π = π' ≫ g) {φ' : K → (Y' ⟶ X)} (e : ∀ k, h ≫ φ k = φ' k) :
    LocGen L π' φ' ε := by
  intro p
  obtain ⟨V, hV, t⟩ := H (g p)
  refine ⟨g ⁻¹ᵁ V, hV, t.of_range ((π' ⁻¹ᵁ (g ⁻¹ᵁ V)).ι ≫ h) (fun y => ?_) (fun k => by rw [Category.assoc, e])⟩
  exact (congrArg (fun q : Y' ⟶ B => q y.1 ∈ V) sq).mpr y.2

end General

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem translPt_one (T : Over S) : translPt A (1 : T ⟶ A) = snd T A := by
  show (fst T A ≫ (1 : T ⟶ A)) * snd T A = snd T A
  rw [MonObj.comp_one, _root_.one_mul]

theorem whisker_translPt {T T' : Over S} (g : T' ⟶ T) (x : T ⟶ A) :
    g ▷ A ≫ translPt A x = translPt A (g ≫ x) := by
  simp [translPt, comp_lift_assoc]

theorem locGen_pow {L : LB A.left} (hL : L.IsLB) {T : Over S}
    (sq : ∀ x y : T ⟶ A, LocGen L (K := Fin 4) (fst T A).left
      ![(translPt A (x * y)).left, (snd T A).left, (translPt A x).left, (translPt A y).left] ![1, 1, -1, -1])
    (x : T ⟶ A) (N : ℕ) :
    LocGen L (K := Fin 3) (fst T A).left ![(translPt A (x ^ N)).left, (snd T A).left, (translPt A x).left]
      ![-1, 1 - (N : ℤ), (N : ℤ)] := by
  induction N with
  | zero =>
    refine locGen_of_trivial hL fun U _ h => ?_
    rw [pow_zero, translPt_one, Fin.prod_univ_three]
    simp
  | succ n ih =>
    refine ih.comb hL (sq (x ^ n) x) fun U _ h => ?_
    rw [pow_succ x n, Fin.prod_univ_three, Fin.prod_univ_three, Fin.prod_univ_four]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    simp
    module

theorem eq_one_of_locGen {L : LB A.left} (hK : KTriv A L) {T : Over S} (y : T ⟶ A)
    (H : LocGen L (K := Fin 2) (fst T A).left ![(translPt A y).left, (snd T A).left] ![1, -1]) : y = 1 := by
  have loc : ∀ (R : CommRingCat.{0}) (f : Spec R ⟶ T.left), f ≫ y.left = f ≫ (1 : T ⟶ A).left := by
    intro R f
    let g : Over.mk (f ≫ T.hom) ⟶ T := Over.homMk f rfl
    have H' := H.baseChange (π' := (fst (Over.mk (f ≫ T.hom)) A).left) (g ▷ A).left f
      (congrArg (fun q => q.left) (whiskerRight_fst g A))
      (φ' := ![(translPt A (g ≫ y)).left, (snd _ A).left]) (fun k => by
        fin_cases k
        · exact congrArg (fun q => q.left) (whisker_translPt g y)
        · exact congrArg (fun q => q.left) (whiskerRight_snd g A))
    have e : g ≫ y = 1 := hK R (f ≫ T.hom) (g ≫ y) ((locGen_iff _ _ _).2 H')
    exact congrArg (fun q => q.left) (e.trans (MonObj.comp_one g).symm)
  ext1
  exact T.left.affineCover.hom_ext _ _ fun i => loc _ (T.left.affineCover.f i)

theorem locGen_theta_iff {L : LB A.left} (hL : L.IsLB) (hK : KTriv A L) {T : Over S}
    (sq : ∀ x y : T ⟶ A, LocGen L (K := Fin 4) (fst T A).left
      ![(translPt A (x * y)).left, (snd T A).left, (translPt A x).left, (translPt A y).left] ![1, 1, -1, -1])
    (x : T ⟶ A) (N : ℕ) :
    LocGen L (K := Fin 2) (fst T A).left ![(snd T A).left, (translPt A x).left] ![(N : ℤ), -(N : ℤ)] ↔ x ^ N = 1 := by
  have triv : LocGen L (K := Fin 0) (fst T A).left ![] ![] := locGen_of_trivial hL fun U _ h => by simp
  have P := triv.comb hL (locGen_pow hL sq x N)
    (φ'' := ![(translPt A (x ^ N)).left, (snd T A).left, (translPt A x).left]) (ε'' := ![1, (N : ℤ) - 1, -(N : ℤ)])
    fun U _ h => by
      rw [Fin.prod_univ_three, Fin.prod_univ_three]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      simp
      module
  constructor
  · intro H
    refine eq_one_of_locGen hK _ (P.comb hL H fun U _ h => ?_)
    rw [Fin.prod_univ_three, Fin.prod_univ_two, Fin.prod_univ_two]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    simp
    module
  · intro H
    refine P.comb hL triv fun U _ h => ?_
    rw [H, translPt_one, Fin.prod_univ_three, Fin.prod_univ_two]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    simp
    module

theorem exists_theta {L : LB A.left} {T : Over S} (x : T ⟶ A) (k : ℤ) (V : T.left.Opens)
    (H : HasGen L (fun i : Fin 2 => ((fst T A).left ⁻¹ᵁ V).ι ≫ ![(snd T A).left, (translPt A x).left] i) ![k, -k]) :
    ∃ θ : ThetaGrp A L k (overRes V), θ.pt = overResι V ≫ x := by
  obtain ⟨t, ht⟩ := H.of_range (overResι V ▷ A).left (fun y =>
      (congrArg (fun q : overRes V ⊗ A ⟶ T => q.left y ∈ V) (whiskerRight_fst (overResι V) A)).mpr
        ((fst (overRes V) A).left y).2)
    (φ' := ![(snd _ A).left, (translPt A (overResι V ≫ x)).left]) (fun i => by
      fin_cases i
      · exact congrArg (fun q => q.left) (whiskerRight_snd (overResι V) A)
      · exact congrArg (fun q => q.left) (whisker_translPt (overResι V) x))
  exact ⟨⟨overResι V ≫ x, t, ht⟩, rfl⟩

end GlobalTheory.KerPow

namespace GlobalTheory

open KerPow in

theorem kerPow_of_square :
    (∀ (S : Scheme.{0}) (P : PolAV S) (T : Over S) (x y : T ⟶ P.A) (p : T.left), ∃ V : T.left.Opens, p ∈ V ∧ ∃ c : LB.Gen ((LB.LinComb P.L (K := Fin 4) ![(translPt P.A (x * y)).left, (snd T P.A).left, (translPt P.A x).left, (translPt P.A y).left] ![1, 1, -1, -1]).pull ((fst T P.A).left ⁻¹ᵁ V).ι), c.IsGen) → (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A), (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ c : LB.Gen ((thetaLB P.A P.L N x).pull ((fst T P.A).left ⁻¹ᵁ V).ι), c.IsGen) ↔ x ^ N = 1) ∧ KerPowSt ∧ (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A), x ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp P.A P.L N (overRes V), θ.pt = overResι V ≫ x) := by
  intro sq
  have main := fun (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A) =>
    locGen_theta_iff P.isLB P.ktriv (fun x y => (locGen_iff _ _ _).1 (sq S P T x y)) x N
  have one : ∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A),
      (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
        ∃ c : LB.Gen ((thetaLB P.A P.L N x).pull ((fst T P.A).left ⁻¹ᵁ V).ι), c.IsGen) ↔ x ^ N = 1 :=
    fun S P N T x => (locGen_iff _ _ _).trans (main S P N T x)
  refine ⟨one, fun S _ P N _ T x => one S P N T x, fun S P N T x hx p => ?_⟩
  obtain ⟨V, hV, H⟩ := (main S P N T x).2 hx p
  exact ⟨V, hV, exists_theta x N V H⟩

end GlobalTheory
