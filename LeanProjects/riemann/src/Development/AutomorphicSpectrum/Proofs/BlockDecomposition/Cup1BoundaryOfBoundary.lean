import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SlantProductSecondAction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoboundaryCup1
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoboundaryCup0
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValSuccAbove
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFactorOfExactIsField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDualFunctionalsOfLinearIndependent
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HodgeCx

namespace GlobalTheory.CompanionTheory.HopfLe

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C]

section Prism

variable (F : C ⥤ CommAlgCat.{0} R)

theorem neg_one_pow_smul_int {A : Type} [AddCommGroup A] [Module R A] (k : ℕ) (a : A) :
    ((-1 : R) ^ k) • a = ((-1 : ℤ) ^ k) • a := by
  rcases Nat.even_or_odd k with h | h
  · simp [h.neg_one_pow]
  · simp [h.neg_one_pow]

theorem S_dn (q : ℕ) (w : Cn (box F) (q + 1)) :
    S F (q + 1) (dn (box F) (q + 1) w) =
      a1 F (cst 0 (1 : Fin 2)) (S0 F (q + 1) w) - a1 F (cst 0 (0 : Fin 2)) (S0 F (q + 1) w) -
        ∑ j : Fin (q + 2), ((-1 : R) ^ (j : ℕ)) • a2 F (Fin.succAboveOrderEmb j).toOrderHom (S F q w) := by
  have e1 : S F (q + 1) (dn (box F) (q + 1) w) = ∑ i : Fin (q + 2), ∑ j : Fin (q + 3),
      ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) • bi F ((th (q + 1) i).comp (Fin.succAboveOrderEmb j).toOrderHom)
        ((sg (q + 1) i).comp (Fin.succAboveOrderEmb j).toOrderHom) w := by
    rw [S_apply]
    simp only [dn, LinearMap.sum_apply, LinearMap.smul_apply, cof_eq]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [LinearMap.map_smul, bi_act, smul_smul, ← pow_add, neg_one_pow_smul_int (R := R)]
  have e2 : ∑ j : Fin (q + 2), ((-1 : R) ^ (j : ℕ)) • a2 F (Fin.succAboveOrderEmb j).toOrderHom (S F q w) =
      ∑ j : Fin (q + 2), ∑ i : Fin (q + 1), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) •
        bi F (th q i) ((Fin.succAboveOrderEmb j).toOrderHom.comp (sg q i)) w := by
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [S_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [LinearMap.map_smul, bisimplicial_action_second_factor, smul_smul, ← pow_add, neg_one_pow_smul_int (R := R),
      Nat.add_comm (j : ℕ) (i : ℕ)]
  have e3 : a1 F (cst 0 (1 : Fin 2)) (S0 F (q + 1) w) = bi F (cst (q + 1) 1) OrderHom.id w := bisimplicial_action_first_factor F _ _ _ w
  have e4 : a1 F (cst 0 (0 : Fin 2)) (S0 F (q + 1) w) = bi F (cst (q + 1) 0) OrderHom.id w := bisimplicial_action_first_factor F _ _ _ w
  rw [e1, e2, e3, e4]
  exact PrismComb.prism_faces q (fun θ ψ ↦ bi F θ ψ w)

theorem T_dn [Fintype (Fin 1 ⥤ C)] [Fintype (Fin 2 ⥤ C)] (q : ℕ) (ρ : Cn F 1 →ₗ[R] R) (w : Cn (box F) (q + 1)) :
    T F (q + 1) ρ (dn (box F) (q + 1) w) = U F (q + 1) (ρ ∘ₗ dn F 0) w - dn F q (T F q ρ w) := by
  have e : ρ ∘ₗ dn F 0 = ρ ∘ₗ act F (cst 0 (1 : Fin 2)) - ρ ∘ₗ act F (cst 0 (0 : Fin 2)) := by
    have d : dn F 0 = act F (cst 0 (1 : Fin 2)) - act F (cst 0 (0 : Fin 2)) := by
      have c0 : (Fin.succAboveOrderEmb (0 : Fin 2)).toOrderHom = cst 0 (1 : Fin 2) := by
        ext j
        fin_cases j
        simp [cst_apply]
      have c1 : (Fin.succAboveOrderEmb (1 : Fin 2)).toOrderHom = cst 0 (0 : Fin 2) := by
        ext j
        fin_cases j
        simp [cst_apply]
      have c0' : cof F 0 0 = act F (cst 0 (1 : Fin 2)) := (cof_eq F 0 0).trans (congrArg (act F) c0)
      have c1' : cof F 0 1 = act F (cst 0 (0 : Fin 2)) := (cof_eq F 0 1).trans (congrArg (act F) c1)
      rw [← c0', ← c1']
      exact LinearMap.ext fun f ↦ funext fun c ↦ GlobalTheory.CompanionTheory.Dict.dn0 F f c
    rw [d, LinearMap.comp_sub]
  change sl F (q + 1) ρ (S F (q + 1) _) = sl F (q + 1) (ρ ∘ₗ dn F 0) (S0 F (q + 1) w) - dn F q (sl F q ρ (S F q w))
  rw [S_dn, e, map_sub, map_sub, map_sum, slant_product_first_action, slant_product_first_action, sl_sub]
  congr 1
  simp only [dn, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, slant_product_second_action, cof_eq]

end Prism

section Core

variable (F : C ⥤ CommAlgCat.{0} R)

def IsB {n : ℕ} : Cn F n → Prop :=
  match n with
  | 0 => fun z ↦ z = 0
  | k + 1 => fun z ↦ ∃ y, z = dn F k y

theorem cup1_boundary_of_boundary {n : ℕ} (x : Cn F 1) (hx : dn F 1 x = 0) (z : Cn F n) (h : IsB F z) :
    ∃ y, cup1 F x z = dn F n y := by
  cases n with
  | zero =>
    have h0 : z = 0 := h
    exact ⟨0, by rw [h0, cup1_zero, map_zero]⟩
  | succ k =>
    obtain ⟨y, rfl⟩ := h
    exact ⟨- cup1 F x y, by rw [map_neg, DnCup.coboundary_cup1 F x y hx, neg_neg]⟩

theorem T_cup_L' [Fintype (Fin 1 ⥤ C)] [Fintype (Fin 2 ⥤ C)] (hR : IsField R)
    (hS : Function.Exact (Algebra.linearMap R (Cn F 0)) (dn F 0)) (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (q : ℕ)
    (Λ : Cn F 1 →ₗ[R] R) (x : Cn F 1) (hx : dn F 1 x = 0) (w : Cn (box F) (q + 1))
    (hw : dn (box F) (q + 1) w = 0) :
    ∃ y, T F (q + 1) Λ (cup1 (box F) (pulln (boxL F) 1 x) w) =
      Λ x • pulln (boxE F T₀ ε) (q + 1) w + dn F q y := by
  have h1 : evz F T₀ ε 1 = 1 := by
    change ε 1 = 1
    exact map_one ε
  obtain ⟨ρ, hρ⟩ := exists_rho_of_exact F hR hS (nu F Λ x) (evz F T₀ ε) h1
  have hA := T_dn F q ρ w
  rw [hw, map_zero] at hA
  refine ⟨T F q ρ w, ?_⟩
  rw [T_cup_L F q Λ x hx w, hρ, U_add, U_smul, U_evz, nu_one]
  have : U F (q + 1) (ρ ∘ₗ dn F 0) w = dn F q (T F q ρ w) := (sub_eq_zero.1 hA.symm)
  rw [this]

variable {F}
variable {D : Type} [Category.{0} D] {G : D ⥤ CommAlgCat.{0} R}

theorem core_step [Fintype (Fin 1 ⥤ C)] [Fintype (Fin 2 ⥤ C)] (hR : IsField R)
    (hS : Function.Exact (Algebra.linearMap R (Cn F 0)) (dn F 0))
    (π : CoefMap (RingHom.id R) (box F) G) (m : CoefMap (RingHom.id R) F G) (hπ : AllQIso π)
    (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (g : ℕ) (x : Fin (g + 1) → Cn F 1) (hx : ∀ i, dn F 1 (x i) = 0)
    (hprim : ∀ i, ∃ u, pulln π 1 (pulln (boxL F) 1 (x i) + pulln (boxR F) 1 (x i)) - pulln m 1 (x i) = dn G 0 u)
    (Λ : Fin (g + 1) → Cn F 1 →ₗ[R] R) (hΛ : ∀ i, Λ i ∘ₗ dn F 0 = 0) (hΛ1 : ∀ i, Λ i (x i) = 1)
    (hΛ0 : ∀ i j, i ≠ j → Λ i (x j) = 0) (s : ℕ) (hs : s ≤ g) :
    ∃ (z : Cn F (s + 1)) (w : Cn (box F) (s + 1)), dn F (s + 1) z = 0 ∧ dn (box F) (s + 1) w = 0 ∧
      (∃ v, pulln π (s + 1) w - pulln m (s + 1) z = dn G s v) ∧ pulln (boxE F T₀ ε) (s + 1) w = z ∧
      (∀ i : Fin (g + 1), (i : ℕ) + s < g → IsB F (T F s (Λ i) w)) ∧
      ((∃ y, z = dn F s y) → ∃ y, x (Fin.last g) = dn F 0 y) := by
  have cmπ : ∀ n u, pulln π (n + 1) (dn (box F) n u) = dn G n (pulln π n u) := fun n u ↦
    LinearMap.congr_fun (GlobalTheory.CompanionTheory.HodgeCx.pulln_dn π n) u
  have cmm : ∀ n u, pulln m (n + 1) (dn F n u) = dn G n (pulln m n u) := fun n u ↦
    LinearMap.congr_fun (GlobalTheory.CompanionTheory.HodgeCx.pulln_dn m n) u
  have cmL : ∀ (y : Cn F 1), dn F 1 y = 0 → dn (box F) 1 (pulln (boxL F) 1 y) = 0 := fun y hy ↦ by
    have := LinearMap.congr_fun (GlobalTheory.CompanionTheory.HodgeCx.pulln_dn (boxL F) 1) y
    simp only [LinearMap.comp_apply, hy, map_zero] at this
    exact this.symm
  have cmR : ∀ (y : Cn F 1), dn F 1 y = 0 → dn (box F) 1 (pulln (boxR F) 1 y) = 0 := fun y hy ↦ by
    have := LinearMap.congr_fun (GlobalTheory.CompanionTheory.HodgeCx.pulln_dn (boxR F) 1) y
    simp only [LinearMap.comp_apply, hy, map_zero] at this
    exact this.symm
  induction s with
  | zero =>
    obtain ⟨u, hu⟩ := hprim (Fin.last g)
    refine ⟨x (Fin.last g), pulln (boxL F) 1 (x (Fin.last g)) + pulln (boxR F) 1 (x (Fin.last g)), hx _,
      by rw [map_add, cmL _ (hx _), cmR _ (hx _), add_zero], ⟨u, hu⟩, ?_, fun i hi ↦ ?_, fun h ↦ ?_⟩
    · rw [map_add, tau_L F T₀ ε _ (hx _), tau_R F T₀ ε 1]
      exact zero_add _
    · have hne : i ≠ Fin.last g := fun e ↦ by
        rw [e] at hi
        simp at hi
      change T F 0 (Λ i) _ = 0
      rw [T_base F _ _ (hx _), hΛ0 i _ hne, zero_smul]
    · exact h
  | succ s ih =>
    obtain ⟨z, w, hz, hw, ⟨v, hv⟩, hτ, hB, hI⟩ := ih (by omega)
    have hj : g - s - 1 < g + 1 := by omega
    set j : Fin (g + 1) := ⟨g - s - 1, hj⟩ with hjdef
    set xj := x j with hxj
    have hxj0 : dn F 1 xj = 0 := hx j
    set pj := pulln (boxL F) 1 xj with hpj
    set qj := pulln (boxR F) 1 xj with hqj
    have hpq : dn (box F) 1 (pj + qj) = 0 := by
      rw [map_add, cmL _ hxj0, cmR _ hxj0, add_zero]

    have hT : ∀ i : Fin (g + 1), ∃ y, T F (s + 1) (Λ i) (cup1 (box F) (pj + qj) w) =
        Λ i xj • z + dn F s y - cup1 F xj (T F s (Λ i) w) := fun i ↦ by
      obtain ⟨y, hy⟩ := T_cup_L' F hR hS T₀ ε s (Λ i) xj hxj0 w hw
      refine ⟨y, ?_⟩
      rw [cup1_add_left, map_add, hy, T_cup_R F s (Λ i) xj hxj0 w, hτ]
      abel
    have hw' : dn (box F) (s + 1 + 1) (cup1 (box F) (pj + qj) w) = 0 := by
      rw [DnCup.coboundary_cup1 _ _ _ hpq, hw, cup1_zero, neg_zero]
    have hW : ∃ v', pulln π (s + 1 + 1) (cup1 (box F) (pj + qj) w) - pulln m (s + 1 + 1) (cup1 F xj z) =
        dn G (s + 1) v' := by
      obtain ⟨u, hu⟩ := hprim j
      have e1 : pulln π 1 (pj + qj) = pulln m 1 xj + dn G 0 u := by
        rw [← hu]; abel
      have e2 : pulln π (s + 1) w = pulln m (s + 1) z + dn G s v := by
        rw [← hv]; abel
      have hmx : dn G 1 (pulln m 1 xj) = 0 := by
        rw [← cmm, hxj0, map_zero]
      have hmz : dn G (s + 1) (pulln m (s + 1) z) = 0 := by
        rw [← cmm, hz, map_zero]
      have hcup : cup1 G (dn G 0 u) (pulln π (s + 1) w) = dn G (s + 1) (cup0 G u (pulln π (s + 1) w)) := by
        have hd : dn G (s + 1) (pulln π (s + 1) w) = 0 := by
          rw [← cmπ, hw, map_zero]
        rw [coboundary_cup0, hd]
        simp [cup0]
      refine ⟨- cup1 G (pulln m 1 xj) v + cup0 G u (pulln π (s + 1) w), ?_⟩
      rw [pullback_cup1, pullback_cup1, e1, cup1_add_left, hcup, e2, cup1_add_right, map_add, map_neg,
        DnCup.coboundary_cup1 G _ _ hmx, ← e2]
      abel
    refine ⟨cup1 F xj z, cup1 (box F) (pj + qj) w, ?_, hw', hW, ?_, fun i hi ↦ ?_, fun h ↦ ?_⟩
    · rw [DnCup.coboundary_cup1 F _ _ hxj0, hz, cup1_zero, neg_zero]
    · rw [pullback_cup1, map_add, tau_L F T₀ ε _ hxj0, tau_R F T₀ ε 1, zero_add, hτ]
    · have hij : i ≠ j := fun e ↦ by
        have := congrArg Fin.val e
        simp only [hjdef] at this
        omega
      obtain ⟨y, hy⟩ := hT i
      obtain ⟨y', hy'⟩ := cup1_boundary_of_boundary F xj hxj0 _ (hB i (by omega))
      refine ⟨y - y', ?_⟩
      rw [hy, hΛ0 i j hij, zero_smul, hy', map_sub, zero_add]
    · obtain ⟨t, ht⟩ := h
      obtain ⟨v', hv'⟩ := hW
      obtain ⟨r, hr⟩ := (hπ.2 (s + 1)).1 _ hw' ⟨pulln m (s + 1) t + v', by
        rw [map_add, ← cmm, ← ht, ← hv']
        abel⟩
      obtain ⟨y, hy⟩ := hT j
      have hjs : (j : ℕ) + s < g := by
        simp only [hjdef]
        omega
      obtain ⟨y', hy'⟩ := cup1_boundary_of_boundary F xj hxj0 _ (hB j hjs)
      have hA := T_dn F s (Λ j) r
      rw [hr, hy, hΛ j, U_zero, hΛ1, one_smul, hy', zero_sub] at hA
      refine hI ⟨y' - y - T F s (Λ j) r, ?_⟩
      rw [map_sub, map_sub]
      linear_combination (exp := 1) hA

end Core

section Top

theorem chains_finite (P : Type) [PartialOrder P] [Finite P] (n : ℕ) : Finite (Fin (n + 1) ⥤ Pᵒᵖ) := by
  have : Finite Pᵒᵖ := Finite.of_equiv P Opposite.equivToOpposite
  refine Finite.of_injective (fun (c : Fin (n + 1) ⥤ Pᵒᵖ) (i : Fin (n + 1)) ↦ c.obj i) fun c c' h ↦ ?_
  exact CategoryTheory.Functor.ext (fun i ↦ congrFun h i) (fun _ _ _ ↦ Subsingleton.elim _ _)

theorem exists_extend_of_isField (hR : IsField R) {V : Type} [AddCommGroup V] [Module R V] (p : Submodule R V)
    (f : p →ₗ[R] R) : ∃ g : V →ₗ[R] R, g ∘ₗ p.subtype = f := by
  letI := hR.toField
  exact LinearMap.exists_extend f

variable {D : Type} [Category.{0} D] {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}

theorem L1_pullback_naturality (m : CoefMap (RingHom.id R) F G) (f : Cn F 1) :
    GlobalTheory.CompanionTheory.Dict.L1 G (pulln m 1 f) = GlobalTheory.CompanionTheory.HodgeLow.pullbackOneCochains m (GlobalTheory.CompanionTheory.Dict.L1 F f) := by
  funext T T' φ
  change m.α T' (f (ComposableArrows.mk₁ φ ⋙ m.G)) = m.α T' (f (ComposableArrows.mk₁ (m.G.map φ)))
  exact congrArg (m.α T') (eq_of_heq (GlobalTheory.CompanionTheory.HodgeLow.cn_heq f (GlobalTheory.CompanionTheory.HodgeLow.mk₁_comp m.G φ)))

theorem exact_of_stein (hSt : Stein F) : Function.Exact (Algebra.linearMap R (Cn F 0)) (dn F 0) := by
  have hal : ∀ r : R, GlobalTheory.CompanionTheory.Dict.L0 F (algebraMap R (Cn F 0) r) = algebraMap R (C0 F) r := fun r ↦ rfl
  intro y
  refine ⟨fun h ↦ ?_, ?_⟩
  · have h0 : d0 F (GlobalTheory.CompanionTheory.Dict.L0 F y) = 0 := by
      rw [← GlobalTheory.CompanionTheory.Dict.L1_dn_zero_eq_d0_L0, h, map_zero]
    obtain ⟨r, hr⟩ := (hSt.1 _).1 h0
    exact ⟨r, (GlobalTheory.CompanionTheory.Dict.L0_bijective_cochain F).1 ((hal r).trans hr)⟩
  · rintro ⟨r, rfl⟩
    refine (GlobalTheory.CompanionTheory.Dict.L1_bijective_cochain F).1 ?_
    rw [map_zero, GlobalTheory.CompanionTheory.Dict.L1_dn_zero_eq_d0_L0]
    exact (hSt.1 _).2 ⟨r, (hal r).symm⟩

end Top

theorem hopfLeSt : CxSt → DictSt → LowSt → HopfLeSt := by
  intro _ _ _ R _ P _ _ F g hR hSt hvan hH x hx
  obtain ⟨D, _, G, π, m, hπ, hprim, hb⟩ := hH
  obtain ⟨T₀, ε, -⟩ := hb trivial
  haveI : Nontrivial R := ⟨hR.exists_pair_ne⟩
  letI : Fintype (Fin 1 ⥤ Pᵒᵖ) := @Fintype.ofFinite _ (chains_finite P 0)
  letI : Fintype (Fin 2 ⥤ Pᵒᵖ) := @Fintype.ofFinite _ (chains_finite P 1)
  have hS := exact_of_stein hSt
  choose f hf using fun i ↦ H1.mk_surjective F (x i)
  choose xt hxt using fun i ↦ (GlobalTheory.CompanionTheory.Dict.L1_bijective_cochain F).2 (f i).1
  have hxc : ∀ i, dn F 1 (xt i) = 0 := fun i ↦ by
    refine (GlobalTheory.CompanionTheory.Dict.L2_bijective_cochain F).1 ?_
    rw [GlobalTheory.CompanionTheory.Dict.L2_dn_one_eq_d1_L1, hxt, map_zero]
    exact LinearMap.mem_ker.1 (commAlgFunctorCocyclesOne_eq_ker F ▸ (f i).2)
  obtain ⟨l, hl⟩ := exists_dual_functionals_of_linearIndependent hR x hx
  have hZ : ∀ t : LinearMap.ker (dn F 1), GlobalTheory.CompanionTheory.Dict.L1 F t.1 ∈ Z1 F := fun t ↦ by
    rw [commAlgFunctorCocyclesOne_eq_ker, LinearMap.mem_ker, ← GlobalTheory.CompanionTheory.Dict.L2_dn_one_eq_d1_L1, LinearMap.mem_ker.1 t.2, map_zero]
  let Φ : LinearMap.ker (dn F 1) →ₗ[R] H1 F :=
    H1.mk F ∘ₗ ((GlobalTheory.CompanionTheory.Dict.L1 F) ∘ₗ (LinearMap.ker (dn F 1)).subtype).codRestrict (Z1 F) hZ
  choose Λ hΛ using fun i ↦ exists_extend_of_isField hR (LinearMap.ker (dn F 1)) (l i ∘ₗ Φ)
  have hΛv : ∀ i (t : Cn F 1) (ht : dn F 1 t = 0), Λ i t = l i (Φ ⟨t, ht⟩) := fun i t ht ↦
    LinearMap.congr_fun (hΛ i) ⟨t, ht⟩
  have hΦx : ∀ j, Φ ⟨xt j, hxc j⟩ = x j := fun j ↦ by
    rw [← hf j]
    exact congrArg (H1.mk F) (Subtype.ext (hxt j))
  have hdd : ∀ y : Cn F 0, dn F 1 (dn F 0 y) = 0 := fun y ↦
    LinearMap.congr_fun (GlobalTheory.CompanionTheory.HodgeCx.dn_comp_dn F 0) y
  have hΦd : ∀ y : Cn F 0, Φ ⟨dn F 0 y, hdd y⟩ = 0 := fun y ↦
    H1.mk_eq_zero.2 ⟨GlobalTheory.CompanionTheory.Dict.L0 F y, (GlobalTheory.CompanionTheory.Dict.L1_dn_zero_eq_d0_L0 F y).symm⟩
  have hΛ0 : ∀ i, Λ i ∘ₗ dn F 0 = 0 := fun i ↦ LinearMap.ext fun y ↦ by
    rw [LinearMap.comp_apply, hΛv i _ (hdd y), hΦd, map_zero]
    rfl
  have hΛ1 : ∀ i, Λ i (xt i) = 1 := fun i ↦ by
    rw [hΛv i _ (hxc i), hΦx, hl, if_pos rfl]
  have hΛn : ∀ i j, i ≠ j → Λ i (xt j) = 0 := fun i j h ↦ by
    rw [hΛv i _ (hxc j), hΦx, hl, if_neg h]
  have hpr : ∀ i, ∃ u, pulln π 1 (pulln (boxL F) 1 (xt i) + pulln (boxR F) 1 (xt i)) - pulln m 1 (xt i) =
      dn G 0 u := fun i ↦ by
    have h := hprim (x i)
    rw [← hf i, CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class, ← map_add, CoefMap.pullCohomologyOne_class,
      H1.mk_eq_mk] at h
    obtain ⟨a, ha⟩ := h
    obtain ⟨u, rfl⟩ := (GlobalTheory.CompanionTheory.Dict.L0_bijective_cochain G).2 a
    refine ⟨-u, (GlobalTheory.CompanionTheory.Dict.L1_bijective_cochain G).1 ?_⟩
    rw [map_neg, map_neg, GlobalTheory.CompanionTheory.Dict.L1_dn_zero_eq_d0_L0, ha, map_sub, L1_pullback_naturality, map_add, L1_pullback_naturality, L1_pullback_naturality, L1_pullback_naturality, hxt]
    rw [neg_sub]
    rfl
  obtain ⟨z, w, hz, -, -, -, -, hI⟩ := core_step hR hS π m hπ T₀ ε g xt hxc hpr Λ hΛ0 hΛ1 hΛn g le_rfl
  obtain ⟨y, hy⟩ := hI (by
    obtain ⟨y, hy⟩ := (hvan g le_rfl z).1 hz
    exact ⟨y, hy.symm⟩)
  refine hx.ne_zero (Fin.last g) ?_
  rw [← hf]
  refine H1.mk_eq_zero.2 ⟨GlobalTheory.CompanionTheory.Dict.L0 F y, ?_⟩
  rw [← GlobalTheory.CompanionTheory.Dict.L1_dn_zero_eq_d0_L0, ← hy, hxt]

end GlobalTheory.CompanionTheory.HopfLe
