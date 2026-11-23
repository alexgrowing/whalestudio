import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfCountAtOf
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLevelGenB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFirstColumnSpaceRankSignatureSelfDual

noncomputable section

namespace GlobalTheory.SumCount.Pure

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem reps_fg {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V] (M : Submodule ℤ V) (hM : M.FG) (n : ℕ)
    (hn : 0 < n) : ∃ R : Finset V, R.card ≤ n ^ Module.finrank ℚ V ∧ ∀ u ∈ M, ∃ r ∈ R, ∃ v ∈ M, u = r + n • v := by
  classical
  haveI : Module.Finite ℤ M := Module.Finite.iff_fg.2 hM
  haveI : IsAddTorsionFree V := IsAddTorsionFree.of_module_rat V
  haveI : Module.Free ℤ M := inferInstance
  let b := Module.finBasis ℤ M
  have h1 : LinearIndependent ℤ (fun i => (b i : V)) := b.linearIndependent.map' M.subtype M.ker_subtype
  have h2 : LinearIndependent ℚ (fun i => (b i : V)) := (LinearIndependent.iff_fractionRing ℤ ℚ).1 h1
  have h3 : Module.finrank ℤ M ≤ Module.finrank ℚ V := by simpa using h2.fintype_card_le_finrank
  refine ⟨Finset.univ.image fun c : Fin (Module.finrank ℤ M) → Fin n => ∑ i, ((c i : ℕ) : ℤ) • (b i : V), ?_, fun u hu => ?_⟩
  · refine Finset.card_image_le.trans ?_
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    exact Nat.pow_le_pow_right hn h3
  · have hn' : (0 : ℤ) < n := by exact_mod_cast hn
    let c := b.repr ⟨u, hu⟩
    have hlt : ∀ i, (c i % n).toNat < n := fun i => by
      have := Int.emod_lt_of_pos (c i) hn'
      have := Int.emod_nonneg (c i) hn'.ne'
      omega
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ fun i => (⟨_, hlt i⟩ : Fin n)),
      ∑ i, (c i / n) • (b i : V), M.sum_mem fun i _ => M.smul_mem _ (b i).2, ?_⟩
    have e : u = ∑ i, c i • (b i : V) := by
      have := congrArg M.subtype (b.sum_repr ⟨u, hu⟩)
      rw [map_sum] at this
      exact this.symm
    rw [e, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Nat.cast_smul_eq_nsmul ℤ, smul_smul, ← add_smul, Int.toNat_of_nonneg (Int.emod_nonneg _ hn'.ne'), Int.emod_add_mul_ediv]

variable {D : D7}

private theorem reps_latO (S T : HSp D) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : LS.FG) (hT : LT.FG) (n : ℕ) (hn : 0 < n) :
    ∃ R : Finset (WO S T), R.card ≤ n ^ (T.rank * S.rank * (2 * D.R.f)) ∧
      ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True), ∃ r ∈ R,
        ∃ v ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True), u = r + n • v := by
  classical
  let gen : D.host.E → (Fin S.rank → D.host.E) → (Fin T.rank → D.host.E) → Matrix (Fin T.rank) (Fin S.rank) D.host.E :=
    fun a s t => Matrix.of fun i j => a * t i * ∑ k, star (s k) * S.gram k j
  let M : Submodule ℤ (Matrix (Fin T.rank) (Fin S.rank) D.host.E) :=
    Submodule.span ℤ {w | ∃ a ∈ D.host.AA, ∃ s ∈ LS, ∃ t ∈ LT, w = gen a s t}
  have hM : M.FG := by
    let ρ : Fin S.rank → (Fin S.rank → D.host.E) →+ D.host.E := fun j =>
      { toFun := fun s => ∑ k, star (s k) * S.gram k j
        map_zero' := by simp
        map_add' := fun s s' => by simp [add_mul, Finset.sum_add_distrib] }
    have hA : ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E).restrictScalars ℤ).FG :=
      Submodule.FG.restrictScalars (FractionalIdeal.fg_of_isNoetherianRing le_rfl _)
    have hS' : (LS.restrictScalars ℤ).FG := Submodule.FG.restrictScalars hS
    have hT' : (LT.restrictScalars ℤ).FG := Submodule.FG.restrictScalars hT
    let N : Fin T.rank → Fin S.rank → Submodule ℤ D.host.E := fun i j =>
      (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).restrictScalars ℤ * (LT.restrictScalars ℤ).map (LinearMap.proj i) *
        (LS.restrictScalars ℤ).map (ρ j).toIntLinearMap
    have hN : (Submodule.pi Set.univ fun i => Submodule.pi Set.univ fun j => N i j).FG :=
      Submodule.fg_pi fun i => Submodule.fg_pi fun j => (hA.mul (hT'.map _)).mul (hS'.map _)
    refine Submodule.FG.of_le (R := ℤ) hN (Submodule.span_le.2 ?_)
    rintro _ ⟨a, ha, s, hs, t, ht, rfl⟩ i - j -
    exact Submodule.mul_mem_mul (Submodule.mul_mem_mul ha ⟨t, ht, rfl⟩) ⟨s, hs, rfl⟩
  obtain ⟨R, hR, hR'⟩ := reps_fg M hM n hn
  rw [Module.finrank_matrix, Fintype.card_fin, Fintype.card_fin, Formalism.MainNotions.StandardLattice.finrank_host D] at hR
  let φ : Matrix (Fin T.rank) (Fin S.rank) D.host.E →+ WO S T :=
    { toFun := fun x => Matrix.of fun i j => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] x i j
      map_zero' := by ext i j; simp
      map_add' := fun x y => by ext i j; simp [TensorProduct.tmul_add] }
  set Λ := latO S T (LS : Set _) (LT : Set _) (fun _ => True) with hΛ
  have h1 : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by rw [map_one]; exact one_mem _
  have hφ : ∀ x ∈ M, φ x ∈ Λ := fun x hx => by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hx
      exact AddSubgroup.subset_closure ⟨1, h1, fun v h => absurd trivial h, a, ha, s, hs, t, ht, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_zsmul]; exact zsmul_mem hx c
  have key : ∀ u ∈ Λ, ∃ x ∈ M, ∃ v ∈ Λ, u = φ x + n • v := fun u hu => by
    induction hu using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
      obtain ⟨c, β, hβ, e⟩ := Formalism.MainNotions.BridgeLevelGenB.dense_mod n hn α hα
      refine ⟨gen a s (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c • t),
        Submodule.subset_span ⟨a, ha, s, hs, _, LT.smul_mem _ ht, rfl⟩, _,
        AddSubgroup.subset_closure ⟨β, hβ, fun v h => absurd trivial h, a, ha, s, hs, t, ht, rfl⟩, ?_⟩
      have e1 : pairA D.host.F 0 α = (c : D.host.F) • pairA D.host.F 0 1 + n • pairA D.host.F 0 β := by
        rw [e]
        refine Prod.ext ?_ ?_
        · show (0 : Ainf D.host.F) = (c : D.host.F) • (0 : Ainf D.host.F) + n • (0 : Ainf D.host.F)
          simp
        · show _ + _ = (c : D.host.F) • (1 : Af D.host.F) + n • β
          rw [Algebra.smul_def, mul_one, nsmul_eq_mul]
      ext i j
      show _ ⊗ₜ[D.host.F] _ = (pairA D.host.F 0 1) ⊗ₜ[D.host.F] _ + n • (_ ⊗ₜ[D.host.F] _)
      rw [e1, TensorProduct.add_tmul, TensorProduct.smul_tmul, TensorProduct.smul_tmul']
      congr 2
      show _ = a * (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c • t i) * _
      have e2 : algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c) =
        algebraMap D.host.F D.host.E (c : D.host.F) := rfl
      rw [Algebra.smul_def (c : D.host.F), Algebra.smul_def _ (t i), e2]
      ring
    | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, v, hv, rfl⟩ := hx
      obtain ⟨a', ha', v', hv', rfl⟩ := hy
      exact ⟨a + a', add_mem ha ha', v + v', add_mem hv hv', by rw [map_add, nsmul_add]; abel⟩
    | neg x _ hx =>
      obtain ⟨a, ha, v, hv, rfl⟩ := hx
      exact ⟨-a, neg_mem ha, -v, neg_mem hv, by rw [map_neg, smul_neg]; abel⟩
  refine ⟨R.image φ, Finset.card_image_le.trans hR, fun u hu => ?_⟩
  obtain ⟨x, hx, v, hv, rfl⟩ := key u hu
  obtain ⟨r, hr, y, hy, rfl⟩ := hR' x hx
  exact ⟨φ r, Finset.mem_image_of_mem _ hr, φ y + v, add_mem (hφ y hy) hv, by rw [map_add, map_nsmul, nsmul_add]; abel⟩

private theorem coset_fns {a b : ℕ} (e : AE D) (Λ : AddSubgroup (Mx D a b)) {k : ℕ} (hk : 0 < k) (R : Finset (Mx D a b))
    (hR : ∀ u ∈ Λ, ∃ r ∈ R, ∃ v ∈ Λ, u = r + (k * k) • v) :
    ∃ Fn : Finset (Mx D a b → ℂ), Fn.card ≤ R.card ∧
      ∀ x₀, IsHalf e x₀ → k • x₀ ∈ Λ → (halfCoset e Λ k x₀).indicator 1 ∈ Fn := by
  classical
  have inv : incA D (k : D.host.E)⁻¹ * (k : AE D) = 1 := by
    rw [← map_natCast (incA D), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hk.ne'), map_one]
  have inj : ∀ x y : Mx D a b, k • x = k • y → x = y := fun x y h => by
    have h' := congrArg (fun z : Mx D a b => incA D (k : D.host.E)⁻¹ • z) h
    rwa [← Nat.cast_smul_eq_nsmul (AE D), ← Nat.cast_smul_eq_nsmul (AE D), smul_smul, smul_smul, inv,
      one_smul, one_smul] at h'
  let P : Mx D a b → Mx D a b → Prop := fun r x => IsHalf e x ∧ ∃ v ∈ Λ, k • x = r + (k * k) • v
  refine ⟨R.image fun r => (halfCoset e Λ k (Classical.epsilon (P r))).indicator 1, Finset.card_image_le, fun x hx hx' => ?_⟩
  obtain ⟨r, hr, v, hv, h⟩ := hR _ hx'
  obtain ⟨hy, v', hv', h'⟩ := Classical.epsilon_spec (p := P r) ⟨x, hx, v, hv, h⟩
  refine Finset.mem_image.2 ⟨r, hr, ?_⟩
  set y := Classical.epsilon (P r)
  have e1 : x = y + k • (v - v') := inj _ _ (by rw [nsmul_add, h, h', ← mul_nsmul', nsmul_sub]; abel)
  have e2 : IsHalf e (v - v') := by
    have e3 : (v - v').map (e * ·) = v - v' := inj _ _ (by
      ext i j
      have e4 : (k • (v - v')) i j = x i j - y i j := by rw [e1]; simp
      rw [e4, ← hx i j, ← hy i j, ← mul_sub, ← e4]
      simp [mul_left_comm])
    exact fun i j => congrFun (congrFun e3 i) j
  rw [halfCoset_eq (x := x) ⟨v - v', sub_mem hv hv', e2, e1⟩]

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

private theorem rank_le {μ : T} (hL : L.Is μ) {X : Node} (h : DefNode D.R.m X) :
    (G.Λ X).FG ∧ (G.V X).rank ≤ bigN D := by
  have hX : X.InRange D.R.m := by cases X <;> simp only [DefNode, Node.InRange] at h ⊢ <;> omega
  have hV : (G.node X).IsV (X.rank D) (X.neg D.R.m) := by
    by_cases h0 : ∀ j, X ≠ .grid 0 j
    · exact G.isV hX h0
    · push Not at h0
      obtain ⟨j, rfl⟩ := h0
      exact GlobalTheory.ChiGrid.colY_isV D T L μ hL j hX.2
  refine ⟨hV.sd.1.fg, hV.rank.trans_le ?_⟩
  have := D.R.two_le_m
  rcases X with ⟨i, j⟩ | i | j
  · obtain ⟨h1, rfl⟩ := h
    have := Nat.mul_le_mul_right (sLen D) h1
    simp only [Node.rank, rankV, bigN, mul_add, mul_one, Ranks.r]
    omega
  · exact h.elim
  · have := Nat.mul_le_mul_right (D.R.t + 1) (show j ≤ D.R.m from h)
    have e : sLen D = sLen D - 1 + 1 := by unfold sLen; omega
    simp only [Node.rank, rankX, rankP, nRk, bigN]
    rw [e]
    simp only [mul_add, mul_one, Ranks.r, Nat.add_sub_cancel] at this ⊢
    omega

private theorem pair_fns {μ : T} (hL : L.Is μ) {p : Pair T} (hp : DefPair D.R.m p) (e : AE D) {k : ℕ} (hk : 0 < k) :
    ∃ Fn : Finset (WO (G.pS p) (G.pT p) → ℂ), Fn.card ≤ k ^ (4 * D.R.f * bigN D ^ 2) ∧
      ∀ t (d : FinDatum G t p), d.e = e → IsCosetDatum k d → d.fn ∈ Fn := by
  obtain ⟨h1, h2⟩ := hp.nodes
  obtain ⟨a1, a2⟩ := rank_le (G := G) hL h1
  obtain ⟨b1, b2⟩ := rank_le (G := G) hL h2
  have key : (G.latS p).FG ∧ (G.latT p).FG ∧ (G.pS p).rank ≤ bigN D ∧ (G.pT p).rank ≤ bigN D := by
    cases p
    · exact ⟨b1, a1, b2, a2⟩
    · exact ⟨a1, b1, a2, b2⟩
    · exact ⟨b1, a1, b2, a2⟩
    · exact ⟨a1, b1, a2, b2⟩
  obtain ⟨R, hR, hR'⟩ := reps_latO _ _ _ _ key.1 key.2.1 (k * k) (Nat.mul_pos hk hk)
  obtain ⟨Fn, hF, hF'⟩ := coset_fns e _ hk R hR'
  refine ⟨Fn, hF.trans (hR.trans ?_), ?_⟩
  · rw [← sq, ← pow_mul]
    refine Nat.pow_le_pow_right hk ?_
    have := Nat.mul_le_mul key.2.2.2 key.2.2.1
    calc _ = 4 * D.R.f * ((G.pT p).rank * (G.pS p).rank) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (by rwa [sq])
  · rintro t d rfl ⟨x, hx, hx', h⟩
    rw [h]
    exact hF' x hx hx'

private theorem card_support {μ : T} (hL : L.Is μ) {W : G.Weil} {U : Set T} {S : GridChoice W U} {t Φ β k τ}
    (h : IsCosetExpansion S t Φ β k τ) : τ.support.card ≤ k ^ (8 * D.R.f * D.R.m * bigN D ^ 2) := by
  classical
  obtain ⟨hk, ⟨e, -, h1, -⟩, h3⟩ := h
  have ext : ∀ {p : Pair T} (a b : FinDatum G t p), a.P = b.P → a.e = b.e → a.fn = b.fn → a.z = b.z → a = b := by
    rintro p ⟨⟩ ⟨⟩ h1 h2 h3 h4
    simp only at h1 h2 h3 h4
    subst h1 h2 h3 h4
    rfl
  choose F1 c1 m1 using fun j : Fin D.R.m => pair_fns (G := G) hL (p := .top t j) j.2 e hk
  choose F2 c2 m2 using fun i : Fin D.R.m => pair_fns (G := G) hL (p := .chi i D.R.m) ⟨i.2, rfl⟩ e hk
  have hle : τ.support.card ≤ (Fintype.piFinset F1 ×ˢ Fintype.piFinset F2).card := by
    refine Finset.card_le_card_of_injOn (fun d => (fun j => (d.1 j).fn, fun i => (d.2 i).fn)) (fun d hd => ?_)
      fun d hd d' hd' hh => ?_
    · exact Finset.mem_product.2 ⟨Fintype.mem_piFinset.2 fun j => m1 j t _ ((h1 d hd).1 j).2.1 ((h3 d hd).1 j),
        Fintype.mem_piFinset.2 fun i => m2 i t _ ((h1 d hd).2 i).2.1 ((h3 d hd).2 i)⟩
    · refine Prod.ext (funext fun j => ?_) (funext fun i => ?_)
      · obtain ⟨a1, a2, a3⟩ := (h1 d hd).1 j
        obtain ⟨b1, b2, b3⟩ := (h1 d' hd').1 j
        exact ext _ _ (a1.trans b1.symm) (a2.trans b2.symm) (congrFun (congrArg Prod.fst hh) j) (a3.trans b3.symm)
      · obtain ⟨a1, a2, a3⟩ := (h1 d hd).2 i
        obtain ⟨b1, b2, b3⟩ := (h1 d' hd').2 i
        exact ext _ _ (a1.trans b1.symm) (a2.trans b2.symm) (congrFun (congrArg Prod.snd hh) i) (a3.trans b3.symm)
  refine hle.trans ?_
  rw [Finset.card_product, Fintype.card_piFinset, Fintype.card_piFinset]
  refine (Nat.mul_le_mul (Finset.prod_le_pow_card _ _ _ fun j _ => c1 j) (Finset.prod_le_pow_card _ _ _ fun j _ => c2 j)).trans_eq ?_
  rw [Finset.card_univ, Fintype.card_fin, ← pow_mul, ← pow_add]
  congr 1
  ring

private theorem depth_le {k : ℕ} (hk : 0 < k) (h : ∀ l : ℕ, l.Prime → padicValNat l k ≤ depL G l) :
    k ≤ (q0 D * (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde')) ^ (depth0 D sc.cDep sc.b + 2) := by
  classical
  set P := q0 D * (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') with hP
  have hP0 : P ≠ 0 := mul_ne_zero (leastSplitAuxiliaryPrimeThetaChain_spec D).1.ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero) D.host.pde_prime.ne_zero) D.host.pde'_prime.ne_zero)
  refine Nat.le_of_dvd (Nat.pos_of_ne_zero (pow_ne_zero _ hP0)) ?_
  refine (Nat.factorization_prime_le_iff_dvd hk.ne' (pow_ne_zero _ hP0)).1 fun l hl => ?_
  rw [Nat.factorization_def _ hl, Nat.factorization_pow]
  refine (h l hl).trans (Finset.sup_le fun w hw => ?_)
  obtain ⟨hw, hlw⟩ := Finset.mem_filter.1 hw
  obtain ⟨v, hv, rfl⟩ : ∃ v ∈ G.pl.S0, G.pl.w v = w := by simpa [Places.W0] using hw
  have h1 : (P : 𝓞 D.host.F) ∈ v.asIdeal := by
    rw [hP]
    push_cast
    rcases G.pl.mem_S0_of_sum_eq.1 hv with rfl | h
    · exact Ideal.mul_mem_right _ _ G.pl.basePlace_over_qZero
    · refine Ideal.mul_mem_left _ _ ?_
      rcases (S1_mem_OmF D).1 h with h | h | h | h
      · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h))
      · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ h))
      · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ h)
      · exact Ideal.mul_mem_left _ _ h
  have h2 : (P : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal := by
    rw [← G.pl.under_w hv] at h1
    have : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (P : 𝓞 D.host.F) ∈ (G.pl.w v).asIdeal := h1
    rwa [map_natCast] at this
  have h3 : l ∣ P := by
    by_contra hn
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hl).2 hn)
    refine (G.pl.w v).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    have := congrArg (Int.cast : ℤ → 𝓞 D.host.E) hab
    push_cast at this
    rw [← this]
    exact add_mem (Ideal.mul_mem_left _ _ hlw) (Ideal.mul_mem_left _ _ h2)
  have h4 : 1 ≤ P.factorization l := (hl.dvd_iff_one_le_factorization hP0).1 h3
  have h5 : depthAt G (G.pl.w v) ≤ depth0 D sc.cDep sc.b + 2 := by
    rw [(depthAt_w G hv).2, Places.depth]
    split_ifs <;> omega
  rw [Finsupp.smul_apply, smul_eq_mul]
  exact h5.trans (Nat.le_mul_of_pos_right _ h4)

private theorem size_le (large₂ : SizeData₂ D) (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) {CF : ℝ} (hCF : 0 ≤ CF) {k : ℕ} (hk : 0 < k)
    (h : k ≤ (q0 D * (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde')) ^ (depth0 D CF large₂.sc.b + 2)) :
    8 * (bigN D : ℝ) * Real.log k ≤ 1840 * (50 * CF + 3) * large₂.sc.b * Real.log large₂.sc.b := by
  obtain ⟨-, hz, -, -, -, -, -, hg, hq, hrd, hc, -⟩ := hs
  obtain ⟨-, -, -, -, -, hcond, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hp, hp'⟩, -⟩ := hz
  unfold SizeCond at hcond
  have hb : Real.log large₂.sc.b = large₂.sc.L := Real.log_exp _
  have hb0 : 0 < large₂.sc.b := Real.exp_pos _
  have hL : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  set L := large₂.sc.L with hLdef
  have pos : ∀ {n : ℕ}, n.Prime → (0 : ℝ) < n := fun h => by exact_mod_cast h.pos
  have p0 := pos (D.host.g_prime 0)
  have p1 := pos (D.host.g_prime 1)
  have p2 := pos D.host.pde_prime
  have p3 := pos D.host.pde'_prime
  have p4 := pos (leastSplitAuxiliaryPrimeThetaChain_spec D).1
  have n1 := D.R.rank_add_five_le
  have n2 := D.R.two_le_m
  have n3 := D.R.f_le_k
  have nf : D.R.f ≤ D.R.t := by unfold Ranks.f Ranks.n; omega
  have nn : nRk D ≤ D.R.t := by unfold nRk Ranks.r; omega
  have nN : bigN D ≤ 5 * D.R.t ^ 2 := by
    have a1 : D.R.m * (D.R.t + sLen D + 1) ≤ D.R.t * (4 * D.R.t) :=
      Nat.mul_le_mul (by omega) (by unfold sLen Ranks.r; omega)
    have a2 : D.R.t * 1 ≤ D.R.t * D.R.t := Nat.mul_le_mul_left _ (by omega)
    have a3 : D.R.k ≤ D.R.t := by omega
    unfold bigN
    nlinarith
  have t1 : (1 : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : 1 ≤ D.R.t)
  have tf : (D.R.f : ℝ) ≤ D.R.t := by exact_mod_cast nf
  have tn : (nRk D : ℝ) ≤ D.R.t := by exact_mod_cast nn
  have tN : (bigN D : ℝ) ≤ 5 * (D.R.t : ℝ) ^ 2 := by exact_mod_cast nN
  have n0 : (0 : ℝ) < nRk D := by exact_mod_cast (by unfold nRk; omega : 0 < nRk D)
  have f0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  generalize (D.R.t : ℝ) = t at t1 tf tn tN hcond
  have d1 : (1 : ℝ) ≤ |((discr D.host.E : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs (discr_ne_zero D.host.E)
  have hd : Real.log |((discr D.host.E : ℤ) : ℝ)| ≤ t * L := by
    have e : Real.log |((discr D.host.E : ℤ) : ℝ)| = 2 * D.R.f * Real.log D.host.rdE := by
      have : (Module.finrank ℚ D.host.E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
      have e2 : (2 * D.R.f : ℝ) = Module.finrank ℚ D.host.E := by rw [Formalism.MainNotions.StandardLattice.finrank_host D]; push_cast; ring
      unfold Host.rdE
      rw [Real.log_rpow (by linarith), e2]
      field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left (hrd.trans hc) f0
    nlinarith
  have hlog : Real.log (large₂.sc.b * nRk D * D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' * |(discr D.host.E : ℝ)|) ≤
      25 * (t * L) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), hb]
    have a1 := (Real.log_le_sub_one_of_pos n0)
    have a2 : L ≤ t * L := le_mul_of_one_le_left (by linarith) t1
    have a3 : t ≤ t * L := le_mul_of_one_le_right (by linarith) hL
    linarith [hg 0, hg 1]
  have hS : sizeP D CF large₂.sc.b ≤ 25 * CF * (t ^ 9 * L) := by
    unfold sizeP
    calc _ ≤ CF * (D.R.f : ℝ) ^ 2 * (nRk D : ℝ) ^ 6 * (25 * (t * L)) := by gcongr
      _ ≤ CF * t ^ 2 * t ^ 6 * (25 * (t * L)) := by gcongr
      _ = _ := by ring
  have tL : 1 ≤ t ^ 9 * L := one_le_mul_of_one_le_of_one_le (one_le_pow₀ t1) hL
  have lq : 1 / 2 ≤ Real.log (q0 D) := by
    have : (2 : ℝ) ≤ q0 D := by exact_mod_cast (leastSplitAuxiliaryPrimeThetaChain_spec D).1.two_le
    linarith [Real.log_two_gt_d9, Real.log_le_log two_pos this]
  have hM : ((depth0 D CF large₂.sc.b + 2 : ℕ) : ℝ) ≤ (50 * CF + 3) * (t ^ 9 * L) := by
    have a1 : sizeP D CF large₂.sc.b / Real.log (q0 D) ≤ 50 * CF * (t ^ 9 * L) := by
      rw [div_le_iff₀ (by linarith)]
      have : 0 ≤ 50 * CF * (t ^ 9 * L) := by positivity
      nlinarith
    have a2 : (⌊sizeP D CF large₂.sc.b / Real.log (q0 D)⌋₊ : ℝ) ≤ 50 * CF * (t ^ 9 * L) :=
      (Nat.cast_le.2 (Nat.floor_le_floor a1)).trans (Nat.floor_le (by positivity))
    unfold depth0
    push_cast
    linarith
  have hk' : Real.log k ≤ (50 * CF + 3) * (t ^ 9 * L) * (23 * L) := by
    have a1 : (k : ℝ) ≤ ((q0 D : ℝ) * (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde')) ^ (depth0 D CF large₂.sc.b + 2) := by
      exact_mod_cast h
    refine (Real.log_le_log (by exact_mod_cast hk) a1).trans ?_
    rw [Real.log_pow]
    have a2 : Real.log ((q0 D : ℝ) * (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde')) ≤ 23 * L := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
      linarith [hg 0, hg 1]
    calc _ ≤ ((depth0 D CF large₂.sc.b + 2 : ℕ) : ℝ) * (23 * L) := by gcongr
      _ ≤ _ := by gcongr
  have hcond1 : 1 ≤ szCond large₂ := by
    have e : szCond large₂ = (LevelStarExponents.condE D : ℝ) := by unfold szCond LevelStarExponents.condE; push_cast; rfl
    have h1 := (rPr_spec D).2
    have : LevelStarExponents.condE D ≠ 0 := fun z => h1 (by rw [z]; simp)
    rw [e]
    exact_mod_cast Nat.pos_of_ne_zero this
  have s1 : t ^ 11 ≤ Real.sqrt large₂.sc.b := by
    refine le_trans ?_ hcond
    calc t ^ 11 ≤ t ^ 150 := pow_le_pow_right₀ t1 (by norm_num)
      _ ≤ _ := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hcond1)
  have s2 : L / 2 ≤ Real.sqrt large₂.sc.b := by
    have : Real.sqrt large₂.sc.b = Real.exp (L / 2) := (Real.exp_half L).symm
    linarith [Real.add_one_le_exp (L / 2)]
  have s3 : t ^ 11 * (L / 2) ≤ large₂.sc.b := by
    calc _ ≤ Real.sqrt large₂.sc.b * Real.sqrt large₂.sc.b := by gcongr
      _ = _ := Real.mul_self_sqrt hb0.le
  rw [hb]
  calc _ ≤ 8 * (5 * t ^ 2) * ((50 * CF + 3) * (t ^ 9 * L) * (23 * L)) := by
        gcongr
    _ = 1840 * (50 * CF + 3) * (t ^ 11 * (L / 2)) * L := by ring
    _ ≤ _ := by gcongr

end GlobalTheory.SumCount.Pure

end

open GlobalTheory.SumCount GlobalTheory.SumSize
open GlobalTheory.SumCount.Pure Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.RowTest NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.T.pureTensorCountBound_of_cosetDepthBound : GlobalTheory.SumSize.DepthK → GlobalTheory.SumCount.PureK := by
  rintro ⟨a, h⟩
  refine ⟨max a 0, fun CF hCF => ?_⟩
  have hCF0 : 0 ≤ CF := le_of_max_le_right hCF
  obtain ⟨c, h⟩ := h CF (le_of_max_le_left hCF)
  refine ⟨max c (1840 * (50 * CF + 3)), fun ε C hC => ?_⟩
  obtain ⟨x, h⟩ := h ε C (le_of_max_le_left hC)
  refine ⟨x, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j k Φ β hβ τ hτ => ?_⟩
  have hd := (h D large₂ e hx Γ Pl0 T A Ks R F s ch i j k A.μ0 Φ β hβ).2
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hQ : R.toLevCh.Q A.μ0 = ∅ := Finset.eq_empty_of_forall_notMem fun PP hP => (hL.Q_ram A.μ0 PP).2 (Or.inl hP) (by
    rw [hL.xi_base]
    exact fun _ _ => rfl)
  have hk := hτ.1
  have h1 := card_support hL hτ
  set n := expDepth ch.S.toGridChoice A.μ0 Φ β
  have h2 := depth_le (G := ch.G) hk fun l hl => by
    haveI : (Ideal.span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime (by exact_mod_cast hl.ne_zero)).2
      (Nat.prime_iff_prime_int.1 hl)
    obtain ⟨Q, hQ1, hQ2⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 D.what₂.LL) (Ideal.span {(l : ℤ)})
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 D.what₂.LL)).injective_int]; exact bot_le)
    have hm : (l : 𝓞 D.what₂.LL) ∈ Q := by
      have : (l : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 D.what₂.LL)) := by rw [hQ2]; exact Ideal.mem_span_singleton_self _
      simpa using this
    refine hd ⟨Q, hQ1, fun z => ?_⟩ l hl hm fun PP hP => ?_
    · rw [z, Ideal.mem_bot] at hm
      exact hl.ne_zero (by exact_mod_cast hm)
    · rw [hQ] at hP
      exact absurd hP (Finset.notMem_empty _)
  have e1 : ch.sc.cDep = CF := by rw [j]
  have e2 : ch.sc.b = large₂.sc.b := by rw [j]
  rw [e1, e2] at h2
  have h3 := size_le large₂ s.size hCF0 hk h2
  have hC1 : 1840 * (50 * CF + 3) ≤ C := le_of_max_le_right hC
  have hC0 : 0 ≤ C := le_trans (by positivity) hC1
  have hb0 : 0 < large₂.sc.b := Real.exp_pos _
  have hb1 : 0 ≤ Real.log large₂.sc.b := by
    rw [Scale.b, Real.log_exp]
    exact Real.rpow_nonneg (zero_le_one.trans large₂.sc.one_lt_alt.le) _
  have hs : 0 ≤ sig ch.G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have hk' : (0 : ℝ) < n := by exact_mod_cast hk
  calc (τ.support.card : ℝ) ≤ (n : ℝ) ^ (8 * D.R.f * D.R.m * bigN D ^ 2) := by exact_mod_cast h1
    _ = Real.exp (D.R.m * (D.R.f * bigN D * (8 * (bigN D : ℝ) * Real.log n))) := by
      rw [← Real.exp_log (pow_pos hk' _), Real.log_pow]
      congr 1
      push_cast
      ring
    _ ≤ _ := by
      refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
      have h4 : 8 * (bigN D : ℝ) * Real.log n ≤ C * large₂.sc.b * Real.log large₂.sc.b := h3.trans (by gcongr)
      have h5 : 0 ≤ C * D.R.m * (bigN D : ℝ) ^ 2 * sig ch.G := by positivity
      have h6 := mul_le_mul_of_nonneg_left h4 (show (0 : ℝ) ≤ D.R.f * bigN D by positivity)
      unfold aOne
      linarith
