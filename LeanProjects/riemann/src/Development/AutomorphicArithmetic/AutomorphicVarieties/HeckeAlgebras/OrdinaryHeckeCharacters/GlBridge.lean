import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IwMemMul
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BranchingSmooth
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem br_loc : IsLocalRing 𝒪[k] := (inferInstance : IsDiscreteValuationRing 𝒪[k]).toIsLocalRing
attribute [local instance] br_loc

private theorem br_unif : valuation k (unif k : k) = uniformizer k := by
  obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
  have h0 : x ≠ 0 := by
    rintro rfl
    exact uniformizer_pos.ne (by simpa using hx)
  exact Classical.epsilon_spec (p := fun x : kˣ => valuation k (x : k) = uniformizer k) ⟨Units.mk0 x h0, hx⟩

private theorem br_pow (c : ℕ) (x : 𝒪[k]) :
    x ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c ↔ valuation k (x : k) ≤ uniformizer k ^ c := by
  have hI := Valuation.integer.integers (valuation k)
  let p : 𝒪[k] := ⟨unif k, (br_unif.trans_lt uniformizer_lt_one).le⟩
  have hp : valuation k (algebraMap 𝒪[k] k p) = uniformizer k := br_unif
  have e : IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {p} := by
    ext y
    rw [← IsLocalRing.residue_eq_zero_iff, GlobalTheory.StepData.residue_eq_zero_iff_lt, Ideal.mem_span_singleton,
      hI.dvd_iff_le, hp, le_uniformizer_iff]
    rfl
  rw [e, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hI.dvd_iff_le, map_pow, map_pow, hp]
  rfl

private theorem br_memKc {c : ℕ} {g : GL (Fin n) k} :
    g ∈ Kc k n c ↔ g ∈ KO k (Fin n) ∧ ∀ i j, valuation k ((g.val - 1) i j) ≤ uniformizer k ^ c := by
  have key : ∀ u : GL (Fin n) 𝒪[k],
      u ∈ (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c))).ker ↔
      ∀ i j, valuation k (((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u).val - 1) i j) ≤ uniformizer k ^ c := by
    intro u
    rw [MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
    refine forall₂_congr fun i j => ?_
    have e : ((1 : GL (Fin n) (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ c)).val) i j =
        Ideal.Quotient.mk _ ((1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j) := by
      simp only [Units.val_one, Matrix.one_apply]; split_ifs <;> simp
    rw [e]
    refine (Ideal.Quotient.eq.trans (br_pow c _)).trans (iff_of_eq ?_)
    congr 2
    simp only [Matrix.sub_apply, Matrix.one_apply]; split_ifs <;> simp <;> rfl
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, rfl⟩, (key u).1 hu⟩
  · rintro ⟨⟨u, rfl⟩, hu⟩
    exact ⟨u, (key u).2 hu, rfl⟩

private theorem br_Kc_anti {c d : ℕ} (h : c ≤ d) : Kc k n d ≤ Kc k n c := fun _ hg =>
  br_memKc.2 ⟨(br_memKc.1 hg).1, fun i j => ((br_memKc.1 hg).2 i j).trans
    (pow_le_pow_right_of_le_one' uniformizer_lt_one.le h)⟩

private theorem br_Kc_open (c : ℕ) : IsOpen (Kc k n c : Set (GL (Fin n) k)) := by
  have e : (Kc k n c : Set (GL (Fin n) k)) = (KO k (Fin n) : Set (GL (Fin n) k)) ∩
      ⋂ i, ⋂ j, (fun g : GL (Fin n) k => (g.val - 1) i j) ⁻¹' {x | valuation k x ≤ uniformizer k ^ c} := by
    ext g; simp only [SetLike.mem_coe, br_memKc, Set.mem_iInter, Set.mem_inter_iff]; rfl
  rw [e]
  refine GlobalTheory.SplitFlip.isOpen_KO.inter <|
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.preimage ?_ ?_
  · have := Units.continuous_val (M := Matrix (Fin n) (Fin n) k)
    fun_prop
  · have h0 : (valuation k).restrict ((unif k : k) ^ c) ≠ 0 := by simp
    simpa only [Valuation.restrict_le_iff, map_pow (valuation k), br_unif] using Valuation.isOpen_closedBall h0

private theorem br_basis (U : Subgroup (GL (Fin n) k)) (hU : IsOpen (U : Set (GL (Fin n) k))) :
    ∃ c, Kc k n c ≤ U := by
  refine exists_subset_nhds_of_isCompact' (V := fun c => (Kc k n c : Set (GL (Fin n) k)))
    (directed_of_isDirected_le fun _ _ h => br_Kc_anti h)
    (fun c => GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ (br_Kc_open c))
      fun g hg => (br_memKc.1 hg).1) (fun c => Subgroup.isClosed_of_isOpen _ (br_Kc_open c)) fun g hg => ?_
  have : g = 1 := by
    ext i j
    by_contra h
    have h0 : valuation k ((g.val - 1) i j) ≠ 0 := by
      simpa [sub_eq_zero] using h
    obtain ⟨c, hc⟩ := exists_pow_lt₀ (uniformizer_lt_one (R := k)) (Units.mk0 _ h0)
    exact hc.not_ge ((br_memKc.1 (Set.mem_iInter.1 hg c)).2 i j)
  rw [this]
  exact hU.mem_nhds (one_mem U)

private theorem br_memN {g : GL (Fin n) k} :
    g ∈ (glIwa k n).N ↔ g ∈ unipB k (Fin n) ∧ ∀ i j, valuation k (g.val i j) ≤ 1 := by
  refine ⟨fun h => ⟨h.1, GlobalTheory.StepData.intM_of_mem_KO h.2⟩, fun ⟨h, h1⟩ => ⟨h, ?_⟩⟩
  obtain ⟨h2, h3⟩ := (mem_unipB k).1 h
  let A : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨g.val i j, h1 i j⟩
  have hA : A.det = 1 := by
    rw [Matrix.det_of_upperTriangular (M := A) fun i j hij => Subtype.ext (h2 i j hij)]
    exact Finset.prod_eq_one fun i _ => Subtype.ext (h3 i)
  exact ⟨Matrix.GeneralLinearGroup.mk'' A (by rw [hA]; exact isUnit_one), Units.ext rfl⟩

private theorem br_memNconj (a : Fin n → ℤ) {g : GL (Fin n) k} :
    g ∈ (glIwa k n).Nconj (upow k n a) ↔
      g ∈ unipB k (Fin n) ∧ ∀ i j, valuation k (g.val i j) ≤ uniformizer k ^ (a i - a j) := by
  have e : (MulAut.conj (upow k n a)).symm g =
      diagT k (Fin n) (fun i => unif k ^ a i)⁻¹ * g * (diagT k (Fin n) (fun i => unif k ^ a i)⁻¹)⁻¹ := by
    simp [upow]
  have e' : g = diagT k (Fin n) (fun i => unif k ^ a i) * (diagT k (Fin n) (fun i => unif k ^ a i)⁻¹ * g * (diagT k (Fin n) (fun i => unif k ^ a i)⁻¹)⁻¹) * (diagT k (Fin n) (fun i => unif k ^ a i))⁻¹ := by
    rw [map_inv]; group
  rw [Iwa.Nconj, Subgroup.mem_map_equiv, e, br_memN]
  refine and_congr ⟨fun h => e' ▸ GlobalTheory.IwahoriTraceProof.conj_mem_unipB _ h, GlobalTheory.IwahoriTraceProof.conj_mem_unipB _⟩
    (forall₂_congr fun i j => ?_)
  rw [← map_inv, inv_inv, GlobalTheory.IwahoriTraceProof.diag_mul_mul_diag, map_mul, Pi.inv_apply, ← _root_.zpow_neg,
    ← _root_.zpow_add, Units.val_zpow_eq_zpow_val, map_zpow₀, br_unif,
    show -a i + a j = -(a i - a j) by ring, _root_.zpow_neg, inv_mul_le_iff₀ (zpow_pos uniformizer_pos _), mul_one]

private theorem br_memNm {c : ℕ} {g : GL (Fin n) k} :
    g ∈ (glIwa k n).Nm c ↔ g ∈ unipBLower k (Fin n) ∧ g ∈ Kc k n (c + 1) := by
  refine and_congr ?_ Iff.rfl
  rw [← inv_mem_iff (H := unipBLower k (Fin n)), GlobalTheory.IwahoriTraceProof.mem_unipBLower]
  refine (mem_unipB k).trans ?_
  exact ⟨fun h => ⟨fun i j hij => h.1 j i hij, h.2⟩, fun h => ⟨fun i j hij => h.1 j i hij, h.2⟩⟩

private theorem br_memT {g : GL (Fin n) k} :
    g ∈ (glIwa k n).T ↔ ∃ t ∈ torusO k (Fin n), diagT k (Fin n) t = g := Iff.rfl

private theorem br_smooth {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (h : GlobalTheory.PRep.IsSmooth π) : (glIwa k n).Smooth π :=
  _root_.UpperTheory.Reformulated.B.BranchingSmooth.br_smooth π h

private theorem br_Kone : Kc k n 1 = KOne k (Fin n) := by
  ext g
  rw [br_memKc, pow_one]
  simp only [le_uniformizer_iff]
  exact ⟨fun h => GlobalTheory.StepData.mem_KOne.2 h.2, fun h => ⟨GlobalTheory.StepData.KOne_le_KO h, GlobalTheory.StepData.mem_KOne.1 h⟩⟩

private theorem br_Iw : (glIwa k n).Iw 0 = iwahori k (Fin n) := by
  apply le_antisymm
  · refine sup_le (sup_le (fun g hg => (GlobalTheory.IwahoriTraceProof.mem_unipO_iff hg.1).2 hg) ?_) fun g hg => ?_
    · rintro _ ⟨t, ht, rfl⟩
      exact diagT_mem_iwahori ht
    · exact KOne_le_iwahori k _ (br_Kone (k := k) (n := n) ▸ hg.2)
  · intro g hg
    obtain ⟨u, hu, d, hd, y, hy, rfl⟩ := GlobalTheory.IwahoriTraceProof.iwahori_factorisation hg
    exact (iwMem _ _ 0 _).1.2 ⟨u, hu, _, ⟨d, hd, rfl⟩, y, br_memNm.2 ⟨hy.1, br_Kone (k := k) (n := n) ▸ hy.2⟩, rfl⟩

private theorem br_K_le (c : ℕ) : Kc k n (c + 1) ≤ (glIwa k n).I1 c := by
  intro g hg
  have hg1 : g ∈ iwahori k (Fin n) :=
    KOne_le_iwahori k _ (br_Kone (k := k) (n := n) ▸ br_Kc_anti (Nat.le_add_left 1 c) hg)
  obtain ⟨u, hu, d, hd, y, hy, e⟩ := GlobalTheory.IwahoriTraceProof.iwahori_factorisation hg1
  have hdK : diagT k (Fin n) d ∈ KO k (Fin n) := iwahori_le_KO k _ (diagT_mem_iwahori hd)
  have hw := GlobalTheory.StepData.intM_of_mem_KO (mul_mem hu.2 hdK)
  obtain ⟨u2, u3⟩ := (mem_unipB k).1 hu.1
  obtain ⟨y2, y3⟩ := GlobalTheory.IwahoriTraceProof.mem_unipBLower.1 (inv_mem hy.1)
  have e1 : (y⁻¹).val - (u * diagT k (Fin n) d).val = ((g⁻¹).val - 1) * (u * diagT k (Fin n) d).val := by
    rw [Matrix.sub_mul, Matrix.one_mul, ← Units.val_mul, e]
    congr 2
    group
  have key : ∀ i j, valuation k ((y⁻¹).val i j - u.val i j * d j) ≤ uniformizer k ^ (c + 1) := by
    intro i j
    have e2 := congrFun (congrFun e1 i) j
    rw [Matrix.sub_apply, Units.val_mul, val_diagT, Matrix.mul_diagonal, ← val_diagT, ← Units.val_mul] at e2
    rw [e2, Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    exact (mul_le_of_le_one_right' (hw l j)).trans ((br_memKc.1 (inv_mem hg)).2 i l)
  refine (iwMem _ _ c _).2.1.2 ⟨u, hu, _, ⟨⟨d, hd, rfl⟩, br_memKc.2 ⟨hdK, fun i j => ?_⟩⟩, y,
    br_memNm.2 ⟨hy.1, inv_mem_iff.1 (br_memKc.2 ⟨inv_mem (GlobalTheory.StepData.KOne_le_KO hy.2), fun i j => ?_⟩)⟩, e⟩
  · rw [val_diagT]
    by_cases hij : i = j
    · subst hij
      have := key i i
      rw [y3, u3, one_mul, Valuation.map_sub_swap] at this
      simpa using this
    · simp [hij]
  · rcases lt_trichotomy i j with hij | rfl | hij
    · simp only [Matrix.sub_apply, y2 i j hij, Matrix.one_apply_ne hij.ne, sub_self, map_zero, zero_le]
    · simp only [Matrix.sub_apply, y3 i, Matrix.one_apply_eq, sub_self, map_zero, zero_le]
    · have := key i j
      rw [u2 i j hij, zero_mul] at this
      rwa [Matrix.sub_apply, Matrix.one_apply_ne hij.ne']

private theorem iwahori_first_le_maximal_compact (c : ℕ) : (glIwa k n).I1 c ≤ KO k (Fin n) :=
  sup_le (sup_le (fun _ hg => hg.2) fun _ hg => (br_memKc.1 hg.2).1) fun _ hg => (br_memKc.1 hg.2).1

private theorem iwahori_z_eq_product : (glIwa k n).z = ((List.range n).map (al k n)).prod := by
  have key : ∀ m : ℕ, ((List.range m).map (al k n)).prod = upow k n fun i => ((m - 1 - i : ℕ) : ℤ) := by
    intro m
    induction m with
    | zero =>
      rw [upow, List.range_zero, List.map_nil, List.prod_nil, ← (diagT k (Fin n)).map_one]
      congr 1
      funext i
      simp
    | succ m ih =>
      rw [List.range_succ, List.map_append, List.prod_append, ih, List.map_singleton, List.prod_singleton, al, upow, upow,
        upow, ← map_mul]
      congr 1
      funext i
      rw [Pi.mul_apply, ← _root_.zpow_add]
      congr 1
      split_ifs <;> omega
  rw [key]
  show upow k n _ = _
  congr 1
  funext i
  have := i.2
  omega

private theorem iwahori_torus_product_form (t : (glIwa k n).T) : ∃ y : Fin n → Uo k,
    (t : GL (Fin n) k) = (List.ofFn fun i => (eT k n i (y i) : GL (Fin n) k)).prod ∧
      ∀ c, (t : GL (Fin n) k) ∈ (glIwa k n).Tc c → ∀ i, (y i : kˣ) ∈ Uc k (c + 1) := by
  obtain ⟨_, d, hd, rfl⟩ := t
  refine ⟨fun i => ⟨d i, hd i⟩, ?_, fun c hc i => ?_⟩
  · show diagT k (Fin n) d = (List.ofFn fun i => diagT k (Fin n) (Pi.mulSingle i (d i))).prod
    rw [show (fun i => diagT k (Fin n) (Pi.mulSingle i (d i))) = diagT k (Fin n) ∘ fun i => Pi.mulSingle i (d i) from rfl,
      ← List.map_ofFn, ← map_list_prod, List.prod_ofFn, Finset.univ_prod_mulSingle]
  · have h := (br_memKc.1 hc.2).2 i i
    let u : 𝒪[k]ˣ := ⟨⟨d i, (hd i).le⟩, ⟨((d i)⁻¹ : kˣ), (inv_mem hd i).le⟩,
      Subtype.ext (d i).mul_inv, Subtype.ext (d i).inv_mul⟩
    refine ⟨u, ?_, Units.ext rfl⟩
    refine Units.ext (show Ideal.Quotient.mk _ u.val = Ideal.Quotient.mk _ 1 from ?_)
    refine Ideal.Quotient.eq.2 ((br_pow _ _).2 ?_)
    simpa [val_diagT] using h

private theorem br_index (j : ℕ) (hj : j ≤ n) :
    ((glIwa k n).Nconj (al k n j)).relIndex (glIwa k n).N = Nat.card 𝓀[k] ^ (j * (n - j)) := by
  have hint : ∀ x : BlockIx n j → 𝒪[k], unip (fun p => (x p : k)) ∈ (glIwa k n).N := by
    intro x
    refine br_memN.2 ⟨(mem_unipB k).2 ⟨fun a b hab => ?_, fun a => ?_⟩, fun a b => ?_⟩
    · have : (b : ℕ) < a := hab
      show (1 + nilM _ : Matrix _ _ k) a b = 0
      simp only [nilM, Matrix.add_apply, Matrix.of_apply]
      rw [dif_neg (fun h => by omega), add_zero, Matrix.one_apply_ne hab.ne']
    · show (1 + nilM _ : Matrix _ _ k) a a = 1
      simp only [nilM, Matrix.add_apply, Matrix.of_apply]
      rw [dif_neg (fun h => by omega), add_zero, Matrix.one_apply_eq]
    · show (1 + nilM _ : Matrix _ _ k) a b ∈ 𝒪[k]
      refine add_mem (GlobalTheory.StepData.intM_one a b) ?_
      simp only [nilM, Matrix.of_apply]
      split_ifs
      exacts [(x _).2, zero_mem _]
  have hmem : ∀ g ∈ (glIwa k n).N, g ∈ (glIwa k n).Nconj (al k n j) ↔
      ∀ p : BlockIx n j, valuation k (g.val p.1.1 p.1.2) < 1 := by
    intro g hg
    obtain ⟨h1, h2⟩ := br_memN.1 hg
    rw [al, br_memNconj]
    refine ⟨fun h p => ?_, fun h => ⟨h1, fun a b => ?_⟩⟩
    · have := h.2 p.1.1 p.1.2
      rwa [if_pos p.2.1, if_neg p.2.2.not_gt, sub_zero, zpow_one, le_uniformizer_iff] at this
    · split_ifs with ha hb hb
      · simpa using h2 a b
      · simpa [le_uniformizer_iff] using h ⟨(a, b), ha, not_lt.1 hb⟩
      · rw [((mem_unipB k).1 h1).1 a b (show (b : ℕ) < a by omega), map_zero]
        exact zero_le
      · simpa using h2 a b
  let f : Multiplicative (BlockIx n j → 𝒪[k]) →* GL (Fin n) k :=
    MonoidHom.mk' (fun x => unip fun p => (x.toAdd p : k)) fun x y => unip_add _ _
  let r : Multiplicative (BlockIx n j → 𝒪[k]) →* Multiplicative (BlockIx n j → 𝓀[k]) :=
    AddMonoidHom.toMultiplicative ((IsLocalRing.residue 𝒪[k]).toAddMonoidHom.compLeft _)
  have hle : f.range ≤ (glIwa k n).N := by
    rintro _ ⟨x, rfl⟩
    exact hint _
  have h1 : ((glIwa k n).Nconj (al k n j)).comap f = r.ker := by
    ext x
    rw [Subgroup.mem_comap, hmem _ (hle ⟨x, rfl⟩), MonoidHom.mem_ker]
    refine Iff.trans (forall_congr' fun p => ?_) (funext_iff (f := (r x).toAdd) (g := 0)).symm
    refine Iff.trans (iff_of_eq ?_) (GlobalTheory.StepData.residue_eq_zero_iff_lt (x.toAdd p)).symm
    congr 2
    show (1 + nilM _ : Matrix _ _ k) _ _ = _
    simp only [nilM, Matrix.add_apply, Matrix.of_apply]
    rw [dif_pos p.2, Matrix.one_apply_ne (fun h => by have := p.2; rw [h] at this; omega), zero_add]
  have h2 : r.range = ⊤ := by
    refine MonoidHom.range_eq_top.2 fun y => ?_
    choose x hx using fun p => IsLocalRing.residue_surjective (y.toAdd p)
    exact ⟨.ofAdd x, funext hx⟩
  have h3 : Nat.card (BlockIx n j) = j * (n - j) := by
    let e : BlockIx n j ≃ Fin j × Fin (n - j) :=
      { toFun := fun p => (⟨p.1.1, p.2.1⟩, ⟨p.1.2 - j, by have := p.2.2; have := p.1.2.2; omega⟩)
        invFun := fun q => ⟨(⟨q.1, by have := q.1.2; omega⟩, ⟨j + q.2, by have := q.2.2; omega⟩), q.1.2, Nat.le_add_right _ _⟩
        left_inv := fun p => by
          have := p.2.2
          ext
          · rfl
          · show j + (p.1.2 - j) = p.1.2
            omega
        right_inv := fun q => by
          ext
          · rfl
          · show j + q.2 - j = q.2
            omega }
    rw [Nat.card_congr e]
    simp
  have h4 : ((glIwa k n).Nconj (al k n j)).relIndex f.range = ((glIwa k n).Nconj (al k n j)).relIndex (glIwa k n).N := by
    refine Nat.card_congr (Equiv.ofBijective (Subgroup.quotientSubgroupOfEmbeddingOfLE _ hle)
      ⟨Function.Embedding.injective _, fun q => ?_⟩)
    induction q using QuotientGroup.induction_on with
    | H x =>
    obtain ⟨x, hx⟩ := x
    let B : Matrix (Fin n) (Fin n) k := nilM fun p : BlockIx n j => x.val p.1.1 p.1.2
    have hB : GlobalTheory.StepData.IntM B := fun a b => by
      simp only [B, nilM, Matrix.of_apply]
      split_ifs
      exacts [(br_memN.1 hx).2 _ _, zero_mem _]
    have hY := hB.mul (GlobalTheory.StepData.intM_of_mem_KO (inv_mem hx).2)
    let y : BlockIx n j → 𝒪[k] := fun p => ⟨_, hY p.1.1 p.1.2⟩
    have e : nilM (fun p => (y p : k)) = B * (x⁻¹).val := by
      ext a b
      simp only [nilM, Matrix.of_apply]
      split_ifs with h
      · rfl
      · rw [Matrix.mul_apply]
        refine (Finset.sum_eq_zero fun l _ => ?_).symm
        by_cases hl : (a : ℕ) < j ∧ j ≤ (l : ℕ)
        · rw [((mem_unipB k).1 (inv_mem hx).1).1 l b (show (b : ℕ) < l by omega), mul_zero]
        · simp only [B, nilM, Matrix.of_apply, dif_neg hl, zero_mul]
    refine ⟨((⟨f (.ofAdd y), _, rfl⟩ : f.range) : _ ⧸ _), ?_⟩
    rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf,
      hmem _ (Subtype.mem _)]
    intro p
    have e2 : ((f (.ofAdd y))⁻¹ * x).val = x.val - B := by
      show (1 - nilM (fun p => (y p : k))) * x.val = _
      rw [e, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    show valuation k (((f (.ofAdd y))⁻¹ * x).val _ _) < 1
    rw [e2]
    simp only [B, nilM, Matrix.sub_apply, Matrix.of_apply, dif_pos p.2, sub_self, map_zero, zero_lt_one]
  rw [← h4, ← Subgroup.index_comap, h1, Subgroup.index_ker, h2, Subgroup.card_top, ← h3]
  exact Nat.card_fun

end SlopeTestRemainingChoices

theorem UpperTheory.V.Hi.glBridge :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), ((glIwa k n).jacKer π = GlobalTheory.PRep.twKer π (unipB k (Fin n)) 1) ∧ (GlobalTheory.PRep.IsSmooth π → (glIwa k n).Smooth π) ∧ (∀ c, IsOpen ((glIwa k n).I1 c : Set (GL (Fin n) k)) ∧ IsCompact ((glIwa k n).I1 c : Set (GL (Fin n) k))) ∧ (∀ U : Subgroup (GL (Fin n) k), IsOpen (U : Set (GL (Fin n) k)) → ∃ c, Kc k n c ≤ U) ∧ (∀ c, Kc k n (c + 1) ≤ (glIwa k n).I1 c) ∧ (glIwa k n).Iw 0 = iwahori k (Fin n) ∧ valuation k (unif k : k) = uniformizer k ∧ (∀ j ≤ n, ((glIwa k n).Nconj (al k n j)).relIndex (glIwa k n).N = Nat.card 𝓀[k] ^ (j * (n - j))) ∧ (glIwa k n).z = ((List.range n).map (al k n)).prod ∧ ∀ t : (glIwa k n).T, ∃ y : Fin n → Uo k, (t : GL (Fin n) k) = (List.ofFn fun i => (eT k n i (y i) : GL (Fin n) k)).prod ∧ ∀ c, (t : GL (Fin n) k) ∈ (glIwa k n).Tc c → ∀ i, (y i : kˣ) ∈ Uc k (c + 1) := by
  intro k _ _ _ _ n V _ _ π
  refine ⟨?_, br_smooth π, fun c => ?_, br_basis, br_K_le, br_Iw, br_unif, br_index, iwahori_z_eq_product, iwahori_torus_product_form⟩
  · refine congrArg (Submodule.span ℂ) (Set.ext fun w => ⟨?_, ?_⟩)
    · rintro ⟨x, hx, v, rfl⟩
      exact ⟨⟨x, hx⟩, v, by simp⟩
    · rintro ⟨x, v, rfl⟩
      exact ⟨x, x.2, v, by simp⟩
  · have ho := Subgroup.isOpen_mono (br_K_le c) (br_Kc_open (k := k) (n := n) (c + 1))
    exact ⟨ho, GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) (iwahori_first_le_maximal_compact c)⟩
