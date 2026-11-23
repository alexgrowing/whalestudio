import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LogVandermondeBounds.HookGammaAmgmMultinomialBounds
import Formalism.GL3MeanSquares.GenusMassVolumeResults
import Formalism.GL3MeanSquares.GlobalBoundRefinementResults
import Formalism.HermitianLattices.FinalMass
import Formalism.GL3MeanSquares.FinalB
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces

noncomputable section

namespace Formalism.MainNotions.StandardLattice

open NumberField Formalism.BasicNotions Finset

theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  have hb := (factEmb D.R D.host).1
  have h1 : Nat.card (D.R.GG) = Nat.card (D.host.E →+* ℂ) := Nat.card_congr (Equiv.ofBijective _ hb)
  have h2 : Nat.card (D.host.E →+* ℂ) = Module.finrank ℚ D.host.E := by
    rw [Nat.card_eq_fintype_card]; exact NumberField.Embeddings.card D.host.E ℂ
  have h3 := (factCardPsi D.R D.host).1
  have h4 : Nat.card (D.R.GG) = 4 * D.R.ord := D.R.natCard_GG
  rw [← h2, ← h1, h4]
  show 4 * D.R.ord = 2 * (2 * D.R.ord)
  ring

theorem fDeg_host (D : D7) : Formalism.HermitianLatticesTheory.fDeg D.host.E = D.R.f := by
  let _ := D.host.cmStar
  have : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  have h1 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := D.host.E)
  have h2 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank D.host.E
  have h3 : NumberField.InfinitePlace.nrRealPlaces D.host.E = 0 := by
    rw [NumberField.nrRealPlaces_eq_zero_iff]; infer_instance
  have h4 := finrank_host D
  unfold Formalism.HermitianLatticesTheory.fDeg
  omega

theorem vInv_host (D : D7) : Formalism.HermitianLatticesTheory.vInv D.host.E = D.host.v := by
  unfold Formalism.HermitianLatticesTheory.vInv Host.v Host.rdE
  rw [fDeg_host, finrank_host]
  push_cast
  rfl

theorem zetaR_eq (M : ℕ) : zetaR M = Formalism.LogVandermondeBounds.StandardLattice.zetaR M := rfl

theorem cmField_unramified_massIdentity : LogLValueZetaBound := by
  intro K _ _ _ hK M hM
  exact (Formalism.HermitianLattices.GlobalBoundRefinements.log_l_value_field_bound K hK M hM).2.2

theorem massIdentity_holds (D : D7) : gram_det_kernel_dual_lattice D := by
  let _ := D.host.cmStar
  intro M hM
  have h := cmField_unramified_massIdentity D.host.E D.sp.cm.cmUnram M hM
  rwa [fDeg_host] at h

theorem lVal_pos (D : D7) (M : ℕ) (hM : 2 ≤ M) :
    letI := D.host.cmStar; 0 < Formalism.HermitianLatticesTheory.lValEta D.host.E M := by
  let _ := D.host.cmStar
  exact (Formalism.HermitianLattices.GlobalBoundRefinements.log_l_value_field_bound D.host.E D.sp.cm.cmUnram M hM).2.1

end Formalism.MainNotions.StandardLattice

namespace Formalism.MainNotions.StandardLattice

open NumberField Formalism.BasicNotions Finset

theorem levelPartB_holds (D : D7) : Conclusion4b D := by
  have h := Formalism.LogVandermondeBounds.StandardLattice.blockDimensionIdentities D.R.k D.R.m D.R.rS D.R.r D.R.two_le_m D.R.m_even rfl
    (by have := D.R.rS_two; have := D.R.r_eq; omega)
  obtain ⟨h1, h2, -, -, h5⟩ := h
  refine ⟨by have := D.R.rS_two; have := D.R.r_eq; omega, ?_, h5⟩
  have : dimN D.R.k D.R.m = ((range D.R.r ×ˢ range D.R.r).filter
      (fun p : ℕ × ℕ => p.1 < p.2 ∧ (fun i => if i < D.R.rS then i else if i < D.R.rS + D.R.k + 1 then D.R.rS else i - D.R.k) p.1 ≠
        (fun i => if i < D.R.rS then i else if i < D.R.rS + D.R.k + 1 then D.R.rS else i - D.R.k) p.2)).card := rfl
  rw [this]
  exact h2

theorem levelPartE_holds (D : D7) : LevelIndexAtPlace D := by
  intro u v φ hφ
  have h := Formalism.LogVandermondeBounds.StandardLattice.cardStabilizerVector ((D.mem u).A.Fv v) D.R.k φ hφ
  rw [(D.mem u).A.card_Fv v] at h
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  convert h.symm using 2

theorem card_GL_subtype_eq_card_matrix {F : Type} [Field F] {n : ℕ} (P : Matrix (Fin n) (Fin n) F → Prop)
    (hP : ∀ A, P A → A.det = 1) :
    Nat.card {A : GL (Fin n) F // P (A : Matrix (Fin n) (Fin n) F)} = Nat.card {A : Matrix (Fin n) (Fin n) F // P A} := by
  let e : {A : GL (Fin n) F // P (A : Matrix (Fin n) (Fin n) F)} ≃ {A : Matrix (Fin n) (Fin n) F // P A} :=
    { toFun := fun A => ⟨(A.1 : Matrix (Fin n) (Fin n) F), A.2⟩
      invFun := fun A => ⟨Matrix.nonsingInvUnit A.1 (by rw [hP A.1 A.2]; exact isUnit_one), A.2⟩
      left_inv := fun A => Subtype.ext (Units.ext rfl)
      right_inv := fun A => rfl }
  exact Nat.card_congr e

theorem det_eq_one_of_unitriangular {F : Type} [Field F] {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (h : IsUnitri A) : A.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => h.1 i j hij)]
  simp [h.2]

def RowLevCard : Prop :=
  ∀ g k m : ℕ, g.Prime → 2 ≤ m → Even m →
    Nat.card {A : GL (Fin (k + m - 1)) (ZMod g) // IsRowLev k (m / 2 - 1) (A : Matrix (Fin (k + m - 1)) (Fin (k + m - 1)) (ZMod g))} =
      g ^ (((k + m - 1) ^ 2 - (k + 1) ^ 2 - 2 * (m / 2 - 1)) / 2) * g ^ (k * (k - 1) / 2)

theorem levelRowCard_of_card (hR : RowLevCard) (D : D7) : Conclusion4a D := by
  intro i hg
  have : Fact (D.host.g i).Prime := ⟨D.host.g_prime i⟩
  have hc : Fintype.card (ZMod (D.host.g i)) = D.host.g i := ZMod.card _
  obtain ⟨⟨θ, hθ1, hθ2, h1⟩, ⟨θ', hθ1', hθ2', h2⟩⟩ :=
    Formalism.HermitianLattices.GenusMassVolumes.local_index_formula (ZMod (D.host.g i)) D.R.k D.R.m D.R.two_le_m D.R.m_even (by rw [hc]; exact hg)
  rw [hc] at h1 h2
  have hgpos : (0 : ℝ) < (D.host.g i : ℝ) := by exact_mod_cast (D.host.g_prime i).pos
  have e1 : idxColLoc (D.host.g i) D.R.k = (D.host.g i : ℝ) ^ (D.R.k * (D.R.k + 1) / 2) * θ := by
    rw [← h1]
    unfold idxColLoc idxLoc
    rw [card_GL_subtype_eq_card_matrix _ det_eq_one_of_unitriangular]
    have := Formalism.LogVandermondeBounds.StandardLattice.cardUnitriangular (ZMod (D.host.g i)) D.R.k
    rw [hc] at this
    have h3 : Nat.card {A : Matrix (Fin D.R.k) (Fin D.R.k) (ZMod (D.host.g i)) // IsUnitri A} =
        D.host.g i ^ (D.R.k * (D.R.k - 1) / 2) := this
    rw [h3, Nat.card_eq_fintype_card]
    push_cast
    rfl
  have e2 : idxRowLoc (D.host.g i) D.R.k D.R.m =
      (D.host.g i : ℝ) ^ ((D.R.r ^ 2 + 3 * D.R.k + 1 + 2 * D.R.rS) / 2) * θ' := by
    have h2' : _ = (D.host.g i : ℝ) ^ ((D.R.r ^ 2 + 3 * D.R.k + 1 + 2 * D.R.rS) / 2) * θ' := h2
    rw [← h2']
    unfold idxRowLoc idxLoc
    rw [hR _ _ _ (D.host.g_prime i) D.R.two_le_m D.R.m_even, Nat.card_eq_fintype_card]
    push_cast
    rfl
  have p1 : (0 : ℝ) < (D.host.g i : ℝ) ^ (D.R.k * (D.R.k + 1) / 2) := pow_pos hgpos _
  have p2 : (0 : ℝ) < (D.host.g i : ℝ) ^ ((D.R.r ^ 2 + 3 * D.R.k + 1 + 2 * D.R.rS) / 2) := pow_pos hgpos _
  rw [e1, e2]
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

theorem hostDegree_of_finrank (D : D7) (hfin : Module.finrank ℚ D.host.E = 2 * D.R.f) : PrimeSumLogBound D := by
  let _ := D.host.cmStar
  intro g hg A _ hA hA1
  let b := (D.sp.X 0).frame
  let φ : ((D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) →* Matrix (Fin (D.sp.X 0).rank) (Fin (D.sp.X 0).rank) D.host.E :=
    ((LinearMap.toMatrixAlgEquiv b : _ ≃ₐ[D.host.E] _) : _ →* _).comp
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom)
  have hinj : Function.Injective φ := by
    intro x y hxy
    have : (x : (D.sp.X 0).V →ₗ[D.host.E] (D.sp.X 0).V) = y := (LinearMap.toMatrixAlgEquiv b).injective hxy
    exact LinearEquiv.toLinearMap_injective this
  have h := Formalism.LogVandermondeBounds.StandardLattice.primeOrderFinrank D.host.E (D.sp.X 0).rank g (φ A) hg
    (by rw [← map_pow, hA, map_one]) (fun h => hA1 (hinj (by rw [h, map_one])))
  rw [hfin, D.sp.rank0] at h
  exact h

theorem levelDimension_of_admissible (D : D7) (Lv : LevelData D) (h17 : adm17 D Lv) (hp : Conclusion4p D Lv) : SmallOrderPrimeLogSumBound D Lv := by
  let _ := D.host.cmStar
  intro hg u c
  have h := h17 hg u (hp u) c
  have hnt : Nontrivial (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    (RestrictedProduct.evalRingHom (fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletion D.host.F) (Lv u).w1).domain_nontrivial
  have key : ∀ γ : (D.mem u).C.stab 0 c, (Lv u).stabI c γ = 1 := by
    intro γ
    have h1 := ((Lv u).stabI_range c ((Lv u).stabI c γ).1 ((Lv u).stabI c γ).2).1 ⟨γ, rfl⟩
    have h2 : Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F))
        ((Lv u).stabI c γ).1 ∈
        Formalism.UG.ratPts D.sp.cm.sig D.sp.gram0 (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
      Subgroup.mem_map.2 ⟨_, ((Lv u).stabI c γ).2, rfl⟩
    have h3 := (Subgroup.mem_bot.1 (h ▸ Subgroup.mem_inf.2 ⟨h2, h1⟩))
    apply Subtype.ext
    exact Formalism.UG.P.UG_inclusion_injective _ _ _ _ hnt (h3.trans (map_one _).symm)
  exact ⟨fun a b => (Lv u).stabI_inj c ((key a).trans (key b).symm)⟩

theorem card_matrices_with_free_support (F : Type) [Field F] [Fintype F] (n : ℕ) (S : Fin n × Fin n → Prop) [DecidablePred S] :
    Nat.card {A : Matrix (Fin n) (Fin n) F // ∀ i j, ¬ S (i, j) → A i j = if i = j then 1 else 0} =
      Fintype.card F ^ Nat.card {p : Fin n × Fin n // S p} := by
  let e : {A : Matrix (Fin n) (Fin n) F // ∀ i j, ¬ S (i, j) → A i j = if i = j then 1 else 0} ≃
      ({p : Fin n × Fin n // S p} → F) :=
    { toFun := fun A p => A.1 p.1.1 p.1.2
      invFun := fun f => ⟨Matrix.of fun i j => if h : S (i, j) then f ⟨(i, j), h⟩ else if i = j then 1 else 0,
        fun i j h => by simp [h]⟩
      left_inv := fun A => by
        ext i j
        by_cases h : S (i, j)
        · simp [h]
        · simp [h, A.2 i j h]
      right_inv := fun f => by
        funext p
        obtain ⟨⟨i, j⟩, hp⟩ := p
        simp [hp] }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := F)]

def IsFreePosition (k rS n : ℕ) (p : Fin n × Fin n) : Prop :=
  Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.bb k rS p.1.val < Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.bb k rS p.2.val ∨
    (rS ≤ p.1.val ∧ p.1.val < p.2.val ∧ p.2.val < rS + k)

instance (k rS n : ℕ) : DecidablePred (IsFreePosition k rS n) := fun _ => by unfold IsFreePosition; infer_instance

theorem isLevel_iff_free_support (k rS n : ℕ) {F : Type} [Zero F] [One F] (A : Matrix (Fin n) (Fin n) F) :
    IsRowLev k rS A ↔ ∀ i j, ¬ IsFreePosition k rS n (i, j) → A i j = if i = j then 1 else 0 := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩ i j hS
    by_cases hij : i = j
    · subst hij; simp [h2]
    · rw [if_neg hij]
      have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
      unfold IsFreePosition Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.bb at hS
      simp only at hS
      by_cases c1 : blk rS k j.val < blk rS k i.val
      · exact h1 i j c1
      · by_cases c2 : j < i
        · refine h3 i j ?_ c2
          have c2' : j.val < i.val := c2
          unfold blk at c1 ⊢
          split_ifs at c1 ⊢ <;> omega
        · have c2' : ¬ j.val < i.val := c2
          refine h4 i j ?_ hij ?_
          · unfold blk at c1
            split_ifs at c1 hS <;> omega
          · unfold blk at c1 ⊢
            split_ifs at c1 hS ⊢ <;> omega
  · intro h
    refine ⟨fun i j c => ?_, fun i => ?_, fun i j c c2 => ?_, fun i j c hij c2 => ?_⟩
    · have hne : i ≠ j := by rintro rfl; exact lt_irrefl _ c
      rw [h i j ?_, if_neg hne]
      unfold IsFreePosition Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.bb
      unfold blk at c
      simp only
      split_ifs at c ⊢ <;> omega
    · rw [h i i ?_, if_pos rfl]
      unfold IsFreePosition
      simp
    · have c2' : j.val < i.val := c2
      rw [h i j ?_, if_neg (ne_of_gt c2)]
      unfold IsFreePosition Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.bb
      unfold blk at c
      simp only
      split_ifs at c ⊢ <;> omega
    · rw [h i j ?_, if_neg hij]
      unfold IsFreePosition Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.bb
      unfold blk at c2
      simp only
      split_ifs at c2 ⊢ <;> omega

theorem card_upper_pairs_in_interval (k rS n : ℕ) (hn : rS + k ≤ n) :
    Nat.card {p : Fin n × Fin n // rS ≤ p.1.val ∧ p.1.val < p.2.val ∧ p.2.val < rS + k} = k * (k - 1) / 2 := by
  rw [← Formalism.LogVandermondeBounds.StandardLattice.card_lt_pairs k]
  refine Nat.card_congr
    { toFun := fun p => ⟨(⟨p.1.1.val - rS, by have := p.2; omega⟩, ⟨p.1.2.val - rS, by have := p.2; omega⟩), by
        have := p.2; rw [Fin.lt_def]; simp only; omega⟩
      invFun := fun q => ⟨(⟨q.1.1.val + rS, by have := q.1.1.2; omega⟩, ⟨q.1.2.val + rS, by have := q.1.2.2; omega⟩), by
        have h := q.2; rw [Fin.lt_def] at h; have := q.1.2.2; simp only; omega⟩
      left_inv := fun p => by
        have := p.2
        apply Subtype.ext; apply Prod.ext <;> apply Fin.ext <;> simp only <;> omega
      right_inv := fun q => by
        apply Subtype.ext; apply Prod.ext <;> apply Fin.ext <;> simp only <;> omega }

theorem card_free_positions (k rS : ℕ) :
    Nat.card {p : Fin (rS + (k + 1) + rS) × Fin (rS + (k + 1) + rS) // IsFreePosition k rS _ p} =
      rS * (2 * k + 1 + 2 * rS) + k * (k - 1) / 2 := by
  classical
  have hd : Disjoint (fun p : Fin (rS + (k + 1) + rS) × Fin (rS + (k + 1) + rS) =>
      Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.bb k rS p.1.val < Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.bb k rS p.2.val)
      (fun p => rS ≤ p.1.val ∧ p.1.val < p.2.val ∧ p.2.val < rS + k) := by
    rw [Pi.disjoint_iff]
    intro p
    rw [disjoint_iff_inf_le]
    rintro ⟨h1, h2⟩
    unfold Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.bb at h1
    split_ifs at h1 <;> omega
  have h := Fintype.card_subtype_or_disjoint _ _ hd
  have e1 := Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.countFree k rS _ rfl
  have e2 := card_upper_pairs_in_interval k rS (rS + (k + 1) + rS) (by omega)
  rw [Nat.card_eq_fintype_card] at e2 ⊢
  rw [← e1, ← e2, ← Fintype.card_subtype]
  convert h using 1
  exact Fintype.card_congr (Equiv.refl _)

theorem rowLevCard_holds : RowLevCard := by
  intro g k m hg hm he
  have : Fact g.Prime := ⟨hg⟩
  obtain ⟨c, hc⟩ := he
  obtain ⟨rS, hrS⟩ : ∃ rS, m / 2 - 1 = rS := ⟨_, rfl⟩
  have hn : k + m - 1 = rS + (k + 1) + rS := by omega
  rw [hrS, hn]
  have hdet : ∀ A : Matrix (Fin (rS + (k + 1) + rS)) (Fin (rS + (k + 1) + rS)) (ZMod g), IsRowLev k rS A → A.det = 1 := by
    intro A hA
    apply det_eq_one_of_unitriangular
    refine ⟨fun i j hji => ?_, hA.2.1⟩
    have hji' : j.val < i.val := hji
    by_cases c1 : blk rS k j.val < blk rS k i.val
    · exact hA.1 i j c1
    · refine hA.2.2.1 i j ?_ hji
      unfold blk at c1 ⊢
      split_ifs at c1 ⊢ <;> omega
  rw [card_GL_subtype_eq_card_matrix _ hdet]
  have e : Nat.card {A : Matrix (Fin (rS + (k + 1) + rS)) (Fin (rS + (k + 1) + rS)) (ZMod g) // IsRowLev k rS A} =
      Nat.card {A : Matrix (Fin (rS + (k + 1) + rS)) (Fin (rS + (k + 1) + rS)) (ZMod g) //
        ∀ i j, ¬ IsFreePosition k rS _ (i, j) → A i j = if i = j then 1 else 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun A => isLevel_iff_free_support k rS _ A)
  rw [e, card_matrices_with_free_support, card_free_positions, ZMod.card, pow_add]
  congr 2
  have : (rS + (k + 1) + rS) ^ 2 = (k + 1) ^ 2 + 2 * rS + 2 * (rS * (2 * k + 1 + 2 * rS)) := by ring
  rw [this]; omega

theorem levelRowCard_holds (D : D7) : Conclusion4a D := by
  exact levelRowCard_of_card rowLevCard_holds D

theorem strictAnti_of_succ_lt_alt {n : ℕ} (x : Fin n → ℝ) (h : ∀ i j : Fin n, j.val = i.val + 1 → x j < x i) :
    StrictAnti x := by
  cases n with
  | zero => intro a; exact a.elim0
  | succ m =>
    rw [Fin.strictAnti_iff_succ_lt]
    intro i
    exact h _ _ (by simp)

theorem strictAnti_fin_append {a m : ℕ} (v : Fin a → ℝ) (w : Fin m → ℝ) (hv : StrictAnti v) (hw : StrictAnti w)
    (hvw : ∀ i j, w j < v i) : StrictAnti (Fin.append v w) := by
  intro i j hij
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      rw [Fin.append_left, Fin.append_left]
      apply hv
      rw [Fin.lt_iff_val_lt_val] at hij ⊢
      simpa using hij
    | right j =>
      rw [Fin.append_left, Fin.append_right]
      exact hvw i j
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      exfalso
      rw [Fin.lt_iff_val_lt_val] at hij
      simp only [Fin.coe_natAdd, Fin.coe_castAdd] at hij
      have := j.isLt
      omega
    | right j =>
      rw [Fin.append_right, Fin.append_right]
      apply hw
      rw [Fin.lt_iff_val_lt_val] at hij ⊢
      simp only [Fin.coe_natAdd] at hij
      omega

theorem strictAnti_param_v (D : D7) (ρ : D.what₂.Tau) : StrictAnti (fun i => (((D.hc ρ).v i : ℚ) : ℝ)) := by
  apply strictAnti_of_succ_lt_alt
  intro i j hij
  have h1 := (D.hc ρ).v_gt_u i
  have h2 := (D.hc ρ).u_gt_v j
  have e : (⟨i.1 + 1, by omega⟩ : Fin D.R.k) = ⟨j.1, by omega⟩ := by ext; simp [hij]
  rw [e] at h1
  exact_mod_cast h2.trans h1

theorem strictAnti_neg_param_b (D : D7) (ρ : D.what₂.Tau) : StrictAnti (fun j => -(((D.hc ρ).b j : ℚ) : ℝ)) := by
  apply strictAnti_of_succ_lt_alt
  intro i j hij
  have h1 := (D.hc ρ).gap_be i
  have h2 := (D.hc ρ).gap_eb i (by have := j.2; omega)
  have e : (⟨i.1 + 1, by have := j.2; omega⟩ : Fin D.R.m) = j := by ext; simp [hij]
  rw [e] at h2
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  have : (D.hc ρ).b i < (D.hc ρ).b j := by linarith
  have : (((D.hc ρ).b i : ℚ) : ℝ) < (((D.hc ρ).b j : ℚ) : ℝ) := by exact_mod_cast this
  linarith

theorem line_param_strictAnti (D : D7) (ρ : D.what₂.Tau) : StrictAnti (rowLam D ρ) := by
  apply strictAnti_fin_append _ _ (strictAnti_param_v D ρ) (strictAnti_neg_param_b D ρ)
  intro i j
  have hk := D.R.k_ge
  have hm := D.R.two_le_m
  have h0 := (D.hc ρ).u_last_gt (by omega) (by omega)
  have h1 := (D.hc ρ).v_gt_u ⟨D.R.k - 2, by omega⟩
  have e : (⟨(⟨D.R.k - 2, by omega⟩ : Fin (D.R.k - 1)).1 + 1, by simp; omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := by
    ext; simp; omega
  rw [e] at h1
  have h2 : (((D.hc ρ).v ⟨D.R.k - 2, by omega⟩ : ℚ) : ℝ) ≤ (((D.hc ρ).v i : ℚ) : ℝ) :=
    (strictAnti_param_v D ρ).antitone (by rw [Fin.le_def]; have := i.2; simp; omega)
  have h3 : -(((D.hc ρ).b j : ℚ) : ℝ) ≤ -(((D.hc ρ).b ⟨0, by omega⟩ : ℚ) : ℝ) :=
    (strictAnti_neg_param_b D ρ).antitone (by rw [Fin.le_def]; simp)
  have h4 : -(((D.hc ρ).b ⟨0, by omega⟩ : ℚ) : ℝ) < (((D.hc ρ).v ⟨D.R.k - 2, by omega⟩ : ℚ) : ℝ) := by
    exact_mod_cast h0.trans h1
  linarith

theorem factorial_product_pos (N : ℕ) : 0 < facProd N := by
  unfold facProd
  exact Finset.prod_pos fun i _ => Nat.cast_pos.mpr (Nat.factorial_pos i)

theorem dim_weyl_pos_of_strictAnti {N : ℕ} (x : Fin N → ℝ) (h : StrictAnti x) : 0 < dimV x := by
  unfold dimV vand
  apply div_pos
  · apply Finset.prod_pos
    intro a _
    apply Finset.prod_pos
    intro b hb
    rw [Finset.mem_filter] at hb
    exact sub_pos.mpr (h hb.2)
  · exact factorial_product_pos N

theorem local_index_nonneg (F : Type) [CommRing F] (n : ℕ) (P : Matrix (Fin n) (Fin n) F → Prop) : 0 ≤ idxLoc F n P := by
  unfold idxLoc
  positivity

theorem volume_eq_mass_at_rank (D : D7) (h2v : VolumeEqMass₂ D) : volY0 D = massI D D.R.r := by
  let _ := D.host.cmStar
  have h := h2v.2 (D.sp.Y 0) D.R.sigY0.1 D.R.sigY0.2 (D.sp.Y_sig 0) (fun τ => D.sp.baseSpace_signature_eq τ)
    (by have := D.R.k_ge; simp only [Ranks.sigY0]; omega)
  have e : D.R.sigY0.1 + D.R.sigY0.2 = D.R.r := by
    have := D.R.rS_two; have := D.R.r_eq; simp only [Ranks.sigY0]; omega
  rw [e] at h
  exact h

theorem lastLine_of_massAndDegree (D : D7) (C3 : ℝ) (h2v : VolumeEqMass₂ D) (h3 : PointsLemma D C3) : DstarLowerFromGap D C3 := by
  intro hgap
  unfold DstarLow DstarD DstarP
  rw [volume_eq_mass_at_rank D h2v]
  have hm : 0 < massI D D.R.r := by rw [← volume_eq_mass_at_rank D h2v]; exact D.vol_pos _
  have hI : 0 ≤ idxSig D (D.host.g 0) (D.host.g 1) := by
    unfold idxSig idxRowLoc
    exact mul_nonneg (pow_nonneg (local_index_nonneg _ _ _) _) (pow_nonneg (local_index_nonneg _ _ _) _)
  have hr : Real.exp (-(D.R.r : ℝ)) ≤ 1 / 3 := by
    have h2 : (2 : ℝ) ≤ D.R.r := by
      have := D.R.k_ge; have := D.R.r_eq; have := D.R.two_le_m
      exact_mod_cast (by omega : 2 ≤ D.R.r)
    have h5 : (3 : ℝ) ≤ Real.exp (D.R.r : ℝ) := by
      have := Real.add_one_le_exp (D.R.r : ℝ); linarith
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) h5
  have hp : (2 / 3 : ℝ) ^ D.R.f * ∏ ρ, dimV (rowLam D ρ) ≤ ∏ ρ, D.dsig ρ := by
    rw [← D.what₂.card_Tau, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun ρ _ => mul_nonneg (by norm_num) (dim_weyl_pos_of_strictAnti _ (line_param_strictAnti D ρ)).le) fun ρ _ => ?_
    have := (h3 (1 / 3) hr (by norm_num) ρ (hgap ρ)).1
    linarith
  calc (2 / 3 : ℝ) ^ D.R.f * massI D D.R.r * idxSig D (D.host.g 0) (D.host.g 1) * ∏ ρ, dimV (rowLam D ρ)
      = massI D D.R.r * idxSig D (D.host.g 0) (D.host.g 1) * ((2 / 3 : ℝ) ^ D.R.f * ∏ ρ, dimV (rowLam D ρ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (mul_nonneg hm.le hI)

theorem levelStatement_of_classes (D : D7) (Lv : LevelData D) (C3 : ℝ)
    (hfin : Module.finrank ℚ D.host.E = 2 * D.R.f)
    (hp : Conclusion4p D Lv) (hn : ClassNumberFormula₂ D Lv) (hg : OrthonormalLatticeRankK D) : ThetaChernBoundOfLastLine D Lv C3 := by
  intro h2 h3 h17
  have hd := levelDimension_of_admissible D Lv h17 hp
  exact ⟨levelRowCard_holds D, levelPartB_holds D, hostDegree_of_finrank D hfin, hp, hd, levelPartE_holds D, hn, level_rank_of_trivial_stabilisers D Lv hd hn, hg,
    lastLine_of_massAndDegree D C3 h2.2.1 h3⟩

theorem line_param_apply (D : D7) (ρ : D.what₂.Tau) (a : Fin (D.R.k - 1 + D.R.m)) :
    rowLam D ρ a = Formalism.LogVandermondeBounds.StandardLattice.rowPar D.R.k (vN D ρ) (bN D ρ) a.val := by
  induction a using Fin.addCases with
  | left i =>
    have hi : (Fin.castAdd D.R.m i).val = i.val := rfl
    unfold rowLam Formalism.LogVandermondeBounds.StandardLattice.rowPar vN
    rw [Fin.append_left, hi, if_pos i.2, dif_pos i.2]
  | right j =>
    have hj : (Fin.natAdd (D.R.k - 1) j).val = D.R.k - 1 + j.val := rfl
    unfold rowLam Formalism.LogVandermondeBounds.StandardLattice.rowPar bN
    rw [Fin.append_right, hj, if_neg (by omega), Nat.add_sub_cancel_left, dif_pos j.2]

theorem line_sign_apply (D : D7) (a : Fin (D.R.k - 1 + D.R.m)) :
    rowSgn D a = Formalism.LogVandermondeBounds.StandardLattice.plusSign D.R.k a.val := by
  unfold rowSgn Formalism.LogVandermondeBounds.StandardLattice.plusSign
  induction a using Fin.addCases with
  | left i =>
    rw [Fin.append_left]
    simp [i.isLt]
  | right j =>
    rw [Fin.append_right]
    simp

theorem gap_bound_mono (D : D7) (C C' ep0 : ℝ) (h : C ≤ C') : gap3 D C ep0 ≤ gap3 D C' ep0 := by
  unfold gap3
  have hr : (1 : ℝ) ≤ D.R.r := by
    have := D.R.k_ge; have := D.R.r_eq; have := D.R.two_le_m
    exact_mod_cast (by omega : 1 ≤ D.R.r)
  have hl : 0 ≤ Real.log (D.R.r : ℝ) := Real.log_nonneg hr
  gcongr

theorem exponent_pos_of_rank_le_pow (D : D7) (sc : Scale) (C0 : ℝ) (h5 : (D.R.k : ℝ) ≤ sc.x ^ C0) : 0 < C0 := by
  by_contra hn
  have h1 : sc.x ^ C0 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos sc.one_lt_alt.le (not_lt.1 hn)
  have h2 : (5 : ℝ) ≤ D.R.k := by exact_mod_cast D.R.k_ge
  linarith

theorem gap_bound_at_one_third (D : D7) (C : ℝ) (hC : 0 ≤ C) : gap3 D C (1 / 3) ≤ 9 * C * (D.R.r : ℝ) ^ 9 := by
  have hk := D.R.k_ge
  have hm := D.R.two_le_m
  have hm2 := D.R.rS_two
  have er : D.R.r = D.R.k + D.R.m - 1 := rfl
  have ep : pY D ≤ D.R.r := by unfold pY; simp only [Ranks.sigY0]; omega
  have eq : qY D ≤ D.R.r := by unfold qY; simp only [Ranks.sigY0]; omega
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : 1 ≤ D.R.r)
  have hl0 : 0 ≤ Real.log (D.R.r : ℝ) := Real.log_nonneg hr
  have hl : Real.log (D.R.r : ℝ) ≤ D.R.r := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (D.R.r : ℝ) by linarith)
    linarith
  have hp : (pY D : ℝ) ≤ D.R.r := by exact_mod_cast ep
  have hq : (qY D : ℝ) ≤ D.R.r := by exact_mod_cast eq
  have hmin : ((min (pY D) (qY D) : ℕ) : ℝ) ≤ D.R.r := by exact_mod_cast le_trans (min_le_left _ _) ep
  unfold gap3
  have e1 : C * (min (pY D) (qY D) : ℕ) * ((pY D : ℝ) * (qY D : ℝ)) ^ 3 * (D.R.r : ℝ) *
      Real.log (D.R.r : ℝ) / (1 / 3) ^ 2 =
      9 * C * (((min (pY D) (qY D) : ℕ) : ℝ) * ((pY D : ℝ) * (qY D : ℝ)) ^ 3 * (D.R.r : ℝ) *
      Real.log (D.R.r : ℝ)) := by ring
  rw [e1]
  have e2 : ((min (pY D) (qY D) : ℕ) : ℝ) * ((pY D : ℝ) * (qY D : ℝ)) ^ 3 * (D.R.r : ℝ) *
      Real.log (D.R.r : ℝ) ≤ (D.R.r : ℝ) * ((D.R.r : ℝ) * (D.R.r : ℝ)) ^ 3 * (D.R.r : ℝ) * (D.R.r : ℝ) := by
    gcongr
  calc 9 * C * (((min (pY D) (qY D) : ℕ) : ℝ) * ((pY D : ℝ) * (qY D : ℝ)) ^ 3 * (D.R.r : ℝ) *
      Real.log (D.R.r : ℝ)) ≤ 9 * C * ((D.R.r : ℝ) * ((D.R.r : ℝ) * (D.R.r : ℝ)) ^ 3 * (D.R.r : ℝ) * (D.R.r : ℝ)) :=
        mul_le_mul_of_nonneg_left e2 (by positivity)
    _ = 9 * C * (D.R.r : ℝ) ^ 9 := by ring

theorem parameter_gap_under_section_B (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (ρ : D.what₂.Tau) : GapAtLeast (rowSgn D) (rowLam D ρ) ((D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * sc.L / C0) := by
  obtain ⟨-, -, -, -, h5, -, h7, h8, -, -, -, -, -, -, h15, h16⟩ := hB
  have hk := D.R.k_ge
  have hC0 := exponent_pos_of_rank_le_pow D sc C0 h5
  have hx : 0 < sc.x := lt_trans one_pos sc.one_lt_alt
  have hL : 0 ≤ sc.L := by unfold Scale.L; exact (Real.rpow_pos_of_pos hx _).le
  have hb0 : 0 < bN D ρ 0 := by
    have h1 := (h15 ρ).1
    have h2 : 0 < (D.R.k : ℝ) * (4 * Δ) := by
      have : (0 : ℝ) < D.R.k := by exact_mod_cast (by omega : 0 < D.R.k)
      positivity
    have h3 : 0 < bN D ρ 0 / sc.x := lt_of_lt_of_le h2 h1
    by_contra hn
    exact absurd h3 (not_lt.2 (div_nonpos_of_nonpos_of_nonneg (not_lt.1 hn) hx.le))
  have key := Formalism.HermitianLattices.GenusMassVolumes.least_noncompact_gap D.R.k D.R.m (vN D ρ) (bN D ρ)
    ((D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * sc.L / C0)
    (by omega) (by positivity) (fun i hi => (h8 ρ i hi).1) hb0 (fun j hj => h16 ρ j hj)
  intro a b hab
  rw [line_sign_apply, line_sign_apply] at hab
  rw [line_param_apply, line_param_apply]
  rcases lt_trichotomy a.val b.val with h | h | h
  · exact (key a.val b.val h b.2 hab).trans (le_abs_self _)
  · exact absurd (by rw [h]) hab
  · rw [abs_sub_comm]
    exact (key b.val a.val h a.2 hab.symm).trans (le_abs_self _)

theorem levelStatement_eventually (eps C3 C0 : ℝ) (heps : 0 < eps) :
    ∃ x0 : ℝ, ∀ (D : D7) (Lv : LevelData D) (sc : Scale), sc.eps = eps → x0 ≤ sc.x → PartFourSectionBStatement D Lv sc C3 C0 := by
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop heps).eventually_ge_atTop (9 * max C3 0 * C0))
  refine ⟨x0, fun D Lv sc he hx h4 Δ w hB => ?_⟩
  obtain ⟨-, -, -, -, h4d, -, -, -, -, h4h⟩ := h4
  have hk := D.R.k_ge
  have hB' := hB
  obtain ⟨-, -, -, -, h5, h6, -⟩ := hB'
  have hg : ∀ i : Fin 2, 2 * D.R.f * D.R.k < D.host.g i - 1 := by
    intro i
    have h1 := (h6 i).1
    have hb : (1 : ℝ) ≤ sc.b := by
      unfold Scale.b
      exact Real.one_le_exp (by unfold Scale.L; exact (Real.rpow_pos_of_pos (lt_trans one_pos sc.one_lt_alt) _).le)
    have hk0 : (0 : ℝ) ≤ D.R.k := by positivity
    have h2 : (D.R.k : ℝ) ^ 8 ≤ (D.host.g i : ℝ) :=
      le_trans (pow_le_pow_left₀ hk0 (by nlinarith) 8) h1
    have h3 : D.R.k ^ 8 ≤ D.host.g i := by exact_mod_cast h2
    have hf : D.R.f ≤ D.R.k := D.R.f_le_k
    have h4 : 2 * D.R.f * D.R.k + 1 < D.R.k ^ 8 := by
      have e1 : 2 * D.R.f * D.R.k ≤ 2 * (D.R.k * D.R.k) := by nlinarith
      have e2 : D.R.k ^ 8 = (D.R.k * D.R.k) * (D.R.k ^ 6) := by ring
      have e3 : 5 ^ 6 ≤ D.R.k ^ 6 := Nat.pow_le_pow_left hk 6
      have e4 : 25 ≤ D.R.k * D.R.k := by nlinarith
      rw [e2]
      nlinarith
    omega
  have hgap : ∀ ρ, GapAtLeast (rowSgn D) (rowLam D ρ) (gap3 D C3 (1 / 3)) := by
    intro ρ a b hab
    refine le_trans ?_ (parameter_gap_under_section_B D sc C0 Δ w hB ρ a b hab)
    refine le_trans (gap_bound_mono D C3 (max C3 0) _ (le_max_left _ _)) ?_
    refine le_trans (gap_bound_at_one_third D (max C3 0) (le_max_right _ _)) ?_
    have hC0 := exponent_pos_of_rank_le_pow D sc C0 h5
    have hL : 9 * max C3 0 * C0 ≤ sc.L := by unfold Scale.L; rw [he]; exact hx0 sc.x hx
    have hr : (1 : ℝ) ≤ D.R.r := by
      have := D.R.k_ge; have := D.R.r_eq; have := D.R.two_le_m
      exact_mod_cast (by omega : 1 ≤ D.R.r)
    have hf : (1 : ℝ) ≤ D.R.f := by
      have h2 : 2 ≤ D.R.f := le_trans D.R.two_le_m D.R.m_le_f
      exact_mod_cast le_trans one_le_two h2
    have hL0 : 0 ≤ sc.L := le_trans (by have := le_max_right C3 0; positivity) hL
    rw [le_div_iff₀ hC0]
    have e1 : (D.R.r : ℝ) ^ 9 ≤ (D.R.r : ℝ) ^ 19 := pow_le_pow_right₀ hr (by norm_num)
    have e2 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ hf
    calc 9 * max C3 0 * (D.R.r : ℝ) ^ 9 * C0 = (D.R.r : ℝ) ^ 9 * (9 * max C3 0 * C0) := by ring
      _ ≤ (D.R.r : ℝ) ^ 9 * sc.L := mul_le_mul_of_nonneg_left hL (by positivity)
      _ = (D.R.r : ℝ) ^ 9 * 1 * sc.L := by ring
      _ ≤ (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * sc.L :=
          mul_le_mul_of_nonneg_right (mul_le_mul e1 e2 zero_le_one (by positivity)) hL0
  exact ⟨hg, hgap, fun u => h4d ⟨0, hg 0⟩ u, h4h hgap⟩

theorem familyLevelSectionB_holds {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C3 : ℝ) : FamilySectionBStatement Fm C3 := by
  intro h4 C0
  have heps : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_eps 0 i]; exact (Fm.L 0 i).sc.eps_pos
  obtain ⟨x0, hx0⟩ := levelStatement_eventually eps C3 C0 heps
  refine ⟨x0, fun x hx hx1 i => ?_⟩
  exact hx0 (Fm.D x i) (Fm.ex x hx1 i).lev (Fm.L x i).sc (Fm.L_eps x i) (by rw [Fm.L_x x i hx1]; exact hx) (h4 x hx1 i)

theorem familyLevel_of_classes {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C3 : ℝ)
    (hfin : ∀ x (i : Fm.Ix x), Module.finrank ℚ (Fm.D x i).host.E = 2 * (Fm.D x i).R.f)
    (hp : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Conclusion4p (Fm.D x i) (Fm.ex x hx i).lev)
    (hn : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev)
    (hg : ∀ x (i : Fm.Ix x), OrthonormalLatticeRankK (Fm.D x i)) : LiftNormFamilyStatement Fm C3 :=
  fun h2 h3 h17 x hx i =>
    levelStatement_of_classes (Fm.D x i) (Fm.ex x hx i).lev C3 (hfin x i) (hp x hx i) (hn x hx i) (hg x i) (h2 x i) (h3 x i) (h17 x hx i)

section P3

open Formalism.MainNotions.S MeasureTheory
open scoped InnerProductSpace

theorem formal_degree_of_eq {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
    (μ : Measure (Formalism.REAL.UJ ε)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d : ℝ) (h : IsFdeg μ σ d)
    (w : H) (hw : w ≠ 0) : fdegOf μ σ w = d := by
  obtain ⟨hd, hh⟩ := h
  obtain ⟨-, h2⟩ := hh w w w w
  have e1 : ∀ g, coefOn σ w w g * star (coefOn σ w w g) = ((‖coefOn (ε := ε) σ w w g‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [e1] at h2
  rw [integral_complex_ofReal] at h2
  have e2 : (⟪w, w⟫_ℂ : ℂ) = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [e2] at h2
  have h3 : (∫ g, ‖coefOn (ε := ε) σ w w g‖ ^ 2 ∂μ) = ‖w‖ ^ 2 * ‖w‖ ^ 2 / d := by
    exact_mod_cast h2
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  unfold fdegOf
  rw [h3]
  field_simp

theorem dim_weyl_finCast {n n' : ℕ} (h : n = n') (x : Fin n' → ℝ) : dimV (fun i => x (Fin.cast h i)) = dimV x := by
  subst h
  rfl
theorem formal_degree_finCast {n n' : ℕ} (h : n = n') (s : Fin n' → Bool) (x : Fin n' → ℝ) :
    dTau (fun i => s (Fin.cast h i)) (fun i => x (Fin.cast h i)) = dTau s x := by
  subst h
  rfl
theorem abs_param_sup_finCast {n n' : ℕ} (h : n = n') (x : Fin n' → ℝ) : lamAbs (fun i => x (Fin.cast h i)) = lamAbs x := by
  subst h
  rfl
theorem count_plus_finCast {n n' : ℕ} (h : n = n') (s : Fin n' → Bool) : nPlus (fun i => s (Fin.cast h i)) = nPlus s := by
  subst h
  rfl
theorem count_minus_finCast {n n' : ℕ} (h : n = n') (s : Fin n' → Bool) : nMinus (fun i => s (Fin.cast h i)) = nMinus s := by
  subst h
  rfl
theorem strictAnti_comp_finCast {n n' : ℕ} (h : n = n') (x : Fin n' → ℝ) (hx : StrictAnti x) :
    StrictAnti (fun i => x (Fin.cast h i)) := by
  subst h
  exact hx
theorem gapAtLeast_finCast {n n' : ℕ} (h : n = n') (s : Fin n' → Bool) (x : Fin n' → ℝ) (g : ℝ) (hx : GapAtLeast s x g) :
    Formalism.QuantumDeterminants.GapAtLeast (fun i => s (Fin.cast h i)) (fun i => x (Fin.cast h i)) g := by
  subst h
  exact hx

theorem rank_dimension_identity (R : Ranks) : 2 * R.rS + R.k + 1 = R.k - 1 + R.m := by
  show 2 * (R.m / 2 - 1) + R.k + 1 = R.k - 1 + R.m
  have h1 := R.two_le_m
  have h2 := R.m_add_three_le_k
  obtain ⟨j, hj⟩ := R.m_even
  omega

theorem param_vector_eq_line_param (D : D7) (ρ : D.what₂.Tau) :
    lamSH D.R (D.hc ρ) = fun i => rowLam D ρ (Fin.cast (rank_dimension_identity D.R) i) := by
  funext i
  rw [line_param_apply]
  have hi : i.val < D.R.k - 1 + D.R.m := by have := i.2; have := rank_dimension_identity D.R; omega
  unfold lamSH lamS Formalism.LogVandermondeBounds.StandardLattice.rowPar vN bN
  simp only [Fin.val_cast]
  by_cases h : i.val < D.R.k - 1
  · rw [dif_pos h, if_pos h, dif_pos h]
  · have h' : i.val - (D.R.k - 1) < D.R.m := by omega
    rw [dif_neg h, if_neg h, dif_pos h', dif_pos h']

theorem sign_vector_eq_line_sign (D : D7) : epsSH D.R = fun i => rowSgn D (Fin.cast (rank_dimension_identity D.R) i) := by
  funext i
  rw [line_sign_apply]
  unfold epsSH epsS Formalism.LogVandermondeBounds.StandardLattice.plusSign
  simp only [Fin.val_cast]
  by_cases h : i.val < D.R.k - 1
  · simp [h]
  · simp [h]

theorem sum_indicator_even_range (c : ℕ) : ∑ j ∈ range (2 * c), (if j % 2 = 0 then 1 else 0) = c := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [show 2 * (c + 1) = 2 * c + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h1 : (2 * c) % 2 = 0 := by omega
    have h2 : (2 * c + 1) % 2 = 1 := by omega
    simp [h1, h2]

theorem count_plus_line_sign (D : D7) : nPlus (rowSgn D) = pY D := by
  unfold nPlus rowSgn
  rw [Finset.card_filter, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, if_true, decide_eq_true_eq]
  rw [Fin.sum_univ_eq_sum_range (fun j => if j % 2 = 0 then 1 else 0) D.R.m]
  obtain ⟨c, hc⟩ := D.R.m_even
  have hc' : D.R.m = 2 * c := by omega
  rw [hc', sum_indicator_even_range]
  have := D.R.rS_two; have := D.R.k_ge
  unfold pY
  simp only [Ranks.sigY0, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  omega

private lemma card_split_lemma {α : Type*} (S : Finset α) (p : α → Prop) [DecidablePred p] :
    (S.filter p).card + (S.filter (fun a => ¬ p a)).card = S.card := by
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases h : p a <;> simp [h]

theorem count_plus_add_count_minus (N : ℕ) (s : Fin N → Bool) : nPlus s + nMinus s = N := by
  unfold nPlus nMinus
  have h := card_split_lemma (univ : Finset (Fin N)) (fun a => s a = true)
  have e : (univ.filter (fun a : Fin N => ¬ s a = true)) = univ.filter (fun a => s a = false) := by
    ext a
    simp
  rw [e, Finset.card_univ, Fintype.card_fin] at h
  exact h

theorem count_minus_line_sign (D : D7) : nMinus (rowSgn D) = qY D := by
  have h1 := count_plus_add_count_minus _ (rowSgn D)
  rw [count_plus_line_sign] at h1
  have := D.R.rS_two; have := D.R.k_ge
  unfold pY at h1
  unfold qY
  simp only [Ranks.sigY0] at h1 ⊢
  omega

theorem line_param_harish_chandra (D : D7) (ρ : D.what₂.Tau) : Formalism.QuantumDeterminants.IsHCParam (lamSH D.R (D.hc ρ)) := by
  rw [param_vector_eq_line_param]
  refine ⟨strictAnti_comp_finCast _ _ (line_param_strictAnti D ρ), fun a => ?_⟩
  obtain ⟨c, hc⟩ := D.R.m_even
  obtain ⟨c', hc'⟩ := D.R.k_even
  have hrS := D.R.rS_two
  have hN : (((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) - 1) / 2 = ((D.R.rS + c' : ℕ) : ℝ) := by
    rw [hc']; push_cast; ring
  rw [hN]
  have hz : ∃ z : ℤ, rowLam D ρ (Fin.cast (rank_dimension_identity D.R) a) = (z : ℝ) := by
    generalize Fin.cast (rank_dimension_identity D.R) a = b
    induction b using Fin.addCases with
    | left i =>
      obtain ⟨z, hz⟩ := (D.hc ρ).v_int i
      refine ⟨z, ?_⟩
      unfold rowLam
      rw [Fin.append_left, hz]; push_cast; rfl
    | right j =>
      obtain ⟨z, hz⟩ := (D.hc ρ).b_int j
      refine ⟨-z, ?_⟩
      unfold rowLam
      rw [Fin.append_right, hz]; push_cast; rfl
  obtain ⟨z, hz⟩ := hz
  exact ⟨z - ((D.R.rS + c' : ℕ) : ℤ), by show rowLam D ρ (Fin.cast (rank_dimension_identity D.R) a) - _ = _; rw [hz]; push_cast; ring⟩

theorem formalDegreeBound_of_general (D : D7) (C3 : ℝ) : TowerRallisLemma D C3 := by
  intro hAll hT hEx ep0 he1 he2 ρ hgap
  obtain ⟨H, i1, i2, σ, hDS, hF⟩ := hEx ρ
  have hcs : CompleteSpace H := hDS.1
  have hnt : Nontrivial H := hDS.2.1
  obtain ⟨w, hw⟩ := exists_ne (0 : H)
  have hHC := line_param_harish_chandra D ρ
  have hdt := (hT _ (epsSH D.R) (lamSH D.R (D.hc ρ)) hHC H σ hDS).2
  have hp : ((Finset.univ.filter (fun a => epsSH D.R a = true)).card : ℝ) = (pY D : ℝ) := by
    have : (Finset.univ.filter (fun a => epsSH D.R a = true)).card = nPlus (epsSH D.R) := rfl
    rw [this, sign_vector_eq_line_sign, count_plus_finCast, count_plus_line_sign]
  have hq : ((Finset.univ.filter (fun a => epsSH D.R a = false)).card : ℝ) = (qY D : ℝ) := by
    have : (Finset.univ.filter (fun a => epsSH D.R a = false)).card = nMinus (epsSH D.R) := rfl
    rw [this, sign_vector_eq_line_sign, count_minus_finCast, count_minus_line_sign]
  have hN : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = (D.R.r : ℝ) := by rw [dimS_eq]
  have hg' : Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamSH D.R (D.hc ρ)) (gap3 D C3 ep0) := by
    rw [sign_vector_eq_line_sign, param_vector_eq_line_param]; exact gapAtLeast_finCast _ _ _ _ hgap
  have key := hAll _ (epsSH D.R) (lamSH D.R (D.hc ρ)) ep0 (gap3 D C3 ep0) H σ w hHC hg'
    (by rw [hN]; exact he1) he2
    (by rw [hp, hq, hN]; unfold gap3; rw [Nat.cast_min]) hDS hw
  rw [formal_degree_of_eq _ σ _ hF w hw, hp, hq, hN, hdt] at key
  rw [← dimV_eq_fdegHC _ hHC.1] at key
  rw [sign_vector_eq_line_sign, param_vector_eq_line_param, dim_weyl_finCast, formal_degree_finCast, abs_param_sup_finCast] at key
  refine ⟨key.1, ?_⟩
  have e : ((pY D : ℝ) * (qY D : ℝ)) = ((pY D * qY D : ℕ) : ℝ) := by push_cast; rfl
  rw [e, Real.rpow_natCast] at key
  exact key.2

theorem familyFormalDegree_holds {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C3 : ℝ) : FlatLineDegreeFamilyStatement Fm C3 :=
  fun h1 h2 h3 x i => formalDegreeBound_of_general (Fm.D x i) C3 (h1 x i) (h2 x i).2.2 (h3 x i)

end P3

end Formalism.MainNotions.StandardLattice

namespace Formalism.MainNotions.StandardLattice

open NumberField Formalism.BasicNotions Finset

theorem log_vandermonde_eq_sum {N : ℕ} (x : Fin N → ℝ) (h : StrictAnti x) : Real.log (vand x) = Formalism.LogVandermondeBounds.StandardLattice.vandLog x := by
  unfold vand Formalism.LogVandermondeBounds.StandardLattice.vandLog
  rw [Real.log_prod]
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Real.log_prod]
    intro b hb
    rw [Finset.mem_filter] at hb
    exact (sub_pos.mpr (h hb.2)).ne'
  · intro a _
    apply Finset.prod_ne_zero_iff.mpr
    intro b hb
    rw [Finset.mem_filter] at hb
    exact (sub_pos.mpr (h hb.2)).ne'

theorem log_vandermonde_variation_generic (k : ℕ) (hk : 2 ≤ k) (Δ : ℝ) (u u' : Fin k → ℝ) (h0 : 0 < Δ)
    (hg : ∀ a b, a < b → 1 ≤ u a - u b) (hg' : ∀ a b, a < b → 1 ≤ u' a - u' b) (hd : ∀ i, |u i - u' i| ≤ Δ)
    (hfirst : ∀ i : Fin k, i.val = 0 → u i = u' i) (hlast : ∀ i : Fin k, i.val = k - 1 → u i = u' i)
    (h3 : ∀ i j : Fin k, 1 ≤ i.val → j.val = i.val + 1 → j.val ≤ k - 2 → 3 * Δ ≤ u i - u j ∧ 3 * Δ ≤ u' i - u' j)
    (hl : Real.log (1 + Δ) ≤ k) :
    |Real.log (vand u) - Real.log (vand u')| ≤ 8 * k * (1 + Real.log k) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  have a1 : StrictAnti u := fun a b hab => by have := hg a b hab; linarith
  have a2 : StrictAnti u' := fun a b hab => by have := hg' a b hab; linarith
  rw [log_vandermonde_eq_sum u a1, log_vandermonde_eq_sum u' a2]
  have := Formalism.LogVandermondeBounds.StandardLattice.variation_in_context n Δ u u'
    ⟨h0, hg, hg', hd, hfirst 0 rfl, hlast _ (by simp), fun i j hi hj hjn => h3 i j hi hj (by omega)⟩
    (by push_cast at hl; exact hl)
  push_cast
  exact this

theorem column_param_apply (D : D7) (u : D.what₂.Word) (ρ : D.what₂.Tau) (i : Fin D.R.k) : uColR D u ρ i = uN D u ρ i.val := by
  unfold uColR uN; rw [dif_pos i.2]

theorem column_param_strictAnti (D : D7) (u : D.what₂.Word) (ρ : D.what₂.Tau) : StrictAnti (uColR D u ρ) := by
  apply strictAnti_of_succ_lt_alt
  intro i j hij
  have hi : i.val < D.R.k - 1 := by have := j.2; omega
  have h1 := (D.hcW u ρ).u_gt_v ⟨i.val, hi⟩
  have h2 := (D.hcW u ρ).v_gt_u ⟨i.val, hi⟩
  have e : (⟨(⟨i.val, hi⟩ : Fin (D.R.k - 1)).1 + 1, by simp; omega⟩ : Fin D.R.k) = j := by ext; simp [hij]
  rw [e] at h2
  unfold uColR
  exact_mod_cast h2.trans h1

theorem one_le_column_param_sub (D : D7) (u : D.what₂.Word) (ρ : D.what₂.Tau) (a b : Fin D.R.k) (hab : a < b) :
    1 ≤ uColR D u ρ a - uColR D u ρ b := by
  have h := column_param_strictAnti D u ρ hab
  obtain ⟨z, hz⟩ := (D.hcW u ρ).u_half a
  obtain ⟨z', hz'⟩ := (D.hcW u ρ).u_half b
  unfold uColR at h ⊢
  rw [hz, hz'] at h ⊢
  push_cast at h ⊢
  have h1 : (z' : ℝ) < z := by linarith
  have h2 : z' < z := by exact_mod_cast h1
  have h3 : (z' : ℝ) + 1 ≤ z := by exact_mod_cast h2
  linarith

theorem log_one_add_delta_le_rank (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (ρ : D.what₂.Tau) : Real.log (1 + Δ) ≤ D.R.k := by
  obtain ⟨-, -, -, h4, -, -, h7, -, -, -, -, -, h13, h14, h15, -⟩ := hB
  have hk := D.R.k_ge
  have hm := D.R.two_le_m
  have hx := sc.one_lt_alt
  have hL : 0 < sc.L := by unfold Scale.L; exact Real.rpow_pos_of_pos (by linarith) _
  have chain : ∀ j, j < D.R.m → bN D ρ 0 ≤ bN D ρ j := by
    intro j
    induction j with
    | zero => intro _; exact le_refl _
    | succ j ih =>
      intro hj
      have := ih (by omega)
      have := (h13 ρ j (by omega)).2.1
      have := h14 ρ j hj
      linarith
  have hb : bN D ρ 0 ≤ 2 * sc.b := by
    have := chain (D.R.m - 1) (by omega)
    have := (h13 ρ (D.R.m - 1) (by omega)).2.1
    have := (h15 ρ).2
    linarith
  have hkR : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hbpos : 0 < sc.b := Real.exp_pos _
  have h1 : (D.R.k : ℝ) * (4 * Δ) ≤ 2 * sc.b := by
    refine le_trans (h15 ρ).1 (le_trans ?_ hb)
    have hb0 : 0 ≤ bN D ρ 0 := by
      by_contra hn
      have : bN D ρ 0 / sc.x < 0 := div_neg_of_neg_of_pos (not_le.1 hn) (by linarith)
      have h2 := (h15 ρ).1
      have : 0 ≤ (D.R.k : ℝ) * (4 * Δ) := by positivity
      linarith
    exact div_le_self hb0 hx.le
  have h2 : Δ ≤ sc.b := by nlinarith
  have hb1 : 1 ≤ sc.b := Real.one_le_exp hL.le
  have h3 : Real.log (1 + Δ) ≤ Real.log (2 * sc.b) := Real.log_le_log (by linarith) (by linarith)
  have h5 : Real.log (2 * sc.b) = Real.log 2 + sc.L := by
    rw [Real.log_mul (by norm_num) hbpos.ne']; unfold Scale.b; rw [Real.log_exp]
  have h6 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hmR : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have hm2 : (4 : ℝ) ≤ (D.R.m : ℝ) ^ 2 := by nlinarith
  have h8 : 4 * sc.L ≤ (D.R.m : ℝ) ^ 2 * sc.L := mul_le_mul_of_nonneg_right hm2 hL.le
  linarith

theorem log_vandermonde_variation_le (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (u u' : D.what₂.Word) (ρ : D.what₂.Tau) :
    |Real.log (vand (uColR D u ρ)) - Real.log (vand (uColR D u' ρ))| ≤ 16 * D.R.k * Real.log D.R.k := by
  have hl := log_one_add_delta_le_rank D sc C0 Δ w hB ρ
  obtain ⟨-, -, -, -, -, -, h7, -, h9, h10, -⟩ := hB
  have hk := D.R.k_ge
  have cl : ∀ (u : D.what₂.Word) (i : Fin D.R.k), 1 ≤ i.val → i.val ≤ D.R.k - 2 →
      uColR D u ρ i = vN D ρ (i.val - 1) - 1 / 2 ∨ uColR D u ρ i = vN D ρ (i.val - 1) - 1 / 2 - Δ := by
    intro u i h1 h2; rw [column_param_apply]; exact h10 u ρ i.val h1 h2
  have hfirst : ∀ i : Fin D.R.k, i.val = 0 → uColR D u ρ i = uColR D u' ρ i := by
    intro i hi
    have e : i = ⟨0, by omega⟩ := Fin.ext hi
    unfold uColR
    rw [e, D.hcW_first u ρ (by omega), D.hcW_first u' ρ (by omega)]
  have hlast : ∀ i : Fin D.R.k, i.val = D.R.k - 1 → uColR D u ρ i = uColR D u' ρ i := by
    intro i hi
    have e : i = ⟨D.R.k - 1, by omega⟩ := Fin.ext hi
    unfold uColR
    rw [e, D.hcW_last u ρ (by omega), D.hcW_last u' ρ (by omega)]
  have h := log_vandermonde_variation_generic D.R.k (by omega) Δ (uColR D u ρ) (uColR D u' ρ) (by linarith)
    (one_le_column_param_sub D u ρ) (one_le_column_param_sub D u' ρ)
    (by
      intro i
      by_cases h1 : i.val = 0
      · rw [hfirst i h1]; simp; linarith
      · by_cases h2 : i.val = D.R.k - 1
        · rw [hlast i h2]; simp; linarith
        · rcases cl u i (by omega) (by omega) with e1 | e1 <;> rcases cl u' i (by omega) (by omega) with e2 | e2 <;>
            rw [e1, e2, abs_le] <;> constructor <;> linarith)
    hfirst hlast
    (by
      intro i j hi hj hjk
      have hv := h9 ρ (i.val - 1) (by omega)
      have ej : j.val - 1 = i.val - 1 + 1 := by omega
      constructor
      · rcases cl u i hi (by omega) with e1 | e1 <;> rcases cl u j (by omega) hjk with e2 | e2 <;>
          rw [e1, e2, ej] <;> linarith
      · rcases cl u' i hi (by omega) with e1 | e1 <;> rcases cl u' j (by omega) hjk with e2 | e2 <;>
          rw [e1, e2, ej] <;> linarith)
    hl
  refine le_trans h ?_
  have hkR : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hlog : 1 ≤ Real.log D.R.k := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  nlinarith

theorem weylLawVariation_holds (D : D7) (sc : Scale) (C0 C : ℝ) (hC : 16 ≤ C) : VandermondeVariationBound D sc C0 C := by
  intro Δ w hB
  have hk := D.R.k_ge
  have hkR : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hlog : 0 ≤ Real.log D.R.k := Real.log_nonneg (by linarith)
  have hf : (0 : ℝ) < D.R.f := by
    have : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
    exact_mod_cast this
  refine ⟨fun u u' ρ => le_trans (log_vandermonde_variation_le D sc C0 Δ w hB u u' ρ) (by gcongr), fun u u' => ?_⟩
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hC hlog)
  have hP : ∀ u : D.what₂.Word, 0 < ∏ ρ, dimV (uColR D u ρ) :=
    fun u => Finset.prod_pos fun ρ _ => dim_weyl_pos_of_strictAnti _ (column_param_strictAnti D u ρ)
  have hlogP : ∀ u : D.what₂.Word, Real.log (∏ ρ, dimV (uColR D u ρ)) =
      ∑ ρ, (Real.log (vand (uColR D u ρ)) - Real.log (facProd D.R.k)) := by
    intro u
    rw [Real.log_prod (fun ρ _ => (dim_weyl_pos_of_strictAnti _ (column_param_strictAnti D u ρ)).ne')]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    unfold dimV
    rw [Real.log_div ?_ (factorial_product_pos _).ne']
    exact (Finset.prod_pos fun a _ => Finset.prod_pos fun b hb =>
      sub_pos.2 (column_param_strictAnti D u ρ (Finset.mem_filter.1 hb).2)).ne'
  have hX : ∀ u : D.what₂.Word, logXuD D u = (1 / ((D.R.f : ℝ) * D.R.k)) *
      Real.log (DstarD D / (massI D D.R.k * idxPi D (D.host.g 0) (D.host.g 1)) / ∏ ρ, dimV (uColR D u ρ)) := by
    intro u
    unfold logXuD logXu duStarU duStarP
    rw [div_mul_eq_div_div (DstarD D)]
  rw [hX, hX, ← mul_sub]
  by_cases ha : DstarD D / (massI D D.R.k * idxPi D (D.host.g 0) (D.host.g 1)) = 0
  · rw [ha]; simp; positivity
  · rw [Real.log_div ha (hP u).ne', Real.log_div ha (hP u').ne', hlogP, hlogP]
    have e : ∀ A : ℝ, A - ∑ ρ, (Real.log (vand (uColR D u ρ)) - Real.log (facProd D.R.k)) -
        (A - ∑ ρ, (Real.log (vand (uColR D u' ρ)) - Real.log (facProd D.R.k))) =
        ∑ ρ, (Real.log (vand (uColR D u' ρ)) - Real.log (vand (uColR D u ρ))) := by
      intro A
      simp only [Finset.sum_sub_distrib]
      ring
    rw [e, abs_mul, abs_of_pos (by positivity)]
    have hs : |∑ ρ, (Real.log (vand (uColR D u' ρ)) - Real.log (vand (uColR D u ρ)))| ≤
        (D.R.f : ℝ) * (16 * D.R.k * Real.log D.R.k) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_card_nsmul _ _ _ fun ρ _ => log_vandermonde_variation_le D sc C0 Δ w hB u' u ρ) ?_
      rw [Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul]
    calc 1 / ((D.R.f : ℝ) * D.R.k) * |∑ ρ, (Real.log (vand (uColR D u' ρ)) - Real.log (vand (uColR D u ρ)))|
        ≤ 1 / ((D.R.f : ℝ) * D.R.k) * ((D.R.f : ℝ) * (16 * D.R.k * Real.log D.R.k)) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 16 * Real.log D.R.k := by field_simp

theorem three_le_level_of_section_B (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w) (i : Fin 2) :
    3 ≤ D.host.g i := by
  obtain ⟨-, -, -, -, -, h6, -⟩ := hB
  have hk := D.R.k_ge
  have h1 := (h6 i).1
  have hb : (1 : ℝ) ≤ sc.b := by
    unfold Scale.b
    exact Real.one_le_exp (by unfold Scale.L; exact (Real.rpow_pos_of_pos (lt_trans one_pos sc.one_lt_alt) _).le)
  have hk0 : (0 : ℝ) ≤ D.R.k := by positivity
  have h2 : (D.R.k : ℝ) ^ 8 ≤ (D.host.g i : ℝ) := le_trans (pow_le_pow_left₀ hk0 (by nlinarith) 8) h1
  have h3 : D.R.k ^ 8 ≤ D.host.g i := by exact_mod_cast h2
  have e3 : 5 ^ 8 ≤ D.R.k ^ 8 := Nat.pow_le_pow_left hk 8
  omega

theorem local_indices_pos (D : D7) (hg : ∀ i, 3 ≤ D.host.g i) :
    0 < idxPi D (D.host.g 0) (D.host.g 1) ∧ 0 < idxSig D (D.host.g 0) (D.host.g 1) := by
  have h := fun i => levelRowCard_holds D i (hg i)
  have hp : ∀ i, (0 : ℝ) < (D.host.g i : ℝ) := fun i => by exact_mod_cast (D.host.g_prime i).pos
  have c : ∀ i, 0 < idxColLoc (D.host.g i) D.R.k :=
    fun i => lt_of_lt_of_le (div_pos (pow_pos (hp i) _) two_pos) (h i).1
  have r : ∀ i, 0 < idxRowLoc (D.host.g i) D.R.k D.R.m :=
    fun i => lt_of_lt_of_le (div_pos (pow_pos (hp i) _) two_pos) (h i).2.2.1
  exact ⟨mul_pos (pow_pos (c 0) _) (pow_pos (c 1) _), mul_pos (pow_pos (r 0) _) (pow_pos (r 1) _)⟩

theorem dual_degree_pos (D : D7) (hg : ∀ i, 3 ≤ D.host.g i) : 0 < DstarD D := by
  unfold DstarD DstarP volY0
  exact mul_pos (mul_pos (D.vol_pos _) (local_indices_pos D hg).2) (Finset.prod_pos fun ρ _ => D.dsig_pos ρ)

theorem dual_degree_word_pos (D : D7) (hg : ∀ i, 3 ≤ D.host.g i) (hmk : 0 < massI D D.R.k) (u : D.what₂.Word) :
    0 < duStarU D u := by
  unfold duStarU duStarP
  exact mul_pos (mul_pos hmk (local_indices_pos D hg).1)
    (Finset.prod_pos fun ρ _ => dim_weyl_pos_of_strictAnti _ (column_param_strictAnti D u ρ))

theorem one_le_scale_length (sc : Scale) : 1 ≤ sc.L := by
  show 1 ≤ sc.x ^ sc.eps
  exact Real.one_le_rpow sc.one_lt_alt.le sc.eps_pos.le

theorem lower_bound_antitone_const (D : D7) (sc : Scale) (C C' : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (h : C ≤ C') :
    lowB D sc C' w ≤ lowB D sc C w := by
  unfold lowB
  have hL := one_le_scale_length sc
  have : 0 ≤ sc.L + (D.R.m : ℝ) ^ 2 * sc.L / D.R.k := by positivity
  have := mul_le_mul_of_nonneg_right h this
  linarith

theorem weylLaw_mono_const (D : D7) (sc : Scale) (C0 C C' : ℝ) (h : C ≤ C') (h5 : Conclusion5 D sc C0 C) : Conclusion5 D sc C0 C' := by
  intro Δ w hB u
  obtain ⟨h1, h2⟩ := h5 Δ w hB u
  have hL := one_le_scale_length sc
  refine ⟨le_trans (lower_bound_antitone_const D sc C C' w h) h1, le_trans h2 ?_⟩
  have : (0 : ℝ) ≤ (D.R.m : ℝ) * sc.L := by positivity
  have := mul_le_mul_of_nonneg_right h this
  linarith

theorem thick_places_corollary_of_any_translate (D : D7) (sc : Scale) (C0 C5 C : ℝ) (h5 : Conclusion5 D sc C0 C5) (hC : C5 + 1 ≤ C) (hC1 : 1 ≤ C)
    (hmk : 0 < massI D D.R.k) : TorusPairsWithVariant D sc C0 C := by
  intro Δ w hB Γ hΓ u hT1 hT2
  have hg := three_le_level_of_section_B D sc C0 Δ w hB
  have hD := dual_degree_pos D hg
  have hd := dual_degree_word_pos D hg hmk u
  have hk := D.R.k_ge
  have hf : 1 ≤ D.R.f := by
    have : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
    omega
  have hfk : 2 * D.R.f ≤ 2 ^ D.R.k := by
    have h1 : D.R.f ≤ D.R.k := D.R.f_le_k
    have h2 : D.R.k - 1 < 2 ^ (D.R.k - 1) := Nat.lt_two_pow_self
    have h3 : 2 ^ D.R.k = 2 * 2 ^ (D.R.k - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  have hfR : (0 : ℝ) < D.R.f := by exact_mod_cast hf
  have hkR : (0 : ℝ) < D.R.k := by exact_mod_cast (by omega : 0 < D.R.k)
  have hX : Real.exp (logXuD D u) ^ (D.R.f * D.R.k) = DstarD D / duStarU D u := by
    rw [← Real.exp_nat_mul]
    unfold logXuD logXu
    push_cast
    rw [show (D.R.f : ℝ) * D.R.k * (1 / ((D.R.f : ℝ) * D.R.k) * Real.log (DstarD D / duStarU D u)) =
      Real.log (DstarD D / duStarU D u) by field_simp]
    exact Real.exp_log (div_pos hD hd)
  obtain ⟨l1, l2⟩ := h5 Δ w hB u
  have hT : (2 : ℝ) ≤ ((D.mem u).A.T : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.two_le
  obtain ⟨c1, c2, c3, c4⟩ := Formalism.HermitianLattices.GenusMassVolumes.mass_corollary D.R.f D.R.k ((D.mem u).A.T : ℝ) (Real.exp (logXuD D u)) Γ
    (DstarD D) (duStarU D u) _ (lowB D sc C5 w) (C5 * D.R.m * sc.L) hf (by omega) hfk hT (Real.exp_pos _) hΓ hD hd hX
    hT1 hT2 rfl (by rw [Real.log_exp]; exact l1) (by rw [Real.log_exp]; exact l2)
  have hL := one_le_scale_length sc
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hlog2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hΓ0 : 0 < Γ := by linarith
  have eΓ : Γ ^ (-(2 : ℝ)) = (Γ⁻¹) ^ 2 := by
    rw [Real.rpow_neg hΓ0.le, Real.rpow_two, inv_pow]
  refine ⟨?_, ?_, ?_⟩
  · rw [eΓ]
    have hY : 0 < DstarD D * (Γ⁻¹) ^ 2 := by positivity
    have b1 : 1 / 2 ≤ duStarU D u * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f / (DstarD D * (Γ⁻¹) ^ 2) := by
      rw [le_div_iff₀ hY]; linarith
    have b2 : duStarU D u * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f / (DstarD D * (Γ⁻¹) ^ 2) ≤ Real.exp 1 := by
      rw [div_le_iff₀ hY]; exact c2
    rw [abs_le]
    constructor
    · have := Real.log_le_log (by norm_num) b1
      rw [one_div, Real.log_inv] at this
      linarith
    · have := Real.log_le_log (by linarith) b2
      rw [Real.log_exp] at this
      linarith
  · have : (1 : ℝ) ≤ (D.R.m : ℝ) * sc.L := by nlinarith
    have h2 : (C5 + 1) * ((D.R.m : ℝ) * sc.L) ≤ C * ((D.R.m : ℝ) * sc.L) :=
      mul_le_mul_of_nonneg_right hC (by linarith)
    nlinarith
  · have := lower_bound_antitone_const D sc C5 C w (by linarith)
    linarith

theorem weylLawBounds_all (D : D7) (sc : Scale) (C0 C5 : ℝ) (h5 : Conclusion5 D sc C0 C5) (hmk : 0 < massI D D.R.k) :
    Conclusion5₂ D sc C0 (max (C5 + 1) 16) :=
  ⟨weylLaw_mono_const D sc C0 C5 _ (le_trans (by linarith) (le_max_left _ _)) h5,
    thick_places_corollary_of_any_translate D sc C0 C5 _ h5 (le_max_left _ _) (le_trans (by norm_num) (le_max_right _ _)) hmk,
    weylLawVariation_holds D sc C0 _ (le_max_right _ _)⟩

end Formalism.MainNotions.StandardLattice

namespace Formalism.MainNotions.StandardLattice

open NumberField Formalism.BasicNotions Finset

theorem standard_form_eq_telescope_form (K : Type) [Field K] [NumberField K] [StarRing K] (M : ℕ) :
    stdForm K M = Formalism.HermitianLatticesTheory.massTelescope_form K M := by
  rfl

theorem standard_lattice_eq_telescope_lattice (K : Type) [Field K] [NumberField K] (M : ℕ) :
    stdLat K M = Formalism.HermitianLatticesTheory.massTelescope_lat K M := by
  unfold stdLat Formalism.HermitianLatticesTheory.massTelescope_lat
  congr 1
  ext v
  simp [Pi.basisFun_apply]

theorem stdForm_symm (K : Type) [Field K] [NumberField K] [StarRing K] (M : ℕ) : (stdForm K M).IsSymm := by
  rw [standard_form_eq_telescope_form]; exact Formalism.HermitianLatticesTheory.massTelescope_symm K M

theorem stdLat_ortho (K : Type) [Field K] [NumberField K] [StarRing K] (M : ℕ) :
    Formalism.HermitianLatticesTheory.IsOrthoLattice (stdForm K M) (stdLat K M) M := by
  rw [standard_form_eq_telescope_form, standard_lattice_eq_telescope_lattice]; exact Formalism.HermitianLatticesTheory.massTelescope_ortho K M

theorem massI_pos (D : D7) (M : ℕ) : 0 < massI D M := by
  let _ := D.host.cmStar
  unfold massI
  rw [standard_form_eq_telescope_form, standard_lattice_eq_telescope_lattice]
  exact Formalism.HermitianLatticesTheory.massTelescope_std_pos D.host.E D.sp.cm.cmUnram M

theorem standardMassRatio_of_modelMassRatio (h : SiegelMassRatioModels) : SiegelMassRatioCM := by
  intro K _ _ _ hK M hM
  exact h K hK M hM _ _ _ _ _ _ (stdForm_symm K M) (stdForm_symm K (M - 1)) (stdLat_ortho K M) (stdLat_ortho K (M - 1))

theorem massRatio_of_modelMassRatio (D : D7) (h : SiegelMassRatioModels) : MassRatio₂ D := mass_ratio_of_general D (standardMassRatio_of_modelMassRatio h)

def DefiniteVolumeEqMass (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ W : HSpace D.host.E, W.SigOK → (∀ τ, W.sig τ = (W.rank, 0)) → D.vol W = massI D W.rank

theorem massRatio_of_definiteVolume (D : D7) (h2 : Conclusion2 D) (hv : DefiniteVolumeEqMass D) : MassRatio₂ D := by
  let _ := D.host.cmStar
  intro M hM
  let W : HSpace D.host.E := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral M
  have hW : W.SigOK := Formalism.BasicNotions.Examples₂.posSpace_sigOK _ M
  obtain ⟨x, -, W', ι, -, -, hW', hs', hr⟩ := h2 W M 0 hW (fun _ => rfl) hM true (by simp; omega)
  have hrk : W'.rank = M - 1 := by
    have := Formalism.BasicNotions.sig_sum W' hW' D.host.φ₀
    rw [hs' D.host.φ₀] at this
    simpa using this.symm
  have e1 : D.vol W = massI D M := hv W hW (fun _ => rfl)
  have e2 : D.vol W' = massI D (M - 1) := by
    rw [← hrk]
    exact hv W' hW' (fun τ => by rw [hs' τ, hrk]; rfl)
  rw [← e1, ← e2]
  exact hr

theorem volume_eq_mass_of_definite (D : D7) (h2 : Conclusion2 D) (hv : DefiniteVolumeEqMass D) : VolumeEqMass₂ D := by
  let _ := D.host.cmStar
  have h2b := massRatio_of_definiteVolume D h2 hv
  refine ⟨hv, ?_⟩
  intro W P Q
  induction Q generalizing W with
  | zero =>
    intro hW hs _
    have hrk : W.rank = P := by
      have := Formalism.BasicNotions.sig_sum W hW D.host.φ₀
      rw [hs D.host.φ₀] at this
      simpa using this.symm
    rw [Nat.add_zero, ← hrk]
    exact hv W hW (fun τ => by rw [hs τ, hrk])
  | succ Q ih =>
    intro hW hs hP
    have hrk : W.rank = P + (Q + 1) := by
      have := Formalism.BasicNotions.sig_sum W hW D.host.φ₀
      rw [hs D.host.φ₀] at this
      simpa using this.symm
    obtain ⟨x, -, W', ι, -, -, hW', hs', hr⟩ := h2 W P (Q + 1) hW hs (by omega) false (by simp)
    have e2 : D.vol W' = massI D (P + Q) := ih W' hW' (fun τ => by rw [hs' τ]; simp) hP
    have hb := h2b (P + (Q + 1)) (by omega)
    rw [hrk, ← hb, e2] at hr
    have e3 : P + (Q + 1) - 1 = P + Q := by omega
    rw [e3] at hr
    have hpos := massI_pos D (P + Q)
    field_simp at hr
    exact hr

section Landherr

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def OrthoFam (W : HSpace E) (n : ℕ) : Prop :=
  ∃ e : Fin n → W.V, ∀ i j, W.hT (e i) (e j) = if i = j then 1 else 0

theorem exists_orthogonal_lattice (W : HSpace E) (h : OrthoFam W W.rank) :
    ∃ L : Submodule (𝓞 E) W.V, Formalism.HermitianLatticesTheory.IsOrthoLattice W.hT L W.rank := by
  obtain ⟨e, he⟩ := h
  have hli : LinearIndependent E e := by
    rw [linearIndependent_iff']
    intro s c hc j hj
    have h1 := congrArg (W.hT (e j)) hc
    rw [map_sum, map_zero] at h1
    simp only [map_smul, he, smul_eq_mul, mul_ite, mul_one, mul_zero] at h1
    rw [Finset.sum_ite_eq s j] at h1
    simpa [hj] using h1
  refine ⟨Submodule.span (𝓞 E) (Set.range e), e, hli, ?_, rfl, he⟩
  exact hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, W.rank_eq])

end Landherr

def LandherrSmall (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ W : HSpace D.host.E, W.SigOK → (∀ τ, W.sig τ = (W.rank, 0)) → W.rank ≤ 2 → OrthoFam W W.rank

theorem landherr_of_small (D : D7) (h2 : Conclusion2 D) (hs : LandherrSmall D) :
    letI := D.host.cmStar
    ∀ (n : ℕ) (W : HSpace D.host.E), W.rank = n → W.SigOK → (∀ τ, W.sig τ = (W.rank, 0)) → OrthoFam W W.rank := by
  let _ := D.host.cmStar
  intro n
  induction n with
  | zero => intro W hn hW hsig; exact hs W hW hsig (by omega)
  | succ n ih =>
    intro W hn hW hsig
    by_cases h3 : W.rank ≤ 2
    · exact hs W hW hsig h3
    · obtain ⟨x, hx, W', ι, hι, hr, hW', hs', -⟩ := h2 W W.rank 0 hW hsig (by omega) true (by simp; omega)
      have hrk : W'.rank = n := by
        have := Formalism.BasicNotions.sig_sum W' hW' D.host.φ₀
        rw [hs' D.host.φ₀] at this
        simp at this
        omega
      obtain ⟨e', he'⟩ := ih W' hrk hW' (fun τ => by rw [hs' τ, hrk, hn]; simp)
      have hrk' : W.rank = W'.rank + 1 := by omega
      rw [hrk']
      have hxι : ∀ y, W.hT x (ι y) = 0 := by
        intro y
        have : ι y ∈ LinearMap.ker (W.hT x) := hr ▸ LinearMap.mem_range_self ι y
        exact this
      have hιx : ∀ y, W.hT (ι y) x = 0 := by
        intro y
        rw [← W.herm.eq x (ι y), hxι, map_zero]
      refine ⟨Fin.cons x (fun i => ι (e' i)), fun i j => ?_⟩
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => simpa using hx
        | succ j => simp [hxι, (Fin.succ_ne_zero j).symm]
      | succ i =>
        induction j using Fin.cases with
        | zero => simp [hιx, Fin.succ_ne_zero i]
        | succ j => simp [hι _ _, he']

theorem trivialClass_of_landherr (D : D7) (h2 : Conclusion2 D) (hs : LandherrSmall D) : OrthonormalLatticeRankK D := by
  let _ := D.host.cmStar
  have hpos := Formalism.BasicNotions.baseSpace_posDef D.R D.host.F D.sp
  have h := exists_orthogonal_lattice (D.sp.X 0) (landherr_of_small D h2 hs _ (D.sp.X 0) rfl (D.sp.X_sig 0) hpos)
  rw [D.sp.rank0] at h
  exact h

theorem levelStatement_of_landherrSmall (D : D7) (Lv : LevelData D) (C3 : ℝ)
    (hfin : Module.finrank ℚ D.host.E = 2 * D.R.f)
    (hp : Conclusion4p D Lv) (hn : ClassNumberFormula₂ D Lv) (hs : LandherrSmall D) : ThetaChernBoundOfLastLine D Lv C3 :=
  fun h2 h3 h17 => levelStatement_of_classes D Lv C3 hfin hp hn (trivialClass_of_landherr D h2.1 hs) h2 h3 h17

end Formalism.MainNotions.StandardLattice

namespace Formalism.MainNotions.StandardLattice

open NumberField Formalism.BasicNotions Finset

theorem volumeMass_all_of_modelMassRatio (h : SiegelMassRatioModels) : MassVolumeBoundsAll := ⟨standardMassRatio_of_modelMassRatio h, h, cmField_unramified_massIdentity⟩

theorem stmt2All_of_mod (D : D7) (h : SiegelMassRatioModels) : AbsoluteConstantSecondPart D := fun _ => volumeMass_all_of_modelMassRatio h

theorem volumeMass_of_definiteVolume (D : D7) (h2 : Conclusion2 D) (hv : DefiniteVolumeEqMass D) : VolumeMass D :=
  ⟨h2, volume_eq_mass_of_definite D h2 hv, massRatio_of_definiteVolume D h2 hv, massIdentity_holds D⟩

theorem hostDegree_holds (D : D7) : PrimeSumLogBound D := by
  exact hostDegree_of_finrank D (finrank_host D)

theorem levelStatement_remaining (D : D7) (Lv : LevelData D) (C3 : ℝ) (hp : Conclusion4p D Lv) (hn : ClassNumberFormula₂ D Lv) (hs : LandherrSmall D) :
    ThetaChernBoundOfLastLine D Lv C3 := by
  exact levelStatement_of_landherrSmall D Lv C3 (finrank_host D) hp hn hs

theorem familyLevel_remaining {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C3 : ℝ)
    (hp : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Conclusion4p (Fm.D x i) (Fm.ex x hx i).lev)
    (hn : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev)
    (hs : ∀ x (i : Fm.Ix x), LandherrSmall (Fm.D x i)) : LiftNormFamilyStatement Fm C3 :=
  fun h2 h3 h17 x hx i =>
    levelStatement_remaining (Fm.D x i) (Fm.ex x hx i).lev C3 (hp x hx i) (hn x hx i) (hs x i) (h2 x i) (h3 x i) (h17 x hx i)

theorem familyMass_of_definiteVolume {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (h2 : ∀ x (i : Fm.Ix x), Conclusion2 (Fm.D x i)) (hv : ∀ x (i : Fm.Ix x), DefiniteVolumeEqMass (Fm.D x i)) : DeterminantValueFamily Fm :=
  fun _ _ x i => volumeMass_of_definiteVolume (Fm.D x i) (h2 x i) (hv x i)

theorem familyMass_all_of_modelRatio {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : SiegelMassRatioModels) : FamilyMassTheoremAll Fm := fun _ => volumeMass_all_of_modelMassRatio h

end Formalism.MainNotions.StandardLattice

namespace Formalism.MainNotions.StandardLattice

open NumberField Formalism.BasicNotions Finset

section Transport

open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

variable {K V V' : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']

def tMap (e : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V) : Submodule (𝓞 K) V' :=
  M.map ((e : V →ₗ[K] V').restrictScalars (𝓞 K))

theorem mem_tMap (e : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V) (y : V') : y ∈ tMap e M ↔ e.symm y ∈ M := by
  unfold tMap
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hy
    exact ⟨e.symm y, hy, by simp⟩

theorem tMap_symm (e : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V) : tMap e.symm (tMap e M) = M := by
  ext y
  rw [mem_tMap, mem_tMap]
  simp

theorem tMap_symm' (e : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V') : tMap e (tMap e.symm M) = M := by
  ext y
  rw [mem_tMap, mem_tMap]
  simp

theorem gmap_eq_tMap (g : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) : gmap g M = tMap g M := rfl

def cj (e : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) : V' ≃ₗ[K] V' := (e.symm.trans g).trans e

theorem cj_cj (e : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) : cj e.symm (cj e g) = g := by
  ext x
  simp [cj]

theorem cj_cj' (e : V ≃ₗ[K] V') (g : V' ≃ₗ[K] V') : cj e (cj e.symm g) = g := by
  ext x
  simp [cj]

theorem tMap_cj (e : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) :
    tMap (cj e g) (tMap e M) = tMap e (tMap g M) := by
  ext y
  simp only [mem_tMap, cj, LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.symm_symm,
    LinearEquiv.symm_apply_apply]

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem isoSymm (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y) :
    ∀ x y, h (e.symm x) (e.symm y) = h' x y := by
  intro x y
  have := he (e.symm x) (e.symm y)
  simpa using this.symm

theorem cj_isom (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y) (g : V ≃ₗ[K] V) (hg : g ∈ isom h) :
    cj e g ∈ isom h' := by
  have hg' : ∀ x y, h (g x) (g y) = h x y := hg
  intro x y
  show h' (e (g (e.symm x))) (e (g (e.symm y))) = h' x y
  rw [he, hg', isoSymm e he]

theorem tMap_loc (e : V ≃ₗ[K] V') (p : Ideal (𝓞 K)) (M : Submodule (𝓞 K) V) :
    tMap e (loc (K := K) p M) = loc (K := K) p (tMap e M) := by
  ext y
  rw [mem_tMap]
  show (∃ s ∈ hcompl (K := K) p, s • e.symm y ∈ M) ↔ ∃ s ∈ hcompl (K := K) p, s • y ∈ tMap e M
  simp only [mem_tMap]
  have hs : ∀ s : 𝓞 K, e.symm (s • y) = s • e.symm y := fun s => e.symm.toLinearMap.map_smul_of_tower s y
  simp only [hs]

theorem tMap_lattice (e : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V) (hM : Submodule.IsLattice K M) :
    Submodule.IsLattice K (tMap e M) where
  fg := hM.fg.map _
  span_eq_top := by
    have h1 : ((tMap e M : Submodule (𝓞 K) V') : Set V') = (e : V →ₗ[K] V') '' (M : Set V) := by
      unfold tMap; rw [Submodule.map_coe]; rfl
    rw [h1, Submodule.span_image, hM.span_eq_top, Submodule.map_top]
    exact LinearEquiv.range e

theorem tMap_genus (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y) (L M : Submodule (𝓞 K) V)
    (hM : M ∈ genus h L) : tMap e M ∈ genus h' (tMap e L) := by
  refine ⟨tMap_lattice e M hM.1, fun p hp => ?_⟩
  obtain ⟨g, hg, hgL⟩ := hM.2 p hp
  refine ⟨cj e g, cj_isom e he g hg, ?_⟩
  rw [gmap_eq_tMap] at hgL ⊢
  rw [← tMap_loc, tMap_cj, hgL, tMap_loc]

theorem tMap_inj (e : V ≃ₗ[K] V') : Function.Injective (tMap (K := K) e) := by
  intro M N hMN
  calc M = tMap e.symm (tMap e M) := (tMap_symm e M).symm
    _ = tMap e.symm (tMap e N) := by rw [hMN]
    _ = N := tMap_symm e N

theorem tMap_reps (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y) (L : Submodule (𝓞 K) V)
    (s : Finset (Submodule (𝓞 K) V)) (hs : IsClassReps h L s) :
    IsClassReps h' (tMap e L) (s.map ⟨tMap e, tMap_inj e⟩) := by
  refine ⟨fun M' hM' => ?_, fun M' hM' => ?_⟩
  · obtain ⟨M, hM, rfl⟩ := Finset.mem_map.1 hM'
    exact tMap_genus e he L M (hs.1 M hM)
  · have h1 : tMap e.symm M' ∈ genus h L := by
      have := tMap_genus e.symm (isoSymm e he) _ _ hM'
      rwa [tMap_symm] at this
    obtain ⟨N, ⟨hN, g, hg, hgN⟩, huniq⟩ := hs.2 _ h1
    refine ⟨tMap e N, ⟨Finset.mem_map.2 ⟨N, hN, rfl⟩, cj e g, cj_isom e he g hg, ?_⟩, ?_⟩
    · rw [gmap_eq_tMap] at hgN ⊢
      rw [tMap_cj, hgN, tMap_symm']
    · rintro N'' ⟨hN'', g'', hg'', hgN''⟩
      obtain ⟨N2, hN2, rfl⟩ := Finset.mem_map.1 hN''
      have : N2 = N := by
        refine huniq N2 ⟨hN2, cj e.symm g'', cj_isom e.symm (isoSymm e he) g'' hg'', ?_⟩
        rw [gmap_eq_tMap] at hgN'' ⊢
        have h2 := tMap_cj e.symm g'' (tMap e N2)
        rw [tMap_symm] at h2
        show tMap (cj e.symm g'') N2 = tMap e.symm M'
        rw [h2]
        exact congrArg _ hgN''
      rw [this]
      rfl

theorem card_autL (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y) (M : Submodule (𝓞 K) V) :
    Nat.card (autL h M) = Nat.card (autL h' (tMap e M)) := by
  refine Nat.card_congr
    { toFun := fun g => ⟨cj e g.1, cj_isom e he g.1 g.2.1, ?_⟩
      invFun := fun g => ⟨cj e.symm g.1, cj_isom e.symm (isoSymm e he) g.1 g.2.1, ?_⟩
      left_inv := fun g => Subtype.ext (cj_cj e g.1)
      right_inv := fun g => Subtype.ext (cj_cj' e g.1) }
  · have h2 := g.2.2
    rw [gmap_eq_tMap] at h2 ⊢
    rw [tMap_cj, h2]
  · have h2 := g.2.2
    rw [gmap_eq_tMap] at h2 ⊢
    have h3 := tMap_cj e.symm g.1 (tMap e M)
    rw [tMap_symm, h2, tMap_symm] at h3
    exact h3

theorem mass_transport (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y) (L : Submodule (𝓞 K) V)
    (hB1 : ∃ s', IsClassReps h' (tMap e L) s')
    (hB2 : ∀ s', IsClassReps h' (tMap e L) s' →
      mass h' (tMap e L) = ∑ M ∈ s', ((Nat.card (autL h' M) : ℕ) : ℝ)⁻¹) :
    mass h L = mass h' (tMap e L) := by
  obtain ⟨s', hs'⟩ := hB1
  have hs : ∃ s, IsClassReps h L s := by
    have := tMap_reps e.symm (isoSymm e he) _ s' hs'
    rw [tMap_symm] at this
    exact ⟨_, this⟩
  rw [massBasic_mass_eq h L hs, hB2 _ (tMap_reps e he L _ hs.choose_spec), Finset.sum_map]
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [card_autL e he M]
  rfl

end Transport

theorem mass_ortho (K : Type) [Field K] [NumberField K] [StarRing K] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (n : ℕ)
    (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (ho : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) :
    Formalism.HermitianLatticesTheory.mass h L = Formalism.HermitianLatticesTheory.mass (stdForm K n) (stdLat K n) := by
  obtain ⟨b, hli, hsp, hL, hon⟩ := ho
  let B : Module.Basis (Fin n) K V := Module.Basis.mk hli hsp.ge
  have hB : ∀ i, B i = b i := fun i => Module.Basis.mk_apply hli hsp.ge i
  let e : V ≃ₗ[K] (Fin n → K) := B.equivFun
  have he : ∀ x y, stdForm K n (e x) (e y) = h x y := by
    intro x y
    conv_rhs => rw [← B.sum_repr x, ← B.sum_repr y]
    simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hB, hon,
      RingHom.id_apply, mul_ite, mul_one, mul_zero]
    show ∑ i, star (e x i) * e y i = _
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [e, Module.Basis.equivFun_apply, starRingEnd_apply, mul_comm]
  have heB : ∀ i, e (b i) = Pi.single i 1 := by
    intro i
    rw [← hB i]
    funext j
    simp [e, Pi.single_apply, eq_comm]
  have hT : tMap e L = stdLat K n := by
    unfold tMap stdLat
    rw [hL, Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      exact (heB i).symm
    · rintro ⟨i, rfl⟩
      refine ⟨b i, ⟨i, rfl⟩, ?_⟩
      exact heB i
  have hMB := Formalism.HermitianLatticesTheory.final_massBasic K (Fin n → K) (stdForm K n) (stdForm_symm K n)
    (by rw [standard_form_eq_telescope_form]; exact Formalism.HermitianLatticesTheory.massTelescope_def K hK n) (stdLat K n)
    (by rw [standard_lattice_eq_telescope_lattice]; exact Formalism.HermitianLatticesTheory.massTelescope_isLattice K n)
  rw [← hT] at hMB ⊢
  exact mass_transport e he L hMB.1 hMB.2.1

theorem modelMassRatio_of_standardMassRatio (hA : SiegelMassRatioCM) : SiegelMassRatioModels := by
  intro K _ _ _ hK M hM V V' _ _ _ _ _ _ _ _ h h' L L' _ _ ho ho'
  rw [mass_ortho K hK M V h L ho, mass_ortho K hK (M - 1) V' h' L' ho']
  exact hA K hK M hM

theorem modelMassRatio_iff_standard : SiegelMassRatioModels ↔ SiegelMassRatioCM := by
  exact ⟨standardMassRatio_of_modelMassRatio, modelMassRatio_of_standardMassRatio⟩

theorem volumeMass_all_of_standardMassRatio (h : SiegelMassRatioCM) : MassVolumeBoundsAll := by
  exact volumeMass_all_of_modelMassRatio (modelMassRatio_of_standardMassRatio h)

end Formalism.MainNotions.StandardLattice

namespace Formalism.MainNotions.StandardLattice

open NumberField Formalism.BasicNotions Finset

structure ColCount (D : D7) (u : D.what₂.Word) where

  ι : Type
  [fι : Fintype ι]

  Γ : ι → Type
  [grp : ∀ i, Group (Γ i)]
  [fin : ∀ i, Fintype (Γ i)]

  Y : Type
  [fY : Fintype Y]
  [act : ∀ i, MulAction (Γ i) Y]

  mass_eq : massI D D.R.k = ∑ i, ((Fintype.card (Γ i) : ℝ))⁻¹

  card_Y : (Fintype.card Y : ℝ) =
    idxPi D (D.host.g 0) (D.host.g 1) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f

  cls_eq : (D.mem u).C.cls 0 ≃ Σ i, MulAction.orbitRel.Quotient (Γ i) Y

  stab_eq : ∀ i (y : Y), MulAction.stabilizer (Γ i) y ≃*
    (D.mem u).C.stab 0 (cls_eq.symm ⟨i, Quotient.mk'' y⟩)

attribute [instance] ColCount.fι ColCount.grp ColCount.fin ColCount.fY ColCount.act

theorem classNumber_of_orbitCount (D : D7) (Lv : LevelData D) (hd : SmallOrderPrimeLogSumBound D Lv) (h4g : OrthonormalLatticeRankK D)
    (X : OrthonormalLatticeRankK D → (∀ i, SplitsF D (D.host.g i)) → ∀ u : D.what₂.Word, SplitsF D (D.mem u).A.T →
      Nonempty (ColCount D u)) :
    ClassNumberFormula₂ D Lv := by
  intro hg hs u hT
  obtain ⟨X⟩ := X h4g hs u hT
  have hz := hd hg u
  have hfree : ∀ (i : X.ι) (y : X.Y), MulAction.stabilizer (X.Γ i) y = ⊥ := by
    intro i y
    have := hz (X.cls_eq.symm ⟨i, Quotient.mk'' y⟩)
    have h2 : Subsingleton (MulAction.stabilizer (X.Γ i) y) := (X.stab_eq i y).toEquiv.subsingleton
    exact Subgroup.eq_bot_of_subsingleton _
  have h := Formalism.HermitianLattices.GenusMassVolumes.rank_count_bis X.ι X.Γ X.Y hfree
  rw [Nat.card_congr X.cls_eq, Nat.card_sigma]
  push_cast
  rw [h, ← X.mass_eq, X.card_Y]
  ring

end Formalism.MainNotions.StandardLattice

namespace Formalism.MainNotions.StandardLattice

open NumberField Formalism.BasicNotions Finset

theorem vandermonde_fin_eq_nat (x : ℕ → ℝ) (N : ℕ) : vand (fun i : Fin N => x i.val) = Formalism.LogVandermondeBounds.StandardLattice.vandN x N := by
  unfold vand Formalism.LogVandermondeBounds.StandardLattice.vandN
  rw [← Fin.prod_univ_eq_prod_range (fun i => ∏ j ∈ Ico (i + 1) N, (x i - x j))]
  refine Finset.prod_congr rfl (fun a _ => ?_)
  try dsimp only
  have hI : Ico ((a : ℕ) + 1) N = (univ.filter (fun b : Fin N => a < b)).map Fin.valEmbedding := by
    ext j
    simp only [Finset.mem_Ico, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨j, h2⟩, Fin.lt_iff_val_lt_val.mpr (show (a : ℕ) < j by omega), rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨Fin.lt_iff_val_lt_val.mp hb, b.isLt⟩
  rw [hI, Finset.prod_map]
  try rfl

theorem dim_weyl_fin_eq_nat (x : ℕ → ℝ) (N : ℕ) : dimV (fun i : Fin N => x i.val) = Formalism.LogVandermondeBounds.StandardLattice.dimVN x N := by
  show vand (fun i : Fin N => x i.val) / facProd N =
    Formalism.LogVandermondeBounds.StandardLattice.vandN x N / ∏ i ∈ range N, ((i.factorial : ℕ) : ℝ)
  rw [vandermonde_fin_eq_nat]
  try rfl

theorem column_param_eq_fun (D : D7) (u : D.what₂.Word) (ρ : D.what₂.Tau) :
    uColR D u ρ = fun i : Fin D.R.k => uN D u ρ i.val := by
  exact funext (column_param_apply D u ρ)

theorem line_param_eq_fun (D : D7) (ρ : D.what₂.Tau) :
    rowLam D ρ = fun a : Fin (D.R.k - 1 + D.R.m) => Formalism.LogVandermondeBounds.StandardLattice.rowPar D.R.k (vN D ρ) (bN D ρ) a.val := by
  exact funext (line_param_apply D ρ)

theorem degree_pos_alt (D : D7) : 0 < D.R.f := by
  show 0 < 2 * D.R.ord
  have h1 := D.R.m_le_f
  have h2 := D.R.two_le_m
  omega

def tauOf (D : D7) (n : ℕ) : D.what₂.Tau :=
  (Fintype.equivFinOfCardEq D.what₂.card_Tau).symm ⟨n % D.R.f, Nat.mod_lt _ (degree_pos_alt D)⟩

theorem prod_over_tau_eq_prod_range (D : D7) (F : D.what₂.Tau → ℝ) : ∏ ρ, F ρ = ∏ n ∈ range D.R.f, F (tauOf D n) := by
  rw [← Fin.prod_univ_eq_prod_range (fun n => F (tauOf D n))]
  refine Fintype.prod_equiv (Fintype.equivFinOfCardEq D.what₂.card_Tau) _ _ (fun ρ => ?_)
  show F ρ = F (tauOf D (Fintype.equivFinOfCardEq D.what₂.card_Tau ρ))
  congr 1
  unfold tauOf
  rw [eq_comm, Equiv.symm_apply_eq]
  apply Fin.ext
  exact Nat.mod_eq_of_lt (Fin.isLt _)

theorem sum_over_tau_eq_sum_range (D : D7) (F : D.what₂.Tau → ℝ) : ∑ ρ, F ρ = ∑ n ∈ range D.R.f, F (tauOf D n) := by
  rw [← Fin.sum_univ_eq_sum_range (fun n => F (tauOf D n))]
  refine Fintype.sum_equiv (Fintype.equivFinOfCardEq D.what₂.card_Tau) _ _ (fun ρ => ?_)
  show F ρ = F (tauOf D (Fintype.equivFinOfCardEq D.what₂.card_Tau ρ))
  congr 1
  unfold tauOf
  rw [eq_comm, Equiv.symm_apply_eq]
  apply Fin.ext
  exact Nat.mod_eq_of_lt (Fin.isLt _)

theorem rho_sub_eq_card_opposite {N : ℕ} (s : Fin N → Bool) (a b : Fin N) (hab : a < b) (hs : s a = s b) :
    rhoN s a - rhoN s b = ((univ.filter (fun c : Fin N => a < c ∧ c < b ∧ s c ≠ s a)).card : ℝ) := by
  unfold rhoN
  have e1 := card_split_lemma
    (univ.filter (fun x : Fin N => a < x ∧ s x ≠ s a)) (fun x => x < b)
  have e2 := card_split_lemma
    (univ.filter (fun x : Fin N => x < b ∧ s x ≠ s b)) (fun x => a < x)
  have m1 : (univ.filter (fun x : Fin N => a < x ∧ s x ≠ s a)).filter (fun x => x < b) =
      univ.filter (fun c : Fin N => a < c ∧ c < b ∧ s c ≠ s a) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have m2 : (univ.filter (fun x : Fin N => a < x ∧ s x ≠ s a)).filter (fun x => ¬ x < b) =
      univ.filter (fun x : Fin N => b < x ∧ s x ≠ s b) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, hsx⟩, hxb⟩
      refine ⟨lt_of_le_of_ne (not_lt.mp hxb) ?_, fun h => hsx (h.trans hs.symm)⟩
      rintro rfl
      exact hsx hs.symm
    · rintro ⟨hbx, hsx⟩
      exact ⟨⟨hab.trans hbx, fun h => hsx (h.trans hs)⟩, not_lt.mpr hbx.le⟩
  have m3 : (univ.filter (fun x : Fin N => x < b ∧ s x ≠ s b)).filter (fun x => a < x) =
      univ.filter (fun c : Fin N => a < c ∧ c < b ∧ s c ≠ s a) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hxb, hsx⟩, hax⟩
      exact ⟨hax, hxb, fun h => hsx (h.trans hs)⟩
    · rintro ⟨hax, hxb, hsx⟩
      exact ⟨⟨hxb, fun h => hsx (h.trans hs.symm)⟩, hax⟩
  have m4 : (univ.filter (fun x : Fin N => x < b ∧ s x ≠ s b)).filter (fun x => ¬ a < x) =
      univ.filter (fun x : Fin N => x < a ∧ s x ≠ s a) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, hsx⟩, hax⟩
      refine ⟨lt_of_le_of_ne (not_lt.mp hax) ?_, fun h => hsx (h.trans hs)⟩
      rintro rfl
      exact hsx hs
    · rintro ⟨hxa, hsx⟩
      exact ⟨⟨hxa.trans hab, fun h => hsx (h.trans hs.symm)⟩, not_lt.mpr hxa.le⟩
  rw [m1, m2] at e1
  rw [m3, m4] at e2
  rw [← e1, ← e2]
  push_cast
  ring

theorem card_opposite_sign_between (D : D7) (a b : Fin (D.R.k - 1 + D.R.m)) :
    (univ.filter (fun c : Fin (D.R.k - 1 + D.R.m) => a < c ∧ c < b ∧ rowSgn D c ≠ rowSgn D a)).card =
      Formalism.LogVandermondeBounds.StandardLattice.nBetween D.R.k a.val b.val := by
  unfold Formalism.LogVandermondeBounds.StandardLattice.nBetween
  have hI : (Ioo (a : ℕ) b).filter
      (fun c => Formalism.LogVandermondeBounds.StandardLattice.plusSign D.R.k c ≠ Formalism.LogVandermondeBounds.StandardLattice.plusSign D.R.k a) =
      (univ.filter (fun c : Fin (D.R.k - 1 + D.R.m) => a < c ∧ c < b ∧ rowSgn D c ≠ rowSgn D a)).map
        Fin.valEmbedding := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨j, lt_trans h2 b.isLt⟩, ⟨Fin.lt_iff_val_lt_val.mpr h1, Fin.lt_iff_val_lt_val.mpr h2, ?_⟩, rfl⟩
      rw [line_sign_apply, line_sign_apply]
      exact h3
    · rintro ⟨c, ⟨h1, h2, h3⟩, rfl⟩
      refine ⟨⟨Fin.lt_iff_val_lt_val.mp h1, Fin.lt_iff_val_lt_val.mp h2⟩, ?_⟩
      rw [line_sign_apply, line_sign_apply] at h3
      exact h3
  rw [hI, Finset.card_map]

theorem count_plus_eq (D : D7) : pY D = D.R.k - 1 + D.R.m / 2 := by
  have := D.R.rS_two; have := D.R.k_ge
  simp only [pY, Ranks.sigY0]; omega

theorem count_minus_eq (D : D7) : qY D = D.R.m / 2 := by
  have := D.R.rS_two
  simp only [qY, Ranks.sigY0]; omega

theorem rank_eq_sum (D : D7) : D.R.r = D.R.k - 1 + D.R.m := by
  show D.R.k + D.R.m - 1 = D.R.k - 1 + D.R.m
  have := D.R.m_add_three_le_k
  omega

theorem formal_degree_line_eq (D : D7) (ρ : D.what₂.Tau) :
    dTau (rowSgn D) (rowLam D ρ) =
      Formalism.LogVandermondeBounds.StandardLattice.dTau D.R.k D.R.m (Formalism.LogVandermondeBounds.StandardLattice.rowPar D.R.k (vN D ρ) (bN D ρ)) := by
  unfold dTau Formalism.LogVandermondeBounds.StandardLattice.dTau
  rw [count_plus_line_sign, count_minus_line_sign, count_plus_eq, count_minus_eq]
  unfold facProd
  congr 1
  set lam := Formalism.LogVandermondeBounds.StandardLattice.rowPar D.R.k (vN D ρ) (bN D ρ) with hlam
  set N := D.R.k - 1 + D.R.m with hN
  rw [← Fin.prod_univ_eq_prod_range (fun a => ∏ b ∈ (Ico (a + 1) N).filter
    (fun b => Formalism.LogVandermondeBounds.StandardLattice.plusSign D.R.k b = Formalism.LogVandermondeBounds.StandardLattice.plusSign D.R.k a),
      (lam a - lam b + Formalism.LogVandermondeBounds.StandardLattice.nBetween D.R.k a b)) N]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Finset.prod_filter, Finset.prod_filter]
  have h := Fin.prod_univ_eq_prod_range (fun b => if a.val < b ∧
    Formalism.LogVandermondeBounds.StandardLattice.plusSign D.R.k b = Formalism.LogVandermondeBounds.StandardLattice.plusSign D.R.k a.val then
      (lam a.val - lam b + Formalism.LogVandermondeBounds.StandardLattice.nBetween D.R.k a.val b) else 1) N
  have e : (∏ b : Fin N, if a < b ∧ rowSgn D a = rowSgn D b then
      (rowLam D ρ a + rhoN (rowSgn D) a - (rowLam D ρ b + rhoN (rowSgn D) b)) else 1) =
      ∏ b : Fin N, (fun b => if a.val < b ∧
    Formalism.LogVandermondeBounds.StandardLattice.plusSign D.R.k b = Formalism.LogVandermondeBounds.StandardLattice.plusSign D.R.k a.val then
      (lam a.val - lam b + Formalism.LogVandermondeBounds.StandardLattice.nBetween D.R.k a.val b) else 1) b.val := by
    refine Finset.prod_congr rfl fun b _ => ?_
    by_cases hc : a < b ∧ rowSgn D a = rowSgn D b
    · have hc' : a.val < b.val ∧
          Formalism.LogVandermondeBounds.StandardLattice.plusSign D.R.k b.val = Formalism.LogVandermondeBounds.StandardLattice.plusSign D.R.k a.val :=
        ⟨hc.1, by rw [← line_sign_apply, ← line_sign_apply]; exact hc.2.symm⟩
      simp only [if_pos hc, if_pos hc']
      have h1 := rho_sub_eq_card_opposite (rowSgn D) a b hc.1 hc.2
      rw [card_opposite_sign_between] at h1
      rw [line_param_apply, line_param_apply]
      linarith
    · have hc' : ¬ (a.val < b.val ∧
          Formalism.LogVandermondeBounds.StandardLattice.plusSign D.R.k b.val = Formalism.LogVandermondeBounds.StandardLattice.plusSign D.R.k a.val) := by
        rintro ⟨h1, h2⟩
        exact hc ⟨h1, by rw [line_sign_apply, line_sign_apply]; exact h2.symm⟩
      simp only [if_neg hc, if_neg hc']
  rw [e, h, ← Finset.prod_filter, ← Finset.prod_filter]
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by omega, h1⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h2, by omega, h3⟩

theorem abs_param_sup_le (D : D7) (ρ : D.what₂.Tau) :
    lamAbs (rowLam D ρ) ≤ vN D ρ 0 + bN D ρ (D.R.m - 1) := by
  have hk := D.R.k_ge
  have hm := D.R.two_le_m
  have hN : 0 < D.R.k - 1 + D.R.m := by omega
  have : Nonempty (Fin (D.R.k - 1 + D.R.m)) := ⟨⟨0, hN⟩⟩
  have hanti := (line_param_strictAnti D ρ).antitone
  have h0 : rowLam D ρ ⟨0, hN⟩ = vN D ρ 0 := by
    rw [line_param_apply]; unfold Formalism.LogVandermondeBounds.StandardLattice.rowPar; rw [if_pos (by show 0 < D.R.k - 1; omega)]
  have h1 : rowLam D ρ ⟨D.R.k - 1 + D.R.m - 1, by omega⟩ = - bN D ρ (D.R.m - 1) := by
    rw [line_param_apply]; unfold Formalism.LogVandermondeBounds.StandardLattice.rowPar
    rw [if_neg (by show ¬ (D.R.k - 1 + D.R.m - 1 < D.R.k - 1); omega)]
    congr 2
    show D.R.k - 1 + D.R.m - 1 - (D.R.k - 1) = D.R.m - 1
    omega
  have hup : ∀ a, rowLam D ρ a ≤ vN D ρ 0 := fun a => h0 ▸ hanti (Fin.mk_le_of_le_val (Nat.zero_le _))
  have hlo : ∀ a, - bN D ρ (D.R.m - 1) ≤ rowLam D ρ a := fun a =>
    h1 ▸ hanti (show a ≤ ⟨D.R.k - 1 + D.R.m - 1, by omega⟩ from Fin.le_def.2 (by have := a.2; show a.val ≤ D.R.k - 1 + D.R.m - 1; omega))
  unfold lamAbs
  refine ciSup_le fun a => ciSup_le fun b => ?_
  rw [abs_le]
  constructor <;> linarith [hup a, hup b, hlo a, hlo b]

theorem abs_param_sup_nonneg {N : ℕ} (lam : Fin N → ℝ) : 0 ≤ lamAbs lam := by
  unfold lamAbs
  exact Real.iSup_nonneg fun a => Real.iSup_nonneg fun b => abs_nonneg _

end Formalism.MainNotions.StandardLattice

namespace Formalism.MainNotions.StandardLattice

open NumberField Formalism.BasicNotions Finset

theorem mass_nonneg_alt (D : D7) (M : ℕ) : 0 ≤ massI D M := by
  exact (massI_pos D M).le

def ratioH (D : D7) (M : ℕ) : ℝ :=
  letI := D.host.cmStar
  ((((M - 1).factorial : ℕ) : ℝ) * (D.host.v / Real.pi) ^ M) ^ D.R.f / Real.sqrt ((2 * D.host.v) ^ D.R.f) *
    Formalism.HermitianLatticesTheory.lValEta D.host.E M

theorem mass_ratio_eq (D : D7) (M : ℕ) :
    letI := D.host.cmStar; Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E M = ratioH D M := by
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide ratioH
  rw [vInv_host, fDeg_host]

theorem mass_ratio_pos (D : D7) (hv : 0 < D.host.v) (M : ℕ) (hM : 2 ≤ M) : 0 < ratioH D M := by
  unfold ratioH
  have hl := lVal_pos D M hM
  have hs : 0 < Real.sqrt ((2 * D.host.v) ^ D.R.f) := Real.sqrt_pos.mpr (pow_pos (by linarith) _)
  have h1 : 0 < (((M - 1).factorial : ℕ) : ℝ) * (D.host.v / Real.pi) ^ M :=
    mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (pow_pos (div_pos hv Real.pi_pos) _)
  exact mul_pos (div_pos (pow_pos h1 _) hs) hl

theorem mass_succ_eq_mul_ratio (D : D7) (h2b : MassRatio₂ D) (hv : 0 < D.host.v) (M : ℕ) (hM : 3 ≤ M) :
    massI D (M - 1) ≠ 0 ∧ massI D M = massI D (M - 1) * ratioH D M := by
  have h := h2b M hM
  rw [mass_ratio_eq] at h
  have hp := mass_ratio_pos D hv M (by omega)
  have hb : massI D (M - 1) ≠ 0 := by
    intro h0
    rw [h0, div_zero] at h
    exact hp.ne h
  exact ⟨hb, by rw [div_eq_iff hb] at h; rw [h]; ring⟩

theorem mass_telescope (D : D7) (h2b : MassRatio₂ D) (hv : 0 < D.host.v) (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    massI D (k + n) = massI D k * ∏ M ∈ Ico (k + 1) (k + n + 1), ratioH D M := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := (mass_succ_eq_mul_ratio D h2b hv (k + n + 1) (by omega)).2
    rw [show k + n + 1 - 1 = k + n by omega] at hs
    rw [show k + (n + 1) = k + n + 1 by ring, hs, ih,
      Finset.prod_Ico_succ_top (show k + 1 ≤ k + n + 1 by omega), mul_assoc]

theorem mass_pos_alt (D : D7) (h2b : MassRatio₂ D) (hv : 0 < D.host.v) (k : ℕ) (hk : 2 ≤ k) : 0 < massI D k := by
  exact massI_pos D k

theorem index_ratio_bounds (D : D7) (h4a : Conclusion4a D) (hg : ∀ i, 3 ≤ D.host.g i) :
    0 < idxPi D (D.host.g 0) (D.host.g 1) ∧ 0 < idxSig D (D.host.g 0) (D.host.g 1) ∧
    ((2 : ℝ) ^ (2 * D.R.f))⁻¹ * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ^
        ((D.R.f : ℝ) * D.R.m * (2 * D.R.k + D.R.m - 1) / 2) ≤
      idxSig D (D.host.g 0) (D.host.g 1) / idxPi D (D.host.g 0) (D.host.g 1) ∧
    idxSig D (D.host.g 0) (D.host.g 1) / idxPi D (D.host.g 0) (D.host.g 1) ≤
      (2 : ℝ) ^ (2 * D.R.f) * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ^
        ((D.R.f : ℝ) * D.R.m * (2 * D.R.k + D.R.m - 1) / 2) := by
  have hgp : ∀ i, (0 : ℝ) < (D.host.g i : ℝ) := fun i => by exact_mod_cast (D.host.g_prime i).pos
  have hg1 : ∀ i, (1 : ℝ) ≤ (D.host.g i : ℝ) := fun i => by exact_mod_cast (D.host.g_prime i).one_lt.le
  have hc : ∀ i, 0 < idxColLoc (D.host.g i) D.R.k := fun i =>
    lt_of_lt_of_le (by have := hgp i; positivity) (h4a i (hg i)).1
  have hr : ∀ i, 0 < idxRowLoc (D.host.g i) D.R.k D.R.m := fun i =>
    lt_of_lt_of_le (by have := hgp i; positivity) (h4a i (hg i)).2.2.1
  have hPi : 0 < idxPi D (D.host.g 0) (D.host.g 1) := by
    unfold idxPi; have := hc 0; have := hc 1; positivity
  have hSig : 0 < idxSig D (D.host.g 0) (D.host.g 1) := by
    unfold idxSig; have := hr 0; have := hr 1; positivity
  refine ⟨hPi, hSig, ?_⟩
  have key := Formalism.HermitianLattices.GenusMassVolumes.index_ratio_bound D.R.f D.R.k D.R.m (D.host.g 0 : ℝ) (D.host.g 1 : ℝ)
    (idxPi D (D.host.g 0) (D.host.g 1)) (idxSig D (D.host.g 0) (D.host.g 1))
    (fun i _ => idxColLoc (D.host.g i) D.R.k / (D.host.g i : ℝ) ^ (D.R.k * (D.R.k + 1) / 2))
    (fun i _ => idxRowLoc (D.host.g i) D.R.k D.R.m /
      (D.host.g i : ℝ) ^ ((D.R.r ^ 2 + 3 * D.R.k + 1 + 2 * D.R.rS) / 2))
    D.R.two_le_m D.R.m_even (hg1 0) (hg1 1)
    (by
      intro i _
      obtain ⟨a1, a2, a3, a4⟩ := h4a i (hg i)
      have p1 : (0 : ℝ) < (D.host.g i : ℝ) ^ (D.R.k * (D.R.k + 1) / 2) := pow_pos (hgp i) _
      have p2 : (0 : ℝ) < (D.host.g i : ℝ) ^ ((D.R.r ^ 2 + 3 * D.R.k + 1 + 2 * D.R.rS) / 2) := pow_pos (hgp i) _
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [le_div_iff₀ p1]; linarith
      · rw [div_le_one p1]; exact a2
      · rw [le_div_iff₀ p2]; linarith
      · rw [div_le_one p2]; exact a4)
  refine key ?_ ?_
  · rw [Fin.prod_univ_two]
    simp only [Finset.prod_const, Finset.card_range, Matrix.cons_val_zero, Matrix.cons_val_one]
    unfold idxPi
    rw [mul_div_cancel₀ _ (pow_pos (hgp 0) _).ne', mul_div_cancel₀ _ (pow_pos (hgp 1) _).ne']
  · rw [Fin.prod_univ_two]
    simp only [Finset.prod_const, Finset.card_range, Matrix.cons_val_zero, Matrix.cons_val_one]
    unfold idxSig
    have e0 : (D.host.g 0 : ℝ) ^ (((D.R.k + D.R.m - 1) ^ 2 + 3 * D.R.k + 1 + 2 * (D.R.m / 2 - 1)) / 2) *
        (idxRowLoc (D.host.g 0) D.R.k D.R.m / (D.host.g 0 : ℝ) ^ ((D.R.r ^ 2 + 3 * D.R.k + 1 + 2 * D.R.rS) / 2)) =
        idxRowLoc (D.host.g 0) D.R.k D.R.m := mul_div_cancel₀ (idxRowLoc (D.host.g 0) D.R.k D.R.m)
      (pow_pos (hgp 0) ((D.R.r ^ 2 + 3 * D.R.k + 1 + 2 * D.R.rS) / 2)).ne'
    have e1 : (D.host.g 1 : ℝ) ^ (((D.R.k + D.R.m - 1) ^ 2 + 3 * D.R.k + 1 + 2 * (D.R.m / 2 - 1)) / 2) *
        (idxRowLoc (D.host.g 1) D.R.k D.R.m / (D.host.g 1 : ℝ) ^ ((D.R.r ^ 2 + 3 * D.R.k + 1 + 2 * D.R.rS) / 2)) =
        idxRowLoc (D.host.g 1) D.R.k D.R.m := mul_div_cancel₀ (idxRowLoc (D.host.g 1) D.R.k D.R.m)
      (pow_pos (hgp 1) ((D.R.r ^ 2 + 3 * D.R.k + 1 + 2 * D.R.rS) / 2)).ne'
    rw [e0, e1]

theorem column_param_strictAnti' (D : D7) (u : D.what₂.Word) (ρ : D.what₂.Tau) : StrictAnti (uColR D u ρ) := by
  intro a b hab
  have := one_le_column_param_sub D u ρ a b hab
  linarith

theorem one_le_column_sub_of_lt (D : D7) (u : D.what₂.Word) (ρ : D.what₂.Tau) (i j : ℕ) (hij : i < j) (hj : j < D.R.k) :
    1 ≤ uN D u ρ i - uN D u ρ j := by
  have h := one_le_column_param_sub D u ρ ⟨i, by omega⟩ ⟨j, hj⟩ (Fin.lt_iff_val_lt_val.mpr hij)
  rw [column_param_apply, column_param_apply] at h
  exact h

theorem place_data_under_section_B (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (u : D.what₂.Word) (ρ : D.what₂.Tau) :
    Formalism.LogVandermondeBounds.StandardLattice.PlaceData sc.x Δ (sc.x * Real.exp (sc.x ^ sc.eps)) (Real.exp (sc.x ^ sc.eps)) D.R.k D.R.m
      (uN D u ρ) (vN D ρ) (bN D ρ) (fun j => w j ρ) := by
  obtain ⟨-, -, -, -, -, -, -, h8, h9, -, h11, h12, h13, h14, h15, -⟩ := hB
  have hk := D.R.k_ge
  have hm := D.R.two_le_m
  refine ⟨h8 ρ, h9 ρ, ?_, ?_, ?_, fun j hj => ⟨(h13 ρ j hj).2.1, (h13 ρ j hj).2.2⟩, ?_, (h15 ρ).1, (h15 ρ).2⟩
  · intro i hi
    have h1 := (D.hcW u ρ).u_gt_v ⟨i, hi⟩
    have h2 := (D.hcW u ρ).v_gt_u ⟨i, hi⟩
    rw [D.hcW_v] at h1 h2
    unfold uN vN
    rw [dif_pos (by omega : i < D.R.k), dif_pos (by omega : i + 1 < D.R.k), dif_pos hi]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · have h1 := (D.hcW u ρ).u_last_gt (by omega) (by omega)
    rw [D.hcW_b] at h1
    unfold uN bN
    rw [dif_pos (by omega : D.R.k - 1 < D.R.k), dif_pos (by omega : 0 < D.R.m)]
    exact_mod_cast h1
  · by_cases ht : IsTop D ρ
    · exact Or.inl (h11 u ρ ht)
    · exact Or.inr (h12 u ρ ht)
  · intro j hj
    refine ⟨h14 ρ j hj, ?_⟩
    have g1 := (D.hc ρ).gap_be ⟨j, by omega⟩
    have g2 := (D.hc ρ).gap_eb ⟨j, by omega⟩ hj
    have g3 : (1 : ℚ) ≤ (D.hc ρ).b ⟨j + 1, hj⟩ - (D.hc ρ).b ⟨j, by omega⟩ := by
      have ht : (0 : ℚ) ≤ D.R.t := by positivity
      linarith
    unfold bN
    rw [dif_pos hj, dif_pos (by omega : j < D.R.m)]
    exact_mod_cast g3

end Formalism.MainNotions.StandardLattice

namespace Formalism.MainNotions.StandardLattice

open NumberField Formalism.BasicNotions Finset

theorem dim_weyl_line_eq (D : D7) (ρ : D.what₂.Tau) : dimV (rowLam D ρ) =
    Formalism.LogVandermondeBounds.StandardLattice.dimVN (Formalism.LogVandermondeBounds.StandardLattice.rowPar D.R.k (vN D ρ) (bN D ρ)) (D.R.k - 1 + D.R.m) := by
  rw [line_param_eq_fun]
  exact dim_weyl_fin_eq_nat _ _

theorem dim_weyl_column_eq (D : D7) (u : D.what₂.Word) (ρ : D.what₂.Tau) :
    dimV (uColR D u ρ) = Formalism.LogVandermondeBounds.StandardLattice.dimVN (uN D u ρ) D.R.k := by
  rw [column_param_eq_fun]
  exact dim_weyl_fin_eq_nat _ _

theorem mass_eq_mass_mul_ratio_prod (D : D7) (h2b : MassRatio₂ D) (hv : 0 < D.host.v) :
    massI D D.R.r = massI D D.R.k * ∏ M ∈ Ico (D.R.k + 1) (D.R.k - 1 + D.R.m + 1), ratioH D M := by
  have hr := rank_eq_sum D
  have hm := D.R.two_le_m
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have := mass_telescope D h2b hv D.R.k hk (D.R.m - 1)
  rw [show D.R.k + (D.R.m - 1) = D.R.k - 1 + D.R.m by omega] at this
  rw [hr]
  exact this

theorem dual_degree_word_eq (D : D7) (u : D.what₂.Word) :
    duStarU D u = massI D D.R.k * idxPi D (D.host.g 0) (D.host.g 1) *
      ∏ n ∈ range D.R.f, Formalism.LogVandermondeBounds.StandardLattice.dimVN (uN D u (tauOf D n)) D.R.k := by
  unfold duStarU duStarP
  rw [prod_over_tau_eq_prod_range]
  simp only [dim_weyl_column_eq]

theorem weylLaw_lower_eventually (eps C0 : ℝ) (h1 : 0 < eps) (h2 : eps < 1 / 52) :
    ∃ C : ℝ, ∀ (D : D7) (sc : Scale) (C3 : ℝ), sc.eps = eps → MassRatio₂ D → Conclusion4a D → PartFourSectionBData D sc C3 C0 →
      ∀ (Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ), DataB D sc C0 Δ w → ∀ u : D.what₂.Word,
        lowB D sc C w ≤ logXuD D u := by
  obtain ⟨C, hC⟩ := Formalism.LogVandermondeBounds.vandermonde_place_lower_bound eps (max C0 0) h1 h2 (le_max_right _ _)
  refine ⟨C, fun D sc C3 he h2b h4a h4B Δ w hB u => ?_⟩
  subst he
  let _ := D.host.cmStar
  have hk := D.R.k_ge
  have hm := D.R.two_le_m
  have hg := three_le_level_of_section_B D sc C0 Δ w hB
  have hpl := place_data_under_section_B D sc C0 Δ w hB u
  have hlow := (h4B Δ w hB).2.2.2
  obtain ⟨b1, b2, -, -, b5, -, b7, -⟩ := hB
  have hv : 0 < D.host.v := lt_of_lt_of_le Real.pi_pos b1
  obtain ⟨i1, i2, i3, -⟩ := index_ratio_bounds D h4a hg
  have hg1 : ∀ i, (1 : ℝ) ≤ (D.host.g i : ℝ) := fun i => by exact_mod_cast (D.host.g_prime i).one_lt.le
  have key := hC sc.x sc.one_lt_alt.le D.R.f D.R.m D.R.k D.host.v Δ (D.host.g 0 : ℝ) (D.host.g 1 : ℝ)
    (fun n => uN D u (tauOf D n)) (fun n => vN D (tauOf D n)) (fun n => bN D (tauOf D n))
    (fun n j => w j (tauOf D n)) (DstarD D) (duStarU D u) (massI D D.R.k) (massI D D.R.r)
    (idxSig D (D.host.g 0) (D.host.g 1)) (idxPi D (D.host.g 0) (D.host.g 1))
    (fun M => Formalism.HermitianLatticesTheory.lValEta D.host.E M)
    (degree_pos_alt D) (by omega) (by omega)
    (le_trans b5 (Real.rpow_le_rpow_of_exponent_le sc.one_lt_alt.le (le_max_left _ _)))
    b1 b2 b7 (hg1 0) (hg1 1) (fun n _ => hpl (tauOf D n))
    (mass_pos_alt D h2b hv _ (by omega))
    (mass_pos_alt D h2b hv _ (by have := D.R.r_eq; omega)) i2 i1
    (fun M hM => ⟨lVal_pos D M (by have := (Finset.mem_Ico.1 hM).1; omega),
      massIdentity_holds D M (by have := (Finset.mem_Ico.1 hM).1; omega)⟩)
    (mass_eq_mass_mul_ratio_prod D h2b hv) i3
    (by
      unfold DstarLow at hlow
      rw [prod_over_tau_eq_prod_range] at hlow
      simp only [dim_weyl_line_eq] at hlow
      exact hlow)
    (dual_degree_word_eq D u)
  unfold lowB logXuD logXu
  rw [Fin.sum_univ_two]
  simp only [sum_over_tau_eq_sum_range D]
  exact key

theorem weylLaw_upper_eventually (eps C0 C3 : ℝ) (h1 : 0 < eps) (h2 : eps < 1 / 52) (hC3 : 0 ≤ C3) :
    ∃ C : ℝ, ∀ (D : D7) (sc : Scale), sc.eps = eps → MassRatio₂ D → VolumeEqMass₂ D → PointsLemma D C3 → Conclusion4a D →
      PartFourSectionBData D sc C3 C0 →
      ∀ (Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ), DataB D sc C0 Δ w → ∀ u : D.what₂.Word,
        logXuD D u ≤ C * D.R.m * sc.L := by
  obtain ⟨C, hC⟩ := Formalism.LogVandermondeBounds.upper_place_bound eps (max C0 0) (max C3 1) h1 h2 (le_max_right _ _) (le_max_right _ _)
  refine ⟨C, fun D sc he h2b h2v h3 h4a h4B Δ w hB u => ?_⟩
  subst he
  let _ := D.host.cmStar
  have hk := D.R.k_ge
  have hm := D.R.two_le_m
  have hg := three_le_level_of_section_B D sc C0 Δ w hB
  have hpl := place_data_under_section_B D sc C0 Δ w hB u
  have hgap := (h4B Δ w hB).2.1
  obtain ⟨b1, b2, -, b4, b5, b6, b7, -⟩ := hB
  have hv : 0 < D.host.v := lt_of_lt_of_le Real.pi_pos b1
  have hL0 : 0 ≤ sc.L := le_trans zero_le_one (one_le_scale_length sc)
  obtain ⟨i1, i2, -, i4⟩ := index_ratio_bounds D h4a hg
  have hg1 : ∀ i, (1 : ℝ) ≤ (D.host.g i : ℝ) := fun i => by exact_mod_cast (D.host.g_prime i).one_lt.le
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by have := D.R.m_add_three_le_k; omega : D.R.m ≤ D.R.k)
  have hexp : Real.exp (-(D.R.r : ℝ)) ≤ 1 / 3 := by
    have hr : (2 : ℝ) ≤ D.R.r := by exact_mod_cast (by have := D.R.r_eq; omega : 2 ≤ D.R.r)
    have e1 : Real.exp (-(D.R.r : ℝ)) ≤ Real.exp (-2) := Real.exp_le_exp.2 (by linarith)
    have e2 : (3 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2 : ℝ); linarith
    have e3 : Real.exp (-2) = (Real.exp 2)⁻¹ := Real.exp_neg 2
    have e4 : (Real.exp 2)⁻¹ ≤ 1 / 3 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) e2
    linarith
  have h3' : ∀ ρ : D.what₂.Tau, D.dsig ρ ≤
      4 * Formalism.LogVandermondeBounds.StandardLattice.dTau D.R.k D.R.m (Formalism.LogVandermondeBounds.StandardLattice.rowPar D.R.k (vN D ρ) (bN D ρ)) *
      (max C3 1 * ((D.R.k - 1 + D.R.m / 2 : ℕ) : ℝ) * ((D.R.m / 2 : ℕ) : ℝ) * ((D.R.k - 1 + D.R.m : ℕ) : ℝ) *
        (vN D ρ 0 + bN D ρ (D.R.m - 1))) ^ ((D.R.k - 1 + D.R.m / 2) * (D.R.m / 2)) := by
    intro ρ
    have h := (h3 (1 / 3) hexp (by norm_num) ρ (hgap ρ)).2
    rw [formal_degree_line_eq, count_plus_eq, count_minus_eq, rank_eq_sum] at h
    refine le_trans h ?_
    have hT := (Formalism.LogVandermondeBounds.StandardLattice.UpperPlace_holds sc.eps sc.x sc.eps_pos sc.one_lt_alt.le D.R.k D.R.m Δ (max C3 1)
      (uN D u ρ) (vN D ρ) (bN D ρ) (fun j => w j ρ) hm D.R.m_even (by omega) hmk b7 (le_max_right _ _) (hpl ρ)
      (fun i j hij hj => one_le_column_sub_of_lt D u ρ i j hij hj)).2.1
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine pow_le_pow_left₀ ?_ ?_ _
    · have := abs_param_sup_nonneg (rowLam D ρ); positivity
    · have a1 := abs_param_sup_nonneg (rowLam D ρ)
      have a2 := abs_param_sup_le D ρ
      have a3 : C3 ≤ max C3 1 := le_max_left _ _
      gcongr
  have key := hC sc.x sc.one_lt_alt.le D.R.f D.R.m D.R.k D.host.v Δ (D.host.g 0 : ℝ) (D.host.g 1 : ℝ)
    (fun n => uN D u (tauOf D n)) (fun n => vN D (tauOf D n)) (fun n => bN D (tauOf D n))
    (fun n j => w j (tauOf D n)) (DstarD D) (duStarU D u) (massI D D.R.k) (massI D D.R.r)
    (idxSig D (D.host.g 0) (D.host.g 1)) (idxPi D (D.host.g 0) (D.host.g 1))
    (fun M => Formalism.HermitianLatticesTheory.lValEta D.host.E M) (fun n => D.dsig (tauOf D n))
    (degree_pos_alt D) hm D.R.m_even (by omega) b4
    (le_trans b5 (Real.rpow_le_rpow_of_exponent_le sc.one_lt_alt.le (le_max_left _ _)))
    b1 b2 b7 (hg1 0) (hg1 1)
    (le_trans (b6 0).2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hL0))
    (le_trans (b6 1).2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hL0))
    (fun n _ => ⟨hpl (tauOf D n), fun i j hij hj => one_le_column_sub_of_lt D u (tauOf D n) i j hij hj⟩)
    (mass_pos_alt D h2b hv _ (by omega))
    (mass_pos_alt D h2b hv _ (by have := D.R.r_eq; omega)) i2 i1
    (fun M hM => ⟨lVal_pos D M (by have := (Finset.mem_Ico.1 hM).1; omega),
      massIdentity_holds D M (by have := (Finset.mem_Ico.1 hM).1; omega)⟩)
    (mass_eq_mass_mul_ratio_prod D h2b hv) i4
    (by
      unfold DstarD DstarP
      rw [volume_eq_mass_at_rank D h2v, prod_over_tau_eq_prod_range])
    (fun n _ => ⟨D.dsig_pos _, h3' (tauOf D n)⟩)
    (dual_degree_word_eq D u)
  exact key

theorem weylLaw_eventually (eps C0 C3 : ℝ) (h1 : 0 < eps) (h2 : eps < 1 / 52) (hC3 : 0 ≤ C3) :
    ∃ C : ℝ, ∀ (D : D7) (sc : Scale), sc.eps = eps → MassRatio₂ D → VolumeEqMass₂ D → PointsLemma D C3 → Conclusion4a D →
      PartFourSectionBData D sc C3 C0 → Conclusion5 D sc C0 C := by
  obtain ⟨Ca, ha⟩ := weylLaw_lower_eventually eps C0 h1 h2
  obtain ⟨Cb, hb⟩ := weylLaw_upper_eventually eps C0 C3 h1 h2 hC3
  refine ⟨max Ca Cb, fun D sc he h2b h2v h3 h4a h4B Δ w hB u => ⟨?_, ?_⟩⟩
  · exact le_trans (lower_bound_antitone_const D sc Ca _ w (le_max_left _ _)) (ha D sc C3 he h2b h4a h4B Δ w hB u)
  · refine le_trans (hb D sc he h2b h2v h3 h4a h4B Δ w hB u) ?_
    have hL0 : 0 ≤ sc.L := le_trans zero_le_one (one_le_scale_length sc)
    have : (0 : ℝ) ≤ (D.R.m : ℝ) := by positivity
    have h := le_max_right Ca Cb
    gcongr

theorem weylLawStatement_eventually (eps C0 C3 : ℝ) (h1 : 0 < eps) (h2 : eps < 1 / 52) (hC3 : 0 ≤ C3) :
    ∃ C : ℝ, ∀ (D : D7) (sc : Scale), sc.eps = eps → GGFromIrreducibility D sc C3 C0 C := by
  obtain ⟨C, hC⟩ := weylLaw_eventually eps C0 C3 h1 h2 hC3
  refine ⟨max (C + 1) 16, fun D sc he p2 p3 p4a _ p4B => ?_⟩
  by_cases hB : ∃ (Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ), DataB D sc C0 Δ w
  · obtain ⟨Δ, w, hB⟩ := hB
    have hv : 0 < D.host.v := lt_of_lt_of_le Real.pi_pos hB.1
    exact weylLawBounds_all D sc C0 C (hC D sc he p2.2.2.1 p2.2.1 p3 p4a p4B)
      (mass_pos_alt D p2.2.2.1 hv _ (by have := D.R.k_ge; omega))
  · exact ⟨fun Δ w h => absurd ⟨Δ, w, h⟩ hB, fun Δ w h => absurd ⟨Δ, w, h⟩ hB,
      fun Δ w h => absurd ⟨Δ, w, h⟩ hB⟩

theorem familyWeylLaw_holds {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C3 : ℝ) (hC3 : 0 ≤ C3) : DegreeBoundFamilyStatement Fm C3 := by
  intro p2 p3 p4 p4B C0
  obtain ⟨i0⟩ := Fm.Ix_zero
  have h1 : 0 < eps := by rw [← Fm.L_eps 0 i0]; exact (Fm.L 0 i0).sc.eps_pos
  have h2 : eps < 1 / 52 := by rw [← Fm.L_eps 0 i0]; exact (Fm.L 0 i0).sc.eps_lt
  obtain ⟨C, hC⟩ := weylLawStatement_eventually eps C0 C3 h1 h2 hC3
  obtain ⟨x0, hx0⟩ := p4B C0
  refine ⟨C, x0, fun x hx hx1 i => ?_⟩
  have q4 := p4 x hx1 i
  exact hC (Fm.D x i) (Fm.L x i).sc (Fm.L_eps x i) (p2 x i) (p3 x i) q4.1 q4.2.1 (hx0 x hx hx1 i)

end Formalism.MainNotions.StandardLattice

namespace Formalism.MainNotions.StandardLattice

open NumberField Formalism.BasicNotions Finset

theorem stmt2All_of (D : D7) (h : Conclusion1 D → SiegelMassRatioCM) : AbsoluteConstantSecondPart D := fun h1 => volumeMass_all_of_standardMassRatio (h h1)

theorem massStatement_of_volume (D : D7) (h : Conclusion1 D → VolTie D → Conclusion2 D ∧ DefiniteVolumeEqMass D) : HodgeTateFromSandwich D :=
  fun h1 hV => volumeMass_of_definiteVolume D (h h1 hV).1 (h h1 hV).2

theorem levelStatement_reduction (D : D7) (Lv : LevelData D) (C3 : ℝ) (hp : Conclusion4p D Lv)
    (hn : VolumeMass D → adm17 D Lv → ClassNumberFormula₂ D Lv) (hs : LandherrSmall D) : ThetaChernBoundOfLastLine D Lv C3 :=
  fun h2 h3 h17 => levelStatement_of_landherrSmall D Lv C3 (finrank_host D) hp (hn h2 h17) hs h2 h3 h17

theorem stmt_of_open (eps C0 C3 : ℝ) (h1 : 0 < eps) (h2 : eps < 1 / 52) (hC3 : 0 ≤ C3) :
    ∃ C x0 : ℝ, ∀ (D : D7) (Lv : LevelData D) (sc : Scale), sc.eps = eps → x0 ≤ sc.x →
      Conclusion1 D → (Conclusion1 D → SiegelMassRatioCM) → (Conclusion1 D → VolTie D → Conclusion2 D ∧ DefiniteVolumeEqMass D) → TheoremThreeCompactDual D C3 →
      Conclusion4p D Lv → (VolumeMass D → adm17 D Lv → ClassNumberFormula₂ D Lv) → LandherrSmall D →
      Stmt D Lv sc C3 C0 C := by
  obtain ⟨C, hC⟩ := weylLawStatement_eventually eps C0 C3 h1 h2 hC3
  obtain ⟨x0, hx0⟩ := levelStatement_eventually eps C3 C0 h1
  exact ⟨C, x0, fun D Lv sc he hx o1 o2 o3 o4 o5 o6 o7 =>
    stmt_of_items D Lv sc C3 C0 C o1 (stmt2All_of D o2) (massStatement_of_volume D o3) o4 (formalDegreeBound_of_general D C3)
      (levelStatement_reduction D Lv C3 o5 o6 o7) (hx0 D Lv sc he hx) (hC D sc he)⟩

theorem stmtF_of_open {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C3 : ℝ) (hC3 : 0 ≤ C3)
    (o1 : PeriodFamilyStatement Fm) (o2 : FamilyPartOne Fm → SiegelMassRatioCM)
    (o3 : FamilyPartOne Fm → VolTieF Fm → ∀ x (i : Fm.Ix x), Conclusion2 (Fm.D x i) ∧ DefiniteVolumeEqMass (Fm.D x i))
    (o4 : FamilyTheoremThreeAll Fm C3)
    (o5 : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Conclusion4p (Fm.D x i) (Fm.ex x hx i).lev)
    (o6 : FamilyMassVolumeBounds Fm → FamilyLevelConditionAdmitted Fm → ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev)
    (o7 : ∀ x (i : Fm.Ix x), LandherrSmall (Fm.D x i)) : KudlaFamilyStatement Fm C3 :=
  stmtF_of_items Fm C3 o1 (fun h => volumeMass_all_of_standardMassRatio (o2 h))
    (fun h hV x i => volumeMass_of_definiteVolume (Fm.D x i) (o3 h hV x i).1 (o3 h hV x i).2) o4 (familyFormalDegree_holds Fm C3)
    (fun p2 p3 h17 x hx i => levelStatement_of_landherrSmall (Fm.D x i) (Fm.ex x hx i).lev C3 (finrank_host _) (o5 x hx i)
      (o6 p2 h17 x hx i) (o7 x i) (p2 x i) (p3 x i) (h17 x hx i))
    (familyLevelSectionB_holds Fm C3) (familyWeylLaw_holds Fm C3 hC3)

end Formalism.MainNotions.StandardLattice

namespace Formalism.MainNotions.StandardLattice

open NumberField Formalism.BasicNotions Finset

section T3

open Formalism.MainNotions.S MeasureTheory
open scoped InnerProductSpace

theorem isFormalDegree_smul_measure {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
    (μ : Measure (Formalism.REAL.UJ ε)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d : ℝ) (c : NNReal) (hc : 0 < c)
    (h : IsFdeg μ σ d) : IsFdeg ((c : ENNReal) • μ) σ (d / c) := by
  obtain ⟨hd, hh⟩ := h
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  refine ⟨div_pos hd hc', fun v w v' w' => ?_⟩
  obtain ⟨h1, h2⟩ := hh v w v' w'
  refine ⟨h1.smul_measure ENNReal.coe_ne_top, ?_⟩
  rw [integral_smul_measure, h2, ENNReal.coe_toReal]
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hcc : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc'.ne'
  rw [Complex.real_smul]
  push_cast
  field_simp

theorem formalDegree_pos_discreteSeries (D : D7) (hS : NonvanishingBesselPeriod D) (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ)
    (hlam : Formalism.QuantumDeterminants.IsHCParam lam) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (hDS : IsDS ε lam σ) (w : H) (hw : w ≠ 0) :
    0 < fdegOf ((D.s.cdScale N ε : ENNReal) • Formalism.REAL.muG ε) σ w := by
  have : CompleteSpace H := hDS.1
  obtain ⟨d, hd⟩ := hS N ε lam hlam H σ hDS
  have h := isFormalDegree_smul_measure _ σ d (D.s.cdScale N ε) (D.s.cdScale_pos N ε) hd
  rw [formal_degree_of_eq _ σ _ h w hw]
  exact h.1

theorem formalDegreeFactor_eq_prod {N : ℕ} (s : Fin N → Bool) (lam : Fin N → ℝ) :
    dTau s lam = (∏ a, ∏ b ∈ univ.filter (fun b => a < b ∧ s a = s b),
      (lam a - lam b + ((univ.filter (fun e : Fin N => a < e ∧ e < b ∧ s e ≠ s a)).card : ℝ))) /
      ((∏ i ∈ range (nPlus s), (i.factorial : ℝ)) * ∏ i ∈ range (nMinus s), (i.factorial : ℝ)) := by
  unfold dTau facProd
  congr 1
  refine Finset.prod_congr rfl (fun a _ => Finset.prod_congr rfl (fun b hb => ?_))
  rw [Finset.mem_filter] at hb
  rw [← rho_sub_eq_card_opposite s a b hb.2.1 hb.2.2]
  ring

theorem formalDegreeFactor_pos_of_strictAnti {N : ℕ} (s : Fin N → Bool) (lam : Fin N → ℝ) (h : StrictAnti lam) : 0 < dTau s lam := by
  unfold dTau
  apply div_pos
  · apply Finset.prod_pos
    intro a _
    apply Finset.prod_pos
    intro b hb
    rw [Finset.mem_filter] at hb
    have h1 := rho_sub_eq_card_opposite s a b hb.2.1 hb.2.2
    have h2 : lam b < lam a := h hb.2.1
    have h3 : (0 : ℝ) ≤ ((univ.filter (fun c : Fin N => a < c ∧ c < b ∧ s c ≠ s a)).card : ℝ) :=
      Nat.cast_nonneg _
    linarith
  · exact mul_pos (factorial_product_pos _) (factorial_product_pos _)

def cGr (p q : ℕ) : ℝ := facProd (p + q) / (Real.pi ^ (p * q) * (facProd p * facProd q))

theorem grassmannVolumeConst_pos (p q : ℕ) : 0 < cGr p q := by
  unfold cGr
  exact div_pos (factorial_product_pos _)
    (mul_pos (pow_pos Real.pi_pos _) (mul_pos (factorial_product_pos _) (factorial_product_pos _)))

theorem inv_grassmannVolumeConst_eq (p q : ℕ) : 1 / cGr p q = Real.pi ^ (p * q) * (facProd p * facProd q) / facProd (p + q) := by
  unfold cGr
  rw [one_div, inv_div]

def TheoremThreeHypotheses (C3 : ℝ) {N : ℕ} (ε : Fin N → Bool) (lam : Fin N → ℝ) (ep0 h0 : ℝ) : Prop :=
  Formalism.QuantumDeterminants.IsHCParam lam ∧ Formalism.QuantumDeterminants.GapAtLeast ε lam h0 ∧ Real.exp (-(N : ℝ)) ≤ ep0 ∧ ep0 < 1 / 2 ∧
  C3 * min (nPlus ε : ℝ) (nMinus ε : ℝ) * ((nPlus ε : ℝ) * (nMinus ε : ℝ)) ^ 3 * N * Real.log N / ep0 ^ 2 ≤ h0

def FormalDegreeLowerBound (D : D7) (C3 : ℝ) : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (ep0 h0 : ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H),
    TheoremThreeHypotheses C3 ε lam ep0 h0 → IsDS ε lam σ → w ≠ 0 →
    ∃ Z : ℝ, 0 < Z ∧ Z ≤ (1 - ep0)⁻¹ ∧
      1 / fdegOf ((D.s.cdScale N ε : ENNReal) • Formalism.REAL.muG ε) σ w ≤
        cGr (nPlus ε) (nMinus ε) / (Module.finrank ℂ (lowKSub ε lam σ) : ℝ) *
          (∏ a, ∏ b ∈ univ.filter (fun b : Fin N => a < b ∧ ε a ≠ ε b),
            Real.pi / (lam a - lam b + ((b.val : ℝ) - a.val))) * Z

def FormalDegreeUpperBound (D : D7) (C3 c0 : ℝ) : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (ep0 h0 : ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H),
    TheoremThreeHypotheses C3 ε lam ep0 h0 → IsDS ε lam σ → w ≠ 0 →
    cGr (nPlus ε) (nMinus ε) * (Real.pi ^ (nPlus ε * nMinus ε) *
        (c0 / (2 * N * lamAbs lam)) ^ (nPlus ε * nMinus ε) / ((nPlus ε * nMinus ε).factorial : ℝ)) *
        ((Module.finrank ℂ (lowKSub ε lam σ) : ℝ) / 4) ≤
      (Module.finrank ℂ (lowKSub ε lam σ) : ℝ) ^ 2 /
        fdegOf ((D.s.cdScale N ε : ENNReal) • Formalism.REAL.muG ε) σ w

theorem harishChandraAbs_pos_of_strictAnti {N : ℕ} (lam : Fin N → ℝ) (h : StrictAnti lam) (hN : 2 ≤ N) : 0 < lamAbs lam := by
  unfold lamAbs
  have h0 : (⟨0, by omega⟩ : Fin N) < ⟨1, by omega⟩ := Fin.lt_iff_val_lt_val.mpr (by simp)
  have hpos : 0 < |lam ⟨0, by omega⟩ - lam ⟨1, by omega⟩| := abs_pos.mpr (sub_ne_zero.mpr (h h0).ne')
  have hb1 : BddAbove (Set.range fun b : Fin N => |lam ⟨0, by omega⟩ - lam b|) := (Set.finite_range _).bddAbove
  have hb2 : BddAbove (Set.range fun a : Fin N => ⨆ b : Fin N, |lam a - lam b|) := (Set.finite_range _).bddAbove
  calc (0 : ℝ) < |lam ⟨0, by omega⟩ - lam ⟨1, by omega⟩| := hpos
    _ ≤ ⨆ b : Fin N, |lam ⟨0, by omega⟩ - lam b| := le_ciSup hb1 ⟨1, by omega⟩
    _ ≤ ⨆ a : Fin N, ⨆ b : Fin N, |lam a - lam b| := le_ciSup hb2 ⟨0, by omega⟩

theorem formalDegreeBound_all_unitaryGroups (D : D7) (C3 c0 : ℝ) (hc0 : 0 < c0) (hC : 2 / c0 ≤ C3) (hS : NonvanishingBesselPeriod D)
    (hT : FamilyMassLastLine D) (hL : FormalDegreeLowerBound D C3) (hU : FormalDegreeUpperBound D C3 c0) : RepresentationDimensionGeneral D C3 := by
  intro N ε lam ep0 h0 H _ _ σ w p q hlam hgap he1 he2 hh hDS hw
  have hdat : TheoremThreeHypotheses C3 ε lam ep0 h0 := ⟨hlam, hgap, he1, he2, hh⟩
  have : CompleteSpace H := hDS.1
  have hd := formalDegree_pos_discreteSeries D hS N ε lam hlam H σ hDS w hw
  have hτ := (hT N ε lam hlam H σ hDS).2
  have hτp : 0 < (Module.finrank ℂ (lowKSub ε lam σ) : ℝ) := by rw [hτ]; exact formalDegreeFactor_pos_of_strictAnti ε lam hlam.1
  have hpq : nPlus ε + nMinus ε = N := count_plus_add_count_minus N ε
  have hep : 0 < ep0 := lt_of_lt_of_le (Real.exp_pos _) he1
  have hinv := inv_grassmannVolumeConst_eq (nPlus ε) (nMinus ε)
  rw [hpq] at hinv
  constructor
  · obtain ⟨Z, hZ0, hZ1, hZ⟩ := hL N ε lam ep0 h0 H σ w hdat hDS hw
    rw [← dimV_eq_fdegHC lam hlam.1]
    exact Formalism.HermitianLattices.GenusMassVolumes.joint_lower_bound N lam ε _ (Module.finrank ℂ (lowKSub ε lam σ) : ℝ)
      (cGr (nPlus ε) (nMinus ε)) ep0 Z (fun a b hab => hlam.1 hab) hd (grassmannVolumeConst_pos _ _) hep (by linarith) hZ0 hZ1
      hinv (by rw [hτ]; exact formalDegreeFactor_eq_prod ε lam) hZ
  · have hUU := hU N ε lam ep0 h0 H σ w hdat hDS hw
    have hexp : p * q = ((nPlus ε * nMinus ε : ℕ) : ℝ) := by push_cast; rfl
    rw [hexp, Real.rpow_natCast]
    by_cases h0pq : nPlus ε * nMinus ε = 0
    · have hc1 : cGr (nPlus ε) (nMinus ε) = 1 := by
        have hp := factorial_product_pos N
        rcases Nat.mul_eq_zero.1 h0pq with h | h
        · have hq : nMinus ε = N := by omega
          unfold cGr; rw [h, hq]; simp [facProd]; exact hp.ne'
        · have hq : nPlus ε = N := by omega
          unfold cGr; rw [h, hq]; simp [facProd]; exact hp.ne'
      rw [h0pq, hc1] at hUU
      rw [h0pq]
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one, one_mul] at hUU ⊢
      rw [le_div_iff₀ hd] at hUU
      nlinarith
    · have hp1 : 1 ≤ nPlus ε := Nat.pos_of_ne_zero fun h => h0pq (by rw [h, Nat.zero_mul])
      have hq1 : 1 ≤ nMinus ε := Nat.pos_of_ne_zero fun h => h0pq (by rw [h, Nat.mul_zero])
      have hlp := harishChandraAbs_pos_of_strictAnti lam hlam.1 (by omega)
      have hg : 1 / cGr (nPlus ε) (nMinus ε) ≤ Real.pi ^ (nPlus ε * nMinus ε) := by
        rw [inv_grassmannVolumeConst_eq]
        exact (Formalism.HermitianLattices.GenusMassVolumes.grassmannian_volume (nPlus ε) (nMinus ε)).2
      have key := Formalism.HermitianLattices.GenusMassVolumes.joint_upper_bound (nPlus ε) (nMinus ε) N _
        (Module.finrank ℂ (lowKSub ε lam σ) : ℝ) (cGr (nPlus ε) (nMinus ε)) c0 (lamAbs lam) hd hτp
        (grassmannVolumeConst_pos _ _) hc0 hlp (by omega) hg hUU
      refine le_trans key ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine pow_le_pow_left₀ (by positivity) ?_ _
      have e : C3 * p * q * (N : ℝ) * lamAbs lam = C3 * (((nPlus ε * nMinus ε : ℕ) : ℝ) * N * lamAbs lam) := by
        rw [← hexp]; ring
      rw [e, mul_assoc, mul_assoc]
      rw [← mul_assoc ((nPlus ε * nMinus ε : ℕ) : ℝ)]
      exact mul_le_mul_of_nonneg_right hC (by positivity)

theorem stmt3All_of_steps (D : D7) (C3 c0 : ℝ) (hc0 : 0 < c0) (hC : 2 / c0 ≤ C3)
    (hL : Adm3 D → cdScaleTie D → FormalDegreeLowerBound D C3) (hU : Adm3 D → cdScaleTie D → FormalDegreeUpperBound D C3 c0) : TheoremThreeCompactDual D C3 :=
  fun hA hc => formalDegreeBound_all_unitaryGroups D C3 c0 hc0 hC hA.2.1 hA.2.2 (hL hA hc) (hU hA hc)

theorem familyFormalDegree_all {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C3 c0 : ℝ) (hc0 : 0 < c0) (hC : 2 / c0 ≤ C3)
    (hL : FamilyTheoremThreeAdmitted Fm → ∀ x (i : Fm.Ix x), FormalDegreeLowerBound (Fm.D x i) C3)
    (hU : FamilyTheoremThreeAdmitted Fm → ∀ x (i : Fm.Ix x), FormalDegreeUpperBound (Fm.D x i) C3 c0) : FamilyTheoremThreeAll Fm C3 :=
  fun hA x i => formalDegreeBound_all_unitaryGroups (Fm.D x i) C3 c0 hc0 hC (hA x i).2.1 (hA x i).2.2 (hL hA x i) (hU hA x i)

end T3

theorem host_v_pos (D : D7) : 0 < D.host.v := by
  unfold Host.v Host.rdE
  have h : (0 : ℝ) < |(discr D.host.E : ℝ)| := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
  have := Real.rpow_pos_of_pos h ((1 : ℝ) / (Module.finrank ℚ D.host.E : ℝ))
  linarith

def VolumeRatio₂ (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (P, Q)) → 3 ≤ W.rank →
    ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) →
    ∃ x : W.V, W.hT x x = (if s then 1 else -1) ∧
      ∃ (W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V),
        HSpace.IsIsomEmb W' W ι ∧ LinearMap.range ι = LinearMap.ker (W.hT x) ∧ W'.SigOK ∧
        (∀ τ, W'.sig τ = (if s then (P - 1, Q) else (P, Q - 1))) ∧
        D.vol W' / D.vol W =
          ((2 * Real.pi) ^ W.rank / ((W.rank - 1).factorial : ℝ)) ^ D.R.f *
            ((2 * D.host.v) ^ D.R.f) ^ ((1 : ℝ) / 2 - W.rank) / Formalism.HermitianLatticesTheory.lValEta D.host.E W.rank

theorem volumeMass_of_unfolding (D : D7) (h : VolumeRatio₂ D) : Conclusion2 D := by
  let _ := D.host.cmStar
  intro W P Q hS hsig hr s hs
  obtain ⟨x, hx, W', ι, h1, h2, h3, h4, h5⟩ := h W P Q hS hsig hr s hs
  refine ⟨x, hx, W', ι, h1, h2, h3, h4, ?_⟩
  have key := Formalism.HermitianLattices.GenusMassVolumes.global_arithmetic_identity D.R.f W.rank D.host.v (Formalism.HermitianLatticesTheory.lValEta D.host.E W.rank)
    (by omega) (host_v_pos D) (lVal_pos D _ (by omega))
  rw [mass_ratio_eq]
  unfold ratioH
  refine Eq.trans ?_ key
  rw [← h5, inv_div]

end Formalism.MainNotions.StandardLattice
