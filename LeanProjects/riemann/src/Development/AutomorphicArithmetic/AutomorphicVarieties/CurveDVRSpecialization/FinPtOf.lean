import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PropagationTheoremGL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.OneUnitTF
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PointLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CharpolyFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports

set_option linter.overlappingInstances false

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

namespace UpperTheory.V.Pr

private theorem charpoly_of_cyc {A : Type} [CommRing A] (M : Matrix (Fin 3) (Fin 3) A)
    (h01 : M 0 1 * M 1 0 = 0) (h02 : M 0 2 * M 2 0 = 0) (h12 : M 1 2 * M 2 1 = 0)
    (h012 : M 0 1 * (M 1 2 * M 2 0) = 0) (h021 : M 0 2 * (M 2 1 * M 1 0) = 0) :
    M.charpoly = ∏ i, (Polynomial.X - Polynomial.C (M i i)) := by
  have e : ∀ a b : A, a * b = 0 → Polynomial.C a * Polynomial.C b = 0 := fun a b h => by
    rw [← Polynomial.C_mul, h, Polynomial.C_0]
  have e3 : ∀ a b c : A, a * (b * c) = 0 → Polynomial.C a * (Polynomial.C b * Polynomial.C c) = 0 :=
    fun a b c h => by rw [← Polynomial.C_mul, ← Polynomial.C_mul, h, Polynomial.C_0]
  rw [Matrix.charpoly, Matrix.det_fin_three, Fin.prod_univ_three]
  simp only [Matrix.charmatrix_apply_eq, ne_eq, Fin.reduceEq, not_false_eq_true,
    Matrix.charmatrix_apply_ne]
  linear_combination (-(Polynomial.X - Polynomial.C (M 0 0))) * e _ _ h12
    + (-(Polynomial.X - Polynomial.C (M 2 2))) * e _ _ h01
    + (-(Polynomial.X - Polynomial.C (M 1 1))) * e _ _ h02
    - e3 _ _ _ h012 - e3 _ _ _ h021

private theorem char_eq {l : ℕ} [Fact l.Prime] {G A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [Finite (ResidueField A)] [CharP A l]
    (T : Set G) (h : ℕ) (h0 : h ≠ 0)
    (hcl : ∀ (B : Type) [CommGroup B] [Finite B], IsPGroup l B → ∀ χ : G →* B,
      IsOpen (χ.ker : Set G) → (∀ g ∈ T, χ g = 1) → ∀ g, χ g ^ h = 1)
    (a b : G →* Aˣ) (ha : AdicCont (maximalIdeal A) fun g => (a g : A)) (hb : IsOpen (b.ker : Set G))
    (hab : ∀ g, (a g : A) - b g ∈ maximalIdeal A) (hT : ∀ g ∈ T, a g = b g) (g : G) : a g = b g := by
  set m := maximalIdeal A with hm
  set χ : G →* Aˣ := a * b⁻¹ with hχ
  have hχg : ∀ g, χ g = a g * (b g)⁻¹ := fun g => rfl
  have hm1 : ∀ g, ((χ g : Aˣ) : A) - 1 ∈ m := by
    intro g
    have : ((χ g : Aˣ) : A) - 1 = ((a g : A) - b g) * ((b g)⁻¹ : Aˣ) := by
      rw [hχg, Units.val_mul, sub_mul, Units.mul_inv]
    rw [this]
    exact Ideal.mul_mem_right _ _ (hab g)
  have hfinA : Finite (A ⧸ m) := inferInstanceAs (Finite (ResidueField A))
  have hpowN : ∀ (N : ℕ) g, ((χ g : Aˣ) : A) ^ (l ^ N) - 1 ∈ m ^ N := by
    intro N g
    have hx : ((χ g : Aˣ) : A) = 1 + (((χ g : Aˣ) : A) - 1) := by ring
    rw [hx, add_pow_char_pow, one_pow, add_sub_cancel_left]
    exact Ideal.pow_le_pow_right (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le
      (Ideal.pow_mem_pow (hm1 g) _)
  have key : ∀ (N : ℕ) g, ((χ g : Aˣ) : A) ^ h - 1 ∈ m ^ N := by
    intro N
    haveI : Finite (A ⧸ m ^ N) := Ideal.finite_quotient_pow (IsNoetherian.noetherian m) N
    let q := Ideal.Quotient.mk (m ^ N)
    let χN : G →* (A ⧸ m ^ N)ˣ := (Units.map (q : A →* A ⧸ m ^ N)).comp χ
    let S : Subgroup (A ⧸ m ^ N)ˣ := (powMonoidHom (l ^ N) : (A ⧸ m ^ N)ˣ →* (A ⧸ m ^ N)ˣ).ker
    have hS : ∀ g, χN g ∈ S := by
      intro g
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      ext
      simp only [χN, MonoidHom.comp_apply, Units.val_pow_eq_pow_val, Units.coe_map, Units.val_one,
        MonoidHom.coe_coe]
      rw [← map_pow, ← map_one q, Ideal.Quotient.eq]
      exact hpowN N g
    let χ' : G →* S := χN.codRestrict S hS
    have hp : IsPGroup l S := fun x => ⟨N, Subtype.ext (by
      have := x.2
      rw [MonoidHom.mem_ker, powMonoidHom_apply] at this
      simpa using this)⟩
    have hval : ∀ g, χ' g = 1 ↔ q ((χ g : Aˣ) : A) = 1 := by
      intro g
      constructor
      · intro e
        have := congrArg (fun x : S => ((x : (A ⧸ m ^ N)ˣ) : A ⧸ m ^ N)) e
        simpa [χ', χN] using this
      · intro e
        apply Subtype.ext
        apply Units.ext
        simpa [χ', χN] using e
    have hopen : IsOpen (χ'.ker : Set G) := by
      apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
      have hU : IsOpen ({x | q (a x : A) = q (a 1 : A)} ∩ (b.ker : Set G)) :=
        ((ha N).isOpen_fiber _).inter hb
      refine Filter.mem_of_superset (hU.mem_nhds ⟨rfl, b.ker.one_mem⟩) ?_
      rintro x ⟨hx1, hx2⟩
      show χ' x = 1
      rw [hval]
      have hbx : b x = 1 := hx2
      simp only [Set.mem_setOf_eq, map_one, Units.val_one] at hx1
      rw [hχg, hbx, inv_one, mul_one]
      exact hx1
    have hT' : ∀ g ∈ T, χ' g = 1 := by
      intro g hg
      rw [hval, hχg, hT g hg, mul_inv_cancel, Units.val_one, map_one]
    intro g
    have := hcl S hp χ' hopen hT' g
    rw [← map_pow, hval] at this
    rw [← Ideal.Quotient.eq, map_one]
    simpa using this
  have hbot : ((χ g : Aˣ) : A) ^ h - 1 ∈ (⨅ N : ℕ, m ^ N) := Ideal.mem_iInf.2 (fun N => key N g)
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing m (Ideal.IsPrime.ne_top inferInstance), Ideal.mem_bot,
    sub_eq_zero] at hbot
  have h1 := UpperTheory.V.Pr.T.oneUnitTF l _ h h0 (hm1 g) hbot
  have h2 : χ g = 1 := Units.ext h1
  rw [hχg, mul_inv_eq_one] at h2
  exact h2

private theorem diag_eq {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}
    (hF : F.Ok C₀) {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [Finite (ResidueField A)] (j : k →+* A) (ρ : NRep F 3 A) (hc : ρ.Cont (maximalIdeal A))
    (hbar : ∀ g i, ρ.r g i i - j ((F.Ψ g ^ w 3 i : kˣ) : k) ∈ maximalIdeal A)
    (hmul : ∀ g h i, ρ.r (g * h) i i = ρ.r g i i * ρ.r h i i)
    (h1 : ∀ v, ∀ g ∈ F.Iv v, F.Ψ (F.loc v g) = 1 → ∀ i, ρ.r (F.loc0 v g) i i = 1) (g : F.G0) (i : Fin 3) :
    ρ.r g i i = j ((F.Ψ g ^ w 3 i : kˣ) : k) := by
  haveI : CharP A l := charP_of_injective_ringHom j.injective l
  obtain ⟨h, h0, hcl⟩ := hF.cl
  choose u a₀ hu _ hgen using hF.gen
  have hstar := UpperTheory.V.Fr.star hF
  have hconj : ∀ x : F.G0, F.conj x = F.star x⁻¹ := by
    intro x; simp [Frame.star]
  have hconjc : Continuous F.conj := by
    have : (F.conj : F.G0 → F.G0) = F.star ∘ (fun x => x⁻¹) := funext hconj
    rw [this]
    exact hstar.2.2.2.1.comp continuous_inv
  have hinv1 : ∀ (x : F.G0) (i' : Fin 3), ρ.r x i' i' = 1 → ρ.r x⁻¹ i' i' = 1 := by
    intro x i' hx
    have := hmul x⁻¹ x i'
    rw [inv_mul_cancel, map_one, Matrix.one_apply_eq, hx, mul_one] at this
    exact this.symm
  let T : Set F.G0 := {x | ∃ (p : F.V × Bool) (a : Fin (F.dv p.1)), x = F.loc2 p (u p.1 a)}
  have hcl' : ∀ (B : Type) [CommGroup B] [Finite B], IsPGroup l B → ∀ χ : F.G0 →* B,
      IsOpen (χ.ker : Set F.G0) → (∀ g ∈ T, χ g = 1) → ∀ g, χ g ^ h = 1 := by
    intro B _ _ hp χ hχ hT
    apply hcl B hp χ hχ
    intro p g hg
    have hcont : Continuous (F.loc2 p) := by
      obtain ⟨v, bb⟩ := p
      cases bb
      · simpa [Frame.loc2] using hF.loc_cont v
      · simpa [Frame.loc2] using hconjc.comp (hF.loc_cont v)
    have hop : IsOpen ((χ.comp (F.loc2 p)).ker : Set (F.Gv p.1)) := by
      rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
      exact hχ.preimage hcont
    exact hgen p.1 B hp (χ.comp (F.loc2 p)) hop (fun a => hT _ ⟨p, a, rfl⟩) g hg
  let a : F.G0 →* Aˣ :=
    { toFun := fun g => ⟨ρ.r g i i, ρ.r g⁻¹ i i,
        by rw [← hmul, mul_inv_cancel, map_one, Matrix.one_apply_eq],
        by rw [← hmul, inv_mul_cancel, map_one, Matrix.one_apply_eq]⟩
      map_one' := Units.ext (by simp)
      map_mul' := fun g g' => Units.ext (by simp [hmul]) }
  let b : F.G0 →* Aˣ :=
    (Units.map (j : k →* A)).comp ((zpowGroupHom (w 3 i)).comp (F.Ψ.comp F.del.ker.subtype))
  have hb : IsOpen (b.ker : Set F.G0) := by
    refine Subgroup.isOpen_mono (H₁ := F.Ψ.ker.comap F.del.ker.subtype) ?_ ?_
    · intro x hx
      rw [Subgroup.mem_comap, MonoidHom.mem_ker] at hx
      rw [MonoidHom.mem_ker]
      show Units.map (j : k →* A) ((F.Ψ (F.del.ker.subtype x)) ^ (w 3 i)) = 1
      rw [hx, _root_.one_zpow, map_one]
    · rw [Subgroup.coe_comap]
      exact hF.Ψ_open.preimage continuous_subtype_val
  have ha : AdicCont (maximalIdeal A) fun g => ((a g : Aˣ) : A) := hc.1 i i
  have hab : ∀ g, ((a g : Aˣ) : A) - b g ∈ maximalIdeal A := fun g => hbar g i
  have hT : ∀ g ∈ T, a g = b g := by
    rintro x ⟨⟨v, bb⟩, a', rfl⟩
    obtain ⟨hIv, hΨ⟩ := hu v a'
    have hΨ0 : F.Ψ ((F.loc0 v (u v a') : F.G0) : F.Γ) = 1 := hΨ
    apply Units.ext
    cases bb
    · have e1 := h1 v _ hIv hΨ i
      simp [a, b, Frame.loc2, e1, hΨ0]
    · have e1 := h1 v _ hIv hΨ i.rev
      have e2 : ρ.r (F.conj (F.loc0 v (u v a'))) i i = 1 := by
        rw [hconj, hstar.2.2.2.2]
        exact hinv1 _ _ e1
      have e3 : F.Ψ ((F.conj (F.loc0 v (u v a')) : F.G0) : F.Γ) = 1 := by
        rw [hconj, hstar.2.2.1, Subgroup.coe_inv, map_inv, hΨ0, inv_one, inv_one]
      simp [a, b, Frame.loc2, e2, e3]
  have := char_eq T h h0 hcl' a b ha hb hab hT g
  exact congrArg Units.val this

theorem finPtOf : FinPtOf := by
  intro l _ O _ _ _ _ F C₀ hF S hoff A _ _ _ _ _ ρ hρ hψ g
  haveI : IsLocalHom (algebraMap O A) := UpperTheory.V.Pr.IsCD.isLocalHom
  haveI : Finite (IsLocalRing.ResidueField A) := UpperTheory.V.Pr.IsCD.fin (O := O)
  haveI : IsNoetherianRing A := PrincipalIdealRing.isNoetherianRing
  have hCL : UpperTheory.V.CA.IsCL O A :=
    ⟨inferInstance, UpperTheory.V.Pr.IsCD.complete (O := O), inferInstance, Module.Finite.of_finite⟩
  have hres : ∀ x : ResidueField O,
      IsLocalRing.ResidueField.map (algebraMap O A) x
        = IsLocalRing.residue A (algebraMap (ResidueField O) A x) := by
    intro x
    obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective x
    rw [IsLocalRing.ResidueField.map_residue]
    congr 1
    rw [IsScalarTower.algebraMap_apply O (ResidueField O) A o, IsLocalRing.ResidueField.algebraMap_eq]
  obtain ⟨ξ, hξ, -⟩ := UpperTheory.V.Fr.point_loc hF (Or.inr rfl) S A hCL
    (IsLocalRing.ResidueField.map (algebraMap O A))
    (fun a => IsLocalRing.ResidueField.map_residue _ a) ρ hρ.cont hρ.bar
  have hent : ∀ g i j, ρ.r g i j = ξ (S.u.r g i j) := by
    intro g i j; rw [← hξ]; rfl
  have hψent : ∀ v i x, ((ρ.ψ v i x : Aˣ) : A) = ξ ((S.u.ψ v i x : (↥S.A)ˣ) : S.A) := by
    intro v i x; rw [← hξ]; rfl
  suffices key : (∀ g : F.G0, ρ.r g 0 1 * ρ.r g 1 0 = 0 ∧ ρ.r g 0 2 * ρ.r g 2 0 = 0 ∧
      ρ.r g 1 2 * ρ.r g 2 1 = 0 ∧ ρ.r g 0 1 * (ρ.r g 1 2 * ρ.r g 2 0) = 0 ∧
      ρ.r g 0 2 * (ρ.r g 2 1 * ρ.r g 1 0) = 0) ∧
      (∀ (g : F.G0) (i : Fin 3), ρ.r g i i
        = algebraMap (ResidueField O) A ((F.Ψ (g : F.Γ) ^ w 3 i : (ResidueField O)ˣ) : ResidueField O)) by
    obtain ⟨hc, hd⟩ := key
    obtain ⟨c1, c2, c3, c4, c5⟩ := hc g
    rw [charpoly_of_cyc _ c1 c2 c3 c4 c5]
    exact Finset.prod_congr rfl (fun i _ => by rw [hd])
  by_cases hOT : S.u.OffTri (RingHom.ker (ξ : S.A →+* A))
  · obtain ⟨I, hI, hIle⟩ := hoff
    have hIP := hIle _ (RingHom.ker_isPrime _) hOT
    let φ : S.B →+* A := (ξ : S.A →+* A).comp (S.inc : S.B →+* S.A)
    have hP : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
    have hlam : S.lamId ≤ RingHom.ker φ := by
      refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap]
        intro o ho
        rw [Ideal.mem_comap, RingHom.mem_ker]
        show ξ (S.inc (algebraMap O S.B o)) = 0
        rw [AlgHom.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply O (ResidueField O) A,
          IsLocalRing.ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff o).2 ho, map_zero]
      · rw [Ideal.span_le]
        rintro x ⟨v, i, y, hy, hΨ, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
        have e : S.inc (S.ψB v i y) = ((S.u.ψ v i y : (↥S.A)ˣ) : S.A) := rfl
        show ξ (S.inc (S.ψB v i y)) = 1
        rw [e, ← hψent, hψ v i y hy hΨ, Units.val_one]
    have hIφ : I ≤ RingHom.ker φ := fun x hx => hIP hx
    have hmB : S.mB ≤ RingHom.ker φ :=
      hI.trans ((Ideal.IsPrime.radical_le_iff hP).2 (sup_le hIφ hlam))
    have hval : ∀ c : S.B, φ c = algebraMap (ResidueField O) A (res O S.R (c : S.R)) := by
      intro c
      obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (res O S.R (c : S.R))
      have hk : φ (c - algebraMap O S.B o) = 0 := by
        apply hmB
        show ((c - algebraMap O S.B o : S.B) : S.R) ∈ maximalIdeal S.R
        rw [← res_eq_zero_iff O S.R]
        rw [Subalgebra.coe_sub, Subalgebra.coe_algebraMap, map_sub, AlgHom.commutes,
          IsLocalRing.ResidueField.algebraMap_eq, ho, sub_self]
      rw [map_sub, sub_eq_zero] at hk
      rw [hk, ← ho]
      show ξ (S.inc (algebraMap O S.B o)) = _
      rw [AlgHom.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply O (ResidueField O) A,
        IsLocalRing.ResidueField.algebraMap_eq]
    have hprod : ∀ L : List (F.G0 × Fin 3 × Fin 3),
        (L.map (fun s => w 3 s.2.1 - w 3 s.2.2)).sum = 0 → (∃ s ∈ L, s.2.1 ≠ s.2.2) →
        (L.map (fun s => ρ.r s.1 s.2.1 s.2.2)).prod = 0 := by
      intro L hL hne
      have hx : (L.map (fun s => S.ρ.r s.1 s.2.1 s.2.2)).prod ∈ S.B := S.mon_mem ⟨L, hL, rfl⟩
      have e1 : (L.map (fun s => ρ.r s.1 s.2.1 s.2.2)).prod = φ ⟨_, hx⟩ := by
        have e2 : S.inc ⟨_, hx⟩ = (L.map (fun s => S.u.r s.1 s.2.1 s.2.2)).prod := by
          apply Subtype.ext
          show (L.map (fun s => S.ρ.r s.1 s.2.1 s.2.2)).prod = ((S.A.val) (L.map (fun s => S.u.r s.1 s.2.1 s.2.2)).prod)
          rw [map_list_prod, List.map_map]
          rfl
        show _ = ξ (S.inc ⟨_, hx⟩)
        rw [e2, map_list_prod, List.map_map]
        congr 1
        apply List.map_congr_left
        intro s _
        exact hent _ _ _
      rw [e1, hval]
      show algebraMap (ResidueField O) A (res O S.R (L.map (fun s => S.ρ.r s.1 s.2.1 s.2.2)).prod) = 0
      rw [map_list_prod, List.map_map]
      obtain ⟨s, hs, hs'⟩ := hne
      rw [List.prod_eq_zero (List.mem_map.2 ⟨s, hs, S.lift.2.2 s.1 s.2.1 s.2.2 hs'⟩), map_zero]
    refine ⟨fun g => ⟨?_, ?_, ?_, ?_, ?_⟩, fun g i => ?_⟩
    · simpa using hprod [(g, 0, 1), (g, 1, 0)] (by simp [w]) ⟨(g, 0, 1), by simp, by simp⟩
    · simpa using hprod [(g, 0, 2), (g, 2, 0)] (by simp [w]) ⟨(g, 0, 2), by simp, by simp⟩
    · simpa using hprod [(g, 1, 2), (g, 2, 1)] (by simp [w]) ⟨(g, 1, 2), by simp, by simp⟩
    · simpa using hprod [(g, 0, 1), (g, 1, 2), (g, 2, 0)] (by simp [w]) ⟨(g, 0, 1), by simp, by simp⟩
    · simpa using hprod [(g, 0, 2), (g, 2, 1), (g, 1, 0)] (by simp [w]) ⟨(g, 0, 2), by simp, by simp⟩
    · have e : S.inc (S.aB g i) = S.u.r g i i := rfl
      rw [hent, ← e]
      show φ (S.aB g i) = _
      rw [hval]
      congr 1
      exact S.lift.2.1.1 g i
  · have htri : (∀ (g : F.G0) (i j : Fin 3), j < i → ρ.r g i j = 0) ∨
        (∀ (g : F.G0) (i j : Fin 3), i < j → ρ.r g i j = 0) := by
      unfold NRep.OffTri at hOT
      rw [not_and_or, not_not, not_not] at hOT
      rcases hOT with h | h
      · left
        intro g i j hji
        rw [hent]
        exact h (Ideal.subset_span ⟨g, i, j, hji, rfl⟩)
      · right
        intro g i j hij
        rw [hent]
        exact h (Ideal.subset_span ⟨g, i, j, hij, rfl⟩)
    have hcyc : ∀ g : F.G0, ρ.r g 0 1 * ρ.r g 1 0 = 0 ∧ ρ.r g 0 2 * ρ.r g 2 0 = 0 ∧
        ρ.r g 1 2 * ρ.r g 2 1 = 0 ∧ ρ.r g 0 1 * (ρ.r g 1 2 * ρ.r g 2 0) = 0 ∧
        ρ.r g 0 2 * (ρ.r g 2 1 * ρ.r g 1 0) = 0 := by
      intro g
      rcases htri with h | h
      · simp [h g 1 0 (by decide), h g 2 0 (by decide), h g 2 1 (by decide)]
      · simp [h g 0 1 (by decide), h g 0 2 (by decide), h g 1 2 (by decide)]
    refine ⟨hcyc, fun g i => ?_⟩
    have hmul : ∀ (g h : F.G0) (i : Fin 3), ρ.r (g * h) i i = ρ.r g i i * ρ.r h i i := by
      intro g h i
      rw [map_mul, Matrix.mul_apply]
      refine Finset.sum_eq_single i (fun b _ hb => ?_) (fun hi => absurd (Finset.mem_univ i) hi)
      rcases htri with ht | ht <;> rcases lt_or_gt_of_ne hb with hb' | hb'
      · rw [ht g i b hb', zero_mul]
      · rw [ht h b i hb', mul_zero]
      · rw [ht h b i hb', mul_zero]
      · rw [ht g i b hb', zero_mul]
    have hbar : ∀ (g : F.G0) (i : Fin 3), ρ.r g i i
        - algebraMap (ResidueField O) A ((F.Ψ (g : F.Γ) ^ w 3 i : (ResidueField O)ˣ) : ResidueField O)
        ∈ maximalIdeal A := by
      intro g i
      refine Ideal.Quotient.eq.1 ?_
      have hb := hρ.bar.1 g i
      change IsLocalRing.residue A (ρ.r g i i) = _ at hb
      change IsLocalRing.residue A (ρ.r g i i) = IsLocalRing.residue A _
      rw [hb, hres]
    have h1 : ∀ v, ∀ x ∈ F.Iv v, F.Ψ (F.loc v x) = 1 → ∀ i, ρ.r (F.loc0 v x) i i = 1 := by
      intro v x hx hΨ i
      have hcp := UpperTheory.V.Fr.o1 hF (Or.inr rfl) S v x
      have hm : (S.u.r (F.loc0 v x)).map (ξ : S.A →+* A) = ρ.r (F.loc0 v x) := by
        ext a b; rw [hent]; rfl
      have := congrArg (Polynomial.map (ξ : S.A →+* A)) hcp
      rw [← Matrix.charpoly_map, hm, Polynomial.map_prod] at this
      obtain ⟨c1, c2, c3, c4, c5⟩ := hcyc (F.loc0 v x)
      rw [charpoly_of_cyc _ c1 c2 c3 c4 c5] at this
      have hev := congrArg (Polynomial.eval (ρ.r (F.loc0 v x) i i)) this
      rw [Polynomial.eval_prod, Polynomial.eval_prod,
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp)] at hev
      have hone : ∀ j, (ξ : S.A →+* A) ((S.u.ψ v j x : (↥S.A)ˣ) : S.A) = 1 := by
        intro j
        rw [RingHom.coe_coe, ← hψent, hψ v j x hx hΨ, Units.val_one]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hone,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hev
      obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.1 hev.symm
      exact sub_eq_zero.1 hj
    exact diag_eq hF (algebraMap (ResidueField O) A) ρ hρ.cont hbar hmul h1 g i

end UpperTheory.V.Pr
