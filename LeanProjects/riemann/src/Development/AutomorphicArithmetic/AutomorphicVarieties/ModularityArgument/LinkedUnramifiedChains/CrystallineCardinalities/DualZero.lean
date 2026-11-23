import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrDual

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

private theorem exists_nat_sub_mem_span_pow_and_toZModPow_eq_and_toZMod_eq (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (k : ℕ) (hk : 0 < k) (a : ℤ_[l]) :
    ∃ n : ℕ, algebraMap ℤ_[l] O a - n ∈ Ideal.span {(l : O) ^ k} ∧
      PadicInt.toZModPow k a = n ∧ PadicInt.toZMod a = n := by
  have h1 : PadicInt.toZModPow k a = ((PadicInt.toZModPow k a).val : ZMod (l ^ k)) :=
    (ZMod.natCast_zmod_val _).symm
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (PadicInt.toZModPow k a).val = n := ⟨_, rfl⟩
  rw [hn] at h1
  have h2 : a - (n : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ k} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ← h1, sub_self]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp h2
  have ha : a = (n : ℤ_[l]) + (l : ℤ_[l]) ^ k * t := by
    rw [← ht]; ring
  refine ⟨n, ?_, h1, ?_⟩
  · rw [Ideal.mem_span_singleton]
    refine ⟨algebraMap ℤ_[l] O t, ?_⟩
    rw [ha, map_add, map_mul, map_pow, map_natCast, map_natCast]
    ring
  · rw [ha, map_add, map_mul, map_pow, map_natCast, map_natCast, ZMod.natCast_self,
      zero_pow hk.ne', zero_mul, add_zero]

theorem UpperTheory.V.Z.J.dualZero :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → (l : O) ≠ 0 → ∀ (ρ : NRep F 3 O) (B : Box F 3 O), UpperTheory.V.Fr.IsLift O ρ → B.Of ρ → B.Cont (maximalIdeal O) → ∀ k, 0 < k → HomMu l k F.eps (adK B k) = {0} := by
  intro l _ O _ _ _ _ _ F C₀ hF hl ρ B hL hB hC k hk
  haveI : CharP (ResidueField O) l := IsCoef.char
  have hlm : (l : O) ∈ maximalIdeal O := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero]
  have hI0m : Ideal.span {(l : O) ^ k} ≤ maximalIdeal O := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.pow_mem_of_mem _ hlm _ hk
  set π : O →+* Ok l O k := Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) with hπ
  set φ : Ok l O k →+* ResidueField O :=
    Ideal.Quotient.lift (Ideal.span {(l : O) ^ k}) (IsLocalRing.residue O)
      (fun x hx => (IsLocalRing.residue_eq_zero_iff x).mpr (hI0m hx)) with hφ
  have hφπ : ∀ x, φ (π x) = IsLocalRing.residue O x := fun x => rfl
  have hπs : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hunit : ∀ x : Ok l O k, φ x ≠ 0 → IsUnit x := by
    intro x hx
    obtain ⟨y, rfl⟩ := hπs x
    rw [hφπ] at hx
    have hy : IsUnit y := by
      by_contra h
      exact hx ((IsLocalRing.residue_eq_zero_iff y).mpr ((IsLocalRing.mem_maximalIdeal y).mpr h))
    exact hy.map π
  set I : Ideal (Ok l O k) := (maximalIdeal O).map π with hIdef
  have hIφ : ∀ x ∈ I, φ x = 0 := by
    have hle : I ≤ RingHom.ker φ := by
      rw [hIdef, Ideal.map_le_iff_le_comap]
      intro y hy
      rw [Ideal.mem_comap, RingHom.mem_ker, hφπ]
      exact (IsLocalRing.residue_eq_zero_iff y).mpr hy
    intro x hx
    exact hle hx
  have hφI : ∀ x, φ x = 0 → x ∈ I := by
    intro x hx
    obtain ⟨y, rfl⟩ := hπs x
    rw [hφπ, IsLocalRing.residue_eq_zero_iff] at hx
    exact Ideal.mem_map_of_mem π hx
  have hjac : I ≤ Ideal.jacobson ⊥ := by
    intro x hx
    rw [Ideal.mem_jacobson_bot]
    intro y
    apply hunit
    rw [map_add, map_mul, hIφ x hx, zero_mul, zero_add, map_one]
    exact one_ne_zero
  ext f
  rw [Set.mem_singleton_iff]
  constructor
  swap
  · rintro rfl
    intro s x
    simp
  intro hf
  have hf' : ∀ s x, f (adK B k s x) = PadicInt.toZModPow k (F.eps s : ℤ_[l]) * f x := hf
  have hlin : ∀ (s : F.Γ) (c : Ok l O k) (x : Matrix (Fin 3) (Fin 3) (Ok l O k)),
      adK B k s (c • x) = c • adK B k s x := by
    intro s c x
    show (boxK B k).ad s (c • x) = c • (boxK B k).ad s x
    exact map_smul _ _ _
  have hbr : ∀ (a : ℤ_[l]) (x : Matrix (Fin 3) (Fin 3) (Ok l O k)),
      f (π (algebraMap ℤ_[l] O a) • x) = PadicInt.toZModPow k a * f x := by
    intro a x
    obtain ⟨n, hn1, hn2, -⟩ := exists_nat_sub_mem_span_pow_and_toZModPow_eq_and_toZMod_eq l O k hk a
    have he : π (algebraMap ℤ_[l] O a) = (n : Ok l O k) := by
      rw [← sub_eq_zero, ← map_natCast π, ← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hn1
    rw [he, hn2, Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]
  let N : Submodule (Ok l O k) (Matrix (Fin 3) (Fin 3) (Ok l O k)) :=
    { carrier := {x | ∀ c : Ok l O k, f (c • x) = 0}
      add_mem' := by
        intro x y hx hy c
        rw [smul_add, map_add, hx c, hy c, add_zero]
      zero_mem' := by
        intro c
        rw [smul_zero, map_zero]
      smul_mem' := by
        intro d x hx c
        rw [smul_smul]
        exact hx _ }
  have hP : ∀ (s : F.Γ) x, adK B k s x - π (algebraMap ℤ_[l] O (F.eps s)) • x ∈ N := by
    intro s x c
    rw [smul_sub, ← hlin, smul_comm, map_sub, hf' s, hbr]
    ring
  suffices hN : (⊤ : Submodule (Ok l O k) (Matrix (Fin 3) (Fin 3) (Ok l O k))) ≤ N by
    ext x
    have := hN (Submodule.mem_top (x := x)) 1
    rw [one_smul] at this
    simpa using this
  have hIm : ∀ x : Matrix (Fin 3) (Fin 3) (Ok l O k), (∀ i j, x i j ∈ I) →
      x ∈ I • (⊤ : Submodule (Ok l O k) (Matrix (Fin 3) (Fin 3) (Ok l O k))) := by
    intro x hx
    rw [Matrix.matrix_eq_sum_single x]
    refine Submodule.sum_mem _ (fun i _ => Submodule.sum_mem _ (fun j _ => ?_))
    rw [show Matrix.single i j (x i j) = x i j • Matrix.single i j (1 : Ok l O k) by simp]
    exact Submodule.smul_mem_smul (hx i j) Submodule.mem_top
  have hkey : ∀ (a b : Fin 3) (s : F.Γ),
      φ (adK B k s (Matrix.single a b 1) a b) ≠ φ (π (algebraMap ℤ_[l] O (F.eps s))) →
      (∀ i j, ¬(a = i ∧ b = j) → φ (adK B k s (Matrix.single a b 1) i j) = 0) →
      Matrix.single a b (1 : Ok l O k) ∈ N ⊔ I • ⊤ := by
    intro a b s hu hz
    have hYN := hP s (Matrix.single a b 1)
    set Y := adK B k s (Matrix.single a b 1) - π (algebraMap ℤ_[l] O (F.eps s)) •
      Matrix.single a b (1 : Ok l O k) with hY
    have huu : IsUnit (Y a b) := by
      apply hunit
      rw [hY, Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply_same, smul_eq_mul, mul_one,
        map_sub]
      exact sub_ne_zero.mpr hu
    obtain ⟨v, hv⟩ := huu
    have hR : Y - Y a b • Matrix.single a b 1 ∈
        I • (⊤ : Submodule (Ok l O k) (Matrix (Fin 3) (Fin 3) (Ok l O k))) := by
      apply hIm
      intro i j
      by_cases hij : a = i ∧ b = j
      · obtain ⟨rfl, rfl⟩ := hij
        rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply_same, smul_eq_mul, mul_one,
          sub_self]
        exact I.zero_mem
      · apply hφI
        simp only [hY, Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply_of_ne _ _ _ _ _ hij,
          smul_eq_mul, mul_zero, sub_zero]
        exact hz i j hij
    have hsplit : Matrix.single a b (1 : Ok l O k) =
        (↑v⁻¹ : Ok l O k) • Y - (↑v⁻¹ : Ok l O k) • (Y - Y a b • Matrix.single a b 1) := by
      rw [smul_sub (↑v⁻¹ : Ok l O k) Y, sub_sub_cancel, smul_smul, ← hv, Units.inv_mul, one_smul]
    rw [hsplit]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _ hYN))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ hR))
  have hE : ∀ a b : Fin 3, Matrix.single a b (1 : Ok l O k) ∈ N ⊔ I • ⊤ := by
    have hres : ∀ x : O, res O O x = IsLocalRing.residue O x := by
      intro x
      simp [res, RingEquiv.symm_apply_eq]
    have had1 : ∀ s : F.Γ, (B.r s).right = 1 → ∀ X : Matrix (Fin 3) (Fin 3) (Ok l O k),
        adK B k s X = π.mapMatrix (B.r s).mat * X * π.mapMatrix ↑(B.r s).left⁻¹ := by
      intro s hs X
      show GG.adFun ((boxK B k).r s) X = _
      simp only [GG.adFun]
      rw [if_pos (show ((boxK B k).r s).right = 1 from hs)]
      rfl
    have hG0 : ∀ (h : F.G0) (a b i j : Fin 3), φ (adK B k ↑h (Matrix.single a b 1) i j) =
        if a = i ∧ b = j then ((F.Ψ ↑h ^ (w 3 a - w 3 b) : (ResidueField O)ˣ) : ResidueField O)
        else 0 := by
      intro h a b i j
      have hr : (B.r ↑h).right = 1 := by rw [B.nu]; exact h.2
      have hM : (B.r ↑h).mat = ρ.r h := hB.res h
      have hD : ∀ p q, IsLocalRing.residue O ((B.r ↑h).mat p q) =
          if p = q then ((F.Ψ ↑h ^ w 3 p : (ResidueField O)ˣ) : ResidueField O) else 0 := by
        intro p q
        rw [hM, ← hres]
        split_ifs with hpq
        · subst hpq; exact hL.2.1.1 h p
        · exact hL.2.2 h p q hpq
      have hinv : (B.r ↑h).mat * (↑(B.r ↑h).left⁻¹ : Matrix (Fin 3) (Fin 3) O) = 1 :=
        Units.mul_inv _
      have hR : ∀ p q, IsLocalRing.residue O ((↑(B.r ↑h).left⁻¹ : Matrix (Fin 3) (Fin 3) O) p q) =
          if p = q then (((F.Ψ ↑h ^ w 3 p)⁻¹ : (ResidueField O)ˣ) : ResidueField O) else 0 := by
        intro p q
        have e := congrArg (fun A => IsLocalRing.residue O (A p q)) hinv
        simp only [Matrix.mul_apply, map_sum, map_mul, hD, ite_mul, zero_mul, Finset.sum_ite_eq,
          Finset.mem_univ, if_true, Matrix.one_apply, apply_ite (IsLocalRing.residue O), map_one,
          map_zero] at e
        have hu : ((F.Ψ ↑h ^ w 3 p : (ResidueField O)ˣ) : ResidueField O) ≠ 0 := Units.ne_zero _
        split_ifs with hpq
        · rw [if_pos hpq] at e
          calc _ = (((F.Ψ ↑h ^ w 3 p)⁻¹ : (ResidueField O)ˣ) : ResidueField O) *
                (((F.Ψ ↑h ^ w 3 p : (ResidueField O)ˣ) : ResidueField O) *
                  IsLocalRing.residue O ((↑(B.r ↑h).left⁻¹ : Matrix (Fin 3) (Fin 3) O) p q)) := by
                rw [← mul_assoc, Units.inv_mul, one_mul]
            _ = _ := by rw [e, mul_one]
        · rw [if_neg hpq] at e
          exact (mul_eq_zero.mp e).resolve_left hu
      have hDm : (IsLocalRing.residue O).mapMatrix (B.r ↑h).mat =
          Matrix.diagonal (fun p => ((F.Ψ ↑h ^ w 3 p : (ResidueField O)ˣ) : ResidueField O)) := by
        ext p q
        rw [RingHom.mapMatrix_apply, Matrix.map_apply, hD, Matrix.diagonal_apply]
      have hRm : (IsLocalRing.residue O).mapMatrix (↑(B.r ↑h).left⁻¹ : Matrix (Fin 3) (Fin 3) O) =
          Matrix.diagonal (fun p => (((F.Ψ ↑h ^ w 3 p)⁻¹ : (ResidueField O)ˣ) : ResidueField O)) := by
        ext p q
        rw [RingHom.mapMatrix_apply, Matrix.map_apply, hR, Matrix.diagonal_apply]
      have hφX : φ.mapMatrix (Matrix.single a b (1 : Ok l O k)) = Matrix.single a b 1 := by
        ext p q
        rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.single_apply, Matrix.single_apply]
        split_ifs <;> simp
      have e1 : φ (adK B k ↑h (Matrix.single a b 1) i j) =
          ((IsLocalRing.residue O).mapMatrix (B.r ↑h).mat * φ.mapMatrix (Matrix.single a b 1) *
            (IsLocalRing.residue O).mapMatrix (↑(B.r ↑h).left⁻¹ : Matrix (Fin 3) (Fin 3) O)) i j := by
        rw [had1 _ hr]
        show φ.mapMatrix (_ * _ * _) i j = _
        rw [map_mul, map_mul]
        rfl
      rw [e1, hDm, hRm, hφX, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
      split_ifs with hab
      · obtain ⟨rfl, rfl⟩ := hab
        rw [mul_one, ← Units.val_mul, ← _root_.zpow_neg, ← _root_.zpow_add, ← sub_eq_add_neg]
      · simp
    have hom : ∀ s : F.Γ, φ (π (algebraMap ℤ_[l] O (F.eps s : ℤ_[l]))) =
        ((F.om (ResidueField O) s : (ResidueField O)ˣ) : ResidueField O) := by
      intro s
      obtain ⟨n, hn1, -, hn3⟩ := exists_nat_sub_mem_span_pow_and_toZModPow_eq_and_toZMod_eq l O k hk (F.eps s : ℤ_[l])
      have he : π (algebraMap ℤ_[l] O (F.eps s : ℤ_[l])) = (n : Ok l O k) := by
        rw [← sub_eq_zero, ← map_natCast π, ← map_sub]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hn1
      rw [he, map_natCast]
      simp [Frame.om, hn3]
    have htheta : ∀ (Y : Matrix (Fin 3) (Fin 3) (Ok l O k)) (i j : Fin 3),
        thetaLie Y i j = -Y j.rev i.rev := by
      intro Y i j
      fin_cases i <;> fin_cases j <;> simp [thetaLie, Jmat, Matrix.mul_apply, Fin.sum_univ_three] <;> rfl
    have hc : ∀ Y : Matrix (Fin 3) (Fin 3) (Ok l O k), adK B k F.c Y = thetaLie Y := by
      intro Y
      have h1 : (B.r F.c).left = 1 := Units.ext hB.atc
      have h2 : (B.r F.c).right ≠ 1 := by rw [B.nu, hF.del_c]; decide
      show GG.adFun ((boxK B k).r F.c) Y = _
      simp only [GG.adFun]
      rw [if_neg (show ((boxK B k).r F.c).right ≠ 1 from h2)]
      have h3 : ((boxK B k).r F.c).mat = 1 := by
        show π.mapMatrix (B.r F.c).mat = 1
        rw [hB.atc, map_one]
      have h4 : (↑((boxK B k).r F.c).left⁻¹ : Matrix (Fin 3) (Fin 3) (Ok l O k)) = 1 := by
        show π.mapMatrix (↑(B.r F.c).left⁻¹ : Matrix (Fin 3) (Fin 3) O) = 1
        rw [h1, inv_one, Units.val_one, map_one]
      rw [h3, h4, one_mul, mul_one]
    have L1 : ∀ a b : Fin 3, (w 3 a - w 3 b = 0 ∨ w 3 a - w 3 b = 1 ∨ w 3 a - w 3 b = -1) →
        Matrix.single a b (1 : Ok l O k) ∈ N ⊔ I • ⊤ := by
      intro a b hw
      rcases hw with h0 | h1
      · obtain ⟨g, hg⟩ := hF.f2a
        apply hkey a b ↑g
        · rw [hG0, if_pos ⟨rfl, rfl⟩, hom, h0, zpow_zero, Units.val_one]
          intro heq
          exact hg (Units.val_eq_one.mp heq.symm)
        · intro i j hij
          rw [hG0, if_neg hij]
      · obtain ⟨g, hg⟩ := hF.f2b (w 3 b - w 3 a) (by omega)
        apply hkey a b ↑g
        · rw [hG0, if_pos ⟨rfl, rfl⟩, hom]
          intro heq
          apply hg
          apply Units.ext
          rw [Units.val_mul, ← heq, ← Units.val_mul, ← _root_.zpow_add, sub_add_sub_cancel, sub_self,
            zpow_zero]
        · intro i j hij
          rw [hG0, if_neg hij]
    have L2 : ∀ a b : Fin 3, b = a.rev → (w 3 a - w 3 b = 2 ∨ w 3 a - w 3 b = -2) →
        Matrix.single a b (1 : Ok l O k) ∈ N ⊔ I • ⊤ := by
      intro a b hb hw
      obtain ⟨g, hg⟩ := hF.f2c (w 3 b - w 3 a) (by omega)
      subst hb
      rcases Int.units_eq_one_or (F.del g) with hd | hd
      · have eG := fun i j => (hG0 ⟨g, hd⟩ a a.rev i j :
          φ (adK B k g (Matrix.single a a.rev 1) i j) = _)
        have hdk : ((F.delK (ResidueField O) g : (ResidueField O)ˣ) : ResidueField O) = 1 := by
          simp [Frame.delK, hd]
        apply hkey a a.rev g
        · rw [eG, if_pos ⟨rfl, rfl⟩, hom]
          intro heq
          apply hg
          apply Units.ext
          rw [Units.val_mul, Units.val_mul, hdk, mul_one, ← heq, ← Units.val_mul, ← _root_.zpow_add,
            sub_add_sub_cancel, sub_self, zpow_zero]
        · intro i j hij
          rw [eG, if_neg hij]
      · have hmem : F.c⁻¹ * g ∈ F.del.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hF.del_c, hd]
          decide
        have hΨ : F.Ψ (F.c⁻¹ * g) = F.Ψ g := by
          rw [map_mul, map_inv, hF.Ψ_c, inv_one, one_mul]
        have hsplit : ∀ X, adK B k g X = thetaLie (adK B k (F.c⁻¹ * g) X) := by
          intro X
          rw [← hc]
          conv_lhs => rw [show g = F.c * (F.c⁻¹ * g) by group]
          rw [map_mul]
          rfl
        have eG := fun i j => (hG0 ⟨F.c⁻¹ * g, hmem⟩ a a.rev i j :
          φ (adK B k (F.c⁻¹ * g) (Matrix.single a a.rev 1) i j) = _)
        have hdk : ((F.delK (ResidueField O) g : (ResidueField O)ˣ) : ResidueField O) = -1 := by
          simp [Frame.delK, hd]
        apply hkey a a.rev g
        · rw [hsplit, htheta, Fin.rev_rev, map_neg, eG, if_pos ⟨rfl, rfl⟩, hom]
          dsimp only
          rw [hΨ]
          intro heq
          apply hg
          apply Units.ext
          rw [Units.val_mul, Units.val_mul, hdk, ← heq, mul_neg_one, neg_mul, neg_neg,
            ← Units.val_mul, ← _root_.zpow_add, sub_add_sub_cancel, sub_self, zpow_zero]
        · intro i j hij
          rw [hsplit, htheta, map_neg, eG, if_neg, neg_zero]
          rintro ⟨h1, h2⟩
          apply hij
          refine ⟨Fin.rev_injective h2, ?_⟩
          rw [h1, Fin.rev_rev]
    intro a b
    fin_cases a <;> fin_cases b
    all_goals first
      | exact L1 _ _ (by decide)
      | exact L2 _ _ (by decide) (by decide)
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := I) Module.Finite.fg_top hjac
  intro x _
  rw [Matrix.matrix_eq_sum_single x]
  refine Submodule.sum_mem _ (fun i _ => Submodule.sum_mem _ (fun j _ => ?_))
  rw [show Matrix.single i j (x i j) = x i j • Matrix.single i j (1 : Ok l O k) by simp]
  exact Submodule.smul_mem _ _ (hE i j)
