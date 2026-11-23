import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PWdUni
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma pk_mem {d : ℕ} {I : Finset (Fin (d + 1))} (h : I.Nonempty) : pk I ∈ I := by
  unfold pk
  rw [dif_pos h]
  exact Finset.min'_mem _ _

private lemma lat_mem (hA : LatA) {F : Type} [Field F] [Algebra ℂ F] {d : ℕ} (x : Fin (d + 1) → Fˣ)
    (hpd : IsPd ℂ (xv x)) (I : Finset (Fin (d + 1))) (i : Fin (d + 1)) (hi : i ∈ I) :
    (∏ m ∈ Iᶜ, ((x m : F) / x i)) ∈ omA ℂ (xv x) I := by
  rw [(hA F d x hpd I i hi).2.1]
  have hne : (∏ m ∈ Iᶜ, ((x m : F) / x i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun m _ => div_ne_zero (x m).ne_zero (x i).ne_zero
  have e : (∏ m ∈ Iᶜ, ((x m : F) / x i)) / omG x i = ∏ m ∈ I, ((x i : F) / x m) := by
    unfold omG
    rw [← Finset.prod_mul_prod_compl I (fun l => (x l : F) / x i), div_mul_cancel_right₀ hne,
      ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun m _ => inv_div _ _
  rw [e]
  exact Subalgebra.prod_mem _ fun m hm => Algebra.subset_adjoin ⟨m, hm, i, rfl⟩

private lemma prod_split {F : Type} [Field F] {d : ℕ} (x : Fin (d + 1) → Fˣ) (I : Finset (Fin (d + 1)))
    (i : Fin (d + 1)) : ∏ m ∈ Iᶜ, (x m : F) = (∏ m ∈ Iᶜ, ((x m : F) / x i)) * (x i : F) ^ Iᶜ.card := by
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun m _ => (div_mul_cancel₀ _ (x i).ne_zero).symm

section
variable {F : Type} (K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]
  {d : ℕ} (x : Fin (d + 1) → Fˣ) (a : ℕ)

private lemma act_tmul (f g : F) (k : K) (w : DR ℂ K) :
    (sysP K x a).act (f ⊗ₜ k) (g ⊗ₜ w) = (f * g) ⊗ₜ (k • w) := by
  simp [sysP, Module.endTensorEndAlgHom_apply]

private lemma mulP_one (w : DR ℂ K) : mulP F K ((1 : F) ⊗ₜ[ℂ] w) = w := by
  simp [mulP]

private lemma X_val (i : Fin (d + 1)) : (((sysP K x a).X i : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) = (x i : F) ⊗ₜ 1 := rfl

private lemma Y_val (i : Fin (d + 1)) : (((sysP K x a).Y i : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) =
    1 ⊗ₜ algebraMap F K (x i) := rfl

end

theorem UpperTheory.Gal.productCup_of_system.pTheta_of :
    MJ → ThMu → ThMuLat → KapInd → LatA → ActsLin → GoodZ → SysBasic → SysOk → PTheta := by
  intro hMJ hTh hLat hKap hLA hAL hG hSB _ F K _ _ _ _ _ _ d x hc a p β hβ
  have hU := wdUni_of
  have hl : ∀ {A B : Type} [LinearOrder A] [LinearOrder B] (b : Finset A) (L : Finset B), lft (uni b L) = b :=
    fun {A B} _ _ b L => (hU A B ℂ (fun _ => 0) (fun _ => 0) b L).2.1
  have hr : ∀ {A B : Type} [LinearOrder A] [LinearOrder B] (b : Finset A) (L : Finset B), rgt (uni b L) = L :=
    fun {A B} _ _ b L => (hU A B ℂ (fun _ => 0) (fun _ => 0) b L).2.2.1
  have hcard : ∀ {A B : Type} [LinearOrder A] [LinearOrder B] (b : Finset A) (L : Finset B),
      (uni b L).card = b.card + L.card :=
    fun {A B} _ _ b L => (hU A B ℂ (fun _ => 0) (fun _ => 0) b L).2.2.2.1
  have hlr : ∀ {A B : Type} [LinearOrder A] [LinearOrder B] (s : Finset (A ⊕ₗ B)), uni (lft s) (rgt s) = s :=
    fun {A B} _ _ s => (hU A B ℂ (fun _ => 0) (fun _ => 0) ∅ ∅).2.2.2.2 s
  have hGood : (sysP K x a).Good := (hG F K d x hc a).2.1
  have hβC : ∀ J, β J ∈ (if J.Nonempty ∧ (J.card : ℤ) = (p : ℤ) + 1 then omB ℂ K (rB ℂ K (xv x) J) a else ⊥) :=
    fun J => hβ.1 J (Set.mem_univ J)
  set b : Finset (Fin (d + 1)) → F ⊗[ℂ] DR ℂ K := fun J => (1 : F) ⊗ₜ[ℂ] β J with hbdef
  have hb0 : ∀ J, ¬ (J.Nonempty ∧ J.card = p + 1) → b J = 0 := by
    intro J hJ
    have h := hβC J
    rw [if_neg (by rintro ⟨h1, h2⟩; exact hJ ⟨h1, by exact_mod_cast h2⟩)] at h
    simp only [hbdef, (Submodule.mem_bot ℂ).1 h, TensorProduct.tmul_zero]
  have hb1 : deltaL ℂ _ _ b = 0 := by
    funext t
    have h0 : deltaL ℂ _ _ β t = 0 := congrFun hβ.2 t
    change ∑ i ∈ t, GlobalTheory.cubeSign t i • b (t.erase i) = 0
    have h1 : ∑ i ∈ t, GlobalTheory.cubeSign t i • β (t.erase i) = 0 := h0
    have h2 := congrArg (TensorProduct.mk ℂ F (DR ℂ K) 1) h1
    rw [map_sum, map_zero] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun i _ => by simp only [hbdef, Units.smul_def, map_zsmul, TensorProduct.mk_apply]
  have hb2 : ∀ J, J.card ≠ p + 1 → b J = 0 := fun J hJ => hb0 J fun h => hJ h.2
  have hθ0 : ∀ (I : Finset (Fin (d + 1))) (L : Finset (Mi d)), I.card + L.card ≠ d + 1 →
      detC (sysP K x a).rowMu (uni I L) = 0 := by
    intro I L h
    unfold detC
    rw [dif_neg (by rw [hcard]; exact h)]
  have hθe : ∀ L : Finset (Mi d), detC (sysP K x a).rowMu (uni ∅ L) = 0 :=
    (hTh d _ _ (sysP K x a)).2.1
  have hval : ∀ (I J : Finset (Fin (d + 1))) (L : Finset (Mi d)),
      (sysP K x a).mj p (detC (sysP K x a).rowMu) b (uni (uni I J) L) =
        ((-1 : ℤ) ^ ((p + 1) * L.card)) • (sysP K x a).act (detC (sysP K x a).rowMu (uni I L)) (b J) := by
    intro I J L
    simp only [Sys.mj, hl, hr]
  have hzero : ∀ (I J : Finset (Fin (d + 1))) (L : Finset (Mi d)),
      (I = ∅ ∨ ¬ (J.Nonempty ∧ J.card = p + 1) ∨ I.card + L.card ≠ d + 1) →
      (sysP K x a).mj p (detC (sysP K x a).rowMu) b (uni (uni I J) L) = 0 := by
    intro I J L h
    rw [hval]
    rcases h with rfl | h | h
    · rw [hθe]; simp
    · rw [hb0 J h]; simp
    · rw [hθ0 I L h]; simp
  refine ⟨(sysP K x a).mj p (detC (sysP K x a).rowMu) b, ?_, ?_, ?_, ?_⟩
  · refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · rw [(hSB d _ _ (sysP K x a) (Mi d) n11 (sysP K x a).mu _).2.1]
      intro I J
      split_ifs with hIJ
      · obtain ⟨hI, hJ⟩ := hIJ
        intro L _
        change (sysP K x a).mj p (detC (sysP K x a).rowMu) b (uni (uni I J) L) ∈ _
        dsimp only
        rw [SetLike.mem_coe]
        split_ifs with hL
        · by_cases hJc : J.card = p + 1
          · have hIL : I.card + L.card = d + 1 := by push_cast [hJc] at hL; omega
            have hi := pk_mem hI
            have hj := pk_mem hJ
            obtain ⟨s, hs, hdet⟩ := (hLat d _ _ (sysP K x a) hGood).2 I J L hI (pk J) hj
            have hbJ : β J ∈ omB ℂ K (rB ℂ K (xv x) J) a := by
              have h := hβC J
              rwa [if_pos ⟨hJ, by exact_mod_cast hJc⟩] at h
            have hcompl : Iᶜ.card = L.card := by
              rw [Finset.card_compl, Fintype.card_fin]; omega
            have hfm := lat_mem hLA x hc.pd I (pk I) hi
            have hsplit := prod_split x I (pk I)
            generalize (∏ m ∈ Iᶜ, ((x m : F) / x (pk I))) = f at hfm hsplit
            have hm : f ⊗ₜ[ℂ] β J ∈ (sysP K x a).M I J := Submodule.apply_mem_map₂ _ hfm hbJ
            have hm' := hGood.stab I J hI hJ s hs _ hm
            have hXprod : ∏ m ∈ Iᶜ, (((sysP K x a).X m : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) =
                (f ⊗ₜ (1 : K)) * (((sysP K x a).X (pk I) : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) ^ L.card := by
              have e := congrArg (Algebra.TensorProduct.includeLeftRingHom : F →+* F ⊗[ℂ] K) hsplit
              rw [map_prod, map_mul, map_pow, hcompl] at e
              exact e
            have hU' : (((∏ l ∈ L, (sysP K x a).u n11 (pk I) (pk J) l : (F ⊗[ℂ] K)ˣ)) : F ⊗[ℂ] K) =
                (((sysP K x a).X (pk I) : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) ^ L.card *
                  (((sysP K x a).Y (pk J) : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) ^ L.card := by
              have : ∀ l : Mi d, (sysP K x a).u n11 (pk I) (pk J) l = (sysP K x a).X (pk I) * (sysP K x a).Y (pk J) := by
                intro l; simp [Sys.u, n11]
              simp only [this, Finset.prod_const, mul_pow, Units.val_mul, Units.val_pow_eq_pow_val]
            have hact : (sysP K x a).act (f ⊗ₜ (1 : K)) (b J) = f ⊗ₜ[ℂ] β J := by
              simp [hbdef, act_tmul]
            rw [hval]
            apply zsmul_mem
            refine ⟨(sysP K x a).act s (f ⊗ₜ[ℂ] β J), hm', ?_⟩
            rw [hdet, hXprod, hU', ← hact, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
            congr 2
            ring
          · rw [hzero I J L (Or.inr (Or.inl fun h => hJc h.2))]
            exact Submodule.zero_mem _
        · have : (sysP K x a).mj p (detC (sysP K x a).rowMu) b (uni (uni I J) L) = 0 := by
            refine hzero I J L ?_
            by_cases hJc : J.card = p + 1
            · refine Or.inr (Or.inr fun h => hL ?_)
              push_cast [hJc]; omega
            · exact Or.inr (Or.inl fun h => hJc h.2)
          rw [this]
          exact Submodule.zero_mem _
      · funext L
        refine hzero I J L ?_
        by_cases hI : I.Nonempty
        · exact Or.inr (Or.inl fun h => hIJ ⟨hI, h.1⟩)
        · exact Or.inl (Finset.not_nonempty_iff_eq_empty.1 hI)
    · exact hMJ d _ _ (sysP K x a) (Mi d) (sysP K x a).mu p _ b (hTh d _ _ (sysP K x a)).1 hb1 hb2
  · intro s L hL
    obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (hlr s).symm⟩
    refine hzero I J L ?_
    by_cases hI : I = ∅
    · exact Or.inl hI
    · refine Or.inr (Or.inr fun h => hI ?_)
      exact Finset.card_eq_zero.1 (by omega)
  · intro s L hL
    obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (hlr s).symm⟩
    have hedge : edge2 β (uni I J) = if I.card = 1 then β J else 0 := by simp only [edge2, hl, hr]
    rw [hedge]
    by_cases hI : I.card = 1
    · rw [if_pos hI]
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hI
      obtain ⟨τ, hτ⟩ := hc.exists_isTop
      have h5 := (hAL F K d x hc τ hτ a).2.2.2.2.1
      have hk := hKap F K d x hc _ _ (sysP K x a)
        (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom ℂ F K) (AlgHom.id ℂ K))
        (fun m => by rw [X_val]; simp) (fun m => by rw [Y_val]; simp) i L hL
      rw [hval, hL, map_zsmul, h5, hk, hbdef]
      simp only [mulP_one]
      rw [smul_comm]
    · rw [if_neg hI, hzero I J L (Or.inr (Or.inr (by omega)))]
      simp
  · intro J
    rw [hval, (hTh d _ _ (sysP K x a)).2.2.1]
    simp [hbdef]
