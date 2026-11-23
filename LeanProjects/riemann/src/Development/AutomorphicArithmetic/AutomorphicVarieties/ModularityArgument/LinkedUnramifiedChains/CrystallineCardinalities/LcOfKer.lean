import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.CjFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.AdicContinuousSumThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.OkFin

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

private theorem lc_of_ker {D N : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [AddCommGroup N]
    (τ : Representation ℤ D N) (h : IsOpen (τ.ker : Set D)) : IsLocallyConstant fun s => τ s := by
  rw [IsLocallyConstant.iff_exists_open]
  intro s
  refine ⟨(fun y => s⁻¹ * y) ⁻¹' (τ.ker : Set D), h.preimage (continuous_mul_left s⁻¹), ?_, ?_⟩
  · show s⁻¹ * s ∈ τ.ker
    rw [inv_mul_cancel]
    exact one_mem _
  · intro y hy
    have hy' : τ (s⁻¹ * y) = 1 := hy
    calc τ y = τ (s * (s⁻¹ * y)) := by rw [mul_inv_cancel_left]
      _ = τ s * τ (s⁻¹ * y) := map_mul τ _ _
      _ = τ s := by rw [hy', mul_one]

private theorem cnt {D N : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [AddCommGroup N] [Finite N]
    (σ τ : Representation ℤ D N) (e : N ≃+ N) (he : ∀ s x, σ s (e x) = e (τ s x)) (h : IsOpen (τ.ker : Set D))
    (A : AddSubgroup (D → N)) [Finite A] (hA : (A : Set (D → N)) ⊆ Zc τ) (T : Set N)
    (hT : ∀ Y, (fun s => τ s Y - Y) ∈ A → Y ∈ T) :
    ∃ Z : AddSubgroup (D → N), (Z : Set (D → N)) = {z | ∃ z' ∈ A, ∃ Y, ∀ s, z s = e (z' s) + (σ s Y - Y)} ∧
      (Z : Set (D → N)) ⊆ Zc σ ∧ (∀ Y, (fun s => σ s Y - Y) ∈ Z) ∧
      Nat.card A * Nat.card N ≤ Nat.card Z * Nat.card T := by
  classical
  let ψ : ↥A × N →+ (D → N) :=
    { toFun := fun p => fun s => e ((p.1 : D → N) s) + (σ s p.2 - p.2)
      map_zero' := by
        funext s
        simp
      map_add' := by
        intro p q
        funext s
        simp only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add, Pi.add_apply, map_add]
        abel }
  have hψ : ∀ p : ↥A × N, ∀ s, ψ p s = e ((p.1 : D → N) s) + (σ s p.2 - p.2) := fun p s => rfl
  have hlc : ∀ Y : N, IsLocallyConstant fun s => σ s Y := by
    intro Y
    have h1 : (fun s => σ s Y) = fun s => e (τ s (e.symm Y)) := by
      funext s
      rw [← he, AddEquiv.apply_symm_apply]
    rw [h1]
    exact (lc_of_ker τ h).comp fun f => e (f (e.symm Y))
  refine ⟨ψ.range, ?_, ?_, ?_, ?_⟩
  · ext z
    constructor
    · rintro ⟨⟨a, Y⟩, rfl⟩
      exact ⟨a, a.2, Y, fun s => rfl⟩
    · rintro ⟨z', hz', Y, hz⟩
      exact ⟨(⟨z', hz'⟩, Y), funext fun s => (hz s).symm⟩
  · rintro z ⟨⟨a, Y⟩, rfl⟩
    have ha := hA a.2
    refine ⟨?_, ?_⟩
    · have h2 : IsLocallyConstant fun s => e ((a : D → N) s) := ha.1.comp e
      exact h2.add ((hlc Y).sub (IsLocallyConstant.const Y))
    · intro s t
      simp only [hψ]
      rw [ha.2 s t]
      simp only [map_add, map_sub, he, map_mul, Module.End.mul_apply]
      abel
  · intro Y
    exact ⟨(0, Y), funext fun s => by simp [hψ]⟩
  · have hcard : Nat.card (↥A × N) = Nat.card ψ.range * Nat.card ψ.ker := by
      rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ψ.ker,
        Nat.card_congr (QuotientAddGroup.quotientKerEquivRange ψ).toEquiv]
    have key : ∀ p : ψ.ker, (fun s => τ s (-e.symm p.1.2) - -e.symm p.1.2) = (p.1.1 : D → N) := by
      rintro ⟨⟨a, Y⟩, hp⟩
      have hp' : ∀ s, e ((a : D → N) s) + (σ s Y - Y) = 0 := fun s => congrFun hp s
      show (fun s => τ s (-e.symm Y) - -e.symm Y) = (a : D → N)
      funext s
      apply e.injective
      simp only [map_sub, map_neg, AddEquiv.apply_symm_apply, ← he]
      rw [eq_neg_of_add_eq_zero_left (hp' s)]
      abel
    let f : ψ.ker → T := fun p => ⟨-e.symm p.1.2, hT _ (by rw [key p]; exact p.1.1.2)⟩
    have hf : Function.Injective f := by
      intro p q hpq
      have h2 : p.1.2 = q.1.2 := by
        have h3 : -e.symm p.1.2 = -e.symm q.1.2 := congrArg Subtype.val hpq
        exact e.symm.injective (neg_injective h3)
      have h1 : (p.1.1 : D → N) = q.1.1 := by
        rw [← key p, ← key q, h2]
      exact Subtype.ext (Prod.ext (Subtype.ext h1) h2)
    have hker : Nat.card ψ.ker ≤ Nat.card T := Nat.card_le_card_of_injective f hf
    calc Nat.card A * Nat.card N = Nat.card (↥A × N) := (Nat.card_prod _ _).symm
      _ = Nat.card ψ.range * Nat.card ψ.ker := hcard
      _ ≤ Nat.card ψ.range * Nat.card T := Nat.mul_le_mul_left _ hker

private theorem card_upT (R : Type) [Zero R] [Finite R] :
    Nat.card {Y : Matrix (Fin 3) (Fin 3) R | UpT Y} ≤ Nat.card R ^ 6 := by
  classical
  have hP : Nat.card {p : Fin 3 × Fin 3 // p.1 ≤ p.2} = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hinj : Function.Injective
      (fun Y : {Y : Matrix (Fin 3) (Fin 3) R | UpT Y} =>
        fun p : {p : Fin 3 × Fin 3 // p.1 ≤ p.2} => (Y : Matrix (Fin 3) (Fin 3) R) p.1.1 p.1.2) := by
    rintro ⟨Y, hY⟩ ⟨Y', hY'⟩ e
    apply Subtype.ext
    ext i j
    show Y i j = Y' i j
    by_cases hij : i ≤ j
    · exact congrFun e ⟨(i, j), hij⟩
    · have hji : j < i := lt_of_not_ge hij
      have h1 : UpT Y := hY
      have h2 : UpT Y' := hY'
      rw [h1 i j hji, h2 i j hji]
  calc Nat.card {Y : Matrix (Fin 3) (Fin 3) R | UpT Y}
      ≤ Nat.card ({p : Fin 3 × Fin 3 // p.1 ≤ p.2} → R) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card R ^ 6 := by rw [Nat.card_fun, hP]

private def cjE {R : Type} [CommRing R] (g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R ≃+ Matrix (Fin 3) (Fin 3) R where
  toFun X := ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * (g : Matrix (Fin 3) (Fin 3) R)
  invFun X := (g : Matrix (Fin 3) (Fin 3) R) * X * ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)
  left_inv X := by simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, Units.mul_inv_cancel_left]
  right_inv X := by simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, Units.inv_mul_cancel_left]
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]

private theorem ad_cj {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    {F : Frame l (ResidueField O)} (B : Box F 3 O) (k : ℕ) (v : F.V) (s : F.Gv v)
    (X : Matrix (Fin 3) (Fin 3) (Ok l O k)) :
    adK B k (F.loc v s) (cjE ((boxK B k).g v) X) = cjE ((boxK B k).g v) (cj k (triOf B v) s X) := by
  have hr : (B.r (F.loc v s)).right = 1 := by
    rw [B.nu]
    exact (F.loc0 v s).2
  have e1 : ∀ A : GL (Fin 3) O, (↑A : Matrix (Fin 3) (Fin 3) O).map (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k})) =
      ↑(GeneralLinearGroup.map (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k})) A) := fun A => rfl
  simp only [adK, Box.ad, adRep, GG.ad, boxK, Box.map, GG.map, cjE, cj, triOf, MonoidHom.comp_apply,
    MonoidHom.coe_mk, OneHom.coe_mk, AddEquiv.coe_mk, Equiv.coe_fn_mk, e1]
  show GG.adFun (m := 3) (R := Ok l O k) _ _ = _
  simp only [GG.adFun, GG.mat, SemidirectProduct.map_left, SemidirectProduct.map_right, MonoidHom.id_apply, hr,
    if_true, map_mul, map_inv, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc,
    Units.inv_mul_cancel_left, Units.mul_inv_cancel_left, Units.inv_mul, Units.mul_inv, Matrix.mul_one]

theorem UpperTheory.V.Z.J.zvCnt :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → (l : O) ≠ 0 → ∀ (ρ : NRep F 3 O) (B : Box F 3 O), UpperTheory.V.Fr.IsLift O ρ → B.Of ρ → B.Cont (maximalIdeal O) → ∀ k, 0 < k → ∀ v, (ZF (l := l) (F.Iv v) k (triOf B v)).Finite → ∃ Z : AddSubgroup (F.Gv v → Matrix (Fin 3) (Fin 3) (Ok l O k)), (Z : Set _) = Zv B k v ∧ (Z : Set _) ⊆ Zc ((adK B k).comp (F.loc v)) ∧ (∀ Y, (fun s => adK B k (F.loc v s) Y - Y) ∈ Z) ∧ (ZF (l := l) (F.Iv v) k (triOf B v)).ncard * Nat.card (Ok l O k) ^ 9 ≤ Nat.card Z * Nat.card (Ok l O k) ^ 6 := by
  intro l _ O _ _ _ _ _ F C₀ hF hl ρ B hlift hOf hCont k hk v hfin
  classical
  obtain ⟨hfinOk, -⟩ := okFin l O hl
  haveI : Finite (Ok l O k) := hfinOk k
  have htri := (triOk l O F C₀ hF hl ρ B hlift hOf hCont v).1
  obtain ⟨⟨ρc, hρc, hker⟩, -, -, -, hup⟩ := cjFacts l O (F.Gv v) (triOf B v) k hl htri
  let A : AddSubgroup (F.Gv v → Matrix (Fin 3) (Fin 3) (Ok l O k)) :=
    { carrier := ZF (l := l) (F.Iv v) k (triOf B v)
      add_mem' := by
        rintro a b ⟨ha1, ha2, ha3, ha4⟩ ⟨hb1, hb2, hb3, hb4⟩
        refine ⟨ha1.add hb1, ?_, ?_, ?_⟩
        · intro s s'
          simp only [Pi.add_apply]
          rw [ha2, hb2, ← hρc, ← hρc, ← hρc, map_add]
          abel
        · intro s i j hij
          simp only [Pi.add_apply, Matrix.add_apply, ha3 s i j hij, hb3 s i j hij, add_zero]
        · intro s hs i
          simp only [Pi.add_apply, Matrix.add_apply, ha4 s hs i, hb4 s hs i, add_zero]
      zero_mem' := by
        refine ⟨IsLocallyConstant.const 0, ?_, ?_, ?_⟩
        · intro s s'
          simp only [Pi.zero_apply]
          rw [← hρc, map_zero, add_zero]
        · intro s i j hij
          rfl
        · intro s hs i
          rfl
      neg_mem' := by
        rintro a ⟨ha1, ha2, ha3, ha4⟩
        refine ⟨ha1.neg, ?_, ?_, ?_⟩
        · intro s s'
          simp only [Pi.neg_apply]
          rw [ha2, ← hρc, ← hρc, map_neg, neg_add]
        · intro s i j hij
          simp only [Pi.neg_apply, Matrix.neg_apply, ha3 s i j hij, neg_zero]
        · intro s hs i
          simp only [Pi.neg_apply, Matrix.neg_apply, ha4 s hs i, neg_zero] }
  have hA : (A : Set (F.Gv v → Matrix (Fin 3) (Fin 3) (Ok l O k))) ⊆ Zc ρc := by
    rintro z ⟨h1, h2, -, -⟩
    exact ⟨h1, fun s t => by rw [h2, hρc]⟩
  haveI : Finite A := hfin.to_subtype
  have hT : ∀ Y, (fun s => ρc s Y - Y) ∈ A → Y ∈ {Y : Matrix (Fin 3) (Fin 3) (Ok l O k) | UpT Y} := by
    rintro Y ⟨-, -, h3, -⟩
    exact hup Y fun s => by
      have := h3 s
      simpa only [hρc] using this
  have he : ∀ s x, ((adK B k).comp (F.loc v)) s (cjE ((boxK B k).g v) x) =
      cjE ((boxK B k).g v) (ρc s x) := by
    intro s x
    rw [hρc]
    exact ad_cj B k v s x
  obtain ⟨Z, hZ1, hZ2, hZ3, hZ4⟩ := cnt _ ρc (cjE ((boxK B k).g v)) he hker A hA _ hT
  refine ⟨Z, ?_, hZ2, hZ3, ?_⟩
  · rw [hZ1]
    rfl
  · have hN : Nat.card (Matrix (Fin 3) (Fin 3) (Ok l O k)) = Nat.card (Ok l O k) ^ 9 := by
      show Nat.card (Fin 3 → Fin 3 → Ok l O k) = _
      rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, ← pow_mul]
    have hAc : Nat.card A = (ZF (l := l) (F.Iv v) k (triOf B v)).ncard :=
      Nat.card_coe_set_eq (ZF (l := l) (F.Iv v) k (triOf B v))
    have hTc := card_upT (Ok l O k)
    calc (ZF (l := l) (F.Iv v) k (triOf B v)).ncard * Nat.card (Ok l O k) ^ 9
        = Nat.card A * Nat.card (Matrix (Fin 3) (Fin 3) (Ok l O k)) := by rw [hAc, hN]
      _ ≤ Nat.card Z * Nat.card {Y : Matrix (Fin 3) (Fin 3) (Ok l O k) | UpT Y} := hZ4
      _ ≤ Nat.card Z * Nat.card (Ok l O k) ^ 6 := Nat.mul_le_mul_left _ hTc
