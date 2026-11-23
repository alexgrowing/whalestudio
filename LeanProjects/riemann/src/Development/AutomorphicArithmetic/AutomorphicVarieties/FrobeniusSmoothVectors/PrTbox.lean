import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrCorrect

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_tbox :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ [IsCO O (ResidueField O)] [IsCO O (DualNumber (ResidueField O))] (B : Box F n (ResidueField O)), (IsLocallyConstant fun s => (B.r s).mat) → ∀ x ∈ Z1C F.loc B.ad B.b, ∃ B' : Box F n (DualNumber (ResidueField O)), B'.Cont (maximalIdeal _) ∧ B'.map (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O) : (DualNumber (ResidueField O)) →+* ResidueField O) = B ∧ ∀ s, (B'.r s).mat.map TrivSqZeroExt.snd = x.1 s * (B.r s).mat := by
  intro l _ k _ _ F C₀ n hF O _ _ _ _ B hB x hx
  have hres : ∀ y : ResidueField O, res O (ResidueField O) y = y := by
    intro y
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    have h := (res O (ResidueField O)).commutes a
    rw [IsLocalRing.ResidueField.algebraMap_eq] at h
    exact h
  have hbar : Box.bar O B = B := by
    apply Box.ext
    · ext s
      · simp [Box.bar, Box.map, GG.map, hres]
      · simp [Box.bar, Box.map, GG.map]
    · funext v
      ext i j
      simp [Box.bar, Box.map, hres]
  let ι : ResidueField O →+* DualNumber (ResidueField O) := algebraMap _ _
  let p := TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)
  have hp : ∀ X : GL (Fin n) (ResidueField O), GeneralLinearGroup.map (p : DualNumber (ResidueField O) →+* ResidueField O) (GeneralLinearGroup.map ι X) = X := by
    intro X
    ext i j
    simp [p, ι, TrivSqZeroExt.algebraMap_eq_inl]
  have hloc : ∀ v, Continuous (F.loc v) := by
    intro v
    exact continuous_subtype_val.comp (hF.loc_cont v)
  have hlc : ∀ (f : Matrix (Fin n) (Fin n) (ResidueField O) → DualNumber (ResidueField O)) (N : ℕ),
      IsLocallyConstant fun s => Ideal.Quotient.mk (maximalIdeal (DualNumber (ResidueField O)) ^ N) (f (B.r s).mat) :=
    fun f N => hB.comp (fun M => Ideal.Quotient.mk _ (f M))
  let D : SetLift p B :=
    { r := fun s => GeneralLinearGroup.map ι (B.r s).left
      r_cont := fun i j N => hlc (fun M => ι (M i j)) N
      r_map := fun s => hp _
      g := fun v => GeneralLinearGroup.map ι (B.g v)
      g_map := fun v => hp _
      t := fun v s => GeneralLinearGroup.map ι (B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹)
      t_cont := by
        intro v i j N
        have h := (hlc (fun M => ι (((B.g v).val * M * (B.g v)⁻¹.val) i j)) N).comp_continuous (hloc v)
        exact h
      t_tri := by
        intro v s i j hij
        have h := congrArg ι (B.tri v s i j hij)
        rw [map_zero] at h
        exact h
      t_map := fun v s => hp _ }
  let μ : ResidueField O →+ DualNumber (ResidueField O) :=
    (TrivSqZeroExt.inrHom (ResidueField O) (ResidueField O)).toAddMonoidHom
  have hresD : ∀ a : DualNumber (ResidueField O), res O (DualNumber (ResidueField O)) a = a.fst := by
    intro a
    rw [← res_map p a, hres]
    rfl
  have hμ : IsSq O μ := by
    constructor
    · intro a c
      rw [hresD]
      ext
      · simp [μ]
      · show (TrivSqZeroExt.inr (a.fst * c) : DualNumber (ResidueField O)).snd = (a * TrivSqZeroExt.inr c).snd
        rw [TrivSqZeroExt.snd_mul]
        simp only [TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, MulOpposite.op_zero, zero_smul, add_zero, smul_eq_mul]
    · intro c
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have := hu.map p
      simp [p, μ] at this
  have hR : ∀ s t : F.Γ, GeneralLinearGroup.map ι (B.r (s * t)).left =
      GeneralLinearGroup.map ι (B.r s).left * sgnAct n _ (F.del s) (GeneralLinearGroup.map ι (B.r t).left) := by
    intro s t
    have h1 := congrArg SemidirectProduct.left (map_mul ((GG.map ι).comp B.r) s t)
    have h2 : (((GG.map ι).comp B.r) s).right = F.del s := B.nu s
    rw [SemidirectProduct.mul_left, h2] at h1
    exact h1
  refine (pr_correct hF O _ _ p B D μ hμ (fun c => by simp [p, μ]) (fun s => -x.1 s) (fun v => -x.2 v)
    (fun _ _ => 0) ?g1 ?g2 ?g3 ?g4).imp fun B' h => ⟨h.1, h.2.1, fun s => ?g5⟩
  case g5 =>
    rw [h.2.2 s]
    ext i j
    show (((1 - (-x.1 s).map μ) * ((B.r s).left.val.map ι) : Matrix (Fin n) (Fin n) (DualNumber (ResidueField O))) i j).snd = _
    rw [Matrix.mul_apply, TrivSqZeroExt.snd_sum, GG.mat, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [TrivSqZeroExt.snd_mul]
    simp [Matrix.one_apply, μ, ι, TrivSqZeroExt.algebraMap_eq_inl, op_smul_eq_mul]
    left
    split_ifs <;> simp
  case g1 => exact hx.1.comp (fun M => -M)
  case g2 =>
    intro y
    rw [hbar]
    have hc := hx.2.1 y.1 y.2
    have h0 : dOne B.ad (fun s => -x.1 s) y = 0 := by
      simp only [dOne, map_neg, hc]
      abel
    rw [h0, Matrix.map_zero _ (map_zero μ)]
    show (GeneralLinearGroup.map ι (B.r y.1).left * sgnAct n _ (F.del y.1) (GeneralLinearGroup.map ι (B.r y.2).left) *
      (GeneralLinearGroup.map ι (B.r (y.1 * y.2)).left)⁻¹).val - 1 = 0
    rw [hR, mul_inv_cancel, Units.val_one, sub_self]
  case g3 =>
    intro v s
    rw [Matrix.map_zero _ (map_zero μ)]
    show (GeneralLinearGroup.map ι (B.r (F.loc v s)).left * ((GeneralLinearGroup.map ι (B.g v))⁻¹ *
      GeneralLinearGroup.map ι (B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹) * GeneralLinearGroup.map ι (B.g v))⁻¹).val - 1 = 0
    simp [map_mul, map_inv, mul_assoc]
  case g4 =>
    intro v s
    rw [hbar]
    have h := hx.2.2 v s
    convert h using 1
    simp only [map_neg]
    abel
