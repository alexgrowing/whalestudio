import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrOfbox
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ResDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrSqz
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfKernel

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem lc_of_ker {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    (f : G →* H) (h : IsOpen (f.ker : Set G)) : IsLocallyConstant f :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker f h

private theorem res_dual (O : Type) [CommRing O] [IsLocalRing O] [IsCO O (DualNumber (ResidueField O))]
    (x : DualNumber (ResidueField O)) : res O (DualNumber (ResidueField O)) x = x.fst := by
  obtain ⟨a, ha⟩ := residue_surjective x.fst
  have h1 : x - algebraMap O _ a ∈ maximalIdeal (DualNumber (ResidueField O)) := by
    rw [mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero, not_not,
      TrivSqZeroExt.fst_sub, ← ha]
    exact sub_self _
  have h2 := (res_eq_zero_iff O _ _).2 h1
  rw [map_sub, AlgHom.commutes, sub_eq_zero] at h2
  rw [h2, ← ha]
  rfl

private theorem of_unique {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} {C : Type}
    [CommRing C] {B : Box F n C} {ρ ρ' : NRep F n C} (h : B.Of ρ) (h' : B.Of ρ') : ρ = ρ' := by
  have e : ρ.r = ρ'.r := MonoidHom.ext fun s => (h.res s).symm.trans (h'.res s)
  refine NRep.ext e (funext fun v => funext fun i => MonoidHom.ext fun s => Units.ext ?_)
  rw [← h.psi, ← h'.psi, e]

private theorem conj_mat {m : ℕ} {C : Type} [CommRing C] (h : GL (Fin m) C) (x : GG m C) (hx : x.right = 1) :
    (GG.ofGL h * x * (GG.ofGL h)⁻¹).left = h * x.left * h⁻¹ := by
  rw [← map_inv]
  simp [hx]

private theorem gg_map_ofGL {m : ℕ} {C C' : Type} [CommRing C] [CommRing C'] (f : C →+* C') (h : GL (Fin m) C) :
    GG.map f (GG.ofGL h) = GG.ofGL (GeneralLinearGroup.map f h) := rfl

private theorem dual_mul {K : Type} [Field K] (a : DualNumber K) (c : K) :
    (TrivSqZeroExt.inr (a.fst * c) : DualNumber K) = a * TrivSqZeroExt.inr c := by
  ext <;> simp [mul_comm]

private theorem dual_fst {K : Type} [Field K] {m : ℕ} (X : Matrix (Fin m) (Fin m) K) (i j : Fin m) :
    ((1 + X.map (TrivSqZeroExt.inr : K → DualNumber K)) i j).fst = (1 : Matrix (Fin m) (Fin m) K) i j := by
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

private theorem dual_snd {K : Type} [Field K] {m : ℕ} (X A : Matrix (Fin m) (Fin m) K) :
    ((1 + X.map (TrivSqZeroExt.inr : K → DualNumber K)) * A.map (TrivSqZeroExt.inl : K → DualNumber K)).map
      TrivSqZeroExt.snd = X * A := by
  ext i j
  rw [Matrix.add_mul, Matrix.one_mul]
  simp [Matrix.mul_apply, TrivSqZeroExt.snd_sum]

theorem UpperTheory.V.Fr.pr_tor :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : NRep F n R) (B : Box F n R), ρ.Univ O → B.Of ρ → B.Cont (maximalIdeal R) → (ρ.bar O).Good → thetaLie (lieT (ResidueField O) n) = lieT (ResidueField O) n → ∃ D ∈ Tan O R, ∀ s, B.tanCo O D s = (B.bar O).ad s (lieT _ n) - lieT _ n := by
  intro l _ k _ _ F C₀ n hF O _ _ R _ _ _ ρ B hU hB hC _ hT
  haveI := (co_res O).2
  let K := ResidueField O
  let C := DualNumber K
  let μ : K →+ C := (TrivSqZeroExt.inrHom K K).toAddMonoidHom
  let ι : K →+* C := (TrivSqZeroExt.inlHom K K)
  have hμ : IsSq O μ := by
    refine ⟨fun a c => ?_, fun c => ?_⟩
    · rw [res_dual]
      exact dual_mul a c
    · rw [← res_eq_zero_iff O, res_dual]
      rfl
  have hres : (res O C : C →+* K).comp ι = RingHom.id K := RingHom.ext fun a => res_dual O _
  obtain ⟨e, e1, e2, e3, -, e5⟩ := pr_sqz O C n μ hμ
  set T := lieT K n with hTdef
  let B₀ : Box F n C := (B.bar O).map ι
  have hB₀ : B₀.bar O = B.bar O := by
    show ((B.bar O).map ι).map _ = _
    rw [Box.map_map, hres]
    rfl
  have hr₀ : ∀ s, GG.map (res O C : C →+* K) (B₀.r s) = (B.bar O).r s := fun s => by
    rw [← hB₀]; rfl
  let h := e (-T)
  have hinv : h⁻¹ = e T := by rw [e3, neg_neg]
  have hloc : ∀ s : F.G0, (B₀.r s).right = 1 := fun s => (B₀.nu s).trans s.2
  let B' : Box F n C :=
    { r := conjBy h B₀.r
      nu := fun s => by
        show (GG.ofGL h * B₀.r s * (GG.ofGL h)⁻¹).right = _
        rw [← map_inv]
        simp [B₀.nu]
      g := fun v => B₀.g v * h⁻¹
      tri := fun v s => by
        have : (conjBy h B₀.r (F.loc v s)).left = h * (B₀.r (F.loc v s)).left * h⁻¹ :=
          conj_mat h _ (hloc (F.loc0 v s))
        have h2 := B₀.tri v s
        unfold GG.mat at h2 ⊢
        rw [this, ← Units.val_mul, ← Units.val_mul]
        rw [← Units.val_mul, ← Units.val_mul] at h2
        convert h2 using 2
        group }
  have hform : ∀ s, B'.r s = GG.ofGL (e ((B.bar O).ad s T - T)) * B₀.r s := fun s => by
    show GG.ofGL h * B₀.r s * (GG.ofGL h)⁻¹ = _
    rw [← map_inv, hinv, mul_assoc, e5, hr₀, ← mul_assoc, ← map_mul, ← e2, neg_add_eq_sub]
    rfl
  have hmat : ∀ s, (B'.r s).mat = (1 + ((B.bar O).ad s T - T).map μ) * ((B.bar O).r s).mat.map ι := fun s => by
    rw [hform, ← e1]
    simp [GG.mat]
    rfl
  have hbar : B.bar O |>.Of (ρ.bar O) := hB.map _
  have hc : (B'.r F.c).mat = 1 := by
    have h1 : (B.bar O).ad F.c T = T := by
      have hl : ((B.bar O).r F.c).left = 1 := Units.ext hbar.atc
      have hd : ((B.bar O).r F.c).right ≠ 1 := by
        rw [(B.bar O).nu, hF.del_c]; decide
      show ((B.bar O).r F.c).adFun T = T
      unfold GG.adFun GG.mat
      rw [hl, if_neg hd, hT]
      simp
    rw [hmat, h1, hbar.atc, sub_self, Matrix.map_one _ (map_zero ι) (map_one ι), Matrix.map_zero _ (map_zero μ)]
    simp
  have hdiagE : ∀ a : K, ((e (a • T) : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) =
      Matrix.diagonal fun i => 1 + μ (a * (w n i : K)) := fun a => by
    rw [e1]
    ext1 i j
    by_cases hij : i = j
    · subst hij; simp [hTdef, lieT]
    · simp [hTdef, lieT, hij]
  have hd : ∀ i j, i ≠ j → ((B'.r F.g0).mat - (B'.r (F.star F.g0)).mat) i j = 0 := fun i j hij => by
    have h1 : ∀ s : F.G0, (B'.r s).mat = (h : Matrix (Fin n) (Fin n) C) * ((ρ.bar O).r s).map ι *
        ((h⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) := fun s => by
      rw [← hbar.res]
      exact congrArg Units.val (conj_mat h _ (hloc s))
    have h2 := (ρ.bar O).diag i j hij
    rw [h1, h1, ← Matrix.sub_mul, ← Matrix.mul_sub, hinv, ← one_smul K T, hdiagE, Matrix.mul_diagonal]
    have h3 : h = e ((-1 : K) • T) := by rw [neg_one_smul]
    rw [h3, hdiagE, Matrix.diagonal_mul, Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply, ← map_sub,
      ← Matrix.sub_apply, h2]
    simp
  have hcont : B'.Cont (maximalIdeal C) := fun i j N => by
    have h1 := lc_of_ker _ (pr_open hF O R B hC).1
    exact h1.comp fun x => Ideal.Quotient.mk _ ((GG.ofGL h * GG.map ι x * (GG.ofGL h)⁻¹).mat i j)
  obtain ⟨ρ', hρ', hc'⟩ := pr_ofbox hF C _ B' hc hd hcont
  have hh : GeneralLinearGroup.map (res O C : C →+* K) h = 1 := by
    apply Units.ext
    ext i j
    show res O C ((e (-T) : Matrix (Fin n) (Fin n) C) i j) = _
    rw [e1, res_dual]
    exact dual_fst _ i j
  have hB' : B'.bar O = B.bar O := by
    rw [← hB₀]
    refine Box.ext (MonoidHom.ext fun s => ?_) (funext fun v => ?_)
    · show GG.map _ (GG.ofGL h * B₀.r s * (GG.ofGL h)⁻¹) = GG.map _ (B₀.r s)
      rw [map_mul, map_mul, map_inv, gg_map_ofGL, hh]
      simp
    · show GeneralLinearGroup.map _ (B₀.g v * h⁻¹) = GeneralLinearGroup.map _ (B₀.g v)
      rw [map_mul, map_inv, hh]
      simp
  have hρb : ρ'.bar O = ρ.bar O := of_unique (hB' ▸ hρ'.map _) hbar
  obtain ⟨D, hD, hD'⟩ := pr_dof hF O R ρ B hU hB ρ' B'.r hc' hρb B'.nu hc hρ'.res
  refine ⟨D, hD, fun s => ?_⟩
  have h1 : (B'.r s).mat.map TrivSqZeroExt.snd = ((B.bar O).ad s T - T) * ((B.bar O).r s).mat := by
    rw [hmat]
    exact dual_snd _ _
  have h2 := (hD' s).symm.trans h1
  exact (Units.mul_left_inj ((B.bar O).r s).left).1 h2
