import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RtDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.BkAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtFinFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem tanBK_avg {k G W : Type} [Field k] [CharZero k] [Group G] [AddCommGroup W] [Module k W]
    (a : G → W →ₗ[k] W) (hmul : ∀ g h w, a (g * h) w = a g (a h w)) (f : G → W)
    (hf : ∀ g h, f (g * h) = f g + a g (f h)) (H : Subgroup G) [H.FiniteIndex] (x : W)
    (hx : ∀ h ∈ H, f h = a h x - x) : ∃ y, ∀ g, f g = a g y - y := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  set f' : G → W := fun g => f g - (a g x - x) with hf'
  have hc : ∀ g h, f' (g * h) = f' g + a g (f' h) := by
    intro g h
    simp only [hf', hf, hmul, map_sub]
    abel
  have hH : ∀ g h, h ∈ H → f' (g * h) = f' g := by
    intro g h hh
    rw [hc]
    have : f' h = 0 := by simp only [hf', hx h hh, sub_self]
    rw [this, map_zero, add_zero]
  let F : G ⧸ H → W := Quotient.lift f' (by
    intro g g' hgg
    have h1 : g⁻¹ * g' ∈ H := QuotientGroup.leftRel_apply.1 hgg
    have := hH g _ h1
    rw [mul_inv_cancel_left] at this
    exact this.symm)
  have hF : ∀ (g : G) (q : G ⧸ H), F (g • q) = f' g + a g (F q) := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H z => exact hc g z
  set S : W := ∑ q, F q with hS
  have hsum : ∀ g, S = (Fintype.card (G ⧸ H) : k) • f' g + a g S := by
    intro g
    have e1 : ∑ q, F (g • q) = S := Equiv.sum_comp (MulAction.toPerm g) F
    refine e1.symm.trans ?_
    simp only [hF, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← map_sum,
      Nat.cast_smul_eq_nsmul, ← hS]
  have hn : (Fintype.card (G ⧸ H) : k) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨x - (Fintype.card (G ⧸ H) : k)⁻¹ • S, fun g => ?_⟩
  have e : f' g = (Fintype.card (G ⧸ H) : k)⁻¹ • (S - a g S) := by
    rw [eq_inv_smul_iff₀ hn, eq_sub_iff_add_eq]
    exact (hsum g).symm
  have e2 : f g = f' g + (a g x - x) := by simp only [hf', sub_add_cancel]
  rw [e2, e, map_sub, map_smul, smul_sub]
  abel

section Coc

variable {O Γ R κ : Type} [CommRing O] [Group Γ] [CommRing R] [Algebra O R] [CommRing κ] [Algebra O κ]

private def sndM (F : R →ₐ[O] DualNumber κ) (X : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) κ :=
  X.map fun x => (F x).snd

private def fstM (F : R →ₐ[O] DualNumber κ) : Matrix (Fin 3) (Fin 3) R →+* Matrix (Fin 3) (Fin 3) κ :=
  (dualFst F : R →+* κ).mapMatrix

private theorem sndM_mul (F : R →ₐ[O] DualNumber κ) (X Y : Matrix (Fin 3) (Fin 3) R) :
    sndM F (X * Y) = fstM F X * sndM F Y + sndM F X * fstM F Y := by
  ext a b
  simp [sndM, fstM, dualFst, Matrix.mul_apply, Fin.sum_univ_three, DualNumber.snd_mul]
  ring

private theorem sndM_one (F : R →ₐ[O] DualNumber κ) : sndM F 1 = 0 := by
  ext a b
  by_cases h : a = b <;> simp [sndM, Matrix.one_apply, h]

private theorem sndM_J (F : R →ₐ[O] DualNumber κ) : sndM F (Jmat R 3) = 0 := by
  ext a b
  by_cases h : b = a.rev <;> simp [sndM, Jmat, h]

private theorem fstM_J (F : R →ₐ[O] DualNumber κ) : fstM F (Jmat R 3) = Jmat κ 3 := Jmat_map _ 3

private theorem sndM_tr (F : R →ₐ[O] DualNumber κ) (X : Matrix (Fin 3) (Fin 3) R) : sndM F Xᵀ = (sndM F X)ᵀ := rfl

private theorem fstM_tr (F : R →ₐ[O] DualNumber κ) (X : Matrix (Fin 3) (Fin 3) R) : fstM F Xᵀ = (fstM F X)ᵀ := rfl

private theorem sndM_inv (F : R →ₐ[O] DualNumber κ) (a : GL (Fin 3) R) :
    sndM F ((a⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      -(fstM F ((a⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * sndM F (a : Matrix (Fin 3) (Fin 3) R) *
        fstM F ((a⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) := by
  have h := sndM_mul F ((a⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a
  rw [Units.inv_mul, sndM_one] at h
  have h2 := congrArg (· * fstM F ((a⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) h
  simp only [Matrix.zero_mul, Matrix.add_mul] at h2
  rw [Matrix.mul_assoc (sndM F _), ← map_mul, Units.mul_inv, map_one, Matrix.mul_one] at h2
  exact eq_neg_of_add_eq_zero_right h2.symm

private theorem tan_coc (F : R →ₐ[O] DualNumber κ) (r : Γ →* GG 3 R) (g h : Γ) :
    tanCoc F r (g * h) = tanCoc F r g + adRep (push (dualFst F) r) g (tanCoc F r h) := by
  have e1 : ∀ g, tanCoc F r g = sndM F ((r g).left : Matrix (Fin 3) (Fin 3) R) *
      fstM F (((r g).left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := fun g => rfl
  have e2 : ∀ X, adRep (push (dualFst F) r) g X = fstM F ((r g).left : Matrix (Fin 3) (Fin 3) R) *
      (if (r g).right = 1 then X else thetaLie X) *
      fstM F (((r g).left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := fun X => rfl
  have hn : ((-1 : ℤˣ) = 1) = False := by decide
  have hJ : ∀ Y : Matrix (Fin 3) (Fin 3) κ, Jmat κ 3 * (Jmat κ 3 * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.one_mul]
  have hc : ∀ (b : GL (Fin 3) R) (Y : Matrix (Fin 3) (Fin 3) κ), fstM F (b : Matrix (Fin 3) (Fin 3) R) *
      (fstM F ((b⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * Y) = Y := fun b Y => by
    rw [← Matrix.mul_assoc, ← map_mul, Units.mul_inv, map_one, Matrix.one_mul]
  have hc' : ∀ (b : GL (Fin 3) R) (Y : Matrix (Fin 3) (Fin 3) κ),
      (fstM F ((b⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R))ᵀ *
      ((fstM F (b : Matrix (Fin 3) (Fin 3) R))ᵀ * Y) = Y := fun b Y => by
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, ← map_mul, Units.mul_inv, map_one, Matrix.transpose_one,
      Matrix.one_mul]
  rw [e2, e1, e1, e1, map_mul, SemidirectProduct.mul_left]
  generalize (r g).left = a
  generalize (r h).left = b
  rcases Int.units_eq_one_or (r g).right with hs | hs <;> rw [hs]
  · simp only [sgnAct_one, if_true, _root_.mul_inv_rev, Units.val_mul, sndM_mul, map_mul, Matrix.add_mul,
      Matrix.mul_assoc, hc]
    rw [add_comm]
  · simp only [sgnAct_neg_one, hn, if_false, _root_.mul_inv_rev, Units.val_mul, theta_val, theta_inv_val, sndM_mul,
      map_mul, sndM_J, fstM_J, sndM_tr, fstM_tr, sndM_inv, thetaLie, Matrix.add_mul, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.transpose_neg, Matrix.transpose_mul, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.mul_assoc, hJ, hc']
    rw [add_comm]

end Coc

private theorem tan_cont {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)]
    (R : Type) [CommRing R] [Algebra O R] [IsCO O R]
    (F : R →ₐ[O] DualNumber (PadicAlgCl l)) (hF : IsLocPt (dualFst F)) {X : Type} [TopologicalSpace X] (f : X → R)
    (hf : AdicCont (maximalIdeal R) f) :
    Continuous (fun x => (F (f x)).fst) ∧ Continuous fun x => (F (f x)).snd := by
  haveI : IsAdicComplete (maximalIdeal O) O := (abelian₂.dvr_finite l O).1
  obtain ⟨E, hE⟩ := Loc.ptFin (l := l) R F hF
  haveI : FiniteDimensional ℚ_[l] E.1 := E.2
  let B : Subalgebra ℚ_[l] (DualNumber (PadicAlgCl l)) :=
    { carrier := {x | x.fst ∈ E.1 ∧ x.snd ∈ E.1}
      mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
        rw [DualNumber.snd_mul]; exact add_mem (mul_mem hx.1 hy.2) (mul_mem hx.2 hy.1)⟩
      add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
      algebraMap_mem' := fun a => ⟨E.1.algebraMap_mem a, zero_mem _⟩ }
  let p₁ : B →ₗ[ℚ_[l]] PadicAlgCl l := (TrivSqZeroExt.fstHom ℚ_[l] _ _).toLinearMap.comp B.val.toLinearMap
  let p₂ : B →ₗ[ℚ_[l]] PadicAlgCl l :=
    ((TrivSqZeroExt.sndHom (PadicAlgCl l) (PadicAlgCl l)).restrictScalars ℚ_[l]).comp B.val.toLinearMap
  haveI : Module.Finite ℚ_[l] B := Module.Finite.of_injective
    ((p₁.codRestrict E.1.toSubmodule fun x => x.2.1).prod (p₂.codRestrict E.1.toSubmodule fun x => x.2.2))
    (fun x y h => Subtype.ext (TrivSqZeroExt.ext (congrArg (fun z => (z.1 : PadicAlgCl l)) h)
      (congrArg (fun z => (z.2 : PadicAlgCl l)) h)))
  let x₀ : R →+* B := (F : R →+* DualNumber (PadicAlgCl l)).codRestrict B hE
  letI : Algebra O B := (x₀.comp (algebraMap O R)).toAlgebra
  haveI : IsScalarTower ℤ_[l] O B := IsScalarTower.of_algebraMap_eq fun a => Subtype.ext (by
    show algebraMap ℤ_[l] (DualNumber (PadicAlgCl l)) a = F (algebraMap O R _)
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply])
  let x : R →ₐ[O] B := { x₀ with commutes' := fun _ => rfl }
  have h := (Loc.ptCont (l := l) R B x).1 X f hf
  letI : TopologicalSpace B := moduleTopology ℚ_[l] B
  haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  exact ⟨(IsModuleTopology.continuous_of_linearMap p₁).comp h, (IsModuleTopology.continuous_of_linearMap p₂).comp h⟩

theorem UpperTheory.V.U3.tanCoc_isBK :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ (S : D.Ring U g₁),
      ∀ F : S.R →ₐ[c.O] DualNumber (PadicAlgCl l), IsLocPt (dualFst F) →
        tanCoc F S.r.hom ∈ Z1 (adRep (push (dualFst F) S.r.hom)) ∧ Af.IsBK l (adRep (push (dualFst F) S.r.hom)) (tanCoc F S.r.hom) := by
  intro hI Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ _ S F hF
  haveI : IsLocalRing c.O := c.dvr.toIsLocalRing
  haveI := (abelian₂.dvr_finite l c.O).1
  obtain ⟨-, hkill, f, hf, hfI⟩ := (S.rep S.R).1 (AlgHom.id _ _)
  have hZ : tanCoc F S.r.hom ∈ Z1 (adRep (push (dualFst F) S.r.hom)) := by
    refine ⟨?_, tan_coc F _⟩
    have h1 : Continuous fun g => fstM F (S.r.hom g).mat :=
      continuous_matrix fun a b => (tan_cont S.R F hF _ (S.r.cont a b)).1
    have h2 : Continuous fun g => sndM F (S.r.hom g).mat :=
      continuous_matrix fun a b => (tan_cont S.R F hF _ (S.r.cont a b)).2
    have h0 : ∀ g, fstM F (S.r.hom g).mat *
        fstM F (((S.r.hom g).left⁻¹ : GL (Fin 3) S.R) : Matrix (Fin 3) (Fin 3) S.R) = 1 := fun g => by
      rw [← map_mul, GG.mat, Units.mul_inv, map_one]
    have h3 : tanCoc F S.r.hom = fun g => sndM F (S.r.hom g).mat *
        ((fstM F (S.r.hom g).mat).det⁻¹ • (fstM F (S.r.hom g).mat).adjugate) := funext fun g => by
      rw [← Ring.inverse_eq_inv, ← Matrix.inv_def, Matrix.inv_eq_right_inv (h0 g)]
      rfl
    rw [h3]
    exact h2.matrix_mul ((h1.matrix_det.inv₀ fun g => (Matrix.isUnit_det_of_right_inverse (h0 g)).ne_zero).smul
      h1.matrix_adjugate)
  refine ⟨hZ, fun w hw => ?_, fun τ => ⟨D.j, Subsingleton.elim _ _, ?_⟩⟩
  · refine ⟨placeOf Ω w, isPlaceOver_placeOf Ω w, ?_⟩
    have hA : ¬ (placeOf Ω w).valuation (l : Ω) < 1 := fun h =>
      hw (((places ℚ Ω l _).2.2.1 w (isPlaceOver_placeOf Ω w)).1 h)
    haveI : Finite (ResidueField c.O) := (abelian₂.dvr_finite l c.O).2.1
    haveI : Finite (GG 3 (ResidueField c.O)) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
    obtain ⟨y, hy⟩ := tanBK_avg (k := PadicAlgCl l) (G := Ine (F := ℚ) (placeOf Ω w))
      (fun g => adRep (push (dualFst F) S.r.hom) g) (fun g h x => by simp)
      (fun g => tanCoc F S.r.hom g) (fun g h => hZ.2 g h)
      ((rbar c.O D.η D.Ψ).comp (Ine (F := ℚ) (placeOf Ω w)).subtype).ker 0 (fun g hg => by
        have h1 : S.r.hom g = 1 := hkill g ⟨_, hA, g.2, hg⟩
        have h2 : tanCoc F S.r.hom g = sndM F (S.r.hom g).mat *
          fstM F (((S.r.hom g).left⁻¹ : GL (Fin 3) S.R) : Matrix (Fin 3) (Fin 3) S.R) := rfl
        rw [h2, h1]
        have h3 : sndM F (1 : GG 3 S.R).mat = 0 := sndM_one F
        simp [h3])
    exact ⟨y, fun s hs => hy ⟨s, hs⟩⟩
  · have hfg : ∀ h, GG.map (f : U.R →+* S.R) (U.r.hom h) = S.r.hom (D.ι h) := fun h =>
      DFunLike.congr_fun (congrArg GLift.hom hf) h
    have h1 := Loc.rtDual hI.loc D.loc U (F.comp f)
      (fun a ha => by
        have : f a = 0 := hfI ha
        show F (f a) = 0
        rw [this, map_zero])
      (fun a ha => hF (f a) (by rwa [← res_eq_zero_iff c.O, res_map, res_eq_zero_iff]))
    have e1 : tanCoc (F.comp f) U.r.hom = fun h => tanCoc F S.r.hom (D.ι h) := funext fun h => by
      unfold tanCoc
      rw [← hfg]
      rfl
    have e2 : adRep (push (dualFst (F.comp f)) U.r.hom) = (adRep (push (dualFst F) S.r.hom)).comp D.ι := by
      refine MonoidHom.ext fun h => ?_
      show _ = GG.ad 3 _ (GG.map _ (S.r.hom (D.ι h)))
      rw [← hfg]
      rfl
    rw [e1, e2] at h1
    exact (Loc.bkAbove (F := ℚ) D.j (MonoidHom.id _) D.ι Topology.IsOpenEmbedding.id D.ι_spec _ _ hZ).1 h1
