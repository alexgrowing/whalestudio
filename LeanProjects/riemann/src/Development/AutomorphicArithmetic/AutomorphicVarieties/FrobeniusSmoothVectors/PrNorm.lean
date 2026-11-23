import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrNorm1
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.JconjApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrOfbox

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

namespace UpperTheory.V.Fr

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} {C C' : Type} [CommRing C] [CommRing C']

private theorem conj_left {G : Type} [Group G] (h : GL (Fin n) C) (r : G →* GG n C) (s : G) :
    (conjBy h r s).left = h * (r s).left * sgnAct n C (r s).right h⁻¹ := by
  simp [conjBy, GG.ofGL, MulAut.conj_apply, SemidirectProduct.mul_left, SemidirectProduct.mul_right, mul_assoc]

private theorem conj_right {G : Type} [Group G] (h : GL (Fin n) C) (r : G →* GG n C) (s : G) :
    (conjBy h r s).right = (r s).right := by
  simp [conjBy, GG.ofGL, MulAut.conj_apply, SemidirectProduct.mul_right]

private theorem conj_mat {G : Type} [Group G] (h : GL (Fin n) C) (r : G →* GG n C) (s : G) (hs : (r s).right = 1) :
    (conjBy h r s).mat = (h : Matrix (Fin n) (Fin n) C) * (r s).mat *
      ((h⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) := by
  unfold GG.mat
  rw [conj_left, hs, sgnAct_one, Units.val_mul, Units.val_mul]

private theorem conj_mul {G : Type} [Group G] (h h' : GL (Fin n) C) (r : G →* GG n C) :
    conjBy (h * h') r = conjBy h (conjBy h' r) := by
  apply MonoidHom.ext
  intro s
  simp [conjBy, MulAut.conj_apply, _root_.mul_inv_rev, mul_assoc]

private theorem frame_right_eq_one_of_G0 (B : Box F n C) (s : F.G0) : (B.r s).right = 1 := by
  exact (B.nu s).trans (MonoidHom.mem_ker.mp s.2)

private noncomputable def cj (h : GL (Fin n) C) (B : Box F n C) : Box F n C where
  r := conjBy h B.r
  nu s := (conj_right h B.r s).trans (B.nu s)
  g v := B.g v * h⁻¹
  tri v s := by
    have e : B.g v * h⁻¹ * (conjBy h B.r (F.loc v s)).left * (B.g v * h⁻¹)⁻¹ =
        B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹ := by
      have : (B.r (F.loc v s)).right = 1 := frame_right_eq_one_of_G0 B (F.loc0 v s)
      rw [conj_left, this, sgnAct_one]
      group
    have e' := congrArg Units.val e
    simp only [Units.val_mul] at e'
    have := B.tri v s
    unfold GG.mat at this ⊢
    rw [← e'] at this
    simpa only [Units.val_mul] using this

private theorem cj_map (f : C →+* C') (h : GL (Fin n) C) (B : Box F n C)
    (hh : (h : Matrix (Fin n) (Fin n) C).map f = 1) : (cj h B).map f = B.map f := by
  have hh' : Matrix.GeneralLinearGroup.map f h = 1 := Units.ext (by simpa using hh)
  have hg : GG.map f (GG.ofGL h) = 1 := by
    simp [GG.map, GG.ofGL, hh']
  apply Box.ext
  · apply MonoidHom.ext
    intro s
    show GG.map f (conjBy h B.r s) = GG.map f (B.r s)
    simp [conjBy, MulAut.conj_apply, map_mul, map_inv, hg]
  · funext v
    show Matrix.GeneralLinearGroup.map f (B.g v * h⁻¹) = Matrix.GeneralLinearGroup.map f (B.g v)
    simp [map_mul, map_inv, hh']

private theorem cj_cont (hd : IsOpen (F.del.ker : Set F.Γ)) (I : Ideal C) (h : GL (Fin n) C) (B : Box F n C)
    (hB : B.Cont I) : (cj h B).Cont I := by
  intro i j N
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hdel : ∀ᶠ y in nhds x, F.del y = F.del x := by
    have hopen : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (F.del.ker : Set F.Γ)) :=
      hd.preimage (continuous_const.mul continuous_id)
    filter_upwards [hopen.mem_nhds (by simp)] with y hy
    have e : F.del (x⁻¹ * y) = 1 := hy
    rw [map_mul, map_inv, inv_mul_eq_one] at e
    exact e.symm
  have hM : ∀ᶠ y in nhds x, ∀ a b : Fin n,
      Ideal.Quotient.mk (I ^ N) ((B.r y).mat a b) = Ideal.Quotient.mk (I ^ N) ((B.r x).mat a b) := by
    rw [Filter.eventually_all]
    intro a
    rw [Filter.eventually_all]
    intro b
    exact (hB a b N).eventually_eq x
  filter_upwards [hdel, hM] with y hy hMy
  show Ideal.Quotient.mk (I ^ N) ((conjBy h B.r y).mat i j) = Ideal.Quotient.mk (I ^ N) ((conjBy h B.r x).mat i j)
  simp only [GG.mat] at hMy ⊢
  simp only [conj_left, B.nu, hy, Units.val_mul, Matrix.mul_apply, map_sum, map_mul, hMy]

private theorem of_unique {B : Box F n C} {ρ ρ' : NRep F n C} (h : B.Of ρ) (h' : B.Of ρ') : ρ = ρ' := by
  have e : ρ.r = ρ'.r := MonoidHom.ext fun s => (h.res s).symm.trans (h'.res s)
  apply NRep.ext e
  funext v i
  refine MonoidHom.ext fun s => Units.ext ?_
  rw [← h.psi, ← h'.psi, e]

private theorem star_mat (hc : F.del F.c = -1) (B : Box F n C) (h1 : (B.r F.c).mat = 1) (g : F.G0) :
    (B.r (F.star g)).mat = Jmat C n * (B.r g).matᵀ * Jmat C n := by
  have t1 : theta (1 : GL (Fin n) C) = 1 := by
    simpa [sgnAct_neg_one] using map_one (sgnAct n C (-1))
  have hX : B.r F.c = ⟨1, -1⟩ := SemidirectProduct.ext (Units.ext (by simpa [GG.mat] using h1)) ((B.nu _).trans hc)
  have hY : B.r (g : F.Γ) = ⟨(B.r g).left, 1⟩ := SemidirectProduct.ext rfl (frame_right_eq_one_of_G0 B g)
  rw [show ((F.star g : F.G0) : F.Γ) = F.c * (g : F.Γ)⁻¹ * F.c⁻¹ from rfl, map_mul, map_mul, map_inv, map_inv, hX, hY]
  simp [GG.mat, SemidirectProduct.mul_left, SemidirectProduct.inv_left, map_inv, sgnAct_neg_one, sgnAct_one, theta_inv_val]
  rw [t1, t1, Units.val_one, mul_one, ← Matrix.coe_units_inv, theta_inv_val]

end SlopeTestRemainingChoices

end UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_norm :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (ρ : NRep F n C) (B' : Box F n C'), maximalIdeal C' * RingHom.ker p = ⊥ → (ρ.bar O).Good → (B'.map (p : C' →+* C)).Of ρ → B'.Cont (maximalIdeal C') → ∃ (h : GL (Fin n) C') (ρ' : NRep F n C'), (h : Matrix (Fin n) (Fin n) C').map p = 1 ∧ ρ'.map (p : C' →+* C) = ρ ∧ ρ'.Cont (maximalIdeal C') ∧ (conjBy h B'.r F.c).mat = 1 ∧ ∀ s : F.G0, (conjBy h B'.r s).mat = ρ'.r s := by
  intro l _ k _ _ F C₀ n hF O _ _ C' _ _ _ C _ _ _ p ρ B' hmk hgood hof hcont
  have hkp : RingHom.ker p ≤ maximalIdeal C' := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [← res_eq_zero_iff O C', ← res_map p x, hx, map_zero]
  have hmat : ∀ (B : Box F n C') (s : F.Γ), ((B.map (p : C' →+* C)).r s).mat = (B.r s).mat.map p := fun B s => rfl
  have hx1 : (B'.r F.c).mat.map p = 1 := by
    rw [← hmat]
    exact hof.atc
  obtain ⟨h1, hh1, hc1⟩ := pr_norm1 O C' C p n (B'.r F.c) hmk hkp hgood.two
    (by rw [← map_mul, hF.c_sq, map_one]) ((B'.nu _).trans hF.del_c) hx1
  set B1 := cj h1 B' with hB1
  have hB1c : (B1.r F.c).mat = 1 := hc1
  have hB1map : B1.map (p : C' →+* C) = B'.map (p : C' →+* C) := cj_map _ h1 B' hh1
  have hB1cont : B1.Cont (maximalIdeal C') := cj_cont hF.del_open _ h1 B' hcont
  have hstar : ∀ g : F.G0, (B1.r (F.star g)).mat = Jmat C' n * (B1.r g).matᵀ * Jmat C' n :=
    star_mat hF.del_c B1 hB1c
  set Z := (B1.r F.g0).mat - (B1.r (F.star F.g0)).mat with hZ
  have hJ : ∀ X : Matrix (Fin n) (Fin n) C', Jmat C' n * (Jmat C' n * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.one_mul]
  have hθ : thetaLie Z = Z := by
    rw [hZ, hstar]
    simp only [thetaLie, Matrix.transpose_sub, Matrix.transpose_mul, Jmat_transpose, Matrix.transpose_transpose,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hJ, Jmat_mul_Jmat, Matrix.mul_one]
    abel
  have hZp : Z.map p = ρ.r F.g0 - ρ.r (F.star F.g0) := by
    rw [hZ, Matrix.map_sub _ (fun a b => map_sub p a b), ← hmat, ← hmat, hB1map, hof.res, hof.res]
  have hoff : ∀ i j : Fin n, i ≠ j → p (Z i j) = 0 := by
    intro i j hij
    have e := congrFun (congrFun hZp i) j
    rw [Matrix.map_apply] at e
    rw [e]
    exact ρ.diag i j hij
  have hdist : ∀ i j : Fin n, i ≠ j → res O C' (Z i i) ≠ res O C' (Z j j) := by
    intro i j hij
    have e : ∀ a, p (Z a a) = (ρ.r F.g0 - ρ.r (F.star F.g0)) a a := fun a => by
      rw [← hZp, Matrix.map_apply]
    rw [← res_map p, ← res_map p, e i, e j]
    convert hgood.zd i j hij using 1 <;> simp [NRep.bar, NRep.map]
  obtain ⟨h2', hh2, hθ2, hdiag2⟩ := pr_norm2 O C' C p n Z hmk hkp hθ hoff hdist
  set B2 := cj h2' B1 with hB2
  have hB2c : (B2.r F.c).mat = 1 := by
    show (conjBy h2' B1.r F.c).mat = 1
    have hl : (B1.r F.c).left = 1 := Units.ext hB1c
    unfold GG.mat
    rw [conj_left, B1.nu, hF.del_c, hl, mul_one, map_inv, sgnAct_neg_one, hθ2, mul_inv_cancel, Units.val_one]
  have hB2diag : ∀ i j : Fin n, i ≠ j → ((B2.r F.g0).mat - (B2.r (F.star F.g0)).mat) i j = 0 := by
    intro i j hij
    have e1 := conj_mat h2' B1.r (F.g0 : F.Γ) (frame_right_eq_one_of_G0 B1 F.g0)
    have e2 := conj_mat h2' B1.r ((F.star F.g0 : F.G0) : F.Γ) (frame_right_eq_one_of_G0 B1 (F.star F.g0))
    show ((conjBy h2' B1.r F.g0).mat - (conjBy h2' B1.r (F.star F.g0)).mat) i j = 0
    rw [e1, e2, ← Matrix.sub_mul, ← Matrix.mul_sub]
    exact hdiag2 i j hij
  have hB2cont : B2.Cont (maximalIdeal C') := cj_cont hF.del_open _ h2' B1 hB1cont
  obtain ⟨ρ', hof', hcont'⟩ := pr_ofbox hF C' (maximalIdeal C') B2 hB2c hB2diag hB2cont
  refine ⟨h2' * h1, ρ', ?_, ?_, hcont', ?_, ?_⟩
  · show ((h2' : Matrix (Fin n) (Fin n) C') * h1).map (p : C' →+* C) = 1
    rw [Matrix.map_mul]
    exact (congrArg₂ (· * ·) hh2 hh1).trans (Matrix.one_mul 1)
  · have e := hof'.map (p : C' →+* C)
    rw [show B2.map (p : C' →+* C) = B'.map (p : C' →+* C) from (cj_map _ h2' B1 hh2).trans hB1map] at e
    exact of_unique e hof
  · rw [conj_mul]
    exact hB2c
  · intro s
    rw [conj_mul]
    exact hof'.res s
