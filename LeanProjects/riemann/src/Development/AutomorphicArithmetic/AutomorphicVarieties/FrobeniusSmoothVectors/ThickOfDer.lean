import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpanOfVariable

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section Th

variable {R Q : Type} [CommRing R] [CommRing Q] (π : R →+* Q) (D : R →+ Q)

private def th (a : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) Q :=
  !![π (a 0 0), D (a 0 1), π (a 0 2); 0, π (a 1 1), 0; π (a 2 0), D (a 2 1), π (a 2 2)]

private def Ev (a : Matrix (Fin 3) (Fin 3) R) : Prop :=
  (π (a 0 1) = 0 ∧ π (a 1 0) = 0 ∧ π (a 1 2) = 0 ∧ π (a 2 1) = 0) ∧
    D (a 0 0) = 0 ∧ D (a 0 2) = 0 ∧ D (a 1 1) = 0 ∧ D (a 2 0) = 0 ∧ D (a 2 2) = 0

variable {π D} (hD : ∀ x y, D (x * y) = π x * D y + π y * D x)
include hD

private theorem ev_mul {a b : Matrix (Fin 3) (Fin 3) R} (ha : Ev π D a) (hb : Ev π D b) :
    Ev π D (a * b) ∧ th π D (a * b) = th π D a * th π D b := by
  obtain ⟨⟨a1, a2, a3, a4⟩, a5, a6, a7, a8, a9⟩ := ha
  obtain ⟨⟨b1, b2, b3, b4⟩, b5, b6, b7, b8, b9⟩ := hb
  refine ⟨by simp [Ev, Matrix.mul_apply, Fin.sum_univ_three, *], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [th, Matrix.mul_apply, Fin.sum_univ_three, *] <;> ring

private theorem D_one : D 1 = 0 := by simpa using hD 1 1

private theorem th_one : th π D 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [th]

omit hD in
private theorem ev_sub {a : Matrix (Fin 3) (Fin 3) R} (ha : Ev π D a) {c : R} (hc : D c = 0) :
    Ev π D (a - c • (1 : Matrix (Fin 3) (Fin 3) R)) ∧
      th π D (a - c • (1 : Matrix (Fin 3) (Fin 3) R)) = th π D a - π c • (1 : Matrix (Fin 3) (Fin 3) Q) := by
  obtain ⟨⟨a1, a2, a3, a4⟩, a5, a6, a7, a8, a9⟩ := ha
  refine ⟨by simp [Ev, *], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [th]

private theorem th_ord {H : Type} (r : H → Matrix (Fin 3) (Fin 3) R) (ψ : Fin 3 → H → R) (g : Fin 3 → H)
    (hr : ∀ s, Ev π D (r s)) (hψ : ∀ i s, D (ψ i s) = 0) (h : ordProd r ψ g = 0) :
    ordProd (fun s => th π D (r s)) (fun i s => π (ψ i s)) g = 0 := by
  have e i := ev_sub (hr (g i)) (hψ i (g i))
  simp only [ordProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one] at h ⊢
  rw [← (e _).2, ← (e _).2, ← (e _).2, ← (ev_mul hD (e _).1 (e _).1).2,
    ← (ev_mul hD (e _).1 (ev_mul hD (e _).1 (e _).1).1).2, h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [th]

private theorem D_pow {I : Ideal R} (N : ℕ) : ∀ x ∈ I ^ (N + 1), D x ∈ I.map π ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) fun a b ha hb => by rw [map_add]; exact add_mem ha hb
    rw [hD]
    refine add_mem (Ideal.mul_mem_right _ _ ?_) ?_
    · rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ ha
    · rw [pow_succ']; exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ hb) (ih a ha)

omit hD in
private theorem ac_map {Γ : Type} [TopologicalSpace Γ] {I : Ideal R} {J : Ideal Q} {f : Γ → R} (hf : AdicCont I f)
    (T : R →+ Q) (hT : ∀ N, ∀ x ∈ I ^ (N + 1), T x ∈ J ^ N) : AdicCont J fun g => T (f g) := fun N => by
  refine (IsLocallyConstant.iff_exists_open _).2 fun g => ?_
  obtain ⟨U, hU, hg, h⟩ := (IsLocallyConstant.iff_exists_open _).1 (hf (N + 1)) g
  refine ⟨U, hU, hg, fun g' hg' => Ideal.Quotient.eq.2 ?_⟩
  rw [← map_sub]
  exact hT N _ (Ideal.Quotient.eq.1 (h g' hg'))

end Th

private theorem ord_star {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {R : Type} [CommRing R]
    (ρ : NRep F 3 R) (v : F.V) (g : Fin 3 → F.Gv v) :
    ordProd (fun s => ρ.r (F.star (F.loc0 v s))) (fun i s => (ρ.ψ v i.rev s : R)) g = 0 := by
  have hJ : Jmat R 3 * Jmat R 3 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Jmat, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev]
  have e (a : Matrix (Fin 3) (Fin 3) R) (c : R) : Jmat R 3 * aᵀ * Jmat R 3 - c • (1 : Matrix (Fin 3) (Fin 3) R) =
      Jmat R 3 * (a - c • (1 : Matrix (Fin 3) (Fin 3) R))ᵀ * Jmat R 3 := by
    simp [mul_sub, sub_mul, hJ]
  have hJ' (a : Matrix (Fin 3) (Fin 3) R) : Jmat R 3 * (Jmat R 3 * a) = a := by rw [← mul_assoc, hJ, one_mul]
  have h := congrArg (fun a => Jmat R 3 * aᵀ * Jmat R 3) (ρ.ord v fun i => g i.rev)
  simp only [ordProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, ρ.pol, e] at h ⊢
  simp only [transpose_mul, transpose_zero, mul_zero, zero_mul, mul_assoc, hJ'] at h ⊢
  exact h

private theorem thick_of_der {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}
    (hF : F.Ok C₀) {R : Type} [CommRing R] [IsLocalRing R] (ρ : NRep F 3 R) (P : Ideal R) [P.IsPrime] (hP : ρ.TE P)
    (hc : ρ.Cont (maximalIdeal R)) (hζ : IsUnit (ρ.r F.g0 0 0 - ρ.r F.g0 2 2)) (D : R →+ R ⧸ P)
    (hD : ∀ x y, D (x * y) = Ideal.Quotient.mk P x * D y + Ideal.Quotient.mk P y * D x)
    (h0 : ∀ g i j, ¬ Odd (w 3 i - w 3 j) → D (ρ.r g i j) = 0) (hψ : ∀ v i s, D (ρ.ψ v i s) = 0)
    (hne : ¬ ∀ g i j, D (ρ.r g i j) = 0) : Thick ρ P := by
  have hs := (UpperTheory.V.Fr.star hF).2.2.2.2 ρ
  have h1 g i j (h : Odd (w 3 i - w 3 j)) : Ideal.Quotient.mk P (ρ.r g i j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (hP.2.2 (Ideal.subset_span ⟨g, i, j, h, rfl⟩))
  have hE g : Ev (Ideal.Quotient.mk P) D (ρ.r g) :=
    ⟨⟨h1 g _ _ (by decide), h1 g _ _ (by decide), h1 g _ _ (by decide), h1 g _ _ (by decide)⟩,
      h0 g _ _ (by decide), h0 g _ _ (by decide), h0 g _ _ (by decide), h0 g _ _ (by decide), h0 g _ _ (by decide)⟩
  let r : F.G0 →* Matrix (Fin 3) (Fin 3) (R ⧸ P) :=
    { toFun := fun g => th (Ideal.Quotient.mk P) D (ρ.r g)
      map_one' := by rw [map_one, th_one hD]
      map_mul' := fun g h => by rw [map_mul, (ev_mul hD (hE g) (hE h)).2] }
  have c1 i j : AdicCont ((maximalIdeal R).map (Ideal.Quotient.mk P)) fun g => D (ρ.r g i j) :=
    ac_map (hc.1 i j) D fun N => D_pow hD N
  have c2 i j : AdicCont ((maximalIdeal R).map (Ideal.Quotient.mk P)) fun g => Ideal.Quotient.mk P (ρ.r g i j) :=
    ac_map (hc.1 i j) (Ideal.Quotient.mk P).toAddMonoidHom fun N x hx => by
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ (Ideal.pow_le_pow_right N.le_succ hx)
  have c3 : AdicCont ((maximalIdeal R).map (Ideal.Quotient.mk P)) fun _ : F.G0 => (0 : R ⧸ P) :=
    fun _ => IsLocallyConstant.const _
  refine ⟨hP, r, fun i j => ?_, fun g i j h => ?_, fun g => ⟨rfl, rfl⟩,
    fun v g => th_ord hD _ _ g (fun _ => hE _) (hψ v) (ρ.ord v g),
    fun v g => th_ord hD _ _ g (fun _ => hE _) (fun i => hψ v i.rev) (ord_star ρ v g), ?_⟩
  · fin_cases i <;> fin_cases j <;> first | exact c2 _ _ | exact c1 _ _ | exact c3
  · fin_cases i <;> fin_cases j <;> first | rfl | exact absurd (by decide) h
  rintro K _ f hf ⟨y, y1, hy⟩
  have u : f (Ideal.Quotient.mk P (ρ.r F.g0 0 0)) - f (Ideal.Quotient.mk P (ρ.r F.g0 2 2)) ≠ 0 := by
    rw [← map_sub, ← map_sub]
    exact ((hζ.map _).map f).ne_zero
  have d i j (h : i ≠ j) : ρ.r (F.star F.g0) i j = ρ.r F.g0 i j := (sub_eq_zero.1 (ρ.diag i j h)).symm
  have a g i : f (r g i 0) * y 0 + f (r g i 1) + f (r g i 2) * y 2 = f (r g 1 1) * y i := by
    simpa [mulVec, dotProduct, Fin.sum_univ_three, y1] using congrFun (hy g) i
  have a0 g : f (Ideal.Quotient.mk P (ρ.r g 0 0)) * y 0 + f (D (ρ.r g 0 1)) +
      f (Ideal.Quotient.mk P (ρ.r g 0 2)) * y 2 = f (Ideal.Quotient.mk P (ρ.r g 1 1)) * y 0 := a g 0
  have a2 g : f (Ideal.Quotient.mk P (ρ.r g 2 0)) * y 0 + f (D (ρ.r g 2 1)) +
      f (Ideal.Quotient.mk P (ρ.r g 2 2)) * y 2 = f (Ideal.Quotient.mk P (ρ.r g 1 1)) * y 2 := a g 2
  have s0 : ρ.r (F.star F.g0) 0 0 = ρ.r F.g0 2 2 := hs _ _ _
  have s1 : ρ.r (F.star F.g0) 1 1 = ρ.r F.g0 1 1 := hs _ _ _
  have s2 : ρ.r (F.star F.g0) 2 2 = ρ.r F.g0 0 0 := hs _ _ _
  have y0 : y 0 = 0 := by
    have e := a0 (F.star F.g0)
    rw [s0, s1, d 0 1 (by decide), d 0 2 (by decide)] at e
    exact (mul_eq_zero.1 (by linear_combination a0 F.g0 - e)).resolve_left u
  have y2 : y 2 = 0 := by
    have e := a2 (F.star F.g0)
    rw [s2, s1, d 2 1 (by decide), d 2 0 (by decide)] at e
    exact (mul_eq_zero.1 (by linear_combination e - a2 F.g0)).resolve_left u
  have b0 g : D (ρ.r g 0 1) = 0 := hf (by simpa [y0, y2] using a0 g)
  have b2 g : D (ρ.r g 2 1) = 0 := hf (by simpa [y0, y2] using a2 g)
  have b1 g : D (ρ.r g 1 2) = 0 := by have := b0 (F.star g); rwa [hs] at this
  have b3 g : D (ρ.r g 1 0) = 0 := by have := b2 (F.star g); rwa [hs] at this
  refine hne fun g i j => ?_
  fin_cases i <;> fin_cases j <;>
    first | exact b0 g | exact b1 g | exact b2 g | exact b3 g | exact h0 g _ _ (by decide)

private theorem span_X {O σ : Type} [CommRing O] (I : Ideal (MvPowerSeries σ O)) (s : Finset σ)
    (hs : ∀ i ∈ s, MvPowerSeries.X i ∈ I) :
    ∀ f : MvPowerSeries σ O, (∀ n : σ →₀ ℕ, (∀ i ∈ s, n i = 0) → MvPowerSeries.coeff n f = 0) → f ∈ I :=
  _root_.UpperTheory.Reformulated.B.SpanOfVariable.span_X I s hs

private theorem pderiv_even {O : Type} [CommRing O] {a g : ℕ} (I : Ideal (MvPowerSeries (Fin a ⊕ Fin g) O))
    (hI : ∀ j, MvPowerSeries.X (.inr j) ∈ I) {f : MvPowerSeries (Fin a ⊕ Fin g) O}
    (hf : f ∈ wtPart O (Space.Loc.par a g) 0) (b : Fin g) : MvPowerSeries.pderiv O (.inr b) f ∈ I := by
  refine span_X I (Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩) (by simpa using hI) _ fun n hn => ?_
  have h : ∀ j, n (.inr j) = 0 := by simpa using hn
  rw [MvPowerSeries.coeff_pderiv, hf, zero_mul]
  rw [map_add, Finsupp.weight_single, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Space.Loc.par, h]

private theorem der_ex {O R Q : Type} [CommRing O] [CommRing R] [CommRing Q] [IsDomain Q] [Algebra O R] {a b g : ℕ}
    (p : MvPowerSeries (Fin a ⊕ Fin g) O →ₐ[O] R) (hp : Function.Surjective p) (π : R →+* Q)
    (Fe : Fin b → MvPowerSeries (Fin a ⊕ Fin g) O) (M : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin a ⊕ Fin g) O))
    (hk : RingHom.ker p = Ideal.span (Set.range Fe ∪ Set.range (M *ᵥ fun j => MvPowerSeries.X (.inr j))))
    (hFe : ∀ i, Fe i ∈ wtPart O (Space.Loc.par a g) 0) (hm : ∀ j, π (p (MvPowerSeries.X (.inr j))) = 0)
    (hM : π (p M.det) = 0) :
    ∃ D : R →+ Q, (∀ x y, D (x * y) = π x * D y + π y * D x) ∧
      (∀ f ∈ wtPart O (Space.Loc.par a g) 0, D (p f) = 0) ∧ ∃ j, D (p (MvPowerSeries.X (.inr j))) ≠ 0 := by
  let φ : MvPowerSeries (Fin a ⊕ Fin g) O →+* Q := π.comp (p : _ →+* R)
  have hφ f : π (p f) = φ f := rfl
  simp only [hφ] at hm hM
  obtain ⟨ν, hν, hMν⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := φ.mapMatrix M)).2 (by rw [← RingHom.map_det, hM])
  let D0 : MvPowerSeries (Fin a ⊕ Fin g) O →+ Q :=
    { toFun := fun f => ∑ c, φ (MvPowerSeries.pderiv O (.inr c) f) * ν c
      map_zero' := by simp
      map_add' := fun x y => by simp [add_mul, Finset.sum_add_distrib] }
  have e0 f : D0 f = ∑ c, φ (MvPowerSeries.pderiv O (.inr c) f) * ν c := rfl
  have l0 x y : D0 (x * y) = φ x * D0 y + φ y * D0 x := by
    simp [e0, Finset.mul_sum, add_mul, Finset.sum_add_distrib, mul_assoc]
  have x0 j : D0 (MvPowerSeries.X (.inr j)) = ν j := by
    rw [e0, Finset.sum_eq_single j (fun c _ h => by
      rw [MvPowerSeries.pderiv_X_of_ne (by simpa using h.symm), map_zero, zero_mul]) (by simp)]
    simp
  have ev f (hf : f ∈ wtPart O (Space.Loc.par a g) 0) : D0 f = 0 :=
    (e0 f).trans <| Finset.sum_eq_zero fun c _ => by rw [show φ _ = 0 from pderiv_even (RingHom.ker φ) hm hf c, zero_mul]
  have k0 f (hf : p f = 0) : D0 f = 0 := by
    have hf' : f ∈ RingHom.ker p := hf
    rw [hk] at hf'
    clear hf
    induction hf' using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact ev _ (hFe i)
      · have := congrFun hMν i
        simpa [mulVec, dotProduct, l0, hm, x0] using this
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x hx h =>
      have : p x = 0 := hk.ge hx
      rw [smul_eq_mul, l0, h, ← hφ x, this]
      simp
  have k1 f : D0 (Function.surjInv hp (p f)) = D0 f := by
    rw [← sub_eq_zero, ← map_sub]
    exact k0 _ (by rw [map_sub, Function.surjInv_eq hp, sub_self])
  refine ⟨AddMonoidHom.mk' (fun x => D0 (Function.surjInv hp x)) fun x y => ?_, fun x y => ?_, fun f hf => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := hp x
    obtain ⟨y, rfl⟩ := hp y
    rw [← map_add p, k1, k1, k1, map_add]
  · obtain ⟨x, rfl⟩ := hp x
    obtain ⟨y, rfl⟩ := hp y
    simp only [AddMonoidHom.mk'_apply]
    rw [← map_mul p, k1, k1, k1, l0, hφ, hφ]
  · exact (k1 f).trans (ev f hf)
  · obtain ⟨j, hj⟩ := Function.ne_iff.1 hν
    exact ⟨j, fun h => hj ((x0 j).symm.trans ((k1 _).symm.trans h))⟩

theorem UpperTheory.V.Fr.thick :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ S : Space O F 3, ∀ (x : Ideal S.A) (L : S.Loc x), ∀ (E : L.EPres) (M : Matrix (Fin E.g) (Fin E.g) (MvPowerSeries (Fin E.a ⊕ Fin E.g) L.O')), E.Go = M *ᵥ (fun j => MvPowerSeries.X (.inr j)) → ∀ P : Ideal L.R, P.IsPrime → L.ρ.TE P → E.p M.det ∈ P → Thick L.ρ P := by
  intro l _ O _ _ _ _ F C₀ hF S x L E M hG P hP hT hM
  obtain ⟨hc, hb, -⟩ := UpperTheory.V.Fr.loc_rho hF (Or.inr rfl) S x L
  have hm j : E.p (MvPowerSeries.X (.inr j)) ∈ L.ρ.ee := E.ee ▸ Ideal.subset_span ⟨j, rfl⟩
  obtain ⟨D, hD, h0, j, hj⟩ := der_ex E.p E.surj (Ideal.Quotient.mk P) E.Fe M (hG ▸ E.ker) E.even
    (fun j => Ideal.Quotient.eq_zero_iff_mem.2 (hT.2.2 (hm j))) (Ideal.Quotient.eq_zero_iff_mem.2 hM)
  haveI : IsLocalHom (algebraMap O L.R) := ⟨fun a ha => by
    by_contra hn
    have h1 : algebraMap O L.O' a ∈ maximalIdeal L.O' := L.unr ▸ Ideal.mem_map_of_mem _ hn
    rw [IsScalarTower.algebraMap_apply O L.O' L.R] at ha
    exact h1 (IsLocalHom.map_nonunit _ ha)⟩
  refine thick_of_der hF L.ρ P hT hc ?_ D hD (fun g i j h => ?_) (fun v i s => ?_) fun h => hj ?_
  · have e := (hb (ResidueField.map (algebraMap O L.R)) fun a => ResidueField.map_residue _ a).1 F.g0
    by_contra hn
    have h1 : residue L.R (L.ρ.r F.g0 0 0 - L.ρ.r F.g0 2 2) = 0 := (residue_eq_zero_iff _).2 hn
    rw [map_sub, sub_eq_zero] at h1
    have h2 := Units.ext ((ResidueField.map (algebraMap O L.R)).injective ((e 0).symm.trans (h1.trans (e 2))))
    rw [show w 3 0 = 1 by decide, show w 3 2 = -1 by decide, zpow_one, _root_.zpow_neg_one] at h2
    exact hF.baseSubgroup_spec (by rw [sq]; exact mul_eq_one_iff_eq_inv.2 h2)
  · obtain ⟨f, hf, e⟩ := E.ent g i j
    rw [(ZMod.intCast_eq_zero_iff_even).2 (Int.not_odd_iff_even.1 h)] at hf
    exact e ▸ h0 f hf
  · obtain ⟨f, hf, e⟩ := E.base (S.ψB v i s)
    exact (congrArg D e.symm).trans (h0 f hf)
  · have key y (hy : y ∈ L.ρ.ee) : D y = 0 := by
      induction hy using Submodule.span_induction with
      | mem y hy => obtain ⟨g, a, b, -, rfl⟩ := hy; exact h g a b
      | zero => simp
      | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
      | smul c y hy h' => rw [smul_eq_mul, hD, h', Ideal.Quotient.eq_zero_iff_mem.2 (hT.2.2 hy)]; simp
    exact key _ (hm j)
