import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.OrdOfFlag

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private def diagHom {H C : Type} [Group H] [CommRing C] {n : ℕ} (m : H →* Matrix (Fin n) (Fin n) C)
    (h : ∀ s, UpT (m s)) (i : Fin n) : H →* C where
  toFun s := m s i i
  map_one' := by simp
  map_mul' s t := by
    rw [map_mul, Matrix.mul_apply, Finset.sum_eq_single i]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h' | h'
      · rw [h s i b h', zero_mul]
      · rw [h t b i h', mul_zero]
    · simp

private def conjHom {H R : Type} [Group H] [Monoid R] (u : Rˣ) (m : H →* R) : H →* R where
  toFun s := (u : R) * m s * ((u⁻¹ : Rˣ) : R)
  map_one' := by simp
  map_mul' s t := by simp [mul_assoc]

private theorem cont_conj {X C : Type} [TopologicalSpace X] [CommRing C] {n : ℕ} (I : Ideal C)
    (m : X → Matrix (Fin n) (Fin n) C) (hm : ∀ i j, AdicCont I fun s => m s i j) (a b : Matrix (Fin n) (Fin n) C)
    (i j : Fin n) : AdicCont I fun s => (a * m s * b) i j := by
  intro N
  have e : (fun s => Ideal.Quotient.mk (I ^ N) ((a * m s * b) i j)) = ∑ q, ∑ p, fun s => Ideal.Quotient.mk (I ^ N) (a i p) * Ideal.Quotient.mk (I ^ N) (m s p q) * Ideal.Quotient.mk (I ^ N) (b q j) := by
    funext s
    simp only [Matrix.mul_apply, Finset.sum_mul, map_sum, map_mul, Finset.sum_apply]
  rw [e]
  refine Finset.sum_induction _ IsLocallyConstant (fun _ _ hf hg => hf.add hg) (IsLocallyConstant.const 0) (fun q _ => ?_)
  refine Finset.sum_induction _ IsLocallyConstant (fun _ _ hf hg => hf.add hg) (IsLocallyConstant.const 0) (fun p _ => ?_)
  exact ((IsLocallyConstant.const _).mul (hm p q N)).mul (IsLocallyConstant.const _)

theorem UpperTheory.V.Fr.pr_ofbox :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (C : Type) [CommRing C] (I : Ideal C) (B : Box F n C), (B.r F.c).mat = 1 → (∀ i j, i ≠ j → ((B.r F.g0).mat - (B.r (F.star F.g0)).mat) i j = 0) → B.Cont I → ∃ ρ : NRep F n C, B.Of ρ ∧ ρ.Cont I := by
  intro l _ k _ _ F C₀ n hF C _ I B hc hdg hcont
  let rr : F.G0 →* Matrix (Fin n) (Fin n) C := (Units.coeHom _).comp (glPart F.del B.r B.nu)
  let m : ∀ v, F.Gv v →* Matrix (Fin n) (Fin n) C := fun v => conjHom (B.g v) (rr.comp (F.loc0 v))
  have hup : ∀ v s, UpT (m v s) := fun v s => B.tri v s
  let ψ : (v : F.V) → Fin n → F.Gv v →* Cˣ := fun v i => (diagHom (m v) (hup v) i).toHomUnits
  have hpol : ∀ g : F.G0, rr (F.star g) = Jmat C n * (rr g)ᵀ * Jmat C n := by
    intro g
    have hcc : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hF.c_sq
    have hs : ((F.star g : F.G0) : F.Γ) = F.c * (↑g)⁻¹ * F.c := by
      show ((F.conj g⁻¹ : F.G0) : F.Γ) = _
      rw [Frame.conj, MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply, hcc]
      rfl
    have hPl : (B.r F.c).left = 1 := Units.ext hc
    have hPr : (B.r F.c).right = -1 := by rw [B.nu, hF.del_c]
    have hX : (B.r (↑g)⁻¹).left = (glPart F.del B.r B.nu g)⁻¹ := by
      rw [← map_inv]
      rfl
    show ((B.r ↑(F.star g)).left : Matrix (Fin n) (Fin n) C) = _
    rw [hs, map_mul, map_mul, SemidirectProduct.mul_left, SemidirectProduct.mul_left]
    simp only [hPl, hPr, map_one, mul_one, one_mul, sgnAct_neg_one, hX, theta_val, inv_inv]
    rfl
  have hord : ∀ v (g : Fin n → F.Gv v), ordProd (fun s => rr (F.loc0 v s)) (fun i s => ((ψ v i s : Cˣ) : C)) g = 0 := by
    intro v g
    have hf : UpperTheory.V.W.HasFlag (rr.comp (F.loc0 v)).toHomUnits (ψ v) := ⟨B.g v, fun s => ⟨fun i j hij => hup v s i j hij, fun i => rfl⟩⟩
    exact (ord_of_flag (rr.comp (F.loc0 v)) (ψ v) hf).1 g
  refine ⟨⟨rr, ψ, hpol, fun i j hij => hdg i j hij, hord⟩, ⟨hc, fun s => rfl, fun v i s => rfl⟩, ?_, ?_⟩
  · intro i j N
    exact (hcont i j N).comp_continuous continuous_subtype_val
  · intro v i
    exact cont_conj I (fun s => (B.r (F.loc v s)).mat) (fun p q N => (hcont p q N).comp_continuous (continuous_subtype_val.comp (hF.loc_cont v))) ↑(B.g v) ↑(B.g v)⁻¹ i i
