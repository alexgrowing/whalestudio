import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DetAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.MapSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ConstantAndLinearPartsZeroOfMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.W1sMem

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem clr {K : Type} [Field K] {ι : Type} [Finite ι] (y : ι → FractionRing (PowerSeries K)) :
    ∃ (s : ℕ) (a : ι → PowerSeries K), ∀ i, algebraMap _ (FractionRing (PowerSeries K)) (a i) =
      algebraMap _ (FractionRing (PowerSeries K)) ((PowerSeries.X : PowerSeries K) ^ s) * y i := by
  obtain ⟨b, hb⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (PowerSeries K)) y
  have hb0 : (b : PowerSeries K) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  obtain ⟨s, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 PowerSeries.X_irreducible
  choose r hr using hb
  refine ⟨s, fun i => ↑u⁻¹ * r i, fun i => ?_⟩
  rw [map_mul, hr i, Algebra.smul_def, hu, map_mul, ← mul_assoc, ← map_mul]
  simp

section Mp

variable {A B : Type} [CommRing A] [CommRing B] {n a : ℕ} (f : A →+* B)

private theorem mp_smul (c : A) (M : Matrix (Fin n) (Fin n) A) : f.mapMatrix (c • M) = f c • f.mapMatrix M := by
  ext i j; simp

private theorem mp_tr (M : Matrix (Fin n) (Fin n) A) : f.mapMatrix Mᵀ = (f.mapMatrix M)ᵀ := rfl

private theorem mp_trace (M : Matrix (Fin n) (Fin n) A) : (f.mapMatrix M).trace = f M.trace := by
  simp [Matrix.trace]

variable {f}

private theorem mp_inj (hf : Function.Injective f) {M N : Matrix (Fin n) (Fin n) A}
    (h : f.mapMatrix M = f.mapMatrix N) : M = N := by
  ext i j
  apply hf
  simpa using congrFun (congrFun h i) j

private theorem mp_ev (hf : Function.Injective f) {M : Matrix (Fin n) (Fin n) A} :
    f.mapMatrix M ∈ Ev B B n a ↔ M ∈ Ev A A n a := by
  simp [Ev, blkMat, map_eq_zero_iff f hf]

private theorem mp_od (hf : Function.Injective f) {M : Matrix (Fin n) (Fin n) A} :
    f.mapMatrix M ∈ Od B B n a ↔ M ∈ Od A A n a := by
  simp [Od, blkMat, map_eq_zero_iff f hf]

variable {g : ℕ} (P Q : Matrix (Fin n) (Fin n) (DD A g)) (c : A)

private theorem eta_add : etaM (P + Q) = etaM P + etaM Q := rfl
private theorem eta_neg : etaM (-P) = -etaM P := rfl
private theorem eta_sub : etaM (P - Q) = etaM P - etaM Q := (rfl)
private theorem eta_tr : etaM Pᵀ = (etaM P)ᵀ := rfl
private theorem eta_C : etaM ((DD.C c : DD A g) • P) = c • etaM P := by
  have ha : (DD.C c : DD A g).a = c := rfl
  have he : (DD.C c : DD A g).eta = 0 := rfl
  have hp : (DD.C c : DD A g).ep = 0 := rfl
  have hq : (DD.C c : DD A g).ep' = 0 := rfl
  ext i j
  simp [etaM, ha, he, hp, hq]
private theorem eta_smul : etaM (c • P) = c • etaM P := eta_C P c
private theorem ep_add (j) : ep'M j (P + Q) = ep'M j P + ep'M j Q := rfl
private theorem ep_neg (j) : ep'M j (-P) = -ep'M j P := rfl
private theorem ep_sub (j) : ep'M j (P - Q) = ep'M j P - ep'M j Q := (rfl)
private theorem ep_tr (j) : ep'M j Pᵀ = (ep'M j P)ᵀ := rfl
private theorem ep_C (j) : ep'M j ((DD.C c : DD A g) • P) = c • ep'M j P := by
  have ha : (DD.C c : DD A g).a = c := rfl
  have hq : (DD.C c : DD A g).ep' = 0 := rfl
  ext i k
  simp [ep'M, ha, hq]
private theorem ep_smul (j) : ep'M j (c • P) = c • ep'M j P := ep_C P c j

private theorem constant_smul_mem_symmetric_deformation (h : P ∈ pairedDualFirstOrderDualMatrixSpace n A A g a) : (DD.C c : DD A g) • P ∈ pairedDualFirstOrderDualMatrixSpace n A A g a := by
  have ha : (DD.C c : DD A g).a = c := rfl
  have hp : (DD.C c : DD A g).ep = 0 := rfl
  have hq : (DD.C c : DD A g).ep' = 0 := rfl
  simp [pairedDualFirstOrderDualMatrixSpace, blkMat, ddPart] at h ⊢
  intro i j
  constructor
  · intro hij
    obtain ⟨h1, h2, h3⟩ := (h i j).1 hij
    refine ⟨by simp [h1], ?_, ?_⟩
    · funext k
      have e : (P i j).ep k = 0 := congrFun h2 k
      simp [ha, hp, h1, e]
    · funext k
      have e : (P i j).ep' k = 0 := congrFun h3 k
      simp [ha, hq, h1, e]
  · intro hij
    obtain ⟨h1, h2, h3⟩ := (h i j).2 hij
    refine ⟨by simp [h1], ?_, by simp [h3]⟩
    funext k
    have e : (P i j).ep k = 0 := congrFun h2 k
    simp [ha, hp, h1, e]

private theorem transpose_mem_symmetric_deformation (h : P ∈ pairedDualFirstOrderDualMatrixSpace n A A g a) : Pᵀ ∈ pairedDualFirstOrderDualMatrixSpace n A A g a := by
  simp [pairedDualFirstOrderDualMatrixSpace, blkMat, ddPart] at h ⊢
  intro i j
  have hji := h j i
  constructor
  · intro hij
    exact hji.1 hij.symm
  · intro hij
    exact hji.2 (fun e => hij e.symm)

end Mp

private theorem isKap {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x)
    (D : DetFr (FractionRing x.A) F.G₀ n) (ha : D.a = x.a) (hσ : D.σ = F.conj)
    (hr : ∀ g, D.r g = (algebraMap x.A (FractionRing x.A)).mapMatrix (x.ρX x.A g)) :
    D.IsKap fun j g => (algebraMap x.A (FractionRing x.A)).mapMatrix (k.κ j g) := by
  set φ := algebraMap x.A (FractionRing x.A) with hφ
  have hinj : Function.Injective φ := IsFractionRing.injective x.A (FractionRing x.A)
  have hsel := k.mem
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j g _ h _
    have e := (hsel j).2.2.1 g h
    simp only [one_smul]
    rw [hr, hr, e, map_add, map_mul, map_mul]
  · intro j g
    rw [ha, mp_od hinj]
    exact (hsel j).1 g
  · intro j g
    rw [hσ, (hsel j).2.2.2.1 g, map_neg, mp_tr]
  · intro c Y hY hYt hc
    rw [ha] at hY
    obtain ⟨s, b, hb⟩ := clr (K := x.K) (Sum.elim c (fun p : Fin n × Fin n => Y p.1 p.2))
    set t : FractionRing x.A := φ ((PowerSeries.X : x.A) ^ s) with ht
    have ht0 : t ≠ 0 :=
      (map_ne_zero_iff φ hinj).2 (pow_ne_zero _ PowerSeries.X_ne_zero)
    let c' : Fin k.g → x.A := fun j => b (Sum.inl j)
    let Y' : Matrix (Fin n) (Fin n) x.A := fun i j => b (Sum.inr (i, j))
    have hc' : ∀ j, φ (c' j) = t * c j := fun j => hb (Sum.inl j)
    have hY' : φ.mapMatrix Y' = t • Y := by
      ext i j
      exact hb (Sum.inr (i, j))
    have hY'od : Y' ∈ Od x.A x.A n x.a := by
      rw [← mp_od hinj, hY']
      exact Submodule.smul_mem _ t hY
    have hY't : Y'ᵀ = -Y' := by
      apply mp_inj hinj
      rw [mp_tr, hY', map_neg, hY', Matrix.transpose_smul, hYt, smul_neg]
    have hfun : (∑ j, c' j • k.κ j) = dY F (x.ρX x.A) Y' := by
      funext g
      apply mp_inj hinj
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, map_sum, mp_smul, hc', mul_smul]
      rw [← Finset.smul_sum, hc g]
      simp only [dTw, dY, one_smul, map_sub, map_mul, hY', hr]
      simp [smul_sub, Matrix.mul_smul, Matrix.smul_mul]
    have hzero := k.indep c' ⟨Y', hY'od, hY't, hfun⟩
    funext j
    have e := hc' j
    rw [hzero] at e
    simp only [Pi.zero_apply, map_zero] at e
    exact (mul_eq_zero.1 e.symm).resolve_left ht0

theorem UpperTheory.V.Pa.Det.detAsm :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x), l ≠ 2 → (∃ g : F.G₀, PadicInt.toZMod ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1) → Detects k (F.G' : Set F.G₀) := by
  intro l _ F n x k hl hε
  set φ := algebraMap x.A (FractionRing x.A) with hφ
  have hinj : Function.Injective φ := IsFractionRing.injective x.A (FractionRing x.A)
  obtain ⟨D, hDa, hDG, hDr, hDσ, hDχ⟩ := UpperTheory.V.Pa.Det.detFr x hl hε
  have hr : ∀ g, D.r g = φ.mapMatrix (x.ρX x.A g) := by
    intro g
    rw [hDr]
    ext i j
    simp [NP.ρX, hφ]
  have hK := isKap k D hDa hDσ hr
  have hmapid : ∀ M : Matrix (Fin n) (Fin n) x.A, M.map (algebraMap x.A x.A) = M := by
    intro M
    ext i j
    simp
  intro z hz hell
  obtain ⟨hzW, -, hzc, hzconj⟩ := hz
  let e : F.Γ → x.A := fun g => algebraMap ℤ_[l] x.A ↑(F.ε g)
  have heps : ∀ g, epsD k x.A g = (DD.C (e g) : DD x.A k.g) := fun g => rfl
  have hχ : ∀ g : F.G₀, D.χF g = φ (e g) := hDχ
  have hW := UpperTheory.V.Pa.Det.w1sMem (A := x.A) (X := x.A) (g := k.g) (n := n) (a := x.a)
  have hact := UpperTheory.V.Pa.Det.w1sAct k x.A
  let ph : F.G₀ → Matrix (Fin n) (Fin n) (FractionRing x.A) := fun g => φ.mapMatrix (etaM (z g))
  let la : Fin k.g → F.G₀ → Matrix (Fin n) (Fin n) (FractionRing x.A) :=
    fun j g => φ.mapMatrix (ep'M j (z g))
  let s : FractionRing x.A := -φ (e F.c)
  have hee : e F.c * e F.c = 1 := by
    simp only [e, ← map_mul, ← Units.val_mul, ← map_mul F.ε, F.c_sq, map_one, Units.val_one]
  have hTw : D.IsTw (fun j g => φ.mapMatrix (k.κ j g)) s ph la := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [s, neg_mul_neg, ← map_mul, hee, map_one]
    · intro j g _ h _
      simp only [la, hzc g h, ep_add, heps, ep_C, (hact (z h) (hzW h) g).2.1 j, map_add, mp_smul,
        map_mul, hr, hχ]
    · intro j g
      rw [hDa, mp_od hinj]
      exact (hW.1 _ (hzW g)).2 j
    · intro j g
      simp only [la, hDσ, hzconj g, ep_neg, heps, ep_C, ep_tr, map_neg, mp_smul, mp_tr, s, neg_smul]
    · intro g
      rw [hDa, mp_ev hinj]
      exact (hW.1 _ (hzW g)).1
    · intro g h
      simp only [ph, la, hzc g h, eta_add, heps, eta_C, (hact (z h) (hzW h) g).2.2.1, hmapid,
        map_add, mp_smul, map_sum, map_sub, map_mul, hr, hχ]
    · intro g
      simp only [ph, hDσ, hzconj g, eta_neg, heps, eta_C, eta_tr, map_neg, mp_smul, mp_tr, s, neg_smul]
    · intro g hg
      rw [hDG] at hg
      have h0 := hell g hg
      simp only [ell, (hact (z g) (hzW g) g).2.2.2, hmapid] at h0
      simp only [ph, la, hr, ← map_mul, mp_trace, ← map_sum, ← map_add, h0, map_zero]
  obtain ⟨Y₀, Y, hY₀ev, hY₀s, hY, hph⟩ := UpperTheory.V.Pa.Det.detAlg D _ la s ph hK hTw
  obtain ⟨m, b, hb⟩ := clr (K := x.K)
    (Sum.elim (fun p : Fin n × Fin n => Y₀ p.1 p.2) (fun q : Fin k.g × Fin n × Fin n => Y q.1 q.2.1 q.2.2))
  set t : FractionRing x.A := φ ((PowerSeries.X : x.A) ^ m) with ht
  let Y₀' : Matrix (Fin n) (Fin n) x.A := fun i j => b (Sum.inl (i, j))
  let Y' : Fin k.g → Matrix (Fin n) (Fin n) x.A := fun q i j => b (Sum.inr (q, i, j))
  have hY₀' : φ.mapMatrix Y₀' = t • Y₀ := by
    ext i j
    exact hb (Sum.inl (i, j))
  have hY' : ∀ q, φ.mapMatrix (Y' q) = t • Y q := by
    intro q
    ext i j
    exact hb (Sum.inr (q, i, j))
  have hY₀'ev : Y₀' ∈ Ev x.A x.A n x.a := by
    rw [← mp_ev hinj, hY₀', ← hDa]
    exact Submodule.smul_mem _ t hY₀ev
  have hY'od : ∀ q, Y' q ∈ Od x.A x.A n x.a := by
    intro q
    rw [← mp_od hinj, hY', ← hDa]
    exact Submodule.smul_mem _ t (hY q).1
  obtain ⟨Z, hZW, hZeta, hZep⟩ := hW.2.2 Y₀' Y' hY₀'ev hY'od
  refine ⟨m, Z, hZW, ?_, ?_⟩
  · apply hW.2.1
    · rw [heps]
      exact Submodule.neg_mem _ (constant_smul_mem_symmetric_deformation _ _ (transpose_mem_symmetric_deformation _ hZW))
    · exact hZW
    · apply mp_inj hinj
      rw [heps, eta_neg, eta_C, eta_tr, hZeta, map_neg, mp_smul, mp_tr, hY₀']
      conv_rhs => rw [← hY₀s]
      simp only [s, Matrix.transpose_smul, smul_smul, neg_smul, smul_neg, mul_neg, mul_comm]
    · intro j
      apply mp_inj hinj
      rw [heps, ep_neg, ep_C, ep_tr, hZep, map_neg, mp_smul, mp_tr, hY']
      conv_rhs => rw [← (hY j).2.1]
      simp only [s, Matrix.transpose_smul, smul_smul, neg_smul, smul_neg, mul_neg, mul_comm]
  · funext g
    apply hW.2.1
    · exact Submodule.smul_mem _ _ (hzW g)
    · rw [heps]
      exact Submodule.sub_mem _ (constant_smul_mem_symmetric_deformation _ _ (hact Z hZW g).1) hZW
    · apply mp_inj hinj
      have h1 := hph g
      simp only [ph] at h1
      simp only [Pi.smul_apply, eta_smul, heps, eta_sub, eta_C, (hact Z hZW g).2.2.1, hmapid,
        hZeta, hZep, map_sub, map_add, mp_smul, map_sum, map_mul, ← hr, hY₀', hY', h1, dTw, hχ]
      simp only [smul_add, smul_sub, Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
        mul_comm]
      abel
    · intro j
      apply mp_inj hinj
      have h1 := (hY j).2.2 g
      simp only [la] at h1
      simp only [Pi.smul_apply, ep_smul, heps, ep_sub, ep_C, (hact Z hZW g).2.1 j,
        hZep, map_sub, mp_smul, map_mul, ← hr, hY', h1, dTw, hχ]
      simp only [smul_sub, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm]
      rfl
