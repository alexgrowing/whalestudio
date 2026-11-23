import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich

noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

namespace UpperTheory.V.Z.Sym.Sig

section Alg

variable {K : Type} [Field K] {Δ s : K}

private theorem proj_apply (hs : s * s = Δ) (x : Lsq K Δ) : proj hs x = x.re + s * x.im := rfl

private theorem proj_star (hs : s * s = Δ) (x : Lsq K Δ) : proj hs (star x) = x.re - s * x.im := by
  simp [proj_apply]; ring

private def lf (s Δ p q : K) : Lsq K Δ := ⟨(p + q) / 2, (p - q) / (2 * s)⟩

private theorem proj_lf (hs : s * s = Δ) (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) (p q : K) : proj hs (lf s Δ p q) = p := by
  rw [proj_apply]
  show (p + q) / 2 + s * ((p - q) / (2 * s)) = p
  field_simp
  ring

private theorem eq_lf (hs : s * s = Δ) (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) (x : Lsq K Δ) :
    x = lf s Δ (proj hs x) (proj hs (star x)) := by
  rw [proj_star, proj_apply]
  refine QuadraticAlgebra.ext_iff.2 ⟨?_, ?_⟩
  · show x.re = (x.re + s * x.im + (x.re - s * x.im)) / 2
    field_simp
    ring
  · show x.im = (x.re + s * x.im - (x.re - s * x.im)) / (2 * s)
    field_simp
    ring

private theorem lf_self (h2 : (2 : K) ≠ 0) (z : K) : lf s Δ z z = algebraMap K (Lsq K Δ) z := by
  refine QuadraticAlgebra.ext_iff.2 ⟨?_, ?_⟩
  · show (z + z) / 2 = _
    rw [QuadraticAlgebra.algebraMap_re]
    field_simp
    ring
  · show (z - z) / (2 * s) = _
    simp

private theorem star_lf (hs : s * s = Δ) (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) (p q : K) : star (lf s Δ p q) = lf s Δ q p := by
  refine QuadraticAlgebra.ext_iff.2 ⟨?_, ?_⟩
  · rw [QuadraticAlgebra.re_star]
    show (p + q) / 2 + 0 * ((p - q) / (2 * s)) = (q + p) / 2
    ring
  · rw [QuadraticAlgebra.im_star]
    show -((p - q) / (2 * s)) = (q - p) / (2 * s)
    ring

private theorem lf_neg (hs : s * s = Δ) (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) (p q : K) : lf s Δ (-p) (-q) = -lf s Δ p q := by
  refine QuadraticAlgebra.ext_iff.2 ⟨?_, ?_⟩
  · show (-p + -q) / 2 = -((p + q) / 2)
    ring
  · show (-p - -q) / (2 * s) = -((p - q) / (2 * s))
    ring

private theorem lf_mul (hs : s * s = Δ) (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) (a b c d : K) :
    lf s Δ a b * lf s Δ c d = lf s Δ (a * c) (b * d) := by
  refine QuadraticAlgebra.ext_iff.2 ⟨?_, ?_⟩
  · rw [QuadraticAlgebra.re_mul]
    show (a + b) / 2 * ((c + d) / 2) + Δ * ((a - b) / (2 * s)) * ((c - d) / (2 * s)) = (a * c + b * d) / 2
    rw [← hs]
    field_simp
    ring
  · rw [QuadraticAlgebra.im_mul]
    show (a + b) / 2 * ((c - d) / (2 * s)) + (a - b) / (2 * s) * ((c + d) / 2) + 0 * ((a - b) / (2 * s)) * ((c - d) / (2 * s)) = (a * c - b * d) / (2 * s)
    field_simp
    ring

private theorem lf_add (hs : s * s = Δ) (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) (a b c d : K) :
    lf s Δ a b + lf s Δ c d = lf s Δ (a + c) (b + d) := by
  refine QuadraticAlgebra.ext_iff.2 ⟨?_, ?_⟩
  · show (a + b) / 2 + (c + d) / 2 = (a + c + (b + d)) / 2
    ring
  · show (a - b) / (2 * s) + (c - d) / (2 * s) = (a + c - (b + d)) / (2 * s)
    ring

private theorem lf_sub (hs : s * s = Δ) (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) (a b c d : K) :
    lf s Δ a b - lf s Δ c d = lf s Δ (a - c) (b - d) := by
  refine QuadraticAlgebra.ext_iff.2 ⟨?_, ?_⟩
  · show (a + b) / 2 - (c + d) / 2 = (a - c + (b - d)) / 2
    ring
  · show (a - b) / (2 * s) - (c - d) / (2 * s) = (a - c - (b - d)) / (2 * s)
    ring

private def gm (s Δ : K) (h : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) (Lsq K Δ) :=
  !![lf s Δ (h 0 0) (h 1 1), lf s Δ (h 0 1) (-h 1 0); lf s Δ (h 1 0) (-h 0 1), lf s Δ (h 1 1) (h 0 0)]

private theorem det_gm (hs : s * s = Δ) (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) (h : Matrix (Fin 2) (Fin 2) K) :
    (gm s Δ h).det = algebraMap K _ h.det := by
  rw [gm, det_fin_two_of, lf_mul hs h2 h0, lf_mul hs h2 h0, lf_sub hs h2 h0, det_fin_two, ← lf_self h2]
  congr 1 <;> ring

private theorem trace_gm (hs : s * s = Δ) (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) (h : Matrix (Fin 2) (Fin 2) K) :
    (gm s Δ h).trace = algebraMap K _ h.trace := by
  rw [gm, trace_fin_two_of, lf_add hs h2 h0, trace_fin_two, ← lf_self h2]
  congr 1
  ring

private theorem conj_w (M : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) :
    (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * M * !![0, 1; -1, 0] = !![M 1 1, -M 1 0; -M 0 1, M 0 0] := by
  rw [Matrix.eta_fin_two M]
  simp [Matrix.mul_fin_two]

private theorem mem_DX (g : GL (Fin 2) (Lsq K Δ)) : g ∈ DX Δ ↔
    star (g.val 0 0) = g.val 1 1 ∧ star (g.val 0 1) = -g.val 1 0 ∧ star (g.val 1 0) = -g.val 0 1 ∧ star (g.val 1 1) = g.val 0 0 := by
  have e : g ∈ DX Δ ↔ g.val.map star = !![0, -1; 1, 0] * g.val * !![0, 1; -1, 0] := by
    show _ = _ ↔ _
    rw [Units.ext_iff]
    rfl
  rw [e, conj_w, Matrix.eta_fin_two (g.val.map star)]
  simp [and_assoc]

private theorem eD_apply (hs : s * s = Δ) (g : DX Δ) (i j : Fin 2) :
    (eD hs g).val i j = proj hs ((g : GL (Fin 2) (Lsq K Δ)).val i j) := rfl

private theorem val_eq_gm (hs : s * s = Δ) (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) (g : DX Δ) :
    (g : GL (Fin 2) (Lsq K Δ)).val = gm s Δ (eD hs g).val := by
  obtain ⟨e00, e01, e10, e11⟩ := (mem_DX _).1 g.2
  set M := (g : GL (Fin 2) (Lsq K Δ)).val with hM
  have k := fun x => eq_lf hs h2 h0 x
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  · show M 0 0 = lf s Δ (proj hs (M 0 0)) (proj hs (M 1 1))
    rw [← e00]
    exact k _
  · show M 0 1 = lf s Δ (proj hs (M 0 1)) (-proj hs (M 1 0))
    rw [← map_neg, ← e01]
    exact k _
  · show M 1 0 = lf s Δ (proj hs (M 1 0)) (-proj hs (M 0 1))
    rw [← map_neg, ← e10]
    exact k _
  · show M 1 1 = lf s Δ (proj hs (M 1 1)) (proj hs (M 0 0))
    rw [← e11]
    exact k _

private def gG (hs : s * s = Δ) (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) (h : GL (Fin 2) K) : DX Δ :=
  ⟨GeneralLinearGroup.mk'' (gm s Δ h.val) (by
      rw [det_gm hs h2 h0]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit).map _), (mem_DX _).2
    ⟨star_lf hs h2 h0 _ _, by
      show star (lf s Δ _ _) = -lf s Δ _ _
      rw [star_lf hs h2 h0, ← lf_neg hs h2 h0, neg_neg], by
      show star (lf s Δ _ _) = -lf s Δ _ _
      rw [star_lf hs h2 h0, ← lf_neg hs h2 h0, neg_neg], star_lf hs h2 h0 _ _⟩⟩

private theorem eD_gG (hs : s * s = Δ) (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) (h : GL (Fin 2) K) : eD hs (gG hs h2 h0 h) = h := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [eD_apply]
  fin_cases i <;> fin_cases j <;> exact proj_lf hs h2 h0 _ _

private theorem eD_bij (hs : s * s = Δ) (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) : Function.Bijective (eD hs) :=
  ⟨fun a b e => Subtype.ext (Units.ext (by rw [val_eq_gm hs h2 h0 a, val_eq_gm hs h2 h0 b, e])),
    fun h => ⟨gG hs h2 h0 h, eD_gG hs h2 h0 h⟩⟩

private theorem proj_alg (hs : s * s = Δ) (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) (z : K) : proj hs (algebraMap K (Lsq K Δ) z) = z := by
  rw [proj_apply]
  simp

private theorem isScal_iff (hs : s * s = Δ) (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) (z : Kˣ) (g : DX Δ) :
    IsScal z g ↔ eD hs g = GeneralLinearGroup.scalar (Fin 2) z := by
  have hgm : gm s Δ (Matrix.scalar (Fin 2) (z : K)) = Matrix.scalar (Fin 2) (algebraMap K (Lsq K Δ) (z : K)) := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [gm, lf_self h2]
  have inj : ∀ A B : Matrix (Fin 2) (Fin 2) K, gm s Δ A = gm s Δ B → A = B := by
    intro A B h
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    · simpa [gm, proj_lf hs h2 h0] using congrArg (fun M => proj hs (M 0 0)) h
    · simpa [gm, proj_lf hs h2 h0] using congrArg (fun M => proj hs (M 0 1)) h
    · simpa [gm, proj_lf hs h2 h0] using congrArg (fun M => proj hs (M 1 0)) h
    · simpa [gm, proj_lf hs h2 h0] using congrArg (fun M => proj hs (M 1 1)) h
  have hv : ((GeneralLinearGroup.scalar (Fin 2) z : GL (Fin 2) K) : Matrix _ _ _) = Matrix.scalar (Fin 2) (z : K) := by
    simp
  show ((g : GL (Fin 2) (Lsq K Δ)) : Matrix _ _ _) = Matrix.scalar (Fin 2) (algebraMap K (Lsq K Δ) (z : K)) ↔ _
  rw [val_eq_gm hs h2 h0 g, Units.ext_iff, ← hgm, hv]
  exact ⟨inj _ _, fun h => by rw [h]⟩

private theorem comap_scalar (hs : s * s = Δ) (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) :
    (GeneralLinearGroup.scalar (Fin 2) : Kˣ →* GL (Fin 2) K).range.comap (eD hs) = ZD Δ := by
  ext g
  rw [Subgroup.mem_comap, MonoidHom.mem_range, ZD, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
  refine exists_congr fun z => ?_
  rw [eq_comm, ← isScal_iff hs h2 h0]
  show ((g : GL (Fin 2) (Lsq K Δ)) : Matrix _ _ _) = Matrix.scalar (Fin 2) (algebraMap K (Lsq K Δ) (z : K)) ↔ _
  rw [Units.ext_iff, eq_comm]
  simp

end Alg

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {O : Type} [CommRing O] [Algebra O k] {Δ s : k}

private theorem ints (hO : IsInts k O) : Valuation.Integers (valuation k) O :=
  ⟨hO.inj, fun x => (hO.range _).1 ⟨x, rfl⟩, fun x hx => (hO.range x).2 hx⟩

private theorem alg_tower (x : O) : algebraMap O (Lsq k Δ) x = algebraMap k (Lsq k Δ) (algebraMap O k x) := by
  exact IsScalarTower.algebraMap_apply O k _ x

private theorem isIntegral_lf (hO : IsInts k O) (hs : s * s = Δ) (h2 : (2 : k) ≠ 0) (h0 : s ≠ 0) {p q : k}
    (hp : valuation k p ≤ 1) (hq : valuation k q ≤ 1) : IsIntegral O (lf s Δ p q) := by
  obtain ⟨a, ha⟩ := (hO.range (p + q)).2 ((valuation k).map_add_le hp hq)
  obtain ⟨b, hb⟩ := (hO.range (p * q)).2 (by rw [map_mul]; exact mul_le_one' hp hq)
  have e : lf s Δ p q ^ 2 - algebraMap k (Lsq k Δ) (p + q) * lf s Δ p q + algebraMap k (Lsq k Δ) (p * q) = 0 := by
    rw [← lf_self (s := s) h2, ← lf_self (s := s) h2, sq, lf_mul hs h2 h0, lf_mul hs h2 h0,
      lf_sub hs h2 h0, lf_add hs h2 h0]
    rw [show p * p - (p + q) * p + p * q = 0 by ring, show q * q - (p + q) * q + p * q = 0 by ring, lf_self h2, map_zero]
  refine ⟨Polynomial.X ^ 2 - Polynomial.C a * Polynomial.X + Polynomial.C b, by monicity!, ?_⟩
  rw [← Polynomial.aeval_def]
  simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
  rw [alg_tower a, alg_tower b, ha, hb]
  exact e

private theorem int_of_KO (hO : IsInts k O) (hs : s * s = Δ) (h2 : (2 : k) ≠ 0) (h0 : s ≠ 0) (g : DX Δ)
    (hg : eD hs g ∈ KO k (Fin 2)) (i j : Fin 2) : IsIntegral O ((g : GL (Fin 2) (Lsq k Δ)).val i j) := by
  have hb := GlAx.bd_zero.1 (GlAx.mem_KO.1 hg).1
  have hv : ∀ a b, valuation k ((eD hs g : GL (Fin 2) k) a b) ≤ 1 := fun a b => hb a b
  have hn : ∀ a b, valuation k (-(eD hs g : GL (Fin 2) k) a b) ≤ 1 := fun a b => by
    rw [Valuation.map_neg]
    exact hv a b
  rw [val_eq_gm hs h2 h0 g]
  fin_cases i <;> fin_cases j
  · exact isIntegral_lf hO hs h2 h0 (hv 0 0) (hv 1 1)
  · exact isIntegral_lf hO hs h2 h0 (hv 0 1) (hn 1 0)
  · exact isIntegral_lf hO hs h2 h0 (hv 1 0) (hn 0 1)
  · exact isIntegral_lf hO hs h2 h0 (hv 1 1) (hv 0 0)

private theorem comap_KO (hO : IsInts k O) (hs : s * s = Δ) (h2 : (2 : k) ≠ 0) (h0 : s ≠ 0) :
    (KO k (Fin 2)).comap (eD hs) = KD Δ O := by
  have key : ∀ x : Lsq k Δ, IsIntegral O x → valuation k (proj hs x) ≤ 1 := fun x hx =>
    (ints hO).mem_of_integral (IsIntegral.map_of_comp_eq (RingHom.id O) (proj hs)
      (RingHom.ext fun y => by
        show algebraMap O k y = proj hs (algebraMap O (Lsq k Δ) y)
        rw [alg_tower y, proj_alg hs h2 h0]) hx)
  ext g
  rw [Subgroup.mem_comap, KD, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
  constructor
  · intro hg
    have hg' : eD hs g⁻¹ ∈ KO k (Fin 2) := by
      rw [map_inv]
      exact inv_mem hg
    have I1 := int_of_KO hO hs h2 h0 g hg
    have I2 := int_of_KO hO hs h2 h0 g⁻¹ hg'
    let f : integralClosure O (Lsq k Δ) →+* Lsq k Δ := ((integralClosure O (Lsq k Δ)).val : _ →+* _)
    let A : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq k Δ)) := fun i j => ⟨_, I1 i j⟩
    let B : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq k Δ)) := fun i j => ⟨_, I2 i j⟩
    have hA : A.map f = (g : GL (Fin 2) (Lsq k Δ)).val := Matrix.ext fun _ _ => rfl
    have hB : B.map f = ((g⁻¹ : DX Δ) : GL (Fin 2) (Lsq k Δ)).val := Matrix.ext fun _ _ => rfl
    have finj : Function.Injective (fun M : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq k Δ)) => M.map f) :=
      Matrix.map_injective fun a b hab => Subtype.ext hab
    have hAB : A * B = 1 := finj (by
      simp only
      rw [Matrix.map_mul, hA, hB, Matrix.map_one f (map_zero f) (map_one f), Subgroup.coe_inv, Units.mul_inv])
    have hBA : B * A = 1 := finj (by
      simp only
      rw [Matrix.map_mul, hA, hB, Matrix.map_one f (map_zero f) (map_one f), Subgroup.coe_inv, Units.inv_mul])
    exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩
  · rintro ⟨h, hh⟩
    have hI : ∀ i j, IsIntegral O ((g : GL (Fin 2) (Lsq k Δ)).val i j) := fun i j => by
      rw [← hh]
      exact (h.val i j).2
    have hI' : ∀ i j, IsIntegral O (((g⁻¹ : DX Δ) : GL (Fin 2) (Lsq k Δ)).val i j) := fun i j => by
      rw [Subgroup.coe_inv, ← hh, ← map_inv]
      exact ((h⁻¹).val i j).2
    rw [GlAx.mem_KO, GlAx.bd_zero, GlAx.bd_zero]
    refine ⟨fun i j => key _ (hI i j), fun i j => ?_⟩
    rw [← map_inv]
    exact key _ (hI' i j)

end Loc

end UpperTheory.V.Z.Sym.Sig

theorem UpperTheory.V.Z.Sym.Sig.eD_facts :
    UpperTheory.V.Z.Sym.Sig.ED := by
  intro k _ _ _ _ O _ _ hO h2 Δ s hs h0
  refine ⟨eD_bij hs h2 h0, comap_KO hO hs h2 h0, comap_scalar hs h2 h0, isScal_iff hs h2 h0, fun g => ?_, fun V => ?_⟩
  · show ((g : GL (Fin 2) (Lsq k Δ)).val).det = _ ∧ ((g : GL (Fin 2) (Lsq k Δ)).val).trace = _
    rw [val_eq_gm hs h2 h0 g]
    exact ⟨det_gm hs h2 h0 _, trace_gm hs h2 h0 _⟩
  · rw [Lev.ZJ, ← Subgroup.comap_sup_eq _ _ _ (eD_bij hs h2 h0).2, comap_scalar hs h2 h0]

end
