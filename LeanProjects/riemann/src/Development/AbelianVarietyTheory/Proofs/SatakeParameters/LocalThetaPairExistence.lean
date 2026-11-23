import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

section LatModelAux

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def intMatSub (n n' : ℕ) : AddSubgroup (Matrix (Fin n') (Fin n) L) where
  carrier := {u | ∀ i j, u i j ∈ Formalism.UG.intL L}
  zero_mem' := fun _ _ => (Formalism.UG.intL L).zero_mem
  add_mem' := by
    intro a b ha hb i j
    exact (Formalism.UG.intL L).add_mem (ha i j) (hb i j)
  neg_mem' := by
    intro a ha i j
    exact (Formalism.UG.intL L).neg_mem (ha i j)

theorem mem_intL_iff {x : L} : x ∈ Formalism.UG.intL L ↔ Valued.v x ≤ 1 := Iff.rfl

theorem glint_entry {m : ℕ} {g : GL (Fin m) L} (hg : g ∈ Formalism.UG.GLint (Fin m) (Formalism.UG.intL L)) (i j : Fin m) :
    (g : Matrix (Fin m) (Fin m) L) i j ∈ Formalism.UG.intL L := by
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hg
  exact (k.val i j).2

theorem matMul_int {a b c : ℕ} {A : Matrix (Fin a) (Fin b) L} {B : Matrix (Fin b) (Fin c) L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (hB : ∀ i j, B i j ∈ Formalism.UG.intL L) (i : Fin a) (j : Fin c) :
    (A * B) i j ∈ Formalism.UG.intL L := by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

theorem locH_conj (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (δ : L) (hδ : σ δ = -δ) {n n' : ℕ}
    (JS : GL (Fin n) L) (JT : GL (Fin n') L)
    (hS : ∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i)
    (hT : ∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i)
    (x y : Matrix (Fin n') (Fin n) L) :
    σ (locH σ δ JS JT x y) = - locH σ δ JS JT y x := by
  set P : Matrix (Fin n) (Fin n) L := ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hPdef
  have hSm : (JS : Matrix (Fin n) (Fin n) L).map σ = (JS : Matrix (Fin n) (Fin n) L)ᵀ := by
    ext i j; simp [hS]
  have hTm : (JT : Matrix (Fin n') (Fin n') L).map σ = (JT : Matrix (Fin n') (Fin n') L)ᵀ := by
    ext i j; simp [hT]
  have hPJ : P * (JS : Matrix (Fin n) (Fin n) L) = 1 := by rw [hPdef]; exact JS.inv_mul
  have h1 : P.map σ * (JS : Matrix (Fin n) (Fin n) L)ᵀ = 1 := by
    rw [← hSm, ← Matrix.map_mul, hPJ]; exact Matrix.map_one σ (map_zero σ) (map_one σ)
  have h2 : (JS : Matrix (Fin n) (Fin n) L) * (P.map σ)ᵀ = 1 := by
    have := congrArg Matrix.transpose h1
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have h3 : (P.map σ)ᵀ = P := by
    calc (P.map σ)ᵀ = (P * (JS : Matrix (Fin n) (Fin n) L)) * (P.map σ)ᵀ := by rw [hPJ, Matrix.one_mul]
      _ = P := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  have hPm : P.map σ = Pᵀ := by
    have := congrArg Matrix.transpose h3
    rwa [Matrix.transpose_transpose] at this
  have htr : ∀ A : Matrix (Fin n) (Fin n) L, σ (Matrix.trace A) = Matrix.trace (A.map σ) := by
    intro A; simp [Matrix.trace, map_sum]
  have hyy : (y.map σ).map σ = y := by ext i j; simp [hσ]
  unfold locH
  rw [← hPdef, map_mul, hδ, htr]
  simp only [Matrix.map_mul, hPm, Matrix.transpose_map, hyy, hTm]
  rw [← Matrix.trace_transpose]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [Matrix.mul_assoc P, Matrix.mul_assoc P, Matrix.trace_mul_comm P]
  simp only [Matrix.mul_assoc]
  ring

end LatModelAux

end GlobalTheory.Hk3

namespace GlobalTheory.Hk3

section LatModelAux2

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem locH_sub_right (σ : L →+* L) (δ : L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L)
    (u x y : Matrix (Fin n') (Fin n) L) :
    locH σ δ JS JT u (x - y) = locH σ δ JS JT u x - locH σ δ JS JT u y := by
  have hm : (x - y).map σ = x.map σ - y.map σ := by ext i j; simp
  unfold locH
  rw [hm, Matrix.transpose_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.trace_sub, mul_sub]

theorem int_of_psi {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : Formalism.UG.IsUnramInv ϖ σ q) (ψ : AddChar L ℂ)
    (hne : ∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) (w : L)
    (hw : ∀ b ∈ Formalism.UG.intL L, ψ (b * w + σ (b * w)) = 1) : w ∈ Formalism.UG.intL L := by
  obtain ⟨hσ, hv, hϖ, hvϖ, ⟨x0, hx0, hd⟩, -, -⟩ := hU
  obtain ⟨a0, ha0, hσa, hψa⟩ := hne
  by_contra hwi
  have hwv : 1 < Valued.v w := not_le.mp hwi
  have hw0 : w ≠ 0 := by rintro rfl; simp at hwv
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; simp at hvϖ
  have hd0 : σ x0 - x0 ≠ 0 := by intro h; rw [h] at hd; simp at hd
  have h1 : 1 ≤ Valued.v (ϖ * w) := by
    rw [map_mul, hvϖ]
    obtain ⟨k, hk⟩ := WithZero.ne_zero_iff_exists.mp (zero_lt_one.trans hwv).ne'
    rw [← hk] at hwv ⊢
    rw [← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_le_coe]
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at hwv
    have : (0 : ℤ) < Multiplicative.toAdd k := hwv
    show (0 : ℤ) ≤ -1 + Multiplicative.toAdd k
    omega
  have hinv : (ϖ * w)⁻¹ ∈ Formalism.UG.intL L := by
    rw [mem_intL_iff, map_inv₀]; exact inv_le_one_of_one_le₀ h1
  set e := x0 / (x0 - σ x0) with he
  have hse : e + σ e = 1 := by
    have hd1 : x0 - σ x0 ≠ 0 := by intro h; apply hd0; rw [← neg_sub, h, neg_zero]
    rw [he, map_div₀, map_sub, hσ]
    field_simp
    ring
  have hei : e ∈ Formalism.UG.intL L := by
    rw [mem_intL_iff, he, map_div₀]
    have : Valued.v (x0 - σ x0) = 1 := by rw [← neg_sub, Valuation.map_neg, hd]
    rw [this, div_one]; exact hx0
  set b := e * a0 * (ϖ * w)⁻¹ with hb
  have hbi : b ∈ Formalism.UG.intL L := Subring.mul_mem _ (Subring.mul_mem _ hei ha0) hinv
  have hbw : b * w = e * (ϖ⁻¹ * a0) := by rw [hb]; field_simp
  have key : b * w + σ (b * w) = ϖ⁻¹ * a0 := by
    rw [hbw, map_mul, map_mul, map_inv₀, hϖ, hσa, ← add_mul, hse, one_mul]
  exact hψa (key ▸ hw b hbi)

end LatModelAux2

end GlobalTheory.Hk3

namespace GlobalTheory.Hk3

section LatModelAux3

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem intMat_of_psi {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : Formalism.UG.IsUnramInv ϖ σ q) {δ : L} (hδ : Valued.v δ = 1)
    {n n' : ℕ} {JS : GL (Fin n) L} {JT : GL (Fin n') L}
    (hJS : JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L)) (hJT : JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L))
    (ψ : AddChar L ℂ) (hne : ∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) (z : Matrix (Fin n') (Fin n) L)
    (hz : ∀ u ∈ intMatSub (L := L) n n', ψ (locH σ δ JS JT u z + σ (locH σ δ JS JT u z)) = 1) :
    z ∈ intMatSub (L := L) n n' := by
  intro i j
  have hJTi : (JT⁻¹ : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) := Subgroup.inv_mem _ hJT
  have hw : δ * σ (z i j) ∈ Formalism.UG.intL L := by
    refine int_of_psi hU ψ hne _ (fun b hb => ?_)
    set u : Matrix (Fin n') (Fin n) L := ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Matrix.single i j b *
      (JS : Matrix (Fin n) (Fin n) L) with hu
    have huI : u ∈ intMatSub (L := L) n n' := by
      intro k l
      refine matMul_int (matMul_int (glint_entry hJTi) ?_) (glint_entry hJS) k l
      intro a c
      rw [Matrix.single_apply]
      split_ifs
      · exact hb
      · exact (Formalism.UG.intL L).zero_mem
    have hloc : locH σ δ JS JT u z = b * (δ * σ (z i j)) := by
      unfold locH
      rw [hu]
      have e1 : ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (z.map σ)ᵀ * (JT : Matrix (Fin n') (Fin n') L) *
          (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Matrix.single i j b * (JS : Matrix (Fin n) (Fin n) L)) =
          ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((z.map σ)ᵀ * Matrix.single i j b) * (JS : Matrix (Fin n) (Fin n) L) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (JT : Matrix (Fin n') (Fin n') L), JT.mul_inv, Matrix.one_mul]
      rw [e1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, JS.mul_inv, Matrix.one_mul, Matrix.trace_mul_single]
      simp only [Matrix.transpose_apply, Matrix.map_apply, op_smul_eq_mul]
      ring
    rw [← hloc]
    exact hz u huI
  have hv := hU.2.1
  rw [mem_intL_iff, map_mul, hδ, one_mul, hv] at hw
  exact hw

theorem eig_indep {M : Type} [AddCommGroup M] [Module ℂ M] {ι U : Type} [DecidableEq ι]
    (T : U → Module.End ℂ M) (χ : ι → U → ℂ) (v : ι → M) (hv : ∀ i u, T u (v i) = χ i u • v i)
    (s : Finset ι) (hχ : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∃ u, χ i u ≠ χ j u) :
    ∀ C : ι → ℂ, ∑ i ∈ s, C i • v i = 0 → ∀ i ∈ s, C i • v i = 0 := by
  induction s using Finset.induction_on with
  | empty => intro C _ i hi; simp at hi
  | insert a s ha ih =>
    intro C hC
    rw [Finset.sum_insert ha] at hC
    have hrest : ∀ i ∈ s, C i • v i = 0 := by
      intro i hi
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      obtain ⟨u, hu⟩ := hχ i (Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self a s) hia
      have hS : ∑ k ∈ s, (C k * (χ k u - χ a u)) • v k = 0 := by
        have e1 : T u (∑ k ∈ s, C k • v k) = ∑ k ∈ s, (C k * χ k u) • v k := by
          simp [map_sum, map_smul, hv, smul_smul]
        have e2 : ∑ k ∈ s, C k • v k = -(C a • v a) := eq_neg_of_add_eq_zero_right hC
        have e3 : ∑ k ∈ s, (C k * (χ k u - χ a u)) • v k =
            T u (∑ k ∈ s, C k • v k) - χ a u • ∑ k ∈ s, C k • v k := by
          rw [e1, Finset.smul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [smul_smul, ← sub_smul]; ring_nf
        rw [e3, e2, map_neg, map_smul, hv, smul_smul, smul_neg, smul_smul, mul_comm, sub_self]
      have := ih (fun k hk l hl hkl => hχ k (Finset.mem_insert_of_mem hk) l (Finset.mem_insert_of_mem hl) hkl)
        (fun k => C k * (χ k u - χ a u)) hS i hi
      rw [mul_comm, mul_smul, smul_eq_zero] at this
      exact this.resolve_left (sub_ne_zero.mpr hu)
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [Finset.sum_eq_zero hrest, add_zero] at hC; exact hC
    · exact hrest i hi

end LatModelAux3

end GlobalTheory.Hk3

namespace GlobalTheory.Hk3

theorem locVac_rel_indep : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ c : Matrix (Fin n') (Fin n) L →₀ ℂ, ∀ s, s ≠ 0 → LocVac ρ s → (c.sum fun x z => z • ρ x s) = 0 → ∀ s', LocVac ρ s' → (c.sum fun x z => z • ρ x s') = 0 := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP c s hs hvac hsum s' hvac'
  classical
  obtain ⟨hU, -, hSint, hTint, hS, hT, hδ, -, hpsi_ne, hρ0, hρ, -, -, -⟩ := hP
  have hσ := hU.1
  have hA : ∀ x y : Matrix (Fin n') (Fin n) L, σ (locH σ δ JS JT x y) = - locH σ δ JS JT y x :=
    locH_conj σ hσ δ hδ.2 JS JT hS hT
  have hψinv : ∀ a, ψ a * ψ (-a) = 1 := fun a => by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]

  have hshift : ∀ t, LocVac ρ t → ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ (x + u) t = ψ (-((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2)) • ρ x t := by
    intro t ht x u hu
    have h1 : ρ x t = ψ ((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2) • ρ (x + u) t := by
      have := congrArg (fun f => f t) (hρ x u)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
      rwa [ht u hu] at this
    rw [h1, smul_smul, mul_comm, hψinv, one_smul]

  have heig : ∀ t, LocVac ρ t → ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ u (ρ x t) = ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) • ρ x t := by
    intro t ht x u hu
    have := congrArg (fun f => f t) (hρ u x)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [this, add_comm u x, hshift t ht x u hu, smul_smul, ← AddChar.map_add_eq_mul]
    congr 2
    rw [hA u x, hA x u]; ring

  have hdist : ∀ x y : Matrix (Fin n') (Fin n) L, (∀ u ∈ intMatSub (L := L) n n',
      ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) = ψ (locH σ δ JS JT u y + σ (locH σ δ JS JT u y))) →
      x - y ∈ intMatSub (L := L) n n' := by
    intro x y hxy
    refine intMat_of_psi hU hδ.1 hSint hTint ψ hpsi_ne (x - y) (fun u hu => ?_)
    have e : locH σ δ JS JT u (x - y) + σ (locH σ δ JS JT u (x - y)) =
        (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) + -(locH σ δ JS JT u y + σ (locH σ δ JS JT u y)) := by
      rw [locH_sub_right, map_sub]; ring
    rw [e, AddChar.map_add_eq_mul, hxy u hu, hψinv]

  have hnz : ∀ x, ρ x s ≠ 0 := by
    intro x h0
    have := congrArg (fun f => f s) (hρ (-x) x)
    simp only [Module.End.mul_apply, LinearMap.smul_apply, h0, map_zero, neg_add_cancel, hρ0,
      Module.End.one_apply] at this
    have hne : ψ ((locH σ δ JS JT (-x) x + σ (locH σ δ JS JT (-x) x)) / 2) ≠ 0 := by
      intro h; have := hψinv ((locH σ δ JS JT (-x) x + σ (locH σ δ JS JT (-x) x)) / 2); rw [h, zero_mul] at this
      exact zero_ne_one this
    exact hs ((smul_eq_zero.mp this.symm).resolve_left hne)

  set Λ := intMatSub (L := L) n n' with hΛ
  have hmem : ∀ x : Matrix (Fin n') (Fin n) L, -(QuotientAddGroup.mk x : _ ⧸ Λ).out + x ∈ Λ := by
    intro x
    rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
  set κ : Matrix (Fin n') (Fin n) L → ℂ := fun x =>
    ψ (-((locH σ δ JS JT (QuotientAddGroup.mk x : _ ⧸ Λ).out (-(QuotientAddGroup.mk x : _ ⧸ Λ).out + x) +
      σ (locH σ δ JS JT (QuotientAddGroup.mk x : _ ⧸ Λ).out (-(QuotientAddGroup.mk x : _ ⧸ Λ).out + x))) / 2)) with hκ
  have hdec1 : ∀ t, LocVac ρ t → ∀ x, ρ x t = κ x • ρ (QuotientAddGroup.mk x : _ ⧸ Λ).out t := by
    intro t ht x
    have := hshift t ht (QuotientAddGroup.mk x : _ ⧸ Λ).out _ (hmem x)
    rwa [add_neg_cancel_left] at this
  set I : Finset (Matrix (Fin n') (Fin n) L ⧸ Λ) := c.support.image (fun x => (QuotientAddGroup.mk x : _ ⧸ Λ)) with hI
  set C : (Matrix (Fin n') (Fin n) L ⧸ Λ) → ℂ := fun y =>
    ∑ x ∈ c.support with (QuotientAddGroup.mk x : _ ⧸ Λ) = y, c x * κ x with hC
  have hdec : ∀ t, LocVac ρ t → (c.sum fun x z => z • ρ x t) = ∑ y ∈ I, C y • ρ y.out t := by
    intro t ht
    unfold Finsupp.sum
    have e1 : ∑ x ∈ c.support, c x • ρ x t = ∑ x ∈ c.support, (c x * κ x) • ρ (QuotientAddGroup.mk x : _ ⧸ Λ).out t := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hdec1 t ht x, smul_smul]
    rw [e1, ← Finset.sum_fiberwise_of_maps_to (s := c.support) (t := I) (g := fun x => (QuotientAddGroup.mk x : _ ⧸ Λ))
      (fun x hx => Finset.mem_image_of_mem _ hx)]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hC, Finset.sum_smul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [(Finset.mem_filter.mp hx).2]

  have hC0 : ∀ y ∈ I, C y = 0 := by
    have hind := eig_indep (fun u : Λ => ρ (u : Matrix (Fin n') (Fin n) L))
      (fun (y : Matrix (Fin n') (Fin n) L ⧸ Λ) (u : Λ) =>
        ψ (locH σ δ JS JT (u : Matrix (Fin n') (Fin n) L) y.out + σ (locH σ δ JS JT (u : Matrix (Fin n') (Fin n) L) y.out)))
      (fun y => ρ y.out s) (fun y u => heig s hvac y.out u u.2) I
      (by
        intro y _ y' _ hyy
        by_contra hcon
        push_neg at hcon
        apply hyy
        have hm := hdist y.out y'.out (fun u hu => hcon ⟨u, hu⟩)
        rw [← QuotientAddGroup.out_eq' y, ← QuotientAddGroup.out_eq' y', QuotientAddGroup.eq_iff_sub_mem]
        exact hm)
      C (by rw [← hdec s hvac]; exact hsum)
    intro y hy
    exact (smul_eq_zero.mp (hind y hy)).resolve_right (hnz _)
  rw [hdec s' hvac']
  exact Finset.sum_eq_zero fun y hy => by rw [hC0 y hy, zero_smul]

end GlobalTheory.Hk3
