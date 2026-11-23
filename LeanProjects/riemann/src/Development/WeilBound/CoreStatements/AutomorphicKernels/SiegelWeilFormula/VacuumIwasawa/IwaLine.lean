import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.ParabolicThetaScalar
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.SiegelMultOf

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Avac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace LineFix

theorem good (d : SD σ) : (PositivityTheory.RgEis.adCM σ d.χ).Good :=
  PositivityTheory.RgEis.Hd.cmGood_of PositivityTheory.RgEis.Hd.stdGood PositivityTheory.RgEis.Hd.dict PositivityTheory.RgEis.Hd.dictInf F E σ d.χ d.m
    d.ok.good.cm d.ok.good.unram d.ok.hecke d.ok.res

theorem cc (d : SD σ) (x : AE F E) : cA σ (cA σ x) = x := (good d).σσ x

theorem frame_eps (d : SD σ) : ∃ ε : ℤˣ, (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) =
    Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E))) 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  refine ⟨ε, ?_⟩
  have e1 : (incM F d.b.1).map (cA σ) = incM F (d.b.1.map σ) := by
    ext i j
    simp [incM, cA, inclR, Algebra.TensorProduct.map_tmul]
  have e2 : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
    simp [dbl, incM, Matrix.fromBlocks_map, Matrix.map_neg]
  have key : incM F (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ) =
      (incM F d.b.1)ᵀ * incM F (dbl d.Y.J) * incM F (d.b.1.map σ) := by
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  rw [e1, e2, ← key, hε]
  ext (i|i) (j|j) <;> simp [incM, Matrix.fromBlocks_map, Matrix.one_apply] <;> split_ifs <;> simp

variable {n : ℕ}

def Dk (κ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E) :=
  (((κ⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ))ᵀ

def Nk (κ : GL (Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) :=
  Matrix.fromBlocks (κ : Matrix (Fin n) (Fin n) (AE F E)) 0 0 (Dk (σ := σ) κ)

theorem val_mul_inv (κ : GL (Fin n) (AE F E)) :
    (κ : Matrix (Fin n) (Fin n) (AE F E)) * ((κ⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem val_inv_mul (κ : GL (Fin n) (AE F E)) :
    ((κ⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * (κ : Matrix (Fin n) (Fin n) (AE F E)) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem mapc_mul (X Y : Matrix (Fin n) (Fin n) (AE F E)) : (X * Y).map (cA σ) = X.map (cA σ) * Y.map (cA σ) := by
  rw [← AlgHom.mapMatrix_apply, ← AlgHom.mapMatrix_apply, ← AlgHom.mapMatrix_apply, map_mul]

theorem mapc_one : (1 : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) = 1 := by
  rw [← AlgHom.mapMatrix_apply, map_one]

theorem Dk_mul_inv (κ : GL (Fin n) (AE F E)) : Dk (σ := σ) κ * Dk (σ := σ) κ⁻¹ = 1 := by
  simp only [Dk, inv_inv]
  rw [← Matrix.transpose_mul, ← mapc_mul, val_mul_inv, mapc_one, Matrix.transpose_one]

theorem Nk_mul_inv (κ : GL (Fin n) (AE F E)) : Nk (σ := σ) κ * Nk (σ := σ) κ⁻¹ = 1 := by
  simp only [Nk, Matrix.fromBlocks_multiply, val_mul_inv, Dk_mul_inv, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Matrix.fromBlocks_one]

theorem Nk_form (hc : ∀ x : AE F E, cA σ (cA σ x) = x) (e : AE F E) (κ : GL (Fin n) (AE F E)) :
    (Nk (σ := σ) κ)ᵀ * Matrix.fromBlocks 0 1 (e • (1 : Matrix (Fin n) (Fin n) (AE F E))) 0 * (Nk (σ := σ) κ).map (cA σ) =
      Matrix.fromBlocks 0 1 (e • (1 : Matrix (Fin n) (Fin n) (AE F E))) 0 := by
  have hDc : (Dk (σ := σ) κ).map (cA σ) = ((κ⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))ᵀ := by
    ext i j
    simp [Dk, hc]
  have hDt : (Dk (σ := σ) κ)ᵀ = ((κ⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) := by
    simp [Dk]
  simp only [Nk, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_zero,
    Matrix.map_zero _ (map_zero (cA σ)), Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, hDc, hDt]
  rw [← Matrix.transpose_mul, val_inv_mul, Matrix.transpose_one, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    ← mapc_mul, val_inv_mul, mapc_one]

section Unit

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem transpose_mem_unitaryGroup_vacuum_iwasawa {U : Matrix ι ι ℂ} (h : U ∈ Matrix.unitaryGroup ι ℂ) : Uᵀ ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h2 := Matrix.mem_unitaryGroup_iff'.1 h
  rw [Matrix.star_eq_conjTranspose] at h2 ⊢
  have e : (Uᵀ)ᴴ = (Uᴴ)ᵀ := by ext i j; simp
  rw [e, ← Matrix.transpose_mul, h2, Matrix.transpose_one]

theorem blk_unit {P Q : Matrix ι ι ℂ} (hP : P ∈ Matrix.unitaryGroup ι ℂ) (hQ : Q ∈ Matrix.unitaryGroup ι ℂ) :
    Matrix.fromBlocks P 0 0 Q * (Matrix.fromBlocks P 0 0 Q)ᴴ = 1 := by
  have hP' : P * Pᴴ = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.1 hP
  have hQ' : Q * Qᴴ = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.1 hQ
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp [hP', hQ', Matrix.fromBlocks_one]

end Unit

variable (d : SD σ)

theorem mL_mem (κ : GL (Fin d.n) (AE F E)) :
    (incM F d.b.1 * Nk (σ := σ) κ * incM F (d.b⁻¹).1)ᵀ * dbl (incM F d.Y.J) *
      (incM F d.b.1 * Nk (σ := σ) κ * incM F (d.b⁻¹).1).map (cA σ) = dbl (incM F d.Y.J) := by
  obtain ⟨ε, hε⟩ := frame_eps d
  have hN := Nk_form (σ := σ) (cc d) ((ε : ℤ) : AE F E) κ
  rw [← hε] at hN
  exact KWhit.form_conj_out (cA σ).toRingHom (KWhit.incM_mul_inv d) hN

theorem mL_mul (κ : GL (Fin d.n) (AE F E)) :
    (incM F d.b.1 * Nk (σ := σ) κ * incM F (d.b⁻¹).1) * (incM F d.b.1 * Nk (σ := σ) κ⁻¹ * incM F (d.b⁻¹).1) = 1 := by
  calc _ = incM F d.b.1 * Nk (σ := σ) κ * (incM F (d.b⁻¹).1 * incM F d.b.1) * Nk (σ := σ) κ⁻¹ * incM F (d.b⁻¹).1 := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [KWhit.incM_inv_mul d, Matrix.mul_one, Matrix.mul_assoc (incM F d.b.1), Nk_mul_inv, Matrix.mul_one,
          KWhit.incM_mul_inv d]

def mL (κ : GL (Fin d.n) (AE F E)) : d.G :=
  ⟨⟨incM F d.b.1 * Nk (σ := σ) κ * incM F (d.b⁻¹).1, incM F d.b.1 * Nk (σ := σ) κ⁻¹ * incM F (d.b⁻¹).1, mL_mul d κ,
    by simpa using mL_mul d κ⁻¹⟩, by
    show (incM F d.b.1 * Nk (σ := σ) κ * incM F (d.b⁻¹).1)ᵀ * dbl (incM F d.Y.J) *
      (incM F d.b.1 * Nk (σ := σ) κ * incM F (d.b⁻¹).1).map (cA σ) = dbl (incM F d.Y.J)
    exact mL_mem d κ⟩

theorem inFrame_mL (κ : GL (Fin d.n) (AE F E)) : inFrame d.b (mL d κ) = Nk (σ := σ) κ := by
  show incM F (d.b⁻¹).1 * (incM F d.b.1 * Nk (σ := σ) κ * incM F (d.b⁻¹).1) * incM F d.b.1 = Nk (σ := σ) κ
  simp only [← Matrix.mul_assoc, KWhit.incM_inv_mul d, Matrix.one_mul]
  rw [Matrix.mul_assoc, KWhit.incM_inv_mul d, Matrix.mul_one]

theorem mL_inv (κ : GL (Fin d.n) (AE F E)) : mL d κ⁻¹ = (mL d κ)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  apply KWhit.inFrame_injective d
  rw [KWhit.inFrame_mul, inFrame_mL, inFrame_mL, Nk_mul_inv, inFrame_one]

theorem O_int {z : AE F E} (hz : z ∈ (PositivityTheory.RgEis.adCM σ d.χ).O) : finOne F • z ∈ intHat F E :=
  ((PositivityTheory.RgEis.Hd.dict F E).2.2.2.1 z).1 hz

theorem Nk_int {κ : GL (Fin d.n) (AE F E)} (hκ : κ ∈ (PositivityTheory.RgEis.adCM σ d.χ).kGL (Fin d.n)) (i j : Fin d.n ⊕ Fin d.n) :
    finOne F • Nk (σ := σ) κ i j ∈ intHat F E := by
  have hκ' := hκ.1
  rcases i with i | i <;> rcases j with j | j
  · exact O_int d (hκ' i j).1
  · simp [Nk, (intHat F E).zero_mem]
  · simp [Nk, (intHat F E).zero_mem]
  · exact O_int d ((good d).σO _ (hκ' j i).2)

theorem Nk_unit {κ : GL (Fin d.n) (AE F E)} (hκ : κ ∈ (PositivityTheory.RgEis.adCM σ d.χ).kGL (Fin d.n)) (w : InfinitePlace F) :
    (Nk (σ := σ) κ).map (piInf (d.B.emb w)) * ((Nk (σ := σ) κ).map (piInf (d.B.emb w)))ᴴ = 1 := by
  obtain ⟨w', hw'⟩ := ((PositivityTheory.RgEis.Hd.dictInf F E σ d.ok.good.cm).2 d.B.emb).1 w
  set g := (PositivityTheory.RgEis.adCM σ d.χ).φ w' with hg
  have hU : (κ : Matrix (Fin d.n) (Fin d.n) (AE F E)).map g ∈ Matrix.unitaryGroup (Fin d.n) ℂ := hκ.2 w'
  have hV : ((κ⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)).map g ∈
      Matrix.unitaryGroup (Fin d.n) ℂ := (inv_mem hκ).2 w'
  have hσφ : ∀ z, g (cA σ z) = (starRingEnd ℂ) (g z) := fun z => (good d).σφ w' z
  rcases hw' with hf | hf
  · have hf' : ∀ z, piInf (d.B.emb w) z = g z := hf
    have e : (Nk (σ := σ) κ).map (piInf (d.B.emb w)) = Matrix.fromBlocks ((κ : Matrix (Fin d.n) (Fin d.n) (AE F E)).map g) 0 0
        (star (((κ⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)).map g)) := by
      ext (i | i) (j | j) <;> simp [Nk, Dk, hf', hσφ, Matrix.star_apply]
    rw [e]
    exact blk_unit hU (Unitary.star_mem hV)
  · have hf' : ∀ z, piInf (d.B.emb w) z = (starRingEnd ℂ) (g z) := hf
    have e : (Nk (σ := σ) κ).map (piInf (d.B.emb w)) = Matrix.fromBlocks (star ((κ : Matrix (Fin d.n) (Fin d.n) (AE F E)).map g))ᵀ 0 0
        ((((κ⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)).map g))ᵀ := by
      ext (i | i) (j | j) <;> simp [Nk, Dk, hf', hσφ, Matrix.star_apply]
    rw [e]
    exact blk_unit (transpose_mem_unitaryGroup_vacuum_iwasawa (Unitary.star_mem hU)) (transpose_mem_unitaryGroup_vacuum_iwasawa hV)

theorem mL_mem_K {κ : GL (Fin d.n) (AE F E)} (hκ : κ ∈ (PositivityTheory.RgEis.adCM σ d.χ).kGL (Fin d.n)) : mL d κ ∈ d.K := by
  refine (d.ok.stdK _).2 ⟨fun w => ?_, fun k' hk' i j => ?_⟩
  · rw [inFrame_mL]; exact Nk_unit d hκ w
  · rcases hk' with rfl | hk'
    · rw [inFrame_mL]; exact Nk_int d hκ i j
    · rw [Set.mem_singleton_iff] at hk'
      subst hk'
      rw [← mL_inv, inFrame_mL]
      exact Nk_int d (inv_mem hκ) i j

end LineFix

theorem line_fix' {d : SD σ} (i₀ : Fin d.n) (x : d.G) : ∃ (p k : d.G) (lam : (AE F E)ˣ), k ∈ d.K ∧ x = p * k ∧
    ∀ a, inFrame d.b p a (Sum.inl i₀) = if a = Sum.inl i₀ then (lam : AE F E) else 0 := by
  obtain ⟨p0, t, hp, k1, hk1, rfl⟩ := d.ok.hgt.iwa x
  have h21 := KWhit.parabolic_lower_block_zero d p0 t hp
  obtain ⟨-, -, A, -, -, -, hA, -, -⟩ := par_frame d p0 h21
  obtain ⟨a1, ha1, κ, hκ, hAe⟩ := (LineFix.good d).iwa (Fin d.n) {i₀} A
  have hs : ∀ r, r ≠ i₀ → (a1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) r i₀ = 0 ∧
      ((a1⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)) r i₀ = 0 :=
    fun r hr => ha1 r (by simpa using hr) i₀ rfl
  have hunit : (a1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) i₀ i₀ *
      ((a1⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)) i₀ i₀ = 1 := by
    have := congrFun (congrFun (LineFix.val_mul_inv a1) i₀) i₀
    rw [Matrix.mul_apply, Finset.sum_eq_single i₀ (fun r _ hr => by rw [(hs r hr).2, mul_zero]) (by simp),
      Matrix.one_apply_eq] at this
    exact this
  refine ⟨p0 * (LineFix.mL d κ)⁻¹, LineFix.mL d κ * k1, Units.mkOfMulEqOne _ _ hunit,
    d.K.mul_mem (LineFix.mL_mem_K d hκ) hk1, by group, fun a => ?_⟩
  have hMb : inFrame d.b p0 = Matrix.fromBlocks (A : Matrix (Fin d.n) (Fin d.n) (AE F E)) (inFrame d.b p0).toBlocks₁₂ 0
      (inFrame d.b p0).toBlocks₂₂ := by
    rw [hA, ← h21, Matrix.fromBlocks_toBlocks]
  have hAk : (A : Matrix (Fin d.n) (Fin d.n) (AE F E)) * ((κ⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)) =
      a1 := by
    rw [hAe, Units.val_mul, Matrix.mul_assoc, LineFix.val_mul_inv, Matrix.mul_one]
  rw [KWhit.inFrame_mul, ← LineFix.mL_inv, LineFix.inFrame_mL, hMb]
  rcases a with r | r
  · simp only [LineFix.Nk, Matrix.fromBlocks_multiply, Matrix.mul_zero, add_zero, Matrix.fromBlocks_apply₁₁, hAk]
    by_cases hr : r = i₀
    · subst hr; simp
    · rw [(hs r hr).1]; simp [hr]
  · simp [LineFix.Nk, Matrix.fromBlocks_multiply]

end PositivityTheory.SiegelWeilFormula.Avac

end
