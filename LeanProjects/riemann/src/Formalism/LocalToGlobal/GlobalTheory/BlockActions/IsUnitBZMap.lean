import Formalism.LocalToGlobal.GlobalTheory.BlockActions.IsUnitALMap

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix NumberField

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem embS_embLLF : embS D D.what₂.embLL = Formalism.L2.Forms.embT D := by
  funext τ
  apply RingHom.ext
  intro x
  show D.what₂.embLL (D.embE (D.host.sigmaOf (D.eTau τ : D.R.GG) x)) =
    D.host.φ₀ (D.host.sigmaOf (D.eTau τ : D.R.GG) x)
  rw [← D.embE_φ₀]
  rfl

theorem pc_rat (Tf : FormsTiedSym D u Ch chOf) (x : Vl D u D.R.m)
    (Pc : (D.mem u).C.cls D.R.m → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) D.what₂.LL)
    (hPc : ∀ c z, (D.fm u).emb D.R.m x c z = fnOf _ (shiftOf (lamT u D.R.m)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))
      ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY z)) (c' : (D.mem u).C.cls D.R.m) :
    MvPolynomial.map D.what₂.embLL (Pc c') ∈ RatSpan D ((D.fm u).lam D.R.m) := by
  obtain ⟨⟨oN, -⟩, -⟩ := framesAt D u Ch chOf Tf D.what₂.embLL
  rw [embS_embLLF] at oN
  have hx := ((Tf.val D.R.m le_rfl (Or.inr rfl)).rat ((D.fm u).emb D.R.m x)).1 ⟨x, rfl⟩
  obtain ⟨P1, hP1, hP1z⟩ := hx.2 c'
  have hP1e : P1 = MvPolynomial.map D.what₂.embLL (Pc c') := by
    apply Formalism.L2.Col.fnOf_injective _ _ 1 (fun τ => by simp) oN
    funext y
    obtain ⟨z, rfl⟩ := (Tf.val D.R.m le_rfl (Or.inr rfl)).eY.surjective y
    rw [← hP1z, hPc]
  rw [← hP1e]
  exact hP1

theorem isUnit_bZ_map (Tf : FormsTiedSym D u Ch chOf) (τ : D.what₂.Tau) :
    IsUnit ((bZ u Tf.til.z0).map (Formalism.L2.Forms.embT D τ)).det := by
  have := (bZ_isUnitS Tf).map (Formalism.L2.Forms.embT D τ)
  rw [RingHom.map_det] at this
  exact this

set_option maxHeartbeats 1000000 in

theorem base_eq (Tf : FormsTiedSym D u Ch chOf) (hL : Formalism.L2.Rows.LowerMapTieS Tf) (h : (D.fm u).PRat) (x : Vl D u D.R.m)
    (Pc : (D.mem u).C.cls D.R.m → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) D.what₂.LL)
    (hPc : ∀ c z, (D.fm u).emb D.R.m x c z = fnOf _ (shiftOf (lamT u D.R.m)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))
      ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY z))
    (Qc : (D.fm u).clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) D.what₂.LL)
    (hQc : ∀ c, Tf.valP.eW ((D.fm u).ptEmb ((D.fm u).PtL h x)) c =
      fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL (Qc c))) (c : (D.fm u).clsP) :
    MvPolynomial.map D.what₂.embLL (Qc c) =
      ((((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi (Tf.tilAd.ka c) : ℂˣ) : ℂ))⁻¹ •
        MvPolynomial.map D.what₂.embLL (brTenL D u (PL Tf c (Pc ((D.fm u).til c)))) := by
  classical
  have hB := bZ_isUnitS Tf
  have hmZ := mZ_isUnit hB
  obtain ⟨-, ⟨oP, -⟩⟩ := framesAt D u Ch chOf Tf D.what₂.embLL
  rw [embS_embLLF] at oP
  have hP0 : MvPolynomial.map D.what₂.embLL (Pc ((D.fm u).til c)) ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m) :=
    map_mem_CSpan_of_rat _ _ (pc_rat Tf x Pc hPc _) D.what₂.embLL
  let ginv : GL (Fin (D.R.N D.R.m)) D.host.E := ((Tf.til.ga c).1)⁻¹
  let M' : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ := atInf (Formalism.L2.Forms.embT D) (ginv : Matrix _ _ D.host.E)
  let A0 : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ := fun τ => M' τ * (mZ u Tf.til.z0 τ)⁻¹
  have hA0 : ∀ τ, (AL Tf c τ).map D.what₂.embLL = A0 τ := by
    intro τ
    rw [AL_map, embS_embLLF]
    show ((ginv : Matrix _ _ D.host.E) * bZ u Tf.til.z0).map (Formalism.L2.Forms.embT D τ) =
      (ginv : Matrix _ _ D.host.E).map (Formalism.L2.Forms.embT D τ) * (((bZ u Tf.til.z0)⁻¹).map (Formalism.L2.Forms.embT D τ))⁻¹
    rw [Matrix.map_mul, Formalism.L2.Col.map_inv_matrix, Matrix.nonsing_inv_nonsing_inv _ (isUnit_bZ_map Tf τ)]
  have hA0u : ∀ τ, IsUnit (A0 τ).det := fun τ => by rw [← hA0]; exact isUnit_AL_map Tf c _ τ
  have hmapPL : MvPolynomial.map D.what₂.embLL (PL Tf c (Pc ((D.fm u).til c))) =
      (∏ τ, (A0 τ).det ^ shiftOf (lamT u D.R.m) τ) • blkRow A0 (MvPolynomial.map D.what₂.embLL (Pc ((D.fm u).til c))) := by
    rw [map_PL]
    simp only [hA0]
  set χ : ℂ := ((((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi (Tf.tilAd.ka c) : ℂˣ) : ℂ)) with hχ
  have hPbmem : χ⁻¹ • MvPolynomial.map D.what₂.embLL (PL Tf c (Pc ((D.fm u).til c))) ∈
      Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m) := by
    rw [hmapPL]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (blkRow_mem_CSpan _ A0 hA0u _ hP0))
  have hPb : ∀ s, Tf.eWz ((D.mem u).P.evz ((D.fm u).emb D.R.m x)) c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) (χ⁻¹ • MvPolynomial.map D.what₂.embLL (PL Tf c (Pc ((D.fm u).til c))))
        ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s) := by
    intro s
    rw [Tf.evz ((D.fm u).emb D.R.m x) c s ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY.symm
      (((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s).tr M' (isUnit_det_atInf (Formalism.L2.Forms.embT D) ginv)))]
    · rw [hPc, Equiv.apply_symm_apply, fnOf_trG]
      have e1 : (fun τ => (1 : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ) τ * M' τ) = M' :=
        funext fun τ => by simp
      rw [e1, fnOf_change _ _ (mZ u Tf.til.z0) M' hmZ, hmapPL]
      simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, Units.val_inv_eq_inv_val]
      rfl
    · intro τ
      simp only [Equiv.apply_symm_apply]
      show ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s).1 τ =
        atInf (Formalism.L2.Forms.embT D) (Tf.til.ga c).1.1 τ * (M' τ * ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s).1 τ)
      rw [← Matrix.mul_assoc, atInf_mul_inv, Matrix.one_mul]
  have h3 := hL hB ((D.mem u).P.evz ((D.fm u).emb D.R.m x)) c _ hPbmem hPb
  have h4 : fnOf (gramC (gramP D) (Formalism.L2.Forms.embT D)) (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL (Qc c)) =
      fnOf (gramC (gramP D) (Formalism.L2.Forms.embT D)) (shiftOf (sgT u)) 1 (Formalism.L2.Ker.brTen D u (χ⁻¹ • MvPolynomial.map D.what₂.embLL (PL Tf c (Pc ((D.fm u).til c))))) := by
    rw [← hQc c, (D.fm u).PtL_spec h x, h3]
  have h5 := Formalism.L2.Col.fnOf_injective _ _ 1 (fun τ => by simp) oP h4
  rw [h5, map_smul, map_brTenL]

end Formalism.L2.GlobalTheoryTheory.Br
