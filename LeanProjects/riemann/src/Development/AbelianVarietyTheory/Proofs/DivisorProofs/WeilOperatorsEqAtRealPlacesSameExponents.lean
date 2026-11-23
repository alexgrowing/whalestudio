import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DownRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicWeilRepSchrodingerModelUnique

noncomputable section

namespace GlobalTheory.ArchWeil

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

section Idem

variable {R : Type} [CommRing R] (e : R) {ι : Type} [Fintype ι] [DecidableEq ι]

def cut (m : Matrix ι ι R) : Matrix ι ι R := e • m + (1 - e) • 1

omit [Fintype ι] in
theorem cut_one : cut e (1 : Matrix ι ι R) = 1 := by
  simp only [cut, ← add_smul, add_sub_cancel, one_smul]

omit [Fintype ι] in
theorem cut_transpose (x : Matrix ι ι R) : (cut e x)ᵀ = cut e xᵀ := by
  simp [cut, Matrix.transpose_add, Matrix.transpose_smul]

theorem cut_mul_right {κ : Type} (x : Matrix ι ι R) (D : Matrix ι κ R) : cut e x * D = e • (x * D) + (1 - e) • D := by
  simp [cut, Matrix.add_mul, Matrix.smul_mul]

omit [Fintype ι] [DecidableEq ι] in
theorem mul_cut {κ : Type} [Fintype κ] [DecidableEq κ] (D : Matrix ι κ R) (t : Matrix κ κ R) :
    D * cut e t = e • (D * t) + (1 - e) • D := by
  simp [cut, Matrix.mul_add, Matrix.mul_smul]

omit [DecidableEq ι] in
theorem cut_mul_eq {κ : Type} [Fintype κ] [DecidableEq κ] [DecidableEq ι] {x : Matrix ι ι R} {D : Matrix ι κ R}
    {t : Matrix κ κ R} (h : x * D = D * t) : cut e x * D = D * cut e t := by
  rw [cut_mul_right, mul_cut, h]

variable {e} (he : e * e = e)
include he

theorem cut_mul_mul {κ : Type} [Fintype κ] [DecidableEq κ] (x : Matrix ι ι R) (J : Matrix ι κ R) (y : Matrix κ κ R) :
    cut e x * J * cut e y = e • (x * J * y) + (1 - e) • J := by
  have h1 : e * (1 - e) = 0 := by linear_combination -he
  have h2 : (1 - e) * e = 0 := by linear_combination -he
  have h3 : (1 - e) * (1 - e) = 1 - e := by linear_combination he
  simp only [cut, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul, he, h1, h2, h3, zero_smul, zero_smul, add_zero,
    zero_add]

theorem cut_mul (x y : Matrix ι ι R) : cut e (x * y) = cut e x * cut e y := by
  rw [← Matrix.mul_one (cut e x), cut_mul_mul he, Matrix.mul_one]; rfl

theorem det_cut (x : Matrix ι ι R) : (cut e x).det = e * x.det + (1 - e) := by
  have h1 : e * (1 - e) = 0 := by linear_combination -he
  have h3 : (1 - e) * (1 - e) = 1 - e := by linear_combination he
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Matrix.det_isEmpty]
  have hpow : ∀ f : R, f * f = f → f ^ Fintype.card ι = f := fun f hf => by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := ι))
    rw [hk]
    exact IsIdempotentElem.pow_succ_eq k hf
  have ea : e • cut e x = e • x := by
    simp only [cut, smul_add, smul_smul, he, h1, zero_smul, add_zero]
  have eb : (1 - e) • cut e x = (1 - e) • (1 : Matrix ι ι R) := by
    have h2 : (1 - e) * e = 0 := by linear_combination -he
    simp only [cut, smul_add, smul_smul, h2, h3, zero_smul, zero_add]
  have da := congrArg Matrix.det ea
  have db := congrArg Matrix.det eb
  rw [Matrix.det_smul, Matrix.det_smul, hpow e he] at da
  rw [Matrix.det_smul, Matrix.det_smul, hpow _ h3, Matrix.det_one, mul_one] at db
  linear_combination da + db

def cutHom : Matrix ι ι R →* Matrix ι ι R where
  toFun := cut e
  map_one' := cut_one e
  map_mul' := cut_mul he

def cutGL : GL ι R →* GL ι R := Units.map (cutHom he)

theorem cutGL_val (g : GL ι R) : ((cutGL he g : GL ι R) : Matrix ι ι R) = cut e (g : Matrix ι ι R) := rfl

omit he [Fintype ι] in
theorem cut_map {R₀ : Type} [CommRing R₀] [Algebra R₀ R] (c : R →ₐ[R₀] R) (hce : c e = e) (x : Matrix ι ι R) :
    (cut e x).map c = cut e (x.map c) := by
  ext i j
  simp only [cut, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  split_ifs <;> simp [hce]

def cutUG {R₀ : Type} [CommRing R₀] [Algebra R₀ R] (c : R →ₐ[R₀] R) (hce : c e = e) (J : Matrix ι ι R) :
    UG c J →* UG c J :=
  ((cutGL he).comp (UG c J).subtype).codRestrict (UG c J) fun g => by
    show (cut e ((g : GL ι R) : Matrix ι ι R))ᵀ * J * (cut e ((g : GL ι R) : Matrix ι ι R)).map c = J
    rw [cut_transpose, cut_map c hce, cut_mul_mul he, g.2]
    simp only [← add_smul, add_sub_cancel, one_smul]

theorem cutUG_val {R₀ : Type} [CommRing R₀] [Algebra R₀ R] (c : R →ₐ[R₀] R) (hce : c e = e) (J : Matrix ι ι R)
    (g : UG c J) : (((cutUG he c hce J g : UG c J) : GL ι R) : Matrix ι ι R) = cut e ((g : GL ι R) : Matrix ι ι R) := rfl

theorem continuous_cutUG [TopologicalSpace R] [IsTopologicalRing R] {R₀ : Type} [CommRing R₀] [Algebra R₀ R]
    (c : R →ₐ[R₀] R) (hce : c e = e) (J : Matrix ι ι R) : Continuous (cutUG he c hce J) := by
  have hcut : Continuous (cut e : Matrix ι ι R → Matrix ι ι R) :=
    (continuous_const_smul e).add continuous_const
  have hGL : Continuous (cutGL he : GL ι R → GL ι R) := by
    refine Units.continuous_iff.2 ⟨hcut.comp Units.continuous_val, ?_⟩
    have : (fun g : GL ι R => (((cutGL he g)⁻¹ : GL ι R) : Matrix ι ι R)) = fun g => cut e ((g⁻¹ : GL ι R) : Matrix ι ι R) :=
      funext fun g => by rw [← map_inv]; rfl
    rw [this]
    exact hcut.comp Units.continuous_coe_inv
  exact (hGL.comp continuous_subtype_val).subtype_mk _

end Idem

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F) in

def eInf : AF F := LinearMap.inl F (Ainf F) (Af F) 1

theorem eInf_mul_self : eInf F * eInf F = eInf F :=
  Prod.ext (mul_one _) (mul_zero _)

theorem mul_eInf_of_evI {u : AF F} (hu : evI F u = 0) : u * eInf F = 0 := by
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  exact Prod.ext (by show u.1 * 1 = 0; rw [h1, mul_one]) (mul_zero _)

theorem evI_one_sub_eInf : evI F (1 - eInf F) = 0 := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F (1 - (eInf F).1) = 0
  rw [show (eInf F).1 = 1 from rfl, sub_self, map_zero]

variable (F E) in

def eE : AE F E := algebraMap (AF F) (AE F E) (eInf F)

theorem eE_mul_self : eE F E * eE F E = eE F E := by rw [eE, ← map_mul, eInf_mul_self]

theorem cA_eE (σ : E →ₐ[F] E) : cA σ (eE F E) = eE F E := (cA σ).commutes _

local instance topRingAE : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)

theorem at_eE_mul (x : AE F E) : At (evI F) (eE F E * x) := fun u hu => by
  rw [Algebra.smul_def, eE, ← mul_assoc, ← map_mul, mul_eInf_of_evI hu, map_zero, zero_mul]

theorem cut_eq_of_at {ι : Type} [Fintype ι] [DecidableEq ι] (m : Matrix ι ι (AE F E)) (hm : At (evI F) (m - 1)) :
    cut (eE F E) m = m := by
  have h := hm _ evI_one_sub_eInf
  have h' : (1 - eE F E) • (m - 1) = 0 := by
    rw [eE, ← map_one (algebraMap (AF F) (AE F E)), ← map_sub, algebraMap_smul]; exact h
  rw [smul_sub] at h'
  calc cut (eE F E) m = eE F E • m + (1 - eE F E) • m := by rw [cut, sub_eq_zero.mp h']
    _ = m := by rw [← add_smul, add_sub_cancel, one_smul]

theorem at_fromBlocks_one {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (m : Matrix ι ι (AE F E)) (hm : At (evI F) (m - 1)) :
    At (evI F) (Matrix.fromBlocks m 0 0 (1 : Matrix κ κ (AE F E)) - 1) := fun u hu => by
  have h := hm u hu
  rw [← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add, Matrix.fromBlocks_smul,
    ← sub_eq_add_neg, h]
  simp

theorem at_det_cut {ι : Type} [Fintype ι] [DecidableEq ι] (m : Matrix ι ι (AE F E)) :
    At (evI F) ((cut (eE F E) m).det - 1) := by
  rw [det_cut eE_mul_self, show eE F E * m.det + (1 - eE F E) - 1 = eE F E * (m.det - 1) by ring]
  exact at_eE_mul _

abbrev archUG (σ : E →ₐ[F] E) {ι : Type} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι (AE F E)) : UG (cA σ) J →* UG (cA σ) J :=
  cutUG eE_mul_self (cA σ) (cA_eE σ) J

theorem continuous_archUG (σ : E →ₐ[F] E) {ι : Type} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι (AE F E)) :
    Continuous (archUG σ J) := continuous_cutUG eE_mul_self (cA σ) (cA_eE σ) J

open GlobalTheory.WeilSchUnique in

theorem member_eq_of_arch (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {a b : ℕ} (JA : Matrix (Fin a) (Fin a) E)
    (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ) (hJ : ∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) (hdet : JB.det ≠ 0)
    (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ]
    (d : Darboux (symp (cA σ) (-1) (incM F JA) (incM F JB)) κ) (χ χ₁ : Chr F E)
    (hχ : ∀ z : (AE F E)ˣ, At (evI F) ((z : AE F E) - 1) → χ₁ z = χ z)
    (om om₁ : UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ))
    (h : IsUWeilB (cA σ) (adeleClass F) ψ (-1) (incM F JA) (incM F JB) d χ om)
    (h₁ : IsUWeilB (cA σ) (adeleClass F) ψ (-1) (incM F JA) (incM F JB) d χ₁ om₁) :
    ∀ g : UG (cA σ) (incM F JB), At (evI F) (((g : GL (Fin b) (AE F E)) : Matrix (Fin b) (Fin b) (AE F E)) - 1) →
      ∀ Φ ∈ schA F κ, om g Φ = om₁ g Φ := by
  obtain ⟨-, dd, omd, hdd, ⟨-, hS, hR⟩, hres⟩ := h
  obtain ⟨-, dd₁, omd₁, hdd₁, ⟨-, hS₁, hR₁⟩, hres₁⟩ := h₁
  have hee : ∀ w, dd₁.e w = dd.e w := fun w => by
    rw [← Matrix.fromCols_toCols w, hdd, hdd₁]
  have hrho : ∀ w, dd₁.rho ψ w = dd.rho ψ w := fun w => by simp only [Darboux.rho, hee]
  have inv_mul : ∀ (p : UG (cA σ) (dbl (incM F JB))) φ, omd p (omd p⁻¹ φ) = φ := fun p φ => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨φz, hφz, hφz0⟩ := GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F (κ ⊕ κ)
  have key : ∀ p, ∃ c : ℂ, ∀ φ ∈ schA F (κ ⊕ κ), omd₁ p φ = c • omd p φ := fun p => by
    obtain ⟨c, hc⟩ := scalar_of_commute ψ hψ (omd p⁻¹ * omd₁ p)
      (fun l hl => by
        rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc]
        exact hS₁.adm p _ (hS.adm p⁻¹ l hl))
      (fun w φ hφ => by
        obtain ⟨w', rfl⟩ := dd.e.surjective w
        have e1 : schr ψ (dd.e w') = dd.rho ψ w' := rfl
        rw [e1, Module.End.mul_apply, Module.End.mul_apply]
        calc omd p⁻¹ (omd₁ p (dd.rho ψ w' φ)) = omd p⁻¹ (omd₁ p (dd₁.rho ψ w' φ)) := by rw [hrho]
          _ = omd p⁻¹ (dd₁.rho ψ (actB (cA σ) p w') (omd₁ p φ)) := by rw [hS₁.impl p w' φ hφ]
          _ = omd p⁻¹ (dd.rho ψ (actB (cA σ) p w') (omd₁ p φ)) := by rw [hrho]
          _ = dd.rho ψ (actB (cA σ) p⁻¹ (actB (cA σ) p w')) (omd p⁻¹ (omd₁ p φ)) :=
              hS.impl _ _ _ (hS₁.pres p φ hφ)
          _ = _ := by rw [actB_inv_actB])
    refine ⟨c, fun φ hφ => ?_⟩
    have := congrArg (omd p) (hc φ hφ)
    rwa [Module.End.mul_apply, inv_mul, map_smul] at this
  choose cf hcf using key
  have hsp : ∀ p, ∀ φ ∈ schA F (κ ⊕ κ), omd p φ ∈ schA F (κ ⊕ κ) := fun p φ hφ => hS.pres p φ hφ
  have huniq : ∀ p (c : ℂ), (∀ φ ∈ schA F (κ ⊕ κ), omd₁ p φ = c • omd p φ) → c = cf p := fun p c hc => by
    have h1 := hc _ (hsp p⁻¹ φz hφz)
    rw [hcf p _ (hsp p⁻¹ φz hφz), inv_mul] at h1
    have h2 := congrFun h1 0
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    exact (mul_right_cancel₀ hφz0 h2).symm
  have hmul : ∀ p q, cf (p * q) = cf p * cf q := fun p q => (huniq (p * q) _ fun φ hφ => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hcf q φ hφ, map_smul,
      hcf p _ (hsp q φ hφ), smul_smul, mul_comm]).symm
  have hone : cf 1 = 1 := (huniq 1 1 fun φ _ => by simp).symm
  let cM : UG (cA σ) (dbl (incM F JB)) →* ℂ := { toFun := cf, map_one' := hone, map_mul' := hmul }
  let c := cM.toHomUnits
  have hcv : ∀ p, ((c p : ℂˣ) : ℂ) = cf p := fun p => rfl
  have hcont_cf : Continuous cf := by
    refine continuous_iff_continuousAt.2 fun p₀ => ?_
    have hφ := hsp p₀⁻¹ φz hφz
    have hf := hS.cont _ (evalZero_mem_adelicSchwartzAdmittedForms (κ ⊕ κ)) _ hφ
    have hf₁ := hS₁.cont _ (evalZero_mem_adelicSchwartzAdmittedForms (κ ⊕ κ)) _ hφ
    simp only [LinearMap.proj_apply] at hf hf₁
    have h0 : omd p₀ (omd p₀⁻¹ φz) 0 ≠ 0 := by rw [inv_mul]; exact hφz0
    refine (hf₁.continuousAt.div hf.continuousAt h0).congr ?_
    filter_upwards [hf.continuousAt.eventually_ne h0] with p hp
    show omd₁ p _ 0 / omd p _ 0 = cf p
    rw [hcf p _ hφ]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  have hcont : Continuous c := by
    refine Units.continuous_iff.2 ⟨hcont_cf, ?_⟩
    have : (fun p => ((c p)⁻¹ : ℂˣ).val) = fun p => (cf p)⁻¹ := funext fun p => by
      rw [Units.val_inv_eq_inv_val, hcv]
    rw [this]
    exact hcont_cf.inv₀ fun p => by rw [← hcv]; exact (c p).ne_zero

  let π := archUG σ (dbl (incM F JB))
  let c' := c.comp π
  have hcont' : Continuous c' := hcont.comp (continuous_archUG σ _)
  obtain ⟨l, hl, hlinv, φ₀, hφ₀, hl0⟩ := GlobalTheory.T.exists_diagonalLagrangian_invariant_form F ψ κ
  have hP : ∀ (p : UG (cA σ) (dbl (incM F JB))) (t : GL (Fin b) (AE F E)),
      ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix _ _ (AE F E)) * diagCols (Fin b) = diagCols (Fin b) * t.1 →
        c' p = 1 := fun p t hpt => by
    let t' := cutGL eE_mul_self t
    have hpt' : (((π p : UG (cA σ) (dbl (incM F JB))) : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix _ _ (AE F E)) *
        diagCols (Fin b) = diagCols (Fin b) * (t' : Matrix (Fin b) (Fin b) (AE F E)) := by
      rw [cutUG_val, cutGL_val]
      exact cut_mul_eq _ hpt
    have harch : At (evI F) (((Matrix.GeneralLinearGroup.det t' : (AE F E)ˣ) : AE F E) - 1) := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, cutGL_val]
      exact at_det_cut _
    have hφ := hsp (π p)⁻¹ φ₀ hφ₀
    have e1 := hR l hl (fun z φ hφ => by
      convert hlinv (d.e z).1 (d.e z).2 φ hφ using 2; exact congrFun (dd_rho_diag hdd ψ z) φ) (π p) t' hpt' _ hφ
    have e2 := hR₁ l hl (fun z φ hφ => by
      convert hlinv (d.e z).1 (d.e z).2 φ hφ using 2; exact congrFun (dd_rho_diag hdd₁ ψ z) φ) (π p) t' hpt' _ hφ
    rw [hχ _ harch] at e2
    rw [← e2, hcf (π p) _ hφ, inv_mul, map_smul, smul_eq_mul] at e1
    show c (π p) = 1
    refine Units.ext ?_
    rw [hcv, Units.val_one]
    exact mul_right_cancel₀ hl0 (by rw [one_mul]; exact e1.symm)
  have hc1 := GlobalTheory.T.doubledUnitary_character_trivial_of_siegel F E σ hσ b JB ε hJ hdet c' hcont' hP
  intro g hg Φ hΦ
  obtain ⟨gd, hgd⟩ := GlobalTheory.T.exists_unitaryDoubled_blockDiag_one (AF F) (AE F E) (cA σ) (Fin b) (incM F JB) g
  have hgdA : At (evI F) (((gd : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) - 1) :=
      fun u hu => by
    show u • (((gd : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) - 1) = 0
    rw [hgd]
    exact at_fromBlocks_one _ hg u hu
  have hπ : π gd = gd := Subtype.ext (Units.ext (by rw [cutUG_val]; exact cut_eq_of_at _ hgdA))
  have hcf1 : cf gd = 1 := by
    have := congrArg (fun f : UG (cA σ) (dbl (incM F JB)) →* ℂˣ => ((f gd : ℂˣ) : ℂ)) hc1
    simp only [MonoidHom.one_apply, Units.val_one] at this
    rw [← hcv, ← hπ]
    exact this
  obtain ⟨φ₂, hφ₂, hφ₂0⟩ := GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F κ
  have hb := GlobalTheory.T.productFunctionOnSumCoords_mem_adelicSchwartzSpace F κ κ Φ hΦ φ₂ hφ₂
  have e := hres g gd hgd Φ hΦ φ₂ hφ₂
  have e₁ := hres₁ g gd hgd Φ hΦ φ₂ hφ₂
  rw [hcf gd _ hb, hcf1, one_smul, e] at e₁
  funext x
  have := congrFun e₁ (Sum.elim x 0)
  simp only [boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr] at this
  exact mul_right_cancel₀ hφ₂0 this

end Adelic

section Pair

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let Bm : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have hB : Bmᵀ * M * Bm.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]; rfl
  have hD : (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_neg, Matrix.det_one]; simp
  have h2 := congrArg Matrix.det hB
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_mul] at h2
  intro h0
  rw [h0, mul_zero, zero_mul] at h2
  exact hD h2.symm

theorem det_ne_zero_of_map {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ) (h : (J.map f).det ≠ 0) : J.det ≠ 0 :=
  fun h0 => h (by rw [show J.map f = f.mapMatrix J from rfl, ← RingHom.map_det, h0, map_zero])

theorem pair_eq_of_arch (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {n d : ℕ} (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (χX χW χX₁ χW₁ : Chr F E)
    (hX : ∀ i j, σ (X.J j i) = X.J i j) (hXd : X.J.det ≠ 0) (hW : ∀ i j, σ (W.J j i) = -W.J i j) (hWd : W.J.det ≠ 0)
    (hχX : ∀ z : (AE F E)ˣ, At (evI F) ((z : AE F E) - 1) → χX₁ z = χX z)
    (hχW : ∀ z : (AE F E)ˣ, At (evI F) ((z : AE F E) - 1) → χW₁ z = χW z)
    (om om₁ : Rep σ X W) (h : M.IsWeil ψ χX χW om) (h₁ : M.IsWeil ψ χX₁ χW₁ om₁) :
    ∀ g k, g ∈ UAt σ X (evI F) → k ∈ UAt σ W (evI F) →
      ∀ Φ ∈ schA F (Fin n × Fin d), om (g, k) Φ = om₁ (g, k) Φ := by
  intro g k hg hk Φ hΦ
  obtain ⟨hB, ⟨d', hd', hA⟩, -⟩ := h
  obtain ⟨hB₁, ⟨d'₁, hd'₁, hA₁⟩, -⟩ := h₁
  have eW : ∀ i j, σ (W.J j i) = (((-1 : ℤˣ) : ℤ) : E) * W.J i j := fun i j => by simp [hW i j]
  have eX : ∀ i j, σ (X.J j i) = (((1 : ℤˣ) : ℤ) : E) * X.J i j := fun i j => by simp [hX i j]
  have uB := member_eq_of_arch σ hσ X.J W.J (-1) eW hWd ψ hψ M.co χX χX₁ hχX _ _ hB hB₁
  have he : d'₁.e = d'.e := LinearEquiv.ext fun y => by rw [← Matrix.transpose_transpose y, hd'₁, hd']
  obtain ⟨e₁, f₁⟩ := d'₁
  obtain ⟨e₂, f₂⟩ := d'
  simp only at he
  subst he
  have uA := member_eq_of_arch σ hσ W.J X.J 1 eX hXd ψ hψ _ χW χW₁ hχW _ _ hA hA₁
  have hx : ((g, k) : UA σ X.J × UA σ W.J) = (g, 1) * (1, k) := by simp
  rw [hx, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  have h1 : om (1, k) Φ = om₁ (1, k) Φ := uB k hk Φ hΦ
  rw [h1]
  exact uA g hg _ (hB₁.1.pres k Φ hΦ)

end Pair

end GlobalTheory.ArchWeil

section Main

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.ArchWeil.weil_eq_at_real_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xa Xb : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) oa oa' ob ob',
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B Γ Xa oa oa' → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B Γ Xb ob ob' →
    (∀ g h, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) → h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.W (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) →
      ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), oa (g, h) Φ = ob (g, h) Φ) ∧
    (∀ g h, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) → h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.W (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) →
      ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), oa' (g, h) Φ = ob' (g, h) Φ) := by
  intro F E _ _ _ _ _ σ B a a' Γ Xa Xb oa oa' ob ob' ha hb
  have hσ := ha.base.cm
  have hψ := ha.base.std
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hVd : Γ.V.J.det ≠ 0 :=
    GlobalTheory.ArchWeil.det_ne_zero_of_map _ _ (GlobalTheory.ArchWeil.det_ne_zero_of_hasSig (ha.geo.hV.sig w))
  have hV'd : Γ.V'.J.det ≠ 0 :=
    GlobalTheory.ArchWeil.det_ne_zero_of_map _ _ (GlobalTheory.ArchWeil.det_ne_zero_of_hasSig (ha.geo.hV'.sig w))
  have hWd : Γ.W.J.det ≠ 0 := by
    refine GlobalTheory.ArchWeil.det_ne_zero_of_map _ (B.emb w).1 fun h0 => ?_
    have h1 := GlobalTheory.ArchWeil.det_ne_zero_of_hasSig (ha.geo.hW.sig w)
    rw [Matrix.det_smul, h0, mul_zero] at h1
    exact h1 rfl
  have eβ : ∀ z : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)ˣ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) ((z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) - 1) →
      Xb.β z = Xa.β z := fun z hz => Circle.ext (by rw [hb.chars.expβ z hz, ha.chars.expβ z hz])
  have eα : ∀ z : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)ˣ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) ((z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) - 1) →
      Xb.α z = Xa.α z := fun z hz => Circle.ext (by rw [hb.chars.expα z hz, ha.chars.expα z hz])
  refine ⟨GlobalTheory.ArchWeil.pair_eq_of_arch σ hσ Γ.V Γ.W Γ.M B.ψ hψ _ _ _ _ ha.geo.hV.herm hVd ha.geo.hW.skew hWd eβ
      (fun z hz => by rw [MonoidHom.div_apply, MonoidHom.div_apply, eβ z hz, eα z hz]) oa ob ha.weil hb.weil,
    GlobalTheory.ArchWeil.pair_eq_of_arch σ hσ Γ.V' Γ.W Γ.M' B.ψ hψ _ _ _ _ ha.geo.hV'.herm hV'd ha.geo.hW.skew hWd eα
      (fun z hz => by rw [MonoidHom.div_apply, MonoidHom.div_apply, eβ z hz, eα z hz]) oa' ob' ha.weil' hb.weil'⟩

end Main
