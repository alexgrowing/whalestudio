import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryElementActsLocalOperatorAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorLatticeStabiliserRightPreservesVacuu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenLatticePointAtPlaceLocalIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalSubgroupFirstProjEqAnnihilator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenProportionalLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatAtVSelfDual
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.DblVacAny

section Alg

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in

theorem symp_dbl (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α (β ⊕ β) E) :
    symp (R := R) c ξ JA (dbl JB) x y =
      symp (R := R) c ξ JA JB x.toCols₁ y.toCols₁ - symp (R := R) c ξ JA JB x.toCols₂ y.toCols₂ := by
  unfold symp
  rw [← map_sub, ← mul_sub]
  congr 2
  simp [hTens, dbl, Fintype.sum_sum_type, Matrix.toCols₁, Matrix.toCols₂, Finset.sum_add_distrib, sub_eq_add_neg]

omit [DecidableEq α] [DecidableEq β] in
theorem symp_zero_right (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x : Matrix α β E) :
    symp (R := R) c ξ JA JB x 0 = 0 := by
  simp [symp, hTens]

theorem schr_box_star [Invertible (2 : R)] (ψ : AddChar R ℂ) (hψ : ∀ a, star (ψ a) = ψ (-a)) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (Φ Ψ : (κ → R) → ℂ) :
    schr ψ (Sum.elim w.1 w'.1, Sum.elim w.2 (-w'.2)) (boxFun Φ fun x => star (Ψ x)) =
      boxFun (schr ψ w Φ) fun x => star (schr ψ w' Ψ x) := by
  funext x
  have e1 : (x + Sum.elim w.1 w'.1) ∘ Sum.inl = x ∘ Sum.inl + w.1 := by funext i; rfl
  have e2 : (x + Sum.elim w.1 w'.1) ∘ Sum.inr = x ∘ Sum.inr + w'.1 := by funext i; rfl
  have e3 : x ⬝ᵥ Sum.elim w.2 (-w'.2) + ⅟(2 : R) * (Sum.elim w.1 w'.1 ⬝ᵥ Sum.elim w.2 (-w'.2)) =
      ((x ∘ Sum.inl) ⬝ᵥ w.2 + ⅟(2 : R) * (w.1 ⬝ᵥ w.2)) + -((x ∘ Sum.inr) ⬝ᵥ w'.2 + ⅟(2 : R) * (w'.1 ⬝ᵥ w'.2)) := by
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, mul_neg,
      Finset.sum_neg_distrib, Function.comp_apply]
    ring
  simp only [schr, boxFun, e1, e2, e3, AddChar.map_add_eq_mul ψ _ (-_), star_mul', hψ]
  ring

theorem box_mem_SB {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem local_identity (v : Pl F) {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : Darboux B κ) (ψ : AddChar (AF F) ℂ) (γ : W) (f : (κ → Fv F v) → ℂ) (χ : ℂ) (hγ : At (evFin F v) γ)
    (r : (κ → AF F) → ℂ) (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x)
    (hA : co.rho ψ γ (tens (evFin F v) f r) = χ • tens (evFin F v) f r) (x₀ : κ → AF F) (hx₀ : r x₀ ≠ 0)
    (ξ : κ → Fv F v) : GlobalTheory.LatVac.psiAt ψ v (ξ ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 +
        (2 : Fv F v)⁻¹ * ((GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2)) *
      f (ξ + (GlobalTheory.LatVac.locCo co v γ).1) = χ * f ξ := by
  have hx1 : ∀ k, At (evFin F v) ((co.e γ).1 k) := fun k u hu => by
    have h := congrArg (fun w => (co.e w).1 k) (hγ u hu)
    simpa [LinearEquiv.map_smul] using h
  have hy1 : ∀ k, At (evFin F v) ((co.e γ).2 k) := fun k u hu => by
    have h := congrArg (fun w => (co.e w).2 k) (hγ u hu)
    simpa [LinearEquiv.map_smul] using h
  set z : κ → AF F := fun k => GlobalTheory.LatVac.liftV v (ξ k - evFin F v (x₀ k)) with hz
  have hzat : At (evFin F v) z := GlobalTheory.VacIndic.at_pi fun k => GlobalTheory.LatVac.at_liftV v _
  set x : κ → AF F := x₀ + z with hx
  have hevx : (fun i => evFin F v (x i)) = ξ := by
    funext i
    simp [hx, hz, GlobalTheory.LatVac.evFin_liftV]
  have hrx : r x = r x₀ := hr x₀ z hzat
  have hrx1 : r (x + (co.e γ).1) = r x := hr x _ (GlobalTheory.VacIndic.at_pi hx1)
  have key := congrFun hA x
  simp only [Darboux.rho, schr, tens, Pi.smul_apply, smul_eq_mul] at key
  have hAt : At (evFin F v) (x ⬝ᵥ (co.e γ).2 + ⅟(2 : AF F) * ((co.e γ).1 ⬝ᵥ (co.e γ).2)) := by
    refine GlobalTheory.VacIndic.at_add ?_ (GlobalTheory.VacIndic.at_mul_left ?_)
    · exact GlobalTheory.VacIndic.at_sum _ _ fun i => GlobalTheory.VacIndic.at_mul_left (hy1 i)
    · exact GlobalTheory.VacIndic.at_sum _ _ fun i => GlobalTheory.VacIndic.at_mul_left (hy1 i)
  rw [GlobalTheory.VacIndic.psi_of_at ψ hAt, hrx1] at key
  have hhalf : evFin F v (⅟(2 : AF F)) = (2 : Fv F v)⁻¹ := by
    rw [GlobalTheory.VacIndic.invOf_two_eq, GlobalTheory.VacIndic.evFin_algebraMap]
    simp [map_ofNat]
  have hdot : ∀ a b : κ → AF F, evFin F v (a ⬝ᵥ b) = (fun i => evFin F v (a i)) ⬝ᵥ (fun i => evFin F v (b i)) := by
    intro a b
    simp [dotProduct, map_sum, map_mul]
  have hsum : (fun i => evFin F v ((x + (co.e γ).1) i)) = ξ + (GlobalTheory.LatVac.locCo co v γ).1 := by
    funext i
    rw [← hevx]
    simp [GlobalTheory.LatVac.locCo]
  rw [map_add, map_mul, hhalf, hdot, hdot, hevx, hsum] at key
  have hr0 : r x ≠ 0 := hrx ▸ hx₀
  rw [GlobalTheory.LatVac.psiAt_apply]
  apply mul_right_cancel₀ hr0
  rw [mul_assoc χ, ← key]
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  ring

def latDbl {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl F) :
    AddSubgroup (Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) where
  carrier := {z | z.toCols₁ ∈ latAtV X Y v ∧ z.toCols₂ ∈ latAtV X Y v}
  zero_mem' := ⟨(latAtV X Y v).zero_mem, (latAtV X Y v).zero_mem⟩
  add_mem' := fun ha hb => ⟨(latAtV X Y v).add_mem ha.1 hb.1, (latAtV X Y v).add_mem ha.2 hb.2⟩
  neg_mem' := fun ha => ⟨(latAtV X Y v).neg_mem ha.1, (latAtV X Y v).neg_mem ha.2⟩

theorem at_latDbl {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl F) :
    ∀ γ ∈ latDbl X Y v, At (evFin F v) γ := by
  intro γ hγ u hu
  have h1 := (GlobalTheory.LatVac.latAtV_at_stable X Y v).1 _ hγ.1 u hu
  have h2 := (GlobalTheory.LatVac.latAtV_at_stable X Y v).1 _ hγ.2 u hu
  ext i (j | j)
  · exact congrFun (congrFun h1 i) j
  · exact congrFun (congrFun h2 i) j

theorem vecMulVec_mem_latDbl {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl F) {x : Fin n → E} (hx : x ∈ X.L)
    {z : Fin d ⊕ Fin d → AE F E} (hz : z ∈ GlobalTheory.DblVac.latD Y v) :
    Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) z ∈ latDbl X Y v :=
  ⟨GlobalTheory.VacTransport.vecMulVec_mem X Y v hx hz.1, GlobalTheory.VacTransport.vecMulVec_mem X Y v hx hz.2⟩

theorem mul_transpose_mem_doubledTensorLattice_of_into_doubled {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl F)
    (h : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))
    (hh : ∀ z ∈ GlobalTheory.InertSph.latAt Y v, h *ᵥ z ∈ GlobalTheory.DblVac.latD Y v)
    {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X Y v) : γ * hᵀ ∈ latDbl X Y v := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, x, hx, y, hy, rfl⟩ := hz
    have hm : (a • fun i => inclR (F := F) (AF F) (y i)) ∈ GlobalTheory.InertSph.latAt Y v :=
      AddSubgroup.subset_closure ⟨a, ha, hv, y, hy, rfl⟩
    have e : a • incM F (Matrix.vecMulVec x y) =
        Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (a • fun i => inclR (F := F) (AF F) (y i)) := by
      ext i j
      simp [Matrix.vecMulVec_apply, incM]
    rw [e, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
    exact vecMulVec_mem_latDbl X Y v hx (hh _ hm)
  | zero => rw [Matrix.zero_mul]; exact zero_mem _
  | add z z' _ _ h h' => rw [Matrix.add_mul]; exact add_mem h h'
  | neg z _ h => rw [Matrix.neg_mul]; exact neg_mem h

theorem mul_transpose_mem_latDbl {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl F)
    (h : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E))
    (hh : ∀ z ∈ GlobalTheory.DblVac.latD Y v, h *ᵥ z ∈ GlobalTheory.DblVac.latD Y v)
    {γ : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)} (hγ : γ ∈ latDbl X Y v) : γ * hᵀ ∈ latDbl X Y v := by
  have e : γ * hᵀ = γ.toCols₁ * (h.toCols₁)ᵀ + γ.toCols₂ * (h.toCols₂)ᵀ := by
    ext i j
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toCols₁, Matrix.toCols₂]
  rw [e]
  refine add_mem (mul_transpose_mem_doubledTensorLattice_of_into_doubled X Y v _ (fun z hz => ?_) hγ.1)
    (mul_transpose_mem_doubledTensorLattice_of_into_doubled X Y v _ (fun z hz => ?_) hγ.2)
  · have e1 : h.toCols₁ *ᵥ z = h *ᵥ Sum.elim z 0 := by
      ext i
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toCols₁]
    rw [e1]
    exact hh _ ⟨hz, (GlobalTheory.InertSph.latAt Y v).zero_mem⟩
  · have e1 : h.toCols₂ *ᵥ z = h *ᵥ Sum.elim 0 z := by
      ext i
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toCols₂]
    rw [e1]
    exact hh _ ⟨(GlobalTheory.InertSph.latAt Y v).zero_mem, hz⟩

theorem latDbl_selfDual (σ : E →ₐ[F] E) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl F) (ψ : AddChar (AF F) ℂ)
    (hsd : ∀ z : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) z → (z ∈ latAtV X Y v ↔ ∀ γ ∈ latAtV X Y v,
      ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F Y.J) z γ) = 1))
    (z : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) (hz : At (evFin F v) z) :
    z ∈ latDbl X Y v ↔ ∀ γ ∈ latDbl X Y v,
      ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F Y.J)) z γ) = 1 := by
  have hz1 : At (evFin F v) z.toCols₁ := fun u hu => by
    ext i j; exact congrFun (congrFun (hz u hu) i) (Sum.inl j)
  have hz2 : At (evFin F v) z.toCols₂ := fun u hu => by
    ext i j; exact congrFun (congrFun (hz u hu) i) (Sum.inr j)
  constructor
  · intro hm γ hγ
    rw [symp_dbl, AddChar.map_sub_eq_div, (hsd _ hz1).1 hm.1 _ hγ.1, (hsd _ hz2).1 hm.2 _ hγ.2, div_one]
  · intro h
    refine ⟨(hsd _ hz1).2 fun γ hγ => ?_, (hsd _ hz2).2 fun γ hγ => ?_⟩
    · have := h (Matrix.fromCols γ 0) ⟨by simpa using hγ, by simpa using zero_mem _⟩
      rwa [symp_dbl, Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols, symp_zero_right, sub_zero] at this
    · have := h (Matrix.fromCols 0 γ) ⟨by simpa using zero_mem _, by simpa using hγ⟩
      rw [symp_dbl, Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols, symp_zero_right, zero_sub,
        AddChar.map_neg_eq_inv] at this
      exact inv_eq_one.1 this

theorem dbl_eigen (σ : E →ₐ[F] E) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (hX : X.L.IsLattice E)
    (hY : Y.L.IsLattice E) (M : Model σ X Y) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (v : Pl F) (hunr : PsiUnr ψ v)
    (hsd : ∀ z : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) z → (z ∈ latAtV X Y v ↔ ∀ γ ∈ latAtV X Y v,
      ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F Y.J) z γ) = 1))
    (φ : (Fin n × Fin d → Fv F v) → ℂ) (hφ : M.IsVac ψ v φ)
    (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F X.J) (dbl (incM F Y.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d)))
    (omd : GlobalTheory.DblVac.UD σ Y →* Module.End ℂ (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ))
    (hdc : IsDblCoord (cA σ) (-1 : AE F E) (incM F X.J) (incM F Y.J) M.co dd)
    (hU : IsUSplitting (adeleClass F) ψ dd (actB (cA σ)) omd)
    (r : (Fin n × Fin d → AF F) → ℂ) (hr : Rest (evFin F v) φ r) (g : GlobalTheory.DblVac.UD σ Y)
    (hg : g ∈ GlobalTheory.DblVac.KD σ Y v) : ∃ μ : ℂ,
      omd g (boxFun (tens (evFin F v) φ r) (fun x => star (tens (evFin F v) φ r x))) =
        μ • boxFun (tens (evFin F v) φ r) (fun x => star (tens (evFin F v) φ r x)) := by
  classical
  obtain ⟨hvSB, hφ0, θ, -, hvac⟩ := hφ
  have hstar : ∀ a, star (ψ a) = ψ (-a) := fun a => by
    rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, GlobalTheory.StdCharFromIsStd.norm_psi hψ a]
    simp
  set vD := boxFun φ (fun x => star (φ x)) with hvD
  set RD := boxFun r (fun x => star (r x)) with hRD
  have hvDSB : vD ∈ SB _ := box_mem_SB hvSB ⟨hvSB.1.comp _, hvSB.2.comp_left (star_zero _)⟩
  have hvD0 : vD ≠ 0 := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hφ0
    refine Function.ne_iff.mpr ⟨Sum.elim x x, ?_⟩
    simp only [hvD, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.zero_apply] at hx ⊢
    exact mul_ne_zero hx (star_ne_zero.mpr hx)
  have hS : boxFun (tens (evFin F v) φ r) (fun x => star (tens (evFin F v) φ r x)) = tens (evFin F v) vD RD := by
    funext x
    simp only [tens, boxFun, hvD, hRD, Function.comp_def, star_mul']
    ring
  have hRest : Rest (evFin F v) vD RD := by
    refine ⟨fun x z hz => ?_, ?_⟩
    · have hz1 : At (evFin F v) (z ∘ Sum.inl) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inl i)
      have hz2 : At (evFin F v) (z ∘ Sum.inr) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inr i)
      show r ((x + z) ∘ Sum.inl) * star (r ((x + z) ∘ Sum.inr)) = r (x ∘ Sum.inl) * star (r (x ∘ Sum.inr))
      rw [show (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl from rfl,
        show (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr from rfl, hr.1 _ _ hz1, hr.1 _ _ hz2]
    · rw [← hS]
      exact GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ _ hr.2 _ (GlobalTheory.ConjSch.star_mem_schA _ _ hr.2)

  obtain ⟨φ₁, -, hA⟩ : ∃ φ₁ ∈ SB _, Acts (evFin F v) (omd g) vD φ₁ := by
    refine GlobalTheory.DblActs.acts_of_comm v ψ hψ (omd g) (fun Φ hΦ => hU.pres g Φ hΦ)
      (fun μ hμ Φ hΦ => hU.unit μ hμ g Φ hΦ) ?_ vD hvDSB
    intro u hu x y Φ hΦ
    set z := dd.e.symm (x, y) with hz
    have he : dd.e (u • z) = (u • x, u • y) := by
      rw [LinearEquiv.map_smul, hz, LinearEquiv.apply_symm_apply, Prod.smul_mk]
    have h2 := hg.1 u hu
    have e2 : actB (cA σ) g (u • z) = u • z := by
      simp only [actB]
      set P := GlobalTheory.DblVac.matD g with hP
      set c : AE F E := algebraMap (AF F) (AE F E) u with hc
      have hs1 : u • z = c • z := (algebraMap_smul (AE F E) u z).symm
      have hs2 : u • (P - 1) = c • (P - 1) := (algebraMap_smul (AE F E) u (P - 1)).symm
      have h2' : c • (P - 1) = 0 := hs2 ▸ h2
      have : (c • z) * Pᵀ - c • z = z * (c • (P - 1))ᵀ := by
        rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
          Matrix.mul_sub, Matrix.mul_one, smul_sub]
      rw [h2'] at this
      simp only [Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this
      rw [hs1]
      exact this
    have h3 := hU.impl g (u • z) Φ hΦ
    simp only [Darboux.rho, he, e2] at h3
    exact h3
  have hT : omd g (tens (evFin F v) vD RD) = tens (evFin F v) φ₁ RD := hA RD hRest
  rw [hS, hT]
  by_cases hR0 : RD = 0
  · refine ⟨0, ?_⟩
    funext x
    simp [tens, hR0]
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hR0

  set Λ := latDbl X Y v with hΛ
  set ch : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E) → ℂ := fun γ =>
    ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (dbl (incM F Y.J)) γ γ) with hch
  have hE0 : ∀ γ ∈ Λ, dd.rho ψ γ (tens (evFin F v) vD RD) = ch γ • tens (evFin F v) vD RD := by
    intro γ hγ
    have h1 := hvac _ hγ.1 r hr
    have h2 := hvac _ hγ.2 r hr
    rw [GlobalTheory.VacTransport.tens_smul] at h1 h2
    simp only [Darboux.rho] at h1 h2
    have h3 := hdc γ.toCols₁ γ.toCols₂
    rw [Matrix.fromCols_toCols] at h3
    rw [← hS, Darboux.rho, h3, schr_box_star ψ hstar, h1, h2]
    funext x
    simp only [hch, boxFun, Pi.smul_apply, smul_eq_mul, star_mul', hstar, symp_dbl, mul_sub, sub_eq_add_neg, mul_add,
      mul_neg, AddChar.map_add_eq_mul]
    ring
  have hE1 : ∀ γ ∈ Λ, dd.rho ψ γ (tens (evFin F v) φ₁ RD) = ch γ • tens (evFin F v) φ₁ RD := by
    intro γ hγ
    have hγ' : γ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ ∈ Λ :=
      mul_transpose_mem_latDbl X Y v _ (fun z hz => (hg.2 z hz).2) hγ
    have hback : actB (cA σ) g (γ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ) = γ := by
      change γ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ * (GlobalTheory.DblVac.matD g)ᵀ = γ
      have e : GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.matD g⁻¹ = 1 := Units.mul_inv g.1
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.mul_one]
    have hsy : ch (γ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ) = ch γ := by
      simp only [hch]
      rw [GlobalTheory.VacTransport.symp_mul_transpose (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (dbl (incM F Y.J))
        (GlobalTheory.DblVac.matD g⁻¹) (g⁻¹).2 γ γ]
    have h1 := hU.impl g (γ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ) _ hRest.2
    rw [hback, hE0 _ hγ', hsy, map_smul, hT] at h1
    exact h1.symm

  have hAt : ∀ γ ∈ Λ, At (evFin F v) γ := at_latDbl X Y v
  let χ : ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v) × ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v) → ℂ := fun l =>
    if h : ∃ γ ∈ Λ, GlobalTheory.LatVac.locCo dd v γ = l then ch h.choose else 0
  have loc : ∀ f : ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v) → ℂ,
      (∀ γ ∈ Λ, dd.rho ψ γ (tens (evFin F v) f RD) = ch γ • tens (evFin F v) f RD) →
      ∀ l ∈ Λ.map (GlobalTheory.LatVac.locCo dd v), ∀ ξ,
        GlobalTheory.LatVac.psiAt ψ v (ξ ⬝ᵥ l.2 + (2 : Fv F v)⁻¹ * (l.1 ⬝ᵥ l.2)) * f (ξ + l.1) = χ l * f ξ := by
    intro f hf l hl ξ
    have h : ∃ γ ∈ Λ, GlobalTheory.LatVac.locCo dd v γ = l := AddSubgroup.mem_map.mp hl
    have key := local_identity v dd ψ h.choose f _ (hAt _ h.choose_spec.1) RD hRest.1 (hf _ h.choose_spec.1) x₀ hx₀ ξ
    simp only [χ, dif_pos h]
    rw [h.choose_spec.2] at key
    exact key
  obtain ⟨c, hc0, hcb⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded X Y v M.co hX hY
  have hsd' := GlobalTheory.LatVac.DualLoc.map_selfDual v dd ψ Λ hAt (latDbl_selfDual σ X Y v ψ hsd)
  have hfill := GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v (GlobalTheory.LatVac.psiAt ψ v)
    (Λ.map (GlobalTheory.LatVac.locCo dd v)) c hc0 (fun x => hunr x) hsd'
    (fun l hl i => by
      obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.mp hl
      have h3 := hdc γ.toCols₁ γ.toCols₂
      rw [Matrix.fromCols_toCols] at h3
      simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, h3] at hcb ⊢
      rcases i with i | i
      · exact hcb _ hγ.1 i
      · refine ⟨(hcb _ hγ.2 i).1, ?_⟩
        simp only [Sum.elim_inr, Pi.neg_apply, map_neg, mul_neg]
        exact neg_mem (hcb _ hγ.2 i).2)
  obtain ⟨μ, hμ⟩ := GlobalTheory.heisenbergEigen_proportional (GlobalTheory.LatVac.psiAt ψ v) (Λ.map (GlobalTheory.LatVac.locCo dd v)) χ vD φ₁
    (loc vD hE0) (loc φ₁ hE1) hvD0 hfill
  exact ⟨μ, by rw [hμ, GlobalTheory.VacTransport.tens_smul]⟩

theorem split_eigen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → v ∉ X.T → PsiUnr B.ψ v →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.V.J) (dbl (incM F G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.V.J) (incM F G.W.J) G.M.co dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F G.V.J) (dbl (incM F G.W.J)) dd X.β (diagCols (Fin (a + a'))) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.W v, ∃ μ : ℂ,
      omd g (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v _ _ hunr dd omd hdc hsp r hr g hg
  exact dbl_eigen σ G.V G.W hT.geo.hV.lat hT.geo.hW.lat G.M B.ψ hT.base.std v hunr
    (GlobalTheory.PsiUnrSelfDual.latAtV_selfDual F E σ B a a' G X om om' hT v hunr) _ (hT.geo.hM.vac v) dd omd hdc hsp.2.1 r hr g hg

end GlobalTheory.DblVacAny

end
