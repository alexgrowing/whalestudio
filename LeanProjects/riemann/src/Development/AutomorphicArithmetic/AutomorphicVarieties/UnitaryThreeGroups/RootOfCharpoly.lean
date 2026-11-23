import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PowEqOneOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtInertiaAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtIneL
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLeOneOfIsIntegral

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem quot_mem {H M : Type} [Group H] [CommGroup M] (U : Subgroup M) (a t : H →* M) (g : H) (i j : Fin 3)
    (h1 : a g / t g ^ wt1 i ∈ U) (h2 : a g = t g ^ wt1 j) : t g ^ (wt1 j - wt1 i) ∈ U := by
  rwa [h2, div_eq_mul_inv, ← _root_.zpow_sub] at h1

private theorem eq_away {H M : Type} [Group H] [CommGroup M] (U : Subgroup M) (I : Subgroup H) (a t : H →* M)
    (i : Fin 3) (hred : ∀ g, a g / t g ^ wt1 i ∈ U) (hroot : ∀ g ∈ I, ∃ j, a g = t g ^ wt1 j)
    (hI : ∀ g ∈ I, t g ∈ U → t g = 1) (g : H) (hg : g ∈ I) : a g = t g ^ wt1 i := by
  obtain ⟨j, hj⟩ := hroot g hg
  have h := quot_mem U a t g i j (hred g) hj
  rw [← map_zpow] at h
  have h' := hI _ (I.zpow_mem hg _) h
  rw [map_zpow, _root_.zpow_sub, mul_inv_eq_one] at h'
  rw [hj, h']

private theorem eq_of_sq {H M : Type} [Group H] [CommGroup M] (U : Subgroup M) (a t : H →* M)
    (i : Fin 3) (g : H) (hred : a g / t g ^ wt1 i ∈ U) (hroot : ∃ j, a g = t g ^ wt1 j)
    (hs : t g ^ 2 ∉ U) : a g = t g ^ wt1 i := by
  obtain ⟨j, hj⟩ := hroot
  by_cases hij : j = i
  · rw [hj, hij]
  exfalso
  have h := quot_mem U a t g i j hred hj
  have hd : (wt1 j - wt1 i) ∣ 2 := by
    revert hij
    fin_cases i <;> fin_cases j <;> simp [wt1]
  obtain ⟨m, hm⟩ := hd
  apply hs
  have := U.zpow_mem h m
  rwa [← _root_.zpow_mul, ← hm, zpow_ofNat] at this

private theorem eq_above {H M : Type} [Group H] [CommGroup M] (U : Subgroup M) (I : Subgroup H) (a t : H →* M)
    (i : Fin 3) (hred : ∀ g, a g / t g ^ wt1 i ∈ U) (hroot : ∀ g ∈ I, ∃ j, a g = t g ^ wt1 j)
    (s : H) (hs : s ∈ I) (hs2 : t s ^ 2 ∉ U) (g : H) (hg : g ∈ I) : a g = t g ^ wt1 i := by
  by_cases h : t g ^ 2 ∈ U
  · have h1 := eq_of_sq U a t i s (hred s) (hroot s hs) hs2
    have h2 := eq_of_sq U a t i (g * s) (hred _) (hroot _ (I.mul_mem hg hs)) (by
      rw [map_mul, mul_pow]
      exact fun h' => hs2 ((U.mul_mem_cancel_left h).1 h'))
    rw [map_mul, map_mul, mul_zpow, h1] at h2
    exact mul_right_cancel h2
  · exact eq_of_sq U a t i g (hred g) (hroot g hg) h

private theorem norm_eq_one_of {F : Type} [NormedField F] [IsUltrametricDist F] {u : F} (h : ‖u - 1‖ < 1) : ‖u‖ = 1 := by
  have e : u = (u - 1) + 1 := by ring
  rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact h.ne), norm_one]
  exact max_eq_right h.le

private def U1 (F : Type) [NormedField F] [IsUltrametricDist F] : Subgroup Fˣ where
  carrier := {u | ‖(u : F) - 1‖ < 1}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    have e : ((u * v : Fˣ) : F) - 1 = u * (v - 1) + (u - 1) := by push_cast; ring
    show ‖((u * v : Fˣ) : F) - 1‖ < 1
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ hu)
    rw [norm_mul, norm_eq_one_of hu, one_mul]
    exact hv
  inv_mem' := by
    intro u hu
    have e : (u : F) * (((u⁻¹ : Fˣ) : F) - 1) = -((u : F) - 1) := by rw [mul_sub, Units.mul_inv]; ring
    have h := congrArg norm e
    rw [norm_mul, norm_eq_one_of hu, one_mul, norm_neg] at h
    show ‖((u⁻¹ : Fˣ) : F) - 1‖ < 1
    rw [h]
    exact hu

private theorem root_of_charpoly {F : Type} [Field F] (a b : Fin 3 → F)
    (h : (Matrix.diagonal a).charpoly = (Matrix.diagonal b).charpoly) (i : Fin 3) : ∃ j, a i = b j := by
  have h1 := congrArg (Polynomial.eval (a i)) h
  rw [Matrix.charpoly_diagonal, Matrix.charpoly_diagonal, Polynomial.eval_prod, Polynomial.eval_prod,
    Finset.prod_eq_zero (Finset.mem_univ i) (by simp), eq_comm, Finset.prod_eq_zero_iff] at h1
  obtain ⟨j, -, hj⟩ := h1
  exact ⟨j, by simpa [sub_eq_zero] using hj⟩

private theorem exists_diag {Γ R : Type} [Group Γ] [CommRing R] (η : Γ →* ℤˣ) (r : Γ →* GG 3 R) (hm : HasMult η r)
    (hU : Upper η r) (hL : Lower η r) :
    ∃ a : Fin 3 → η.ker →* Rˣ, ∀ g : η.ker, (r g).mat = Matrix.diagonal fun i => (a i g : R) := by
  have hd : ∀ g : η.ker, (r g).mat = Matrix.diagonal fun i => (r g).mat i i := by
    intro g
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    rw [Matrix.diagonal_apply_ne _ hij]
    rcases lt_trichotomy (wt i j) 0 with h | h | h
    · exact hU g g.2 i j h
    · exact absurd (Fin.ext (by simp only [wt, wt1] at h; omega)) hij
    · exact hL g g.2 i j h
  let b : Fin 3 → η.ker →* R := fun i =>
    { toFun := fun g => (r g).mat i i
      map_one' := by simp [GG.mat]
      map_mul' := fun g h => by
        have e : (r ((g * h : η.ker) : Γ)).mat = (r g).mat * (r h).mat :=
          congrArg Units.val (map_mul (glPart η r hm) g h)
        rw [e, hd g, Matrix.diagonal_mul, Matrix.diagonal_apply_eq] }
  exact ⟨fun i => (b i).toHomUnits, hd⟩

private theorem norm_le_one_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx

private theorem norm_unit {l : ℕ} [Fact l.Prime] (c : Coef l) {x : c.O} (hx : IsUnit x) :
    ‖algebraMap c.O (PadicAlgCl l) x‖ = 1 := by
  have hle : ∀ y : c.O, ‖(y : PadicAlgCl l)‖ ≤ 1 := fun y =>
    norm_le_one_int l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) y).map c.O.val)
  obtain ⟨u, rfl⟩ := hx
  show ‖((u : c.O) : PadicAlgCl l)‖ = 1
  have h1 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖((u⁻¹ : c.Oˣ) : c.O).1‖ = 1 := by
    rw [← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
  have h2 := hle u
  have h3 := hle (u⁻¹ : c.Oˣ)
  have h4 := norm_nonneg ((u : c.O) : PadicAlgCl l)
  nlinarith

theorem UpperTheory.V.U3.pt_fixed :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG 3 (PadicAlgCl l)} (h : D.IsPt U g₁ r),
      Upper D.η r → Lower D.η r → r = r0 D.η D.ΨQ := by
  intro hC Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hM r h hU hL
  obtain ⟨a, ha⟩ := exists_diag D.η r h.mult hU hL
  obtain ⟨-, -, -, -, -, hkill, -, -, hcont, -, hab⟩ := dat_facts D
  let t : D.η.ker →* (PadicAlgCl l)ˣ := D.ΨQ.comp D.η.ker.subtype
  have htv : ∀ g : G ℚ Ω, (D.ΨQ g : PadicAlgCl l) = algebraMap c.O (PadicAlgCl l) (D.Ψ g : c.O) := fun _ => rfl
  have hr0 : ∀ g : D.η.ker, (r0 D.η D.ΨQ g).mat = Matrix.diagonal fun i => ((t g ^ wt1 i : (PadicAlgCl l)ˣ) : PadicAlgCl l) :=
    fun _ => rfl
  have hai : ∀ i (g : D.η.ker), (a i g : PadicAlgCl l) = (r g).mat i i := fun i g => by
    rw [ha g, Matrix.diagonal_apply_eq]
  have hred : ∀ i g, a i g / t g ^ wt1 i ∈ U1 (PadicAlgCl l) := by
    intro i g
    have h1 := h.red g i i
    rw [← hai, hr0, Matrix.diagonal_apply_eq] at h1
    have h2 : ‖((t g ^ wt1 i : (PadicAlgCl l)ˣ) : PadicAlgCl l)‖ = 1 := by
      rw [Units.val_zpow_eq_zpow_val, norm_zpow]
      have : ‖(t g : PadicAlgCl l)‖ = 1 := norm_unit c (D.Ψ g).isUnit
      rw [this, _root_.one_zpow]
    show ‖((a i g / t g ^ wt1 i : (PadicAlgCl l)ˣ) : PadicAlgCl l) - 1‖ < 1
    rw [Units.val_div_eq_div_val, div_sub_one (Units.ne_zero _), norm_div, h2, div_one]
    exact h1
  have hroot : ∀ i (g : D.η.ker), (r g).mat.charpoly = (r0 D.η D.ΨQ g).mat.charpoly → ∃ j, a i g = t g ^ wt1 j := by
    intro i g hg
    rw [ha, hr0] at hg
    obtain ⟨j, hj⟩ := root_of_charpoly _ _ hg i
    exact ⟨j, Units.ext hj⟩
  have hine : ∀ i (A : ValuationSubring Ω) (g : D.η.ker), (g : G ℚ Ω) ∈ Ine (F := ℚ) A → a i g = t g ^ wt1 i := by
    intro i A g hg
    by_cases hA : A.valuation (l : Ω) < 1
    · obtain ⟨hle, s, hs, hsu⟩ := hab A hA
      refine eq_above (U1 _) ((Ine (F := ℚ) A).subgroupOf D.η.ker) (a i) t i (hred i)
        (fun x hx => hroot i x ((pt_inertia_above hC D hM h A hA).1 x hx)) ⟨s, hle hs⟩ hs (fun hu => ?_) g hg
      have h1 := norm_unit c hsu
      rw [map_sub, map_pow, map_one] at h1
      exact absurd hu (not_lt.2 h1.ge)
    · obtain ⟨M, hMc⟩ := pt_inertia_away D hM h A hA
      refine eq_away (U1 _) ((Ine (F := ℚ) A).subgroupOf D.η.ker) (a i) t i (hred i)
        (fun x hx => hroot i x ?_) (fun x hx hu => ?_) g hg
      · have h1 : (r0 D.η D.ΨQ x).mat = (M : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) * (r x).mat *
            ((M⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) := by
          rw [hMc x hx x.2, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
        rw [h1, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      · have h1 : ¬ IsUnit ((D.Ψ x : c.O) - 1) := fun hx1 => by
          have h1 := norm_unit c hx1
          rw [map_sub, map_one] at h1
          exact absurd hu (not_lt.2 h1.ge)
        have h2 : barChar c.O D.Ψ x = 1 := by
          apply Units.ext
          show residue c.O (D.Ψ x : c.O) = 1
          rw [← sub_eq_zero, ← map_one (residue c.O), ← map_sub, residue_eq_zero_iff]
          exact h1
        have h3 : (x : G ℚ Ω) ∈ D.Kill := by
          refine ⟨A, hA, hx, SemidirectProduct.ext ?_ x.2⟩
          show tor _ (barChar c.O D.Ψ x) = 1
          rw [h2, map_one]
        have h4 := congrArg (fun y => GG.mat y 0 0) (hkill x h3)
        have h5 : (D.Ψ x : c.O) = 1 := by simpa [GG.mat, tor_val, wt1] using h4
        apply Units.ext
        show (D.ΨQ x : PadicAlgCl l) = 1
        rw [htv, h5, map_one]
  have hall : ∀ i g, a i g = t g ^ wt1 i := by
    intro i g
    have hk := char_eq_one D (a i / (zpowGroupHom (wt1 i)).comp t) ?_ (hred i)
      (fun A g hg => div_eq_one.2 (hine i A g hg))
    · exact div_eq_one.1 (DFunLike.congr_fun hk g)
    · have c1 : Continuous fun g : D.η.ker => (r g).mat i i :=
        (h.cont.comp continuous_subtype_val).matrix_elem i i
      have c2 : Continuous fun g : D.η.ker => (t g : PadicAlgCl l) :=
        Units.continuous_val.comp (hcont.comp continuous_subtype_val)
      refine (c1.div (c2.zpow₀ (wt1 i) fun g => Or.inl (Units.ne_zero _))
        fun g => zpow_ne_zero _ (Units.ne_zero _)).congr fun g => ?_
      show _ = ((a i g / t g ^ wt1 i : (PadicAlgCl l)ˣ) : PadicAlgCl l)
      rw [Units.val_div_eq_div_val, Units.val_zpow_eq_zpow_val, hai]
      rfl
  have hker : ∀ g ∈ D.η.ker, r g = r0 D.η D.ΨQ g := by
    intro g hg
    refine SemidirectProduct.ext (Units.ext ?_) (h.mult g)
    show (r (⟨g, hg⟩ : D.η.ker)).mat = (r0 D.η D.ΨQ (⟨g, hg⟩ : D.η.ker)).mat
    rw [ha, hr0]
    simp only [hall]
  have hc : r D.cc = r0 D.η D.ΨQ D.cc := by
    refine SemidirectProduct.ext (Units.ext ?_) (h.mult _)
    have h1 : D.ΨQ D.cc = 1 := by
      apply Units.ext
      rw [htv, hM.Ψc]
      simp
    rw [unitaryThreeReflection_left, h1, map_one]
    exact h.norm.atc
  refine MonoidHom.ext fun g => ?_
  rcases Int.units_eq_one_or (D.η g) with hg | hg
  · exact hker g hg
  · have h1 : g * D.cc ∈ D.η.ker := by
      rw [MonoidHom.mem_ker, map_mul, hg, hM.ηc]
      simp
    have h2 := hker _ h1
    rw [map_mul, map_mul, hc] at h2
    exact mul_right_cancel h2
