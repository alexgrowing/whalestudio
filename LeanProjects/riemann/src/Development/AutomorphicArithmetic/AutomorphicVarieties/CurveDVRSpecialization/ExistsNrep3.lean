import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.HostFrameEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PropagationTheoremGL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.MatGstar

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V
open Matrix
open scoped Pointwise

private def diagCh {D A : Type} [Group D] [CommRing A] (T : D →* Matrix (Fin 3) (Fin 3) A)
    (hT : ∀ g a b, b < a → T g a b = 0) (i : Fin 3) : D →* A where
  toFun g := T g i i
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, Matrix.mul_apply, Finset.sum_eq_single i]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h1 | h1
      · rw [hT g i b h1, zero_mul]
      · rw [hT h b i h1, mul_zero]
    · exact fun h => absurd (Finset.mem_univ _) h

private theorem ord_zero {D A : Type} [CommRing A] (T R : D → Matrix (Fin 3) (Fin 3) A)
    (hT : ∀ g a b, b < a → T g a b = 0) (P Q : Matrix (Fin 3) (Fin 3) A) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hR : ∀ g, R g = P * T g * Q) (g : Fin 3 → D) : Fr.ordProd R (fun i s => T s i i) g = 0 := by
  have h10 : ∀ s, T s 1 0 = 0 := fun s => hT s 1 0 (by decide)
  have h20 : ∀ s, T s 2 0 = 0 := fun s => hT s 2 0 (by decide)
  have h21 : ∀ s, T s 2 1 = 0 := fun s => hT s 2 1 (by decide)
  have conj : ∀ s (t : A), R s - t • (1 : Matrix (Fin 3) (Fin 3) A) = P * (T s - t • 1) * Q := by
    intro s t
    rw [hR, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hPQ]
  have key : (T (g 0) - T (g 0) 0 0 • (1 : Matrix (Fin 3) (Fin 3) A)) *
      ((T (g 1) - T (g 1) 1 1 • 1) * (T (g 2) - T (g 2) 2 2 • 1)) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.sub_apply, Matrix.one_apply, h10, h20, h21]
  simp only [Fr.ordProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  rw [conj, conj, conj]
  have e : P * (T (g 0) - T (g 0) 0 0 • 1) * Q * (P * (T (g 1) - T (g 1) 1 1 • 1) * Q *
      (P * (T (g 2) - T (g 2) 2 2 • 1) * Q)) =
      P * ((T (g 0) - T (g 0) 0 0 • 1) * ((T (g 1) - T (g 1) 1 1 • 1) * (T (g 2) - T (g 2) 2 2 • 1))) * Q := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q P, hQP, Matrix.one_mul, ← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
  rw [e, key, Matrix.mul_zero, Matrix.zero_mul]

private theorem descend {H Γ A : Type} [Group H] [TopologicalSpace H] [CompactSpace H] [Group Γ] [TopologicalSpace Γ]
    [T2Space Γ] [CommRing A] (I : Ideal A) (p : H →* Γ) (hp : Continuous p) (hs : Function.Surjective p)
    (r : H →* GG 3 A) (hk : p.ker ≤ r.ker) (hc : UnitaryThreeInertia.AdicCont I r) :
    ∃ r' : Γ →* GG 3 A, (∀ s, r' (p s) = r s) ∧ UnitaryThreeInertia.AdicCont I r' := by
  let r' : Γ →* GG 3 A :=
    p.liftOfRightInverse (Function.surjInv hs) (Function.rightInverse_surjInv hs) ⟨r, hk⟩
  have hr' : ∀ s, r' (p s) = r s := fun s => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ s
  refine ⟨r', hr', fun n => ?_⟩
  have hq : Topology.IsQuotientMap p := IsClosedMap.isQuotientMap hp.isClosedMap hp hs
  intro U
  have h := hc n U
  rw [← hq.isOpen_preimage]
  convert h using 1
  ext s
  simp [hr']

private theorem closed_one {H A : Type} [Group H] [TopologicalSpace H] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (r : H →* GG 3 A) (hc : UnitaryThreeInertia.AdicCont (maximalIdeal A) r) : IsClosed {s | (r s).mat = 1} := by
  have hne : maximalIdeal A ≠ ⊤ := (maximalIdeal.isMaximal A).ne_top
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal A) hne
  have e : {s | (r s).mat = 1} = ⋂ n : ℕ, {s | (r s).mat.map (Ideal.Quotient.mk (maximalIdeal A ^ n)) =
      (1 : Matrix (Fin 3) (Fin 3) A).map (Ideal.Quotient.mk (maximalIdeal A ^ n))} := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h n
      rw [h]
    · intro h
      ext i j
      rw [← sub_eq_zero]
      have hm : (r s).mat i j - (1 : Matrix (Fin 3) (Fin 3) A) i j ∈ ⨅ n, maximalIdeal A ^ n := by
        rw [Submodule.mem_iInf]
        intro n
        have := congrFun (congrFun (h n) i) j
        simp only [Matrix.map_apply] at this
        exact Ideal.Quotient.eq.mp this
      rw [hbot] at hm
      exact (Submodule.mem_bot _).mp hm
  rw [e]
  exact isClosed_iInter fun n => (hc n).isClosed_fiber _

private theorem z_diag {A : Type} [CommRing A] (X : Matrix (Fin 3) (Fin 3) A)
    (h01 : (X - Jmat A 3 * Xᵀ * Jmat A 3) 0 1 = 0) (h10 : (X - Jmat A 3 * Xᵀ * Jmat A 3) 1 0 = 0) (i j : Fin 3) (h : i ≠ j) :
    (X - Jmat A 3 * Xᵀ * Jmat A 3) i j = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [Jmat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.sub_apply, Matrix.transpose_apply, Fin.rev] <;>
    first
    | rfl
    | linear_combination h01
    | linear_combination -h01
    | linear_combination h10
    | linear_combination -h10
    | exact absurd rfl h

private theorem upl_compact (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (L : Type) [Field L] [NumberField L]
    [Algebra L Ω] : CompactSpace (upl Ω L) := by
  have stab : ∀ z : Ω, IsClosed {s : G ℚ Ω | s z = z} := by
    intro z
    have hz : IsIntegral ℚ z := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) z).isIntegral
    haveI := IntermediateField.adjoin.finiteDimensional hz
    have hle : (IntermediateField.adjoin ℚ {z}).fixingSubgroup ≤ MulAction.stabilizer (G ℚ Ω) z := by
      intro s hs
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
      exact (IntermediateField.mem_fixingSubgroup_iff _ s).mp hs z
        (IntermediateField.mem_adjoin_simple_self ℚ z)
    have hopen := Subgroup.isOpen_mono hle (IntermediateField.fixingSubgroup_isOpen _)
    have hcl := Subgroup.isClosed_of_isOpen _ hopen
    convert hcl using 1
    ext s
    simp [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
  have hcl : IsClosed ((upl Ω L : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
    have e : ((upl Ω L : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) =
        ⋂ x ∈ maximalRealSubfield L, {s : G ℚ Ω | s (algebraMap L Ω x) = algebraMap L Ω x} := by
      ext s
      simp [upl]
      exact Iff.rfl
    rw [e]
    exact isClosed_biInter fun x _ => stab _
  exact isCompact_iff_compactSpace.mp hcl.isCompact

private theorem mat_mul {A : Type} [CommRing A] (x y : GG 3 A) (hx : x.right = 1) : (x * y).mat = x.mat * y.mat := by
  simp [GG.mat, hx]

private theorem conj_mat {G A : Type} [Group G] [CommRing A] (h : GL (Fin 3) A) (r : G →* GG 3 A) (s : G)
    (hs : (r s).right = 1) : (conjBy h⁻¹ r s).mat = (h⁻¹ : GL (Fin 3) A).val * (r s).mat * h.val := by
  simp [conjBy, GG.mat, MulAut.conj_apply, hs, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    mul_assoc]

private theorem local_chars {G H O A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    [TopologicalSpace H] [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A] [Algebra O A]
    (η : G →* ℤˣ) (Ψ : G →* Oˣ) (D I : Subgroup G) (r : G →* GG 3 A) (hr : UnitaryThreeInertia.Red η Ψ r)
    (hc : UnitaryThreeInertia.AdicCont (maximalIdeal A) r)
    (ht : UnitaryThreeInertia.CondT (η.comp D.subtype) (Ψ.comp D.subtype) (I.subgroupOf D) (r.comp D.subtype))
    (φ : H →* G) (hφ : Continuous φ) (γ : G) (hγ : η γ = 1) (h1 : ∀ g, η (φ g) = 1) (hD : ∀ g, γ⁻¹ * φ g * γ ∈ D) :
    ∃ ψ : Fin 3 → H →* Aˣ, (∀ g, Fr.ordProd (fun s => (r (φ s)).mat) (fun i s => (ψ i s : A)) g = 0) ∧
      (∀ i, Alg.AdicCont (maximalIdeal A) fun g => (ψ i g : A)) ∧
      (∀ i g, residue A (ψ i g) = residue A (algebraMap O A (UnitaryThreeInertia.psi Ψ i (φ g)))) ∧
      ∀ i g, γ⁻¹ * φ g * γ ∈ I → (ψ i g : A) = algebraMap O A (UnitaryThreeInertia.psi Ψ i (φ g)) := by
  obtain ⟨h, hh, htri⟩ := ht
  have hmult : ∀ g, (r g).right = η g := hr.mult
  let d : H →* D :=
    { toFun := fun g => ⟨γ⁻¹ * φ g * γ, hD g⟩
      map_one' := by
        ext
        simp
      map_mul' := by
        intro a b
        ext
        simp only [map_mul, Subgroup.coe_mul]
        group }
  have hd : ∀ g, ((d g : D) : G) = γ⁻¹ * φ g * γ := fun _ => rfl
  have hd_eta : ∀ g, η ((d g : D) : G) = 1 := by
    intro g
    rw [hd, map_mul, map_mul, map_inv, hγ, h1]
    simp
  have hγinv : η γ⁻¹ = 1 := by rw [map_inv, hγ, inv_one]
  let R' := conjBy h⁻¹ (r.comp D.subtype)
  have hright : ∀ x : D, (R' x).right = (r x).right := by
    intro x
    simp [R', conjBy, MulAut.conj_apply]
  have hrd : ∀ g, (r ((d g : D) : G)).right = 1 := fun g => by rw [hmult]; exact hd_eta g
  let Tm : H →* Matrix (Fin 3) (Fin 3) A :=
    { toFun := fun g => (R' (d g)).mat
      map_one' := by
        simp [GG.mat]
      map_mul' := by
        intro a b
        rw [map_mul, map_mul, mat_mul _ _ (by rw [hright]; exact hrd a)] }
  have hTm : ∀ g, Tm g = (R' (d g)).mat := fun _ => rfl
  have hTconj : ∀ g, Tm g = (h⁻¹ : GL (Fin 3) A).val * (r ((d g : D) : G)).mat * h.val := by
    intro g
    rw [hTm]
    exact conj_mat h (r.comp D.subtype) (d g) (hrd g)
  have hwt : ∀ a b : Fin 3, b < a → wt a b < 0 := by
    unfold wt wt1
    decide
  have hT : ∀ g a b, b < a → Tm g a b = 0 := by
    intro g a b hab
    refine htri.tri (d g) ?_ a b (hwt a b hab)
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact hd_eta g
  let ψ : Fin 3 → H →* Aˣ := fun i => (diagCh Tm hT i).toHomUnits
  have hψ : ∀ i g, (ψ i g : A) = Tm g i i := fun _ _ => rfl
  have hrγ : (r γ).right = 1 := by rw [hmult, hγ]
  have hrγi : (r γ⁻¹).right = 1 := by rw [hmult, hγinv]
  have hγγ : (r γ).mat * (r γ⁻¹).mat = 1 := by
    rw [← mat_mul _ _ hrγ, ← map_mul, mul_inv_cancel, map_one]
    simp [GG.mat]
  have hγγ' : (r γ⁻¹).mat * (r γ).mat = 1 := by
    rw [← mat_mul _ _ hrγi, ← map_mul, inv_mul_cancel, map_one]
    simp [GG.mat]
  have hhh : h.val * (h⁻¹ : GL (Fin 3) A).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hhh' : (h⁻¹ : GL (Fin 3) A).val * h.val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin 3) (Fin 3) A, P = (r γ).mat * h.val := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin 3) (Fin 3) A, Q = (h⁻¹ : GL (Fin 3) A).val * (r γ⁻¹).mat := ⟨_, rfl⟩
  have hPQ : P * Q = 1 := by
    rw [hP, hQ, Matrix.mul_assoc, ← Matrix.mul_assoc h.val, hhh, Matrix.one_mul, hγγ]
  have hQP : Q * P = 1 := by
    rw [hP, hQ, Matrix.mul_assoc, ← Matrix.mul_assoc (r γ⁻¹).mat, hγγ', Matrix.one_mul, hhh']
  have hφd : ∀ g, φ g = γ * ((d g : D) : G) * γ⁻¹ := by
    intro g
    rw [hd]
    group
  have hR : ∀ g, (r (φ g)).mat = P * Tm g * Q := by
    intro g
    rw [hφd g, map_mul, map_mul, mul_assoc, mat_mul _ _ hrγ, mat_mul _ _ (hrd g), hTconj, hP, hQ]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc h.val (h⁻¹ : GL (Fin 3) A).val, hhh, Matrix.one_mul,
      ← Matrix.mul_assoc h.val (h⁻¹ : GL (Fin 3) A).val, hhh, Matrix.one_mul]
  have hT' : ∀ g, Tm g = Q * (r (φ g)).mat * P := by
    intro g
    rw [hR, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQP, Matrix.one_mul, Matrix.mul_assoc, hQP,
      Matrix.mul_one]
  have req : ∀ x y : A, x - y ∈ maximalIdeal A → residue A x = residue A y := by
    intro x y hxy
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hxy
  have hone : (1 : Matrix (Fin 3) (Fin 3) A).map (residue A) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hmh : h.val.map (residue A) = 1 := by
    rw [← hone]
    ext a b
    exact req _ _ (by simpa [Matrix.sub_apply] using hh a b)
  have hmhi : (h⁻¹ : GL (Fin 3) A).val.map (residue A) = 1 := by
    have e := congrArg (fun X : Matrix (Fin 3) (Fin 3) A => X.map (residue A)) hhh'
    simp only [Matrix.map_mul, hmh, hone, Matrix.mul_one] at e
    exact e
  have hΨ : ∀ g i, UnitaryThreeInertia.psi Ψ i ((d g : D) : G) = UnitaryThreeInertia.psi Ψ i (φ g) := by
    intro g i
    unfold UnitaryThreeInertia.psi
    rw [hd, map_mul, map_mul, map_inv, mul_comm (Ψ γ)⁻¹, inv_mul_cancel_right]
  have hres : ∀ i g, residue A (ψ i g : A) = residue A (algebraMap O A (UnitaryThreeInertia.psi Ψ i (φ g))) := by
    intro i g
    have e0 : (Tm g).map (residue A) = (r ((d g : D) : G)).mat.map (residue A) := by
      rw [hTconj g, Matrix.map_mul, Matrix.map_mul, hmh, hmhi, Matrix.mul_one, Matrix.one_mul]
    have e1 : residue A (Tm g i i) = residue A ((r ((d g : D) : G)).mat i i) :=
      congrFun (congrFun e0 i) i
    rw [hψ, e1, ← hΨ]
    refine req _ _ ?_
    have e2 := hr.red ((d g : D) : G) i i
    have e3 : (r0 η Ψ ((d g : D) : G)).mat = ((tor O (Ψ ((d g : D) : G)) : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) := rfl
    rw [Matrix.sub_apply, Matrix.map_apply, e3, tor_val, Matrix.diagonal_apply_eq] at e2
    exact e2
  refine ⟨ψ, fun g => ord_zero Tm (fun s => (r (φ s)).mat) hT P Q hPQ hQP hR g, ?_, hres, ?_⟩
  · intro i N
    have e : (fun g => Ideal.Quotient.mk (maximalIdeal A ^ N) (ψ i g : A)) =
        (fun M : Matrix (Fin 3) (Fin 3) (A ⧸ maximalIdeal A ^ N) =>
          (Q.map (Ideal.Quotient.mk (maximalIdeal A ^ N)) * M * P.map (Ideal.Quotient.mk (maximalIdeal A ^ N))) i i) ∘
        (fun g => (r (φ g)).mat.map (Ideal.Quotient.mk (maximalIdeal A ^ N))) := by
      funext g
      simp only [Function.comp, hψ]
      rw [hT' g, ← Matrix.map_mul, ← Matrix.map_mul]
      rfl
    rw [e]
    exact ((hc N).comp_continuous hφ).comp _
  · intro i g hg
    have hmem : d g ∈ I.subgroupOf D := by
      rw [Subgroup.mem_subgroupOf]
      exact hg
    have e := htri.ine (d g) hmem (hd_eta g) i
    rw [hψ, hTm, e, ← hΨ]
    rfl

theorem UpperTheory.V.Pr.exists_nrep3 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
      {L : Type} [Field L] [NumberField L] [Algebra L Ω] {Φ : Fr.Frame l (ResidueField O)} (k : GalLink η Ψ σ g₁ B M L Φ) [CharP (ResidueField O) l] {C₀ : ℕ}, Φ.Ok C₀ → l ∣ M → σ * σ = 1 →
    ∀ {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [Algebra O A] [IsLocalHom (algebraMap O A)] (r : G ℚ Ω →* GG 3 A), OrdPt l η Ψ σ g₁ B r → ∃ ρ : Fr.NRep Φ 3 A, IsLiftA O ρ ∧ (∀ s : G L Ω, ρ.r (k.p0 s) = (r (Base.galEmb ℚ L Ω s)).mat) ∧
      ∀ v i, ∀ g ∈ Φ.Iv v, (ρ.ψ v i g : A) = algebraMap O A (UnitaryThreeInertia.psi Ψ i (k.j v g)) := by
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ Φ k _ C₀ hOk hlM hσ A _ _ _ _ _ _ r hr
  haveI := upl_compact Ω L
  let ru : ↥(upl Ω L) →* GG 3 A := r.comp (upl Ω L).subtype
  have ru_cont : UnitaryThreeInertia.AdicCont (maximalIdeal A) ru := fun n =>
    (hr.cont n).comp_continuous continuous_subtype_val
  have hk : k.p.ker ≤ ru.ker := by
    intro s hs
    have hs1 : k.p s = 1 := hs
    have hη : η s = 1 := by
      rw [← k.del s, hs1, map_one]
    have hN : Subgroup.normalClosure
        {s : ↥(upl Ω L) | ∃ B' : ValuationSubring Ω, ¬B'.valuation (l : Ω) < 1 ∧ (s : G ℚ Ω) ∈ Ine B' ∧
          η s = 1 ∧ (barChar O Ψ) s = 1} ≤ ru.ker := by
      refine Subgroup.normalClosure_le_normal ?_
      rintro t ⟨B', hB', hI, ht1, hb⟩
      have hΨ : Ψ t = 1 := k.teich B' hB' t ⟨hI, t.2⟩ hb
      exact hr.away B' hB' t hI ht1 hΨ
    have hcl := closed_one ru ru_cont
    rw [k.p_ker] at hs
    have hs2 : s ∈ closure ((Subgroup.normalClosure
        {s : ↥(upl Ω L) | ∃ B' : ValuationSubring Ω, ¬B'.valuation (l : Ω) < 1 ∧ (s : G ℚ Ω) ∈ Ine B' ∧
          η s = 1 ∧ (barChar O Ψ) s = 1} : Subgroup ↥(upl Ω L)) : Set ↥(upl Ω L)) := by
      rw [← Subgroup.topologicalClosure_coe]
      exact hs
    have hmat : (ru s).mat = 1 := by
      refine closure_minimal (fun t ht => ?_) hcl hs2
      have h1 : ru t = 1 := hN ht
      show (ru t).mat = 1
      rw [h1]
      rfl
    rw [MonoidHom.mem_ker]
    refine SemidirectProduct.ext (Units.ext hmat) ?_
    rw [SemidirectProduct.one_right]
    exact (hr.red.mult s).trans hη
  obtain ⟨r', hr', hc'⟩ := descend (maximalIdeal A) k.p k.p_cont k.p_surj ru hk ru_cont
  have rt : ∀ x : Φ.Γ, (r' x).right = Φ.del x := by
    intro x
    obtain ⟨s, rfl⟩ := k.p_surj x
    rw [hr', k.del]
    exact hr.red.mult s
  have rt0 : ∀ g : Φ.G0, (r' g).right = 1 := fun g => (rt g).trans g.2
  let ρr : Φ.G0 →* Matrix (Fin 3) (Fin 3) A :=
    { toFun := fun g => (r' g).mat
      map_one' := by
        show (r' ((1 : Φ.G0) : Φ.Γ)).mat = 1
        rw [OneMemClass.coe_one, map_one]
        rfl
      map_mul' := fun g h => by
        show (r' ((g * h : Φ.G0) : Φ.Γ)).mat = (r' g).mat * (r' h).mat
        rw [Subgroup.coe_mul, map_mul]
        exact mat_mul _ _ (rt0 g) }
  have hρr : ∀ g : Φ.G0, ρr g = (r' g).mat := fun _ => rfl
  obtain ⟨hσu, hpσ⟩ := k.c
  obtain ⟨hg1u, hpg1⟩ := k.g0
  have rσ : r' Φ.c = r σ := by rw [← hpσ, hr']; rfl
  have rg1 : r' Φ.g0 = r g₁ := by rw [← hpg1, hr']; rfl
  have atc : (r' Φ.c).mat = 1 := by rw [rσ]; exact hr.norm.atc
  have rtc : (r' Φ.c).right = -1 := by rw [rt]; exact hOk.del_c
  have cinv : Φ.c⁻¹ = Φ.c := inv_eq_of_mul_eq_one_right hOk.c_sq
  have star_eq : ∀ g : Φ.G0, ((Φ.star g : Φ.G0) : Φ.Γ) = gstar Φ.c (g : Φ.Γ) := by
    intro g
    show ((MulAut.conjNormal Φ.c) g⁻¹ : Φ.Γ) = Φ.c * (g : Φ.Γ)⁻¹ * Φ.c
    rw [MulAut.conjNormal_apply, cinv]
    rfl
  have pol : ∀ g : Φ.G0, ρr (Φ.star g) = Jmat A 3 * (ρr g)ᵀ * Jmat A 3 := by
    intro g
    rw [hρr, hρr, star_eq]
    exact (mat_gstar r' Φ.c g atc rtc (rt0 g)).1
  have diag : ∀ i j : Fin 3, i ≠ j → (ρr Φ.g0 - ρr (Φ.star Φ.g0)) i j = 0 := by
    intro i j hij
    have hσr : (r σ).right = -1 := by rw [← rσ]; exact rtc
    have hg1r : (r g₁).right = 1 := by rw [← rg1]; exact rt0 _
    have hz := (mat_gstar r σ g₁ hr.norm.atc hσr hg1r).1
    have e : ρr Φ.g0 - ρr (Φ.star Φ.g0) = (r g₁).mat - Jmat A 3 * (r g₁).matᵀ * Jmat A 3 := by
      rw [pol, hρr, rg1]
    rw [e]
    have z12 := hr.norm.z12
    have z21 := hr.norm.z21
    simp only [zmat, hz] at z12 z21
    exact z_diag _ z12 z21 i j hij
  have LC : ∀ v : Φ.V, ∃ ψ : Fin 3 → Φ.Gv v →* Aˣ,
      (∀ g, Fr.ordProd (fun s => (r (k.j v s)).mat) (fun i s => (ψ i s : A)) g = 0) ∧
      (∀ i, Alg.AdicCont (maximalIdeal A) fun g => (ψ i g : A)) ∧
      (∀ i g, residue A (ψ i g) = residue A (algebraMap O A (UnitaryThreeInertia.psi Ψ i (k.j v g)))) ∧
      ∀ i, ∀ g ∈ Φ.Iv v, (ψ i g : A) = algebraMap O A (UnitaryThreeInertia.psi Ψ i (k.j v g)) := by
    intro v
    obtain ⟨γ, hγ, hpl⟩ := k.pl_conj v
    have hlift : IsLift (RingEquiv.refl ℚ) (γ : Ω ≃ₐ[ℚ] Ω).toRingEquiv := fun x => γ.commutes x
    have hmemiff : ∀ x : Ω, (γ : Ω ≃ₐ[ℚ] Ω).toRingEquiv x ∈ k.pl v ↔ x ∈ B := by
      intro x
      rw [hpl]
      exact ValuationSubring.smul_mem_pointwise_smul_iff
    have hconj : ∀ g : Φ.Gv v, γ⁻¹ * ((k.j v g : G ℚ Ω)) * γ = conjGal hlift (k.j v g) := by
      intro g
      apply AlgEquiv.ext
      intro x
      rfl
    have hD : ∀ g, γ⁻¹ * ((upl Ω L).subtype.comp (k.j v)) g * γ ∈ Dec B := by
      intro g
      show γ⁻¹ * ((k.j v g : G ℚ Ω)) * γ ∈ Dec B
      rw [hconj]
      exact conjGal_mem_Dec hlift hmemiff ((k.j_range v _).mp ⟨g, rfl⟩)
    have h1 : ∀ g, η (((upl Ω L).subtype.comp (k.j v)) g) = 1 := by
      intro g
      show η (k.j v g : G ℚ Ω) = 1
      rw [← k.del, ← k.j_loc]
      exact (Φ.loc0 v g).2
    obtain ⟨ψ, h1', h2', h3', h4'⟩ := local_chars η Ψ (Dec B) (Ine B) r hr.red hr.cont hr.ord
      ((upl Ω L).subtype.comp (k.j v)) (continuous_subtype_val.comp (k.j_cont v)) γ hγ h1 hD
    refine ⟨ψ, h1', h2', h3', fun i g hg => h4' i g ?_⟩
    show γ⁻¹ * ((k.j v g : G ℚ Ω)) * γ ∈ Ine B
    rw [hconj]
    exact conjGal_mem_Ine hlift hmemiff ((k.j_ine v g).mp hg)
  choose ψ hψ1 hψ2 hψ3 hψ4 using LC
  have rloc : ∀ v (s : Φ.Gv v), ρr (Φ.loc0 v s) = (r (k.j v s)).mat := by
    intro v s
    rw [hρr]
    show (r' (Φ.loc v s)).mat = _
    rw [k.j_loc, hr']
    rfl
  have redg : ∀ (s : G ℚ Ω) (i j : Fin 3), residue A ((r s).mat i j) =
      residue A (algebraMap O A ((Matrix.diagonal fun a => ((Ψ s ^ wt1 a : Oˣ) : O)) i j)) := by
    intro s i j
    have h0 : (r0 η Ψ s).mat = Matrix.diagonal fun a => ((Ψ s ^ wt1 a : Oˣ) : O) := tor_val (Ψ s)
    have h := hr.red.red s i j
    rw [h0, Matrix.sub_apply, Matrix.map_apply] at h
    rw [← sub_eq_zero, ← map_sub]
    exact (residue_eq_zero_iff _).mpr h
  have bar_eq : ∀ (s : ↥(upl Ω L)) (i : Fin 3),
      ResidueField.map (algebraMap O A) ((Φ.Ψ (k.p s) ^ Fr.w 3 i : (ResidueField O)ˣ) : ResidueField O) =
        residue A (algebraMap O A ((Ψ s ^ wt1 i : Oˣ) : O)) := by
    intro s i
    have hw : Fr.w 3 i = wt1 i := by simp [Fr.w, wt1]
    rw [k.psi, hw, barChar, MonoidHom.comp_apply, ← map_zpow, Units.coe_map]
    simp [ResidueField.map_residue]
  refine ⟨⟨ρr, ψ, pol, diag, fun v g => ?_⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩, ?_, hψ4⟩
  · have e : (fun s => ρr (Φ.loc0 v s)) = fun s => (r (k.j v s)).mat := funext (rloc v)
    show Fr.ordProd (fun s => ρr (Φ.loc0 v s)) (fun i s => ((ψ v i s : Aˣ) : A)) g = 0
    rw [e]
    exact hψ1 v g
  · intro i j N
    have h := (hc' N).comp_continuous (continuous_subtype_val : Continuous (fun g : Φ.G0 => (g : Φ.Γ)))
    exact h.comp (fun X => X i j)
  · intro v i
    exact hψ2 v i
  · intro g i
    obtain ⟨s, hs⟩ := k.p_surj (g : Φ.Γ)
    show residue A (ρr g i i) = _
    rw [hρr, ← hs, hr', bar_eq]
    show residue A ((r s).mat i i) = _
    rw [redg, Matrix.diagonal_apply_eq]
  · intro v i g
    show residue A ((ψ v i g : Aˣ) : A) = _
    rw [hψ3, Fr.Frame.loc, MonoidHom.comp_apply]
    show _ = ResidueField.map (algebraMap O A) ((Φ.Ψ (Φ.loc v g) ^ Fr.w 3 i : (ResidueField O)ˣ) : ResidueField O)
    rw [k.j_loc, bar_eq]
    rfl
  · intro g i j hij
    obtain ⟨s, hs⟩ := k.p_surj (g : Φ.Γ)
    show residue A (ρr g i j) = 0
    rw [hρr, ← hs, hr']
    show residue A ((r s).mat i j) = 0
    rw [redg, Matrix.diagonal_apply_ne _ hij, map_zero, map_zero]
  · intro s
    rw [hρr]
    show (r' (k.p _)).mat = _
    rw [hr']
    rfl
