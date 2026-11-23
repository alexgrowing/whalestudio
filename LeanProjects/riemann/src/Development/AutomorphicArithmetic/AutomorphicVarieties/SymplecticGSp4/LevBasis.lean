import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.SymplecticGSp4
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtInSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EptInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SplAdjUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGeneratingCharacters
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem lev_basis {ι k : Type} [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ} (X : ι → Matrix (Fin n) (Fin n) k)
    (hc : ∀ a b, Commute (X a) (X b)) (hf : ∀ a, IsOfFinOrder (X a)) :
    ∃ (P : GL (Fin n) k) (d : ι → Fin n → k), ∀ a, X a * P = P * Matrix.diagonal (d a) := by
  classical
  let f : ι → Module.End k (Fin n → k) := fun a => Matrix.toLinAlgEquiv' (X a)
  have hss : ∀ a, (f a).IsFinitelySemisimple := fun a => by
    obtain ⟨m, hm, h1⟩ := isOfFinOrder_iff_pow_eq_one.1 (hf a)
    refine (Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (Polynomial.separable_X_pow_sub_C (1 : k) (Nat.cast_ne_zero.2 hm.ne') one_ne_zero).squarefree ?_).isFinitelySemisimple
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, f]
    rw [← map_pow, h1, map_one, sub_self]
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
    (fun a b _ => (hc a b).map _) fun a => Module.End.iSup_maxGenEigenspace_eq_top _
  simp only [fun a => (hss a).maxGenEigenspace_eq_eigenspace] at htop
  let S : Set (Fin n → k) := {v | ∃ d : ι → k, ∀ a, (X a).mulVec v = d a • v}
  have hS : Submodule.span k S = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun d v hv => Submodule.subset_span ⟨d, fun a => ?_⟩
    exact Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hv a)
  obtain ⟨t, ht, hsp, hli⟩ := exists_linearIndependent k S
  let b₀ : Module.Basis t k (Fin n → k) := Module.Basis.mk hli (by rw [Subtype.range_coe, hsp, hS])
  let b := b₀.reindex (b₀.indexEquiv (Pi.basisFun k (Fin n)))
  have hb : ∀ i, b i ∈ S := fun i => by
    rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
    exact ht (Subtype.coe_prop _)
  choose d hd using hb
  haveI := (Pi.basisFun k (Fin n)).invertibleToMatrix b
  refine ⟨unitOfInvertible ((Pi.basisFun k (Fin n)).toMatrix b), fun a i => d i a, fun a => ?_⟩
  ext i j
  have := congrFun (hd j a) i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
  rw [Matrix.mul_diagonal]
  simp [Matrix.mul_apply, Module.Basis.toMatrix_apply, this, mul_comm]

private theorem lev_diag {Γ A k : Type} [Group Γ] [CommGroup A] [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ}
    (r : Γ →* GL (Fin n) k) (H : Subgroup Γ) (φ : Γ →* A) (hφ : ∀ s, IsOfFinOrder (φ s))
    (hr : ∀ s ∈ H, φ s = 1 → r s = 1) :
    ∃ χ : Fin n → Γ →* kˣ, (∀ i s, φ s = 1 → χ i s = 1) ∧ Af.IsDiagOn r H χ := by
  obtain ⟨P, d, hP⟩ := lev_basis (fun s : H => (r s : Matrix (Fin n) (Fin n) k)) (fun a b => by
      have h := hr ((a : Γ) * b * ((b : Γ) * a)⁻¹) (mul_mem (mul_mem a.2 b.2) (inv_mem (mul_mem b.2 a.2))) (by
        rw [map_mul, map_inv, map_mul, map_mul, mul_comm (φ a), mul_inv_cancel])
      rw [map_mul, map_inv, mul_inv_eq_one, map_mul, map_mul] at h
      exact congrArg Units.val h) fun a => by
    obtain ⟨m, hm, h1⟩ := isOfFinOrder_iff_pow_eq_one.1 (hφ a)
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, ?_⟩
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hr _ (pow_mem a.2 m) (by rw [map_pow, h1]), Units.val_one]
  have hd : ∀ s : H, ((P⁻¹ * r s * P : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = Matrix.diagonal (d s) := fun s => by
    rw [Units.val_mul, Units.val_mul, mul_assoc, hP, Units.inv_mul_cancel_left]
  let κ : Fin n → H →* kˣ := fun i => MonoidHom.toHomUnits
    { toFun := fun s => d s i
      map_one' := by simpa using (congrFun (congrFun (hd 1) i) i).symm
      map_mul' := fun s t => by
        have h : (P⁻¹ * r (s * t : H) * P : GL (Fin n) k) = (P⁻¹ * r s * P) * (P⁻¹ * r t * P) := by
          rw [Subgroup.coe_mul, map_mul]
          group
        have h1 := hd (s * t)
        rw [h, Units.val_mul, hd, hd, Matrix.diagonal_mul_diagonal] at h1
        simpa using (congrFun (congrFun h1 i) i).symm }
  have hsurj := (φ.comp H.subtype).rangeRestrict_surjective
  have hker : ∀ i, (φ.comp H.subtype).rangeRestrict.ker ≤ (κ i).ker := fun i s hs => by
    have h1 := hd s
    rw [hr s s.2 (congrArg Subtype.val hs), mul_one, inv_mul_cancel] at h1
    apply Units.ext
    show d s i = 1
    simpa using (congrFun (congrFun h1 i) i).symm
  choose χ hχ using fun i => GlobalTheory.PrimaryCharacter.exists_extend_of_injective (φ.comp H.subtype).range.subtype
    (Subgroup.subtype_injective _) ((φ.comp H.subtype).rangeRestrict.liftOfSurjective hsurj ⟨κ i, hker i⟩)
  refine ⟨fun i => (χ i).comp φ, fun i s hs => by rw [MonoidHom.comp_apply, hs, map_one], P⁻¹, fun s hs => ?_⟩
  rw [inv_inv, hd ⟨s, hs⟩]
  congr 1
  funext i
  have h := hχ i ((φ.comp H.subtype).rangeRestrict ⟨s, hs⟩)
  rw [MonoidHom.liftOfRightInverse_comp_apply] at h
  exact (congrArg Units.val h).symm

private theorem lev_place {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {p : ℕ} (hp : p.Prime)
    {A : ValuationSubring Ω} (hA : A.valuation (p : Ω) < 1) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    IsPlaceOver A w := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨p1, p2, p3, -⟩ := places ℚ Ω p A
  obtain ⟨v, hv⟩ := p1 fun h => (p2 h).2 hA
  have hpr : Prime (p : 𝓞 ℚ) := by
    have e : (p : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (p : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr (Nat.prime_iff_prime_int.1 hp)
  have hm : (Ideal.span {(p : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpr.ne_zero).2 hpr).isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)
  have e : v = w := HeightOneSpectrum.ext
    ((hm.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 ((p3 v hv).1 hA))).symm.trans
      (hm.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hw)))
  exact e ▸ hv

open Matrix in
private theorem lev_dual {k : Type} [Field k] : ∃ P : GL (Fin 4) k, ∀ (ν : k) (X : M4 k), IsGSp ν X →
    Xᵀ * (P : M4 k) * X = ν • (P : M4 k) := by
  let J : M4 k := !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]
  have hJ : J * -J = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply, Fin.sum_univ_four]
  refine ⟨⟨J, -J, hJ, by rw [neg_mul, ← mul_neg, hJ]⟩, fun ν X h => ?_⟩
  have h1 : Xᵀ * J = J * adj X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev]
  show Xᵀ * J * X = ν • J
  rw [h1, mul_assoc, h, Matrix.mul_smul, mul_one]

theorem UpperTheory.V.GradeZeroInterpolatingElement.level :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ N : ℕ, 1 ≤ N → Af.KillsMu N D.ψ → Af.KillsMu N D.ξ → Af.KillsMu N D.om → ∀ r, D.EPt r → Af.Level l N ![(D.e : ℤ) + 1, D.e, 1, 0] r.toHomUnits ∧ ∃ θ, Af.IsCycWt l ((D.e : ℤ) + 1) θ ∧ Af.DualTw r.toHomUnits θ ∧ ∀ g, (θ g : PadicAlgCl l) = ((D.th g : c.O) : PadicAlgCl l) := by
  intro Ω _ _ _ l hl c D hD N hN hψ hξ hom r hr
  obtain ⟨hmult, hunr, -, -, hP, -⟩ := ptIn D hD _ r hr
  have hcont := (eptInt D hD r hr).1
  let m : c.Oˣ →* (PadicAlgCl l)ˣ := Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom
  have hcyc : ∀ s : G ℚ Ω, GlobalTheory.GalOfCusp.cycBar ℚ Ω l s = m (chiO ℚ Ω l c.O s) := fun s => Units.ext rfl
  let χ₀ : Fin 4 → G ℚ Ω →* c.Oˣ := ![D.om⁻¹ * D.ξ * D.ψ, D.ψ, D.om⁻¹ * D.ξ, 1]
  have hχ₀ : ∀ i s, D.ψ s = 1 → D.ξ s = 1 → D.om s = 1 → χ₀ i s = 1 := fun i s h1 h2 h3 => by
    fin_cases i <;> simp [χ₀, h1, h2, h3]
  have hps : ∀ i s, D.ps i s = chiO ℚ Ω l c.O s ^ (![(D.e : ℤ) + 1, D.e, 1, 0] i) * χ₀ i s := fun i s => by
    fin_cases i <;> simp [χ₀, Raw.ps, Raw.th, Raw.al, Raw.Psi, Chr.Psi, zpow_add_one, mul_comm, mul_left_comm, mul_assoc]
  have hK : ∀ i, Af.KillsMu N (m.comp (χ₀ i)) := fun i s hs => by
    rw [MonoidHom.comp_apply, hχ₀ i s (hψ s hs) (hξ s hs) (hom s hs), map_one]
  refine ⟨⟨?_, fun w hw => ?_, fun w hw => ?_⟩, m.comp D.th, ⟨N, m.comp (χ₀ 0), hN, hK 0, ?_⟩, ?_, fun _ => rfl⟩
  · exact Units.continuous_iff.2 ⟨hcont, hcont.comp continuous_inv⟩
  · let φ := D.ψ.prod (D.ξ.prod D.om)
    have hφ : ∀ s, IsOfFinOrder (φ s) := fun s => by
      haveI : Finite (G ℚ Ω ⧸ D.ψ.ker) := Subgroup.quotient_finite_of_isOpen _ hD.psi_open
      haveI : Finite (G ℚ Ω ⧸ D.ξ.ker) := Subgroup.quotient_finite_of_isOpen _ hD.xi_open
      refine IsOfFinOrder.prod_mk ?_ (IsOfFinOrder.prod_mk ?_ ?_)
      · exact (QuotientGroup.kerLift D.ψ).isOfFinOrder (isOfFinOrder_of_finite (s : G ℚ Ω ⧸ D.ψ.ker))
      · exact (QuotientGroup.kerLift D.ξ).isOfFinOrder (isOfFinOrder_of_finite (s : G ℚ Ω ⧸ D.ξ.ker))
      · exact isOfFinOrder_iff_pow_eq_one.2 ⟨l - 1, Nat.sub_pos_of_lt hl.out.one_lt, DFunLike.congr_fun hD.om_pow s⟩
    obtain ⟨A, hA, h⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ ∀ s ∈ Ine (F := ℚ) A, φ s = 1 → r s = 1 := by
      obtain ⟨B, hB⟩ := exists_isPlaceOver Ω w
      by_cases hT : Raw.Away D.T B
      · refine ⟨B, hB, fun s hs h1 => hunr B hT s hs ?_⟩
        have h2 : cycZ ℚ Ω l s = 1 := (places ℚ Ω l B).2.2.2 (hT l (Finset.mem_insert_self _ _)) hs
        have h3 : ∀ i, D.ps i s = 1 := fun i => by
          rw [hps, hχ₀ i s (congrArg Prod.fst h1) (congrArg (·.2.1) h1) (congrArg (·.2.2) h1), chiO, MonoidHom.comp_apply, h2,
            map_one, one_zpow, mul_one]
        have h4 : D.r0 s = 1 := by
          show Matrix.diagonal (fun i => (D.ps i s : c.O)) = 1
          simp only [h3, Units.val_one, Matrix.diagonal_one]
        show (residue c.O).mapMatrix (D.r0 s) = 1
        rw [h4, map_one]
      · obtain ⟨p, hp, hB'⟩ : ∃ p ∈ D.T, B.valuation (p : Ω) < 1 := by simpa [Raw.Away] using hT
        have hpw : (p : 𝓞 ℚ) ∈ w.asIdeal := (hB _).1 (by simpa using hB')
        have hpb : p ∈ D.Sb := (Finset.mem_insert.1 hp).resolve_left fun e => hw (e ▸ hpw)
        have hpp := ((facts D hD).1 p hpb).1
        exact ⟨D.pl p, lev_place hpp (hD.pl_over p hpp) hpw, fun s hs h1 =>
          (hP p hpb).2 ⟨s, hs.1⟩ ⟨hs, congrArg Prod.fst h1⟩⟩
    obtain ⟨χ, h1, h2⟩ := lev_diag r.toHomUnits (Ine (F := ℚ) A) φ hφ fun s hs e => Units.ext (h s hs e)
    exact ⟨A, hA, χ, fun i s hs => h1 i s (Prod.ext (hψ s hs) (Prod.ext (hξ s hs) (hom s hs))), h2⟩
  · obtain ⟨R, i1, i2, i3, ρ, y, hpt, rfl⟩ := hr
    obtain ⟨h, κ, hF, h1, -, -, -, h2⟩ := UpperTheory.V.Loc.spPtL D hD
      ((mapRep (y : R →+* PadicAlgCl l) ρ.hom).comp (D.Gp l).subtype)
      ⟨R, i1, i2, i3, D.loc ρ l, y, hpt.atL, rfl⟩
    refine ⟨D.pl l, lev_place hl.out (hD.pl_over l hl.out) hw, fun i => m.comp (χ₀ i), κ, hK, ⟨h⁻¹, fun s => ?_⟩,
      fun i s hs => ?_, Or.inl fun i j hij => ?_⟩
    · rw [inv_inv]
      exact hF s
    · have e : κ i s = m (D.ps i s) := Units.ext (h1 i s hs)
      rw [e, hps, map_mul, map_zpow, hcyc]
      rfl
    · by_cases e : i = j
      · subst e
        have h3 := DFunLike.congr_fun hij D.s0
        rw [MonoidHom.mul_apply, left_eq_mul] at h3
        have h4 : cycZ ℚ Ω l D.s0 = 1 := by
          refine Units.ext (Subtype.val_injective ((algebraMap ℚ_[l] (PadicAlgCl l)).injective ?_))
          exact (congrArg Units.val h3).trans (map_one _).symm
        exact hD.decompSigma_ord (h4 ▸ IsOfFinOrder.one)
      · obtain ⟨g, -, hg⟩ := h2 i j e ⊤ isOpen_univ
          ⟨⟨D.sg l, ((facts D hD).2.1 l (Finset.mem_insert_self _ _)).1⟩, trivial, rfl⟩
        exact hg (congrArg Units.val (DFunLike.congr_fun hij g))
  · ext s : 1
    have e : D.th s = _ := hps 0 s
    rw [MonoidHom.comp_apply, e, map_mul, map_zpow, ← hcyc]
    rfl
  · obtain ⟨P, hP⟩ := lev_dual (k := PadicAlgCl l)
    exact ⟨P, fun s => hP _ _ (hmult s)⟩
