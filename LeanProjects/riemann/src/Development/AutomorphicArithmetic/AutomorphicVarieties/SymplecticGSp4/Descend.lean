import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ResidueCharMemLevelPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement.DescentNormaliser

open Matrix

section Abstract

variable {O : Type} [CommRing O] [IsLocalRing O] {Γ Γ' ι : Type} [Group Γ] [TopologicalSpace Γ] [Group Γ']
  [TopologicalSpace Γ'] [Fintype ι] [DecidableEq ι] {R : Type} [CommRing R] [Algebra O R] [IsCO O R]

private theorem closed_ker {rbar : Γ →* Matrix ι ι (ResidueField O)} (ρ : Lift O rbar R) :
    IsClosed (ρ.hom.ker : Set Γ) := by
  have hH : IsHausdorff (maximalIdeal R) R := (IsCO.complete (O := O) (R := R)).toIsHausdorff
  have key : (ρ.hom.ker : Set Γ) = ⋂ a, ⋂ b, ⋂ N : ℕ,
      (fun g => Ideal.Quotient.mk (maximalIdeal R ^ N) (ρ.hom g a b)) ⁻¹'
        {Ideal.Quotient.mk (maximalIdeal R ^ N) ((1 : Matrix ι ι R) a b)} := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h a b N
      rw [h]
    · intro h
      ext a b
      have hz : ρ.hom g a b - (1 : Matrix ι ι R) a b = 0 := by
        apply hH.haus
        intro n
        rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
        exact Ideal.Quotient.eq.mp (h a b n)
      exact sub_eq_zero.mp hz
  rw [key]
  exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun N =>
    (ρ.cont a b N).isClosed_fiber _

private theorem exists_down {rbar : Γ →* Matrix ι ι (ResidueField O)} {rb : Γ' →* Matrix ι ι (ResidueField O)}
    (φ : Γ →* Γ') (hφ : Topology.IsQuotientMap φ) (hb : rb.comp φ = rbar) (ρ : Lift O rbar R)
    (h : Γ' →* Matrix ι ι R) (hh : h.comp φ = ρ.hom) : ∃ r : Lift O rb R, r.hom = h := by
  refine ⟨⟨h, fun a b N => ?_, fun g' a b => ?_⟩, rfl⟩
  · intro s
    rw [← hφ.isOpen_preimage]
    have e : (fun g' => Ideal.Quotient.mk (maximalIdeal R ^ N) (h g' a b)) ∘ φ =
        fun g => Ideal.Quotient.mk (maximalIdeal R ^ N) (ρ.hom g a b) := by
      funext g
      rw [← hh]
      rfl
    rw [← Set.preimage_comp, e]
    exact ρ.cont a b N s
  · subst hb
    obtain ⟨g, rfl⟩ := hφ.surjective g'
    have hr := ρ.red g a b
    rw [← hh] at hr
    exact hr

private theorem exists_up {rbar : Γ →* Matrix ι ι (ResidueField O)} {rb : Γ' →* Matrix ι ι (ResidueField O)}
    (φ : Γ →* Γ') (hφ : Continuous φ) (hb : rb.comp φ = rbar) (r : Lift O rb R) :
    ∃ ρ : Lift O rbar R, ρ.hom = r.hom.comp φ := by
  subst hb
  exact ⟨⟨r.hom.comp φ, fun a b N => (r.cont a b N).comp_continuous hφ, fun g a b => r.red (φ g) a b⟩, rfl⟩

end Abstract

section Form

variable {O R : Type} [CommRing O] [CommRing R] [Algebra O R]

private theorem JR_eq : (form O).JR R = J4 R := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [FormData.JR, form, J4]

private theorem J_adj (X : M4 R) : J4 R * adj X = Xᵀ * J4 R := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J4, adj, sgn, Matrix.mul_apply, Fin.sum_univ_four, Fin.rev] <;> ring

private theorem J_sq : -J4 R * J4 R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J4, Matrix.mul_apply, Fin.sum_univ_four]

private theorem gsp_iff (ν : R) (X : M4 R) : IsGSp ν X ↔ Xᵀ * J4 R * X = ν • J4 R := by
  have hJ' : J4 R * -J4 R = 1 := by rw [Matrix.mul_neg, ← Matrix.neg_mul, J_sq]
  have hA : adj X = -J4 R * (Xᵀ * J4 R) := by
    rw [← J_adj, ← Matrix.mul_assoc, J_sq, Matrix.one_mul]
  have e1 : Xᵀ * J4 R * X = J4 R * (adj X * X) := by
    rw [hA, show J4 R * (-J4 R * (Xᵀ * J4 R) * X) = (J4 R * -J4 R) * (Xᵀ * J4 R * X) by noncomm_ring,
      hJ', Matrix.one_mul]
  unfold IsGSp
  constructor
  · intro h
    rw [e1, h, Matrix.mul_smul, Matrix.mul_one]
  · intro h
    calc adj X * X = (-J4 R * J4 R) * (adj X * X) := by rw [J_sq, Matrix.one_mul]
      _ = -J4 R * (Xᵀ * J4 R * X) := by rw [e1, Matrix.mul_assoc]
      _ = ν • 1 := by rw [h, Matrix.mul_smul, J_sq]

private theorem gsp_diag (ν : R) (d : Fin 4 → R) (h : ∀ i, d i * d i.rev = ν) : IsGSp ν (diagonal d) := by
  have hs : ∀ i : Fin 4, sgn i * sgn i = 1 := by
    intro i
    fin_cases i <;> simp [sgn]
  have hA : adj (diagonal d) = diagonal (fun i => d i.rev) := by
    ext i j
    rw [adj_apply]
    by_cases hij : i = j
    · subst hij
      rw [hs, one_smul, diagonal_apply_eq, diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hij, diagonal_apply_ne _ (fun e => hij (Fin.rev_injective e).symm), smul_zero]
  unfold IsGSp
  rw [hA, diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]
  congr 1
  funext i
  rw [mul_comm]
  exact h i

private theorem normalises {Γ : Type} [Group Γ] (ρ : Γ →* M4 R)
    (h : ∀ g, ∃ (ν : R) (d : Fin 4 → R), (∀ i, d i * d i.rev = ν) ∧ ρ g = diagonal d) : (form O).Normalises ρ := by
  refine ⟨fun g => ?_, ⟨1, fun g a b _ => rfl⟩, fun g a b hab => ?_⟩
  · obtain ⟨ν, d, hd, hg⟩ := h g
    refine ⟨ν, ?_⟩
    rw [JR_eq, hg]
    exact (gsp_iff ν _).mp (gsp_diag ν d hd)
  · obtain ⟨ν, d, hd, hg⟩ := h g
    rw [hg]
    exact diagonal_apply_ne _ (fun e => hab (by rw [e]))

private theorem pres_iff {J X Y Y' : M4 R} {ν : R} (h1 : Y * Y' = 1) (h2 : Y' * Y = 1) (hY : Yᵀ * J * Y = ν • J) :
    (X * Y')ᵀ * J * (X * Y') = J ↔ Xᵀ * J * X = ν • J := by
  have e : (X * Y')ᵀ * J * (X * Y') = Y'ᵀ * (Xᵀ * J * X) * Y' := by
    rw [Matrix.transpose_mul]
    noncomm_ring
  have t1 : Yᵀ * Y'ᵀ = 1 := by rw [← Matrix.transpose_mul, h2, Matrix.transpose_one]
  have t2 : Y'ᵀ * Yᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  rw [e, ← hY]
  constructor
  · intro hc
    calc Xᵀ * J * X = (Yᵀ * Y'ᵀ) * (Xᵀ * J * X) * (Y' * Y) := by rw [t1, h2, Matrix.one_mul, Matrix.mul_one]
      _ = Yᵀ * (Y'ᵀ * (Xᵀ * J * X) * Y') * Y := by noncomm_ring
      _ = Yᵀ * J * Y := by rw [hc]
  · intro hc
    rw [hc]
    calc Y'ᵀ * (Yᵀ * J * Y) * Y' = (Y'ᵀ * Yᵀ) * J * (Y * Y') := by noncomm_ring
      _ = J := by rw [t2, h1, Matrix.one_mul, Matrix.mul_one]

private theorem hh_iff [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [IsCO O R]
    {Γ : Type} [Group Γ] [TopologicalSpace Γ] {rb : Γ →* M4 (ResidueField O)} (r0 : Lift O rb O) (r : Lift O rb R)
    (s : Γ) (ν : O) (h : IsGSp ν (r0.hom s)) :
    (form O).HH (r.hom s * (r0.hom s⁻¹).map (algebraMap O R)) ↔ IsGSp (algebraMap O R ν) (r.hom s) := by
  have hJ : (J4 O).map (algebraMap O R) = J4 R := JR_eq (O := O) (R := R)
  have h1 : (r0.hom s).map (algebraMap O R) * (r0.hom s⁻¹).map (algebraMap O R) = 1 := by
    rw [← Matrix.map_mul, ← map_mul, mul_inv_cancel, map_one,
      Matrix.map_one _ (map_zero (algebraMap O R)) (map_one (algebraMap O R))]
  have h2 : (r0.hom s⁻¹).map (algebraMap O R) * (r0.hom s).map (algebraMap O R) = 1 := by
    rw [← Matrix.map_mul, ← map_mul, inv_mul_cancel, map_one,
      Matrix.map_one _ (map_zero (algebraMap O R)) (map_one (algebraMap O R))]
  have hY : ((r0.hom s).map (algebraMap O R))ᵀ * J4 R * (r0.hom s).map (algebraMap O R) =
      algebraMap O R ν • J4 R := by
    have h0 := congrArg (fun M => M.map (algebraMap O R)) ((gsp_iff ν (r0.hom s)).mp h)
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hJ,
      Matrix.map_smul' _ _ _ (fun a b => map_mul (algebraMap O R) a b), hJ] at h0
    exact h0
  have hC : (r.hom s * (r0.hom s⁻¹).map (algebraMap O R)).map (res O R) = 1 := by
    have e1 : (r.hom s).map (res O R) = rb s := by
      ext a b
      exact r.red s a b
    have e2 : ((r0.hom s⁻¹).map (algebraMap O R)).map (res O R) = rb s⁻¹ := by
      ext a b
      simp only [Matrix.map_apply]
      rw [AlgHom.commutes, ← r0.red s⁻¹ a b]
      exact ((res O O).commutes _).symm
    rw [Matrix.map_mul, e1, e2, ← map_mul, mul_inv_cancel, map_one]
  rw [gsp_iff, ← pres_iff (X := r.hom s) h1 h2 hY]
  unfold FormData.HH
  rw [JR_eq]
  exact ⟨fun hh => hh.1, fun hh => ⟨hh, fun a b hab => absurd rfl hab, hC⟩⟩

end Form

section Places

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)

private theorem val_iff {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 ℚ)} (hv : IsPlaceOver A v) (n : ℕ) :
    A.valuation (n : Ω) < 1 ↔ ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  have e : (algebraMap ℚ Ω) (((n : 𝓞 ℚ)) : ℚ) = (n : Ω) := by simp
  rw [← e]
  exact hv _

private theorem ns_le {M : Type} [Monoid M] (f : G ℚ Ω →* M) (hc : IsClosed (f.ker : Set (G ℚ Ω)))
    (h : ∀ A, Raw.Away D.S A → Ine (F := ℚ) A ≤ f.ker) : NS Ω D.SP ≤ f.ker := by
  unfold NS
  refine Subgroup.topologicalClosure_minimal _ ?_ hc
  refine Subgroup.normalClosure_le_normal ?_
  intro g hg
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff, exists_prop] at hg
  obtain ⟨v, hv, A, hA, hgA⟩ := hg
  have hAw : Raw.Away D.S A := by
    intro p hp hlt
    apply hv
    exact ⟨p, hp, (val_iff hA p).mp hlt⟩
  exact h A hAw hgA

private theorem toGS_ine {A : ValuationSubring Ω} (hA : Raw.Away D.S A) {g : G ℚ Ω} (hg : g ∈ Ine (F := ℚ) A) :
    toGS Ω D.SP g = 1 := by
  show (QuotientGroup.mk' (NS Ω D.SP)) g = 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  by_cases htop : A = ⊤
  · have h1 := ((places ℚ Ω l A).2.1 htop).1
    rw [h1] at hg
    rw [Subgroup.mem_bot.mp hg]
    exact one_mem _
  · obtain ⟨v, hv⟩ := (places ℚ Ω l A).1 htop
    have hvS : v ∉ D.SP := by
      rintro ⟨p, hp, hpv⟩
      exact hA p hp ((val_iff hv p).mpr hpv)
    apply Subgroup.le_topologicalClosure
    apply Subgroup.subset_normalClosure
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff, exists_prop]
    exact ⟨v, hvS, A, hv, hg⟩

omit [CharZero Ω] [IsAlgClosure ℚ Ω] in
private theorem not_both (A : ValuationSubring Ω) {m n : ℕ} (hc : m.Coprime n)
    (hm : A.valuation (m : Ω) < 1) : ¬ A.valuation (n : Ω) < 1 := by
  intro hn
  have hb := Nat.gcd_eq_gcd_ab m n
  rw [hc.gcd_eq_one, Nat.cast_one] at hb
  have hb' : (1 : Ω) = (m : Ω) * ((m.gcdA n : ℤ) : Ω) + (n : Ω) * ((m.gcdB n : ℤ) : Ω) := by
    have h0 := congrArg (fun z : ℤ => (z : Ω)) hb
    push_cast at h0
    exact h0
  have ha : A.valuation ((m.gcdA n : ℤ) : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A _)
  have hb2 : A.valuation ((m.gcdB n : ℤ) : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A _)
  have h1 : A.valuation ((m : Ω) * ((m.gcdA n : ℤ) : Ω)) < 1 := by
    rw [map_mul]
    calc A.valuation (m : Ω) * A.valuation ((m.gcdA n : ℤ) : Ω) ≤ A.valuation (m : Ω) * 1 := by
          gcongr
      _ = A.valuation (m : Ω) := mul_one _
      _ < 1 := hm
  have h2 : A.valuation ((n : Ω) * ((m.gcdB n : ℤ) : Ω)) < 1 := by
    rw [map_mul]
    calc A.valuation (n : Ω) * A.valuation ((m.gcdB n : ℤ) : Ω) ≤ A.valuation (n : Ω) * 1 := by
          gcongr
      _ = A.valuation (n : Ω) := mul_one _
      _ < 1 := hn
  have h3 : A.valuation (1 : Ω) < 1 := by
    rw [hb']
    exact lt_of_le_of_lt (A.valuation.map_add _ _) (max_lt h1 h2)
  rw [map_one] at h3
  exact lt_irrefl _ h3

private theorem T_sub (hD : D.Good) {p : ℕ} (hp : p ∈ D.T) : p ∈ D.S := by
  simp only [Raw.T, Raw.Sb, Finset.mem_insert, Finset.mem_filter] at hp
  rcases hp with h | h
  · rw [h]
    exact hD.l_mem
  · exact h.1

private theorem kill_iff (hD : D.Good) {M : Type} [Monoid M] (f : D.Gam →* M) :
    (∀ q ∈ D.S \ D.T, ∀ g ∈ D.Ip q ⊓ D.rbar.ker, f (toGS Ω D.SP g) = 1) ↔ D.UnrT (f.comp (toGS Ω D.SP)) 1 := by
  constructor
  · intro hk A hA g hg hr
    show f (toGS Ω D.SP g) = 1
    by_cases hS : Raw.Away D.S A
    · rw [toGS_ine D hS hg, map_one]
    · unfold Raw.Away at hS
      push_neg at hS
      obtain ⟨p, hpS, hpA⟩ := hS
      have hpT : p ∉ D.T := fun hpT => hA p hpT hpA
      have hpr : Nat.Prime p := hD.S_prime p hpS
      obtain ⟨u, -, hu⟩ := (Chr.placesQ Ω).2.2 p A (D.pl p) hpr hpA (hD.pl_over p hpr)
      have hg' := hu g hg
      have hk' := hk p (Finset.mem_sdiff.mpr ⟨hpS, hpT⟩) (u⁻¹ * g * u) (Subgroup.mem_inf.mpr ⟨hg', by
        rw [MonoidHom.mem_ker, map_mul, map_mul, hr, mul_one, ← map_mul, inv_mul_cancel, map_one]⟩)
      have e : toGS Ω D.SP g = toGS Ω D.SP u * toGS Ω D.SP (u⁻¹ * g * u) * (toGS Ω D.SP u)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
        group
      rw [e, map_mul, map_mul, hk', mul_one, ← map_mul, mul_inv_cancel, map_one]
  · intro hU q hq g hg
    obtain ⟨hqS, hqT⟩ := Finset.mem_sdiff.mp hq
    have hqp : Nat.Prime q := hD.S_prime q hqS
    have hAw : Raw.Away D.T (D.pl q) := by
      intro p hpT hpv
      have hpp : Nat.Prime p := hD.S_prime p (T_sub D hD hpT)
      have hne : p ≠ q := fun e => hqT (e ▸ hpT)
      exact not_both (D.pl q) ((Nat.coprime_primes hpp hqp).mpr hne) hpv (hD.pl_over q hqp)
    obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.mp hg
    exact hU (D.pl q) hAw g hg1 (MonoidHom.mem_ker.mp hg2)

end Places

end UpperTheory.V.GradeZeroInterpolatingElement.DescentNormaliser

open UpperTheory.V.GradeZeroInterpolatingElement.DescentNormaliser in
theorem UpperTheory.V.GradeZeroInterpolatingElement.descend :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∃ (rb : D.Gam →* M4 (ResidueField c.O)) (r0 : Lift c.O rb c.O), rb.comp (toGS Ω D.SP) = D.rbar ∧ r0.hom.comp (toGS Ω D.SP) = D.r0 ∧ (form c.O).Normalises rb ∧ (form c.O).Normalises r0.hom ∧ ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R], (∀ r : Lift c.O rb R, ∃ ρ : Lift c.O D.rbar R, ρ.hom = r.hom.comp (toGS Ω D.SP) ∧ ((form c.O).InH r0.hom R r ↔ D.Mult ρ.hom) ∧ ((∀ q : D.frame.Q, killCond (rb.comp (D.frame.ψ q)) (D.frame.N q) R (r.comap (D.frame.ψ q) (D.frame.hψ q))) ↔ D.UnrT ρ.hom 1)) ∧ ∀ ρ : Lift c.O D.rbar R, D.UnrT ρ.hom 1 → ∃ r : Lift c.O rb R, ρ.hom = r.hom.comp (toGS Ω D.SP) := by
  intro Ω _ _ _ l _ c D hD
  obtain ⟨-, -, -, -, -, hpsth, -, -, -, -, hcont, -, -, hunr⟩ := facts D hD
  have hdiag : ∀ g, D.r0 g = Matrix.diagonal (fun i => ((D.ps i g : (↥c.O)ˣ) : ↥c.O)) := fun g => rfl
  have hd : ∀ g (i : Fin 4), ((D.ps i g : (↥c.O)ˣ) : ↥c.O) * ((D.ps i.rev g : (↥c.O)ˣ) : ↥c.O) =
      ((D.th g : (↥c.O)ˣ) : ↥c.O) := by
    intro g i
    rw [← Units.val_mul, ← MonoidHom.mul_apply, hpsth i]
  have hres : ∀ x : ↥c.O, res ↥c.O ↥c.O x = residue ↥c.O x := fun x => (res _ _).commutes x
  have hc0 : ∀ a b : Fin 4, AdicCont (maximalIdeal ↥c.O) fun g => D.r0 g a b := by
    intro a b
    by_cases hab : a = b
    · subst hab
      have e : (fun g => D.r0 g a a) = fun g => ((D.ps a g : (↥c.O)ˣ) : ↥c.O) := by
        funext g
        rw [hdiag, Matrix.diagonal_apply_eq]
      rw [e]
      exact hcont a
    · intro N
      have e : (fun g => Ideal.Quotient.mk (maximalIdeal ↥c.O ^ N) (D.r0 g a b)) = fun _ => 0 := by
        funext g
        rw [hdiag, Matrix.diagonal_apply_ne _ hab, map_zero]
      rw [e]
      exact IsLocallyConstant.const 0
  let r0L : Lift ↥c.O D.rbar ↥c.O := ⟨D.r0, hc0, fun g a b => by rw [hres]; rfl⟩
  have hIne : ∀ A, Raw.Away D.S A → Ine (F := ℚ) A ≤ D.r0.ker := by
    intro A hA g hg
    rw [MonoidHom.mem_ker, hdiag]
    have e : (fun i => ((D.ps i g : (↥c.O)ˣ) : ↥c.O)) = fun _ => 1 := by
      funext i
      rw [(MonoidHom.mem_ker).mp (hunr i A hA hg), Units.val_one]
    rw [e, Matrix.diagonal_one]
  have hle0 : NS Ω D.SP ≤ D.r0.ker := ns_le D D.r0 (closed_ker r0L) hIne
  let r0b : D.Gam →* M4 ↥c.O := QuotientGroup.lift (NS Ω D.SP) D.r0 hle0
  have hr0b : r0b.comp (toGS Ω D.SP) = D.r0 := MonoidHom.ext fun g => rfl
  let rb : D.Gam →* M4 (ResidueField ↥c.O) := mapRep (residue ↥c.O) r0b
  have hrb : rb.comp (toGS Ω D.SP) = D.rbar := MonoidHom.ext fun g => rfl
  have hq : Topology.IsQuotientMap (toGS Ω D.SP) := QuotientGroup.isQuotientMap_mk (NS Ω D.SP)
  have hcont' : Continuous (toGS Ω D.SP) := hq.continuous
  obtain ⟨r0', hr0'⟩ := exists_down (toGS Ω D.SP) hq hrb r0L r0b hr0b
  have hnorm0 : (form ↥c.O).Normalises r0b := by
    apply normalises
    intro s
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective s
    exact ⟨((D.th g : (↥c.O)ˣ) : ↥c.O), fun i => ((D.ps i g : (↥c.O)ˣ) : ↥c.O), hd g, hdiag g⟩
  have hnormb : (form ↥c.O).Normalises rb := by
    apply normalises
    intro s
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective s
    refine ⟨residue ↥c.O ((D.th g : (↥c.O)ˣ) : ↥c.O),
      fun i => residue ↥c.O ((D.ps i g : (↥c.O)ˣ) : ↥c.O), fun i => ?_, ?_⟩
    · rw [← map_mul, hd g i]
    · show (D.r0 g).map (residue ↥c.O) = _
      rw [hdiag, Matrix.diagonal_map (map_zero _)]
  refine ⟨rb, r0', hrb, by rw [hr0']; exact hr0b, hnormb, by rw [hr0']; exact hnorm0, ?_⟩
  intro R _ _ _
  refine ⟨fun r => ?_, fun ρ hρ => ?_⟩
  · obtain ⟨ρ, hρ⟩ := exists_up (toGS Ω D.SP) hcont' hrb r
    refine ⟨ρ, hρ, ?_, ?_⟩
    · have key : ∀ g : G ℚ Ω, (form ↥c.O).HH (r.hom (toGS Ω D.SP g) *
          (r0'.hom (toGS Ω D.SP g)⁻¹).map (algebraMap ↥c.O R)) ↔
          IsGSp (algebraMap ↥c.O R ((D.th g : (↥c.O)ˣ) : ↥c.O)) (r.hom (toGS Ω D.SP g)) := by
        intro g
        apply hh_iff r0' r
        rw [hr0']
        show IsGSp _ (D.r0 g)
        rw [hdiag]
        exact gsp_diag _ _ (hd g)
      show (∀ s, (form ↥c.O).HH (r.hom s * (r0'.hom s⁻¹).map (algebraMap ↥c.O R))) ↔
        ∀ g, IsGSp (algebraMap ↥c.O R ((D.th g : (↥c.O)ˣ) : ↥c.O)) (ρ.hom g)
      rw [hρ]
      constructor
      · intro h g
        exact (key g).mp (h _)
      · intro h s
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective s
        exact (key g).mpr (h g)
    · have hk := kill_iff D hD r.hom
      rw [hρ, ← hk]
      constructor
      · intro h q hq g hg
        obtain ⟨hg1, -⟩ := Subgroup.mem_inf.mp hg
        have hgD : g ∈ D.Gp q := Ine_le_Dec _ hg1
        exact h ⟨q, hq⟩ ⟨g, hgD⟩ (Subgroup.mem_subgroupOf.mpr hg)
      · intro h q n hn
        exact h q.1 q.2 n.1 (Subgroup.mem_subgroupOf.mp hn)
  · have hle : NS Ω D.SP ≤ ρ.hom.ker := by
      refine ns_le D ρ.hom (closed_ker ρ) ?_
      intro A hA g hg
      rw [MonoidHom.mem_ker]
      refine hρ A (fun p hp => hA p (T_sub D hD hp)) g hg ?_
      show (D.r0 g).map (residue ↥c.O) = 1
      rw [MonoidHom.mem_ker.mp (hIne A hA hg)]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    let h : D.Gam →* M4 R := QuotientGroup.lift (NS Ω D.SP) ρ.hom hle
    obtain ⟨r, hr⟩ := exists_down (toGS Ω D.SP) hq hrb ρ h (MonoidHom.ext fun g => rfl)
    exact ⟨r, by rw [hr]; exact MonoidHom.ext fun g => rfl⟩
