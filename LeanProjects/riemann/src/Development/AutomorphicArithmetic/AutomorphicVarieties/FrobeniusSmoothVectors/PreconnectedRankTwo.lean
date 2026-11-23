import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrSMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FramePointFiberNonempty
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ExistsMemStrSNeZeroOfFrameOk
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SmoothHomWeightSumNeg
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SmoothCharacterExtendsToOpenSubgroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SmoothDualExact

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem pol2 {Q : Type} [CommRing Q] (x y z : Q) :
    (!![z, 0; y, x] : Matrix (Fin 2) (Fin 2) Q) = Jmat Q 2 * (!![x, 0; y, z])ᵀ * Jmat Q 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Jmat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

private theorem ord2 {H Q : Type} [CommRing Q] (r : H → Matrix (Fin 2) (Fin 2) Q) (ψ : Fin 2 → H → Q) (γ : Q)
    (h : ∀ s, r s = !![ψ 0 s, 0; (ψ 0 s - ψ 1 s) * γ, ψ 1 s]) (g : Fin 2 → H) : ordProd r ψ g = 0 := by
  have e : ∀ i : Fin 2, List.ofFn (fun i => r (g i) - ψ i (g i) • (1 : Matrix (Fin 2) (Fin 2) Q)) =
      [r (g 0) - ψ 0 (g 0) • 1, r (g 1) - ψ 1 (g 1) • 1] := fun _ => by
    simp [List.ofFn_succ]
  unfold ordProd
  rw [e 0, h, h]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem hom_ex {G Q : Type} [Group G] [CommRing Q] (p q : G →* Q) (a : G → Q) (a0 : a 1 = 0)
    (h : ∀ g g', a (g * g') = a g * p g' + q g * a g') :
    ∃ r : G →* Matrix (Fin 2) (Fin 2) Q, ∀ g, r g = !![p g, 0; a g, q g] := by
  refine ⟨{ toFun := fun g => !![p g, 0; a g, q g],
            map_one' := ?_, map_mul' := ?_ }, fun g => rfl⟩
  · simp only [map_one, a0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro g g'
    simp only [h]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, map_mul] <;> ring

private theorem isLocallyConstant_psi_restrict_of_isOpen_ker {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k}
    (hΨ : IsOpen (F.Ψ.ker : Set F.Γ)) : IsLocallyConstant fun g : F.G0 => F.Ψ (g : F.Γ) := by
  rw [IsLocallyConstant.iff_isOpen_fiber_apply]
  intro g
  have hK : IsOpen ((fun h : F.G0 => ((g⁻¹ * h : F.G0) : F.Γ)) ⁻¹' (F.Ψ.ker : Set F.Γ)) :=
    hΨ.preimage (continuous_subtype_val.comp (continuous_const.mul continuous_id))
  convert hK using 1
  ext h
  simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe, MonoidHom.mem_ker,
    Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
  constructor
  · intro e
    rw [e, inv_mul_cancel]
  · intro e
    exact (inv_mul_eq_one.mp e).symm

private theorem rep_ex {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}
    (hF : F.Ok C₀) (Q : Type) [CommRing Q] [Algebra k Q] {a : F.G0 → Q} (ha : a ∈ F.strS Q) :
    ∃ ρ : NRep F 2 Q, ρ.IsBar (algebraMap k Q) ∧ ρ.triM = ⊥ ∧ (∀ i j, IsLocallyConstant fun g => ρ.r g i j) ∧
      ∀ g, ρ.r g 1 0 = a g := by
  classical
  obtain ⟨hlc, hmul, hstar, hloc⟩ := ha
  let φ : F.G0 →* kˣ := F.Ψ.comp F.del.ker.subtype
  let p : F.G0 →* Q := (algebraMap k Q).toMonoidHom.comp ((Units.coeHom k).comp φ)
  let q : F.G0 →* Q := (algebraMap k Q).toMonoidHom.comp ((Units.coeHom k).comp φ⁻¹)
  have hp : ∀ g, p g = algebraMap k Q (F.Ψ (g : F.Γ) : k) := fun g => rfl
  have hq : ∀ g, q g = algebraMap k Q ((F.Ψ (g : F.Γ))⁻¹ : kˣ) := fun g => rfl
  have hΨstar : ∀ g : F.G0, F.Ψ ((F.star g : F.G0) : F.Γ) = (F.Ψ (g : F.Γ))⁻¹ := by
    intro g
    simp only [Frame.star, Frame.conj, MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply,
      map_mul, map_inv, Subgroup.coe_inv]
    rw [mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]
  have a0 : a 1 = 0 := by
    have h1 := hmul 1 1
    simp only [mul_one, map_one, Units.val_one, one_smul, inv_one] at h1
    simpa using h1
  have hmul' : ∀ g g', a (g * g') = a g * p g' + q g * a g' := by
    intro g g'
    rw [hmul, hp, hq, Algebra.smul_def, Algebra.smul_def, mul_comm (algebraMap k Q _) (a g)]
  obtain ⟨r, hr⟩ := hom_ex p q a a0 hmul'
  let χ : (v : F.V) → F.Gv v →* Qˣ := fun v => (Units.map (algebraMap k Q).toMonoidHom).comp (F.Ψ.comp (F.loc v))
  have hpstar : ∀ g, p (F.star g) = q g := fun g => by rw [hp, hq, hΨstar]
  have hqstar : ∀ g, q (F.star g) = p g := fun g => by rw [hp, hq, hΨstar, inv_inv]
  let ρ : NRep F 2 Q :=
    { r := r
      ψ := fun v => ![χ v, (χ v)⁻¹]
      pol := by
        intro g
        rw [hr, hr, hpstar, hqstar, hstar]
        exact pol2 _ _ _
      diag := by
        intro i j hij
        rw [hr, hr]
        fin_cases i <;> fin_cases j
        · exact absurd rfl hij
        · simp
        · simp [hstar]
        · exact absurd rfl hij
      ord := by
        intro v g
        obtain ⟨γ, hγ⟩ := hloc v
        refine ord2 _ _ γ (fun s => ?_) g
        rw [hr, hγ]
        simp [χ, hp, hq, Algebra.smul_def, Frame.loc] }
  refine ⟨ρ, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro g i
    show r g i i = _
    rw [hr]
    fin_cases i <;> simp [w, hp, hq]
  · intro v i g
    fin_cases i <;> simp [ρ, χ, w]
  · apply Ideal.span_eq_bot.mpr
    rintro _ ⟨g, i, j, hij, rfl⟩
    show r g i j = 0
    rw [hr]
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · have hl : IsLocallyConstant fun g : F.G0 => F.Ψ (g : F.Γ) := isLocallyConstant_psi_restrict_of_isOpen_ker hF.Ψ_open
    intro i j
    show IsLocallyConstant fun g => r g i j
    simp only [hr]
    fin_cases i <;> fin_cases j
    · exact hl.comp fun z => algebraMap k Q (z : k)
    · exact IsLocallyConstant.const _
    · exact hlc
    · exact hl.comp fun z => algebraMap k Q ((z⁻¹ : kˣ) : k)
  · intro g
    show r g 1 0 = a g
    rw [hr]
    simp

section

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
  {F : Frame l (ResidueField O)} {C₀ : ℕ} (hF : F.Ok C₀) (S : Space O F 2)
include hF

private theorem pt_ex (Q : Type) [CommRing Q] [Nontrivial Q] [Algebra (ResidueField O) Q] {a : F.G0 → Q}
    (h : a ∈ F.strS Q) : ∃ ξ : S.A →+* Q, S.FPt ξ ∧ S.u.triM ≤ RingHom.ker ξ ∧ ∀ g, ξ (S.u.r g 1 0) = a g := by
  haveI : CharP (ResidueField O) l := IsCoef.char
  obtain ⟨ρ, hbar, htri, hlc, h10⟩ := rep_ex hF Q h
  obtain ⟨ξ, hξ, hmap⟩ := UpperTheory.smoothHom_weight_sum_neg hF (Or.inl rfl) S Q ρ hbar htri hlc
  refine ⟨ξ, hξ, ?_, fun g => ?_⟩
  · rw [NRep.triM, Ideal.span_le]
    rintro _ ⟨g, i, j, hij, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have hm : ρ.r g i j ∈ ρ.triM := Ideal.subset_span ⟨g, i, j, hij, rfl⟩
    rw [htri, Ideal.mem_bot] at hm
    rw [← hm, ← hmap, NRep.map_r]
  · rw [← h10, ← hmap, NRep.map_r]

private theorem pt_uniq {Q : Type} [CommRing Q] [Algebra (ResidueField O) Q] {ξ ξ' : S.A →+* Q}
    (h : S.FPt ξ) (h' : S.FPt ξ') (t : S.u.triM ≤ RingHom.ker ξ) (t' : S.u.triM ≤ RingHom.ker ξ')
    (e : ∀ g, ξ' (S.u.r g 1 0) = ξ (S.u.r g 1 0)) : ξ' = ξ := by
  have H := UpperTheory.smoothCharacter_extends_to_open_subgroup hF (Or.inl rfl) S Q ξ h
  have H' := UpperTheory.smoothCharacter_extends_to_open_subgroup hF (Or.inl rfl) S Q ξ' h'
  refine H.2.2 ξ' h' (fun g i j => ?_)
  have z : ∀ {ζ : S.A →+* Q}, S.u.triM ≤ RingHom.ker ζ → ζ (S.u.r g 0 1) = 0 := fun hz =>
    RingHom.mem_ker.mp (hz (Ideal.subset_span ⟨g, 0, 1, by decide, rfl⟩))
  have d : ∀ i : Fin 2, ξ' (S.u.r g i i) = ξ (S.u.r g i i) := by
    intro i
    have d1 := H.1.1 g i
    have d2 := H'.1.1 g i
    rw [NRep.map_r] at d1 d2
    rw [d1, d2]
  fin_cases i <;> fin_cases j
  · exact d 0
  · exact (z t').trans (z t).symm
  · exact e g
  · exact d 1

private theorem pt_mem {Q : Type} [CommRing Q] [Algebra (ResidueField O) Q] {ξ : S.A →+* Q}
    (h : S.FPt ξ) (t : S.u.triM ≤ RingHom.ker ξ) : (fun g => ξ (S.u.r g 1 0)) ∈ F.strS Q := by
  have H := UpperTheory.smoothCharacter_extends_to_open_subgroup hF (Or.inl rfl) S Q ξ h
  haveI : CharP (ResidueField O) l := IsCoef.char
  have htri : (NRep.map ξ S.u).triM = ⊥ := by
    apply Ideal.span_eq_bot.mpr
    rintro _ ⟨g, i, j, hij, rfl⟩
    rw [NRep.map_r]
    exact RingHom.mem_ker.mp (t (Ideal.subset_span ⟨g, i, j, hij, rfl⟩))
  have h2 := framePoint_fiber_nonempty hF Q (NRep.map ξ S.u) H.1 htri H.2.1
  simpa only [NRep.map_r] using h2

private theorem line {K : Type} [Field K] [Algebra (ResidueField O) K] {A : F.G0 → Polynomial K}
    (h : A ∈ F.strS (Polynomial K)) :
    ∃ η : PrimeSpectrum S.A, S.mB ≤ S.π η.asIdeal ∧
      ∀ (c : K) (ξ : S.A →+* K), S.FPt ξ → S.u.triM ≤ RingHom.ker ξ →
        (∀ g, (A g).eval c = ξ (S.u.r g 1 0)) → η.asIdeal ≤ RingHom.ker ξ := by
  obtain ⟨ξA, hA, tA, vA⟩ := pt_ex hF S (Polynomial K) h
  refine ⟨⟨RingHom.ker ξA, RingHom.ker_isPrime ξA⟩, ?_, ?_⟩
  · exact Ideal.le_comap_map.trans (Ideal.comap_mono hA.x0)
  · intro c ξ hξ tξ vξ
    let φ : Polynomial K →ₐ[ResidueField O] K := (Polynomial.aeval c).restrictScalars (ResidueField O)
    have hφ : S.FPt ((φ : Polynomial K →+* K).comp ξA) := hA.comp φ
    have tφ : S.u.triM ≤ RingHom.ker ((φ : Polynomial K →+* K).comp ξA) := fun x hx => by
      rw [RingHom.mem_ker, RingHom.comp_apply, RingHom.mem_ker.mp (tA hx), map_zero]
    have heq : (φ : Polynomial K →+* K).comp ξA = ξ := pt_uniq hF S hξ hφ tξ tφ (fun g => by
      rw [RingHom.comp_apply, vA g, ← vξ g]
      simp [φ, Polynomial.coe_aeval_eq_eval])
    intro x hx
    rw [RingHom.mem_ker, ← heq, RingHom.comp_apply, RingHom.mem_ker.mp hx, map_zero]

end

theorem UpperTheory.V.Fr.preconnected_rank_two :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ S : Space O F 2, IsPreconnected S.BB := by
  intro l _ O _ _ _ _ F C₀ hF S
  classical
  haveI : CharP (ResidueField O) l := IsCoef.char
  obtain ⟨b, hb, hb0⟩ := UpperTheory.exists_mem_strS_ne_zero_of_frameOk hF
  obtain ⟨ξb, hbF, hbt, hbv⟩ := pt_ex hF S (ResidueField O) hb
  let qb : PrimeSpectrum S.A := ⟨RingHom.ker ξb, RingHom.ker_isPrime ξb⟩
  have hnz : ∃ g, b g ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hb0 (funext hc)
  obtain ⟨g1, hg1⟩ := hnz
  have hqb : qb ∈ S.BB := by
    refine ⟨Ideal.le_comap_map.trans (Ideal.comap_mono hbF.x0), fun hle => hg1 ?_⟩
    have hm : S.u.r g1 1 0 ∈ S.u.triP := Ideal.subset_span ⟨g1, 1, 0, by decide, rfl⟩
    rw [← hbv g1]
    exact RingHom.mem_ker.mp (hle hm)
  refine isPreconnected_of_forall qb (fun p hp => ?_)
  obtain ⟨K, _, _, ξ, hker, hξ, tξ⟩ := UpperTheory.smoothDual_exact hF (Or.inl rfl) S p hp
  have ha := pt_mem hF S hξ tξ
  let bK : F.G0 → K := fun g => algebraMap (ResidueField O) K (b g)
  have hbK : bK ∈ F.strS K := F.strS_map (Algebra.linearMap (ResidueField O) K) hb
  let Lin : K →ₗ[ResidueField O] Polynomial K :=
    (Algebra.linearMap K (Polynomial K)).restrictScalars (ResidueField O)
  let A : F.G0 → Polynomial K := fun g =>
    (1 - Polynomial.X) * Lin (ξ (S.u.r g 1 0)) + Polynomial.X * Lin (bK g)
  have hAmem : A ∈ F.strS (Polynomial K) :=
    Submodule.add_mem _ (F.strS_mul _ (F.strS_map Lin ha)) (F.strS_mul _ (F.strS_map Lin hbK))
  obtain ⟨η, hηB, hη⟩ := line hF S hAmem
  have hη0 : η.asIdeal ≤ p.asIdeal := by
    rw [← hker]
    exact hη 0 ξ hξ tξ (fun g => by simp [A, Lin])
  let ι : ResidueField O →ₐ[ResidueField O] K := Algebra.ofId _ _
  have tb' : S.u.triM ≤ RingHom.ker ((ι : ResidueField O →+* K).comp ξb) := fun x hx => by
    rw [RingHom.mem_ker, RingHom.comp_apply, RingHom.mem_ker.mp (hbt hx), map_zero]
  have hη1 : η.asIdeal ≤ qb.asIdeal := by
    have h1 := hη 1 ((ι : ResidueField O →+* K).comp ξb) (hbF.comp ι) tb'
      (fun g => by simp [A, Lin, bK, hbv, ι])
    intro x hx
    have hx1 := h1 hx
    rw [RingHom.mem_ker, RingHom.comp_apply] at hx1
    exact RingHom.mem_ker.mpr ((ι : ResidueField O →+* K).injective (by rw [hx1, map_zero]))
  have hηBB : η ∈ S.BB := ⟨hηB, fun hle => hp.2 (hle.trans hη0)⟩
  refine ⟨{η, p, qb}, ?_, by simp, by simp, ?_⟩
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hηBB
    · exact hp
    · exact hqb
  · refine (isPreconnected_singleton (x := η)).subset_closure (by simp) ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rw [← PrimeSpectrum.le_iff_mem_closure]
    rcases hz with rfl | rfl | rfl
    · exact le_rfl
    · exact hη0
    · exact hη1
