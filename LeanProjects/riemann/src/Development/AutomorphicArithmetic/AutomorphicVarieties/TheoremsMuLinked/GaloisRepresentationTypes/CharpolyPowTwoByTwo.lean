import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.LinkedRig
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.AdDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ExistsNrep2
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.LkMarks
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CliffPrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.MatrixIrreducibility.IrrOfMatIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolCOfSolDescent
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SolDescent
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.DenseRangeUnitsR
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CsdOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AutBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FreeRatios

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th

private theorem irr2 {G κ k A : Type} [Group G] [Field κ] [IsAlgClosed κ] [Field k] [CommRing A]
    (r : G →* GL (Fin 2) κ) (hr : U3.MatIrr ⊤ (Pr.gm r)) (j : A →+* κ) (hj : Function.Injective j) (φ : A →+* k)
    (χ : G →* kˣ) (t : G → A) (ht : ∀ g, j (t g) = (Pr.gm r g).trace)
    (hχ : ∀ g, φ (t g) = (χ g : kˣ) + ((χ g)⁻¹ : kˣ)) (U : Subgroup G) [U.Normal] {u : G} (hu : u ∈ U)
    (hd : (Pr.gm r u).det = 1) (hne : χ u ^ 2 ≠ 1) : U3.MatIrr U (Pr.gm r) := by
  have hy : ((χ u : kˣ) : k) ^ 2 - 1 ≠ 0 := fun h => hne (Units.ext (by simpa [sub_eq_zero] using h))
  rcases Pr.cliffPrime G κ 2 Nat.prime_two r hr U with h | h | ⟨b, la, π, -, hla, hπ, htr⟩
  · exact h
  · exfalso
    obtain ⟨a, ha⟩ := h u hu
    have e : t u ^ 2 = 4 := by
      apply hj
      rw [map_pow, ht, map_ofNat]
      rw [ha] at hd ⊢
      simp only [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul] at hd ⊢
      push_cast
      linear_combination 4 * hd
    have e2 := congrArg φ e
    rw [map_pow, hχ, map_ofNat] at e2
    have e3 := (χ u).mul_inv
    apply pow_ne_zero 2 hy
    linear_combination ((χ u : kˣ) : k) ^ 2 * e2 - (2 * ((χ u : kˣ) : k) ^ 2 + (χ u : kˣ) * ((χ u)⁻¹ : kˣ) + 1) * e3
  · exfalso
    obtain ⟨g, hg⟩ := htr 0 1
    have hne' : ∀ i, π g i ≠ i := by
      intro i hi
      fin_cases i
      · exact absurd (hg.symm.trans hi) (by decide)
      · exact absurd ((π g).injective (hg.trans hi.symm)) (by decide)
    have tr0 : ∀ s ∈ U, (Pr.gm r (g * s)).trace = 0 := fun s hs => by
      rw [← Matrix.trace_toLin'_eq, LinearMap.trace_eq_matrix_trace κ b]
      refine Finset.sum_eq_zero fun i _ => ?_
      obtain ⟨a, ha⟩ := hπ g i
      have := hla i ⟨s, hs⟩
      simp only [Pr.gm] at this ha
      rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Matrix.toLin'_apply]
      simp only [Pr.gm, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
      rw [this, Matrix.mulVec_smul, ha]
      simp [hne' i]
    have z : ∀ s ∈ U, ((χ (g * s) : kˣ) : k) ^ 2 + 1 = 0 := fun s hs => by
      have e : t (g * s) = 0 := hj (by rw [ht, tr0 s hs, map_zero])
      have e2 := hχ (g * s)
      rw [e, map_zero] at e2
      have e3 := (χ (g * s)).mul_inv
      linear_combination -((χ (g * s) : kˣ) : k) * e2 - e3
    have z1 := z 1 U.one_mem
    have z2 := z u hu
    rw [mul_one] at z1
    rw [map_mul, Units.val_mul] at z2
    apply hy
    linear_combination ((χ u : kˣ) : k) ^ 2 * z1 - z2

private theorem pair2 {κ : Type} [Field κ] :
    ∃ J : GL (Fin 2) κ, ∀ M : Matrix (Fin 2) (Fin 2) κ, M.transpose * J.val * M = M.det • J.val := by
  refine ⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩, fun M => ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

private theorem freeRes {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (L : Type) [Field L]
    [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (h : FreeAt l W) :
    FreeAt l (W.comp (Base.galEmb ℚ L Ω)) :=
  _root_.UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.freeRes L W h

theorem UpperTheory.V.Th.rigEnd2 :
    Af.HypothesesH → AdL → RigEnd2 := by
  intro hH hAd Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H hΨσ hF A _ _ r hr hII _ K _ _ _ _ hK2 hK W hWc hW hdet haut hfree θ hθ R hR
  obtain ⟨L, _, _, _, _, g₂, Φ, C₀, ⟨k⟩, hok, hbig, hseed⟩ := hF
  haveI := Db.algClo L Ω
  haveI := Db.algClo K Ω
  obtain ⟨-, ka, hka, hrig⟩ := linkedRig hH hAd Ω l ι c N e ψ η σ g₂ B M H L Φ C₀ k hok hbig hseed
  generalize Chr.Psi l e (Chr.dirG ℚ Ω ψ) = Ψ at *
  have hl : l ∣ M := (dvd_mul_right l N).trans H.dvd
  have hσ : σ * σ = 1 := Db.cc_sq H.cc
  have hmk := Pr.marks_of_link k hok hl hσ hΨσ
  have hLη := Db.galL_le k
  obtain ⟨_, _⟩ := Db.algKL K L Ω (hK ▸ hLη)
  obtain ⟨_, hsol⟩ := Db.galKL K L k.ab
  haveI := Db.locHom c A
  haveI := (isNoetherianRing_iff_ideal_fg A).2 fun I => (IsPrincipalIdealRing.principal I).fg
  haveI : Normal ℚ L := k.ab.toIsGalois.to_normal
  have hb : U3.Block η r := fun g hg a b hab => Subtype.ext (hII.1 g hg a b hab)
  have hg₂ : g₂ ∈ η.ker := hmk.ηg
  have hgs : U3.gstar σ g₂ ∈ η.ker := by
    show η (σ * g₂⁻¹ * σ) = 1
    rw [map_mul, map_mul, map_inv, hmk.ηg, hmk.ηc]
    simp
  have hr' : Pr.OrdPt l η Ψ σ g₂ B r :=
    ⟨hr.red, hr.cont, ⟨hr.norm.atc,
      by rw [U3.zmat, Matrix.sub_apply, hb _ hg₂ _ _ (by decide), hb _ hgs _ _ (by decide), sub_zero],
      by rw [U3.zmat, Matrix.sub_apply, hb _ hg₂ _ _ (by decide), hb _ hgs _ _ (by decide), sub_zero]⟩, hr.away, hr.ord⟩
  obtain ⟨ρ', h1, h2, h3⟩ := Pr.exists_nrep2 k hok hl hσ r hr' hb
  have hηL : ∀ s : G L Ω, η (Base.galEmb ℚ L Ω s) = 1 := fun s => hLη (Base.galEmb_mem ℚ L Ω s)
  have hηK : ∀ s : G K Ω, η (Base.galEmb ℚ K Ω s) = 1 := fun s => hK.ge (Base.galEmb_mem ℚ K Ω s)
  let χ : G ℚ Ω →* (ResidueField A)ˣ := (Units.map ((residue A).comp (algebraMap c.O A)).toMonoidHom).comp Ψ
  have hU : U3.MatIrr ((Base.galOf ℚ L Ω).subgroupOf η.ker) (Pr.gm (W.comp η.ker.subtype)) := by
    refine irr2 (W.comp η.ker.subtype) (fun V hV => hII.2 V fun g hg v hv => ?_) (A.val : A →+* PadicAlgCl l)
      Subtype.val_injective (residue A) (χ.comp η.ker.subtype) (fun g => (r g).mat 0 0 + (r g).mat 2 2) (fun g => ?_) (fun g => ?_)
      _ (u := ⟨g₂, hg₂⟩) ?_ ?_ ?_
    · have := hV ⟨g, hg⟩ trivial v hv
      beta_reduce
      rw [← hW g hg]
      exact this
    · show _ = (W g).val.trace
      rw [hW g g.2, Matrix.trace_fin_two, map_add]
      rfl
    · have e2 : ∀ i, residue A ((r g).mat i i) = residue A (algebraMap c.O A ((U3.r0 η Ψ g).mat i i)) := fun i =>
        Ideal.Quotient.eq.2 (hr.red.red g i i)
      rw [map_add, e2, e2, ← map_inv]
      show _ = residue A (algebraMap c.O A (Ψ g : c.Oˣ)) + residue A (algebraMap c.O A (Ψ (g : G ℚ Ω)⁻¹ : c.Oˣ))
      simp [U3.GG.mat, U3.tor_val, U3.wt1]
    · rw [Subgroup.mem_subgroupOf, k.gal]
      exact ⟨k.g0.1, hg₂⟩
    · show (W g₂).val.det = 1
      rw [hdet, hmk.ηg]
      simp
    · intro h
      refine (hmk.Ψg.map ((residue A).comp (algebraMap c.O A))).ne_zero ?_
      rw [map_sub, map_pow, map_one, sub_eq_zero]
      have h' := congrArg Units.val h
      rw [Units.val_pow_eq_pow_val] at h'
      exact h'
  have hirr : Af.IsIrr (W.comp (Base.galEmb ℚ L Ω)) :=
    Db.irr_of_matIrr (by norm_num) (Base.galOf ℚ L Ω) (fun g => (W g).val)
      (fun V hV => hU V fun g hg v hv => hV g hg v hv) (Base.galEmb ℚ L Ω) (Base.range_galEmb ℚ L Ω).ge _ fun _ => rfl
  obtain ⟨J, hJ⟩ := pair2 (κ := Qbar l)
  have hpair : ∀ s : G ℚ Ω, η s = 1 →
      (W s).val.transpose * (J * (W σ)⁻¹).val * (W (σ * s * σ⁻¹)).val = (J * (W σ)⁻¹).val := fun s hs => by
    have e1 : J * (W σ)⁻¹ * W (σ * s * σ⁻¹) = J * W s * (W σ)⁻¹ := by
      rw [map_mul, map_mul, map_inv]; group
    rw [Matrix.mul_assoc, ← Units.val_mul, e1, Units.val_mul, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ, hdet,
      hs, Units.val_mul]
    simp
  have halg : Af.IsAlgChar ι (1 : G ℚ Ω →* (Qbar l)ˣ) := by
    refine (Af.algOfCyc hH ℚ Ω l ι).1 _ continuous_const fun w _ => ?_
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    exact ⟨A, hA, 0, 1, one_pos, fun s _ => by simp⟩
  have hautL : Af.IsAut ι (W.comp (Base.galEmb ℚ L Ω)) :=
    (Z.Bc.solC_of_solDescent (Af.solDescent hH) ℚ K L Ω hsol ⟨inferInstance, Or.inr ⟨hK2, inferInstance⟩⟩ inferInstance
      inferInstance l ι 2 (by norm_num) (W.comp (Base.galEmb ℚ K Ω)) 1 (hWc.comp (Base.galEmbTop ℚ K Ω).1.continuous) hirr halg
      (fun _ _ _ _ => rfl) ⟨σ, J * (W σ)⁻¹, H.cc, fun s s' hs => by
        have hs' : Base.galEmb ℚ K Ω s' = σ * Base.galEmb ℚ K Ω s * σ⁻¹ := hs
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hs', hpair _ (hηK s)]
        simp⟩).1 ((Af.autBridge hH K Ω l ι 2 _).2.1.2 haut)
  have hcsd : Af.IsAutCsd ι (Af.tw (W.comp (Base.galEmb ℚ L Ω)) ka) := by
    obtain ⟨hc, art, χ, a, h'⟩ := hka.alg
    refine Af.csdOf hH ℚ L Ω inferInstance l ι 2 (by norm_num) _ σ (J * (W σ)⁻¹) H.cc
      (Af.twi hH L Ω l ι 2 _ ka hautL ⟨χ, hc, art, a, h'⟩) fun s s' hs => ?_
    have hs' : Base.galEmb ℚ L Ω s' = σ * Base.galEmb ℚ L Ω s * σ⁻¹ := hs
    have hp := hpair _ (hηL s)
    rw [← hs'] at hp
    rw [MonoidHom.zpow_apply, ← hka.conj s s' hs', Units.val_mul (ka s)]
    simp only [Af.tw_val, MonoidHom.comp_apply, Matrix.transpose_smul, smul_mul_assoc, mul_smul_comm, hp]
    rw [mul_comm, mul_smul]
  obtain ⟨s, V, ρ, a1, a2, a3⟩ := hrig A ρ' h1 h3 (W.comp (Base.galEmb ℚ L Ω))
    (fun s => by rw [h2, MonoidHom.comp_apply, hW _ (hηL s)]; rfl) hirr hcsd (freeRes L W hfree)
  refine adDown Ω l K L hK2 (hK ▸ hLη) s V 2 _ _ R (hWc.comp (Base.galEmbTop ℚ K Ω).1.continuous) hR ρ ka
    (fun g t ht => ?_) (fun g g' t hg ht => ?_) a3
  · rw [a1]
    show _ • (W (Base.galEmb ℚ L Ω g)).val = _ • (W (Base.galEmb ℚ K Ω t)).val
    rw [ht]
  · have : θ (Base.galEmb ℚ K Ω t) = 1 := Units.ext (by rw [hθ, hηK]; simp)
    rw [← a2 g g' hg]
    exact mul_eq_left.2 this
