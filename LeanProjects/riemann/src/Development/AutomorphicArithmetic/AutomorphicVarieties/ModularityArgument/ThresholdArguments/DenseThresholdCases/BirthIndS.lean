import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.IndAutLOfAutCsP
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EGPolMix
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthAwChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthSphOfUnrW

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V UpperTheory.V.Z.Win.Birth
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.Z.Bc UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E
private theorem deg_two {Ω : Type} [Field Ω] [CharZero Ω] (A B M : IntermediateField ℚ Ω) [FiniteDimensional ℚ A]
    [FiniteDimensional ℚ B] (hM : M = A ⊔ B) (hA : Module.finrank ℚ A = 2) (hn : ¬ A ≤ B) [Algebra B M] [IsScalarTower ℚ B M] :
    Module.finrank B M = 2 := by
  have h1 : Module.finrank ℚ M ≤ Module.finrank ℚ A * Module.finrank ℚ B := hM ▸ IntermediateField.finrank_sup_le A B
  haveI : FiniteDimensional ℚ M := hM ▸ IntermediateField.finiteDimensional_sup A B
  haveI : Module.Free B M := Module.Free.of_divisionRing B M
  have h2 := Module.finrank_mul_finrank ℚ B M
  have h3 : 0 < Module.finrank ℚ B := Module.finrank_pos
  have h4 : 0 < Module.finrank ℚ M := Module.finrank_pos
  have h5 : Module.finrank ℚ B ≠ Module.finrank ℚ M := fun e =>
    hn (IntermediateField.eq_of_le_of_finrank_eq (hM ▸ le_sup_right : B ≤ M) e ▸ (hM ▸ le_sup_left : A ≤ M))
  generalize Module.finrank B M = n at h2 ⊢
  rw [hA, ← h2, mul_comm 2] at h1
  have h6 := Nat.le_of_mul_le_mul_left h1 h3
  rw [← h2] at h4 h5
  interval_cases n <;> simp_all
private theorem two_places {k : Type} [Field k] [NumberField k] [IsTotallyReal k] (h : Module.finrank ℚ k = 2)
    {v v' : InfinitePlace k} (hv : v ≠ v') (w : InfinitePlace k) : w = v ∨ w = v' := by
  classical
  by_contra hw
  push Not at hw
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank k
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces k
  have h3 : ({w, v, v'} : Finset (InfinitePlace k)).card = 3 := Finset.card_eq_three.2 ⟨w, v, v', hw.1, hw.2, hv, rfl⟩
  have h4 := Finset.card_le_univ ({w, v, v'} : Finset (InfinitePlace k))
  omega
private theorem two_emb {L M : Type} [Field L] [Field M] [CharZero L] [Algebra L M] (h : Module.finrank L M = 2) (φ : L →+* ℂ) :
    ∃ τ τ' : M →+* ℂ, τ ≠ τ' ∧ τ.comp (algebraMap L M) = φ ∧ τ'.comp (algebraMap L M) = φ := by
  letI : Algebra L ℂ := φ.toAlgebra
  haveI : FiniteDimensional L M := Module.finite_of_finrank_pos (by omega)
  have hc := AlgHom.card L M ℂ
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (α := M →ₐ[L] ℂ) (by omega)
  exact ⟨a, b, fun e => hab (AlgHom.coe_ringHom_injective e), a.comp_algebraMap, b.comp_algebraMap⟩
private theorem hom_ext_sup {Ω : Type} [Field Ω] [CharZero Ω] (A B M : IntermediateField ℚ Ω) (hA : A ≤ M) (hB : B ≤ M)
    (hM : M ≤ A ⊔ B) (τ τ' : M →+* ℂ) (eA : ∀ x : A, τ ⟨x, hA x.2⟩ = τ' ⟨x, hA x.2⟩) (eB : ∀ x : B, τ ⟨x, hB x.2⟩ = τ' ⟨x, hB x.2⟩) :
    τ = τ' := by
  let S : IntermediateField ℚ M := (τ.eqLocusField τ').toIntermediateField fun q => by
    rw [RingHom.mem_eqLocusField]
    simp
  have h : M ≤ IntermediateField.lift S := hM.trans <| sup_le
    (fun x hx => (IntermediateField.mem_lift (⟨x, hA hx⟩ : M)).2 (eA ⟨x, hx⟩))
    (fun x hx => (IntermediateField.mem_lift (⟨x, hB hx⟩ : M)).2 (eB ⟨x, hx⟩))
  ext x
  exact (IntermediateField.mem_lift x).1 (h x.2)
private theorem inf_reg (m : Fin 2 → ℤ) (h : m 0 ≠ m 1) :
    (infOf m).Nodup ∧ ∀ z ∈ infOf m, ∃ n : ℤ, z = (n : ℂ) + (((2 : ℕ) : ℂ) - 1) / 2 := by
  refine ⟨Multiset.Nodup.map (fun i j e => ?_) Finset.univ.nodup, fun z hz => ?_⟩
  · have e' : m i = m j := by exact_mod_cast add_left_cancel e
    fin_cases i <;> fin_cases j <;> simp_all
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
    exact ⟨m i, add_comm _ _⟩
private theorem val_of_mem {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) (p : ℕ) : A.valuation (p : Ω) < 1 ↔ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  rw [← hA]
  simp
set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indAutLP_of_upQuad_upSol_indAutCs (H : _root_.UpperTheory.V.Af.HypothesesH') : UpQuadI → UpSolI → IndAutCs → IndAutLP := by
  intro hQ hS hI Ω _ _ _ l _ c D T k₀ _ _ φ ι k t r α β R δ h hrw
  have hKL : T.K ≤ T.L := T.hL ▸ le_sup_right
  have hfix : ∀ g : G T.F Ω, g ∈ T.GalL → resQ T.F g ∈ T.L.fixingSubgroup := fun g hg => by
    rw [T.hL, IntermediateField.fixingSubgroup_sup]
    exact ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => g.commutes ⟨y, hy⟩, hg⟩
  have hirr : IsIrr ((R.comp (resQ T.F)).comp T.G'.subtype) := UpperTheory.induced_irreducible Ω l c D T k₀ φ ι k t r α β R δ h
  have hL : IsIrr (R.comp (resQ T.L)) := by
    obtain ⟨h1, -, h3⟩ := hirr
    refine ⟨h1, fun _ _ _ => Submodule.mem_top, fun W hW hi => h3 W hW fun g v hv => ?_⟩
    have hg : resQ T.F g ∈ galOf ℚ T.L Ω := fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hfix g g.2.1) x x.2
    rw [← range_galEmb] at hg
    obtain ⟨g', hg'⟩ := hg
    have := hi g' v hv
    rwa [show (R.comp (resQ T.L)) g' = R (resQ T.F g) from congrArg R hg'] at this
  have hkL : ¬ k₀ ≤ T.L := fun hle => by
    obtain ⟨g, hg, hne⟩ := UpperTheory.residual_characters_psi_ne Ω l c D T h.hyp.good h.hyp.ok h.hyp.two
    exact hne ((h.hyp.ps g).2 (IntermediateField.fixingSubgroup_le hle (hfix g hg.1)))
  have hKk : ¬ T.K ≤ k₀ := fun hle => by
    letI : Algebra T.K k₀ := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    haveI : IsTotallyComplex k₀ := isTotallyComplex_of_algebra T.K k₀
    obtain ⟨w⟩ : Nonempty (InfinitePlace k₀) := inferInstance
    exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w) (IsTotallyReal.isReal w)
  haveI := T.nK.to_finiteDimensional
  haveI := T.nL.to_finiteDimensional
  haveI : FiniteDimensional ℚ k₀ := NumberField.to_finiteDimensional
  obtain ⟨E, hE⟩ : ∃ E : IntermediateField ℚ Ω, E = k₀ ⊔ T.K := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : IntermediateField ℚ Ω, M = k₀ ⊔ T.L := ⟨_, rfl⟩
  haveI : FiniteDimensional ℚ E := hE ▸ IntermediateField.finiteDimensional_sup k₀ T.K
  haveI : FiniteDimensional ℚ M := hM ▸ IntermediateField.finiteDimensional_sup k₀ T.L
  haveI : NumberField E := {}
  haveI : NumberField M := {}
  have hEM : E ≤ M := hE ▸ hM ▸ sup_le_sup_left hKL _
  have hKE : T.K ≤ E := hE ▸ le_sup_right
  have hkE : k₀ ≤ E := hE ▸ le_sup_left
  have hLM : T.L ≤ M := hM ▸ le_sup_right
  letI : Algebra T.K E := (IntermediateField.inclusion hKE).toRingHom.toAlgebra
  letI : Algebra k₀ E := (IntermediateField.inclusion hkE).toRingHom.toAlgebra
  letI : Algebra T.L M := (IntermediateField.inclusion hLM).toRingHom.toAlgebra
  letI : Algebra E M := (IntermediateField.inclusion hEM).toRingHom.toAlgebra
  haveI : IsScalarTower k₀ E Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower T.L M Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower E M Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℚ k₀ E := IsScalarTower.of_algebraMap_eq fun _ => by simp
  haveI : IsScalarTower ℚ T.L M := IsScalarTower.of_algebraMap_eq fun _ => by simp
  haveI : IsScalarTower ℚ E M := IsScalarTower.of_algebraMap_eq fun _ => by simp
  haveI : IsTotallyComplex E := isTotallyComplex_of_algebra T.K _
  haveI : IsTotallyComplex M := isTotallyComplex_of_algebra T.L _
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  haveI : IsAlgClosure M Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  haveI : Algebra.IsQuadraticExtension ℚ T.K := { finrank_eq_two' := T.degK }
  haveI hK : IsAbelianGalois ℚ T.K := IsAbelianGalois.of_isCyclic ℚ T.K
  haveI : Algebra.IsQuadraticExtension ℚ k₀ := { finrank_eq_two' := h.hyp.deg }
  haveI hk₀ : IsAbelianGalois ℚ k₀ := IsAbelianGalois.of_isCyclic ℚ k₀
  haveI hLa : IsAbelianGalois ℚ T.L := by
    have h := @GroundTheory.Global.isAbelianGalois_sup ℚ Ω _ _ _ _ T.F T.K
      T.nF.to_finiteDimensional T.nK.to_finiteDimensional T.abF hK
    rw [← T.hL] at h
    exact h
  haveI : IsAbelianGalois ℚ M := hM ▸ @GroundTheory.Global.isAbelianGalois_sup ℚ Ω _ _ _ _ k₀ T.L ‹_› ‹_› hk₀ hLa
  haveI : IsAbelianGalois E M := IsAbelianGalois.tower_top ℚ _ _
  haveI : Group.IsSolvable (M ≃ₐ[E] M) := Group.isSolvable_of_comm fun a b => mul_comm' a b
  have dE : Module.finrank k₀ E = 2 := deg_two T.K k₀ _ (hE.trans (sup_comm _ _)) T.degK hKk
  have dM : Module.finrank T.L M = 2 := deg_two k₀ T.L _ hM h.hyp.deg hkL
  obtain ⟨π, hatt, v, v', hv, hi, hi'⟩ := h.dat.att
  have hk := h.dat.hk
  have ht := h.dat.ht
  have hreg : π.IsRegAlg := fun w => by
    rcases two_places h.hyp.deg hv w with rfl | rfl
    · exact ⟨_, hi, inf_reg _ (by simp; omega)⟩
    · exact ⟨_, hi', inf_reg _ (by simp; omega)⟩
  have RE := resFacts k₀ E Ω l 2 r
  have RM := resFacts E M Ω l 2 (r.comp (galEmb k₀ E Ω))
  obtain ⟨P₁, reg₁, att₁, inf₁⟩ := hQ k₀ E Ω l ι dE r π h.dat.cont hreg hatt (RE.2.2.2.1.1 (h.dat.irr _ RE.2.1))
  obtain ⟨P, reg, att, inf⟩ := hS E M Ω l ι _ P₁ (h.dat.cont.comp RE.1) reg₁ att₁
    (RM.2.2.2.1.1 (RE.2.2.2.2.1 h.dat.irr _ RM.2.1))
  haveI : IsCMField M := IsCMField.of_isAbelianGalois M
  haveI : IsAbelianGalois T.L M := IsAbelianGalois.tower_top ℚ _ _
  have hMfix : ∀ s : G T.L Ω, resQ T.L s ∈ k₀.fixingSubgroup → ∀ x : M, s (algebraMap M Ω x) = algebraMap M Ω x := fun s hs x => by
    have : resQ T.L s ∈ M.fixingSubgroup := by
      rw [hM, IntermediateField.fixingSubgroup_sup]
      exact ⟨hs, (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => s.commutes ⟨y, hy⟩⟩
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 this x x.2
  have hsp : ∀ (p : ℕ) (v : HeightOneSpectrum (𝓞 T.L)), S2.SplitIn p k₀ → ((p : ℕ) : 𝓞 T.L) ∈ v.asIdeal → UpperTheory.ConvolutionTheory.GM.Split M v :=
    fun p v hp hv => splitOfDec T.L M Ω v fun A hA s hs => hMfix s (hp A ((val_of_mem hA p).2 hv) hs)
  have hpol : Sol.Pol ι ((r.comp (galEmb k₀ E Ω)).comp (galEmb E M Ω)) := by
    obtain ⟨m, hm⟩ := h.hyp.two.ord
    refine UpperTheory.solvable_polarized_restriction E M Ω l ι 2 _ (UpperTheory.solvable_polarized_restriction k₀ E Ω l ι 2 r (_root_.UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.polMix_alt H Ω l k₀ ι _ k t r h.dat ⟨2 ^ m, by positivity, ?_⟩))
    refine MonoidHom.ext fun g => ?_
    rw [MonoidHom.pow_apply, S2.up, MonoidHom.comp_apply, ← map_pow, ← MonoidHom.pow_apply, hm, MonoidHom.one_apply, map_one,
      MonoidHom.one_apply]
  haveI : IsAbelianGalois ℚ E := IsAbelianGalois.tower_bot ℚ E M
  haveI : IsCMField E := IsCMField.of_isAbelianGalois E
  have hW : AllW ι ((r.comp (galEmb k₀ E Ω)).comp (galEmb E M Ω)) := by
    haveI : IsAlgClosure k₀ Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
    have h1 : Sd.IsAlgChar ι (1 : G E Ω →* (Qbar l)ˣ) := by simpa using (_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results H.toClassicalTheorems E Ω l ι).1 0 1 (by rw [MonoidHom.ker_one]; exact isOpen_univ)
    have h2 := _root_.UpperTheory.V.Z.Win.Birth.awChain_of_printsH H k₀ E M Ω dE l ι r 1 h.dat.cont hrw h1 (RM.2.2.2.1.1 (RE.2.2.2.2.1 h.dat.irr _ RM.2.1))
    have e : tw (r.comp (galEmb k₀ E Ω)) 1 = r.comp (galEmb k₀ E Ω) := MonoidHom.ext fun g => Units.ext (by rw [tw_val]; simp)
    rwa [e] at h2
  have hbad : SplitBad T.L P := fun v hv => by
    refine ⟨unrOfIne T.L M Ω v fun A _ s hs => hMfix s ?_, fun w hw => ?_⟩
    · let g : G T.F Ω := AlgEquiv.ofRingEquiv (f := s.toRingEquiv) fun x => s.commutes ⟨x, T.F_le x.2⟩
      exact (h.hyp.ps g).1 (h.hyp.two.unr A g ⟨hs.1, hs.2⟩)
    · have hn : ∀ p : ℕ, S2.SplitIn p k₀ → ((p : ℕ) : 𝓞 M) ∉ w.asIdeal := fun p hp hm => hv (hsp p v hp (by
        rw [← hw]
        change algebraMap (𝓞 T.L) (𝓞 M) p ∈ w.asIdeal
        rwa [map_natCast]))
      obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
      haveI : IsAlgClosure k₀ Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
      refine _root_.UpperTheory.V.Z.Win.Birth.sphOfUnrW_alt H M Ω l ι 2 one_le_two _ P ((h.dat.cont.comp RE.1).comp RM.1) hpol reg att
        hW w (hn l h.hyp.spl) A hA fun s hs => ?_
      obtain ⟨g, hg⟩ := h.dat.away A (mt (val_of_mem hA l).1 (hn l h.hyp.spl))
      have h2 : D.ξ (resQ k₀ (galEmb k₀ E Ω (galEmb E M Ω s))) = 1 :=
        h.hyp.two.xi A (fun p hp => by
          rw [Finset.mem_singleton.1 hp]
          exact mt (val_of_mem hA 2).1 (hn 2 h.hyp.sp2)) ⟨hs.1, hs.2⟩
      have h3 := hg (galEmb k₀ E Ω (galEmb E M Ω s)) ⟨hs.1, hs.2⟩
      have h5 : (S2.up D.ξ).comp (resQ k₀) (galEmb k₀ E Ω (galEmb E M Ω s)) = 1 := by
        rw [MonoidHom.comp_apply, S2.up, MonoidHom.comp_apply, h2, map_one]
      generalize (S2.up D.ξ).comp (resQ k₀) = y at h3 h5
      have h4 : g * r (galEmb k₀ E Ω (galEmb E M Ω s)) * g⁻¹ = 1 := Units.ext (h3.trans (by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h5]))
      exact mul_left_cancel (a := g) (by rw [mul_one]; exact mul_inv_eq_one.1 h4)
  refine (fun h1 h2 => And.intro (hI T.L M Ω dM l ι P _ att h1 hbad _ ((UpperTheory.galoisRep_irreducibility_criterion.1 _ Unit _ 4 _).2.1 hL) h2)
    (awInd T.L M Ω dM l ι P _ att (hW P reg att) hbad _ h2)) (fun ψ => ?_) fun s hs => ?_
  · obtain ⟨τ, τ', hne, e, e'⟩ := two_emb dM ψ
    let pl : (M →+* ℂ) → InfinitePlace k₀ := fun τ =>
      InfinitePlace.mk ((τ.comp (algebraMap E M)).comp (algebraMap k₀ E))
    have hpl : ∀ τ m, π.HasInfChar (pl τ) m → P.HasInfChar τ m := fun τ m hm => inf τ m (inf₁ _ m hm)
    have hd : pl τ ≠ pl τ' := fun hp => by
      refine hne (hom_ext_sup k₀ T.L M (hkE.trans hEM) hLM hM.le τ τ' (fun x => ?_) fun x => DFunLike.congr_fun (e.trans e'.symm) x)
      rcases InfinitePlace.mk_eq_iff.1 hp with hp | hp
      · exact DFunLike.congr_fun hp x
      · rw [ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))] at hp
        exact DFunLike.congr_fun hp x
    have hinj : Function.Injective ![![(k : ℤ) + t, -(t : ℤ)] 0, ![(k : ℤ) + t, -(t : ℤ)] 1, ![(k : ℤ), 0] 0, ![(k : ℤ), 0] 1] := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> first | rfl | (simp at hij <;> omega)
    rcases two_places h.hyp.deg hv (pl τ) with p | p <;> rcases two_places h.hyp.deg hv (pl τ') with p' | p'
    · exact absurd (p.trans p'.symm) hd
    · exact ⟨_, _, τ, τ', hne, e, e', hpl _ _ (p ▸ hi), hpl _ _ (p' ▸ hi'), hinj⟩
    · exact ⟨_, _, τ', τ, hne.symm, e', e, hpl _ _ (p' ▸ hi), hpl _ _ (p ▸ hi'), hinj⟩
    · exact absurd (p.trans p'.symm) hd
  · have hs' : resQ T.L s ∉ (resQ k₀).range := by
      rintro ⟨u, hu⟩
      apply hs
      rw [range_galEmb]
      have : resQ T.L s ∈ M.fixingSubgroup := by
        rw [hM, IntermediateField.fixingSubgroup_sup]
        exact ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => hu ▸ u.commutes ⟨y, hy⟩,
          (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => s.commutes ⟨y, hy⟩⟩
      exact fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 this x x.2
    obtain ⟨c1, c2⟩ := UpperTheory.symmetric_square_mixed_charpoly _ _ _ _ _ _ _ _ _ h.mix _ hs'
    refine ⟨fun g g' e => c1 (galEmb k₀ E Ω (galEmb E M Ω g)) (galEmb k₀ E Ω (galEmb E M Ω g')) ?_,
      fun g e => c2 (galEmb k₀ E Ω (galEmb E M Ω g)) ?_⟩
    · have := congrArg (resQ T.L) e
      rw [map_mul, map_mul, map_inv] at this
      exact this
    · have := congrArg (resQ T.L) e
      rw [map_mul] at this
      exact this
end
